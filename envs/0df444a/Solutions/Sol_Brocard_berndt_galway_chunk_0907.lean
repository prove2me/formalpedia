-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0907
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:50:40.521101+00:00
-- url     : https://prove2.me/submissions/c2e0b4a2-61e9-479b-ba33-ec9f19d3c55a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 162949640 ≤ n < 163129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 162950890 1250 162949640 162949669
    0xa03030b1c1205372c01030605100c05070609050319050f06040507090510030309090c020c060d0b040b04020a0c031b0f121206150c0305090301050109140a0605 70
    0x6140d07000142821906406684544030421800803401414000d0500b0786003501c0000c030780e103411301052208081d41c10706924903903140980c848000614030314645607900c0710340038814140060b00b6030f202e50200e514000c0308410140400c1e24181220140103040100400800152502da40024205808251201c40003d0a020300c031034804403640410406010728607102d07201d541100c019103890b00704a0794503e900d10a0300ca84038548000304101c0b0a03451244002d0301c0e09a01c81d003005c00c0c40c0401c10802400c810301c0403803c502035031410054139981c3d0001040901a02d01c00801c920b021601004121b80b01a030300c4a00c02c9104100282003103420141e003c4986400d41024a14140c421240d00251f60b0031120003003c5500101d4107008205050500040702c0d9025901d84401001c1d180a90048039008c0c0110200000c1c01080c03031107a140b00d00000145248603191080c108010000440d0035141c007a080950016103c0141e089107440301039032580e2243c0b0181c014810315240c00003048411889008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 162952140 1250 162950890 162950903
    0x3041109240604080d030b100e15030a18050c0102011415040203060604080f0703030f0e0a030816080408100b0a0b03150418030806090c0f09040510080d020a03030b1c 73
    0x1484850390b59400641c1c0c0104602020303180e4003010080003c0c028056604613034401c600c1e01044068451146000000c0b01c1005411960340701c02c1c194040c00c440c0c000034039176401d240d00c502400e012503d4054812581c1071007140140076074040341001a0035104004412250103003007900f008184507086003c83c2000009171801640d0b51a1200410302c2e91050b41c00c11011441420351020300c01000003070443c00c80303001c2e58500c2280702c0e02600485449004c50440740d0b1182030107000340302003141c4c0c40c000d0040312a101c1c1c5442c0e0390701c441c2c2c0e22040c40d604940c0c002c07a031035002110394a030084080e0241c0e40a03200200c2d00240c48501b008005005404058804c40c46040080c0f10600a41c079240d0210806803c651000f0440c21aa85002030580c0011141d45004501002c04225480c3d038200688129039081004c0074180b084513400e010080500400000d5400c0f03041100195101c4c05020200d00d10740ca9501420005a4a04002e070035a8a4694018055603d01c0c40704035001040360300140700b03142c1c80f05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 162953390 1250 162952140 162952201
    0x607020111250f03090810060302060706050901150f03050f030405100305091002070b06011205192703110c06120402091510030608010e0d0c030c0611030a0203041109 73
    0x3001c0300403002d6540010004403018150405145d04400a00100d85850045031840c017031414403102501da2a1000a400410071300070600000e98035000547d01c609803800001d000150f81c6080003081c42940d012030b42d06480c0300c205005114092003c1c41c00c240762039000f18581407030400030806410a030881c2500f0503035584040740b1440c40520200c1c502035007004003552110691b00700703200c0020003920b165000c1890a810001c0e0b2003114001e283c0b10300900805020324103402640403001e44040100c0460a00581c402c2e017020b00a040d4218400c0d0313000c3d0741c1d603d0405001d2801c143c40c0050421145124210070703c10405407040100744154001d0381502c0c08007a94a6545a09000400d4a042c2e15031120032008901c240d0f81c4e1660003d4201c60a0000900034661a0220203450f40b8081540f00000303512031104001081c09040b0345481d10f4030501002454421994600b45503800030740702d03d240e49400006000c00d010b10b00005505945044070600154100a161448805a00003891480d042c004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 162954640 1250 162953390 162953437
    0x10e0106080a060906090b13150b09060403150504020a080c090106120b030a0b15061303080f0d050a092306060907120203100906080d05161e0b090607020111 69
    0x1074200c88001c04d5a9901030184070b455800c280c02401070a22401d0159034640c1102040c0042030281d140c0d811403041d40302d0ba0f0b00381400802c0c4001c0e48041d0b0b0303168002c1d4040000000040c2e10b85403254003298845c0300000d8604251042100c20b600c0d541c4004041d900c00320000ea95076480010103411240c0c5400d0006a00e180710400801a03d0f040819035418040d103070381001800402d00c806840b03442c100d00c403450048194070411100f400b92100344c428485c1510001e00004d80f0f1000101460a07401280c2418000212085030590380100e8141c00c0c419141c0c105001007201b2640000810400510404100d0041c00586555220010f00b40e9110f00d004030007003800a8003540e80c03040201108176080d035603454140c804180b401404d1288002e440e103041300001c0d08044c0494101e00224556881903d4000c5420801002e40500242950300c50240c800900e00c3d80b15014081d4642442100c00c050700d454040085da05102008040750207590400d176908030402228006c07540f1950014110158003c0c24 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 162955890 1250 162954640 162954661
    0x2030a18050306071101050c0c070b0d02040308030a0603120f050a0c030905041514010908120307030f020d090303051012081303080f0403060b01020a0309050418021e03060f010e010608 81
    0x66500450b018062a800c1c81820303a444160f4890107a9210001e11898a5071140300d1040c3c0310784036403210203070000242484013462907c010702a500c901d020250800da1291295016a0b0040d03400b000b61907980d89040007000541a2030340020b21490034410409401841e005d415445000310700382c200f00d9680207040426005200345009410060010424400134603000440620580255900c00c80c201c40001d8880d80b00d100c03600261001c0102030101c080c584400281030340c00141082d000d150b00c0b00b0485280f10214400307800d80943d003042c003048402c6642409011550b02505082021501440c2030102013415203003008080d6118454a87d90b488880c02a0f50180e082c0e0001004440c001400f0102003003084090801c1c0c9006d80b904110300c0c8043c5e0b0040e65901c4031071100401103003c4190401007840d0561181445005283c0000c01c1c407402540001d0210880d42103414905605a2041c0c015081c1009919845900d408109401e9418958020400d0300144946000c00500c0070001e0a802c18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 162957140 1250 162955890 162955937
    0x3060e07080f010c0207080703210e030d08150d0b060d050a02060408062707090c121b1106040b04060203041e08191d060f07080f030a050c0a02030a 65
    0x4941099602d2044400340c1c0358041e0194042800040c0701703109011502c0a03000ca805401c480c1d015417116008015410011806101807841ea010b00031030054070f044c42d4800740501c8100c0c001035a101c60503850001d40d003d0300c90010703071150740c001c0e50303030345210800110102c1c04203422510841d900210548035207403603860a612104000c1d0801c10214000031080c50000d00180240540a408a0110b0b00451580c0c2844040c1c20f0101b280d6210410800c403440306548002c44001c03443c40c3c52039038640d00e2074500c7e0940384241215103a2b110507162400b1460b0340b10300f000c0d04d00c445450182216092175143c1003403410300600040c0801f1790000c0843c04011101c0500500e507044404040d03290b03140340c209061a50408ac1c451302c0d200508442d075007811446816155107280d1001402c2c5029000c0c1000e001c00e0340c10555018140c0641004036102141241d000342c81c0d92540014216520b283c4072011105849000c0c01400001d0024801d032001d07184c010081d5074030441c039880c114210340e041d00c45003c1c8410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 162958390 1250 162957140 162957149
    0x100510030807110306010b03090d030903050c010e0f010c0e030304090b061306111504050a0b0a020c120403050d0201020a2c04091506080c01140309030d050c040e061903060e07 77
    0xa00007034101c100103c10904a195080803030070f8440c980ea03a0300c0000300502c8200d0b227030605500500c410360310050095200e00d82041c040d2600318240714200c04c0d0070f401c4031002d42d4018156840200c421306002024041c80b100d519240c98844050403824000c01d40e280120f0240da40e00507298030010b80e183d1104819101c1da0038603c0d15030503d00d580d404015100d07141c02001d03850b032070140c4c04802c2c40e5a000c0294960080354460010a0702e1300440d1200b40843c1c401130a68255503800300300c0a509071070100f00b80940008060700c0306035200d144d880d0403890405021100c9003076900610143d40d000360040d800703a0b585403503031211820943c00c0070236082409100c0c3c43c59a9215103004c00d00018810300440c91055401c0c0d41204002d02c0d601c0710001650ba61078540b0003400103106a0a003d44182d140c0080c617041904881264184401150500305688040724007600148002c02c3c10008604d040c00f030300c5c0d0400d42c00c0e80c03e26410004884050003d082c03a00001d40203940700c1016203400038080043d04020b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 162959640 1250 162958390 162958403
    0x1b180409060204032f0604050d050f0303152409130e030d02030601170912280206041203051b0f090d0b0610030b100f0c0506010603090314030910051003 67
    0x440c0c0b0fa05d41031204650085035a5000745051070b541880e40246070424120142c0140344a00b400c1c500010001030180c1c0c6c1d417080307030b190068010300c20410310204081c50250900020100380c5050303403014450140e1944a044150b2061151210f00a0480303c00300c64410780140d0b40225011880480b003400b40440302c465611520000132101c4011511354007850140350240ea41000100c21100c12014100c4103654807821901302480e000304038031150f00140182e020004440d800b07410711400b04480040250308600241c0c10400800c030801031a06103540c0707421924242000f203820300c614044112005207503024098800000c1000460100d03070191005060018041500d1006916110300c08110680c2c11501030792481c2500d00025010f4020341102d5040500404030703c00740001e080300c0800c10354240406028a0307600301808642c080c0030b40c1e4040c06441c1c4000c90380b6040b52600030116032031507001c2d07040a9001d00030304c9170206d00407a014034089000c1c80c0c0400c440d1500c442d80c5102244590006240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 162960890 1250 162959640 162959647
    0x8160309051c031d1501090c090506040902030108010e030712050f0c100603020f040c020a080d0b060316020706090e0403080a060801060801061508190c03020909090a0b1b1804090602 80
    0x58642c50b070403000c000d40104c0c4821540e0040704061544d9800b200c00e650041180c1140103000305035055100c82c1d4440c151389030681c0700b2682c0d04086811390f842a08540b890036000401030190400902521500110100007035140140c0341c0c846201441e0070294107002c2040000f120410340c0c0b0510700740c82c0001c041c0d105841c10b9000507482140180300c01c1c03008a010714507003150741d400b42c07400d8852402c0d44420364003c1c00031042a9600c10100e41d102c0c20030f44601565581c1c00320360343c4d01e40c0d0780590321600d56000900d60105641101a2038080c04d94095403c200094000748500300c155184541c1295040c1081480c03529006070440103130003a9040008290f2a15000042c84c08054000d2012038040750f03c42085501804070803a103192044400f401c64240c001688110b00302c041c0c0c03040c0c4141590707160046c10207800741d0000c2c02044041c1e600c0320f800e900010360300050040b0b40c42c409800c661b105809080900c1e05410b0700595001c0d210110b9240e44007030060b0748a1740c503503401c40086ca99000208640d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 162962140 1250 162960890 162960943
    0x312130b01091a0f06041e031a0103080906161407030605090f030a0c03031b0c0b060108150d0309050a03030915080c0d0b061303050102190816030905 66
    0x61081002680c68036005030000030ba18842d8840d2100c03081c0c0305400f15820507010302c10f01a00300c1e40e039081035802c400104400598030030303808260704150004c3c4c0c088066040c59410b14080003043d2040ca0320008034000010170000e2203160450702c0f080030950707400741c55a001000008090030107000190041903480d40705141c0c0c60000c507114040d2807007103c0412483e207500c1c118940d1854584190140d60b40208410300045014240c2c00341c48500c28034021a902c8a115034490a20001811003408281011148402c00c1440301d00b03c0d82c000d100b0301c0c107a1154a4000300906280300c1c005049801007464448a00c10b00d0f10030203503c805040041c004842d11a9030f494020701495081c81003820040030002081011441001410b0050358103034001818409860000d1b00200543c4c92610352001341000800e138902100b02010000310301500006884080800041c5803040c1d42c422a40200100da40400c02465220f180624106180d454005100c0700701d032500916100072140e0482e10018031006222 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 162963390 1250 162962140 162962161
    0x12120c0c070305010b1905030a11030708010f0c090902030907050910090915150803030408031510020c011202040f120c0812040504110304020102060708070504120b0f060f0904030c050312 82
    0x148605c10540c1e040e1046902104902c8019880340602135054025078928000700d107051110500044005064958050b5280380791800c554444641000ca01e40728004001d040707070031505090083c90401420752075454885400da841e03409900459101e404c00c80302158103500400c1d2100041d1003110303020131480d800b0342400ca41d06042458004505070812a000000100000d181c1c401c91704403000071821920396a07614601c0b60401011600b40c01c43c00700d07540b196656940c20781a20640755801610581030710034001403a114200306240c108500400017000a1140e4108103011030b003a20450700c0042501d49401051082c09502c050a1446140105401d03051040000c10854a080f6810400c210031241e4640ba140011140640980c2203800041c5605010b16012a8004054501980303420340755a400c3c01011051071042d6141c241000400102c860f90031511500100308980c1a000d0b00b501d0b1001610745400204014100000240381d02c080040400644100500003002100c807450002c0245 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 162964640 1250 162963390 162963401
    0x7030501060e130f03030b01021c1106100b0702010302090a0302040606050408061e180c03070603020c0c0f0a0b0c03090a090c020d0f05030718090204030c061112120c0c07030501 78
    0x300c1c209400400f08100c0c22188000c1040194040700344000c3c3d0600c2c0e00e0903801403112610050540c00303240c3c0c1044040801c082003941840d41600d40c40d03e20001c4010302071170804020003442c4111500e80b404d05c44019040181c1d4802d0307509180250f034440b510808a00207000030342c40250414204400481c003150440040e00907507010f40c0860745c50b5030b00c00340c01c1c030320b090f08c10036070341d440848804007161440c100d07440880c04151642d0101c6081b10407082c04a0310b0070840e030b400540042e030b0220b580311180000303118042e0b5160040b108110b42c020303540002070340203810303100e204000200065405031101050003030301c0503a10020b094101c05903881c500c040c0604040314031840140900614050075030701138080e01e0544c86d542d6669070304566070303d4420f42d489107400076102528042c030000040c1e540401d00080015503c070b01040414246440c2015180c51121401401141c2000d035500e501c03142d010003034800340910641603079002d4450000c01c611030702c600d03111103166002d505800f005003d0150400b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 162965890 1250 162964640 162964649
    0x40609050a0504140c0108060103090609021809010f0b030c09091005090c0a080a0f06050c040302040f02090306070912030503062107030506012106091713030b07030504080a030509010e0703050106 86
    0x20140312400c154020b9172180725122074a8040360800020036180c3d4800d911903880d1a100f407400040f0604640c0005040e6009034803000701c0700d150801007101000e400e0061766090702038900180711800400d40001e8a8009481d105809106020002509107004202d81a81039801c050300b00560709000c2c4046441c1c019030380c002c0d0b020340c1c812000018101400030b051f0181d01e802402c580d20baa031603a901c41e005000e000e1300515103060705000200c0980d543e482650303607441c4004401030740c9203c0d6030145410540014400010f2282500307080081c44001c040204150354140341060741e9a0341c5800041d20305540382240d094a00e10603042450741c0320001002d9044d40d000e4011210030f42e0303030742d00d1403035604025501c400d0200c0b90902092000420942011070001c7c420132156904034440540940160401085000001001403040060080c0c1c2046150000e42c103103828040c0e0b2410752207046032480354071140302c20140c0c1c5100241400c1402c2d4001850b0b00f1020050323501241e52400c00c140a84158001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 162967140 1250 162965890 162965903
    0x18050313210303090c08070e0405010b010e06190201150603020a030f1b0e031002030c03040b220f02150a0906020c0406060918020904090c03030e040902011409040609050a0504 77
    0x50200305948001034074000016a000c291551140030380d4110040e1910040444000c0740511022401800911040c000707040385c0c05024003149820b090007802c1d5110044040c0c10722800161890f0b4a80b650300454920000c3c0c0220720000d0400010200c0c010200c0c100048000e1500e21070210f002c40c0c0c0354004000040c2556028000742424030b44290448241105080300340d001d000c03440fa400f9004075540c80c42d2580007010750310580407100084090340e1049a00300d600e0b42c8000200010040c0181d039590f005110b0742d188038406080c101201d0489150f2802c0a400c8074511000801159650720000800e0100c40e000e4680300e15100101400c110110b000700c00250255407603000c40c5003410700c6880d08540541e03607840c1400b458800d0824003000034404200c00d85408000314a5262221f0045110161040700307100741540ca10300b4014840c03070a1000e0148202d0a1080300340250380d00003c1c01c0d285920702c05406039070b228484000340c001c0c45190300c084040c900307090130483c60810507031180740301c0c1b0300411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 162968390 1250 162967140 162967177
    0x304031e0509270405150906010e040b090307022d0616080a12091101030518060402011b021305070f09151b1e0201030605041112070201180503 63
    0x34840c1540d603400200e5440060401e100000e00c600d001003640d102c42c4118020391603600800c1c0d48140d0b81110860b070a545d40d0b4010705c601107515004409850707000c003801d00a81945e504141420086040242010b030034107200030301250b8850b00500032114038941c024801c081701003d0f000c280c255000e410405014821010700c55400c9070a120003154164286040000403c0e5110340d96950700d5007041503500b04004140304a40c400100a100e10310480e40644400d80d41c1d100034400040c01e40300300500c26680c03107004090701c690003030000400036001942402e15114a0b0700e032002e8041c8180160744041c4d444140a040040ca0340c0c4603070700c454010300e0160f0781c9512902c1c0c00202914007003401e00c41c09541e010724502d10b00350544114081c04440407049903462041101c1e84901040c41da40008a8203c1c408202980c401c66030140301d020b000b06000e40c1c041c8914102c14000d00d4860040001442e008400c1c417000800d020b1007075000ca02098158994010080d4a80c00c105a80c1c0e0010408a0038a1fa2900d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 162969640 1250 162968390 162968417
    0x50913020a05030111030a0903021908030f0a0204060f110c04022b0902060d090f060e010b030c010207050616020402070f0c061107150f03110a0f1b020d0f05070801020f030403 77
    0x1070241c0c0c850307034080414046c69030b2103440741c08004003038591054045004401580300010107a10b80c800149000d00341e410780324240f0240c0d03041c0225024101402a502c104005c0000030781110711090711082038200b181202620160240c00d102040171044e500a1001078044280c1d0f403041c0502c940c22002c4510300564001a4001c2d40883e18038140103540b111080c042081c1800068021700845d600c101c2500c80490070643d00e54003030f500e208100d0701a070b944030600d01030305007010081d0b011281400d00c0105841460315020400714030403926020903041c1c0015010040d0b4035280c04885020350b2242d80c400841001e0704118503035000602a8400281c0010b0a907540c0c0c03000043e442055604c3c402c5201128091a40c0a841d000c0c0c03242c111409054991400d1410307804c2481c05081c900941da122903034010008880288070503141e454616100d0a2003c1100140e15600800342c3c02d40d030700c40801a44000c41b82401460240c00c1c3e0702c80034856000146c1035010309030307a0380954000c5200b40c40707500c40003001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 162970890 1250 162969640 162969643
    0xa2c100209090f10120308180c100e03030910030b03060708220515011e08060103050706050a14031501080c1c0f020705060405060403090b03010b04120606050913020a0503 75
    0x200001076501144400200b0a038903107142d50940c01c82244450fa02050b40d1303a91900310340c07001c0e00c0e01c190041136070752040006440708044408a041c0d111005440d528500000051450380400c900c4003c2006241c04480103031410400c41d00c440d000240308502d01407001c54005c000d00500700300c1c03034001d00440003c00c4582d4010406c96014001000940710320f002c15201c00285001900c0042e01d8600c1040701180e508008240c10501030452071018200800804c8011260b41120764403105195000400400103c0e4010554100b074841525200f80c0d00da443c0d0008035918080e402e58100d0150300007051280205001010400340f0500b03072038070b1407541d503201c400200c140603070010501180ea410b200240c24080c00e81c001401c01c0c906010043c18950103480e5140303010800c8030101e80e1544400700b8801415002a10b0300028607009803820300d9581040c0c01c1a4041c0158410004400703480d203060020040c0940020f0003500b409009000c0a02d02000b500203a0b03142c2080990013262281004180d5060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 162972140 1250 162970890 162970897
    0x60504031407050c091e0a050f070507050309090618010f050103180f0f031112070512040f060804030903080c1606050a0215040c0e0c18010c0209040b0a2c1002 70
    0x4102000c0e048000100007030200f1628020074640301580c42c01c041b07100b90100d5045e02c6000d05a9500e001481d85030842805d041041c1c0902280305000c02031140034001240082120308510080c1d0702144c41d0340b03075203011554820200042c0628841c0160001c02c16002e008480b104640c004d98091010018006200d01548100200904148034200d84403020a520451300c0c42d10520070703d0044001c40c90482c42c141041c0c488a817405e13060000007402c0080c440f00b01b0007082c1d6a0f18101089192a14211220712200b129204003403e0080c3c210018082c14081e040820080d17400c410f0b0180d84030103c48540d5150300c40821940046580000d002c14920b02c03038010380b130701000e0540081002400e00c405042498074000c0080f523610001002c08280c8181c41410a40130b241000212521840480d9900c030601c107503490314504002100d10740d074002d030760307210030072500a030b044107c4c94441e449146015001d464604500d800340110312055007148020a4840058a1011020b8505c03182c02c400341801640b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 162973390 1250 162972140 162972143
    0x10255020c1f030c0c2109050603010e0609040611041512060608012d0803120a0e03160f1a10060203030613020c073201080603100b0a030807060504031407 68
    0x1080e48048103840c1c000d40c8484413000f01410301c0300340510030313540e4442d004902daa0380d804c0c0a010600a944480c0c0c00501c202d0180c0001c0f90750504541c1458107030480800c000305110307c10b01d060000f040500040b03502500203820340d81381444d900c41e00c5901130f4a50000081c2c810000400250301e80c0800c0d1014858130301680e216642e100c003030b6481c01c1c00e00000b1001d0044c88540440c0254844e080c0c19000300210001070900d0800b6588640d502480c015a4000042000b03c2641c203002c0c6034001501c02004171280300f43c050102400f0030416007000280c54400140c000c8c2220041e083c5120750140744041c00e03100301d880e190544c50090b218201203882c0e01041e80c0d010342003010700400f06006030164000d051000034100442e110300e9681e000600b43d501560813a0950500d01c00f501c0781410085516100c035024081c01c190a69003400b402113a90341581700c0e0031280702c8d9907801c0340210079501c6076140c0004582054045481d8041420010000c00c030540d803c40105940740380241d1300140d85426503050700e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 162974640 1250 162973390 162973429
    0x50f0a140406110f19110f03031f0e150f04090f080705030c07060305060f060c1504060e100e0f0106050102030304290406020702030f010255020c 64
    0x507200c5990b000702814980800d4070307402c2010311442e03c0301c602500150124101840e41012002d59040000c0c014501c180403074a42c82c1c000815080350094004112030b044207010111039442100602042c01d02d0141c1d030000076080203c0c5042c840b00007208048041c1c0c0d0070f41112380150000a002c200b000b11620f00c1001014200b0b08000315020a4480300034040c0c00f4059001c0d20318003240c004c0c0241c1000c44030380000c00440c1c2daaa050202a081034007881c0c50003203040d110a4134000c4003200c51696080c00741a0709114962100004040001c80c1d0024030b51860f1100c00c80b80c0c2c00c400000064042c0400099007500381c07094a8200c1d450071014004e0b002140c0042c0c020714950b03100c5440e80c0007000009001c032100504610000d4440700000f5114a110f5400340b0030058464082e0320415052004040307103030043d03a0062001080800c28800034a04035490307407801c6000f4500700540d401040c840304490340e01c480e10841b00c250160039100f4441c070000c00c1a13400d596884022904000800740b52100c00a0386 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 162975890 1250 162974640 162974681
    0x405030706120207050304080f0c042a0908030d1a1c1202010605031603230606010507030e0607060b0a0911090d02030a120210140c090d24050f0a 64
    0x200d4018074031460321038280b21000d4075100742501caa42c80e65001c0e44c0588030315030000e94031035985001405280d40c491001c890034010303800c1040c0e202103468404500d2a5028a900b0580500c2500a00c480401030a000003581e481d82d0072200120001c205040c1e030040c0f07840c40d1400700c1c09a446e00005201030140708441c208441c0b0340a4544c2c6400c010382c0040e11041d907580705008038440d40c041003000312402e0701403000500107085161034015030302c0341554140c01026035101c1c2880341c040400c0e425802842841d20b9916820107007001ca80c80c1c03407942c010b5078100c48001010018000079812183d4103000945a02a105544008600c100c0d004064015490070701032005034114030301030b010300403954001000c8504102e101c0d144c0307400840701480c00c1809170744641c5008048008074015521400c000c10345400c035034600304a0b000210b10503401d82c580700301c001080382400c000c48410401300e03200030f00c0808181d0a80010784080104402e5030301000380c10192000031240a801e0241c41c2e056907180c45d0041d074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 162977140 1250 162975890 162975899
    0x504050f0f07030b0109091502070c14100906110a0b010e01060905090106020303042303120412030e10020a1806030221070e121f1d06090d08070921021504050307 71
    0x41488040823106c1c1c00c05201d21000300b071920b0025221017401180c003109860300c0c10317950055035264544100e0107003c059004046168203c41750300219170701030401c205004802d03503560b424203804090050051016034000f1445100c0da24041d03050301d4241d141c80700c40302c1c0c441c0100200c540d82480b842d00103920400c00140003a540d20103411001c692500340902c2d6104040c44207003590014021700305248a000100814400c800004180504040c00c04001c11940d524a4684800e01302c09011589034001071203a2500307104132450303a0140c03216100301c603100e138648030014042d6119896205010400401c0e0741d900c001c6019a5602801c0c4603107038100310000c04818000e080c00d03000c1002d0614010418010390a40006582184810b55034400080001f00130502c4842524031b020144170a030310240030405030300000110b000083c1400c3c20800309981d601042101d4100c80c9030019007840c4184820020205102d1080708551403007101d014010041402e200c0b0001d015a208081e0f065014100800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 162978390 1250 162977140 162977159
    0x3080a0c020a030c060503041a101e09090308090105010b09100315090c090e01090903050a0810080a0b0405190206040504271a0106020303040c060f120504050f0f07030b01 75
    0x410600c050302d1800100ea4a0b140c01255590590204005c40e10010030001000402a1101c070103903940c0180341000e041c290302e40564200c0f01d000b041541002d005d110000d0b00304400030000201748150080c01a0b100c40e14000300502001da880000d550309050003c81c400203440192194450040d103030170450541c56a003180034128006520309462861840802c04050500a103010750002c0c0c0c849003030007454080c06110803103050388001c010a190402c2d100001c1d0f070144c126221001140341040342c60302c50505520007510380d50311804052107602050b07007c024800d2000c3e13214900907026602c404070030b00d4041e509080c00f180005c0d889074080006008600c0e081d4041c13500340b05462000a500859074990340882500c040e816a000800351503010001d4805502a40c058111071024600710704040d80c444194010764003c441c1408145007010000c5441031541e2040340c940842c05101a0030329040940c0c459111628108081c020035580901401001481d44100c0c0c0c1d1200320b0580981c41d20682c2c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 162979640 1250 162978390 162978407
    0x1902030a020f040f050c1909050303070303050423010510090c0206040305031b030414060606040b090607060f02030708070f0e031e0118080a020106230405060621040203070b0403080a 80
    0x681c40b83d84d800341c500c8140300c10f10469100c1d10380308020a03a5618a251100c1e04000c003c500300c0f08012903074401380401c4c0c1700030042c1c1c6d000c1a411306010a20362528604040d0011080089006102c15220704403030b00e100c1500f01038016002c000c1d001003130a40360500300081d20b1041c43d1b00809a44040301050010340f0400c003c41c1e00074802600b03805d00c038038030548151081d8400e03242a110076500c1d040769164840103200709a08488220380f01c0d454146058410b44940c011440c80910408000c10920f0912561b034000d000402180c020441da6031820460280040c0fa0544000d400201f90104100c8606d010381a0149021b500400600d44e89800c0410004d40d4003441111101c25500c0752076003504030f01c0b0740220f0b0385514071410035952940034080000b400c442440d4411600c20401214280d2040008030101810080a031004201581c640000c070744948500d00d440c401e402c01e1010881c459101021101e80180d00c01c17416500305654070554803526018070b010140102c241003016411a07070103050807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 162980890 1250 162979640 162979669
    0x807030b04060b03101d01030f06060e0f0a0608010b03030d0e150c0304030f0807050a181a0a03060b0a0801050d050a0501052509080d0e040b0306040c030201021902030a02 75
    0x420200d0200000c01c0c00d6821950000380d85000100c00d03c0107001c0b845100401601456803d00c40040160b41c4c0c5400703d840600c80608010300d031200c1c82061120035040b64000c0e0005218a1982d420411003601c0e01074011190400302e01c0c41c0100c04105801c060182e000245c03030080c01103041000100d0890020701083c01d61418a1150900e2040c40107010480103101e031035035514072034aa10702070030b001d0301d01500822941c0810004008022480b60032100352070b810f2905140010310103258882c0e21300c0c8105550050210313203480400410080700e00300024010341800390307414860565a5002e615107030003803e0b004000f16000304014400d0b420302c0202c04040301e00440448031500301907100c581c00c541c1c00b52a22504042280c81d0f001c0044c030780c11103c544c085034610b41124030070300d4144d0301030b00c0d2181141c0840030031045402851495886400900310110001d0540b569410a840c20072640303481c0f0311040b4054004d440b04a20040c0c0000085c014003600a005840c0140c031980c00c00560343d051001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 162982140 1250 162980890 162980897
    0x90414070509040213091a01110d12050c091302090414040c090203090709020d020901030605030f12090102010e0f010207020f01080c0a030504030c1203060e10030804120c050915150705030304030807 87
    0x40010780f0314040c2c002c4805041d01015008030b142040400140700c108107070107117509e683c80040101d00c041c0d0710521028400a04d0840018a41c84080d4088443e2080350207003a800209186500d010200075401801a40c004480811020300344c1c298001c2c203200c0496003d466420f20410810206250303070000c5d030340711010030150750642e600c1d00c072a801242c01c20f1000600582d80882ca1180b80d580600c04d00020380000c40023801c000030fa4111840d0b481c02e84440c0c4c0c0110201c049015040c59000350481c103014406d00c070941c4e00c0c0d8000810618005d400c407000c16441000300440120b110b50099040501426580106a06d4150341c420260041c3c40060b02c1141000910203004000c40c0002c030413500407141a40c2d020070b000d490b06101004207040034004c8031a0310789250080001461050031501104c0d00491a881e804440f030424a68103040d0394401c41d04055141c0800c03401c0754803031783d601d40303008022100685a0407444e10402058001c035013000742540d00c200041408603000707081d0194026614039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 162983390 1250 162982140 162982177
    0xf01151b0f141207110913120e03030703020102070b010e06011202090118140a0501020606010c061a03030a0809100c0c0b15041a01020c090f041e05120904140705090402 74
    0xb210301c0c5000c1a100705980d0550303000c5101d00402051031000301400c18102c17641451424a0072000340280048540149140143da810041050041008a02440f0b0080a41380c40b02c8080c1400f078040d50151a00701d0708402100000b1a0000350f50000c94022001a915a0041100c1c10b030080c000754440386449062206213510104d40f80d254034048005402082c0c3d41004800c03290341481a8114590041415500404100612070b61711080d810481034101c0404102c00c2c83e4100414820059524040c3d01070100142d00b02c180b40d04032074194042c810400407502c00096a82e003030702c12215815446000030350f0260000020513228110a90020035690707400c10503a0486d4005400c4642080c17040081d0f00750001c038508a9a014001c1c1907a120042e5150640c6241c00d8054100d12280108010001c00c0d100c1c1c000305800d168203914040700c507408001c58041074513444040e1441c1d00121583e901c2903041a0400d6041d5a2110080740114465102c3c2c07420320001104001c040d403c00c0880803150110034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 162984640 1250 162983390 162983423
    0x201120b030a03050c100b0f13090204020c240405060a0b04020d060905090c06070b06013501030b090307110f0f06040e070e0306010b03070f03140f01151b0f 69
    0x3800020702c8144242c846a551709000c0342900d040c9121140140c24081c980f92855075a5102c45819919450f412940502c4c402000d5207403074000d140e854800b940151000c00c03210306040740003900780036101e0085119203940a14101c50f00c01414125401003032a0454801314091080302e42040d81a024020405810018040340c0078084900d2507001c0400e0783d0300d880074060400d20500840102c02401e44803149425840c3d240c8090114001c1c00b000c1c100301740300284620303410883c403200e9a42020105207102c03210b030390781d54940140300038002a54680280d50102d643c03000000129400c49034001c4894640c48031080401061b90300b5a01d48980115100c542c0003a25610000140060301218511041f9400c0c140360007400d1111550880e0300030f601001c010b00100388003038150f9501503402d18040120b40000103040700501ba80d0400031400e40d41500071300851854064050707050302c0c01e000c280001003c080c0c0b41141d0221450f903504007420382d540f4220780440c0c1d03020850320070070380118010b04407180035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 162985890 1250 162984640 162984643
    0xe030303130611040303140702010306050a0b0306130e1e070f03061b03020901090b07020409020d0605090c01020304050109140604170f0d0c030813050f01020a020318100c0201120b03 80
    0x8960064220810004107000c00c4414407a6200050101803144e0410b400c50764003808003828220004405034010681104680c0300c2d40001e80a028090000190345a5070407050030f66400990384e080c82100e800a540502c1080c52040a0050103600020604014803210f510071025200540c0b50440c0500b42000c250790b45150170b00801544241c1000aa1507000d1540c40307192900c80e004c2108043c01040015100d0303910410f038a0944095051295541007a84005401851040303402074100d411143d010051000550289200d680c8010503079400041c0c11004980b02c2c8140d00035035000c02c55088003401403032400c54203103804120281c9054a4641c0b1000c1c501c900f44040401035101d640002c0c0000414402402005584070407810300140140280c1e9010700520801000002004200d000d400c0a011003082007040e01d04008000710740e83c1896450003501d03076201940000c94800d640000b071016042c0030030340da442d000c0190307110341b0004502c0d07004481d0144514005140366483c4c0e01004400e580 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 162987140 1250 162985890 162985897
    0xc0c150903070309050d020a150201020705011b020d0c080d090311030403060b0310060608070809030702181e040203030a21050f10080d020c04020f040b1b011b0c0803070e0303 77
    0x240d80045885282516009145659580000f400780009148510040e1114070b500030560302c800013034404d0392282c41e4003203009028502000d13000358207003075484c1365a4012160071130a4100a50a80747c05040100081c0c43c7c55031040c0c0001c0110400700b0601c20b07480e05960004c0e06951007481d00b03100c1c0244410b141c0d4a1a0042d400c140e40007036490350800b4251034204903004402c1d04100091005030b24013480541031480c000c01090034400707000e0000394010010b10845503466401041c1c0c40450302190003008803c601142c64050013108500001ca0611210f0a25440f995005004528042c030078207081310141d5883c008032903a1221030251944014050142c1071040240100304909440c08082110382202150302c800c003241c001c0c1c2c014024165000c10110740e102c509541c0540c4c1c648c00e01c0c3c0e6884081c460750348400100400483e074445030015002d59a5002081368009100b40500c45010301d06030800360110304045105240040001141080959400101030503c2d0442101c404086400d551 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 162988390 1250 162987140 162987151
    0x20c090a02040f0608040b0f0c0d090302060f0a110304020f01170f090c0406081c050c0d1d0102070e13080d05041202011a010210050a0f0e0d09060201050c030c0c15 72
    0x180c000c0703010712440303d0040b9420020181d0780b40198482c20203032101880c4c0303180074103500c0c4005c69200c0012032080103901103507076450185604100001640c06c00a440350426655000107a0208010404100c40c0b405802017843c0c04008151444c2ca880d1b00b0841e0030702868250340d044c041042031035022941c0d0860464461083c3e0980c0007100d1902d1100a03040000c118811841940340c21003c0c4403140000410706031007401c088084200c1601490180c03014003c449185942d84501c0c0f00406829a00190201c0300c0c9a0100e492441c00c0b410100581e00c4090b203028180b240a24200064813020400710038200207805007000034a8940410064000c1e10411135040d145d280c0f54095000e0081d42c2403003032480c0c9000344108822382c0c01104000035211082300740541e1540340c030340001c50780619080e1710007248022440020041600c034040615220007103030707924134041401c480d00008e2180c0180201c0c0e1050002c0302c049480d40d90b0f02d0010110f0381d004030b00401d100b807084900030581070a01d8080b460242 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 162989640 1250 162988390 162988411
    0x80c040b271c0c0f0f17011508010c0801090507050a0c030e0301090c03020f030a080d0b030c040c0e1f0801050d080d05010e01052425170a110c1f020c09 67
    0x707900508100f540100907502204d14200f095200b0402402c02640d10400d44079003260040e0b0f402181c440c0a8003408851a1580c40100007800006d504001503101a201d03004580711811f980e80e0302e410000c101c45086601c1c0010850412408082d14400e1544152051190802c0040c503803086020a007110000101100c0c142500d40090095140190311888042c90031001050004800d94a102c914011010070a0b080e582743c00d10748196540520601d40d01141c0a0700401000c1c1c090f900c010400c0320002e0096003c1d450400706525944185140010080c4075901d514501d84d20303110600003801e210060903986594248111990443d06002d094001c00e404416140c195050104202e140503014501c105a0380703503816000b007505600815195a00c0c00218481c0844c1165400c0000105c0410701c01042c4102d00500702000c1d0140c032002d45000303012951580d49811a81c6d494079550f1611610859002d545103040a0050075060307443c13411011548140c6205208550200300460310960747d60562 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 162990890 1250 162989640 162989689
    0x21509030405040b100c02061608120a1b08060d02040207080d060807120c0902091809030d05060a05010c2a0602010911010c1505130807080a080c040b27 67
    0x40d4580380c0554503144d5001c1319880300100d050800074115174000c42000340902008142d0000391154802c0181100d43c12210284d50b034081000114140b210031240f8200040c0741070328546e008220034008503016165a01c80d02541d40740d03c400c0103060300e80d4400c12a0f2040d001c22190780080e041c10003a040391110240c001c503081d4141107040b804c04071941c21a821048a07108a18046520f61100c04116200b40308016035580c0c00310041028001010800350003584450288405c0c03144c0000100642c1c0c000b20b10400c4951111810008402c580e80b0030a0300040618100002080b0190314a00c144e9890001a010700740683d016021045010381c0501c025035980d500c05070a00001e1410f800c0030b03942c240f0f4040303840b101030703950a0f405080c2e8180d08a0b020b43c2d1440000c200001d0402c00014185e0812241920340010b807414080c542c1c0b0100d0864005442e1001041940c00ba960984040d1040c40310100c0c10500f40d24120f6484107050074141e500d40501d01c035030031500d0300d540c41c030410b200041e508010301c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 162992140 1250 162990890 162990899
    0x1e130f090201080703050c040b0904090803010b070b060406060504030206092805010314060a0312030b06030a051501090b0d0906090c03030825021504062c150f160215090304 76
    0x142e03d000030035120070316003450100000006030f10708403030591380f44a502607164915840441c0040c00340160080c260f030400000850044141c60190503041d10940018001703a50f00ca05110549055108490110710103000500051400a010b0805031601078150620421488201c42c09030405544040b030601e4054400d001c1960305004401c0440d0846030441c40c00c0c01c0400220380c010303481e0701c0090100c0f42c20224581505201e43c000d2010408010102c0e51281400600c00c0300409040d101644541080e00f500c0d20254029a40c010450f80c603104054181900781e015003001d4020b11008440003503461032881d0024507081100390207540030740e81d020b20520f0656070301090b2581c424200003c641040a12555541d03000800c4c04180050b80b03000f1040ea151071070004081c02d00c8450000d510031403c1003521440107095400c90024159034102c1e45011003842180b903002d031064400003400b01e100d031b001403044c003030980201041d800c240c8102c480e00c242e48860100c0c1f07036000355074804098000280402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 162993390 1250 162992140 162992147
    0x6030c030c090f03080306180c0918130320100b09060306040b04020121090501151d160e090702010501150e060d240b03010e0a0b1e130f090201 63
    0x1071a109081c1001c0c0b903a030341014124102c0340264803004105010001c0003402035112458041814203411140c00502c0c200035107503207000e41002d107400703010b04034a20a42120308102800320b4090604540e9880e608100c40c0c40c21500a140d05c1c10102c415450701600c40c1ca4034004000ad540d200740500000104183c0040c1007100032900a071901d48a5800785040c040810820703020f281d00719909007003038030400c61600b031400b041c2d4500003a003c24492900300ba00090000640111008000383c3c0048213515450741d0b80012490700410b00c1c0c801503622240061040e0ba1a00d00c5400f0000c401d04104a00d44040da0010b402413004554510041c0d440b003004020030800700405940600050400c01044812803000c42c0ca07501071110000402038a40180450f08611030082034018500b45e1411408503441d000008410340c806c0c412030135242c81600002e0305100c40e03445902c08000c03000b040e20710070700d681808480c03400000e1200d0542c420482c150103c0800c111788a44916a01c03500310110743c2079a90300014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 162994640 1250 162993390 162993401
    0x503010f0b070506070305060103181208010608070f0c020d0b010b1206040203040807020103200a0c0b010b0f071b12060617160909030c0b040b090d0201090201020c06090609030706030c03 82
    0x200035010500c00000002c00c00709038a45e002c50540f5000809541e1800120054441ca03c01d078501c03a0f0031142000c080c894110959200c08440c0d4990580503661070804546001c0120f03081e800154540c102c584900340328082c1041100c0c0020904008112951075507041c10900780d0029401880010f504001d220504880d50303802030f0112011411031600303071101c4026100300700e4000d040565034a40361814a0010300b6090003800c81c041d41a8a07410341c0c0310301134610384a214060ba502a603075000055002a004110703001000340065044c10040c04c0e03914040d9243c0c00001c24503407a000d07005c001c6441070988004180c0349005485c0450400e20303001d0a40100300d010092a00c207070304804000c0a41020040c03004044a40201c0c00040a107410f0804984d01c0043d000028500300302da105210620a81030706d82c5001d404031105840c594951888203074200c030b1400d1002030141e0011268911640340c000d01400301e80070f01525680ca030200c0e080000f802c00701a0340050000c03d0344d40290882d000d0f418880c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 162995890 1250 162994640 162994649
    0xb010609150903030509060903010905070305060711010902030304060804080c0d0207031a07090302210a1202151608100b16060515031f020f0307020703050c06030f130501020c0d0503010f 82
    0x41411410f50310b0042c40c0b403150940c04e0f401540c0c0010045074546095020000982d0800180c070002a140d00d001c6403540000d480781800039003101580c0020a0041c800c085503250700a0040d4503040c2703000c40030340c0e02d03080080054800e2442446261249075040c840c0111880030760340031f06880c90275850110b503460504140b0417840700c6030f441000340054021000301c0903250125801c24141038446042003200340e074281c40c603600d8024244500100b1004c1400008a1a510340070b0f11b01c0718400c0c00010499800c00c07100d25000d030010150950b072203805007000c0c5401070304a01e220b00c2c0362134031070810602582c072a00c6c116a0500f4008040403d116003031003040d0b0450118200e254080b504500046d5071000110902d170f03001c0f0a91604808681c9a580c1103500d6402e428034440d88910f000240651280301380d01c820384207406800d05007000d41c601101100d21440168042005130b1716490a91385807940d80301c00403600740d98204070250301e024003000506040e40c0c259480665940c18402a803000361120b034031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 162997140 1250 162995890 162995897
    0xc0303090b1c090204020f04030606090605030a02031c140a020a0b1014090a02120103050d120908120619140102010b0a0b03060105030c09100509091003051b030a0b01060915 76
    0x500150310452804440b05201c04240128240e00d003800003600030b11800c20b0245007070a00080010801000d904104100c9440340002c010059482c0141a1a03588054009505800642c12411103003108c40100c02d00003590320f03042d90f40124100c0c2c4840306a02404201015a10403808030040140001c42c550303100c025190510f01040c5800000c0040b8100345440d24030408449001440c00700c41c1d41d054407501000c05408014a50f92410160f0b00d40e0718102810001070380361130340e1484811441c020400250f60105580c0e2a0803040020312551400c0940415030180b480c100113009900d51381c1518018100c4068800b0080b15000006421141a606400d0080100100030040c0b1000241600c1d032203042802e06a903250399103810170381036228641d502036200030508144070071141d102c4090009101d0a8074012010b458418a1060141d0907120041965016074492460440c40c802c6e811780b0500041e084500001641c0d5440c0040d0100340c1116001604a42003040300c148031800946690105d0308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 162998390 1250 162997140 162997147
    0x20f0d2105180a03050319021002160302070902040b0d0c02100e0105060f09240607050712031d0f1002030c1b011b1109060d050f01140a02090109090f06120c0303090b 73
    0x5803002d0301c6c0c0c00384603012102c0c03400c0c20450b038210b00d0090140e40b0004294500840d5100403049083e0510884801c00703500601c01d050020411407158400c40d4142c940c0220102e052078080800740c000f9100d890180d8085015800c0304291b010300e20f000d40c2070842105030001c10145001d00c10303c140c0742c0124224501c6186901c0a210408061103034031040c85840000c0020580c1c524001321b6060701c5414030040c180e00c1080000901210b0005140034054400d0382c03075051003501120f0301b10b40c01d0791641e1929072020590000400e913241405e4204d1224000740190390030554845240350500001d002d22030328448001c0380002c02c0b982c0c0001c41c61011031810100e08010880364450450412036111040d010340c400b03102040f191340e41c002451120076880000c17560ba00c500d1b1100c050103441c40c170355160b8103000400c021500344403890003652441c00e01a510000702525103e10480a0b00318201000c290300e03135420000c141403140381d401e01c0c0840e0250700c1075031480c5d10710302c0d0081003403416611020380a94140b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 162999640 1250 162998390 162998393
    0x10020406080a0b0a030f03020106060206060d020618010315090213060219060c02100507030e07050f0f0103050402060c1e0609010c09050d061d1609020403020f0d2105180a03 76
    0x1100070307800114046001407411407040109101c801c65030400b8015140300502001050783c15003080055071015400d851003915040305110480407a6180250f1025042c08540c0e007146c500d04030040341010526000c1100c1c605204c9030700d6000c42d01e070000200a90001407600d9030700c41c0208400001d0441d4070081014407503d90615121800c031401c0180786544400500e902c080c07007001500144260110704114604064202030024100c062500405000d60784000416140c210258820b98a018000e4140c0c110000c00442c010304005004a1b8400c200b44000c2003451010440c2941c0552a1301c480b010880c414501d19141c110001c08120041c2e040400c0415010b41c0101c07520201c450540e0a01d070900824500030025011200e41d03480b003081d030b107001044c1c507410000d1084100c0c141d40056850302c44e00c80882c01c4c03e911440c00f01940007030b6156007420560405c010104509801205444600e1290710060030000b00005100c10001e9000b1070000007a00303440055945004040319801842882e5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 163000890 1250 162999640 162999647
    0x606170a0b09151303020f030a0822080406030f150306090c0e010f0b0711030d02060105010f0c1109061302030f060f0409120e0102160e010812131e1e0810020406 71
    0x741410345401180382c4800415000300003141c000c47c2d20310192500d4060101000b00010000c40c0c115084080c40340900355400242ca0300b90305001e4000c55568034090a102050b4040c0159190480070251340781d80c068406000b1004100141d8801d400110b11040c50381080380b150002c1303400620b03115509100400000c01c01014480442e41281d8240d0b8032025682004241c0300031064405401d40110303e00d5400780c44d80444d9143c16140242c075203020440081004480f880040ea9000303001d02941c000302c0020f0701d0440c2031a50302c050000d1000464880e40900070b41a81c005984040181d12240e050242078503001440780b01c1104141c07000c00982c03642e92a1900d48c1c2d8001c0a0110a0044004406100e079100b8030107000406126840206001d60381c4035100880f2509200c1c8c01030324080e10220002800624048a01242d510707204c0c030103290b0030044003143d16000301d20740007004079801600103a04001300785c20356001042113240d4888a454000d4082c2094503400440280314810481440404d80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 163002140 1250 163000890 163000933
    0x1b03121e01080a020d0201050f12041e080d11040317040807090903080a050a0e03160204050a020406020d11161205070519091a0301050c03070f21090606170a0b09 71
    0x301105c00c80119030b441d0005854511950035541240c540c000b5916640759440406c0a0181b4804c0500c628203140c2c42e03069425400d500e600c02005001c00b0031031003c540c0c41d030ba0020120750300740c000d645107070550b41e940350900c0c124400900116000081001c01c90341d402480341000500e07108506204900340c50b80d00800701a001021003510f5941e80001c500d0311a466400b0b45d01c0114404122940c849048040003281c1c1c0d42100d0880c4a00d041000140e0300c0c084500948040300d015400601205442c140b003600c1c009200032041c01e8600c110070368078191201e4071440c0d20003011031500d900c00442c4141011402c1c0185034004d580100d1200340f105034080e404010030000c40709c12010025855030b0000d0500c840c09a0300c045d1641c0b5600300001d02c400c580b064002140156116260b5041c0000f0b5154103590154070103a034240a44010f40514181c1c001c1a04414085440b401c40002c800380c07100c19210620005655807075140d07000030001001c0280101c1e0b215000600304000345071190061000202000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 163003390 1250 163002140 163002143
    0x109060f050a0c051204081b0a0621050a0e101a120a060e0d170405070509060303090301060b03090106060503010f050f03070b030403030212010605120c1b03121e01080a 74
    0x100041061142c1d01c40c07a004103242d82e0082c140c4010811060455003982c0060003072000724040c02088552150022a2000ea0104050911101c692401e0029034507840b512030000f01080103c20100d80750b8903207109152060940b04c200040340b15540514600d0901625880c1001c1c40c5460402000c44a659005c1e04210000f2285200c000d4802d07010709062122141009100b6410441c1241c41d20001040c54008403009584d050b00303020748031111075000e0700c00380c1e0060055040b000092125082080d2010350000018044a01d0401c074040030a084603501e82c04039121000201c18000180d40038000e44005002610b841800e550500c1c001c00080302d0203214040c401ca42d110f802e1051910f003408024000c00004d82102d84070302c0e103400c0140180d07020f01c0010b20030328101d0001182083c013840030307114001c101e112076007510f130340c3c85d000000d50f035001c80c04d03a0201c20381c104003240d20407800b00000d2596113038100380c000290030302d11485410710822107001700d03042500c24010f021543c0005020400349 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 163004640 1250 163003390 163003397
    0x60103031d21070503031801030b0312040905040204020417060103050c120c0906010903080d020a02010b04020a0c0201080402150d0b030d08071707180603090b090c01050d0b040e24060109060f 84
    0x8030820300d501c524080044c2d00507600350001080c00c84012082120090150200b030b241840002c00803010103494064100340180501c0302484148280e200c9a400326034850b2002d0001445c2640798007445080c120703464061422079200354014410080c09000980d04d5541c242d4642c81e03442d200e00d04803505c0b4400d1014040c000e142c1c001c0090350381d80c401c41070400159089465140c0d217103000c01502c1c0181d030080d43c0c020702640c2805106006810035208580c2e058101c2d5640301000303c50b07075004548071580038100b681d100c12074228002c2c40071021743c02011141c03a1110001034400440050504001c0ca504188061015410404c40480c0d00010002070007214036404999541d07540905550501880601c0d440380aa040e402245c1d0790782590014070030701c2c00b4241d00d4400c0c1c1e480d00c044a40c0ca506200307860740022000d011140010b10180c114591000000b0f00c0403840500000e18140350070340101100b202000c0512881a5954a2072071890b04440280707003021905003030050203030001061034048804c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 163005890 1250 163004640 163004689
    0x20c0c1305090304050603131e0309060c1a0a09020901140123030705070c0f0b030405010e01050114011d04051f12031d03011509240f09090510020c060103031d 70
    0x700234508410804003070703008014010060020754009034044201d90210042924200c01103900c9000c1d501d5140010390101103681600b604050522aa000c0505803d21040c0c81e801a0001641c451062501030b0140c005d4aa401c030851400050520503561140d03800c90441440c6640c4201c411000c03a80d004500741090f40d80c90107189132109404c0016480021107051380400400e200308100011b50040380a940280003a168075800c25007200c8081c4074080341950b0390510141c00b540a8000c01039454123103612401320741c030030380049820b6030707011100035107440140156100c600c08000901006000101c1030064220501c6d540640b4601c40304254115034482d482d03c024181d9000d40003544180d850204c0e00607403590b6849070034060b002000c40f4100b0342c505201c030b0040142a000505048034a8042c0c802c030b82d2480c11100c64003c000d100d030141c58074010f61301100360040c1180000e0888001404c010403c030340c55402c0052007031501c00380c2043c842c4080c9907030082903030303c4a241d40748040194064000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 163007140 1250 163005890 163005901
    0x303020f01152d21060c050a0804031103122a030106120902060f071212140103080307092c010509010509041704050d0b150a0501140a090504020c0c1305090304050603 73
    0x344041c0d25031190968455000504c008030041030220300300e480c40f9200c01d00c04000e0b426020f0f10f45004490010000815030300010b004284901c80c10550142c54800b50f038540b480091842e640c100c4122041d00300e00000500b10b10110000500c0764001c036000c010454255410700c45c00070300d00990703071594414068854007610190b40c0c5500407145072407440d0740c0a5950ba0300b10314000c03c81e640c4520321b03000452180c110320340c0d1581e69400b992032040e034941d040c02c00c40d030300310380d202d00d8281c0000e03069030100b024401001c0b036030000352507200098214144224156200301e9000703030060780050b0400c038040d101a01c010000c9460b55540284c20651048210160208002000c2c8060143e41d10581d80401605050b6040c0002070b070740e503406001410b103101e014407580018401c810400340f140d140080d031398030103c2c440007400b20050004056189081d4228079508e0f80000c0a036040003515107140e030000e20b801c3c40c030341c54152920307048851001c1c400d1140b0314120714900d1300d900440c480c0b140030b034000000041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 163008390 1250 163007140 163007219
    0x303130c09020d0f060905011805040515040f120302040e0705310807080307050c10030b0307030c060e010e060a0e0103110f0c06091b040c11070303020f0115 69
    0x9094081c0c4110340700e500800584010740502840111120300d0840007003a00c034403a000eaa03058640c50710301e5050754000001b9200040030010803c1d42e00b401030542c0c00d620490030b2442c00c1d0255020300891081242c45040080c80c0607109280d140a1501c100010400c8034803c0d40300c1a0b2025990030041e40b00c0307200c0c100507074403540c02100016001c444556091440100b0b90390b0801541e90510454501c039031540b5060355240f0901d4800b401680c88038280e880d0f146400780c0901d9000c80c075403402041c45103200000c2031070300105800c2210341a6402d50140404c1e50710040c601d5071148246400703040401c1100116100e0b214004400c810071007943c05103240f5900a4208850007502c0f001220381d00c0c12400d0031007820b9040705011206900441001c245044000200c8000c840c003c5102c0030248203010007000024051424a40d040c0f00c5150320340c5506080c02d10040d0015402600602107907a01100c003c2c0c00c403010780c1e40b4090784c01d03588c820603c4011400f204500c1400306007003003c91090384600d10720 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 163009640 1250 163008390 163008413
    0xd02030f01050a0203010620070b1c05010b09010e0102061510110a0c06110303040b06130b0303030709061808030d11070507030c0e06010504080c040f1b03050108060c0c030313 77
    0x2900c0075070800b8288040415160b000714100c80d5650f807084034800101c07500e00c080508510a9004651080c4428810101280c004084000c035007101d00c00c861503d40c05c2507041c1c1c0d009030720aa100f00008981c88126503000031031207405050910180a0340e25069050240c503c1c01b0404290281c440301805801c01800303401110700010101c0c003154130315003140c0717024001000c2c9030003914006030f5104861840040000182da01555010f40d200c0710f6541d580c41800a14001c00fa0701c2d80c4040c0d200d044c00102602c05000550040c10745a9401d00010304044018004032103010144803001f010110401c002d01010040e0303501e458803103e0200c1c44440d010b10030301e008c0c003c25402400780d00641e44c00100704580c00d240b05085a101c5034818000c0d580b9000196200d0140e03114503010f41d00401d0f410022807426a00807540061040d500044405d403103004041c201031f0780401d5a0200395075400501a5490070000b56920840007140c042ca000e01040300341c0c0c3c030f83c0005007212852400006401e410441203061a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 163010890 1250 163009640 163009663
    0x1c06051f0b0c011407091401050d09031701060504120b040c080706050c06161d0d060e0307030e0301020723030d020d0204050f1e0607110612040218010302030c0d0203 73
    0xe81003440c1d21825110040d40c407200c46a000b9629040c1000b04c2518541c40f500d200309002d44420540e40e14100300e10700340103130b0354072001d0411508114401c081c0b84c140c41991f10440c0203070785181d0300a0034002c402e41c020700107800c40024801d0600003048801080100c041100307034000d910018035155841d141d401943c940d0011182800b5200b004224586e002d4003400c1c51130100340880c0c4981c0c4441010401119203d2407400000d101d1581e519100d01e0f09072491022048040d004c0c0d0b034010394a8840108032462185031101581000030513030145540501103e0000344118000c51810041b580c889030004d4103071600041f01c0c070100c451403030f541c40148151204e4084400040d9914150b800d4808020b500c24050342d840341b860103280190f1420000c03458000c0c11a01e00380361292035200400c02419400411040341c1100c64034004045d1510340074013521040481244c11b0740c05040501c10041e0450040c082000780601c40d40040015940c0003540d403a0700b100542e1111040d5406001081c242050401e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 163012140 1250 163010890 163010941
    0xc0306020a1107060305070207050904031709030c01060e060a03060b030307060203070903120e0904030e04091a012c01030201030c032310050402040b090402090f090f070e1c0605 78
    0x50100c01c99030444600000101a0000e80f40d2064580c4c20a4084440559071100113910461043c009401c16080064015000f4180801c451300440309401c92500103c3c1d60401a410101d9141d058940074001d007800750404950004891416030080b80c5003091a10002e0405501c032000e100182d00c061080f603401316040b034400c0d0750700d02d003549000d0315411030f3740300c1203401c0c111030a41c0540c0188508507000358402c000b0300b000c11f5919a900d08403683e140130030103242c1c401d940307102140000d201030304486e14021114008280d07030340c034002c49244000924035490003035114201e016017846822b640d8040c196642401c0014003d05158400c070000c01c0840c040540c801c940300c048e100d017903901c100380c01e208030b10700c007495400c441c0c544d0309010030380c015031203040b00c0044144192982d13842e040e00605900a4054160010000400d00245003454241c60704502e038031050091240312075000881e508450400e0f101c5040c09401c15444512120400001600b61f6655102094540e1031401140903120407258 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 163013390 1250 163012140 163012147
    0x120f0e0703060e06010501080705030402010c0203070f170d090303090e04060b0402041d01050103020f04030b04020d0606061e0c0c0905070c050d020c0102010e1b2101060f060e090f0a090c030602 85
    0x90b05500601c06108114160300c40d01c8000034056214801e4180324003141d540e40d80c1540c039164010360380948001d408030381c10301a210b000b00c3c1d000d40c005000700040044000760341d1f07404130404100303092110302c0640100f040101c40050012940184400040320110389818071550b65a0818100602002e00701303a07402800050001041542c849130308480380004a19410030b6607895005408920030980c0c0440003140503c0104042281c62448507405800504800650f104031b81d0b4480864413140c100e41e0111350034004e040203150801907070b08105a03180c1050241030203181c45080c844449886843d11f0503449a0024030f0241c85000c1064911381d01a003120340b01c0d00c1140c40030b91600040c0d10b6160056281910b1b40b032140700300194000c00594101100700c0e0088c2c0342002d01c4120800e2201416500f40c90071950300b1040070911491008111030011300c50890b0034090024105840c094009200d80254020301c0424200460420b4102d10801000140c0700f91601d400307061200d0f03552010b0416803020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 163014640 1250 163013390 163013393
    0x7081308030d060e0601020c010e0f0d080703030e1b01080406110c012f121b0c0613031b051b041409060f0c0408060109020f04030f0f02030715120f0e0703 68
    0x10340000c0f0a8a400540e2070020b60384d2440120703907542100981c01e0008018014000b014200b0005100740d02c03202410b0341241141949680c0364940c000074048000a598128004181d0001e21950140c500f00c000f00c2001c03920542c00003000600090b01c042c1c11169035100030555010150704540d01132034818000d1009036600b00049110340c880c00e0a078401e003521034011300107108015048031111515440d40800544590b4035400c502121040d505a00c44001c00074043c04410400c401446022021400d200e0680e051030010b02c1c4c842c001d0b9002c8081c03c2000c039a400000c00100b0760340b4642c1402c02100421840243c0050058603031400d209100d070340542c0600202400c080b81d42c51044400c802d102103c0e403555000c8110601c40d074825552503810520042c050074006400504803540401c00c1c1d07505064880d1118007071180703413070b9084500004401307080045013814004a40100b26500420320900c070b4100000d07002170300c40d03901031041540e9104044805002680701c03040c01c84070344084170f04090700c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 163015890 1250 163014640 163014667
    0x10140d0b0904200102070503030d022b050702010c05030402030303280c0302030f0c0c0a030c020f0405090f1203011a0c07080f0d0e040917070c0b0a180e0103080708130803 75
    0x50022003080c0506101900f4441d5000041c000100e6030040d005510700380311007580800039041000d07040244420700580d800700142c40b44603140c40700395640e00000c0600342030001031300b1200e40110680038040140100805690f010059940c4017020b984502c99140c03078025102c070513003030009a40d06a05e1800e820020351036410f0380617600c10344006c501044551a2960140d003d400307004100e0a05038041068040000d104603131006000c0d101070402281400d111300020b06507401103d0b66105980308003400028014200902d100595440707212b5440d55040220070188410013501c807607003012000929202d5444c0c2040510000c1100b041a1340540d44038820b081e890349408010708000603004624001145418411260341a901ca150013103c4010040d0034080358202010603a6080d0150000040c100004d500400c400050b540d940901081d0003a006e0f01d406445411048004501078010301c0011842d000729020990422815600c075200649400f5101c0724907004545a400045243ca810300301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 163017140 1250 163015890 163015913
    0x302070308010f0e180102090301020f1c090203100b0613151106010602060f0429060a080f060f060d12050a1205060f1012050f1510140d0b0904 63
    0x401d55400c80207903601d00522803990b405004070701c2500311000c0480c0c1020841c962800782180c0120015042c401440300003401c982040d1000032840303000254510340c3c4151110542d0250b00711410401c600e00442c0c0211303542c1d0020079040e61280340d07103090320704603a581c0100f40c174050400c0c51540c01550392640c0c100181d80000c604c40c1800300304064144680b030a000b041d220b042c0d950310341c0144269615802e4024203440c4c0900160745a9010b15442d696180300f80311307480700140150396019042d040290600c8903a003030310350028200e0382240559010950380420341e107030000001c0000c101f0326210840010382d44041400001c2071011615007140031540c100010f0012850580c5602d03844401c9280da407401d860f42100d4195006004450a40d420310302808401d01c1c021051030080c2a003841500241c0855800b500c001d00400074000401c08030200521032078440660644417070f0700e404030006010700f0340042c825940500b0307200030504071180302e015031203004078810007001c891041c20310b400c0c103104010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 163018390 1250 163017140 163017143
    0x90f0c08010e090307030e060412062a0207051e0303120703110711150c0d0206190903090e22080a180819050102040510050d0b04090f080c0a080a030207 67
    0x1500c62000140003201d89044501c00e40398200614508202a50125442003e54042c0c0d68005002d00c40030800301c08500c3c0040e0b809101d4a4001403104541541e08400682e2120241c03000202089850141d0790200328081100c0d8150b42c1d012680403100100f0502d000e80b15205601352101082d441c0d01000c4100d8060301030341c9140ca0400c2501d50741d107500740700b500c40c03030002600300c0c0c0481c9500e100a003400c0d050007403860100991241400e65900aa030b080c0f55040d00e00c5401a4040c0050110010b42c090017641800782a600130802001159000341004079948a41c1c4003000c0c520340019440034440321340300182c040c0d1919824011041c1d182c034000a40120075a40c0004406204034083c0320080100c2c00306444114008150104001207549a40048410111401d540a000000e01030325903200ca0100c1d00c9446e125152180d8a0307191001c03c0310301c2d0070040c9118a003400400e001040f08805c4007045281c00802c0d49130f07201d452600107440c00000250041c102d40000400d4403100b40c0c56800b405006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 163019640 1250 163018390 163018397
    0x1203020a03031a060f030405010e03040801060f120b130f06020f030406140f0a0b01020a0203010c0c0b0a0b09040206071b060518060c060a0903020708070603140f100302010509010306090f0c 83
    0x280c0b00000c1d10103c8600c00070300c0030b800030070800a41c003812080902560340030707101d60008955031452543c0b00c2d041d60007942c08016140e441c0c04043c80f50144000825000d06848900503003141c50f1030700e4100e40010080c108080700001c444001c42448501445a030025410400540d924091824400c6181e40704a0342641c24510309206141c080541d0003040d401a0400088400d607030302c8124140000b042d200650a0562003440449801a2020f029407a00384040d81c0302c8408400b0342d03040185c20420002e0021650501d041503085255450445c410703001074060b0f8206440790544c2ca8071445c050108224040d041007288000180698481c0007010920007900360407440f400400301740585030140040203980e035007051001802e1b10301e065000c1030035140288125140e0690b038801c91403d210311b0b030708400c6c0001c0d1200080484100000a03d43d0800006180642c0e5480c14141030054141c980c00f0003810000002402d040316803113500100007401212a003000084e040007480d1005014803010075021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 163020890 1250 163019640 163019651
    0x18101a04060e06390f0a020f030a051c050c060901051b130e0c09060409020c060106090e16120609090215031e0c1608030402030111030105130f061203020a0303 70
    0x21810f00c0320584d58404500162145807000040101c2e08002125044c0d1980c028020318900100500304000c005c400c900b80c000e4108a0a540140310980c0c54409079207005e40e204088180c00907400040c140c40c0030a2820340b24107110f0300c000089800b17116110115070f451041c1414010401c806500850080388145400424102c04848810741401844074240c60140602400c00012405d00030761540006601c0c8243c0c68803100c0d4000031910380207508200d03400c660204007460b03000c6040004070f000d0034860070080801460042410070480004080c40100004190350305150b41c090075080800b0110310b40d080c0300c5a91600b1032a0028810b106040c7d00c10745144003030b8010140078070201c0340503011000c4500d01000f04074050b14040701d80038114041804003001421158903000485030011031041d00601e0fa0b904041c0109803c4d03c078280740000d01303c1c004000401c041d0b900d0401c0e8640c50003940201050604000040200803d190380c030408151a0217030801e010181d0100b81c40c00d51622940f420040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 163022140 1250 163020890 163020917
    0x30a122105090709020705010b030703030c06060902071e230c01260c0f0705010f0504020909010b1c020a0312020303180607090509130611040513050618101a0406 71
    0x2600c40580c0e40c20202c3c1c008400511010b0095001018640d000d01d0000c2021075100021030b2614409a01c29400903000c061034108024140c001e0f440244510340040d4240039054403a100c10440500300702c4494540c0410507020065900f010703440308a144000104140b449610031510b0b003540311382450000d01504043c100300010101c1d203000071a803004006c00990f8846d5603204056000c040303480d51151080c4900c0c40010030074001c940c11034440940c04074440c1002d205100540b20050900001641080004c0702c042e101c042400071180300007900f00c500030140340041030f022003442d04003404849104070f5494000d43c00100940c0201000c2006500003911030042ca900c8007800d54151000440c100801c000e035260015045400c004601d98401c400402542c9110032210212034100c010100031804008520b01038204006205004500b4001403900000142c80c503a0740600480295064601040f00104841d0006002c0c0c16020810278410a04180010380d98205201303841c00101c5802c4143c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 163023390 1250 163022140 163022207
    0x602190c0c050603100905090318030318040b04140c07120c0804090903090902190908030906030105040504030903050d020606030c0a150e0105090307030f120305130809030a12 77
    0x14403468010600078180d50030803040107090f038805000d207078813104000c0012802c01c0c002d10800e40100f081000943e642d140b81100168003141030382e02c16101390003e112180341078504000d100c9815000701c0d4001968005100014001c01e40621440b1003002c106041042c00e404040041c44114042c0142d040c1000e11044e045569625802006040f40030900c000c00c90200d151f00400601d41c400d0030041e541c940c80e008030a089130015a0303450f104001d40001074400540201d03180b00503020640255180c680014041015880b06200f0b85000c0c0390b41d000040c007454881c82d09040915401804d0365020912018029034400096401078031030300691f04130f05903519240341041308541c0c81090340d00c880607a0084c25236035081d103841d42d9814003e0812001c21240d07004d10a2501444c41205801100d203400c3c1480d041090308580c0354411b240c50002809081401c0441c0074a080d68000c8140380e641260b08042401d0203c00c10004010320135007072503e482e00b0f0b044041030550031114665215103505942105 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 163024640 1250 163023390 163023407
    0x3190215100503070b0d061203080609090f0d3e06090c010c0605071e021f0204030309031506090504140105070c1112150a0c020d020106030503030a020304060b0409060219 75
    0x242d6151384501010480b1001c003034003030300300c1c11b0a2850005480c0e0b503400d5460981d01a90608a0000d1014020012285400e54085811884400081c00c17480c0fa540c2109075aa5020740c88075091103411f010401040c4581c1c048000805503415041c41c01c100e01c084401c4a0b00c6105002e09842d00560f400210640c400040b1410801e80580d580c0f6003c807407644400d001054045c0c071820030890f40420520705409844948040012103a006106084039840c0300407040500541707450415004210400101e54891400c4007034a81115036628007400290554008080704d5203e240d960b42000c080000303200c8220408136081107130030000c0c4810b98500d00c08a602c10020345004001032281c5000d0102411705240001c008107494044485440300c90026592001c0201c5190900c03540b81c8440c1820075905001d401c110140d03900080c00413504655500d6103d010040c5081e212a501100040078400c0c80d80111901c050050030802c280308803410500081c2d80003000306482007403440b05811038584120841c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 163025890 1250 163024640 163024649
    0x61706090a0312090c030b070914060306060c07080604060c031b090e060a0806090f0106050607150209131b0e060906120a09050d090302090c040b030f090319021510 72
    0x181c821404142d60542c3d8030403000080c03004199481142400007958106410003035801010703c03030103e01e0300c48401410704c4105d4001c9880c0309000d0005c5021900d406040c0c0388c01c40c038219005a100d0441c01314091409045501610661060505100030b00225030300100040080b56020311032121620201c0785146085180710001a084d0001004089038941d03a860300518000c00041c00300b580c4446143c40d000d0140c4180c0d0842d0041143c2003046c034001d10840c0c1c020001903031124101f2805848200907450b031000503041d800c2c0c0014940085aa030070004407446803603905d04000c116031602d000f0030b0000a1480b0007022035007000310403000d450034000b81c8a80c0d42004224a1422030a81c28542a040c0003811103201961505030103000101d0500107480182c1c02680c030500020302e9801000711025016014050303202c8200300034420083d40600300d0b54001e440c2c226500c41360b11900c2c8014514414912110060041c940040c3c00481c1e0108440b94082e007100c51010380da403942d0756920142000e521a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 163027140 1250 163025890 163025893
    0x1060f05090a09030306080d11010c09050303030a2301080303070e120318030102070606180b010509010906030b0f03070902041404020901051e09130209041401030507060c0203030c07080106170609 86
    0x80c0501d002030300840d0f0b205101c0c1c9404100e2aa84110f00340c40c0030809581280490580500390002440034071802d14a00d90b40d1274000070751807400000c01e0722880b02034021590551a0b01101c0461401c201c40351031442c06000c0c0c203089560707490b000c00c1d4403030708180c8a520000394000b80d2140140380000701c200c031290707002d0003071440c2080c5402a644a03c000103c03c41e0555024004400490010712400000f0101c0c8900d51003030000300c25040c4215040400c0c0141489028000a40c0f0741c2d90120601b000d803200390800195110750b9400040c0c000f6030007211a0b90600c1204c4011407000c10a13005030040b00c0a070128040c20712a0501080168029500c2d41400107a09001040000b1003541d1070303020400c80180403c0c075020080000c5110300c0035450552240c6900012280c1031400c01c0d200340c1070504d440f244600c42079411980e0780384d202c1360144078210420030222400001d665081c400c8507405030080d8101c801440d135818026000c2d200da0320410702041c0f6100c8140344000c42c0410f8141c03181c4807900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 163028390 1250 163027140 163027159
    0x70204240504150f0f030302060919080c0307120f0e01020316170d06060513090506030c0103020a0201020d051312080c041505070b04150501120203060609090a021e0301060f05 77
    0x1400b008160341160a04280d80e49007000402c1003600f244440034022041c00e810030749045080180c0340500c081c0c010305580c1e0007101c1e000400300340508080c2c1c880380d114804503a11040d000189285000e016406806011003041c00a001c0390048a1000340c01c08946030003c800c0c441c40010fa07164007440301c4280301d82c205800ca0400150040325413541c02080782c501c040c20940340c2e81c981001c95410340c02c0040800c0700028881c2c2d980d1511080d203130051115010034030043c6010404262110340e010111814150003281c4280c00b40c0c000c1d0183d401c2c002c4184401c1016140c0804901c165602803001647d02c1c3c540b11480c0741c02c940c800c40ca8180b058900c0907450b4a02440c00e152001d506224130306400412000348450030015a4068840340628000c2206084032500c060100f421640180c1c132404c42001602d00740001a1800b088403503109100302c460000b56034410701d4642c104161100001c4d800703026030300084040c142c00302c02240754080a40c02004120f448840c01c0d2406100c2d030245076031104006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 163029640 1250 163028390 163028399
    0x30f0c0507110d1e05010e0705060c190c050d050c090106020c0109060e031504060209030f011b081905040c061103130311010c05030c0703060f110318030c0304060507020424 76
    0x24001e80f042c4520520110b518088814828141c03004110811070303d59442d228130329050007007044890042c1c2011a505841c141d000e20815948880111a24064040c1000f030b0209218070405e480300180b0b0050080303080e036805032a00940b2080c1e66652030f1301c07805203100041400b51000440072803032a81038495030155070900c44280c84211440c6200d9138188140544512041138284030a0701451040314056242c4582c982010f090544415000800c0e030314041581145007401018000082e4850030080f4864640b40b9040c10102000900022454204800e102c02c00c551903228000b11500c503551504c114280405050b01da00c100b411b110259401740ca8144041050307210700040901e014106484510000c2d07039490300f550000d14070300c0310b1500207400400610202c3c1c060310f4000302410300200042d414180d1010040d0001a003003540b1802c0c21011442000b8080007180c2a42d21090200d94a490b51901c00a10650050200324052802d185200142043c0848003002c0e02c030907405082c0380316041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 163030890 1250 163029640 163029649
    0x26070507020616120c0b070e03060109020a0306080f06100e04050706080903070501090c0f0501030e03030705070807062c0309030703060c0314090a050d080c0412061b030f0c050711 79
    0x80038400300c0c0140000401000a1311850b01c400c03807000b4944a0204400b401e052101190a00408460a1108600358200ba584e000300383d17a41074800c030000050312805001e404078000c1025402141c0c00380304840301c84850590005481e481000d20748001000c154441c160449044030031381d0b00904e142d12585007404024081e00029030311514040c00c907410201551101400c0d104c0a28041e40c00403043c000038000c0e00d11083d0401c01070442801c0c18005003c403401c0090b42c0e4070000f482a400c010001c1109000c100c10b07103080395079803a00000c043c0b101d040500d0064000034015a410b448250100111990307440b808400d40c0d401c41c4004004d88925840d41e01c42a02600c140d004140130169686800286032141e440b40900440030400184100c42c0c00e80703062858100010015814072034900304001e000c8031000308440a542c00c1d0b40d00e480011215183c401d000d800c91343c081c500c1c09100214400d01a40c0d250b0b000410315560345905100c4042000c805940a10507808094a160300d0b13070900d0200c0e0b040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 163032140 1250 163030890 163030897
    0x6130f06020306011b0f03090603270c030f1110110a020f1c060603022b29090313051e01030203040c090203071e030c050316110607260705070206 64
    0x1c117040203106043c004e0f8038580074103282c03081110030f03090180c064401c2c154000740703800c041d21003414200709018028500c07a20300002003100f015540400000d0304d040026040b503150085070b22403100c03200d030403542c034220300004400c0440e00d004602d0041054451072080109496074605036010b0301c60740c8000d4090041c1a100c0b203480a070421050300038000000480c81810b22018000c0c2400241c1e20300f1841000b99425801010b05520854050300320b82121000b6003c5611503480621f0000110b0001c0807094607400458445001d07101c1c200400450800110003407880c0c4004130400e000a503160401c05c5540c00e49107803c403d01d03040404100c4504d5000c0c1d8000c42d00325024031100015a60744124400a031380c4225400c4000586074070407920743c60305200b484120740e80315080070300100c494100e005066001c028854207412180310a00035100b0300501105000b205c06500743e900310f140284025005941d616640290402141040c00c5007942c0803415038002e003041d5507500d14114240c0c00304281c81e007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 163033390 1250 163032140 163032151
    0x10c0b0a050603011d0d0306050a0e01290d09050c0108090714120d0207030c1a030a0908070506010e07090602030301150c03021501060c0b01050603041203050a1410030506130f060203 80
    0x642e550220203070905c0d03140f01690b180c061003000b0a9981400d690040a8a00952140d801010005414082400024080ca0549020400c0468002c808820100c40b0b0343c04030f910320a001000041400300406141c1103551602d004a0403200001100001120045011104148036810420040c01440d034403260840074054005c00c0f0000b410001410760741403034207d940c56800360340400d00c108100500400040011f058105011b0038112020300c00283c90302c8000c01e8a400d096486525004022883d016120b520390003e04681d40c031741c2c5404103d030301c07544141c07000c0340850207820000841d54400411a8142e804010140880c400702003815980501d803650100c2c00d5028602051441c002064000743c000c1c182303a610241041d986042c28140500306070415801140304008100116200500070000500c1d1841c002070705540d1083c43d0300c020329210201088c85241030b0148681b00f2440f2604000b583e02440070380700705032180000944006000700700203241d0382a400c081c1c004242140d005c0e40d03004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 163034640 1250 163033390 163033393
    0x302090702030d1a03190314090406030605071d030c01090b0a090e0a09060f05070e0112020f040b070605010509280b0d06090b0a02090a05040b13020c060114010c0b0a050603 76
    0x440403650301d03003d59660781c240d011a00500b40c2c41356810315003001441c9000e8940b0950100f00241910b004001000462051894010000c0c007007030b080e140d941c4400c00131a08480104078509203131000501c10810410807440b42440070500c0c14061601141aa4107800140c40e890342c92450842c4405954000d1480b06043c072002100005105142e40d4105104425810001481c045240381c40c000301c400104e10354100c0c61034a000c00080941040c0140840d041c00d0030304680388001310328040080e10580724840400f09000c0707000101c00ca80c1c00050300c02c0c5481048280000d07070301e907410f0194411040b5240d6007800840b082d01103003036446640040340110b0000010802c001440c2c00304054080051088984958842c2e0100c03d1002800c4241c1e00040c0a503c10351a06003803000085100741d081c000c880c4200d55440d00c0c8211940c40200c01b41c03010b50701d1030081d510303610882402500d42d0024480d0301c01481d4280240b100540c41881c1801c1c200d640000640b0040d1035034541c0c140204001420799405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 163035890 1250 163034640 163034647
    0x120602070b09210414040f0905010c020c130e0c06030c0904090b0a1506090b090613061e090501080a0203061c060222030f02090403020703060509070302100f0801030209070203 77
    0x10030700d460030395407089058800911442d00b034400c415146080c031000071840d00e03d041c0400e024640a1904480c100700c0d044502084020407980668001d01d0344980003012980392a2812200980100e040105c0900844d1003544227022908030302d007030f52102e04903501c140d080b000208140e4903000025640101801c040d45061a0203000441c00b145c2d00c841e0b0682e0600742e020208051104a070003144030046081240d101d880f071031b0101c0138043c0300c050300403820300710408203007510603840345425518503588d9540c0b09107956507600c9c4040c00649030481c0414000e07036400c0700d44044032b005100e8001165010f03540c5844940d50740c1c0e5400000e4101800f110350028024040c800e2136500640703100780090084000507601c544101e0030b81c03501407081400180c07903030103244200f010924490420700c0c510f8060315036139441d035200e180407401e214445e00014030303d5240c070090100400c00001c1c3c8e103003604e2003511100c0b80087c6000042d80d81031114083c03c000211098010720050514110441d0014140e004507802e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 163037140 1250 163035890 163035893
    0x150d021f110d02070e1e01050906031f060527041709040911240f1e19030f091110020c030d050702040c0801030201140f0f070506090105180712060207 66
    0x2d20b03015603a002c0041e03111070018450603143d82c1c4150780106032103000c42001440e10039000341041d0144240c512507040000000c225407400d00c604e00d0451011440e0790f010042218a12005002500a5502a80394503010b130405000f003034450020381c04001e00c41c64031030740e442e5903c0e1503189138007814400d480b00a0026010390707211070090360780c0e0512801162211141e400d051044482d070034004c0141c80031300c2e04507880c1c42c02d15000c129040c62218181031a6a14100649403002c0e41068480a00c490310000301b102012010042d0111003070603668007800a005000f030303141c1c00c1c0ea0480a000c0d2078802c880d0041080741ca8942d140c02e00c00c03901030043d5079289003400c00103410310762000c0303d800c041500010110118038291050340788a80040c01c2a200650542d00024040c01200308440040b9100140040f0050049411f039501d54110042d01581c8042614240e40c0301c4d0800d5a140300b1640c00c11010a92040e09810440c2d1081541e200402035a447e00307110728407000b01c0007801d4441e60b608104020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 163038390 1250 163037140 163037143
    0xa020c01110409021e03220c081c0201060e010501090501050903120a030b04110309062406040f06020f060103030e010f0c0602040f21030509040b2205150d021f11 71
    0x401080348071001a00e642030702d1192075500314174001011021104200708101c654008542c6004041d5806014402c00980d150030b0300400e400e50088040f600c5403580424158801c2040007280c09465270080c016141e40301c203e41840c0a082c0a90f0b404589522002d01c07d551082c000b409410703800400f1640c2c1e60141103500c807020303402420b003e0700203a00e0350401078490030039008240c100940d403c2240d1540c40c0c00c2070460b4403a4070150800003422a01203940009400c0071050306a0040c5c028030075030f59169141e060a0160781244204005801a10400040444041051030490f0f17010b0b100c0c0300001c0c00351401180d900c0c0403e5241000c0c03000302c090000c0410943d201505c0a060740c00010f1340e41c40e052809100130080041038079102ca8201200030000658000240c90400c90240d402007140c01e111030008000b8600045102101001184030791120130702500650702446507040b03000180c44140303041c0881a40c9040019400c032400b0400c0720303081c260311092442554480d00d0070a0b442e01000c140903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 163039640 1250 163038390 163038397
    0xb0312090612190b0a05030a060e03070c0b070606050f010c080a0513180b06040f03081b160501320903071d0708070318171909080c030a03080a020c0111 67
    0x292035240341490601c020701c051310031022405400c071a43e03452285800c002039030313484001000601040d01d40d8011200341000308103076400707d507116841202298031603000004a4002d06015650340b4200032000a860a03c800c5d28180d050044e9076041d01c800454803000b40a0340a034106100704a4100400a151a1070003101005407074801c8961070856204100001a145540b54451103085c0800c41000510300031005481241d501403002d513110b03000130101560b00c01600c1440b456900409421040002c8602a0380b02130b11000d0320383c8a02c610320039860105804031003540d0b0000711048001d01c003049000c0805481c0c3c0400003001c0b07031002600d0f1030030030302c408034000115050406a0410f200c0d589410480d499800300c0d451404000e4120305d0340d0700d01c0c200c8100d82000350100403802200c0071403c0c0681d04441035500c080580380c003002e15082008109519500c03d0708400c0c02502da0244039880c001c0343c40700c052074041e40c4002ea03c1d00c81740701480095000b9624800550350311000d66894145840c0035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 163040890 1250 163039640 163039651
    0x2120a050c0a0b04050a15020102090406121401180308090a080c240411040506030c0915010809010b210c0d0303050a0b01020d09060f0903150608100b0312090612 71
    0x74150310020001804400c1c02141c00641078824280014003094072840190402c0b10109103586804096607d070a0340240b20710550690054140704002c101d00c104904e8101a00b03106054880b010700032056614220f030101c040785101010481010b1000ca8421f0350790b10340200100064503c420000e695000080d44424482e0526400c0846d07101c9100703800f8030104044091a2908400d030b032425584100400e25a002c2c841d01c0380303a495011541070742301004000c070403840142911203141808820301070140c424068460002c0d03c484000350f82c208060240304800c0c80302034506810b0580c0441c0d400809c1d03a50040315080fa00c01c0c40ea2007081c983c2c891144440712802a20005414282a0740c28810390310100b10786410b41d4801c2c1b0328050501e501090300c4080318094a0116070030030b81120100c3c1d0701c102c0c991000d0711402c1e060741000c0b07411030f040d4131101c01c1341c060008940046044020702d80580d402e60300d0700c0364075070005d4440c50784000c0404010700d44400003c2859141c80c11010440c0070320341c4203650 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 163042140 1250 163040890 163040893
    0x3072c01080d0216030c05060f1c0608010605180a050c0d02032a03090a080a1407050105070e01260711010504060902012709020711060403030f0806040501060e090402120a05 76
    0x205480b002d03806100c0c40301c2d0399449941401c0a14190381728801250074920a0030b000d440300140711450f21043c0d1082d80c0c01c040e0807581c4101c14840301c400301409884203000b2407501e5440d26000092902d0009152820005034031060702c00c0340d881103061401400001c00c1d0b425065801c026944100301e248c40190b1050000342400c00341c411808040490601d440e850341c850402080041c0048044000f0703c000c0c6641d48103001565600744840c0896400d64160043c80c2c40b000b01040c1c000c200681908421b01c40d80c1aa03403035940c2c0403501e000444a03414000410071440c0c2d050700d11030744000c7c51005210390003031450038181e54200d0035500150843d5421138050304c61503551940c4501319a841020b10942c101d5111005140c880c140042d8404080c082c4540313034034194000344030000c0014119410351140d00050074035446036541c0c1009000001103265881c00120020001001d501e4507200b220306840590b41c900011042220038400c801c3c03005003059074400401c0721404038010781001404c0c0010320410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 163043390 1250 163042140 163042153
    0xc060e01090203102304030e100e03070305030c15070912020d020d0f06050105041109010305040227090f010c120203040309030c0b09120a0b04300804020111010b03072c0108 76
    0xba10140301d00c140200398840b06002402d10000c6540004100323003401048600400d045030608080d1400210307900916014043c40f075000040c400c010022300041c86101054134800c01d11f901100310040d8049079000c0105143c844240300a00d604001400181d201a10380007514015400160a5082420b022a40341030407a200030108061342c040ca500409065a0502180c030505101c1d060500500e82078a040594520009003950342c1c00f0031000042c0c80c031840c0301d00a1000d0f81c0c4201000c0c101102c81c00c10350701c1082c001502c141014891140c804030150b03100a6003444d510b000c4000fa6001820540401404142c0840410401c0c001c2000402e140342c40c00c0d98840005050011034180f07901e101c1525040403d0300d5021918107110168499881642006240c02400345246c5e04611003c1d11391540c08100741c0c00a244e504410302a0045000b40c90b12030201c003003d94100e00341c51046182a8041d0401c4204102005002c1100085e581c4c81000d224510040300200c6401040c0c01d900801440d44110f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 163044640 1250 163043390 163043411
    0x3021c0302190f15050124020a1401050609010e0108030d02090f040e060702160e0403111c0f090803131e050301090f06050916031101090e190c050a0c060e0109020310 73
    0x8044d00c0c640e080b00404240010b604d441c181d00c06401e51042240ca25000d8942c0d40d040d81d510034806c00e500d60f03a1010154000f40d1301500540c3c001c10382121501d020392050000400d4141000c07070000d040341c00c00302c0210b10340078806250740082d400500d50142c00c442d001484044070303a107074001c114901c807a600c0103000300d20380303080001c1c03401c1c4820f0000b091180c400e04080c0001c00000588541c01600f60510303024510540000d04d140000640400701c105c4c000d22803042c80310707612801e540103401c2aa80d51030741c502c0e296041e0503102d12070b019002039214107220041020302e20324040c501c2d040d076240d03514405e5245d81d01d010034291a00100100c48214009003818200700e001e10829410100c15401000305200300b000c0050090034502001d0444074441c0c0d41050740d68800c071144005007142c0445e01c001801d20300c5119013122400566000c810342410098444940300324261140c40351641d80e000c0d4400119180c4500905400c42440d0440d500c8040c010056102000700704100942d6200010380703c03100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 163045890 1250 163044640 163044653
    0xd0b30010c0311040312050f04090902010807030e0c090403050405060f0408100204050a0905060a050d08030a14071d19081c020111030c1803060109020a090f03021c0302190f 76
    0x10354020740d092601e840c408819080b140c1054805881c1c2c4508444030741c0b4a20a03085d101805489140b0740407810015003c80c1c1c1c05a16003240300708520070703203e91001c0c0d00e62040039020349120500d0404142e00600c0910020b24100c65002c0d006030090400b545042c0e02da40c04140c1590101d442194500ba000804001c1c10504201c40c1526440c0c8400450806017004000364041400e8030941001d2a11680072400650301c6502c4503004100042440c00001101c3c030f8040c9494008a80c0001c41d80d2402c0080c106041113564280d21039041c1da0780e6184500001c4402620128144010580095002000b034668000c100542c0e00508007020007000d0606801250035941e10301418600b045904000c80004c1302054503054036042020909620307200c49001e54210909220b403100c090707140c03180c0800000c03c864168014421101c0c5992808410703500d0b070001c081e08651510000307400402c1007005c60f55041101d0407403481103220388141ea84881180e0130b41e400d42010309000340d5070a010b9103900800c001c00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 163047140 1250 163045890 163045901
    0x2523150406090311102c031903110d0501081e120d0e0304030c05190311040203190606031505030105040215070201020a0f030503010e1e01060e120106120b0c040b0d0b3001 75
    0xa9034040600222000d0041c6c0e42c50380181030305002c070212552001012140243c100c1420b1000b01c07400661595440d04c81da07070180c84203114407280750049120b010f00743c0075510141110740e110000186401349404a0009035a84040904c0e1320442d035540741080040d00c240001c00045009800c241d108900b01820080001412290f4103110940d02108000045510b45080e21000e000c80d0010303140da40b028030018400343d09803020700701246401c5000c0f41c4144c150b0b004a005842203080720a40c252600249800c99505179806544a0810425500c02002810080070194410310507034503a403c05a949045034000040c044021413400320040c010040c03221030f52544600400d03070726400303280b1403030500c040c1310410b0003200200480a00310403810744400380c0340c40c00347da400ba000308403586d500c55600c10945800081145d0b00c0101c140800c650300701c45803d480541d098504170a01e081c442c0c540f90320081c0b0601d00e43c960007501c00c06204509040c4010981105049250ba030503020000150103401c588 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 163048390 1250 163047140 163047191
    0x20106080a050c04051e090f0d090602030702100e0a0306020915030f060d03030e0f10060605040b040e1b07050609160f05010302252315040609031110 66
    0x144480460000b0070301c0050070700c080c2d0006541c0003031151200442d941e0100d1035005200c0c00f8407110824800d080200103010300c200c0710341348161035800304c0c208002c131220101c5100706c0b801a4820712541c005854800d4061071814840d00745100071013001e1010592480442d40155045d5901240713081180c14480301e04101c0c03070b0807040064514940031011800c0c90b00c000d44001d00610035845580c0405019078010004501c0802c200d40b401180300303010558410090042203403036414904002507082c054801c0e502a160340046042c00c260611031031009685000304500d8040c00c04002c0da46a824540004141c40c42c010b4000e00001d2800d107201ca0315040ac0312280d5203c010780075408100380e0101c20301041c10340b03101b440c01581c0d031001e845401201203101e4150004d8101d0000b501008c106d1212448069500840d02c100100384443e0390040e10b400c1c01214014052248600203000200540c1c80200501e1090904918485417410b41603d402c41258040c20207079507d201b9a1818448440b0102031138 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 163049640 1250 163048390 163048393
    0x41502130b03041109130c050607050706080910050406021b060c0313061d060118020901020607140d050103032a02030318010c05060702061501050304020d0803150603040606030302010608 82
    0x595084a42040400318496250540c601001040070408840340c0066000402480d0454505042282140300d5111800c12500b42c01c03d903800040504108060760700d19034001002d07010070351810300c0584280000602000d0640a400480b900605491148034000e900a480040c0c4400d1454100d103500542c240050340558030050030061400d04010480c0d502c0641c0401c0519103801c140b5000001d008107100410f600182c1d15181c0c1c110000005c0d41604070307240200c13000c12030310b80e0085a03400c078070860040c103005810943c00141003a003e10b85c0d698400c08124240b9140c800c3d044081800c4540a0704110005440b01c5000c032034010511540131a400c01c030995410004005600007aa6032045100074a01c040c0c8480c03a401c41607019201001707100d90444180e850520340010b009484640403100c071001c4582103400451694030980c1502d205a074040d0040003504c125454809007a04000c182461010030b0500300e40c01170b16158091030017540b0400c40403030010f04500e000303800e5502c1a0464681d1307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 163050890 1250 163049640 163049647
    0x306050402120103120302070b1e160903020f0a260106090204050d110a1d0402041b1704080904091a011a0412050c1206040303060b0a0203040320040c08041502 70
    0x2c442d800c000e10741160390040101c003043d60b00380000e9010303004195024040f001030b4800c00450f4542c1c1040100141c1b02c25120b90880c0d51002c1a50005c40c1305c101307603800007400b140018401403c041214013614070000b00090780280e034a404148000c03d41155039000d03184613010401c40c045090151402034108030748150b0a00313007480f0208202c0c2ca850391018101e00c0c00709003681095250010300e0000f80807003103420b03024800440d40c91500b031076050307170124052460301440b1500303060000141803031200301e80c0c0e82c440000d05c4549a6240c4000c0030b8010740d05c98a013049881c0b400e40da1403241c284500d1060070800c1c030030521008221502c0505030321551440d4418080c407101509904112000d580e20741082c654074814500309145454020214550442802e582ca5030488000003080740c410703446640d06000c4652544016180ba008611100015034400e11050000404203000d8054a003008080c14080026400010f4140e0708420041001314081d0301c24030043c005c41d40000000480303011004d514 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 163052140 1250 163050890 163050907
    0x3010602010b09060a181a060f070c050405040803010b0a1e091a031302060c0a0605040c0e1501080a090201020a0503030f010611031c0e031b030c01060503061302040e0a080f04060306050402 83
    0x910181005008141c50f68a40070fa04407030740782d181c021f000d03400068240341d00d030840e503110610643d02c00403095030780200443d000195803030300e401014070480c0d01900316030642c0d2900101d0343c4142c002d842c9510034060310f2150440c102c19005400c1c50702c0012503407510800c0c0c1c90b20040c400c0e441c11950204100c400d08104002c00e080072130780700c4041d25506a94055484901314600c034204103090800234a002d08010901040c8890305d0341400076619900c0c81c1e144540c0f078445003044c0d10700f011015680403030040d1000400300e910304e40c80a8001030040c0150748000f9101d58505085600803201c0031458020040184403c0e50700211500d0104410f00c000c6140450354040d480d08400c60580240f801603c2d004a1100d5020510a480355000b101d02d41d040075014429400303071207030885195800c1662a02900060524002401500410100c00c6070400381001341c01b130101a2001403403036012b81c481c82d4902000200d803040106400500300364856140c0e800c000c0c1c014255222680803510a9006102e680e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 163053390 1250 163052140 163052159
    0x30c090d11010f18050d02010507120804110415030605061302030103230706120f06090c0c1209030c050f150307080610090501020d08100527131a1302040203010602010b09060a 77
    0x102550412508110031110b41e100407221480340b00401040c02c01c200052f5405142c02c101d440340514891001d244900c103001080c4402c035a0130640500e00c04000003c03c10102d0010351001c0e4000c00c1c0545100c000d94081c801c00003d9074020b9000b140c0307585240160709001c0103c0d02c500107030030000c80301030040c0754600742c001803050b0000420303010500d070f4402c5440103a5000fa0b000780300030107220106200486c1000c01c00740500700188001e5410120840041d0340ca01c0c0302c1c07240f002c1983e40c803030000c020b903a04200074050f880401030354980d0014100b1084400350f0001c10041c41c8114126540c48500340341c000f00344008000100304c244203001d0742d5502403006070b801007541403009929141c803031003d50ba4031007403003041d90142c0c2c01a50010001ca0203e503008072007000180740104a00c00384003045d207481e4420006086200c0000d083c14121000c0002c11341603110055400905031402000f1112140d00003900f02e0f4802e82c0700d8070150703544d21450200382c1046c04000d94404421503003800024503050080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 163054640 1250 163053390 163053437
    0x11070305040f0f05090a05071e0509100f020703110607050a0b09070602060f040b10031704090b0d020f130f020d06050102010b0d03020d0c1506030503030f0a020a0f0302030c090d11010f 81
    0x4200703072611f40001035046845201c1c50440710a070f1440d0711400c070090340c0d0050102e40c462188940105220302007840001d0085880142d07100060f401401860701d140c840e104040b08141c24240c1c010010088171004c0340040101503507441c099007080100d820810125407400100c0d501980640d0070a00411220406080c0030960040d0030004214443d641c03000c0c51440040307150001800804000c191030401d40d100401b410a65001e40000c225100180c001c0000300ca080e01002544000c0e0b240c00030980f8184a01808100449803074080b0308696064a00c4003a6000300c0740a030501c943d10740d0100142c0d03a0902400d01718540540d0054420280d40d100252078500310005201401092040c80003006a0301886c0c94a01c461031f80f04100369503d80c5042502da500640b100c40b80080303404049041e03441184203c2e400102151945000b18120703a201b07801940000300003240c003004c2030085041945985899403ca07500c600891f40c1017036403440001d01103540c0c100c50b200406c0034101003031a0307180800991 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 163055890 1250 163054640 163054651
    0x5070201050d0905070b030a0b09130822060309060c0e090c030c070f0503040602060105010206130b13051b0a140f040902220509060a02070b0703050a11070305040f0f0509 75
    0xc0da6540c4402041840600203011001309140b040000000b8401c40318005580121003001c0c050100300f01078410030221506c151200283d00540340b18040020b60341c14000e100c1c203080b403074548082104031058440d090302c1d1a841003003c29116030682c4208900d52003411030121032800d018031039500c20400b003407000700d0041c001640302034000081801c0007181c01c140c07500a54000c002d40c2c1c42070081d14144d40c482e04a4031035800580710380400850f880d80041900c9104500b900002041c0001c540c4900300b900b0005481d181868484802d0700000c038500b40050005407854051402059141005000680407250711075640d09a907200c0f207a007a1350324222001000c0100f26008680150513000181c039100940c0300c0b28000282c8880419030341c210300e40203240f1540b0b0306010b4403c16900c2c40d12010030780c880c0c048024641e80c403040004000a02a0380700f5900704560000014000648881d46540d03030f400484117a012507408038081000944c45062003028028140281c3d40382c0d85044003042003000003528 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 163057140 1250 163055890 163055897
    0xd0f08120c180f0f0d03090e0606190c020d0f030f0e010206060105091e040203091005070c08042603030108030c0601090b030607050d090501110405041506080c0d140108010c0207080d05070201 84
    0x794860f450b503e01e4000a981c000040070070303403075002c6490007074080c03007803072145600f1504040001100d610b80700040e1454218000311328661a80b808900700c0f02c01036400c40890b8030000501d40380003c514a0407015000c0f5200c2e481c3d0079880458004003415228103682103904640c0424200007042e40d0100a0320451441038441d6441c121501031800681c02500c1103981d00f0a02c0801081800364000812a040a0724513504102f075454416003111480140d2101038010241044200205d40d20400208581040007400c160219562211281158400e0f071100301d00d5400803070b240f0419281032201c3e500426148804004002002c408039844520003030484060000c080707a09800980c40741c000205541c0e100000b0441080e1081d0380a8560300540180ea002e18504030103030300c0a01c401c200f0388082e46d4460729100101c0d5207412070542e40750700901000e00025151b11a0700c90381565a42054081d0103010b0000c1802020440000c0c9414003982c0040302961203041c074881e190f42c001044900c0e440d02031a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 163058390 1250 163057140 163057159
    0x1803020d0c0519030314070503040206040b07150510140306060d080c0f070602010c0917060402040b0411041518060906031508300a1d0d0f08120c18 65
    0x2c000341002e00c05004600c4541440f5218410103926910220088502600e482c03440d0f02d8400c0211541d00081b02d00030740209041105100c126848000341080d688140420054105081020002c0c1c0341d003600c1a0513501d080407818040d07044403030000080440d0030b8000348100e2400c4000502001c01190001e040010001029a003214090028003000240305040b51011556504000c2c002c04a11042c0360000311004000b04900c072003903c1c480070412841d002010541ca9503003c02c00100301c80c9940d50303401650703100340c040a200750f440604010b0091181d101c91100f11880701070810500c01c3c1d04240b5040f181c40b4207010700e5811880d00801d8404501c0c0000d8030105007001c02c0c290307800c60340003107140c1d1180c2e1349066461000e4580f5035070010700ca010004610988009012150301401185d6004240c00541801c4100c2190981c5184070000410400c0f8581c126200c045e0b40e03204900082d11140c5002500d0761449028602036504040501842c91803d0200c0e50100364150035000d2035481486e504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 163059640 1250 163058390 163058393
    0x1806020307021501290c03091012090807060b0d0804090504021306180c0e031015031202060f070c0215030709030b15040b0a030503040b0f0715020a031803020d0c 71
    0x2c02540141c0d0190040001ea42d50f1141800840c4030060801c03030004010001c0d200030200c40c003c003a03581441686d801582040206420000d0656000d15140208100e4002d600d205141c0f500542c1c029a020f843d03a1035840c3e240e8203154080d02e4080c90b80a00525142e0001c900268800080780e045410400c80002c80c1d880e07034400105064011f1200101141c1840808100c44002c00c2403040030640709101041a000007050545a603d42c42022581c160481c14101c014240280c0140748030480e803503880140e15443c4d070388401c00700b0b0044403140f006920100130803588003282d001d113070380201c02d6040140003d40c0c258005020091071402c1200c01a602102240300103018901c8407020307650001c903000d55845c21b002070110800801000500c62410220840102c0c2415801c02003a250401c1c06036160508141c503050362940320300745802445034200119404074250300c0b04052501c0e03c017003025035034850404000b0241c07242041da0300200c0310210031301c03000a074002a40c3e0b89036520900b0005004603a071b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 163060890 1250 163059640 163059643
    0x40608011a07020301090c093b010905030f0403030f0306031e08090907020123010b0f07170c010f06090e3f030402090907140d0206190c05060a180602030702 69
    0xa1610080d050340c03c2c40000e10400600d46540015a03c1c1c1c1c981c00c201c030555900c1701c0e12703599140314214501c40961903260441100d01110b107000000119001284c3d0503450b503941e07403540e84218074840c0c1145000c1018407c02d030b0710010703a504500c91450144140d9003940c85841d00b882c0d620b10b1301c00ca001000b2000c0c804000181040e10200030300189110b80c03d140c030707c00190103000907040c020403500300e00039120b012440f02c0401c54140d50319500e401c0e082020900c02040d4a5004100030b80308100125040038086503210010074900032514004900381500060f42400c3e00c650390000b5a00c01d0400c0360405046d400003601900c8925100004c110b590700c4510b1114034110050140c41e10701d034103299000340308181780000310301035803007500d030921603a645032005901d4201500540d64040120740b10210701d0719007500e07070003d01170004050310b2801070104076000d50170b0045400b590110702d91154081c01d115050145079400782d0001d270181704541030803015026401c0c044c08014560345d804004161114030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 163062140 1250 163060890 163060897
    0xe120a150614010c15200d0509061305030301090b0a0b0f09040b060c060415021b031c0509070303050901021203130201030c0e030c040f1b080405060a0b010c0b041502040b07021203040608011a 84
    0x80c00d2052950390b0b0400308510740685821152782c091441000003054100480c000c540d0106508407014508507403c05440c80702404201e0030f42980401070000104001b0380c000024402003140490f40c99a400b60501440151600307280f42c5071091105001080ba0070740040703500c40e070095010441d80c03a45800303c1c10b048001e02034034504040143e041540303c03403042d0001000307106283c60310b060010108810ba00c043c044d280700711903000c2503400200302000041d00400c0644031010301401600c000c41d040c0141486240c008417580c05402210122500655816100d4200401590301c0c00c4400220b075000442c1d40c64581c60341941c003856880d10f140c0c5a036411780c1d11100002c14000f540942c610414000100341072015034090310240600d001040300350340c1900c2250143e40060b12a12006101c644680d0315030a002402511066000588aa1000c6003417009002809a000c1c05548560b080d0040c07084441d0b503400d0b00c9506610412061002c00e80202d00c5c141168582082206ca0340451021a5110700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 163063390 1250 163062140 163062191
    0x1706040c03140f010e010e010612020d02090405120307030c120e030301051e03032214090103020d02010c0606180c0203030f130c12030512090309010e120a150614010c15 74
    0x51822008145841047d008814000c903128004d1000c0c40d101d480d00342d403600700e100b0000c0d840304c091201da600600740802050351041c000d5094844040d076410709100c81341d0045603141d000030340d14840c2100c0c0707030b80004000c102c82b103404104000c2404000f01c007955a100c1806054422080e400c000c02c50400f03006002000e50101400380c90704c800c10f4a58281100d010000e481c0d1305000d9038040403414240a004040c02d02d0002080c103d041d0b482e41e0244285060301e4603060307041100c03645864001c5503003806004002d00c981e141200c5424811600d000c11100760400410441d0030400911400c08100f80c1415040400c42c1003444507555107280140c214840c03030f4000020042d60b03225441c18960800040c001d20980b107400b00d02c882d40c90240a5480c0d03c10304c480140030403c0b1604402c50740c1080c0c000256405052011100e480c84591200da034804e011404031200580c0b5003400780050722800c0c00040080c0c200707090405541c0041d81d541c0c02c2c402e803c3c034040c0089940c5c03a092440c414050211201900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 163064640 1250 163063390 163063393
    0x706050c040e2428030c06030b01020a0c050103021b060403080402030c030c18060102070f1e15050a11030d09051e19080d060f140a0b0f04090209150c071706040c03140f 74
    0x145d070b803840d00c8140e0583d14400c0b8000310740751400d240d0407540041000d0500d03d90061220803280d043c071005400a410059900300640075400039010702c40c408000c0140518066200c0004520340303441003502c1d241c2d0101c101c900a4008800070411500d507010410040f2a583e4900c116580d1042c004030703d4042e1030340c00101d2848001d80002000b504d103584030b0916410302c0c1080e0011a0700d07100b464001502c019000f0001600c20001814054400e880c03502c0c00c110381b1803e40b4501a8004401c5082e40d20140083e5520741000720460390b50300405030f20156442000000d4803455002525280e9280c054010207480194002551888007859030f000c82c0103001e00ca9800c1501648441c0c1d0b0b0100901040421401501095400701c0e501e07019005a440c0d100702d68950600c3c01c0d090811003000b03500801000b42c0c011144000452030884420b0180000c1c0d025000200314280c909082a032003c1044000ca400d50b03002a020300010540c0da495030300c103a039080f45260404070f04401820b490000c802901c0b120f02d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 163065890 1250 163064640 163064719
    0x60c0c100f14011211180105010c0303060e2d040b040b0c1204080c01051b03061c0606141503060105030a020703020a0c092c0703060b03030706050c040e24 68
    0x780c0c4e04a41c0840041e0040405503110380b070b85000c2c40006400c181d800907041d5510001004a07611031200c1040d21442864003040c450340e9482c46000c3d451050340c016102e000a0031b40c002466100ca2608003c510010040301454100b5031034510302d1690182001d0400e00e03165000441d10f01c2d4002c11107070040c00100303002e004c1789001c3c20940c2442d0400e0001d0082c65003842c2c04aa0f610000304802d4800d9003060500c0f51658031664200802e001e503640c2c3e131103030050014107007d004c40c450344181e20003011500941c21a031460901044001010a100104408000d00a02c0352a903071050951f03030b1010215100580c0c2e0b00071810180d140c0801d80100401050513182c0100d01511203410003006030090a480312404001071001d10031051f4031007030b05043d692051004201250381504032405254002c0c090302c0c40c0c40204d440d01d4040d18000c960350300706c14100081c10000c03054048241070717004440104002094440c514061501d01070000b0552141c17080f1542103c0901040919441d03000b11104460f00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 163067140 1250 163065890 163065899
    0xf07120c0c030b070e030123060a1a0c01110c150a020c0615040608010e0316031803030e01020d0c110904082a0d0905101107030602040305060405060c0c100f1401 71
    0x103d0007000c40e140c00c0010881140102c0ca403c050045c2c07103508901c180c110103202194550f401400800a0401d9800254010005008008030b00c1c010105211410b00c5651240c13078846640c02d54840203e0589070b040100301c2c3c500340c0840414009601e4900c1c7e186001030340c85280e50000a0300610104d4803040c05400c050003400f100c03004041e5240c00040d1024000203540d00c480031300700c54110055513a560003c01502442c1f207000800e89a03403611a040008001e12100d9202d4840400ca400032008505005000303c250740c6c04000406411320703680b0746042e4108413683d403400c590a40b94540e60044001e10081405c00000600340d03940c95a0803021000300126102d41c28010201980201d40f5500400003603c0129119402c2e92081d039501a0a12107030055040040b120840001c1c0d503083c1e2801a030f80c0110014030140020801507015200420180c1000c0c1000c1c0e003040c0019002c2219a0403c1015001e144008140e80340e50384d6229400042d00d0f207080c5d0140001c0d140d100d07035681e03800907110000f04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 163068390 1250 163067140 163067153
    0x80d020708071a040303060b03010b0702121011030103031805100e010c06020307030b13090b06090709050a0e04050105070906020c060c0c27070516020409020310060603061a0f07120c0c03 82
    0x6100e24000e550a01407243c3ea148c0ba01c903e84400e000d00905401c1c10003608000d400c000744104040c0780f85404441d5480000c0e50314404440d400c01200850341400001081810341c412604050000350845186100d4130f4140000c0c000001c41c0000c005006104c1e80c0041e02e030380216102160300d90440c60655603417403e000000c0c010800e1400c020b21654245203411044004d034814101016030104244459444100422120040040c4000100034810102140035100c4086032401450883c02c80321082c10580b0f451400c1d160020726180400c5000e20042040755070020705540c0310001603070b01350707680c072205400c00d03040c0900c07201c4c06900701108000344040410008101603251701030074181052600c03401c1d0100c0c0c3c50300c1058500100350340b400c03844e00d0162074650300541d040c610003401c884041c034440c14804240e072400d030300c044040f9956003800c00481c0c000c503071813101440040c1d801c18541084948515410700408034064101d01059000c2003900c0c0c012182d09040e40e400c2143d42160558926140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 163069640 1250 163068390 163068443
    0x60108192c0d0804050c0114070c080607030b0f100f021509030a1701180f020714070812160602031506130602070e0c0307080406020f04081c0507080d02070807 70
    0x10200740700b01c1d50503080301841845040d0083e80c1c01005042010407038001110450030b4054000c051210800402c2d00050034461410010089100600f20501e40800040c2c2201d01000c2906c3c0a0044001c2c4071000c0c1d550741503000d01100c440d0401803940b11200c842203142c4000310911114000081007031001000000000d000340303581d1a680c20409842c0340855895900302882001e014841d20b0002d440c035403174150814100d40c3c421107001401c050070760311508648604604982d465410070714040c421180188000c04e00f805070390342c1c1945840c04004038200ca801c00c59402800141d408004076441e100010324441d000e005c001c00894680b0101480f002c00410644203000c098420914002a0b8011541d20b0314401c02c0803020583c21076940e6181035540d0680204101c0301d80340e0801c80072606011180103080545114002402e440c200b400d903128258000310050340a101042c00704c6030004401004480003039003c100b015032902102e00d841c4003180031302072000f4070032a419030b030b02144941c082d0b049 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 163070890 1250 163069640 163069721
    0x30408011a0102030a030b06070807082107050d15081f0b040b0f010302030403020a0c0b090901301410020903190506063c0112020306010819 62
    0x80004080e11000104103450207084503000d070300280304101e2464045ea101594464010f0f0072070303203001c00980e5107800903840094112803038000401c0d0410622083c0700d48000b40354040446c80031364207103103401030f05038041d40380e4008049444000500407807881102040052807240115120045200d1560394000030380d94034000d14034039000c42034020b0b1030240039640a07001c000d0030200904401130011030203544010403d50030342c030581c048040045d18481212000340b60341b241964860a01500b0496070b0001a4041010500c00d66443c0308800d294051242d000a142e0002c0c40c20a4404d103022420700600555a41260107400e6002201440300d40003030440b05011001e98115034290084600c0c0c02081d0000035019902800010b807060900149491424081000c5601d81d184455404e5803d5103d1035244040c0e4868501040e2455030050000030094807028025821403418000007404100020700d00800c401482a08100c500219172000c0c102d04001589141c60b03e2800c1400890112506803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 163072140 1250 163070890 163070893
    0x1a07080c0601090c020f0a080708030a021201060e190f050609010207080109080327210c01061217030112060207021c0b01080f030a080f060105090a030308070e120a030804111002030408 81
    0x85200711400105100c2187c41d03100744860704081054513034005640006105038007850b82004400c468140070441a030080005079100402c4901c040305100b0300c0b40c1d000403da090041156401d200342d051480881003681c0003503410545410030000106d180074042e51009045500c2c0401d50b8050007a042c0c01148500440e189540c01c2c0c41c40080352900901802a8480307454110006400c00c00c1e9000a000240c6140013050341c1c144007044d0505801c6440590090b008034030b4000f42c041c10800e0b00382d1028a10005c0c1c00800e41598900301e0650007285282400801280d8006180c808565880d44032003260091140d440ca070000315444d010405400c01c0c01500782c3c3d441000c91100d804100002160302e1801c00b51381d1000c0350f8131140c440d90070b1a10040c050314144102888080010340f0394604150046000340d482181700c1c01c1140001e00010713072140d403581c012181d12413041c40c500070025443c410740c1d40c14a0001260f5950b414071111742002e07420308550040a003070181c0d8070541d0000140050728181070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 163073390 1250 163072140 163072153
    0xd0b10050109030b0a0504111c05010612150906090b010b1308030307090501180503030a0f030e03070b270313060305060303120105090a110d0c0e04061a07080c0601090c02 75
    0x10015074000c01e05200080404c0c1140c0009646030030a6080b80f90824030960384201c291a059000a4010f200c0a04507003425100f00140000d0041c2409818010249402e0300008000d20303465105020107081ea0384080c054982c019501005400d078007140007150003d8a42d589542c40301a103012507401806010300000300c41501184005000c4101c034005c20254907000c02030740c502401582c1c40010000e0140c40004006e500048913241480108008070095a40b005180d00c803d8001d01104e803280c0c080e940ca40d10a0004070300103007a14510302c0d003001086640b464441e070400d01217500e03042501201d02d2980400f0803a20401005c02c0384172402c0d00c1c15920140300d0f568603071051607a00d00880e1060501010500c00402c0241801160039403c910000c40109288000800f41c001c29442600d0039029150f0700d04410000c1980a1000d8a0035201218144034851410350b0114800d041901c3d042240c0345d001030440c080127407440841d000d040c08138094504641e0b40c1c000e01001800781701d640e50b003d400b070318 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 163074640 1250 163073390 163073399
    0x261612060609090b030309060a090e0705040807091806060608060307060c17030408160b060906040e06190f0e010f05011d0c0306040e1e0f0c0306240d0b10 68
    0x180112425220300d540c078000700c03c0c50801d041019100c1050318030380500040200c202e56840d080300502c0ca09810f0b46070301c065540741c05011291140000d110904100b000c1c0000d004280c00424400300b203410001c400b203141e03002001088081c605180303006000a1401c00000303446608081d1991255000303c0980303d403640d07201c400f074422135800c0c0d034010003401605202e43c81c80c003c600c0c0510703000f600a080c0c0c541809070550106c0a50510204180c80900440741084804e2a000001990007007050b40c0071300c1300f840f499941039510880074201c11041d05401000f008200200d50120f03403141c4030600c0038003000202d03c910074002c0035000f004034091400c20b400400c5051300750030040003070350a18083c105a561040d08603016038101800241d0f1191301c0d00c0460038401c0c402c100c240e40c183c507580c5c03000b44003000038100e4600d0011094070078101d40d0444c0031860501c3c1d4012451a0b1701012062801070400c65000c0555900c9401003e42948a1040300e1030009200070018050b01ca0402c407040c1105050700c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 163075890 1250 163074640 163074677
    0x6050106050a20032a10090807021e0d03120b01020c1e0109050409060515010e0a0e0402040e011401030515101404060923010e090a032616 61
    0x9140c401008180c002e03020a1550003150b041035803d425803420341e810610140e804c2d0420448100071403400031025050014460320501c60b90040b40c4920100f000910301c145d8615507103010740200640b01c3c14036840c08042d280010202c00e4844d50000b00402c041c80a54a8090050740e8860300900d4581d2038600f5131401540005480c210180000f01505002407082c4401154a0f01d40001c0d141023090400d4001800d8489000341c12071640301d0240801c09107051032450000c083c1c403160545c100400140755105a48488071a0401d90700c2111044c0803e076a64008100a0108a41c2503c4c05620340084400c0d40e104415645060f05e01c0740080e40c1010041c03034200325034007100750b500e44084c00840b2010803001d01401202d150000e0050408600e850313032003d140023190b903001d40c101c3c09440030508600e580d00b0102c005a024000c0e401c90300c1420b0404100c1d0780e550703051000004080c40700c0310800204d00840240300c2282d07485410254411454030110040050061040e80700200700070b007030440c101962 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 163077140 1250 163075890 163075897
    0xe0f06030c132405150307110118260405010c050a02090126030c0d030f090609060204060e0306040507051915090e071b060c050f12063307061d0a0605010605 69
    0x8005c0250b07000004100600419504c0980084140310100b05404240075082c040c1281c4200801c0103003003c0a89414543c2005803a81e4010b181d108084104020307405a140940d001c4e11020b00c0c01995120031450300740e25001170200080e5200705007500010300062811450600301d000f001417401410740001500e6500d025840480f981500402000781d103442c801d40c0207078007605885001040308150343e01c40300c1c221018544240c40c019000141400b1880e0403e00310300c0c0c414030980091038585059142e007925203e20f40201c501c07034040c03e291000308507600a003000191000f0b9030698004e03441c1107800342282c400e500c101c00c1c903148000c000540710360044950103c1081c600000105503840344d550880140481d94195040c0070050024000c0c1306003c001811064000020900b1682070078010003110100c18140a600f9403010003070100080d0000341580700440404d400300b43c8900041c50800c01500c08c000003901110041050140c403640c00040030341e0000d005038010080e59803128400ca41520 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 163078390 1250 163077140 163077149
    0x60506030f1308091f030b03030901090e13020a08030304020f0a061d0103110a0201020c07080c0612040f02060d05060a0e06152514160e0f06030c1324 66
    0x2501d600000300784046042c1070040e803922078548030340f91050090028001c21202501d410300001d840c0c040404c92601486800b071320207000c030015401e00486400082035907400e4000c01e101c02d41540f0100703000900c4507030b4940b0202d500511607151203441e45021a074039081254264824aa4403038488100d0a10148030700540b40c2e0743ea02c88145070803041101c00c0e60552405040c0c10980d4501240600d064524003800c2c16240c250f00141c0d4504440c0d040ca4a0035120303170420350f4a50400d042204203981c078101110544400d407151040301380c0e10b5003050500f400102c400130f504a5800034034814128600d41c06035106103000c9600480c0140c0702c42040d43c0e4148101d9400b0340100303580c4650500d601c0031a01034a2803856813180c108030b280c01c10b41907282c800c44060086980740304c0c91003034402210707040c4000001010711240300b5031071500d00017221003035640180521400450000c00700c0d200340c038103100000481001401c81c5c40010b18600d0868001c5c021034044900e00b00c440484450700310790400c010310858 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 163079640 1250 163078390 163078411
    0xb060405130201050307111905160e0f04080c0703030801260607030f0f0903080601020f1c030f0b0405040309080c0607050604020103020a020f0604120806030c0d081602040f0203090106050603 84
    0xd0768550040da916070010b03003200140003a02c02c0c00350195004008034002da0859608031003040d035061620524040800c507002c1520980c0710360900c07445948442003540700007583c036109055103841c2451030251003510201e010074010440048245504002941e04031514500000d601e1480d2629021a400200c000030640b500000081080c09100390003c0340341da00081000240d0610503080c2d1012141058011804030b0b0b0074a0810800e9a0140040611442c0e01310140410025104403c60251031440f11002410794a10400d9110505035020001d00d86003d0010012402d080c100503003040c505100303800d06441100c00e00c00b42410709605480800740d0020040c46a6112540107502a402c000c404204505c1040700f0349000e00b10070001e26010b80d000e4901425142241a8001e1608000812890181d440021a0030494070381c52024111143c2120100d600d030701190349241c0304800c1ba5807010b5441414001c00700748940c5140e00039402240240000c10030950340d0002d0050501080310f049454 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 163080890 1250 163079640 163079671
    0x302060106081005060d091e0b0105150706020a0c060b0a030b06040515030616030510030f02010c051006240201060e1503011b050d050601090b071412160b060405 71
    0x78080c1c20b00d6a000100000342c5100380740c4580118581d5001002e45e07121640d00c440c40c079402c3c030211110090404407100c880d6074505e1500e4803881d29010b810300c20a03010b051b154036004125000b140c240c81c640f03540448259980c100981d402000740c14018002da6559103081c042c021540303000c8002100302c0358441268140c03070b40d9060800c001007500529a0304d2021110b03207401c045507014400c09204003100c4201d0707400744149140c0182200ca0081c440740c0019841071041c404500810078070001c45030b09182c13000c045070841c6081400c0108249486480508041c0701155840254080030700c5010364071b80c2c2d08041050404102e081c1e8074144959491008188042081d0708100721101c0c00c2c08d440540041980d14520f103038032180031002d195410010724045038000d4038924074000c03182c02c0742003440c00005950402449000c01c1c4034401e0006d26404446c0044d540080c4180075500c24411410541c603240e10b0b084000d6490b02d03800ca4821604042d44a00207022484c103031150350300079442150040c66 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 163082140 1250 163080890 163080899
    0xf06030203060607290606030c04091a030105070507200609060d0915020415030c270f030c0602060108011a01030e01150b0c070608060d02040917070602030f1303020601 74
    0x3540302802c080c1d0000e400300101e00100c0c500a401c03903242c0d0401400c3c1100c1c06110b074038040d489035006d00071034401c1c5410010321199100c003800703503016500300500c0003944026a0a200004071244407200e900f55080078100025140c010011b031170041d02605100c502d03103140d0300c001402485200781c041e038044014424040c150070110050a408992200c0014240b0016200d0b80d0382c003070480c544041036540004090001018a13226104081041d0500b40240100c04601a02d96140005400c1007081490f4940c1450340b0480c2200d0700406002c10242880c40c3c880c00c1155052000c0d00424026124800c00000c1045051050607056101c80038078030041418034004401803c524031aa5455648840c1b40c1d144070003e441c0d40c100240101841d080c0c1d1451126803a50410f85558030101c180003841041000c2030300c0b05070203006101d504a1340003800004c03600c1c2c4040e000140050342002150085104400c00015500450158139020b102c10680da5808004207604109400c0c001c0040c2c002100400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 163083390 1250 163082140 163082147
    0x7060e04141f17031b0c030d0e0a030c080a03030b03060106050406030c110303091605010309030e04020706060e040b091c0203180a09020a0207050f0105070209070c03020c0a0e06031005010f06 84
    0x49599826041c650300c0c0b140d440c0c0384002d16402c00105003843d0340000984108600401c203503400c030030070302901030800304003007400090b02d403550003d489041c00f803103850300319a940d01e0601880107035600075480580f5903103948070300f40c0e60791a80d441180800c0c40c00410520030310f00050b80340e04a40f01340e525a071409040c19421070280c15000e10303400c2030104900c1a50510481072014504c104401d00041000c0c000b00c89001d011841c2c941d0065051525059815000c0382e0701100034002000c0079100580d58008030f1901d103000f015190b02c00401144101c00303000411400c4408d240c0200610720868010b01c200c14940707411040e40740b0752840542d0040101c01f0315504034101d0929029001040b119a00d41d031070310418182d80c0700140500040e000804e040c040c6d80707005500740a1992003031a12508141e00e0382d01080c58a880503104100703210b040c88114003010f00c02c00c0303100d400346405460200c0e600d80d100c044900c090825900c20313200e0b00407480c8030001d0004d00d11a00e030485502c0c003047c1e4019860f103c03056 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 163084640 1250 163083390 163083421
    0x105100e040209092a0c0304031e080a0c050105060301020f091c0212010f0f0b010f14040506040e010914220302030c150610050c03071203020c010e07060e0414 70
    0x95030815000d02454074207a6034182c14521990f080c5000b41c075101109a20004003080d01c090451212500703101451b07000d6000000d0740c082e240c0c00440c485051034440350040b0140c1800d500241041340005031f42c4642a402200d644840788200c000380070075120b0504160030707805191450341c00c044c01801031b2481803422000c2440080c3c107420035a41e0304500c2c0e0b00854542480618140c0c200da464096542d41c403440d51181e800e155014940412401242000080080852882040c20003806c0040c6d00003601440049400400000303000c0c0c2d40e10b940e101031520682c3d500744107594007680380031544546c01d0100180144600b5000280c1c0c40d403c45500b0038001a44034020313082d011484180110210050200b00000380030402a820914901c0c1250402800482e14000ca1081160511590841d454004266401680d00040040b8070040c1103030700314028058206840c0f0691700307040003846940c40201d4141b0075034245607503044110303034400c040c0801d6618262008503200382107000650140202c8618 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 163085890 1250 163084640 163084667
    0x30c03050d0f0603030f0e030c0f06071b031208070234030213052205030a050313020d060509010b06040b0304020f0102032703160b0d0f06091a0406050603010510 71
    0x1500c04810b20200c0210703211030f082100400d110b140c1008038981c00c0050b150709004110010010301030400e01180e6120310407585180075501c04248001000041e006580301c000c00704440c1c0c4001c540c0d90900b0601b10014000e00c01c01b2079800070109104610104500118010582c0c02020919101d00d007040c24040c00c0c1030320007000050310004001640c0300c141c0114181907000c400711f030a040407015002c924a03074074014908881c000610100044001c41980c80c40c1c512801c200317440303551307000810302083c0d92040020b62040004000c1020047c1b10f501c0706014940c24070003085101d41c03140a0010901c90782c043c0d617280c034400780005401413426070485c4565203030603c1524181034011a0903100c1601c10000d621196850b0181000c2a040400c030302d81c0381c00401c0806803031070703882c02d94011518480d011020305900c0e217801281e4013514558024100400c5600c20070000252041a4290101642450746201c1c0e410404009071910304442524140c030b10081468600c112a2842034490310030007003c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 163087140 1250 163085890 163085917
    0x31603030f09052809020409021309140f04050c180702060105010504080a06050402240d0e03030606030a05040201210b040e0d0f0c030c05030d24060207060e031510031e030c0305 78
    0x280171441d10407030300242c80180840030f00036031a10306002c078010030040785400241032035140c11403011020412400035a0001c0c9074182c50b0f00c8031748603800d1203030400b0075040d0f025800c11900d600700b80001120001d45da2081015a0035245203236255030044440e072082c0d2064501c150322202a410200f029984038a1b0001c1c070007003512012403110607400d008445600000c03040080c001c50615402080f502444a01c03400301006580b5601e456400220b4a00001d0302211200d03941e0b10006003107900410580d500c454940448079003402440c113003d0058002140c45a0003203052900100c0e0382d560024103200c01d440903803104160000710050403561070384600d1003541005819504880460300510080804100040001c103941c000302d214154520550380d024105190003503400c100d0154003080c1d94060750303514038000950340c0700d140019191000d90031400c062625140103200c1c450008031151411244150039071001c03610480115030f01c501a40e9001b9022942181103a000248143d0040030800e01040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 163088390 1250 163087140 163087219
    0x31602010212010303020a020307090204050a0902030612010e0f0d091508060d120807090b072f03010e01091103030705210705010216020108060a05131a031603030f0905 74
    0xc803002c000d44080c0e0060b00580c100c11003002c25818140003020203030202d164107501d054940404500544014824850826030110104030b00b0303a62064181c00c00c6100c46d000340142400c00c05000e40341d0b000400078900d40d2140702c012155460061003120200c5c1ca10f901c1c1100205c2c40118240c45203600100f40682c00a03812500e40000380120310540c0c11140d00d9a51518a0302d0700c401c0180c1901e84d1070300002001d5109005810008445d80082c02001c4a112009101c1e1020b0742c058050004048803881d51550820701e0f88c1c404100305612000c906402880d02c0f0a1071704502c2c0a040d01d91003640c00151403a007100c6810f2004415120b1090303025046c9801080c80e1803025200d050883e00041c90300f266a803e03020009080d903920034403668000e80100d8241281c40c0c58140001d4010400f420f800a94a4807400000b11309401d80b000300f0501c02000d07059544100011050f1085c03040180012404038074805011a060340c4940340840c00e81d80050f02c0e4400800050180211107411200300280114882c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 163089640 1250 163088390 163088407
    0x509190b03090307030801060503090a1101200a060f021309050702031908070f14040303080c0910020303011508040c030311100c03060302041a180a09050307080901080a110316020102 80
    0x1200110b2107070300c28002441e11840c2c1450010501c0f48103a00013410007009000384a07403504049034203008942d00801d50207804001100617a01c01c0fa80009610803000e4031241a000c144020a25021140c0300761010007a049592022000320f0040c1c24046901c407441071010300442c441540310b02e800c030790213004803414286105c0308507200d035240c1982d65002036401d0040c00000354100e482001d040410341454020801000304207840c5009070b100240800031010f004c07a0078184640e0403031b42c4202014098042403105441c000e9540c1d8003e205001140801e00000302d425482101f070075005a601c0104d01c06541d2035620101c500741d2028004c143c081c06808112280400507208008030940c40d528045842850760040200b240c138440100868442205854000d0707a840c10034060400301071094410842d199551400002c0c011101d00030031a2100007100c4042c8031032180940b100c030300b00f683c8211007556400c104000780c07108079110300c10350901480856040e03046100364400701b50f400d2000504041e0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 163090890 1250 163089640 163089659
    0xe0a1a03070e0d0c05010e09040210050a05071e0515040804030b19090605010609062102030403050f04030602130801020918090a1b0503010e0313141f18080d050919 72
    0x18041151843c0130740e002082156004052030950000c112500b200c58503142d0081911051450039102c2048800650020618041c1c0f05884000740c12403107200903202480003101c49203807522000d40d8584a00c0c503210010601d52069288140d60021a0a04042c555a80c0090ba050003403c0b84401e142c0c000700f0180264024411b654403580504004260b0394949000a020840c04c2d030015000c03c403600e007260480d465961a001c00c0f81103c142c00594a40c0d07076080c00ca84501410901c288070304800a800003d21000c0d401410602003000c0701101d0940d52140618202c1c800c11168076000411010070390341d50090004203d80c007154840c2a01c40c095a10342c2c1d100000c5800c4c3c54100668003080d00c1c103120a0800344240e01109039081e000350700d0003e6a00760580c13517180910030402072082e5800314001548a040d80c2c0d00c0182c4c100084002e8005035030703101400b8550042c9070000038584003040000c02c840001200c0440901c3c603110319103001110030a00c000e1040c0000c1c1c200c0c060320781001c0013810149 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 163092140 1250 163090890 163090909
    0xb0406170105040c050f060313080702090108152508071b0b090114040507031b030c0602010b15092404050901080d0306080c09060603090c03030a02030405010e0a1a03070e 75
    0x3100400001e151401c3d180a508030602604100c0c02a601a01c0f102045d4603800f040300d812084d6920710414a82e85407800d020302d4801c036600250804003807400003c4400c0009609204621800c030b0b19152540d07100c810900c042c1c149603002c00313194120f11081d900140101c106a80000e001d01e0105140e044001400100d108e6840046446c1020f0b0010011104028480e09040c5003020402c45010300b040d8840c0c681e00c019074003028100a40031070280c40300030340d080014801940d10510321108241d031150040e009080404089001e040807490f0607910004c841c0c204d4000070300040c840713804464002e00b0f4503411402c844290481400400c804940c3d603450300b40c01402010b035000180b48581e41264000c0641d82260f000c000603078800681c1e95107503600c03a500180d11640941c1c03038030380303959904082502d810781219809815000000b404030189901000a1041d03c0c001e8903002030b981c02d514284030300c1504c9481101d14210905942c50200099003008640024881c60003644c61a2400d00041500381c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 163093390 1250 163092140 163092179
    0x70c0204061d060d0c050105030a0209030118051c0909090510020304080a14040e0c030a090606140102151501030b12060a1b05091012060f0e040c081209040b0406 71
    0xd240c0b40082100150458201d620110a403102021404c4550f52000d011803039010b001e040c04004000600f0001e030300d5040d00c240c0d1000900a12100390300b0318690b82409010304080c0d40134021b45001104005494244600c9017500f9a13810054515100c075040c02008400011170b4070713001d8820540010142030002e140224041c07103480c0e6544248803405408600c600241b0300f00710805020422510188900641e4404004c94000da602d81d0342008000c0141410540209024074102d800715410044c49800143c3c20030a03002c031200342c07640d4075600402c42d42c100d56824181104d040410307059403080d084240c4e941d0001c0c000b440400d081e00502414003c007200e0070311040303546039180300000c414090b080b035134080c41d42040d610341450710000c560401514070318141403050f504d02d0b0348080d007980c0d4001c0c00140f9055100820950300c070b108424911805541c01c2d10340040305031020500c1440460305002c900c0c99030601d585130855406c148000b0b40031001038036074865070b1600c001840c4818070b0390002c00070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 163094640 1250 163093390 163093409
    0x4050903220e090a05100b0a170d080601020c0307030212010e03030106080a06050d02180c1e0705060f13170909010305010917090105120a0603021c1202030f0d05070c020406 76
    0x260400b031501c01e40810040c071503a2076510651202020039004281e81040d00c00841002c141c00560002141e000d00032644208101c04c500101107112420119028061051542e158078807600d602004984c0c0e142c0e241802035140c0c1210f0fa04100618250324001c82900a01002258441d86008940d05642007640248041342a800400100422511901e005490110ba00e40c00350941500800c1c4040359907045801880c804401280181250070180cae450305105000c2070788185a00c90040340382d0f81048000711203900c03611001c01c41d10404881028400d0a001c00b180081080a40f602c20b10ba010040c66041c040004000a4031192525404140698051800490761081070301e081b0140307403200e0040509090090144800688e80701d4121b400184401500f5982c6403607400c2900014201e03623200941c40204c1914022180f5626900709002c60b005070090201340403080400e82c2c0720f1046c0c20007502003c20811802e0305040841c0d10542e08203516107403889045c0c440303a01041c02c40b100c1d600300c1c1248 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 163095890 1250 163094640 163094707
    0x5011406071a1e010801110405120709050a09021f02030901120609090b09061501090512072c13030e10021e1c030b030307020d170706050109060608100504050903 71
    0x641c60446035004151000c003c00010b0565107e4181c0350066025580c8901e00c0150b5071120f410701000a00050100c402c004c1005003441d20721540241900041240550204441a406002000c00707000e2031482d80d070083c5140160441c01103c40c4030302c449074540349565400d40070500d1111489400c100610803000d403c4a403d020720b1a41c40d000b8010490300e8007881d01d560940d4141d82c031403512000ca80c3c040d160b000d01d016800719058140354079038116280f071206500010684840409480801e03aa80c40121300b0141c40b010405031804800500103008140c1c0c16110200742e04158210b15400201841078aa180700414500c100f0984150600c266a03402610007801a0021601900705642d0a040400000f50007401203a00c0c0e01a0f684040d12407a80544c0303c8003440940305000000240050700740e82d0751405071502134000d1400307000d01c54103145030900c007040150040e0402c2d4017039580c0b148000c0d005464402040040c0100825100313550009010262042d200f0f5155540c1b90b10f01e003003c1405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 163097140 1250 163095890 163095931
    0x80a060506040b0f01090e060a1d01050109060504030515150907030e06060109050a050904030201020c0a0501090605010b0a0c0212011e09020f0303070b070f18080c01080a05011406071a 81
    0x41d290281e003c603110307141e0340c82106441da07044003504089904130484890703075580304000a2420b09a960190700c80c00b204052640c150681c142c0240c0c180e4400343c0315581202d8882c0c504840754010b6010061503a40aa075050440c4071000c2140c036400a003401580414030201c8001c141c0350402038803078601203038503607103802d41c1541c05001c1c0341d50281003840c182102502e4440040d281d0003042c030400e4000c1c040c901c00b040c141407003901122030240910f41241d44107020307031130040c0c001c0060000507640a8500400400d59051180442d10154440e43e80d000714140c05408002d01000740f00c910801643d600e01c5200100f0300703190203241c0900700f8000000b07000103075070040c41656109620b955129800c100700b00f034001510300611039000205882d0510904107a00025075502c201c5106000001c0701d18400003e00d01d80000d01c3c1d61b600f05003079803010540d884980000058890a004902c1100519600c0036501e061a0010746145070242015565121104992100e102020f417000519060304148250 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 163098390 1250 163097140 163097149
    0x20408060a0608011e180204060f0905090c09042a2702040602030a0c032a11090705270411091e0306070c03120501090c030c03060f090504020a080a060506 68
    0x42c010074150000340400c03504800d02d20754074480700380c200385032603a20044031558a104000c54000c05502900401c0590344440007081540c129229401c000c41c01d2800060079a03c0214044041c0303400544000c07804d8850f640d44001c3d0303000c00c44010b9a100c0f618030400c1e420004060000e8010612000402e4031a81d51801c13821240708003c1c41c4605145c010007041050790b80c000100c42580a181c640014203049515040324500d43d0b904d44121f0240118071200d94020300e4800198203140f003100d1070010861030505005031f008040714004c0200e0350a001441600ca58260300c0e4100b1540509248200e0382420001411202c001040e00c0c014140814001c086041240c130000b00c40c1805000140a04a1440000da4802004201c02c0c10040034452034810036020707020103111144211424400c642e1510320307410003840446d1090303000034107140c10386464900070b104e4074081e101e440000d10030907818400108003620020f042207810214100c00010360710b60922101f040301e84102c0012500741040800c21 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 163099640 1250 163098390 163098401
    0xe060f310b0307030809010813060603030206160f2001020f1b06010e01030b010504020a050f031906210b07021e060105041109090727030b16020307080d02090402070204020408060a 79
    0x60003035101807820700c0852041c8046d945960b00c2440c0c60985540d5000790302642c6e01d020a0000c0c41c45040200103c00c15401007102449450071781040004041900c10403640710041140817008a08007414502c00c2121402580440c06031140000d49400b00cc50b84518069011001e04604080c3d84c40c10144500418042c07071b80101071706000c544c515411602c50428010040c80341030300c295800641c8080c00c501902c1680d05070005181070315103e00d00b40010403c540b903048aa8405a8a4031101180c0c50401d0450785122400076031485040310940d580703152200380042c06190a610888140c2c101c2001e0082c8840a10302520010300780300c0d49050300744400c0d01c115a03074440c218501840100120349a151411f80e01880c50b140203814a54201c0c02c85102842040c003291403007181100c0071040c0301e8043c803000e003d04200c16000e00d1a292001d41280c40380160400108000b5041042035903411003a0040d20314544002e02c014a0a060360740010101c1c0d01c69885007090790025410800c190200b0b110b007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 163100890 1250 163099640 163099661
    0x708040c120c23091801091e061b020c013903080105100c080d06230a0e0f0103021e03010204090606030b0a05060913020702041d12040e060f31 63
    0x151129290800049016a004050385d003c4042c010040b1400c50382500001c5030350340c10121141d00201c60039549000200b60324001e8038254240340c40c0700380c400c440c91700e11600c4408980c060300c2c1005d200d4004403002c1b00320904030303007100e64403030769035200d80300300c2c2447d11070a8503140001c481c21041890f0103800c59a050344031a20580300358031081202a0042089001c99038008903a607541d07585806d8060040075640c22104107114040302e140c1003640f422005180103170781120002805ea58540964050101c12070301201c03010500c00c010401410400c4013a809904403c02403000809485d0101e42281c00a0b4400c00910340c43c5c0c1d000308015501403040f052440400da80c100c16a50a040210307103544560b00550b03020b00c102232000508032141b80c1c180d4080c00c1c1c0c002c000340f1400b40e44090b07403020400602c3c0d6008841c00b622000455680c011803c54040714500000c140c403665842c030410030401d8000c0c6c55140c0001020305104800703081d4080032010140c000252081c1e92201c3d0000b04c0466000000c5c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 163102140 1250 163100890 163100939
    0x60302090901060f14030414061f05040207170703050d1401090606020d08040321020d0f1805070501050a030b060d050103030e030a05070e2206320708040c120c 70
    0x208281041e0f0011500200440017801c9a40d01d132541e1070074000341d01c4074041030001400380e54140070b4102d0350414240200c11490700722642c925188e100300000c074410444c0c002c02030480c0b00c84142c100e9482201a110560082c20100c0c10004103060310001c0c1c0390200040301000a10390010b000c02085440380d84040c1010b88000d268203514054060500c1002a0019040c000000c14440341d002c4040985c1072103000d210070a54039103084900000c003900220141c01c9001e8140012241e00002c3d601d4080c2c2e4143c2c001e40185a5145000c0c019503107684020758020415071503450348071141d01c2e640d008084006407040f00045940c9541001000030700e24211891180e0070400e4444007080001030041c0c10b50b054081c5c80401c607140e6008900303000c1801c440754a400312107001c01130180b14030340d0311410001000184181e85c5607c50103400c2760201c688a981c42d0300840a402280e640791294101d07507401071240d80314a1240341c4540f00720b05c00004034182200c1c6500822414000d01081503482c07250702c42400c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 163103390 1250 163102140 163102157
    0x310020a050d050612101a06160305090604030b090604031d010c02010e030a0b16020d0306051503040c09050112050c0a060915031e0f1b020d0c11030102030106030209090106 76
    0x8400400520440c680004040d40341c10200d49540e9886060310322201d44c040c100c071b1030f03403c2c2c003c1480c0c0904036000c0b81c0c0701016a0810200007030f0034440120382c2038451000311910b841c456950140c8003600002800c0e07400420501021000075003403110709009800c035800401291a252400424161000040c05041c002540180180d40d0b00200d61001c40381d424246a010015030001092800d10480c2e00540041c1c0c0330340600c0720180c03880da0007110405c40342d0b00341d40d0441300b40441602136400500c01e01303400c45034207000e02e54004840030185070082c5c402c04a11080540e180340c6401610020b03040f4805022044488404000c0200076000b0303008400d4421002c15807a01c14042c0c5403c1d10741c42800c542e848041907640c0c10900c01d50080520403184200d00b1840e281d444107650052039a03c03030745c003c514600b0403003270207006510340344c0000300e0096401010034502c801c0044440e054020300c205e94842c40e6800d0005196000e002640c040c0851755001a01e456414081040c40f010680c064024840e125 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 163104640 1250 163103390 163103407
    0x6060e07030207120e1c060f05151219060237020d0c02030303010b070201020f03030a060303080603010e250e010b070218012102010e03061305010f0b0109090b0a1203030605031002 79
    0x5140c0406c0c00c2d44020030804c02c8001810008003603c40320381c15010380d5181104018040c03d0700b1250105065003582ea50700120b2040c0015603696415585a0900c0c5426100300e000190244e001041600442c00d000410318880100c854804211a0003210604001401d4040f440d5410000d40c08180128075101146105a40220f1f0300c9110600400005a00c001030b40c0c001d5900820080440000000031650307603182410f96080144160b001c03c40014460070041903151405009192104107900007501803d01c000142107035003002c00e4440a101c5c5803225000503a40c84510110b4000c2628804640c0d541849204004100031032016a00c803a440460050021803880d0900c03007461401a54061403802c12400180d4201c00c108203000d605104400401c0841c0c10320f01025042540305100a10400e4500c401000689046040c102e0000b00381440c00c0218a0098018411a40000c1c14104402d51200c01c1e140c004441000250301090720b1764001c12a508003088840b00600d60980214200100d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 163105890 1250 163104640 163104649
    0x712020906070f0302010b060412030909092001110d030203090d020102130b0a050409050405030c010f0605030c06130806010b0715050c03070c051006080a050c0406030203060106080406060e07030207120e 89
    0x3a041c0140c154024000f00a04142c002d5004400c60031005190701d031201e070b03030300c681c1c40485805075070460018800c0f100c00641820980260b51003143d001c42c0300011032081c01c6103641e030084080001810840800b43c05403660360144801203c00d0222381e005a0b4915169001c03914003400540d40108580c410000504440c400320a80010f1b01e190541c03c0d42c1d00d6003d01c100302e5041c0601d411102d000c3d460030b4180410031200000a009614450001340072601042903d10f0031503003244141d60f0940c00c80b80c5000e9181c906030000700429800d14071001032068440c00d0803403800509030016101d0310303030006100c1e05008841a141003031942c40382c000e00c5107103450404203a95002c09020300e422300c0008614102040014018070008064803401000855a910b0040d5030340c452003901624070703009800104055080502410068a030013400406503a4681141110b0790a002030040da0ba42e40d0b02d90700810300000c10030005008011655003d40c5a051a0510a2012500c000030005200e45c1640703003402d0b5100e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 163107140 1250 163105890 163105897
    0xb0901030201051b0307050d050901020d030e060105010e1309050105041e080904020c01021b0d1103070c140607051605100e090601140903070e090607140d0506010c02030d02060712020906 82
    0x101811408100404c8403052071079400342d020010841d010fa01c1d0640d14081d4040044d05506509a086030156420071a041d01103c482080b04042c60704024014081540030303010881c00346002400c1ea102d0060502c103080225400c00100b100d01e03944507001c1c041070003144000782e01400c04c00054446e013041b80356070741403d5104120304e80d0b000c0c1d5004181400c60003801c0d410b0750130010351000786441811000031501d4a0b440c070406082c0100b10000041c0700e6000b40001540d8040703600078015035050b82010f000400c260204402d030f5500800400032000080e6050012180d8040e040703000002c7d60b82402c0c2040345039510621640304000710844100031998803210980d030400021308120440c1c00042032418001e114200c50302d41c05201f803010008410001401e003502c55070425041d0f500e2911042400c46044000c8050020b000c5402e0180705a004840c0d0f0206420040c141402c000809103a40440c0c10003466800c0764003d600218204040e85420860201207901c000d00114540082c400020b4203600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 163108390 1250 163107140 163107157
    0x60a0207060f0903050d0f030f09050703060203040f05030406111b010206041203021b07171218031c0509120705220209030613110102190f020f0616060b090103020105 73
    0x11080001c00019006001c3c4001035034200003544c0300010700030b00140c01a00781801c5240042c0c501001d140c000700252003415815980100900140ca00c1e6844032006900040c000fa91600302400e12134000400c00c00003040248a56141c0c00e501c4145804d141781483e202c2103d018004441c1c1b140d415103a0780c0480d0040e40301ea480400d0780490254400704500a0040c905030144210701d03030200030402c50300040d0102c21039501d0201c05000600e1100482e444844005403000040824440c006030120302c100c105078080b5001c2c0482e1040c41c000c05c040781c005201200742d440400d10001d0310f039405040160070a5802a0724100511071203203031002003041032502e1400c440305c072255001d081841c0c10140c0c0480f07824007002022101507082c0385418030740b0150448801c4039603801003440c00c54554004980c9403100c48110714800c11038545500d800100c3c62440c0c07412a07000458440035005580c514000e0309800025240c010054080c41c80e01208a40e203580006216a2600004200503a070040031034802c1c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 163109640 1250 163108390 163108397
    0x1051c032006090705031e030a050c0c060315010e0f09060607030c060501060f18061b0303090b04080301080706020c0f0103150b030924091b032b030b060a020706 71
    0x1680400611410400c40c0d004020720380551010b1052940c4001411400c0e148120150390f14400c401420001c84c01030640e403c4030300c2e0010301c0b1000c0164003800c060b158503c03460702034500b001800000100030303910494120303040c0c090380700d904a16940d01171081c050140040c0c039172403c22a180800210545001058280300c0d07c00003a03140d00301403003403c0c04458241e002e0802d108a5860f8200a002c0c19118034030040011840541c07840810356520051045400f2a11002461160032540400810000c4015004c0c1525100844000750003105024403d6008484081e01e035410444050704200781c60340300008640c09040e491409940c0c912401c0f1040c4001d080024101c902012808242c2c011303a48040c100c00c4002c070402440850119139032010185128620410410011126903560401c1d240c4000315480200044162404030345400c010050040c21280c141c00c003004061510344000300480190301540740080c16444e0907019000039814200c0701c2c80e0420040200081d40d0b400c50344182c0303041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 163110890 1250 163109640 163109657
    0x60105100c0b09030304030201050606070c050f1f0206160302132102030d08091501030b0a05042a14030a0f062c0102030907080606060a0e0402040b0417010501051c03 73
    0x161030040e0501d108140d40185141560301d00004100d0700c1c0e07001150164090350074440000d07000e1601c07008236007030700d98412904481c482c142414840d104810790a4540c029413083d1104618016610030192081c16030f40c0107002d140750240302100c1d0740388050044404e050040c46101820350700704405400307540308681e04c0f403000c0491500d241111550000003030340600a0140d188805580702202510074482241140e28204a0511343c406200d070034400548241c3c2e2420224050b2240b80d0030944d08103004d040c3c903424082968050081e8907540c04e00f141100804400c0401c51001c80d49084440420210050b29612000f030702e03812288002e40d42c008200c1e966803e640000d0100500b20b00086940c024188544c583c10b4141080c000e6106492034200d510a4110018240c50f0000b2201c2c42180040c2406080802c3c2003401e54008412004c1c0541c0240c00f40b00214aa0a054020700024940b0303082c4c4a50f603c0780c00381030300e085a80680040c2d02521001d0800020290900800c03021664140fa1003140c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 163112140 1250 163110890 163110919
    0x8030405040e0a020909031321030f1e05040602011d0d110106030b1003110906130f0e03071a09030309120306030102120f0907050102030304050c0906012607030617060105 75
    0xf4003180d603070001d6015107520103100c081d001c00005488170310800744001c2c110944810108000318001c14651481107040300300c007000070340b0500020032400b6040c1816500050086940a021300000541000090009c02c0c1080042c3e424000d01070500086202c034403600120310740468950182ca4001d50502c400088a014a000c0951080c0021500111a03101d50b0504409243c20002c25100c05d03101444030704d030818400d00d020f034656401744e50000d00603101c900500328810060401c5030300107146560b88541d2050180c40900c010302010744030b9080c00e49010045d20810b03400c40e102500301c0c0400c0d8018010000100400520785080c01912305400307840313580f80400240a4460b00c04000c4000010078240210f0a0072840340501455143e000e4800a40c1c6801c012640c5c0c0c00f080760040e0003075100c5240b02041c0e09004410540000c010301d00300f001e01202c1440c00700304110910304181c404d0b0043e0100079203141d152085401034041c00c3d08030307159440302000342c40c3e440c0e4060240034841c0c03012559009 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 163113390 1250 163112140 163112143
    0x11b1a07050f030c031015020601090e01020706060e0709080a0b190e011a10050708030408090406170f0c01050901120e010e070e0a0c11060c070f0209041b05030708030405040e 77
    0x4002c00044050203a0720b15041000909035041581c00c11500f0200542c0400e14403502455024454900ea0084c49140e21b05054440541500490048155801c200d0b00e00491043c1c01840044c0c25841081c0a4909000b840141400010b510a400b65000f01c0010170002d88005400d42d0803a4440c2d00481e140c88858010310001c140070422440c03d90b1a04040020302c0110b010a20390444040b9000014034005610a803442c0c030480000030400407007000003030001285074014110014000d400052a80d407030b2860030001005010f6419203a500132640e001c407082c004c10900303828407030030321300b00d410888501c3c0080c08000350b4629410003152914400d5003840c01c00d50214a60804403012a806c80f42d41d0303d010581d4500c262102c0e0201414003d009280074052401c4c9101c0c07035400c800500003691f80710600444d50b0080102121064111003c0c540984c0e99488083e0140d40101d40c440c20311600c180d8000114006540140d00a030805602007041c40004029141111001d450200d50300c119841242d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 163114640 1250 163113390 163113397
    0xc0b040816050a03030e0f0703060e0109060c0908010e0d0e060c120a050d0501050d030912150501030c060e041527050114090c07020d2d0b06011b1a0705 67
    0x16400500604005001d001c80003c0c1d0510780d070700a48080004920a00503181c48040040c43e842e41540044020000513983d81d00030b5007440c64010000504104076603030041541d5450014000203000b100040c820710780b00f072107030000144440c0c001b0406407001040150003034140503103452080f900445c0380100c0c40010712500c00c10010001c822582c452400101400c607400c20800241c1003460140007085a041c0305000114007509600c0d5907a8075442c0c40440e01c02d200c41c400b13044512001e1844140300440d0140100c43c00b035442403003240b10345410900001d29041c14000c2c070034840d40c144404051121802d07802031007642c440d081c0c0340304404003011404401a03100c0e007a40780454901400003c0301c3e0492081e055020504681c00d8145823502904011b15004c0c43d80040e500081d00e50345100043c4400c80c003038100c00c4a0240e60300d90030003840508800102442000e5443c000b90000700305542d80d1118001e04c2307920705101321b182d0b4042d1940352000040d00141c0510300722048030000ca07404902900a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 163115890 1250 163114640 163114657
    0x5070804030e04090f0b100509040503031614040626060a0302150405030312060415150518030a030306030b0117030f07020301090f2004050f0f04030e040f0203010e0a09030c0b0408 79
    0x30000c5445c00c070f151040002d002196800701d0001120302c00316007841c01030704840c00350b03030440000c1d811a02c0701c070000340c19001c084060310180000f0301c0c4580034081d00b21014000a00803a11040700850611440c0c5c40c401840816151181d0644020007031995200c21020041da038040c1c885c0d01031079200280c034007098800e079044a0b60510010603a002040034401116100d480e054809000008900d611000200c8141c0100030100381c081854590032480380e000340c10000b180c1010108004101c0000c24100621034100307900094440d0700900034420403640b541d0040010f80e14208513182c40010854aa0003500c440c84581400041c0c00c2003550f0b800d4000e8080c0541100c0c00112121452034500700d1201790b490b850b180521108500c100e41d10b030502c0384920848068100c1002681c40c440301c140784100060044061003400c15038810a911207105100e0301540c2200300680d607504110300d06000c1c2800414821600d8144007031030000a074040c11104c00103600c034002c4002900c40745420a6076000b8880d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 163117140 1250 163115890 163115903
    0x30d11010204350601060f03020a0207050d050115060807050702090910020c0312091501051012060b0a0e04020a0519030b2e020f19080c16061205070804030e0409 71
    0xf03a403052600062007400301d10707161030807414100d80440010b98856000b4420310300441d0b004021140e4181c029001019003907458810303941c00e2a1100f0001d00344c846000c0081d00c2d640e540342007101807803c2034844900504080e0801c2c808500e4001030040103442000d50085c01405031001044510b08200a00070680c004d03204150b4481190b074104540d650882a1100d04800c0d9040201c0d03600a80440e00402956a0112041c001d13801c01e42801407820144140d28200808002644006041071166038017400c0c0c080503407944c541da4000000c00c4400340c400041e1080781704029255171a81c00c4412581c031100c18605500c0c552000307034020b60040c2600b070811600404003c048181c000c00c00801426602031004120410440e0014100d0b580d52041402c0b071005c1d40f000d0b090040304040752400b90060341c842d00043c0c0c941074080c4041418810031612500c402010103809014060b0800c80302d0713500c1c0110200070403092401d10030060041201402c05414400c0c03a81088149845580015660640122 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 163118390 1250 163117140 163117169
    0xc0b18010228120204050a05060c100507030b010e0121051b220b090a0303030e010e0106030b04050601080d08010902070f02090f01180e1b040b0d110907030b030d11010204 75
    0x320b4444140399480b042000600ea01245403007240051094405544000d410a84d5240c2010140714496100601e9440b480c440c410f06003000c94181e00606100d06007503513000c568402e00c2000500445410340e0341a050042035915101c00310650300c1c4002001c4282c50020603d0340764051840840100000d0319100c07400d00040044840007442e094521240c0c15449501142d0f907140301c00c0b0650702500e111139500090001040000c240309400c84840d49102500000e0b05d007074a041d600d800c4402d84d600403039205400d0710400050240600c240c0d8010315084001d007101035503880c001800c8500500801c0b04055000c02c1c3c100c14080c100c0c01d82d449995028101000604001075950009942480742d020000c441050840d11304115000e0704a101c8400b000421010200b0b911802c0440e801c2440107070003075910414580203545a41d508801e0b1801402d41d095001072010a028002400818883c00d140c1024204183c80d100001c40c07030b0795030341d4911b03008030f0994000040502912072948030a0000100300c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 163119640 1250 163118390 163118437
    0xa140301030f15050601230f0d140705120103060911040c030203090c12100b0d0501020721021506060a090305011109030c0a1208070f0f210c0b180102 66
    0x501ca01d80424043da60100711081211511001e841c021035203940000d055400c0c1d00d000c441c0d6910884c0302031422021003800d01c85060060200c9030001100032103141d07202c076040300602540340d43ca01d801075654078140b0b24080c1c0140c80901d45a4040c48018441c90382c070071010090100058001105980080080c4005410300c4002801394000351084071182c0206450850a031411290100c2c420072484060f00c0440384c071002c000011b140d5806110b820445100f15500001c01c2880100390b41d5100340e4001044107070094001a0018240807030b0010743d031005901520711417142c10180d0740048110b07010b694403100743c0030464240302340d640020300039030820030381c140d4021580019201d0610103a0031110a060035034200414001e151240d2103500c040e424060300450b00785802090b07418004c02c44a100701c00300e9038411a4091082c1d0081c3c6840030f900003243c40400889a141741c6960301e41c41d084028110070b8a405880c0329016201582007040700c4988d0380722000c06c0d0140c1d41c8455080c241d03620341c044c50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 163120890 1250 163119640 163119653
    0x2040302100f02060709050a0b092115070c0507050904060b0d03021f090803070309030507080f03010e01090e0c09130506010803130608070212090d080304030c06110c120a14030103 79
    0x7140d00c4900903001300b00005101c40d204070170306000c40d0401440c4114540c03601200d80700d0b540c8603510300758201c010010001d80d58000440440881c6180e08020524032035510031404c450b02015085000300b094150b00207000c2140060f004c01a268125030040c01b42e00d0317529012004041369444039400424074500c00303050540110300c901d14002885003d4410015004000e412200c2103080200801010700109544500c6a40f08030300052003810300d80c2c503100c000c1d21111900d402410311404050400401802081c5050240714010021400203014500a00032010f80740c0c00705a4000d8064a100c100041c0030300d01000c503003c034070b0f5003203800c0d9000f9503101d079041a00c075032041015019401c0c1ea0303a40010440e2083d243c061041c2e8450b4041c0005285000b18505e0f6980f00140c0103500500d8108160041a0340c4002940610b00c6520b03800310640d818a4072200351050a804100f0543d07042c4911094480d002c24000c200034021091955113000c00c00c1c0075601c0c2da1820100601c0664084004420800d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 163122140 1250 163120890 163120907
    0x50a030612140f0a0507030f1103060406020913020a051c0f0f020301090e0a0f111305090105041b0b07080306060409180b060a0303090608041104050c07140307020f060d0204030210 79
    0x1001c00581d0450b202c0412800c1d65800540402085981b0802c810000700b218040800080340c4a801e001800c0032298001a207424019641914029400135a03112a85465441d00c440801400019800e001001501502d117025692020120000c52a0080c044c903845a002d0756981d103140404000b120300107083c0d0002034000b40500c900040ca0000e4111040320001158619203900084032030305010190356005c00c4012b00340e02660011b45811110381c01b03158900a9a1082059200000e4145090305000d140c0000d01820070640952800082c0182e119800c110303400c842e0807420311742c0c2c0c0f919520301040c0980302e164400030206180c88000d100e0310900e07100c0c4e480d060b401100c45151544640c4200209100c03a40320040119500c0a0100b20340c0b8002d010442c4d200e801043d140840007060404038040c0c071002c40300c01c5005440010703140c0400014200c2c04401c54200c02c000e604043c2c2ea0781c04510307031421803141c1510a00703000c20402c00c80a1150121805950f01a100041c85403c2c034001421011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 163123390 1250 163122140 163122173
    0x11202040f050f0603010b0316020a02030a0b0405061e13020a051201060f08030f07020f0d1208092413020303040812040e130b0f15150a0905120d050a030612 69
    0x490805800243c90f00c01e0a0306d0507569105401840c64580c0c00741c0700c2c050b924146014056006085800015a90620415418602031502d110340d5103010300d8841e00b8a86e006041d1a081e50251000007240c070440b085103035100c80412600c5034402c0c03150000500510040c0e00c101da015010620500d0842419001030f001c42d140003c9444242d40c51746912901c81c000c0007001c11312200c00344698000340c60948159002e004000d09502c050ac0b4a980702c04030070582d80116403004c15006810f100b0344032410040c24112000618a5100302190500b0651016402a06410321000c94034000710540d6401d00440c1c004100b808110385094100b401500050b401c00e00c03a0b070f20b2503c1e41c90700181c002034500881d4509558001071075651030f5278007800c1e03004c020780140810641c0b0498404107a1140c913449004108004413440340c130344880c40210300810745205504014060100c400012500801c00a82206000d0460034001c0d1503240200003207000704903d138448604800c00d540345409012540c3c01210055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 163124640 1250 163123390 163123399
    0x40905030a0f050f0306010c02150304050706180e06060f0f040e0106020d11030d05091e0102030405060709030203100c0e100e01120204121401090605092a1509011202040f05 76
    0x2c1d0030b2118140e803140144101c810103081d0810016040d5803140e1b035940c400c1c510040c00300b28a071b410f1041c845044c0d001160121a2680320100030f2004680140d584012042100d080d03050b954202201c001c000c0c40040e148600a801c04180d1030095003522090318404130360450210b03140d0743d441e86201c0071b25200380700d08009030090a04071362415202d0070b6007240c1c1c612400c0007945130100c0541c50400030840182020040d010300c03004840c9401c1c0e04c1c0321000101c0307015000580c50303003014200f40e420148090000d40a1104001c800c0006841c0412130f00d00401c402c55000600000d045400d0b6012804280b082d0350100c040340f00001c1490708039040d125000c0081e03a42030b2a2001400b0940100d1003030b80184040d41408031081d000250704842c024005001c1c1100206010398035644174005d8840c1038480c514103400c81d175054011180e1080349061000407100e00c0340000400c0b540806c00024100d01001e200c50f01c00035008400c0d90182c130700200b0400060b0700c1150b44030b5036002c10554001c018001c00d44107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 163125890 1250 163124640 163124657
    0x703031101052404060f0801060914090a080310050d030f031505010917160f1707060806010f0e09070807020705061804020a02120c0105071b0c0303081005040905030a 73
    0x104001441568840c00109403e44400200464100d40a030340301803965902a890301c8000c81e4210301e001030040100340d5100040f4400b42043e207848103440c0042d80401d100c0d00c01004110784254000f9040340c16a4005050b2a6070f511801d40b481c033411501e40116400000b0364103880100741e0700c601001e050048030b981c2004000c2c948011011085cbd43d0780b00c1c4900041c800d040500402e10101540c003101400941125a4005000210019062568006c1d070403024405820442c0303c0d8111002c181c07203614040540034250030954094081440170300302a0400074198a2041c5060261403019154030000309180c4441c517021600402203c0c045070305200501031907400058500b03242045c1c0c3c018054a50031071a003160110f050000a41201c4644c50843c8100152000801c01920081001c00d800c84008502c0f032030404005000111203101d4410f100a003e441840401c2024807008156035040c0341080080d11002d00540880f2820b17046240c2c05413070101c1450130000300200a1080d04c6103078580941 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 163127140 1250 163125890 163125917
    0x70b070c02090103021302040305160f0503060c03010e1008010212071209031b0303110c150708040201080412021c03060e010f03030207090c0212070303050708060a08030f1c090302070303 82
    0x50300451664001c0d081025400140014a050400c01041c5c4c0c0300014014101580d0752510340c07405402c2e002e0f0704d40d8241401014041d02994008003000b419042d4002d000c10f080001d80b4080300c0c8014843e0726404241c3d440401c0603000204900d41c02040480b009549030f03000d0540e01c81d030842082e17950b132010464041d50031022105602a205000e0b07050380320001c8070340c0c2070580b44c84010035078174040341050350325000e200c52515000302401c0140341d4140140389255200b031380e40308401030180c001030a11110f80304200040c2c0c0c0c840c20032039210368080f118191940741d001d0141d19041003419402c05200d00c0e540a0461554503520440499050090640c0240da030b81101c0510300c6640d000c0500180c20025046c42100c409402c00202d202a603c1140c1d2644030480d400821a0800c190440c0000d446000380f01031260300c801d0844d080007080711302c0b0610310312300510b09960340705155000c06000c030b011450201582100d601c4280c03c407007c0c8030a124288080c64000d40b1460306000440100d400310140b100e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 163128390 1250 163127140 163127147
    0x30a0b1c03030f14011802070503090d030203040911130603150308040618050d020102030304140a0c03030305010e06030d05040614040504050406021306050304080d0e0f011b140c0d08040f06020a05070b07 89
    0x34101c800100381d2070340c29408506c04c0302c060b510001058079207100411401d907407500ca001769044024080e81c040d41e2118101a034600581d4092501100d0200091000129416003200e0a60031281a4280043c41070401440e0f800044034071791001d0420b5401090000b0040d0300101100840800b9003a0200195110000c00650440e10203020340140d000380001400504042e0010b20305041c094211015105182d03141c0958590940040f00041d4440d801040700640d94080f454200400700e002c0c240c84c0a042c20001c104d40150300c500d40c1003001d0003000f014800719000882e8080c01000c0c0c414801407429003400d001a521000a1303a00591040d5070000302140300c0c60a0b03d0007180c2c803400403890400c800b0340c620041e0040d0961040b02d405075210146041c0024860606101b003031400205806074407203c09001c40d031000308100c981030340400c0140320300b02001c00c28000069050401d012580c507503042c01d070600380f0a40d4004203034a100140350f5011039000400782c10502c3c03082503a50000c1e640c44000f20b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 163129496 1106 163128390 163128431
    0xc01050703020702040c031b08071b0c0e06221a090f060a08070303050403140c0a0915061d010c14071d0901060b030a0b1c03030f 57
    0x41182050302aa03181300038071f81000c201100481410035040305268080b18100441c40b000501d801e0302640d106501c2d00f405903e03010708500640b0788a1801040d03030107294520300000c4d0000d0785516040c844510303090422031210369007204000e60603000d0855019110b282c2d036031400c007907480d81c1c130f070300000030710034034961040701410b007004c074140b00c5918041d400031040c580000c0701c2840072039041001c840840c1e0303010038180040d0203000c003418201030072990718590101f0700d0f20002131289080c1e044014010544580f07240102d0f42c584043d2034450f50742214001a0300c001c2c00c0da90b1558040d039100c1c00302c2c030b000c0e0210144c0ca08445422034100240d9410402041207180d980301101c0038801181303903004942c07170000c0120030f00b00340d0200c0ca81c4c040205800142078545813881e206844050f441c0c080c01e2017003148a40040c0c91846c01a014219010141c000c0a182031920321090305587c0b401c = true := by decide +kernel

theorem cover : BRFrame.Cov 162949640 163129496 := by
  have h0 := BRFrame.cov_init 162949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 162949640 ≤ n) (h2 : n < 163129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
