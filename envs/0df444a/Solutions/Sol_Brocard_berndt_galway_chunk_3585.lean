-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3585
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:05.335414+00:00
-- url     : https://prove2.me/submissions/aa81537a-c207-4544-936f-c9d002f1eb56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 644604316 ≤ n < 644784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 644605566 1250 644604316 644604341
    0x504080a030c0506011a030403030c0239012d051b010c080f07080714090402120a050f090325051902150901020a120314040b0406050106140a080703 65
    0x2800ca65050901800040c2e41800680d070034012000046140c1070304951485203081e00c81c5249265540302e4400f01c000780402c08070441107000705940d0150007414200e0040d1075030100d0320783c000d2032400100c184151103540c10701c990512540803400307114905c0072982d14104180084138580703050b0700e1041c1150a4401c1865a41f50403444983c0440000760550240110b00e9098031001c4094440c0041d20410201c21107141c0001400000015803861040e000d400d040e5151455090411101800003020303a002076626400e001644020001c14941d5030061540101c2c0701c0a403001507081c00d940710341d240e103c0e409407548181c1048204200c1300f0700308403543c0c0c2e005d50481d0649070802c4e0b40b070b0b90078980c815000c90184e214030301c9198000c030310b22032170b204540140794140c0003071448080603030300c0440361003500c000402419600c030719040300225541080b03803045100348900046071515140020440744107810100400c800c010618440c82103190450304000703582d040100c05550340c06403c40107040030b501c2c40c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 644606816 1250 644605566 644605573
    0x4020414011706010b1206010311040906031b1a030a090804090f020d0c030204120f050f0102030106080717010e0708130512070506010806040201020727090320010603021f050408 78
    0x100030700b48402a86600c1da40000b0755055036070391100e41c0158081e4061110f120b00700913010540d258003d074005401803031305c400c0c1c603420140d075031040d10100e4540341c0c001e071201d000400c41480d01080826440e4044c11001e000d1000c0716103d200ca1302c030710f800010920003125569195003400e005001d01614000e1850441c14042d46002c1d00104010703400200e001c2032540c1c1006000b58440740240295030560310492040c40101d021070f02c80302500c80f08054165103a00981d140d04414207001e000540c0a03100c291030b9400d1506041c0002040040300680151104200c4001130000841402006400c48406e00c1d214101d5292029420b60424a0140060041c032900031b030038200e001e240d4060002e0b90700581c1925205c1e039880750140d0300c4410896009006801500307040c01016074601c2c0503030504007411000b8004001490100f0111242c184068021035404044d100b5034440e140c2400c203070040182d000b0300c1030500c3c5070b01003040756111422030242d080e10301c1c8c81c4036003503442036003039600800154085 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 644608066 1250 644606816 644606819
    0x6020d050c190c080c0d02030309012d0905091810021c0f06090b06090f0105030408130f240f050f0904060308090307080616030c091e0e07140708030402041401 70
    0x5103103094113072190080c240202c1c01001c4491070301150440c1665000390145141c403000100441c0c0d0b00010075444548565003145002c03400f04a00400c00c411181a02c07441d01450900302009202c000041c6140341068440da03070442001c4010603c40b40903030300601d01507168180510000040701441c0d0070071898610700649504a00f00c2500150221410003c1c00c00a500460080c0b260900c203585215800950040b6034444652180d001198442d0040015500f8842194203404005115a2018039001807294050180300c1190000b280001c4603400d8032590359400060240c099442c00300c03684203000c004a0465070043c2424111928900b008004001090301ca1030200d5954110503c0c06019204034031012070313030040c00180140101e40305246180303003464010741100a08018000d00c010804001800550801000d01c40c0d1080c01c00400e1040c505400c20085500710000103010318104407070f8920101003220401c3c110345000d60040b541d2684c0c0d84d0b843c0049006084220728400d54021030100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 644609316 1250 644608066 644608073
    0x706091703070917010b03150c09060a0801090b010c050a1511040e011404020307091701060302100309030206090c0604030224071a060307030c12140607030906060f06020d050c19 78
    0x4083e00c4110104031140d80601322018200e4508880c040d0705030344400d1042c554a10103268003a404a0110190341c41c03c0c0c5c030b020211301a500410011030204915800500000949001e0b44140800a28106001d4812502c0d20b40e40c400315a00003501015011015082400701c030703089500e00c0c1c02c03200942561140c1d038a9900309035136424440d07141020400c42442101386060300881e07009000da41d41e0f004a03035050040e0100022410707420380025641e90b003030000042e29804941c0d010b190503500c00045081c0f450030080e0404c40014071a00c1c450704610580301c016603c102c162400e580e0140c0344c01448044030300701401c01480d90310200ca805640442c520381000b20700001003410404004049030640c49600c01c0c1662100740d40001400c0f00034094007400054a40c4c102d0424450142e58081c0b0301801e02c5002c2d80c10601e00381c0d041e0000a88401040e0309101d1a4061007006010100201c22000d00d009002911070000e6014042001030000340b109400504115049000c0b500e980301600c460918903 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 644610566 1250 644609316 644609327
    0x5060d0b01170f0319120b0a0914061503010603021308011404150b030a080903100507031a0a03050a0212330703020717130f0b0703170408070609170307 67
    0x81a03101d1610801401c209003000c0031041e9481099110ba4000c1c000c445c42c20190340010004103da21038070307580d042009003030b500d660380040100b100000018510085c07840d42488000010300c114010700d55600012503080302039007107d046441e24640144c544404a0703400d4884030156011241560038075201c845040c0143c40454011440303004100c009100b0f0403d07034810b032110090455450b1300300100081c00325089500400707010034000e05980c0c9a5182c082c02008803a0151285000290b81340310030980740441071510342030340c1d2003100c0f483e00480c59513131180e41e10559440001d0040c0d054504c00f042d09003080005041c0c90801c08402808030303201c5c080f06010901040c046030b4a030403150000c17030b01c0d06009100702c038126038102c4000740011901d000c541402c1e604c4101900781c65005a00d00040505050741d069004d06a400b41031a0345000e5410f0041030a00482c02900740304070003005000002d01950100c1e1a515848040810300da4800d040950000c05100d010064070301c400002c1095865204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 644611816 1250 644610566 644610599
    0x305030403050705030d301b02010b0f0301020c0c151c020307020601050901060512101205030409050903030145050414031e0f07080c0304030629010305060d0b01 71
    0x42c2e04540c01090840e03070440781c40c0300c40080040343c001007020f1f240031400020340e40d203404803140034042844440041e11140d080c4200040000503507445000c07007070b1407030219200003110a04034001d5003840c0c0440e4405880c0d5840040a070710540c41d0111190b5410501030543d944101a0541414620030615200019500c110b91300e00060103590004a01464040d0741c4078161003860703071218209282074010952412000d4881d1650120507880002d2000941a5440d201c034841c102440d100e52420f00541e00f62a405404a0300e03a40083c0f005000c1002d4500b143d8007003d000300210041010030000035408140701a003143d4490b0143e600c4100b065030140c000c5d40c006c40c828103942107403200600c10305031a800b5500740301030b008403440101c044402c030110103450703040266544503107481110383d139141c40e980c400030440c059904041020001d211603031040011252140e1320408540e100726000d1029040d00c0580715051569400c0480d5a0340c43d811482406254401c0d4203007038550f1200c00c40950300b33a55 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 644613066 1250 644611816 644611819
    0xa020607090e070c0209130b01060e152b11070c080f1b1e0a0906030b0702070302010207172410140306060103050417073f03050a060305030403050705 66
    0x100d4030000700ca0b4030880c1114800e21065a40e1984010103508104c034000d80982500c40701031082c955000401e1400860070700810243c0c407040070210f041014440c0310341820030740b500000c10a104450610188000d0680303801c031024094034440d41c0c0102d1044c0148a020f074500c109000110703078201000a079040b10015210f10307200304c0d1940040718075101c2d0398600da1f114805044010406041d52414140001540c83c62420070b0300281c110244003207454100c0b80d6001c4888107445400400c1440400791600d500300300c0910140c190907095400103581c88100d44100c0c00d034030890f4507a21141c28003d1001c1c021140c1010051896803c5030340180416a030166001c882c2d0380d00082000500010880c0e40e101000c0000e400352145580e004015001448010400c2c1c031700401d02d01c06070101c012004d0091400c18440e10040703c1c00710446d000e0907080304060540380c07580512010080900c0c140441c5503c06524245404200707a51402d40702005410380c1d920040480c400442c0200c10080040f0b1118242e840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 644614316 1250 644613066 644613077
    0x9070908010e2b0c06050c0714010209270105090c090603040609060c050403020d171e1206010e0d121808030309010c03050408041a37020601060e240a020607 69
    0x42840d140f2108400d1030007140045003c3d402e88100003000354220a40c4040040b604508180041e1500038024460148401550754002000c3c052450018804410483d032840e4094510b43e410000801500040c00790301e03c0b50903400000703541c0180d0342c011980003a0018210944909003854040064481244200e40d06428200141001da116900355800c4030740082c03143d0b00f4480c031134489450304503061500761081c04080091600aa8118010b541030340d1810340d0941d540d008003190f03450040e1001c0d00071810407c007561501d03800e503108074420701a2500820486145540078800781c4401109240322440319060400005a0042c04006503201c0d40c40300009010103508102c08604990088400504100c0300388002d206050404400d1060361038070500a81c5016451030341c00000c0891070301408504040e801021780348540040741501c040321f95000404455040503000f070321001d81c008034240500551581c0c01c10303148507024081c07050040c00b200555929045e400080d00e540044400030003082 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 644615566 1250 644614316 644614363
    0xf020721090b19030b04110403030908060702030f0d0506030c100917030307020a0f0611040e150306062d0409050d020708070806010b070602210108190c0509070908010e 74
    0x48184101d814544220400c07031a44050f5400903001004051001a0081d030f42d140c4905410404000a001950003071f211440c14514028001e8a0044002e01d9202103400500c803141d24621014244c40c07040710300b0f40b0042080c0d952503000c246000945a4a0340e03000003005030b02c3c807896801624440036281c1502031030460102d540040b5540e4801981c140d00140c1c001c00c440004240a0010b8180c0740340b1542c130104041c0080b400e103080540090701b054481c9441407003801105242c0d402044048503042c3c002d403010340350080c0001c000340f40c141d9040182081903417250114501804c82160507020040c0108440c07491410310a550b010f450707004402602c1100c0c404a604503000131880c040f20b40100050160360300b80404600c4a4010100840d031254092003080c03440911250051100b40e0400f01c2c1615940c03510141a203450101860201d08000f200e0f0188049000003801505540c0d05455444540d03e50f0003046800040e83e40c00522954a40243e036020002c1c00704034510b0058503600c0441c00034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 644616816 1250 644615566 644615579
    0x1121b05030618100608091606020114090604210c08030a020d18120518030102180a061106040b04050c03030d0c090b03160c03120c0203032a07060f02072109 69
    0x1180582c0c0c201c0280c40d40003405c100491060090541c011001010b0fa0a14000b1031883d0f000d140e45a005440540d4503806031a15044000001e1a4840d1107000106003d06280e142d480240403411504511600300414201007a8044c4c5814004540d07c9280c1301e54900d0190140300007508560300724451507003004e9a54280d880120804041650000340e0030345445100d42043d1070682c00b03050b20118081d04000000c825580c28806041c0c1b10528030760841040404c402080140f081a8200a042c40301000482c00e484500080c516401680711600355030030344503818198039200042e106658103110005000d41d000050303402c055580c004548400103101d885001e100c1d1a400102c03030140c5000520f02499000301c0c846c1c00040c50b4070f8082c0c10252802c040b007652442c25582e1280840300581e000000b440752692a50010300f007070205500002c4040a4030918240c00ca1143c2c500140c9080c2d00e40d00e03800c0607000703e9070480300400d40c09688207048404040802000303000d101e0341140412158000024171 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 644618066 1250 644616816 644616859
    0x3170112080a110109081902060f15010c020d0b1014040506010e190e0108010204060e0315060105030c0d0f0c020607111e0102041d19090b010501121b050306 69
    0x1000e901992950920b41c003418102c1e102030707006111440f15900e413412500859060002015041c01d0603000808109400c4806454090042e141d034021094000070000e070303108110240d41d80b111091a1184a003c0c0900001c0c401388600c0c40060010b503400001d00c50741d00c01140026040780c86121400311049943d04c100000c40b10100da125000c55144041e003001e9181406c55100544400a0205c00c0c050303d0b00c2c524162203009810a10306a0b40c0090309005903600112800e1043c1c004800410004107800400c0d035410001030002410f001020000c01d00c02c042c400e043c2c410651000c54200b2485a1269606001d031451291103005800b864002c107170068441c6440c000f00e0703000b080043c01c0705c0c2e13507021a15001c05849402e00100d55828407010070070003a044625821146050007503152410b0140c2040900c14403c280081083d1814481e4000030700c511b0805811581b007401c100a100c098000300e003000c3c0c4040c2000c0312a000b60144001e130071540040265018038016520f034000c48401e003444200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 644619316 1250 644618066 644618099
    0x810020a091413270b06180105130e0f030a020a0c0e0603210702031c0f050c060106050d02040806190b0301270309050a0e0f070f0e010c021c031701 65
    0x80000c8500d40b48038600d03140b038000103075070b6940340805030a0341441685210043c50b09481142c18039500000d02c8154601f5a4080c54001c08001c8104425494900047ca40c10840e6802141d142c1e180e540c012050141480164803010640c0113681d920802600c0080d20f81c454180e0403614031000307900c0420301d80c1c900401c240c4201130107002004800c1206980c0d001400c0743c04051500b00740204103030350040c3c9007031101e405c1c0a252845000b180015a40b0094000d001c0051007404200f014003400000b500c00090307003811202035051040e82c411740c00340140d01a200366004043c040c41864140000004030750515a000c00f1000820800041070350101400c3c0d4011603401e41d01c01c0225110b11810390355131090541403606ca0b00f004401c05541c0c102141403100e00343d0200e865044a0f004002000b0301c00e0341469807105591034512500c43d00c02901808507100c900011b4100114452010300310b44481d1100c00d051103840000da90029003034603005254007500007051401d40c42803800000e031200145840c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 644620566 1250 644619316 644619319
    0x503031308120703051206190b0d2003040308060d0605090f1b0d0b130f030503160504050a12060e0304080a050705030c01022505060f2104150e070810020a0914 70
    0x145042d014400b441031906d0702810441d4000440c5904038010880001c130000241480464551250060983c1c0b800715500000b03041100c8201c44141c008915082d804c41c3d0780030b549401c106200351104000305c1d05604e103589000701060303d420280850048006545c3d942040c5190483e011402c00380034134241031074042c01050700310b841d00c0e005c42c00148080050640c03180452070300c50091003083e1603800092030b0640c1c054010074000424080e81c60140d9a6541955540e824001e140c10325043c04a00d22001c28410801c0020001d542c0c44200a5030340c0145e040100721200702c0351601d1300c43c6482519000d200c107084401e482185000641b03400c02003852181200140c014000340b038140840e5442669100f90044542d00d071004000c1850342c0c07140082c14090180c0d0710340c00d485102000f4a04041c072081030a0310103d00d50002041700090100b240001044100c8001288074420f01d11a01d16203649600444d055000300142403194003c1035024205c4507125a4036141c3c280e69421140508038105928103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 644621816 1250 644620566 644620577
    0xf040515190e1327081c05060603040308130c03061506030501080303010b0912100207031d03060705090307030609050c04060b0f07030e18040609021201111c060503031308120703 78
    0x906804040f90b000700c0100d20081d00e0318140000111309078503c0188003004075101030340407800c000f4080c0204605100c00b40384400c00c11107410600002035550000410080400c00740307000051820800051241116a0003081c0540d000d40307e141140161404e44504001d1404c0814005641340c820300034103049480c0700010b14510390a0009206507a0f0040c8841504461101c81071005040d0406c00c0c9002c4410420005840792107a142c0240040420320340d10032503000503d5103000390756002c502c150704460365080130780d40c4d071507080040303401c00c8803036031014040340c1c5480040b41c11310801160703004080c107003140c0400803261100b5031410755010346265030ba07840000380a00c00019000340018943c0400041c081440405040b02a098042088a040320354a840351500411810002203950b21009004001c1c025031030110750101c124007a4610b110000141402060071010721740c4e01043c040c0c41c0c0039003580d07a50700d08101d03072000c0030000c0e114401c20341c07042c0b16125800c03920040949515a50540d0790 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 644623066 1250 644621816 644621839
    0x1b0c0504180308090c090a0b0f0a06170a0c02060f040201030b120303091203040b04080a2a3c0804081c0206070815060d0e06070903020a0f14060f040515190e 69
    0x180c001802d11074086a041401d18810180d540d44200029001b05819134901c0424000c0c0d00700c0b5201000037410416030941045855000103402081c90344c1c0c8014042901c03401036940b400102c0c041c00b20f14200f030707401008403000c50150b4031000c030040d4460000442251014203c5140300e03c42880f0894024100c07080040c082000940c020000700001c100b035182c0b5100031200c0d86850340741566030081c00d420300188440500200300504061000c5a07180e1031103403000e03100103014480e5182105000c002d03840300c400546420000c20000f65000b034540c40d02180d0901262082080b45030445034001400f61148200040460340f0490720984108050052501003500b09030510600b6000349a613000c50070303259241580b010b2810003403075100c0d188680c0c0e0801c2c481d246005015143c901c44e080050950100d00080c0550f801d414500340d00e606050310400d41d500d00c2c0309907600090042d5041640d00c603402084443c000d611030701c050011401c0307c11134a07034107500c2d48109507604d10040340c00d83e4010038900715 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 644624316 1250 644623066 644623081
    0x90e01030c03030f020a1a2d06040f140a05010501090b070210050a02010e060c03070306060e0f210304091e0528090203070b0a090b07031b0c0504180308090c09 70
    0x1034040113185070340100c41d0110503a0b03944800d9001104825810310001c1410402813410701c02d24440007050030080c5907542c04807070003140700c0700310700802c45030203551503a450f0003418560343d2110703400030014080d10f110350070b102c8103c401504080c03282c80c0c0054041100456950700810031980e201d80e004045940351060b020082c0c070030340c00c03040e444015550b132580c1007102000e081c00118480c03201c141d000d5a0300e1034006005022150725400c01c5003040381c9a0201580c584400d89a621001001c0b51002d01d020925803410100c80c0c00d4804000150001080002d800340760390300543c02043c1d06e80300c94031130200000024001c6a078104ca9102400c03a00480f9007420170048004141e42051920700400c2508540d00407078582070480e4400c4074541000101d0050103a8086601e801030040c0c0035243c0e18000f115140100504550350000c0d460103288a070400c1000807900c1d480c0001c20014205000030f020a01290f2841d610811040e80414201c00002d1444100032130a0707055424002c004040686400b207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 644625566 1250 644624316 644624327
    0x16110f3316030c060c09050a14030f0304060305101401081f090204060c020a0801090c06050c2e0c0f120e010f02030f01061805090403180b040f06090e01030c0303 71
    0x504a512540003000480040c0706064800d58806009840b8190700300c03194030303082c01191549030000081007070540c41400a540c1b8100a40100e0b10051828602450790303500190400600f0003440d40e0350b200028002440340d4041d0006440b07603c8118649214540d142500024083c6201d040750001e1125000143c15040032040c50179000d014211b101d1b481920394070648101c2c1d202d5000500460710b1080050300318a80602c040d0301901108000b84000d600301e990b10040b0309458003400f01482000b14007400b13405801c01410000c000901050418807a151502c02103c25070715005101c00c50803c40c00d0012207020b5007101c040404141d0701c00c0101601410100010210603d410999541340d620b0031403880101e001640c0034007500380008410354501038000d0702d0103c1142ca26024040380c500200510350f1620380c61a0b00c2a09410089401e001018080500c0030712a0032155036a58042808541c1c800390340411020b450071038856a010341d455465000002d0824071004014008181c814800a032040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 644626816 1250 644625566 644625649
    0x8090405040c090e0102091507020d02010f0c02091e0a1413050102270a1413090f020a03230606061e04030c0305010906050a020c0d030c020316110f 65
    0x40401c03044039515103071818191104a100004d20740c3d0080740c40340044c60035058a0880d07402030745005c1c0c6021072590200d00344040b00c181c040c1c1803001151a0036070460103150011b4540c3d41c010310000d030904d402141c24801170382510304440041020800a0720100151103070301c016920f201035051700360b50b1b05818005044208082241c0554081c003070302410340b1f45182e078900b21442100782100c181042c0c2c03042c001038807020b500190902503e640480c060b80c840da00c43c1c4180714102000403d1021043c144020311400b0300704002c0d04000d002070004140b00040800c00e910710409051078030944125004107907144001c0c0c441c90340c044000c009050100c0000c4039480000301000c92600d04199581c0c480c0f03101c00c416a0300c10381d4640d45a02c1c0c0c501c1041702c144102548010f08500c110700304501c0d8200706030f840b45000c00301c10a02d83d68501d1441640c3c002c1090302c00b40503c03540e40c1034003c205440d02e006550001e8885030302403006101941d2103460300300724484d154049409454040b06012140700440d1500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 644628066 1250 644626816 644626823
    0xe060103020f031f23070507150905030307120513023f01020d1401061e030f020d0f060609080a08090d082b02040807061d0d030807020c0105070809040504 68
    0x241c2052021000c0c90700b0605500b508004c50008010010102c2c010345e11010040121961480300100076266400200703031200d90750007269100141642ca03a000c8002c1101800c041e00c644030110800811661000004800c10303c003440600942e21094000c0a0360310703007600c0080d130000301007180056052000c1c0b41c00040d051001003100380c0c4a8001c104400040e40011142c115940000781c02400d4106070080b211240180501c0451a40c034082e0010715885e035012014414015a10014034524401d0b00018004103800310115568007071045400010a00c003440e8031511801d048002405e140103040704401c4804000c05000c00701c1d05640c80c4042c540c000c04506901c00b0468006001080391300e000b520031300f8803480416103002503081c80001d01d41c00300b4013551011030040100b407141720404500b0600311405820320300454809100d41c0090f00c000b41702e1841d0801702c0c100004007810740c0012081e00440c1140c003610255100c402c0111164412490044c0c02d58804104610642c00e15900440e8000e01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 644629316 1250 644628066 644628073
    0x105130609061407090303020615280b0a050c01050c041401111903050301030b0907051f0e1c1707030c020d0320010c030b061c05040f12020a03030b03010e060103020f03 74
    0x403509041c10490556941c0001240318401b4410981c04000f11500201d044001240c1c4544185c00580d801390440840406030403940c440c4d060b9076140707140e40c0025090740c0303402e603443e59111a0f00516a400804010015600706008500324100510445003946c0d00d03502001241c80c0c14400554840d02e41007001c401520910b0a004140125015544601803007681c650303940e0351450030a24480500500140302c590445c00042000d50b88044442d01501114004d01c403e038007140009840d1030b500e0490b140d400c17001c003c1740100103458032546908076620402640740075520400005509006184000b0003181e441c811307100c054503080340c1d0103080c54800e02d801c03404009902c038420810b04d08128002966910b5130344c90070700140c050180500e1440203581e140d0500c0021540c2c124880c1c913840e50302a9042c3e41e000814144410240f500d582103420042241400400f400000c0d6035081d00c4001f640044e24045c810031841c5410702846140d20030030380050005909580820500c0443d409480b0b0f070511 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 644630566 1250 644629316 644629331
    0x50607050f03040b13060f0e042c0a030906050f0f1308030a350a0b030703020607030504140607020f010305151917030a080f07031427010513060906 65
    0xc100300024009042004d19403600c40708603083ca52103411450700031005020050300302102a96009071201984442140c0103d00d06418020003d95900d0741c5503c03020001c507000002c1442d1900007203400700c1500c2640c035031000b950ba13070008517054081c0d54024621000100040e030402c1c08000040c00703540604907140c8140035a100fa072107107954428041d480c0850190b000d510307031f90b00013510b40c204501c408a455004500c580d03650070158000060128220343e0f540c05c0d9501c01503e007040800040e580c0581980da6a911504015015820074071a82400c60b41d00c41d100c1d000707400e24605460000b68054440a03041080701c0064000c0c2a0040c580c601d4503d2400c9445010380d03e4918120040110040c0000424100074015402e07602d203d070000c455500800c00c85008a5101400640c040308080300b18400b9203a010046015009103c10400202c501e942400910829900c00b001741c90750403855a041c08050103140b0342690412900064090400039000c004220540c001800c61403242400190b540c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 644631816 1250 644630566 644630593
    0x15060821040e0118110901050904050a060305030705060118061203050c01240515070206070b0c0903010518101b18050603160212030609060d140f0c01020111070c05060705 75
    0x541c09a010250f8098101118204c484951043c02180d83d4800032440c61300c8040000a0400e20542c49014025075540c000140e04241e50750100e401740d41e014040e0b0f541d4184a060681c0e80b003c081c011000361140d00c25981c5040c2c491440345200300c0c1e01107942c0d11000e401d0340d04d094070b00b9048140c64004035501c1d0b0600030f1600701441180c81a41042c2c41e9003048840c100024084045200b01c03028081002c01c00845015a41303440c00e8030350541d441044942141d8500300001303114014500c1041d010740c01e04081c4120307101049804245020410103d80031802d8410401c0155080c8540114006080e4100e0104040c403400700c40c1402201801c440740c03415914408581c5e01d501c1281c030300203502155551814220b90600440341e061807448280b07819810718400203101050045d01c0a8800c0350424403140400010224002c03d09291405a600c00b40c1004022a200e80350002c3c03a0707005502c1c1c6400900750041e550306680859802c440d410003100c3c18035090040c1076000300e1058610740b1440c06840c014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 644633066 1250 644631816 644631839
    0x50309090709170a0f0b04050a0b0a021207081303050d0204051c0519200f0301020706060609050303040b0405040203090f070306020702010306090203190b1f0203071506082104 77
    0xd10680d540d0b04640900d0706404400046a030401e4480c590480941000414070314208081d81e0b607000800703001030b43c94602d012841c00c0c3c10340380c0040c106900785003000344400156026181a800c2039036076081d80d5840c00d00449041900311601004200104940f401180c81880500110000b41e0001803038941c0f83d0300043d11412494184594041d0144c942c5010450240700308903042014030389820400c0e520b55549006640303c81034202d904208030600780c2d556a02c00074102c910316000390085680b0503e9040c404083d1600c1d006890200340c40540006d0941800000c40d81107a0350421550304081c1000c2c1000065030010300310840c103104400c51851307211014003940c002140304541c0107945561318800503041c1c0b03186070700c480c003081c1c4140104081042e424071a003403044400e14000860110100008071501141c1e03410203854000c1a080641e4150000001c0044c01d01440d88042e00301c2803c3c62000940b9481c0c041d0700c0e4980c00001c0c01480a0803180071000d480b803403010305681800e440b424510ba0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 644634316 1250 644633066 644633071
    0x3150c03061c0803132d141c0c05101802150f0d091103121b030412150e0102030a020a08060d051c110d0302030402040c02070e0606070507080304080c09011403060c0705030909 77
    0x25041c003008818005c112000c7d000f038280c00004006400e41058910b9950310488038a03015030280079241799220304002c41440740c50051b05051030100712050300d0442540c81042a1181207008040416a0580500000341940d1074005d00780034040c80c0c10442c400741000f0b0b00c42070314111601c0c0c08607040040640d4040c071007405030f10500b003209501c900c80d804074081da188840d084c41060f070b00100028041140082c1105039455045911216140e0b0041c43c404010b1071542e422000750b502c04800d101c52007910340c00400c02c43c691941c809030241c8412007080481000c4c41c04c000c041d0307409901003081004d01521259010522418a6400002c1000e161130501d158513208400007940001007004600e4144212241043c440c40106a4a0700704882040c495030007414851054a0200c1da107002c00408002c9500a001881c083e02e031195a1400c5c040d90b00e119040d88544100a90400401c0320a1444030403040c0542c01801001c207a140c80725407015590101a05907041e00080002ca1550f4507100b104a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 644635566 1250 644634316 644634383
    0x30b13020607060e240403080a1a04060603050703060f0b0403060b0312070606170d080a0b13020c07091b090b0f0910020705040e12071103150c03061c080313 69
    0x1311421403c17082c05080d0214034002c40808110000d000c00b007540594001d501011000e0002107205a00e142c1581950301c030034020350321900380500410000d6060704018001d00040d181402101d89400b00c030501e255041c0514140e00000b40002c2021460039000340030036031400341c207072100c880210008a40c650f20088050701c540703490741400c0040361071203540c1c580604d40541c0070780100f01250328000e10001025041c40c60032511080b141036190307102e41c402d44513400c1d510b0301155a011007140407074450280c0c1c818020110714004000150758a0040801d03d80c150955031194a18108400b0488a42080000d100280c0050060346d01a03120014248409401c680003881c0c0545490108401d49080c10184192500074008442d0314844850556842e40e81c89109030000a20041c08a4a0014090030081c42c03d40300c58240044901c1a00c01503000b8802030f40c009500301d01c003c07104900c00360750110050219000b000012142c2c0c1c001c1003212001c620902c40c1100c03901a40b4607038441e9100551554 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 644636816 1250 644635566 644635573
    0x90d0804170706032a09080706020601090b01180b030c070f03110606030309010e2205191a10050c0a120e040506041401030f031814030c010306030b13020607060e 71
    0x101d420600401030440180a580307424022448003988500380c0010342d222260070550042001030180c0d014402d820080c09158048441084c0c0e1940000e5461001303101da00c861600c2c00f5880171043d44a505140402010b103d992845a40391101007162030f40300070400c0c40194001c2c440c0c000043c405102520885000399030b0700b48459140400c2c1030030020042c100314030130fa00800c25200baa980021515081510444664001c969940d01150080040f8071410340103034a010100710112a82071100c04c000c4034141002c01c10110100c7d12240f100401100d901d0b4804138444000c071202e07201e100204011b50091056030400050ba95175680445501c0301d600d40400c54105a038102c5040603c1002d0703210134100d40130b106070005842011b01d0864107000117000d008205caa18003d06008441019a4084072503050800c2503403841080300f40d90540002520a000e003a51202c415072090180c5420b44e03403c412050015150310200720080d070314207042203030400000c1c007006001c99000e00c5100e007014a8080078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 644638066 1250 644636816 644636849
    0x80403020d111f0f0204030f030f0306240c050a0b07120504080933030601030609021201051201061e080f0a03080a0515060a0c0c05010309050c06090d0804 68
    0x40e040007509501c010400c00b00a20072002c6680010348904402240311a480f1500102580c1a0141a03082c2000d141c5a000280010030004001032130841070303009548255a402440c00c084054a4182c4034070320f0305100014000e40b814072035a81d01c003a200080e040031202c001187d0b0f1210308091030802d0035162107042000304070523140c20250130003031218030a0080116140903600c90540b4041c0c8110b16000d010600c0716003083c1001440d0300c251442c5030750201d8100460b8005050031590044480c0d43c00241011800a4034440718001ea4422044600da026a00c2e0b00301400c0c48000313244050784c29019900c0ba2800034240d506010b81c1500b0f6a121402101d04a0500e02d10f60710303003566100040042d0313100c502d4040100c0d911a0800350800d0380d190b07000c60181c5030b5104010002c0c83c1d505003903074085d00000c1e20201132034000e036400070b400b0300c82d5808600c2d050340c441c0198111048104064001c0d0030045281c002450804010400f001009002c0d45040c10252100c64040c0c0042d0000d42400401108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 644639316 1250 644638066 644638073
    0x1b1109010501020304120b13140309040b0402070b060114040f0902090f030a03140319110a02060907080304090509010f0617060a06030317040c08060c0a0314040f0b0a15060804 77
    0x4003405080e080c0019880c092404855003038080c03000da4040c00320174106000c01c0b55406000e402030242c0e5088419080910085203489031664002944280305602e080e4007603206042c940207403100c4642109540030030b0b54400d401074031307000d080c88034045081c03508110208101414110007406001c00580060b143e030952024016040300c1d0074101842503000d030151600107a40004c411540640503c440c030744a0b01c45042e5203c05001c140d103201401824074108071000715680d0081c00102d6040e6003214869100d080710039440b403a00b801508516002004148155559030b08a0b6400000786000000e4040c1e103031008104aa1203a0000c201c0c0440d51000b041c001901080420341007251000104001d0f8610b0750094102d030b403444608160a46800d00040178441d07404080c40003000c402045d142d0307515100c003001200b41d101481c03010100c0c2ca40f0a201c528400c0c40e00003d403049501541000c0c0c18071480d216010701940003015401141e4480c282c090300c02c161980c01b2001085e5a8807500e07021b04082c134 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 644640566 1250 644639316 644639329
    0xe15030a1a0d0503031303050f04061d1f0e061b0604050d0f0503150f03151b040305120306030f0a0c0906050121020d0f110c12030411101b11 62
    0x22050751140e411140c5440200728040304481c0c0085c100d880e00e03114400c0b20325081c1d46500034250700d0800104040340000b640d0743c001000c2d0510303141c0401900c6040c41da07081046081c87c141500282e61500c49003201a50900030b030400a02044000d100508001c95042801030b00b080c00800740700c41c2e8200d0428002007060400c0f51003035500690030404103071160454004d080c0d0000030304090369602242090782054031000c156188082c4090143d805181221a403045d000105880c0365480e0000300009141154840099400392903224000e01050303a010601c07c1680d8101074892a0306010b070400710b4140800400141c5d88940c4182d02d140c10651070040500c0444807590302c490705002030109020050090520183d00044800d0401038540c0b01a40c800c1009002000000e014903140007841005816804003a060801d03600003150303580108401e0120403800240d40041c002c00218044003101d00d40856155020340e0301d8500302c6034101800d030b01102c09002c00704c0c0c10f54203240d258048460364200131 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 644641816 1250 644640566 644640611
    0xf270306060906171506091b160c060201090b060904061b030b0406060305010b120901020d020a020a0203010b040b1e040b0405042105040807230a08060108010501051e010e15030a 78
    0x500141140c5c242920028080b940000c0811388201009000982d80d00103410150306440390004640c2d0300c81003840070107400645880000c0c0c40101d409070740007070003c0c41400780845a030f501075400c1010346c5628045c48161038000d44202c07002601c40001403100039030008403840c000103d03500494244001c10a010443c0d0381030300729004060514006204003420030045032541260b003074482c18190f40700c04040e4021700a20ba1146103840c0001242003106600080c40ca007614001c50080206250810403c800c0300d0059100a410407285807076014852148a070254616178054408078243c114400041e044076000c0310100c6441140c441509202010001e0880c0803041c00d0410616090a184100d40d50f64110b01c254610446146000c40f40e82c103040c04104840c5034040c00b003928558980003803949074482402191401d6207080c00003e07240c5030641c090410344c0ea00001100c981a045401142c0c2080c07540000c940021044c0651060040100011440384001c040001203183c0c1c0c82e1001c80200e1085d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 644643066 1250 644641816 644641859
    0xb09371a071b0b190e07060512090f0705060a110a0312051021060902090112031d18060d200a050d020915030a0506250f270306060906 59
    0x90710000041c89025400e600260342e9000c0d100a41c00124402c0040c05400441700314a014134031000844d1500803000e40903039024101444002ea0b2014500e80da0341406100b0503135503900608003009107040c1b0360020840d1034031600e41100d40d000451011882c01c070025508800040c01c007021800b80c00860700c205604544108074400b10b19140907000817017031f10001c80a90040c10041ca0940812000d603124881ca582d014185041940c2c2d1001c2e810101c04d04454140e0100d10300d6141c1c2680b00740c408280ca41200c00062040f20000120200d0703039620031000f81001d40000049903d01c000c40e0000800250764a07155500c51840e6504400b40108048a0b50090b4000e00102041078010381e1400f0180e68041c0706101c503000b05c50342441c002031400001c1071025169004080901c1000c20740310212040c44004200324000111075808100d46000f6250603540014403403800c0501001d2001c12100003208118928650080c0c4070740300c41c01260001c0c0d100014003503585204010340e2105810100c141044e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 644644316 1250 644643066 644643107
    0x60c2a0303110a0c260609010506030d080c040909060b041503021906050d05060105071406070206070e0112111927080d0503190204060c0b09371a07 65
    0x1020f60f600b100042160044e0741034100c110170b403104103c00e480400c451072401d0104490a03030519030314490082205651440c02802104240d602d00781c000c5070500e0184541040ba06d19103860110203500801882c3d900310f84040d01c40c030070414035a41d103010346402c09c06407483c48000180b45104001850140403c80c1c200903086a1003000b0068010042d120304c11100c110100e960750380c100049699209a580003000c1080e40400070007621000640305220b0801c603000c0f0784068440d640151a0380c03071a0b0b24840d0000f50b0680401c48003d0300c6801c901c070180d0012a04508051507540812403a040640c802ea0001c1c3c2d44a861503021114a06145201c28010103060b51144c00c10000c2500c80700da040010701400000030100e4000c1001d051110b2058445020841d11152210b1004103080c80e4080151040d008200101d007014402080540c1000344001118103014400c1241c000244418402240014050700b50540417442881c0001052800c02409004900c1c00ca07601400592600c40450175024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 644645566 1250 644644316 644644333
    0x2c1c201f0b0607060e030403050706080109050a0603020607020f04090c0902070c0f0b0f03070504030c27141b040302120309130603030c02011b060603060501062601060c2a030311 78
    0x440b6181180ea001c1c0d00300f48007285554407511813030325502c00e5600c0148644504440016141da12120b07003030684215000c1440603449120700d0000342c502d01e02001c4e601840410480c00103141140103030380e604502500c0814090020b855806040341f181d4412008583c000a11008108007405110050039071580f070f840d8014107103015620b0030700841c2c0364160400c07000000714083c1c40c041c1003aa03000390341c0721206851060320f038070f081d4401c0a2000800c14009802c042c41d82d003e0300716401100b01c2c014030184a206599211a03005900c0d0151020682107402c0810020016843d65400c0d54184220781c0000d640c0d40c0d02074000e00c20790812002950b0056858940103000083d0311980c450511602440d1031241400110030340ae500c442c20707800092001c0d00c1c061000042042d03d4002c18100c44881d124480340031216640044010805080084001004001071001c0c900039110500114082d402031614114485200c0e40c1560014682d841d01c07203800380c0c0410801d1f5014039184000007804014101c2d55 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 644646816 1250 644645566 644645569
    0x303030e250e04080c030a171524091203040e060303071a070e0d030e01020c18010302240301060201060810140a0e030c0307062c1c201f0b 61
    0x260100d010380c0c0b42c00c01d10310021400780036a200503038044001000c1503958800d011103002c3c18011050040c4140c1c290341000041d038492000c014120301d100d01030801000f443da054403080300c2014840310951141000d005070007940d118000c0c100e92001e5014015650782d420725061001d0000020b000038031a078400c120040006001a0690703000d8981c071481d40485840702c4030140e810040d1140c40ca41c2151000e07002b03400307040d0b101c8075421401400b0b8007904c2e6041c000900740920340b000c910328203691101d02e03801000142032070b4901086042c501104143c0541154001c400b540d8801c1c0e10900050b0b44440c010700500100780070907049200f45010821280710000a00c000707a40008140050140e80c86026003488001401200c05c0d050800d026642d07141d500d49860701c020001c0e5000700805403040100341080b00070401031000400a08001030000e20441401102c0d0844010a09400c202d20b41012400d1075258080300c2d19404c24403c041c0c881c094509010341002552242c4603410141007110450300e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 644648066 1250 644646816 644646883
    0x30901120b01020c10180603021908060303040e040510181e0302072402101808070c0305190201020c030610060c0f1502070311030301030c060302180a0303030e 70
    0x10901000001c1400110000143d0400d403802c1540781e0807400e820b40101c1543c0d400315221002da00000da80c00c200507101c4008038124000ca50380c0c41d5202c00000394a52400b0b00420f0190b41c0b001c4004e040781c0c40c02da10f60500010b10141624121016441044900b804028034000d00300300f20b454082520200950b9100ca918406200710070040000005904e9800e043c4244400009445d4046510104c1ca281c061041510035510b0300190050265011507030040340c49005207145030f42e200e55110006d40183d258800745501c14101190781c4803c0389800030001e10140160881d01e08441c8950092940c64000607060070000f0b00c1882c4203030050000c20a6481e10440030006a5403545801c0a180c1e01c0c500d48080c2c1ea40412402a001089071a61803240f04026002406528440c0d07481083e03203210b11441c0c9940340420b0100401c1c0145e501d005224140c400d0b4050942060403100c0361283d50512000714020003407903002640000e80340d00c514000c8200411100c7d04003007184c040d03e0784990401854192 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 644649316 1250 644648066 644648087
    0x40804050609010c0b10080706080615160609050303071b0f03050d0e06240607080d0b010306150306170a1a0907030506010f030516060206060103091b1202040b03030901 74
    0x70425021a00380b245920441409905030351103406003107141413550883d6542c0c2c04921030031003248503074030300400c01903c103100c001d0003804040c050b05c4005216110020081d00800c086941000d200b40403200820058040c03c40c6043c0100003840c1d0b0b03418031100c0240740c42002862014484543c011003000251014401c012203501407a095448110003481c01019020390020307005075128550074005004010f03c1d50809c1c0d179266109013400b6030701c0001400035034042c544000d02200307000d02019020502540051036081d00c140340004045899a00d0340109420050082c40040d40d60207003440446886001030159243c403170020000c50403950795082d0f090a041440101e08000d450104000c01410080c0d14040c66028003a146d2561711244041c00701c085900c010307103d0b846101e40342042044d4414010381600e01e141e02409040d81c40c0070041d0013802c1c200c03034101ca0071200e41c1c0c045a0340b140c0004d040c9000c3c0061940c1d4031044501401004103590a2012240c0319070010003075118540c2c3c10482c0d012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 644650566 1250 644649316 644649319
    0x90f0f050c0703141c0623010816051209030d05060604180207060f1107030e101b020310061401020c1005030112170f25051e011e090b010e04080405 65
    0x113a06105207040d0480e10301840d1405050044415140900c4e205241c0100e03003a252401c0c102441041c6400600c0c50041038004e400d404203d05c0c0f408580040b51007100c8003400300315414154900a045026400c5516048914441c01e03000030401900c118060f004182c0c0100f4201c1d5a6810a424085da14925502007995107000070740c0060b8050402c40b45070403114150394420703810018408500d41c41e0902e070b486a00110002410308001c1070052a007251a0200e0503225517450b03042036101500312200c0540c10a0070b0741e00d84624500c1d503407601c07514000c440c050022003c00340781d4080e02e4000a4642b110841450f44100707907440718441c0d43c13035002080c1c0c0e044410b400d86580644207a4202029101c0c480c9070a421090000290003540a036180c3c010107850900344406900802c40716803050040f5400340d401130682e00407040c4440000107d13441d240b0b85078060000024062141c500c182f4540039441c130340346041303615540c0342018082c00244240c010203501e0000c854515080c0d548900500c40d41c090389 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 644651816 1250 644650566 644650577
    0x609091209010c0f08071205130b16121808030304050c220f02071703060a0303050c0f07080c0111120406030c0e1305090c03030a0507020f010e0a090f0f050c0703 71
    0x501c582c032645044541d01d0300300c0101a0491203e003400e959590001034142d035a40c1003056402401d82c4214115040036008640003103499051200303e0060754008400003500c210b00d220004080303040850721102108076621080400c0480b01402c5d425094250310400d825042801040003044007c20305503848078088405049400380d01581c1c001103810b183c21040c9030f80c5403190782e8041030300b25030050000034090000c11408402d480ca4954441c0310443e4800d0f007002008404100103800340000c0c00318108000b0540b4100d8614091240c508440356010f55003e0340071120500581d41c1282c40c00141810f9030740500702103d08080404041e00c2588a10f41c101551060003c0343c4d544a142c1002030703c0320007410406a0a0940c8100c4040c00e415502c040b45030041803101c5400f460300000325101c50100e900c500742042059005c214496580c2151503050151344000c00d01150b54890a803400340076103260008400403601418030440c1c00102d0b0051107580741c40d00380109206244199105180d261805 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 644653066 1250 644651816 644651827
    0x20c01060e01050d2118060504261902010905030d030204030b0a200901020114090c1009050a050f0d0605070507050c01080403050d02030421020d030b100912050c1801080606090912 79
    0x701d0b00740111b03815088018030705840c0071515a40c080010022900c0910307035200c1080c074402400007200c80e82c1040921550200c603a081c40c2ca00c070404603007a4540141045e0224581c0c4a0201e42000140301140c00000da00160a00c20042c01228103a002000030314208626503c450f1000540440004500c8001c0d0000c14850f070b1a038802d4120881c1c09407128013034004c50421000440d07558020300c48480c4100c01c03030740031901d07828803860390002119001442c1d070440c28644000d01c511050403407051500114061101d50100d4000d0241e5401592141c0d60640c0d90305003800c003103003000311210704141008813540c2448007089d44007050b10b0810090010042e920340f190310700707800c0b822f240a105010a031304895400d02000e4001c03e4001401149440034060b80b08217004009140d180d40440758080769111000b840301c40c41c0100d03503020f260303c144101c544d019089030009034481d01041c40016500300c034000500c1180306c00d102258100300e0a90310005a0300b040062070b81c035a2118210300e610001301082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 644654316 1250 644653066 644653133
    0x9020c06131b0303080402030f010515010f02030d060303051201080604021e0310060308090a090203010b2d1c0608010c02060604020a2001060e100305030d0f0906020c01060e01050d 79
    0x10806200000103407144982c0d036403031030041c0c40c284080318240e06c02e002d8801340c20070030041801580c3c403030b810540c110407108208a0040d90801c189031a070780c045100910a506a5401610442002e91f00036194141c4078203004c500e00c19107210507000f080068000c1c005010042e02c0e40c3c90002c41511660703030550800012200443c1ca04040000b0085e009820b11500109003c1a14010301c00c0038400c0d01c0d41c2c407210351036864079800d0348800e02c5440c0031202d04121090103403190140c14007070318200c03a0b0317400741e21304404842d00c540b42c1080200100f441001911760740c407010b20740b08000042200f04002c1c46100c0c800003006e51a0702004115502458000406501c61403140c0d8520254600c0c0703121030a100c1d100315031414000c000c2409942ca200c03c001010030f0324240c0307907600712040700c0d40300000310300e1301d4107090320000076001c0c2c40c8140090301d403280b40c94030004006001502080718410000540c0034501002c0941c00319041e03010074050512400c421010490003400d8900994112a0f08000d03c0032424 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 644655566 1250 644654316 644654333
    0x715051c050c2802010b01050a0e060903010204030b0a05061804080a031109040f05091b0a03121713020301050a1107020915030604050706030c0f050a031503020a120c09020c0613 78
    0x10500e202d0340c3c1e140d215003541c01c0842d9008605120031303a000700801c0c8040001501c440c40307812034401c08141146800403407458031400501350307420098009030601e9901d9488000c071100984075144003644900401c040d40c100b038803060a01d000b0030000c0f03a4090600c3e80b82d4640703e114407000c0d00f0425842c0c00c0101844910079040750102d84010740100170854692080c80c00070310b0103984071051030040456403141071454031803201c580d01c1c004044001407803544e81c0f0921041080499041448403184820340284d9214889502c03442800592180d12040c500c10182152801403484031801d1130100101e154014403820b40711a41c6d4103460b140c04a8981d01d0f00492524644282e481e85071007072004100800901180440403190151170602c0700180ba200203445010ba003034911400981e06120700f104185c841c0d00103911360000741d604030301e6054030798000c0703051004150081c007241001da00904040010710004140202400340b411820080c144886944498002d4103040e011070307804458809201442 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 644656816 1250 644655566 644655577
    0x70b0105010521070507020901050613300308040308071809020702010306030605101e0b03060108040219030302011d03030903040b09030709020712091202180c0c0703050715051c050c 80
    0xd5800f001e082c40c141c3c40062459211110890084040760300004441c1841c20a80d004a441c0300100c000103400c2221003811500d40000e910000545000522031500307000d404616068044e55800842d4501410003070300100014048600b0450040317903115140c1d000c030140c01c3c25950003607005641c5100900048015142c903800c050800f6141c0401d01110501d444800e08c222480c21510344403015112411254019442c41000f5200b8010400142d0035803203070b001c1c15030043c8000c10f0111003500490740c42c00c0751500b9030822005030303648041080028100501800354010803070019461440d00c00180390b01c030301851081c2c40f140c00000c41d10900741da40c240442405041066011905d851090034410444001090110042421180041102c8600601905201d0b8002c0c0c40c3c00264182810804150322000b000000840c409025410340c2000a201100085001c0d100806140303040c60321840d843c0b644c801884003070120070040300107012282c81285001560186c0c000074a561a80c00c05046407095 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 644658066 1250 644656816 644656867
    0x1060807090b010908030a17060d050109030c0c0f03050304030605090f0a06060f05010f21110a120506031c12020d060905150114070602030c160f1106070b01050105 72
    0x101000894901c0c1c86078495101002e090307a036888042d6550b29810344030b100b00b120210005600250300d100d01c6003031030602600044003910030449003640e511780034211502c2d002d00320001800d0b0482ca005004003444d02c0c2019081c55903459281c42d141d0f54405541e80700354800144580d454000144113205c00784190450071039030a058810301e6099241c914001c2c002c5010700c2200348500707000403075154032400134405407000303640741c40241c40b00e000603004080c40e401d0342415500d0303101c03000304015400c11300107407040492940380d11525070719003041e0700160b40009040a0003940910f66601003140520703095040c00705a408e200240c3d0910300340c4034002e4403501046040041c1456000a0b120205900c8948a0030004240422901540f401181c012070304402c1c80703125a07070501a2002180143d4010f50b085480142e06505e400884003500403546040c082c10346156482880a0060184e840001e001c4c1500c2140c4170b41c40c1854070754451101c0307401070007414100040890384c0c00c042c0c0560045684440b5a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 644659316 1250 644658066 644658073
    0x60a0f08060303270a0e040f14122a07181b0507030c03170c030406050702010915020919080a03080903030f0a050c1c06080c0316090506180403020a02010e10090303050c010608 77
    0x1c0c14103183d5583e540381403007159255103003c040165030a001c5619000e010080300e90350b01d003880c0c03105482d40e1150a414881c0c44bc00d80146d0324100e0490410100c401040e030010555200c0b0900c4000b0f60440b03001c0d804001c280d0301448442030500d03a1144c00c880b0301d84d0b07040c02e000300d403100d1a090031101540f0345a8103d00e04031000c014440e0100420003d90b100d50f02ca10424441a030b40d080049081e02c6503020300411180c0c83c110200000480ba0b0003400012401503c5882c02034147d201d0fa140d041e0036070340307e4200d80c8c002e08260b82c10b050b401a00664403aa8401c0154594103280031075000301d820003052945425598800b040100d145841103d0050308030801030100701c607600011038001e081520410402d489001c00c805180e003008101c124409210407039142c20245046a00005800e00900c0c4d25442a2481c50191420a506003a0f5001c0d41c001d50007050010b81d07502c009080c2c00142c641c0144200e581c0d45c0821545030b0b01c506084203503949427400c5500c40410358580ca02408080d004000b1501 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 644660566 1250 644659316 644659321
    0x90c2d090504020928051e041407270b04060b0c0c0a080c010c0b1005270705070803060d02040e01090b10060c030203190e060a0f08060303270a0e 64
    0xe003a03810450040b802281d4494454450300e6804e90070403202195000c09401029042444c00400d40c48141d1040059494051158050700120659801207030211184800704a003000504420803043c00504820184050380c07480706880035001e04a080c006078081503c8a0407070a00351125008107004100004c0d030303d5142d140711080541c4541d25141c600c1c2c000c44208000180b4103000042c02da581d640180c4500c04008441d45480010700b01c014403940415005080c0003403a82c0300c40303030308000c400c60140458201120703564403014400780c040c105500700907090004c1400314460b1011650082000c48180300c0b401d40510128010b00449440e92a495180600710009d1002c483c070350900c40ca902e560f62040541d02d81d40d080c1d98010002c54082e00503441800340b02c48603c1c5150280700b58181509046076099251000035890b07500c0480700400043d071003280e2780d0405400403c03842e00b20344100c010f03506060070401903403141c51a4903400c6221410300d6103511030685803103180e10094114940341d584d880c07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 644661816 1250 644660566 644660579
    0x304091518091103030412030c11100801061d0609190b130501080901110a0f050408100b010e01020d020c010c020103020702060307080f0f1308030402043309090c2d 72
    0x1c0400e5241a070341c014100f010042549408000c440580b8000f00400c064400151000c80d22a455101c046030580da282868101c155268100118100655501c23401650f04108000749030f00740c03203100801d1610110792044007a0350750000780da41c081c1e01660340990100c090040c0c001c0640c440d6000b0303481c407600010241001d07a940c00c03504c01500c0c0283c0302d9000d191550300c00c0354203d50342451180001941444242a41d511685010721481650720700282003a03101c41c40f081c1001c140c0d00f9003100d11580c8410007040365812000745100b0410034005003c1031303100b2400194031841c403480300504102d01d51780400116070080d0706032803641da0040c00e4141c403440c00c0a0040e200550665a20038030700c411400041a0100090450344603c07001c1c0f2040c0342e01541e9680d110382d540c1020700226400303515515201d2840340541c050325000e119407100410356103030411002c402031101d03811020354141400c4100d030108440e0030b00b4a0868110000c010054000d250381140440e01c20111102100750550001421 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 644663066 1250 644661816 644661821
    0x1504050405010c020c06070209010306090215190905010f0f0807050f0f030f0c04080a0206070353011206060302030d0c0b060f0d0201030504020f0d1a0907080304091518 74
    0x48420f54003140d9840c070382c417010041d0038025030790001c2d4461012001800040e01075000102500c0c405407000d281c903804004070a2580d0480e11a03000c482c415921525991648900d0710350080200303080103084400d05600c02000043c80002003014041001c012403400c5100d80e003140e0900c42e00c900d441e501c65843c035801101e65403080c1c61406821442001141203c0320003412142101e00b820010201c0207107a40c00d220342c030703002800c06a081c0074094aa01d25500340120f030300101c2251003c808a4004c280a48800c60507903810804820092451a280041401c490310344c1d05441108507030249010b9107141c040090405a003000303415001d02c03816070074507940140c0b0000185100700c000940700e42c0c448050100740320b840c3c00c0d0780b42e00089243c0d00e140594080e03488160054006400342102045800104544030400c2000700c42d04060b851440808406c1d044050747c001c0180005490640d252a090382d550740654055020403a5403019841d00c41786929180e00d00822212056083c00554451800c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 644664316 1250 644663066 644663081
    0x15060706140f010f0e060f0d060c0f0f09030b0402150705030a121b260106091403010603030c15150e01081b0319061e15090e15150405040501 62
    0x20700301c5910049a401242080341c80e0503600e403c0d580c1940b4514010f443d084040010b003260b500b001c0c070b07072644078415101d06074500307590390049001040300f03800600d008044120340e01804040103100072000f103019600601c1401180c0e0000090742c06901c450000440340000210310722150035000079110100000800030344500d48140d01c40c20100781341d941176203085e200c1401404940d00004000c10800c68041d02e032001c9040c030340040b0042c1c8a02030f1004007890620a8200c0070103d0503100c1d00700031046090f2500124035100fa0000c3c8206c5280d40e8010300030f0002100012300450072909800042d00d01c6600c6044d2031069007280e000c135540d841c550200d115000303000d000c1050154260303201074900e0341503e015400c0c0b03010340100703c82c211412020012541240c01203403030684490b01000c081810121741c2c0300980040d40000359440040000d500740300e10380d6020311002401e010000120f49000329030b09400a207007507000030315982c6801d4207610021000003515800b602d010140418400154030039034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 644665566 1250 644664316 644664341
    0xd0903020c010906020601030b04060e010912050408121201030303020306010537030504150c0e0402120f011e030b2502070806180705120114190f090305090915060706 73
    0x440341c888008a03103c21023408050519039040380850b00058280e441102180f030701100001c0c15000d40d50f22680d00f42d8120450b04001000440c051100c6013050000b0220a0100580d01e850b2610a100d0a101c03080140700240074958048009411a40a0000c484100030300c00100c00c0304504910b4001e42600c80e5602d40d1441d404d0940c1e109101a000740300c0d6a00030f54000ca9440d44500312001241c6c05000040b0106080004803078020400340c03198005040030300c0348060840043e15101d0340003040104160310074071070b1742040e031103460704d0317825506a000a13039410172089460381d52461295058006401c680c2c800c00c60070782d20489219580440d1280c145d80181050381c0301522400d801484481c00e02065001c140c101d10f0080040e4a0074945000081d1034031030010031401c4502c50141541d1a00b1110030b41da0401c42160000304600d5842a190111004001041144032030f4500070017501802c0f01180c010003914020a04440c5407581030031966100801081d0354010514020020f0188001440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 644666816 1250 644665566 644665577
    0xd0203121b070603050628050303120613020405090c13050a080309030d0f092c07020307050d090b030c090415080c090f01030206070201180e010902190c081c020d0903020c01 76
    0x7050180c40385c02118080c05006181c034410030b4402865044030122001d09907032105041d2030000340341d141880582282d403112510020b01d80b400303006110200d1040c00a8501c0c1d01d00c1004240314543c0d649030610340214402d0481521441c1072840c800602c406900003a42c08040e895000401e14070000080000304020340584e100c20150140c16210300240009809c0031030600d110074032088449015481c01e0035000c6c5000c0c184501c1d04411640540001d035070081c016000040c0c0390081c007a0803c5445022081454211505031030711400a54a001c0a401141802c400048100c180d54858010468000c079049003100d569545110071907840000484440c041d07116800045d50781950103007206c7c1200c4e00074008929009843d40110f900c06086514800c441c180086d01146e140307c100c0b9018084d0400450060741c402d2000920040721200c0060070f004c2281ea41821800903034071900741c1e4682c1e0b042e00860b030101e012000b8410007a00034103400c920749519100d00c1100741a8005965450140700b80c071603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 644668066 1250 644666816 644666819
    0x12020310060e150312071a0f0c0901110307050d0e0f030c090c070f0606080705090a020a0e040b01020106030b1003110a06023a020a0b06040c09050d0203121b07 70
    0x80c0d400707450207031040500380a1030350b0000b11401c108840300503044400038141c800701140303520300d1000b036040f0309410380c1c0c1000c4103000d17000f0881c65200b045801031242d0607000103a2400660000c520300c500c1001504004140300c480c04101001c10668080c43d92140035a6a8885001d03001813010f01c91040c00c5108400d10a042e0040b42404626070500200147c400c14590350307586841039103035014840403180e400780c582c1c0c03000102d4210b114450142c40b907000a441030758039000821068540140103100740501c10025000700d15006403030402110001d540c00b141e400180d400503070040c11140e0014102001e04020881da110740010440300341c038411101a56116040021710115030141e0103a00056400441c1d8140242604280c0c2101450702d0b0a0f0b0510f0300b401f11250051480d4a92085405039004010a40400001c0301045910110680e001c001c1041c580e50000e0507a84a4459123000e503000502d0301d8155203050080040307240080c0401c680e584800c0d00d01c644841d1007015600024001c0a60 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 644669316 1250 644668066 644668093
    0xd2a080d03051902091f050403082b060509040b07230417070e0f0c13031b060e0d061e2901020304063c03060e090a1a071206120203 58
    0x5d45151140150a003041150940400c1055049042d0034009103d001c2c0b20010014041c90b0050a041106165501545040c40107408440030041144d100c00d5040082c04d00c0b550329075000030740e40a900316203403c000b0f0311058020b0740c0b980c1d9503a2480c80c0e40102b120148120f04001070084c42120450f904074502d07104020610303500d0f00040e01807103100e02e44c0000820703103685102c2d0a0540040d201c1201030303c0d007042841010000380d001d51044071801a04400c180d990440d801c4201c00901c2681800c000080a01c000100d40c4c2e00b01690007000c099440c2441041c41c015644200017450000380700308080b00c90401c0d5192450380b007100034030107141c210411082e9548007005440c2118151707254680c1c0525950f60000c044030900701d001e80d88100008200010b02e81d12206482d1400c242d850000780d031410a6048600300d00002c110302103550000d8540000100040f031000f4043c1d244601d00c00c80b64603401411201400c60b85a02c40c083c606201011640c10420b0314040b5140d4400c81c1203454101d0700d180b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 644670566 1250 644669316 644669321
    0x615180408040b0a090909060b0103150b030106050a03060806090609070f0b03010302220906060f060201020f03180a080301180c030e0c090703020d0e010207020405060d2a080d030519 80
    0x124014280740c000d00c000c001000c202d502800310010a0300707049018540380c5c2d034810308660740c003d400d8810b903840b1403005010356098030814041744509205504a0ba00f4000401001e00c81032140c4c0c001c101000072a4904503120b81e110380040e144003000d48041d03040c610341042e65403000307680e4621680111903002924040c0f400508044079110b07069941140c0c6140c08000d03c4528500d00e10301102c103200004041984140b01d0600124460700c0c0010b2000d0074054010400c0420380c2020065a204100d00d0390300b0080c1c0c005403075124580c1412044102d903003681b2581412040d81c802480c890020001090001d0308208408500c03080050820001c400f1001c00c50544242000c098141d8003d13030544d1160b0700301142155030080440c20003520f030002d4090400102c0d001006046126507001c681042145040c1c061aa000281191032100d91031003030311400fa1074251001010380441c0322079103030354640a8003c2400010042c1d01c0035070300c1c0741800e41c02c047d000d0304040f2404905846411041411010281f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 644671816 1250 644670566 644670571
    0x3091516021203060409051f0b04020f030f04020a050604060305160c150911030a1a0705030709290a020d320c01020c2e09021005090111061518 63
    0x5900900341200071074400380d460b0780f02504680e0041e8907400c5000100340304005c2d0700900c02d100b20314125405a0707120301c6c00440c0c000012152140b0300400080c428070000c40d00ba280c000c03c8226858909490b58800660032141c030703521107078120700046000203000d0f4041d4409842841000704040220480203c225003954031004001d00203181c81c2000d8400300202d82c00300c1d9405210f01e41004115020000191815071000c80858040011802c604035664000071550b40140301810b1050950074404c40c060420422030041450014540202c5808a8a08011100d03041d0790000c420f44c0d64007a080000751184405031801c0c0125600103024202d070341c01c125812201c215280314403809a8040c89244505610807401c8501664090111030f181c00b00c2407000c03141d511030700c140380000320800442c11000381c15a101842c00c00d610342460701c400f5840d41904801110294980305980302c0310f0324010f98903810080216440341c4214010440d5410a450320110b00140480790340c0f001c655413410307244002004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 644673066 1250 644671816 644671861
    0x20903012a0e220b1912171303031101060312050c0114060609130618060602060703110d09020402070b0405010e07080a020618270106120b010c02010807030e03030915 73
    0x4007503d1850403441135001590300c90008000241900b480180e65021811076005294504400a400c60400050320103114142c41c08602da281044003411182101c000350b0b03c00681400f4890035410709404081d88100080c40d8003400072061401706820003402078010042e158071a40ca8001100d0b40048a020401d1045000404240c0f81003591018044d404901d4000711810381e8a80070081928801c00740000c44240541800140c424a03040d0024540300005d00100181440d10000c1d95040000c5400c40f550a9400100440c9015443c800702d4002e2294000181015407400240420464103410145000d030804040341c1441e52034071b038200d8551030340c894001d41c001340c10440802565902ca90b42818813000804803070400da5813007000011000c01c03202c00d0010101c0343c0c005001c03633038110031841c01c1d61404c1602007007000d03240c000192900b5160503000e41400444400101c515220750441d142c0000c0200a0313035100e0030402e441d5030359100c0c80d820a5600000400014003080120703a800c0821980307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 644674316 1250 644673066 644673109
    0xe0420030c0112150909060c140a140f031f0b040605090f0a0b03070509010212030c120a0b0d080711010512071b020907020607020606011e03020903012a0e 68
    0x10054481c00c40c0f0114400106484601c1c0001003400c0381449001844030380000300f03400c40c0d0362910804503001104010309004c16094000500000f000a549c814001400c000c0d00300d0414022004840c042e0342c0701c42100000020800c101c0c2da0010000ca454030103904441d02095440c0e060751955030046014800007d03000340403000301c1e41780c44000150140d03406080c115000d601c0711040c0f05035a01c02ca5161000c01c100151028103544d04000156840010b00c0e245821810100b010141c28440c905480c1411406480801c14500d031650050001d0340008140d400010040e1901c00311a4111100035100c81300d61003a00d03d080d50003901240c80499954a00c0c00080d41c9820085e100c03a0380c510081845c0000c6416650010b8807158946030040000707400500b400c0c501080c000b41b800300000c04d0141081401020000c1840d40c0d5624140e50703240d28240581c45400100c003103070041c100300c0700d07031280c451008204582c803000030161810211020b0762034844c0c29066a088c4480650650b1030000250b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 644675566 1250 644674316 644674333
    0x20714030a06151d09070501020706080c03041b260c0d1407120803180d120903051324050f030a1817031906050907050a1205010e042003 60
    0x81d1141d1082c4280c204004890341e105072643e42d044d400c000c0200519200034010740511051080130030550707000700801d00c001c0090790f0404000810707a1901825103882008040003090401402e1196814030441c0c41815542440d81c1d80002001e0b5441c83c20103c00c400910382484900c004040b50f41160403002070403c05551400340d9030811115800b4001c5034031401050004981c3c0d00c42455038100c42d50203042c555499017002207012a03030001451448610340c0c00030181e0766182d074000703023040c0120202160000b44101c0e07a0405803614816180416407501d020302c4080307111100d5030a072074182c180540c600709040410240546540c81b030629042d4008905100064200d0155003040740c5001001001c2c4174080c0c1241e030350203c134101c10181109994008010054070284400100300c80c603007155420300c031052800011510304000505203504100002600c240d2a0380281c0103d8001310340c1d20410852036940e136a022a4440e000d403400c48e0f0681581e01c690780041d04071814549100700007009400902c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 644676816 1250 644675566 644675573
    0x10206010b0a0503092104050a050105090a092310030b0603030a02030d1107020607060f270609060b03160f0f0b220506070501090209010e0903300412020714030a 71
    0x3500010440f007410f11031030210111030301b01e50390b42015100c0c410b6002a126410481000304000ca290040c90400c50305100348600365440910035001c554414100041c2000ca0b40e05607841140303030218400ca000c0d8030b0800e20040601d40c003a10001c4902030300740020241c40300000c0503101e204004034400161300038054a00000441c0c0d1024148a241001592600d4202d40c080f580b107030800601950290b944108407440408da9000d200c0905800b0300b960100d90001059240708988548009010709607602000342c208401580501c103680c2e001400c03940c80b0705011131514128803403030040e000003554804001800c0c00c14491a07600340c0f01290782c000c1c1006207007044a000100c400580d011800016280084d654035070200074018540180004a14084640140801303404181e1005d4a035195100402c0f0f0030000c0801651034607e01c1024441291103000e8003c01c82d01d000c100280000c000d4541888204410751b00110020b0304560252101c1640c0c0300b0001c030221101c40359054241e0080085074001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 644678066 1250 644676816 644676827
    0x12090703080d0c26090c03010506330c0a11060306010e1e060a0203040519050108010506030a0618021b06010e01050607140d03050106020f060702030d0504050a020d150b010206010b0a 80
    0x1071030340710f1620400c0490b8100b03015080e0201c10380804c10781201c450602046800034888a03150003c260000d01060919a0200b02c4400300c8500107145c6c3c102079440c0c0c42c0740711000ca9040c5003080024035070070b4903504c64602c400c0e100c04100c80c0890781c08c02510411095818401c003508c0c0700c1c08058440e003e4100c201c00c00d00103c01003490894008008241c001c141d00e0740c95102404107480c4c41d03070055407100e05002c00e02034040b00b0421a034000455491040140d1307130344030301c800e41507a0050726100d4407512404c0341000603101030b4005000000862000d0450684142d019086030b1403010342d000001c0d2508603140b6183e10f400e0040c0343c224a259801406503043c07420043c9000361181919898040d070710400c56041213156800b0384002034498004000c040e5040200440c000d60001c0580041e0601000103556071040345000c2c2c54658841c40010f05100060018910a50f00030b004540d2040c01403801609071003201c0c0c0c41081451901412031583d5100041550585c0c0400031801d140c42c24000301943d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 644679316 1250 644678066 644678081
    0xd020d02150415020304050f010c05090f06131412010e0303100b0c0604060c0e0a03060605180c03060108060103061211010915020304120c0317030123010e040f180812090703080d 78
    0x81d1f51040c2d222400e0b06905c24804c41d540049141c0e22151502c010004002507191641140d92099070140700c070135021000481320070704868054032155040040440401c1c5038482c0c00044030181e500c0e102000840d010b01000039480390f40a880c2010700705440c0e080401450103102501e0b40a688030000080000703180c0d46c0078444d030036040c1c2010100e028105001420140342030304229052910380d4001c0041d4140002a043c03e051072103510b88462400740c40c40307030310703804020030042c1000010b00114299034080c2d48050302510718181c240d004100641000340b02c03001200c00040c001904a000080c7c4440d4100044080404c00d602451409180642c0d00515900f1150141d48800d5070001c00800149000ba1034148038000c261280d80329850702e40700c046901601e008100c0740030040d5410174032903030380204c2441028204403000a41e001d50354140c4001082c0c000305075120172840c60444400c0c460143e015080082064019003416540c0e10300440d155402c0c1d01c00140300400610103402c0303c40291708a02c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 644680566 1250 644679316 644679323
    0x615031505041d1b030d14070c1e1401050f210126070e06011b05010f0213090b0f120a05030a0c051c1407080c0d020d02150415020304 59
    0x30000e075151400107084558041d074607580c0b6600180ba005030a001885514142080110614110100007011a0302d441034007480008100f01341c0da0b88444441003406a0340a1500145c01c844d5098403500440310202c0070112003824607012010004220003035241840761060103940c1c485c144803046050709007940180d52000301081d000c4c3c907840800030390080528003e040d0803c12840c030480c2809000300304802c1705451751141d00540d0f41440781100596040da000942880c0c114a40305c03441008441d400c141e60310041041d401c2801035111440d0750b030050203a42c558201d80d446003650750350178034040301d403a680c1e29034001503208150203840c50300c0c0d0b55100c044601e0100b580d000c44502d1b40c809007550f116094220100d528104480f00b800720030045005031040240c00e880b605d1880c5080600218414400341d02c0005001440e1010080301009850034864043d00f100d124034140d180103501c0c0c84141d40d01c100144921500c4900310000c4802c0c1a0185030802c46142c0500b814400000c00707940028002c2c1e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 644681816 1250 644680566 644680601
    0x5061e0114130504090507150309050309130207150b120a0506010519030b01080a06061d0a0e0304030516092003041e0803180f0d1403040c0b031810061503 68
    0x40f141c0f0b440c098001810322500180040c1c0d0309107a142c48000301c5255004080600e0417013440d00291000045407149441100d007030340721850101c1640040d02c10494010402d00440005103006046c1e50400c0e54800380450f610420745420003400740d83c80940c11001b40240c0e0009004020608003c84091040d210b503c220440891701c0c1d4903000c3d15018203900208a42c1e101000007008c0c0102480740303c0180c40140c1944007031880708001d013828201c1c041c00200000ba0f407140d42c8034105904004130b60055511a0560f11080d003018180c5c000910148200c0e1016410254041c160041007c24200c03c0c4400110890542d2101c2c3c8408039034ac8103000152000b42461481c130801314000401071807149808425054018085a03010b038244030b0290f13030413100d40d480003101154240d00201c1e001e28410f1100125a1a6555414401d891455030f80c0000002e9000101b80174190f070818480004101403103084511500540300e1480c100c2d001e030b03c9042201401402d0700106284a904000c1040c0cac0d07a180c0d138 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 644683066 1250 644681816 644681819
    0x29061c0911030610050901090c0c030e19090b0405090a0302071202040212090105041709031e120f0307180b040b03040c17100612080f13031505061e011413 68
    0xc28070f054415644542031800050041100f40341540400b8090003145000f030052401a00c00a460600c4821004050241101680700c96460348003500d030901005500c01d038207103543c80c001000100000002140135609040000d001e0000005080103215855402810100c0c607000800c0310044203203808990140c0c00b044096101071842012501070414000000380c031742041c3c9015102c0051000c002101e0003400d000700041c88e540840c00380041c3d00000200303201001203600090421804c0001031001100208641410000c4200035600c0b031030a90311503a050498007069082d807440c2d544600050702508000030700510f56070b00091900700c0c1c0b1414200345613940b10b124081242500314038054103030b440300c810603c1d03580d624010300004200e04420400f00841c55151084540310321281d068561000144510218000e421050001c0d83c1020424a070002151904e40246c2401e694040c402c8041d012101210341032907092040c0d4803c140c441d410200c41f01c031103242080e00003030420316148960110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 644684316 1250 644683066 644683069
    0xb09061c0b0a0207060f06060f080106020606130605100903020a080705060f09240a0f0305011503092904120206190b0a12060e010e0703051b060d29061c0911 69
    0x404d51036480130003006c6150750900320009c0c011403a01d124102017007514401001819000709143c0e0300030005076030000009038004400c00281c1110b0380220703002003040384140030003036102c0170140c1034a2007200c0c2d29903010343c1e8144403a030300e54a0f40241c65001c90200703c0b06441c0f4000c1001400c0e0000050002c50102c00140c01010080c0c0c200c00074140f1100b000141d13080307800e0703101c81c80e09003c0ea81403e080099505211091007420b00000d0003800785039481403861f00303208082c500505900c2c44840c1200c444800c2c419032402e0000c1c1514121185440134103900c9602d8004515a40309680c0949811050000f2507a01d0b4064a489046582c0001031518003054200805004ca54598001c2002064042d4021103c1e401c49402c503074580075a403c0400c0610000f08041103101d15010205100200c0d4100710f000900203103d0300640314041e0b890040b215070b80d5041d500c1c803003004903143c440c012503201c0c180c0203000031841442d03040805c1503040400c3e5000290301768041c808080c0241c0070403034032200380070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 644685566 1250 644684316 644684321
    0xf04061d040905070302010e0406080601050d0503070b0106050c1002090303030411150f1b0f0607050d1407021b0109060e061606050f010f0614070308280b09061c0b0a020706 76
    0x420f40305034101e41d00070320640d42c10149141c04d480003518200300544c40c19890326100d542c1030045a2013408801c90343d50605c0010010b40340c40c1500b001000400e542c0d20440a851a48148a1760300b043c021050840002202c510030386e444002c0141c051071843ea520b030344030900c002c2c20619160780440014524445080300c0800f500d81520340d05901980d030101c0c07003a85840702c5028000c0d024560b12110207074401c403801003405604003009050182d15001104103060140042408031000c8490302d170f0030404016400110712006850b141818829000c0341d800440b01c91446000f02d8000c41c00c0307651155a9400c000d002000528481c1094510076441170303984200b9a10103642c000842d84100d001840b00c4000c400741c00d00100a2400e02085000c0c2d240a141200d009698019080c080f50388002491418940d0140035060200091001d5007088010b105c0000c2003411f1a59010b482e00e0b10005803117007841c0c0586080144020803070840415250313030f072440e40c05004241061464007807002d10005025030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 644686816 1250 644685566 644685581
    0x40e10020a03020a0e040510060f03061508240a1e05031501180e0c040209040b030a121107050a03060915020408030702090603031201063b01020c01050f04061d04 71
    0x50b500507a540c4504400208039000e10100284a145018280900d642001000204680560038941540c1c0d0f0006010f43c003c14091340f26a0411144082a20703402e544001440c2c0304100303100d18021401022403c03044544000550707076404c40c00b82ca00a000c0d02c14109018913a0b10340640507000020380710380102e420103030080e1111007500d44100040c080c1c032490324950307980c2441b000001c0003401d0898540d0390741c07044000607450003540c3c0020321800070303143c58220302455500a41280c08085951500010700e0303c07054016000605092645100810f0125604080301c03001007048145070f045455940040401c40b02c100c40c20f540018040a00e501940086d01c000d010440103181c461105005118400c04010407251090300204904150051891b43d080e054411038509408603903000e815450440d1801481c09281055607030b00040c0201d2040b03a101e0398403000782c0c01d4880754500d00006403110301802c00350f0016504180400d003c0c0b184524001c9070744001c450603000400d40764502080856544 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 644688066 1250 644686816 644686837
    0x5220e07020705100e0f131815060f0b1b06010b0403020102010b0904150b01020f2508073002100c17030c0a0c0f060213060e04050114040e1002 63
    0x88040204181d010b20054005240c16500075080c1d0300303007007001415080c064803083d201d81718840340465142c44e5100d5441e612640b00c0e10400c880c1c00d0070000190381100b00c0c002100c462610011030011000d090091800300c0300c14014030b00041d030414107414455003104100e43c03507a0904a55a0300d00c980200000c50083c442a40016138036420741c0002400c1d038101c0e040060240f041c02c001e01001603070b01240c0840c00004030000103942401480101d0400040d04030341100c84c0308100e8016a0007000004190110740d00c802c00e03441440d62203c0c4603445000381d12408000d82000120301e04550f58415403500c1000104002c0c05a080c42a400105580c0b0101e50307190000d400803c3c000c00700580003002c080f00001b40034501d41180f52081203940244502c2002c441008684034401082209120280d2181ca45c410429500c40c080c400700c91000310300700d105001c000b0b42090b4441145052520505050320f5441c03480c2d80012100341d0610001c2c1110f05070000e45403243ca444131445140c01c2c130203014440903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 644689316 1250 644688066 644688089
    0x80c03221a1315020a0b07050d051005090f090a150606022109060d060e040f0c0e0610080702100501090e010c0905030d030c050403050616171003030522 67
    0x2084440c2000c08090660180070160810125688190501041085034541c0c10a481c2010950500b2402c010040a0003000280c415081c010255046030140184415a5004006035900c103e8400005072140c0b081d40d80140c4900c0224160084201c5038a9001120200f11120f4083e996550b002155a45030f80c1404183d403110b0902c81c40e5414002c0154445c0b4400c52508140300c114080f284c0d40c81042c110601c00c120008003a0810807440d0007180080000e80c003201070750714003030502107041c60780420100d855007207103800800c02e1041c01c401300780a0030014040d1114208085010b03647d00c0c01c0903184105502c503c901d0040640d0060080c0e0b03010b0300980d100803500c10100340c2c00d5070a403070403007980303c0600c1706800080c081ba07100007078001c42c0308440b071030085107112500106075458440d07078001400310300910007080118071201d032211b0507058103550703100da40000c0400705c0da003484070079074808501d205081c1d001c1001c00d100e10060b062081c65011441e42c0c14600002001307100b001c0341d01c5100d05a1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 644690566 1250 644689316 644689319
    0x150f0d0503030403200c0901090f06080303040f0b070504061b020a080d021605060717031503030f04030b0609010308070b0414030a031506080f0f090c09241c080c0322 73
    0x1201800c5e1100e0603031000c0241928050900000c000d002c050103115405599884150038070400c2d134200800500311141034070f40d02d0510f4100200190702c52501a0b51140c0078002054505116100f01c40481e074565aa444c005440b28511a1103a070026800782c3e81f250320b0f000045848501030015040d071075140e4004080da0052050400d48008003a441a4450a0b06111070800308107401c0f02e01c44d011510481c440d070760313a0700c40b070204c035581d0b048003070341c90b0107200110746800001c10200013042941c2c003030718202c90f003565081d00300107004100340801002e01605020100000e40c25030740c41c0750418840d4030ba8080341926070070000e00e960806802d00700065120460040840d0341c1c8000c40000c1c211620700703800070303241c8030400c51040c800c0617004856811065002411201d400c0c0110101070800501145c281d0800040c25000540b01d100d280d44984400181c2e040c242c9401ba00f0815180c100c694122552811f688074000c01c2d4000c82d40c2041c503400100010350410003ca0100d08100d50703980700714040d0381d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 644691816 1250 644690566 644690597
    0x703030603080319360609050a0f03020106090b0109090b04110f091806030606090709051009091b120c0504090501031217011202210709051e150f0d0503030403 70
    0x214032070300741c140003c01200085110504100211600c5c441400c14171944000d4601c0c2040083c600c42c08050700c54010340c0c035800700304081802c080440c6401f99000340003641e00c42c0500c1048524124001d8040744644804008411058001e4149000006c00014810591040c0e4841c00d900044c640010031344001958401498094a2081110b02c10300240343c3c20300d00200820b64988001d024144502d1401d00024100d620441d13280004e0100039040d95001c5080b000040d22003199409601c82c282c0c00c080d0356031110322143d021440350754000d5441d0f060420585036000010582c0095007810400200804150303260180125030003180b10301a8a54502041c010003041101d1241102c8413041412004210201200016207211901142c1d0540d021904d11042c0c0030b20700500c05684403d001c3c01da4006452507217070b401140f0401603018800088160480c5141a14008482d135100312000701040f51890300f4000c0d4501040d0501409170703090000c0a440329480c5820480d81100000c456000412a1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 644693066 1250 644691816 644691821
    0x804051501060302091206010b1629011a2809050301140a0c0503090304090f0b0d050105161418030a05070b031f0e15030712030230030a020703030603080319 69
    0x6c8181c08000d890554107005a0050912541c0c100361111418061500c06001c0e03001103812801c150f0381d0b4000ca00c14400c0300885582d613424402c0103170941d1808400030f5801da031042100c10038030940d42d0b00d2031019031040301c24a1040402084200300301d400380c0040780070b84007440344043c11040c420301d580840c40c002c1c100300c080d5a622002502088803d1003070010086000050790143d401098011843c40d0300d06001ca001807180b81d800c02d43c001c50b850b4808040c030106511442c0984003041070800c60b51003050f030549642501e4440c0d40710141c01002084d000e91503003a242041c20704001c0a9a0303c17092070362200c900e170545580040b21403010000510080640c550b20707600d03100000702c1c0c1c00c00e10280341420b84250541300038400c0c0120701c801c000c212210380d800d10130321026155142101c1515012400c0096840b070342404070021140c01c00038003d4a0069041450002c042d100b0b217020320f96500c01400c80c0103500401412424191181c0003c000240818081c0d0703c20143c3c2c500038031801d100d40542c2400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 644694316 1250 644693066 644693089
    0x13030c1401090905060f040f0b0a050f1c0809060c031201060201150b03180601080a140118020d0311070e060f01090501050a031d060403030905070e16080405150106030209 75
    0x103030014018994105a604103030300d98122009030350001445d59034034001c03a0b00200c8450301c0507445498801c40322010f14a80e404210201c4040d0340c101d113995150414050040b1480501c50b620201c1c1c11180c0f651884441018510b0f90300c14140c0038103080b030010204d0380d9a04070301c12480712904003044949012014005150041a462000380514031500e9040d02070040170b40140382a6000010001340e40c0315544101e5803001c0c3d008002c0340c0300d5603500c200749e80d01e8114034141140c1000003007075030314407030401400388015607840386803d030108220640c20841200b5003040e046007400114400448036401c203100490040c201d1608040c0c241c907008042100300618203100c1c2c2e06100e05120f0038031140e40d01038250741c800e0100b4140069200a00341394420580d141c030000d48803900c140400c020030035034186c0000780418491011030f91940d0f201c03400d00f079002200b250010311801ca04035500901500c00c000490b001030090b030030356004c040c200c800009810000d80214012a40008090415041903043c41c0c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 644695566 1250 644694316 644694329
    0xe060412050a08040b07050910050316081e04050a0503040618120c14060c1c0e0604060e010c03050d1d06090c0d1514151e0907031d0313030c 62
    0x42c40e1a180d00340c003400300300010b000135103403c1004c0d0004080b40c1c02102160b100d140000c00c890250b507241323540103016a00031540c6840c10040319046900301c50199491500a01c0c070300c418140e80080242c421241c804c4001d00664407440b408007080f0100d0400e200a0014103000c0c0d6502404007007020381000c0c41c810301e51103100003000040705c1d000484c8007403041400361a191440c0d82c011604100000d40c2500a4200405150103224035000919080110002d9133584684071180c15200000411180380654400e110218076600c004044640c414641e20390854840d0824504000280c80458100c44401c0140c0841d001e200358000c00e842d1040225541c090200401028455200390108850409040b8000c1c82d0f550002c01340500b044083d0883c0201801100c034250003498001c00942c58a208004164011034810081c10710001c0c0600013196a60740c06000ac800a4880c040101d004140200e945080541d0015078104000070600c000d20203102c00c01c065019003415803d00303c2d510540ca0344004c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 644696816 1250 644695566 644695577
    0x315030602090a320310060e10150c111c06050405060a020a0e190e10060e0102030405060a05030405010605130c0210140601050a020f03130e060a0e0c07030207090e060412 75
    0x100c40c0c0300500d04005003011301d0034040c514160300408030303240c80c9000b00c0c000225424100040748002d100e1084610880d41b00480800240d503c1c041c0180c0311546003120310000300e0100900c804907141c660b10140d440700240203107402c10046c8061002c54074801008694590f25101440306004c0204030303003500410300c05411494074010349030150840c5086544613002e03459503680001c03503605d030501070070041207882081c92862510b9880c048075106035010b1100820307480091451554400000d603420741d18003804080c9010403608040c0c039103400082c82203c0c95921083c3c017003800c0d1282e506180a1400d0880c0c0490070058004006e070410403001d40544006117843c03003d40c81225034540041d0400800c0c01c04507690803003020200c0c200000b540d200c903e6480005080c41d4055606101d1000702c03081c14411240c0c940b03500c03082005d407005512407212020b1901010485820501c0000e102c05441781c012200c005030707103440301000d1f1480342d4040c2040741c102c17034104418011181003030007007640c8900e0300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 644698066 1250 644696816 644696849
    0xa1206050609040b0120010e060705030702061b0d0911040e0c03060402040b1804030c02040c03050621030c060f10050d150203130b1312030603051207030315030602090a 74
    0x1c9010340c0240d069440c0b16584446045886034083c1c0707119500c0d510f5a401c215840341e51448581c1c0a400008601c140d540300c0c183c00500b00741c1c424002c0c0ca00851843d806000f80351502c0210044011401d0140403504070f007081410f403180341c940b0460300c040b48242c20307614010300300b1b03401c0004031048140340c20b00715040302d0450203540c0d5000c0b80c0c0070b6003c1d44c1102d0000d0780900ea4000f040b8010428135220380052904000d020a25400400d06c1c21502d208031404c1c01940f0080004400f500c0d81907800b141c11140b55140070148a060410b47c150760fa0305902203070301304000380540ea842d001040c2d40001d071080d800d20500454061a0801002038130040d550054100f1956584000a00b40b0103081c000305580400426030310076040251508160300405001111b0030600000f00004100480443c1e0842e522070700c00b041d00d801b900414040341c0d08000904444401060002c00a40c412031045041650b5001038104001035140e180c40a58044c000040c3c9400c081c00511000c00d50b41e401100e280e000c582107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 644699316 1250 644698066 644698069
    0xf0105060a120f06020a2102040e0711151b0406050405031204080d05090a09020705010209030c0103050c0913020c030310060f080127092109120b0c0c0a020a09020a120605 75
    0x1120b10b5540000d00581e074010400080b510f0020f51f0a005030b4030001c1042c0d42d04650580c2d0054000d4400c02071508035152284002601c1300640010101015001217180300c280401000e5125070050b0300446101c554841d40111805070391180e001500030500100c0c0038450341c01c007000400016101e81040c1c2c1d1401d401c00401583c2d5082d5820080108900000c02155680b44e110502c2c0c0140514141036480724558900340d40030f0b401c83c0c103404d4041c2c480c0c0c0001070099807107405180c1c080d415001d0401d01e071085e4071040c003501c060640d10068209800300b050b0f000c004030400c0150300c03682254820540403818904010309000344401d410303007009020001404002d081c88081050700c00da240c004403030041c083c1d000101512400c42d014082441100507900d0b108003111500d0940d8886940d88030b18640c4805d0b50007000c240e0b07180e014111552000c00200000340300f5000300a040404401c40709000c0c0f4980c001254400c3c0384c0c111203072464000c07640304401034010b400392034001c15200b01400458103000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 644700566 1250 644699316 644699333
    0xf0503160510051908070e181303020c030a05060103050f0601060807050c0a0c0603020c0f01020c03030a180b04030306091d0a11240901020c030d02060402090709080f0105060a12 78
    0x11184240340402ca20210240594100e9081150020003a50780c030b4018640645600d4044503170b00080340081015003a02e28020141c40c2c80612503600c42210f40c1c4a85128800e5052042c00480a500c519008410b50350750801c40003903214400c000a154660451134503600b819580a4440500d510240062092541204103070398800b101d458042d0319001030100e1280350101020029003400c1c882d050108000c3d50680080005002071022108409182c018860803840b80d0b04000050303402c240082008514503800c0030383d58801441c07000039965110345a0740c0c1860000c0d00d0880109950b18020001c0308078600030015110500301c51111502c152094481c0c58924000000b4082e00889042d41904c0c3c4d102c158018251740398040344010741c0b50303d0501140310381c400c500389400752088545503941494001044100040d45502812094840307909120b00c02d07401421400078490450404200d08808000880c1034111020000c40c16003020740910003085890340200c090500422140f101003039101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 644701816 1250 644700566 644700569
    0x15030d08060607020625060b01090e04060f020c0706120605010804050c0d1410150504021e0904060302040e0a0b100b070305030a02040506130812280309060f060f050316 74
    0x1601e942d5075504207440040d095108030350700101400e2005142448800d2900b10302c081603441440100b10250381c020041d11060b20034400c02c0c0c15024000002800a0300c41c1d0030070014000e80003005418081c3d082840b038204511608240700244100d40004185134103405640c0082100b0b080c011420705150319641d46030900d06800358000c46401c02e8090800101a0300d84524518000070f07500240b05407400c441c0544500150040c00310701c54400401ca03403405200700c83c940121800098240c4a0405140700c20390002c04880d984140e0f104000400342e00e850080f00d001d504284040e01ca001d0352894004240c80010b00200360941c0502018800801c440701101c020302c0d01030801c0303a01d90743c40030156006071046421550700240040390742031100c0d84003100401038900c80402d840034010207120300080c80c0240d14184036629140c0c04078905441e103031f00420340307546098038000c91400c138151206410f54680c0c03005090b26a6540740c0030000f00302504001d00c09810105c0c060310561400e9068400304590380d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 644703066 1250 644701816 644701819
    0x51e0c0702090c09280503060a0b0a050111010b0301060303081e0c030613090c0e0108070b09150c1504050f01110702241306050a031112010e15030307050615030d0806 73
    0x4507015a41d80d030111550103084184002c05201c05e120421110b61091072040d14020b1143c4004601c01035030038010340c031007007001030026191940303098011030b01d281007801405455580c4200100068800303014403000345010b0f4841c0e000740d0412900700f06088071114014082c00c0041810312040c003020340708a9810120071589654181c501e6100c0a0083c02c441d0401070110020000c00210040889035041c1210041c2040d600256a02d20462005100341848283c0c07001130318502e6090300940381e01030480d0301c10300e40c2152242d40d5092a094064141900c064035650320041c52660040300c24003942c010451049481401c2852550205601c0d400800041c004920b00907000902400700c0d0041d00d100001c2007103008030107591400094480c0e402542c402001909080348014035000240c1183c0b4080410300948507030f0381c0380c82c0034054020310284c05414810108104518a5601040900005801080900000e01b0400d00d007081101213000c0e1240030703401600c0400501c64000d40800d601100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 644704316 1250 644703066 644703091
    0x101110050604020c01060e1e07170a02040902030403090f051c020d060e030a05041a031612110703090503100e10090201020c040f14070810170a06051e0c070209 70
    0x25640700050281c010004450455841d203600002c0035035070392021602400045400e41c4891842c0c01c3c902c1f07040c00702180c2040214041c48802c0f003114a80844040c4d00c1101280c0050500d40c440c40c41100b603038003e990a8000072a4800e0501c00030b80310803a28402414100c404078456440400243c01c22030701c03480043c0c0b194581d4042d0a042c003000d500800c001d9240b9005803039a03040c941070080c02e150054040c0c0905201d0001d1508404024401142d01900300c0c0032200184d00340309070080315052001215940882d884400044401040d0000b4002c40c0f40329454203c3d0a138104014949030500d0080001d05450400b2007074034840d000420fa91274a4140c0c0707000802c1c3c41e031641c00144e19201c00712241c80c3d0024500030340214085010307031040040e5041c15503410f10b903887e80c400444980c1c00603600181700c1080352070b0420926020f0405107401050480c140c0c1c0d0810902d80302d000072500102c4c1d02c2c102031040440d000d1040c8901d401c9036030740712548040c814103084aa4020540c00c0c070000703050864410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 644705566 1250 644704316 644704321
    0x5030705040e15041b090204060c020402070c0810021e090a0510020102210f070f02030a0320070809130e0d05070204020702090a061d0915070c05070e040210111005 72
    0x501030003410110803112810150504280c07900351081a140180c1017003143c1100008101300310140229801c640b810b07030f00d84a42d9002e58007080004e41c00074004071445880410f0020390343d1418881040c00300b0301e500005844401c429003a04200e40340c0003152444420800c800c05482da24076000c4010380b601a210a000702c03003d031b20180d0080c402ca04940748a20341d8010601e490a003e11001032084240c201941019107403010700355103034840b0484840c0903820902004601c07900c40c1d4040d419071400d10681031005124106104042d0b030181c0c0c025100700c800000d055805040100c4603000410900398104018420018034a80303179400800307040b0400130000f904000f03555503a01954241600285507600c0b0f81401c41e441d50040080748284400003042045040980082c1c81d0000d124480d0750014001d60041604824032210005081d030007030000b640c46c15008940b041111001600c186903c402d81414140104103415040e0411141001900040c060001c80082016070501c0703265030000c225078 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 644706816 1250 644705566 644705591
    0x7031a060703111015150e0f040203060d14061608070c030311070501020c0c03122503053f010308120703060b07081e0f03041b051507050f070503070504 67
    0x184000c0315160025091034407005c01100040380050407921200045141300c0e580311360a4500548a4600951045002c1100300f480e042c00d80003036034011801812041c2e10080d5946490218100b00042c207000c1d8009010000b10080103040354203014160304003140c00d49030480005150b1031000ba40101003645501e6150348114003102607540d0203911800940d21b90b82400f0000741c0d03451300712000c24442c2c402e01d100040600400d0007120b4024040320101c40c4003e511861201540b2804402141042410480c3c240d45c02c124079200702074008012600311800d1845001c030004c182c0c031104032841000500303004100090341a002c540b058500f80d0021f40c00fa907158401035000700400e9000d03010104001551004000b0311400820300b42c440010458810200400c04500c41c2c09040d0041014030b00400114000c118140707018803602c150078111400842e21080822070100741002c1c4007198080226414041020a114091541c0e00c40001000382615050011f0380d2a81d442c0b04140c000c03580c620319403028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 644708066 1250 644706816 644706823
    0x70501060b0a12060b130501050c24040606051504050904020a080105070f080c070321150f08010f0903081b0712050c24011a2107031a06070311 63
    0x1440000d41d281c2c1c81e60041140540b280780100701c00c01003d450054040748908101c001d4404140201c0e80b94180f680c100401562aa4000d980710b009a12640b101c259051600c100c80e2140d00002000d07291203414146080c1d001d98100390000d611985200c0071429440e841d20084e14200c6d0021144000d698480740045481184942c104103419402c0c0f00c01c1020301038020b21140490001c40e13641c00e010f076440c402518a58050320320010005200c000780141c2c0485000c66013a5a1100300750001400f13049020007003449040742d0301c4511442e18945080100d00d0082c0700b003040143c0248801e000344a4181c1d00100400c00c01071802001d000501e140c0c2e0307900f01a800656101a40c0205094035036036070040003800310380142c0d0184a141c445c07080301e020840d050b600c220210b0950348132001403507400c0030301c9100364070321400c149035140000b4404106c01e0083c18a4800902070032080c41b0b0890b0500f0403005060b202080c0300c0b400c0c070b603007402c58140d4140c0b20300e012114451780500d426040b405042c01c0c01ca05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 644709316 1250 644708066 644708069
    0xb070b0f042612070f0e060f0d021b01021908010e0424140a0902090c040f050f0612280c020c040c050c1501050310110307030e280506090303090303040807050106 71
    0x1003d1003440100440e90790031140c005030742040e6445000b9006080b40c00c000c0c0601c070307150400d0340500e01441001e54a0480360098203100f4200141c2d1000c0c4036142c00d8a50890300070321410300141c1303070880c201842650480c12081c0074181c400c50141e95407401c1d4035140340f140f403451a408615000389004005007035580d484035a8000740c3c081540c1d003504040f900380000c2c0150004c1079220744c42c9040401c1112a1200403141160118403840304881c0c07a0500f0061100020012190010070400000081412007c1480e00c00e00c00c0143d0900d040184181c3c0001100500d481c0709d2000c0c0c68200c01038031080d000074640240c80d1b0111800300e480707010800125894012400000178910130750301541c10100423a403525040c1c800a0781102c1c1070048103d170207010388090422004201a007000441c2c0043d10135013007000b0030440003040f240c0f59680a0801d201c11b4201c041c0d03c041059041da6030b80100407080c00043d0708241c0c13420082d42941130480c100790702d030701c00504010f21103040000c810080160a400850 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 644710566 1250 644709316 644709337
    0x20108041e060209040507020604050a24020408010c0206060406232b0302192102160602030403020a0902040303080105010503041403071202160303082403070b070b0f0426 75
    0x980c5a450701c2d05901941202c8183c51103035082c20005000c0302e2000480510681c0c00000134034512040d500c450640500101480342203901058100c60204800d0006000a2036400700016540c1d9032140020f05003000a4550f5214034200f100030460440758030503003010994809950350321030740755100199174203008031309640d00e04031500044001c079118000506401c034040d8080c0c40d010310071280306c0c0e44842c031222030003000703a03a440200c01d43e07268039445007484204141c0102c410000b101c6011503031802499100200584c0001800e1046040611002004010064055050034119540900392240c140a1a8100032010000400f40030006030500f10306101c2c441582d5803140c103418485100f05a1040c2c140c00740c400e40a00c503405c1c030a510540d104880c0c03d070355a0320080d103d1141c0e4000e000e90650360b007040381c1e521841d4504656002d00044004004d4105401e40c0d848107450810104071000b007102800d440c11800304000300d141c0e007181f159074408a1510300f030380082440403d062801842c1004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 644711816 1250 644710566 644710613
    0xb04061802090a29030c12040b16020105090303011a0706020703050406090b0c07050910080105010b04030203060717070e061207080402031006050f0d03030b120a060c0c03020a02010804 81
    0x81040d245550300800c619001981c01d403da00d51100d8012003010819210400c04646140311a1359120f410009190003945c920041c501d0401c40c80e4205100010a6a0944c0d00e117001c14103000c91903500c00070701c0010080c180028003140c6070103480b103510b90005101c2c20780d514031044500b5503410800822920960790102c811500c40003a401c0041c0150403034024100440c01c0d0303510100b44000b4407030540345030503120030003440c0c058285824450f20000c0900500702030308003028049581d2070b00380103d6010300000c3c5003043d100d80ca075004040c45c141c0d0182c203001c01c0c0032640c0301c00050f803440d10354820f52140550814100355540d11010506a110303c559100c4c282d0034050502104c664001d8107203010318021400c030b445006401086e80100c440c1445100c2d401040d60101403000c0c101241d052014501078200010074125090210782124101c2080d403003244c20002c2c885042009510400710f0341c21503890941c1018005a41c065601c40f034800c4080d062001200000c0c0c100701800701655203941c502a001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 644713066 1250 644711816 644711849
    0x10e030d0f020618030304060906060b040602061e01030302060c0c030d0203130203100506030d030b0a0305060127060b07031101060510050a0305060d0c0509070504212a090b0406 78
    0x14081c101e2070415100500402010031066504030010340a0349600c04c001d545180c031550f41d00300041c040c08000310b5105850b5400003846841000280005086c82e40140080d849d00d200c007005040c040c0b003008010070b030503100180007180c0d001900d076510000080b406507960840503951884c5000f050201524030f4000020007501da01d2409114002d0761007501220398440068401106480c0c0c1200c081d50968030000c8103080e018840e410020038500701130100071019032a41ca5450030200c0c01d8228021642d03070509059141400f2880d0315130341c01c4003044200704050070310591041c0c0d84034881e009030400000d201407040e08442075101c48020840100421894948200c01a00d0340d00840c45003001b1a10740000200340303082801001000503400500c081509013084200322030803a000e0221400c00c541880302003058440c80e0b0381d81240d041030000b84803200b44940340c0351644038120010100200800d07c2c01100300c2120501103c02e5600601c002705d400b03995000414014440d6601c00c0c052407589040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 644714316 1250 644713066 644713093
    0x4080711031c1806050d18060c020102120c03040f080306040f06061e0207080703081b01021810031a12250f0f15050708120405060105010f02010b09040b06010e03 71
    0xd04103020040b40c1c07036595440c840618000c2103052244512000300d0010030041103079288661180c0ea174120300c2d10b40e400744080c0079200c40301210001100c1c0005030798005444214203114143d03244d4000c41c440d04040c07840c9041c4d81c0e44505442840c00082c5008070101c00300340c5075500c0b50003101038003404280c10803495903102c000802ca451010751404e003551880000c1d60b042c1e1300c0401e50800b51103003600100f012074915650f04000c0c0e840000e00c4950070b2580f80c0c404402c11320a000414901903030712035007102a40c940d001c12411700c030305c40c2c3c8200a15260003290140c10700492200e90100b001168203480f030281c100141410a010780d048103201807904010303480964840d01c074800580d41d40c201c1c91010203443d1444c083c1032641502074a6951010128800d101a11810040070007a10440301c2d2030808901800247c1807000a035000c0303071540c00c90401409203590000300e48214088510003403000044000100342941030150000e8000e144d5440016400d90003840e291810b0003000d0700f20f455100d220311 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 644715566 1250 644714316 644714353
    0x31104080a1a0a020c1b03012913050115030e0f0a0b0405011a03032b020a030b12010209130b0a050603040507080106120b0a0b040f150905010b120408071103 69
    0x107480c080d409111a0100c2c903006004c1c07007030b0b40803c0c003890000c00140e41c50880007826002c00c0b4003003650540d21001c659000030050034041030902d01c480c1c000301801034250304001069140012805580f071400b00100600742200e40018400c680604000981c110030180d69801c101c01c100c0300e60030b284264021030701000310f0702e4545481103004000801252084580c1148240703d09080d20368150310500620540500c0e5071060042150800561003004010f085004180d03003002c840b0601103550f828980b91181000300c07980480d00d440000031032620b04218001209612803180340d04085030746161142540d00c1e000450405010000e222a480346814a444c0d651002c040c02550703034650921000251105081680d807140f1548140d40c1c841a43d40d1140d000c0040c01088052a0b0058a4646010120140307118a1881d2481c02d000f01c4080750520140e176058a106038080d0315424001c0103c109140003c00003150403da20001040d559021420154451086030700c0155040c051007440f01102d00f00c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 644716816 1250 644715566 644715593
    0x210a05090409320601030308010620190b09010b03030d110403021309021005031504050432010608060c0a0c0305040315050106030f0c2f2a1c03031104080a 68
    0x15804030f03030040c505581c00d640720b05003840020f0200b0f40400040c01401d0041000d41480110352a804201c01c84c003030352480c5840343d01c40d80352404001c0d801b80d140500429007499036110402400134000c1c03030241000300b0f650b44665040d00d8540ea036541c803082960605001124010342d0014000c400c0c4103600c0221030002c1c2210742d0124840c11a542c00001c245d401030050f00e02c01c3d0340c2601c0548a205100e01408081c0400a01c1100c400034824410814100d01c20748960b06500e032424100f0940400e0300e00b407400c44038580c10941036584007a080000c1c00003080204c529080407480e0001d2400554502510b45001365080100300d80040703003200c10303001143d40c01103040300c2c00c69406000c0e00b0300c0702030035900b1642d400031307840300041c44a00c0002140290080258035000d4800740e0000e0a9840d00e501401d084459031101450414081c2c056a9181e20356030410245004458034078540758020010403180142000003003c5c1500c3c1d11341d480c24002c07000c0503103000b0030303264099a0b00c84500f864041e2045010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 644718066 1250 644716816 644716883
    0x9050f0607091e0303030506040b03011803091703040515091c060b09011224110306090612100c03110c03070308071b0201120b10020708210a05090409 66
    0x145140094018251000c101c9100f540341c2d98000003a040d501c04802901d001010300d40c0250b1075821a90141e1001d10504580c00c20030301d072001a01e4010700d4014014020f036070100b034480c0b5803810341e680307070b15408021603040354030490780458580440d480c03440d818040c0e541c3d41540301034580c500c1c44c0c260221612203004280b080302c0030402842e81c0303820016101000e0144200000043c0d41c148001440d500c0000c0406112003914402800340c1e00500081c0c40807130f02050309010300070062105c2420490701c4680c1041d42110580b90309a134001070303580e64003482c00046034681d444410320f89a0f180a5403014084a8400d90015619114688103941d0b980c410b400850000f1040800200c0b09441035500c092200c0040580c0c10789814a500112010440828031503450340d611a00c0d8016a034071a5204032400c1841c2e00588801443c4c69041030400400ca090680d10507981c203002c0088549820803030328000d410741003841d103800c00b8201060042910520040040030380c0300204000d560070312503049200c1d11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 644719316 1250 644718066 644718077
    0xd0210050108030a08061306030b0c040509090a050d0f0c0b01060f110c0307060c05010b0909010606140901080105011d0a060806030d110304030b0417040f0306050c191209050f0607 79
    0x1d9450302e03155648155080c05000960000c0411a503141c0212240c014204015021994580f80d40b2949002d90058401148421000130100300c24140004080d40c8911a103000c1e2100500317544405031501541c024880c00c1004100546583d14000d402c0011281e4100d0b03034803040c5603103075031028040d64240c101c90350108402d106480003043c2c001400d901c6001014000c0c01b1114901502998209090f01c0122060f54030b07250104402d44500d00264803401c1000004210680762860152003001900070303c200485040020400998000042a046590a1030800000d20100141d01020315642010390ba201c40000d00000f120b0364010100390080d0002c0701600e90722000c540d170958841d020a035081c1d0050300140410804520703003411442e4841e000703010141c030800607410090183d44c001c0d00005140c1c44004c4051082c481e02d42300f07a80d4404940704a60389414132080043c00060300320b1610804002c0c00e441840001c0040350801015643e01a044035504045c00404a0303c5d180b080b0307440c00c001003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 644720566 1250 644719316 644719319
    0x130b010e07020a0305130803191407031407140a03030e010b010c0c0e0601140703030515090c09090a0b0301020a0c021c080d09031803080d0501050a1802070609050d02100501 76
    0x2019008118010070980d0020f0051044503a0250380302d401c995000086141e03a0b010014621106100905005460340504461001a0000980808402d80c82a1380e600d03818011800066040054100d0142c007507001392303868410a00e01481e0b40855070040c54190301849800c0383c20183c040d007045120001e9903009002c4000300e400110b4035640341110180c4403021004040102c5144104034035003000040c5080d0b80d080d40c195100302c00301ea105a00480020b95250208204c029100c1c940b02120141100c40604504040040c000c1900403061103070310441c00c100100703a01d501aa840400b4202000c0c00954a45403100409003c49000203010f81c041c01009200d600d03910b030303001c00b000300305944100298146448a24484001d0554540450030311121801c408000241c241c003440046110300744081d914036003200b841e8143c1c0d40607404280202c00164060001c2d206107400f03540101d452140050300d07510030b410508040c0c000d849000c0e01a00555508030704a5601059001f004905184148801c1c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 644721816 1250 644720566 644720579
    0x70902042601021e0c120c0a02091308160303061a0403031110060810050a0c200f12030a0c1107120c0302150408060709050d11010c060609050910140103020d1703130b01 74
    0x11f11540d440340390203401807210750b0014074101c03203100c0d00a5035006074002440610b40e551400c46d802186c4903003804494410303000405505000d0600546042e00405821510909404581780154040281804440180908a41c0e020005000400d804102c2806542d584a00181c0c80d02d441148440003075040c140051031440e0640150359160600356100d60f0a0b02840e500007a0035456600803000e14002e480740500b1005081041c002c0e407905440710342da903034281650980225610801d4070003d1001511031404500307800704c1d1f024200e50b0200d82008010b1001c1c82c7c2000c508185801c0254003200a0302e0329070b4010b10070406003003540d20202c115103039621405002d40780c04100f4440c46500680b42d01c1e4500c00150030005082c0e24920606103110000c20b030b82e5481017680c0441d0440c51310b5a5031802005001d000402031485007142101d400c20140c1c3c442d41d07000400000c1400068001c0041d5004901002123140049140d4014181580c8d228249100407500d4560a0751040d1101d034100400403a40c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 644723066 1250 644721816 644721853
    0x10110a0f03020304080d09020d05030a05130806060d140f0f0a0b1308090d02061b010902190f15020a050303040530160c0503071205070902042601021e0c 67
    0x44e81c0c0000d41e150900c8440b143c0d640c003030b1882c404200d80010014084030000380041000c1c2c100f050b0ba0351138154072003d20380b41c100701c45e2360142d200120703e0b032010b018000103440741070a43d940190001081010002502c1c400e9281041c41c0282000720700c1810100e070030361100803c0640744170b442010f90741e0058031200044110f489000744050006c001c100f05a00103441c1114041100ba8405003c981c00d1400250300c0c12860300c070400081030300765100c0b07903401c00314540070504154542d500030800500f182400c0500c10b08030320710300503010700f001c0410425070114000c1024101c0135601900300d99a034275041c94403589030f0301510f05401665083d91012240307114020b84611700200f10500c010703f000d1040c2a040c80c0e02d4800101528046480070021426880c14003010011b400c20001040b0107078031928005280c4070055100003025032050009201180286101550360300030f407981065a020760181c260300920540948450414104c02000d401d00440030191107040c0d00c5905840104550700c4200f0751 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 644724316 1250 644723066 644723071
    0x60904020315270a1a0c091c05030a1101150b030f1305010c0e090a0605011e050c01020a0f0e090603070506071403212d0910110a0f030203 61
    0x501d41c101000200c0c00c180c4502400d40e0040f0101104911035814182c00c01640400e00c80d14507858014000c650280005043c10504a80c081800992585800d140ca00381c107000f0034100b14424071010301c03039850140c3c000540c604110b4001e01642d40e070b04450139000d0032803c541c0d081d580f803650a140718080b2000c062108041210721006220746903949800071590000c800505c4445c92008420007140802c02c00d00c6116201040d58845443d8040e0f003204001c9209401014480c40500b000030510035a640004442480c3c2035100d901841c484a401043e2024001c184a000403580b0100304201d0760303a0302c040d2022030000d0301d40340c075130001800c4414091290782c115030580c1c240c0e02c5060200898204040105502406007980310010741600e4803050550380881180d48881142001e510340a2a00004041e0000c401d41901c600a441c248a01400307601415605401a0898000140e089001b480f5081b4a1505084100400038410281d0701250300024102170010711103180340142d83d4000d06c00c0701d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 644725566 1250 644724316 644724319
    0x3010302060a031d0706020309010311031003060908070b041209120c060f0905030715030e0d080703052205100f0c0212090f0d030305090c060702100806191d06090402 73
    0x74030304508614250042c001e009180c424910815064104d4140117004510250881d680616524482c0304001000d4078404860540b8000d001c1081c0051031815030065030880e03900c100d02103088050740c2840e40c140d000c0d42e5000740c4024120406c1108200200e1080d410000c0181c03110718038262210f09407400c0c170400c1a002405001c04240510889004000349850b1940d80d180251980d500d0b08082404c000300f0360b01c807050301314000d07520319030070b81c3c00d806003a02d10b401502c010141c00300d00750300003005a44060003080615640d500418504a0244038040700c803446114004110445441d10075502c5600c42441e4505601d0000c08400e0242c0c0381c01240032066040e402024030002c039101080d681d9008510490384041e00d203100c801035817540f07400741015038025180001d107454440325035070030283c034844800d1068404000d01d43c0180c0d0355031002002c1c1625407030b0480c016501d04000c0381025940340144030900f282d40d00c0000e400300a1030b44004500b031110303200c031013161140700034050340b5401035800a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 644726816 1250 644725566 644725579
    0x50a02030601020316020307080a06021206100c0f1704121506060906120617060403030b0102281a09030c100507050a080c09090a0605030c030a0c05040207060f0218030607020303010302 81
    0x2080700c81784a2414035401d4001410f40380d41c00e5650880c0c5243c12030300c0004840301ca40214280c6048480c101c1484d60200040e1901041d040003220300400c813414100000701140c500e00c01d02028402c1001c03c80701c1391904444019a100e40b5501603001070442070304121890085440504543c00c414001e95080340d07000e44410040750705082040d81c1c1c0c2052003180e03152156480b00000394a00b003034110b112500c0e80d00d1025204604243c10001e0a8420030401541558402c000f10080800e020007a801280c0c020030395540d48801c94039000292400d54100604000211014080541070100040c40d80d044004103c0f50b880140480c1c0d40180ca0003100c001020443c1840b40e010340ca03000d4070566034032803201805079290114060004522010a4400360307203280c1e40f5a0140b04070f040820000422007412001881c00d4195503440540c10340e800d00415010320340228295040103e150030901401c44408401c0d500c9900e84c1c8c3d0812070304400d5402c403d10030f108250108540d5030000c012281620f8015007072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 644728066 1250 644726816 644726827
    0x409050601320c01060f0620030a050304030309060e01150509010806041b1a0a08151f0e04230105091306090c1d071202090a1a040509090601030204050a020306010203 73
    0x707441c0d0024422100c5035035000c0c10400040c3da401e00b031050070060100803120013501c9060506c01000844c034100490300428400102114801001080e244021007910b4516540c0e952841d00310098940000001c0595040148030000e405041d08106141c00032159000401c55a4501300114088203101d2950550042404a008a041003034041c030700c20840d400c4038078170650782c10680c0d01698408040030058200414922241c644c0f042c3d4258025000344161130040780101c001400400b5a16140741e0000b80c14100748800c1409408144040c0c00010b000304010102074140c050076a051920010442c03a0310000840c1501e40780215034007034107c030110500e60031144e6844074014011128182d5440d143d40e00009401001242100d03401880c0c00c00107282814070748000360203011026400f04110f0300611208509460307904107207003180d4040460360301460031111a001e55119a40015400400040070495540000249035042b00e100396000c000c982c0d61201c6000482c00700342c502e40d00507001000b6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 644729316 1250 644728066 644728127
    0x50111030f0f180907030605041a100807030e070b0d0b090403020604030c0809100509090129071e1a070203070c05060c0f1006080c030d0f180b0d020409050601 70
    0x50300010300c0f4122a140001c44100000e00c0c0e8980841d003100c0001d03242c60040c015800c040c02100503603100c00c022001d5510310800017a48211000030807070200082800080c40d140d109803c07070b0513020f0309107068034041a140e8200e02c3c890f82c0051403400c00b140c1011829000c41c10140d070070a11694059000d0107071502d65507001c07500040c8205c4203990b280c07400d022030296035039401400480e0090355269166112110800e000c80010168402c14080700255407688011041181000c2c2482400245665400712468070082c21000c002c2240050844000b103034082160a084402c4554a005001e0340703103a4907060b00303d81d2442450783c02460700c2d18910b07080110b406c1820181c070311582150b09845130000c8000c40070303103000c144a0703100156503112032040022039014000d0b00c690749070540281c4013800700d5841c003600503c0003500d1103081156000304501100a00786451019019401503265110104140240070b03410502030003082031f103850085482d80d07019424459020074500c038141c0c050045100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 644730566 1250 644729316 644729347
    0x1f020a0c08150c0d0f061404140108210d110714010b030715030902130f0b011b02010c030c050f01020703081f0303051c05010b0c060c1c110c16050111030f 68
    0x1500319031342c00d071182044441c2d44014000c040c041d11004001c0490340c4420300c01c12080d104042540f600454070000107001050340455041400c540c0450500022001c24092484030701c552150400c4041c9000d080c0c281840c917880080c028540a041c03064400c143d42000642240e0045800c6545a88041d108011000c0e041c0254440b05020b03040c00507082400750003245100303242c4900100c43c079507501c05885400c2024411744188120a1030400641c3c154880e500400f0110094080c1c1800307032090003a401c141c81808517071a01d40c0d01009a81c809a13024454a001c1d400410044000ca600750001070001c1c0f011983d410001410009000c140a145440a5582d5030256000c141603c50b05075100231180f1300c90107820300820081e50760399a00e548148000e0b048c40405800014900b5003041284010070a208920f0040341410500003030191612101620728816030090032114001c1c0030001c510b4181108980080304c41c282c035561703e0000940c000340d48074880d40100400c81042440170102080884 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 644731816 1250 644730566 644730577
    0x527061c080a0c0618020303031b041a18150702040f0e07030c0515040521070317090109080f1203102115020304021302091f020a0c08150c 61
    0x10a0454500c109854004455000003540d90218440c4403101d070401c04548a05491503a0500c4410545000755000945912010b08000102c4038001000042d00b03000400f01c400400c030030306524a607071710000f4400d40607030086a03600b4010000c1030216480d41c2040326000c00c10864a035000da1030903a41e603003000000c0c4803851b80070748066900e4003120681c50041000308041d6003d00c150030700c0180791000b000500303c0110b075814031a0b1800e21040105443d0070b01c910b61030b450300c580000b503084510181a80750000c40d920203003030f0340b00000382c00b8009400e5000070200c2640a81e5203000161300e910526981d844005204125944200301e5400e8510412000e960041070000260554650310390b20010a5422110300b10341c4800200084810130100c21424120000064400e50031807400386c0010700704260403402140001d80000f440501640c40f24103d40484e4120300c5c3c1e0f29002e811a04000f9a140303210041140c80308800340e00450301550005545001070082e0f41100ea0507600c000b074114154014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 644733066 1250 644731816 644731849
    0x1150c0f052d3f040306050105030d03200a021207031e0f0c030f030b1801050f0d0b0601180b0a02030327060105040209010c14030301052706 62
    0x11101210001103090152031030100440303001d00341d4401440442951500300000340800c603800341c1d202c40016600900c21000900246a1900341c254000180390250864101c8070760303c2810000340401005500e500c081c0c180c48040d422668140d118100c190107c0302c802c0c0001c24031034140c3c20541c41410000005040d82070461054035820000b4103003500564204820460101d81c41a08400c41d02da52250302040e46442840c4c42203080a034034401510801c00040041e08001c021510b1401c2a07000342c11001f08480040e010441840c007010030009808003c0c0a214814251049150102d00d01407008148841d0003103650215074403108015615007240e82c0c00d900301c42d810135900060038000300d0041c00c422031003500039507528548031f0420307107180c03443c030740310249095105c05c5440191800003041415500c081d540140e03a2011440180d8010651007801844040301090a44c02e2810100207107041300c5082d102405100c07000292008445005e0f00c4081d4541c4906000030071901c0c01e401c0c14a00e40c0328 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 644734316 1250 644733066 644733083
    0x3060613020702090901020315240304141c020606060f250b131208010608150a0b0c010e010b04050f16031d0105040c05030303091005090304050307060903140601150c 73
    0x82da0743c0403e1811000311808403882e50701204201d44118040d00c0e06000313030303802c841c0d042000c154045050340410068036050a218008000074040081000f60096a000c11800700e072100c2d11a00c0042c4409600c0c2ea040d140107020b03020110307071f150403c501500c0421003464507a501303042010460410055240d401410300280705001d60010036811120300d4019902c0142d0b100b664241802c00740e0f243c004005c0c10072f04000c0b460004000c0700740e018201c550411007046494024900c03044c00210b4424450b041100c03070500000703044200e40b4055000201070200b880091280d40c2040007008100d8800310b1340342d00ba42c0da104002070a000540f0f500c403c01c0c0d041c3d1f0300780050f8180c02140200b10094408800c410b4aa43d2002400140a0121003110080800714000c51075454915201602c07000300d440300c104025101c0022079100d0f1014002e8601500c0f01130704903004940d40340d0b0002c0c403003000c0d8801940c0c040c56004100001100102d04c1c02d042c0c4069500740e0ba039880101c00304440d43d08290707109560044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 644735566 1250 644734316 644734327
    0xc090d02190b0c0f03030f1305010b0a0b0a020f0c0a0e070c0b041a0615270d0305040f0f0e060d080c06041202010c030b09010b1b010608100c0e0306061302 68
    0x841801503180604a124001612004102c004519041c0404814407a17070740b090003007020608140d44440c0e030154003400303d806244403c1c03611a003d0094407143c1d44d400882010042269015500038014480e03040d803c442503070700104203d64603401002e601a4000240c036100b4005410070125840d003001c05454100c15001c00c1d502e031b90741a03010982d011501580303080002100e1101400340c00ba00240b046031918034240018428240c1c922039a90302e07160341b468500240210340c1220000000000c0c0107445280082c24034580104554414018116400303007003240490015104500391050741d4914074000310580381c0030308000702c00c0c43d0220b0844e201d00041001e10311b02c04090201c2805540700b0411000313a240c64580107070944462264a01c2014075060a040b0143d8138184054111000180101d584440c03807a08a52180440d480c1300403d5801c007000000c980030b000960149540d84908104100c5081a0701201c01c0d0b51081c1c1440d0303141d03000d4400b00d905850403050950300001c1e0301d0300c01440c21 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 644736816 1250 644735566 644735599
    0x2190902031306050109020a080415091a0412051c02030c0c0109140d050702030c1212040303080f07092402031c050103020a050a05060415022a010f05030c090d02 71
    0x20303403040781c11003070b0859030102040400256000341c5014000d800e0003942031000c44200180001e43c003d1015100d0401e20005844a01450b0701600c9040d800800403c454800100b000c90010010703181101d0f84001401c00f1040e40344288250f603000c0016a03241e54842801e0311101e806500050f00303504000e08200300040411600744980c01019220307031004903150210b07620791410702c02d14011960a001d820441d00006030f50100b000690140700701c803810304507080e903200f551500341100710079101b140c2c0020703022083c103170080d1780e007071150002c003081d0915a601c02c401114800300620030142912100101c0c03200c0c445000700d50a501d0451841241c0c1001401151705600a0701d0f4001c0c00c0341c0669600040c425410f0054042e40680420b03505d901c6030301d2600020034094402c91140e8103c13034000394906002c0510074000143c1d00a0302000741c60b20343d103010301c044066090005486000c03400b51511103002600170001d8a01c40c80c3c072182450b082a08400a12a082070301d0401260300813401807003580720 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 644738066 1250 644736816 644736821
    0xf0c051e0109030801080105100911090a1e0605091008042a08010b030a020d03231306031406010207120f0b010e011502070302030d11010e01050708101a07021909 71
    0x4025910000b050100c20390a000e001c040b410b030401e402690404040101d04581005818200d425142d0300061a0f0060500000ca80c000c50b00070a03880741c4280303000039299080d1000b8000300b0488144500c0c40c55520f03101911b162040740a4503401c01811411401418003070b1100c01e5115005101e401441109207410300f240c0c9400c0c600100300307800f81e1481400003a000344200c0c00c41042c10b5000f403004483d00e40002c1c0d10542c00b03000040800001c0c070b0a601f2000c034013100021520103607003c0580c40d07205202e20840807a595000b407600091030081c0182086103a60011405070806030041c103462400c240d4800c007001841c1c0300c25100102001581e07400a80e0416520303000f080302042000710355040c170500c51119035555015a0440d0301036107003440542c1e804181d089000b0f00f02d04200c0040380f0303c007000c5809000320465003407255281004200d503054201038003a11a81d030789510311070241d444411809000a84030000c1c48200000c6c0b24040043c241100d42d5040102c4503041405140c2c0c3d00d4030448113 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 644739316 1250 644738066 644738113
    0x2070219080c03150f0c0d0906060303080c09180618090105100b040b18011e09030209062202030703061703071208060d060b060c0318120d0f0c05 64
    0x81400031010400c00208103000348500c40c4000c07000b5000c40e0b481c0141c508501c40026003059001100e950103d80307007030040004ca07221003003c01002c0c0315450705810810010140f03440240d000c10610347c00904410300c190110f501c00c1600600c0f50150b240c4140c510031018100418664010440c0c1c25000501c417800386415200701488400805d403490801005640e400950744182c00b2007506020a0040c003914805a42d1a860000510004038100200495490100020340c502d85100485103d4030203030b0114444040d02e00075502d0485540b01c0c1c40c1400030099640011807809900c0c004850308140058000b1034200300d25180114000343c4681d03480413462200c0199111b240c2c800a2360404101d030002100c55050358130b0800e03114034500b080c042160200451001060a541d503002909140c0e524001c4d03c51502c1c255048940b1964050310103125140000c0300d051285c2403003004640341080c000b4410300843d9159940001701c0c81c1d0b0000940d010390b607000c01101c1e58001d0084014040a040100c82d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 644740566 1250 644739316 644739349
    0x203010b182b020406080a0503190509090403020c030610151803140d0f050a0e0d0507030803010f03050c1504230d0659030f0c06010e01030b19020702 66
    0x502c00034588100022250f143d03002c0026504005071610200d01e011040e5041280c20406400110162141c03c0b5514400c1115203a4800e000c1000e00051541c0003403140d4800c5c8060342100c520352216000d902c011513282c81001c0e032111042c1120700911348030381d01071248032010001d065a985e44075a42ea909a8403e601500a55030042403003907011036125500720134004207411b10501d0050301c1c40000301041010180c640c00341b103c40c440d8204020303042007010700440d00a49003603165619250320f441c0c041d0741484280c1d010303c00d6070f03080300051501509040001c480044030900d800c1c6408807a030066044216481d5211007036010f0500142c4600410070001882084001a268007808082042107106818284001001d0121a0109040c0e19100803911103c099440810070200c180d465000041001c03400301d800046003079000400300b2000f50a40b14194010f98007141e80f101038221b103040092001400c0f005001005c51040e609601c020750951713004010151400c0b03440c2e0041600100589501c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 644741816 1250 644740566 644740639
    0xc020c03011a010f030b0906060c1009051606030501083706060501270515090a0b030703051b0f09060f1602092412011407120b01030203010b18 63
    0x82850350707400b505040c600104c0b420308001c5558014003082c1d02e000c00500440c002d40c00080e5104c0f403083e081040140e1250b10745000e209112261401940303030501c800300f0b6803c075003000c0c0c0302040c02402406400d059440081c001d1900c851000d0f000c1801d40308900500811152414514000520160703000080e40e0080320301040c0180f5180004001142001244074041c0c8034080b1001011160800d040803a281101c030030800f450344484003091841596807841e8800072000c0c001079044400c0010f1440b40c40aa10100066607030380703100d000000a01d055402102404000150a20080d00060401d8103009042c0780c4c00c01034500c0c848003da502202982c0005c804030500b1b403013140340c803500b040c0d88000c0d0035610340340140d502a402c1fa05048500001803003a0100e52002404400c2540032105000600c03140d101c044c10801c101030011021080d840c1491400d081e11910954001e0085904031618412401e01d0100c0c50f030360050f26660036004040e40140c1d21041c07215400300501405070504c1804450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 644743066 1250 644741816 644741861
    0x30a141207030516150606110f0109050a170415081812070816080f03040b10060905010305100b04080c010801120b1303020f010908030a15030b0a0c020c0301 69
    0x854941290100c012032144030070049100007980c04800e81d800b0b0070240c0f4025004001d00e2800c5800021640b4441c80154a010f40004031698884a02e050103d1800d0540ba201e0b6680c28000e0309036000d0041c00b070801da11000f00240018011490018961300e585046810140c803585622020400c45001c3c200140804c4140400c0107250040030303004100c1040201001031042b8203c036424051b250022f01081c03004a1840c0c4100c2a458420300c4003640300e501190344001007422040780fa00103440503141c50a50400040000b0444403034841078032215107c04820520b440011005080b0080443c00c1402d1040e00000d00c0c0c01143c0c000d4809004e040001d06086c40395040014803454050344007d10a02e003040450000c50824490b042c1c128404481c0182150464102607142245104102c411903281094440c140104c05001e98000c2d039060906001916181040c0c4541c8011408094038a8103c0e0f4046005107115911a845582c0c2074015986055854400642107625108101d619058241c24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 644744316 1250 644743066 644743103
    0x3031003050d03050f15121212130b040803041103070b1b0105130807021c060b040f0207030f030f06030506040812131a07120e0705040e030a2c030a 65
    0x180084030b03803031600300264548816280c0507200b011307100b0300705c05240580c441c040d500d49601c01d0b52000c41800413180b0950102c01e91000350b50004004101030301d2200b000c1055110136000710b280c8141c2041d802502c5071110744901555900140003150345100040a0b0b40c5a600c0a1003001e00520f40f030324044d84c41e01c108201c200c9110040d14924141645414208111000d10b072501d0880f00750000c0203591100c80707034804107000800c540d8002c0030200f4071400f02800c1004a8008030340a080689090201b6541c0d42080030680c040e00320000d0100c1c080024808929201e98044a2158401000401c01c03a42e242c46860400300240c5081ea0032100019958008071904134a031a003200e030000000c2071007001c1d80c4510805070500c0c08484a14a0b4800119003518440d1500400d01380280c2810401d081d040100107a641d803540c400c1c075020310b040c0000511072b200048190781040000382c0f50740c03c001003024440098621980814517540701903540d0502545c4041204c0425070744202084954100e4040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 644745566 1250 644744316 644744323
    0x2040506040c0804120c0b0114180105100c050c0d050102210105152101090c09090605150706020d020a020604142b11250b0301260f0303100305 63
    0x800c0c90707000d2400c0c00720700c18038941d1140700254065004a020602503000003412656141d500720007500b500c000d0741c0041501e10082010b107046403001c4400ac0050b9205207000001c05009100d41584a4a11207642141304c4c0943c0c0a041030901c00c8040e14107401c018400905c1020180500740c540f81c0d4040340c0c032880d9501602d26102820f00540d5602503940c94280019a036070002922595283c0d40412110424420140011606c200d024003020b003d43c1c480a07074800402040d841000020340c0304000241a040700c1c810301c02611400342100c1451241088880da8603032101c0340486030550308000020740c1c0001417014000050146d4046c111034101403d110781003031b07654500f01c6099007000301030000d480e050f40321094098540280c058a000b03610b20081e240321801809a64041c004d00c0070000e042000c1000c00d040207011004d4204400f9203410840d0298042400b03515400c584200c01111448600c0d40580c00300d49509040310f07200103880705400e003903030020f03a00c003400c16090750010f2003000303402d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 644746816 1250 644745566 644745571
    0x9060c1a1e0c09100f1107030b0603060f060a05010320040603090b0a020406120902011107030b0702011104030c05040207081327140105150708040321020f0d1407060f09020405 77
    0x841c05241048980000101d0014010220b14188850701c00c0303c4802d031b40640c0d0001c01c0d040c0c8070000d0351642507807403e00c020301c80c004a4a6078841c1c042e1900154103000e1228050303001c2c440242442c00d00d02c0c01c140064000f4041c82c4149a028103080c030002c10405802c03002030011b040e03181c0e07001c120742001c0e2030305103a5824054118482d00b80103002c14811194443c00c10080440f1080c4080355540c0c1900040e2030006005070b0410160044039808800e002280c0ea11b0ba003d101142d00800003c3d2114025080d41d0045020052680103822802c01841c58140c0241c582c0a0003a40030510345111481210f205101d55802000c00c840000c108420440002c05000841e9955138401d0101000d8011000820b00050081c80c0c40785060142c440003400600341a600740c0396100c00768a40c0c8686900b0044040612401c451203003114a0380c00492803440442c03510800201d910040c80c10701c420b40300c103a4005464020789a0f4101d82480070b00301050641c090713603c954a140500080020250040c002500d100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 644748066 1250 644746816 644746831
    0x31a01031502130e0f10050a050901090903030e0a030f02070501050f031605040b0703020a060e030c030d0e01090c0312033204110306160f090609060c1a1e 68
    0x400114900124010140c000c0d1440182d480c401c0e0410001d00ca20582c02416105610342c04014103140b45c008014060b20f9010320446150350344000b003288420040c01810b4101e420f001c010456442c0940148029a2207030601080c002500656585451501c0009800155000d6a00740c1440d40500420010700020b1814500e0200f42141d040c01034400a0b080d2030084440e080c0007101507214800f0740303000c0d000300d520f081c1d5181058100299100c2080c6025122103140520115410000000321010340c01400e01450070030408010690052a00000040b07955481d06a001c000a0a400380c0c0406948901c2848040c0f01e00c0c108001e003282c0404030010192803213810010350750304a1800011401e0429050b849072681e0714941440f488040c2d03060300d0380610070320090000f4850078520030380003c8865035544034070690800003201ca51900d4890300380859517900c01440b1581c030601d150480c150040740940160101c80406042d555000c41d82c61420404000f01090160490000e641d00210b9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 644749316 1250 644748066 644748113
    0x31201080d0f1d061303020a09091703040303320a0903051b070b04091e110301050907110d050c0d05401d070c050c1002030409020d0603 60
    0x72103900a40025960704107041849030207451210200680705855103400c00140ca03e07511100c030814442400401d6000480c0300b9007003040301145e2000301e44180411a40c0150a12031720700160400c868036540050010b400301074644200321044411034a000b42800c09490100700540e210170b02c00840e0740c03005081411007606111101d008660300a064491720070710040316211002601051616001203540268048000800c001881c002a0342c840740e40000c00c40440080c0400c410300803401c499840301915516081400148050300703000f40e85c82d5001484e800d01e9241c020514030220700d07058071424803100045000481c8191987c0911202c1c00c60b40082c28071a06090b40344188a00d07110a84600e030689070117000001c0b0764403816041d00c180003019082100ca810303072200b65000302105100203100310040d071100450032442c4260401ca03103060700b203c09842030540c10002c02c4806180c0445400441c0f0040c40041420b04984c401040d05008118001601601d035107000038189040c00301100007680b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 644750566 1250 644749316 644749333
    0x2061332030a150c0e030a060219020d080109020d020d020d0b01020118030504090e0a0c030609120912030c02010e040608070e070504031e020a09020307030c030b0f01020703112103120108 82
    0x10f83c02622a48440300070540850000c00d20041100d10207030114041c0e900d8890390391950140800c550083c0154240d420f14a410030a42e1102669a074240c0440e00c4002801540100440411035014000581c1c2c202c401514000e200428401680c02402c420001d6954803854492150303024420b010f1021807210b0f0818100000b914090300d00d0085115000f4941d84405030828481c905001a00708254000710080c0007a2b101e082003c0144464402110518826000c400340036000e00d90180894075a002060071440560303804880d40040000304a0502035414007a070304ca0b40d520b01920340a803019200070600b161403c00a641c2d4101e000d0500014040c0400082c00030420340100c03542c4a1101c41e440b4001041c081c4040745c0041181c3c7e10000d01030344080240301480b58590807404032643c40b50340c240b048003440000c003c0500701d2215441d02680c0592010400070f1310b18040700c21400c0c002071003207044103042c000b040300f201c000c0c1d061007196030030000e5000c1a42403003440441c050007100c00240303e800f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 644751816 1250 644750566 644750573
    0x15080c0f1e090f03011826071b0902070c0909020d060612030905100816020c030a0803340f0302040e011706090303010e0103080f07050d030b042702061332030a 70
    0x42c0a4030034050480000220210b4140440e0044c441f02c0c2013940b401540e80d41441e08000f100c42c500c8041e4120b164000c03050001d104029170080c0c0719010b402c0715048958130301d805541c000901211004903040004900740c01c01003040d03803017504000c2c840520300c107100c5070140c540100140c2140d0030040c81606034811801803154040300140e400300e01013011600000c81e00b0400d038031700307401c2d2040140c1c0b42c8078901200d0104894200030314018141180c855008800c80c0310035003602a0014151a8443c1d00f80e40381200030340c440c03c0d03070448510641c14014a803545441640f55600c10903044038002e41100d0710301c550000c8041140c2070380011460080d50440d410300c00440e1360101c040c8001740100c8004189480491141003c482c0100c0d03001c13044138001c3c0c0c1303c0180900034002c4c0d10070443c411032604031010b81540700b42981d01e00c03401c0380800301c40c210815a4208050b0360424800d451070103a25080100b200c0c5504a102e103001114481c510f5181842404545170540c6c1410711503000e500f000e2000b0002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 644753066 1250 644751816 644751851
    0x1f060f09121a09030d0f1d0a0302120d02040b0c0f070b071e1e0c080d0201062d03020603070c15020a02030d050403030b04060b040f15080c0f1e090f0301 67
    0x12080b40e4141c01c4207603141c5100f954554040d10f40c031121180d2801c00300f0b8002c1c0060b41c1c0320a805181174202400700d04908804542c4444c180e10f0041e015130805a030b10b0200003030081c010649000041c80040c00c20b07031100d01c020303502c0d00603240b402c42a90040c0f54404d030852040103414018588641013a01d480e4141c1d4850300003038078215130000d00d5034030307507508200b000800c01440c1784d43c1840298440c0060362606190282007003612030039899000744603a20308114410b01440c1d055861003c14048003070001401036000103800025030800000e0302c080030005a49150017540107455039a92609030303c0003030401c0609204500c2c0301d600358510401c00710841c0c54001c0152407481e42c0c950300004044d603540c01c0036400b5021084d1000d50151030031001180c00c5400c80045e00c2590350341300d01c0140c2152100b1015100480c03000410011404850008405112507801401140c0d0243da9442c00c00c403040004a141d0f5411030f4039284582e60104990700d550400c000491019102200240080c0f021700502011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 644754316 1250 644753066 644753093
    0x5011509170c040f0903030606020d020309190f06080907080705010e10110303010807031b0e0606031f1403010c0c03050a0e1f020c1e030c06031f060f0912 68
    0x5854a00c0001252120341c1800004204940076106002502d0034070302420041136000c4089010903e000030100d4102d01c00900d4242208507038005500d0b02c82c0d200d0401c840d1018138074110081503040c41c0007003144401c0410b07480041c49943c13a03181c200d0614603201410300100350042415a400402c04010903a8890030345242c0703200554082e10035040885048071036000d400c55801d8580300c004000940d94200055000490b40262400030356500081d10b1070740c2881d038901c245041482c840c8003151041c50090000d68100c10084400000c840c3c2c0c2400c80404101180e02039183d00345020000300103800c081c0640c044010580c60700c410400004ea41c00340c01400740c6003894040103449011017050351103c20300e509039405021500d5100100c5072500070351300c01c0b50600a500602d82d03c03181044220840311409601180240980040e4402d141070101da40c20060401740b84005c0c0790b07101310101c0d402400c01c001074030841e9a900710341d0680d030310045c2035000305a01c00074042a00e01403001c04644001c01b08013 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 644755566 1250 644754316 644754329
    0xe060d0e0d030c170c3708070e0d0206120c07061b0e04020c0607030209130216061409070e340201061d0604020705010b0307090e010b04020a050a0e0103110703020f0105011509 77
    0x2d44042c20840108601032440928a4220b0480181b0a806500081d05c00d10410150391140b0741078102d40b00b805000ca1039400c0081d0010b0b4140000125114030220a56000d196a0318640c2002c5440d01c1c2c110503207808802c1d070b8980140b01a0002c04403540300b0415400802d046c3d40a615220403220010342d551b0008080d0420150b000c50041c403150740d45841800e8075040c0280070740d19542550340f6042a08006401100c2e00351500a078802d05c80044040c083c40382720349a000e042c8651601c17401841890008180050b411000010824690218050159010070001c1c0a21103d51807201c080d00f1162150032070034503d8600c92010f40860900c5030708030351045041e01d0140c0c030f035403043c038003540901807810b0740591501613002d010444007003550119245242c814000c0c0070a58414040c4000c038481d10440000280e010000102e4683c042d01c1d420f584070304103141c001904002c0c0e008141040c0c010410850068100125070300301100d090290318058565009507500c007113814080503019596920410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 644756816 1250 644755566 644755597
    0xf040f020d020a0f08030405040b0111030a120204030b0106030b190f0515070602030702100f05061e0f151b0c0604060c11090412110105070e060d0e0d030c170c 70
    0x1191648003d1000a100c01150000b805898001d41c6840360868010030b4066031804020686540c45686440250b02c8180007543c030f885440b00342241d200268014080301d19808000010010f001c40d40030500038407150b0341c0045d18040d0321007001005460780810f450780c00c0c40100e051008080303101d0824104c03030702140d2a99488200b0031240e0054000c0000242003a8404010840070325000f280700d141d01c41104104202807105603032404101c500c00d40320143c02c9050515150125915a030b002143c200000b8050042c604191000804c1c8442d90420b000c81c000000c221107503105001c003440c2c48040c09280107401d003941198007050b01e6008911884003080901c1e00000d09101030103c5030418040090300002d000c1c50306041c40d00340441c0e011400c8001801d0045409090081846600d000300f200d0307582c00382d101070300004110f08e6802c2126030030082030742d500541c0790665082141c0b102400160300e020840d84120038000d41900d445840382c002c007031801c0041000891003441200d60070303011490340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 644758066 1250 644756816 644756839
    0x8180411191b060c08090102030c09040908090d080a0908010603082b050103030e090106082422090b010b0f03072003071b09110403020d111e03060f040f02 68
    0x200c0340c0700c95a19542c0440c0e803034400600107024141c0c0118080d103540b034075211055101c0d04d903024201e00c400c442c006941c0d88180950242c070720b8180c028081d040c0c001c8103150304140c07842c00040d142e020015400c589a040002c1e000c0c5044e0340080030440108525002040301d1840d40d142c604861280d1040c0c0200c3d6105941d296040c0b0303240d2005d842c01036030007040c10002580c5a160103003176540309100e803500c200e2595000188007485001d21510a0601040c8100c09200c140d52000d100f04401c04070301c0d4405043c9410b4007541c00c501441403d01c81c1034900c04250340e00383c4e0500703d070080e1041c2c00035200c0200800400d01092040d40c1102c4c1c221200f0320b40044845410002d80000142e41c1d1852441404001101018421940030440c00e4044021901e84425665030004003101e01826401c1c4000304107210400151070702d100395881c1607000d4501005442d04480001e190010b8004180031780c0319160842c0005070074100f008561004010f600c40791107041545901a1542e01c04100a1050150001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 644759316 1250 644758066 644758117
    0x105010c051015230112020a0e09250503040c1205060705070f0228050f010c02040e1216050f01050f040605040204140712110f04150c020a0308180411 66
    0x1280d000a1036503071010000405440064225180350301204c074009079120350316401c0707145103100300c590440c4c0c9511540020814041408003444000704020980c40c1e4008408500140d1812a03001c005559034801d956031a040c0b620700c8090700c09401170b4810005c02020b040000b080041c1e040c0d0000c200c2c0c2040c54440304e0030b240280501110020080d008258003c1d80030340650328900e080603450520b03101d0301d0219242c100f801031041e0b0101d41c0c107000035888114030b0050b0034640d10640684902100341e0b0701d0410103480440380340e4030500d2091100c0020650180c2442070a001443c00300780c1410003801a410641101e250b0036101520107006d080c0d807007001c1011035031181d00604004c41e95102003506803034120b42c0940a05800c0d03000c0c14005080010b0910f41110503070403250708001084420307040a081c000403c552504007801502404200800c100150b0f41d010719480080d44a80c5500381d880e9500c1e00002d1410a01d048450302071070401159031000205a801e5400c40b500305088501d54000649 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 644760566 1250 644759316 644759351
    0x2209110f1804060e0a0506040b031f15030c0303020f01060f060e01180605130e13120207030b0c041503150b03070c140f06070f0c03080730050105010c0510 68
    0x3090780e030180c508040080c0c0c3d541d196403031910400014008000f41d5540034280000d682580780819411380040f41100070381c3e0f40030b5038040a0010900e0001071800003001954500c0c840784d13002950551803005003081050780c100801000590141d0080c01094581211005040d1a5006c1c00082c4400200c604200d42d2140b1020311800b00d820007006401c03aa00c00003e44942d1000018442701400072001180f001c0940c0c02c0305001d010f1484041f00c0d01e194a427109500481c00a000c0021401180c1001011500421120b40200d404441c41e83c2e0355440c120807100c104486d007207000203050a0104c000e00e01344124845504840d12860410b03640d07624008200c0300704045d00001000300706401c1004210020019401e001d00305c0d210700300c0e50580c4440106441e40d6045403c0180042d41540e25440020b114508030b40d0031400c1303400c0c00b2118000f108140d109a000e40302140340384c0c3c1d186032070b103010710112070049500404003801c2825802550b52109503e40400c4088510400e8484207039042c50001d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 644761816 1250 644760566 644760607
    0x41202010807140a0c110a06050d0e01020903030a020c01030c030b090f0703182f0a09023f012c13020a06020f0606180a0513082209110f 60
    0x3032964681d10202402d01401c044c03000107050721152151040e161b080c1c104100b030b00c004d0300c0042d100c84e0704005a00b400480501152120b00000755001c0c02800c115032000c0000c0c09502400341c001e08440b410a400040c103d03040188007030205404c1000c8550b080d110002c2c2c46e5005903d41c6200140e40c2e585040070b0740900190310a01ca4642801c0c241c000030302404106d580c074031015101c107007005d00f240040c107c2051000c400307460f9401301e420441001804095030081481d00c0500204803107100d10f01c440d11308039403854022151913500070125010300c030030024035403805440d6010343d00c245080c03140e400606201d0b01100010707a0f94140c00208801c1c080c03180c41c0e040401e50041a0a81072912a1002912040c2007414500796100c0c43d404100d05280c1012503004c001144942c44000d5a1046103803805410040c0008101500c0104c40c2c90100d0a488000d100c50084a62601848100440c91300b52819855202c2c1038018642071454104490480407100740b0703440182803680314070007c040e80203c1d00d5038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 644763066 1250 644761816 644761847
    0xf1b0606010c0b061933023f0405120a080306010c060b121507050a3e010b1809031b0f0303190e032d070609050a0204050c041202010807 60
    0x15480c00184041a40706c00031201c42011000c0c1180101c10000e4400300c3c401e2036140310160700001051400c001c00500049241c1402c51186121182c1c80b0301da03000203038014180d146c0b800f100050240050700300782c100408191403880041180e102d454851600300d0002400980c1004079002030381c0180481034110b1104000b008100c7c0c0004c15101021554590207010305403050742c09000068285405039058030303400707040c580300c09070076940d086151005580c403021010a140e150000592803581d4081240c5007403410300b800051800d41c1001081094070000102704154403841c000c124900c1d8003c01030b55055400740380e4182d05100d111241c9803d01035410340141181c4800f1080040c00d400035070035500c03040b154210411900441207205d81e01d0b13108a032120f16410139044462101c2c1d801880d21080b107000104401410401c040c0e40c0c9906a404644080e9034079406465034101b9880c09102d01a042034484805030318041c50001c48801c041e00415000e410b0180f6100090480f9000e0000080140203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 644764316 1250 644763066 644763109
    0x9101a0a1809151b14070303111b0106060809190f050325170a0f0807030f090506090c09010509010605030403020a141f0e0c040203040510020f1b0606010c0b06 70
    0xc032040d80700040c139440c15018422003041c012900103900130b00440c40d2920000d5552441c00e00c490310140c000d00024605125016400c000c590070b04104809d00421114000001060312850b044000b456044054281541d640200701003045800e820400618403992024800014584a007811802c502840c0c00c02054a56102c00300180801c0c4038000c04c0320144510101c0301c209407003103845d810500415aa240104004091907503946019410003540061507140c0810340a2a1664030310590720100012980c030340c449030501c000d5100501509100b0407007940c105810b50300d4000041d44c0a01c041c42a4070500c070b0000042002e040c801d00c4402140e64205007400306101000d502d4507a244031400e00340b00c508420150703500001c0228041d2a038007030f440800504020300d046040000070350001d08202c485204812206c4000b281ea400508464580c071404162203020b03e04400c01c250241038071000144d0060b004101641c2c0e002024498042e8000b400c001d0140c2c0e42d100442c02521607070b00080758000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 644765566 1250 644764316 644764343
    0x10c050705070f030b070815060d09031403071b08070c031112011b030e0c03070b0a08132f0a030602090f12070302060309120309101a0a1809 62
    0x64200004145051003070302210b5100b41c3e289070352200c81d080760000030548004c031804680c507244915000c0b030b00600342c084181502c210f03480004131560b10800351046400c1c2c40ea9581418590000d240000002d22720100c5071845c500017100410300240500d0f040b0720310a81010400900010100f5074413410340c0000c4420025072a400c040071111384031591148542d04050840034142d2041c000d02d078840c01c2501800f80c1550316004158040e0144608810952040b00ea0585150703070704011181c002d00729080e01e1130b038030b880c0da02e00105100c4d0010001007240c1c4068800d44000f1302c0d071050301c0c2605100d000114614140c1606109540c00d80710310030644c0300e0350030b40c40031041c00b40550041030402c8089905900704d252102c1444050648840000c2d21500458010009814010700640c6d00110500030b4907540c1c203001540c02602d4105440c1c0700d1303031644000300c4501002c034140714900b1210854000444c86c540000300080d00301055006640b06d606d001100c40540003002d0704150349059102901c0b40000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 644766816 1250 644765566 644765591
    0x150305040311240a090209190e060a0207020a050616060f06030204150510030b0a050d08120412080705040308031302030f15040b010b03060a06030c02070302040e060417030c0904090c0801 82
    0x1804403c002d0a070f0380366a440429504042c610034040c00c1940034062035103954400d40c4903416078683c4005000915154140401620002e120984c4030b9841800c0068940a250050004501076900324074004c850400241c00030003c240488101c0d07640c0720002141641e45d600707854002d003500364070081d00301341002003030004412810351840a41e04151901e54100380003034011016114882c80c110742002c01c0d020248403070305100781c40c0c143d400e01943d03071145850344200c414912514116020744004501c04844d4416a0340410090b801450750700c0d06505003819501e4100c42c41c44082d01c2c07072031401107840713019045450600084000034581000d41c0c2c04c80c007200c84950001c2c4400c0b54200c842403034030b900101e080200141581c0c0100303406489041c04604041c002e40080c40003a094030103600c9134a1000005030344074001e942a01418001030020380c01e06140c8822910054a40c0c0030326001c0510400c040941890242c41c2080812140400c1000030703420000381c03102d665004283d01d5428098a2100c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 644768066 1250 644766816 644766853
    0x20109060b030303070c030318081314030d080f070e03010e25030f0201230a05090310141504060b0a1e02070e150301020d0f1a0406150305040311 64
    0x55000d040d00348104201c40381056201e2004491000c0800c00d40041a40440d200c0d900c400703030080c01c00d26582035440c055251280240c000003525150441e51036814040032000011400301031600f030b8020210308071a101c0103010043c005240c04280f841d420009054184642ca200c0e01d032500240081010031040205a84c403403c90980695510300c5241a4100e40c0700312001d44001c41e600501c102c07103a1003543d8011602c14600108800200b84640004215001410010322441400b6140d03181d403030400506060a0680003441e1100c02e9240400034050050b015142c1a8060700d00d07011000c500d100000007400030100c80e00705e12201c6001203540c031199038001130500710324a10f145800030a030b41d01d0171049079980c0c85801703002c50f800740c01c10220f0422a0307964810040000024005800d240a151510080b6070051806d0019240c4580b120302e81e648003c0829941b80700107580601035203003031144c1309101c1c0c4451061001016030764000942170512665208100c4c0d2618420b4032540542031545841 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 644769316 1250 644768066 644768081
    0x1e02030a110604050a1707050d0504090501090b0d02040507111c0806030d051210030803130212150c09030a1a010317190f0509060406030f05070203090d110415060201 73
    0x401c4503600940c0030154000341e998451644400140720100c059965080c4483e200954108241c07002d10501e0000b607014002d01070284c0c02d0385c0e03d19499078a010450400d84106a1240d09003516041084600e038403103011041075a90141d81c081815101c4a2044907000d43d1101c40344aa030207a0040f13100c00500c04440d00d014030b083c0f0b41d9180256100e000c1095150580d004540c8003041c0c2c10040680350754040765045502c0700c050002c11441c195030b920780c004290300032200700031400580401c41086141c000c0000148034031031070040083e801210b1400130884000b0340214681c0b480400c407ca8642d07010440985600da10622081543c2058004d401106c40203020450340c1c1c03201c4904220035103041c5070603a9480104802000b15140b083e0340180d81c042200300980d000c001c0c04100c24050b81e105c0030014402410b00d50f40008610005072403030000c9840280c03030b030f900b150420020462690303164040039508076000085580700040070b00020700103001100051400300c40c918000210960194807404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 644770566 1250 644769316 644769337
    0x130e010504051803040e06060f0403060e100606090e060f045013050613030207080a020906090915151804031b17030a0b0a060905060414011e0203 64
    0x2c00d0381c81e00e408080036102800501d4480307601c2400704028402e40803c90580010b0040d040c18613140320a601d8500543c0180c00584000c0e464020041080c0020880241c011004c41800c003c0d45040c140c00912000062040d43c50040d21000450065600c001c1d40c0200c011008204000d6603158441030108410080e420040f1407081300c074948420ba08103500d000080d6a5520201da6141c3c07544022250440040d01500c1e40d01023141600001500c00c000319802280d014124103101d5a0503d0001c0c0350080384d82001d500c68000198800061701c1c0d0b8442250041d10803615500c180c1d83d500c500c54900700035400500022a610010321494103050f4000d0340d00e001054a00020340c458041903600424420b0b034009000850f080c00c0c1140b00d000906188000c00d2049a005111041c0790710310b420a1341090781e074079040300d54a94642403035240140482c0014007282c1403440a8525180c0011420f004030b1103013000e0031402c3c04030450581c2c480c2c0a0303000f8800f2150040c00b00c6000c860402544c9420228010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 644771816 1250 644770566 644770571
    0x405030a1415090d050a0e311125080f04030201121a0402090a0f03050f15070206070e1503040b0126061602070b030403051c0506030c01030b0303130e010504 69
    0x354024544030441030701c9481000004e011a8011240840e882c1c0e01800400040012040000d0b100c0e98444000418003c503420000c3e09002003034081c080242c100e00010481c0a10b0141030350450081c40b000e80d88210310001e0700d803c44821000511b1404202510002d141480009180506000f4035000d401964002e90380c403035800803842e903007030100e42c02210b000d5070448008074841c0d203078a00b580050601c600c007d05101401e507030f1100b40c0b103403045961b082150b982e0040540701074030f103034200205441800070003030030912400d000001075114240540a58108145190004415200c07800844d14200c001c0f90401c2da01e241070700f41080711920a0003207010211021300e460004047d0900d03136010410002d0040d0059480c3c580748031391070480d8102031005500480d4000514003600401441c8224025100c1540e0f410055420440002e007a03500480900e04d00402c0c080e960718006080308440400303080010701171000ac00001d245000702c040d010b089100c1b5040110301100904d401e00d04923203069905 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 644773066 1250 644771816 644771833
    0x705150d061202030a150b030f030d0b0406030b13061103070e0442030602040602150603011812090b03011805090d141605030d0c0f090f06050a03020405030a14 70
    0x462800000050001e58960300c0300c00c5d00004280d0303460444000703031207089000403d4810800800d04008a2a90000a03a04040390380c490011150042e1800120110f134108081c0303007140d4400c51820b030084c20344001915542c0320b080c1046000e50081d003140f40440a2291686801341c0d00400e07183d903000340c55010f6030800e113801d100700e15036902580404413682c1d6072002c00008401d28003202c0844c18520135045006800010101d001840144041d2001e83d0203441c0006000b00034170f00c41640508840d0003030b850300d94100045803500961052040e030015044001d889000d104480d003d0040d0407007907182e40f0000001851818540c884000500c42c80c406005036940c995079036489511400402021885400c0a03038000140c14008001c115000ba510b4000c203945500c0c1c440c9540c104240d841c0c00540e50b60400d4810581200589520364070520f0f028800908103500007060044c5486481c0500c440424000e201c01c0c040c5c0c040e10040c0c08080c04449512a581c10b00c1c001300402082c0c07010542c00340100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 644774316 1250 644773066 644773079
    0x50f0304060e1903080106030f020d05042d02030d1215060f170f07051c2906090d02091e04080703090509040305120703180b010f060507050c120705150d06 68
    0x1540b804244c0580351041d040e86048401d030b001e40603225800c00ca190b07082011101006180c440c0d5130003107025803c841c00059144031821034820360140300d284c07240d02a15044005990014215050303a10303a2a050400c03115a030f1501014003a401d0b952440454140c10225808e60b1002880030801000c0d13079210148084943c10301da100009541c20b8817020171180c001031520340503600401d00f80221420503012400410060400c50340840c0e59841440c21354054414400ca04c10400711103180c00f10f422524000340500001c1010f40181c0c0300900074843d10700044c400d04807a2035180000164041c00443c075103800d1500106d1548503001c220040752003400c020660b410462801d51040c0d5250700c1c0c152401e600b412600100d0807009002d501010744a15440b540c0b0281b200c591000c2c00d11804400c04030707504100c01100490140d80004003041030501852002c03940c00545194160410f1302c1e04440a9402900e50b400d04c0035a40042d90081082d041038041e07101403000400c3d0242503408200b1041d512200c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 644775566 1250 644774316 644774353
    0x2061209061614030c130f0303021e060a050612010903170f01050112020c010605041817160f0203031224091303051318021c150303050a050f0304060e 66
    0x1541000443c03001c2401d10380d031002c80055400c40f0801c0c4469051031680410300c01c1c4480c1c26002441d000c001c0752010070400d0b404020700a0401000c144487d00b051080c0403940c0e4410380109100ca0741c64a82012071010385803080006810440103009100000e0103042c080d0000e071444803620340c0e0400800003c2e50040403100f03894140c807030580d9414030840c100b09111000c0d402008454001e5503071482c00003180d42d070703d04c103800b076070001c41c0664400d030b10446c00d010741d0340e4a01c0c54440071422401c020510358510400014429984d01c00102064904107002091450042c901c0c040025107580c1709001890100d80c541f00d070191500703c0c50704a2a803c0d4028084c2041c0140c07000300f030094581350680d00107801380c00900b44107011207440e001ea11742d0b00c80341820b81c01075804150144940c0000c00c0b60b00c0f5a00c2a01103041d5084204090200c01150540030310105da09200c058200308021070345903e468450340c21a11440317580003445880e8245420301c44010034504954060a00c0359401e110201d00441d0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 644776816 1250 644775566 644775601
    0xb0114010804083007391103030f19050a050d0c112e0203091207020a09092009070804111206011502070b160f02010306030206120906 59
    0x1a515004181c40e1541e5010041d000790720884c0031039128648402030b0200c003106042c01918450800b50641c14840c1e03020700031300d0312140e88000040c69500f541950480b030740c132000c04902c0e1052185440d0622410007410740410003801d13541c03500002960303400441c2c0c1ba8000e070481400d5410090f01092746c0500944075807040d007000038040b075018407984540103140e40c8140c10401c0142050312803081e100c5200b42c2800c143c1c030f80340c50401881c1c005031001181e11444501449591450442c0740d1309201901c40c0e510981c0400122640c0c0b0002142411906c038140741c0ad0003080c1c0c200c428015005a4034148808e800c98810100c004a04802c00521901c1c12554180c000d0200d601c50007641c1d02c0c0c030b0f00c071441050414803500d90490348422030030000707406c10015207001300f01030320450741c000c00d40f00d500a080c20170b2984061051603090084000c2c00c20301d10000500340384e101c168042444038502c0180d003e0889030b071000e90b00074008210040f0041600c0740c0c081c407030300040d41a00d1243c0c2e40c2c555240d1122040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 644778066 1250 644776816 644776819
    0x6091b220905010c020f150a06080f060403020606030712060f0605090405030403110d0b0a0b0f12010b040e0d050a1b02040c02030a17015a120b0613060812070b0114 72
    0x124820304d00c8480e40c6041c2e1f68000c1401380c0081340762502d803201c040c0741003144001e00060354011420071052603410f100d40c540244003140a008070500d0903074000c0900388040d4001d000955501c0c041c041c010404e80c0510010040034001860b40e02c2c19042c80c1e0b46070b400901c020369610581007040c0e541403034584030b55800356038040000303201d5844003034102004080e1940c01c160407061100c05003419a403650021011a00c01100100340c40e43c24100740070585e00c140d440280c0740c8e400420f4a400490700002038803542d40d024a0052280c0c6000c1441211811a12101a4000346848105d964042d4007100400c4100030b95298243c04521004849542080900c41d05013501c00650b240301e91500301c0b040901000e003410b0104104d15210480d03050703090202420ba07034035201c1c44c0713103186080600354460540200300542d410300c4a40c00e45d07100d1600c0d0850040000c1d11500c0c0e1007500301c050326000c0c3d1180c0050011802203608892502410300c8031684403243c251080200d84c40000385540c449024076a42d202c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 644779316 1250 644778066 644778073
    0x1b0f090b06030c07260c0705030a1205130509011503140105010f0309111c0302070801090336170c0409050d03022b0207031106091b220905010c020f 65
    0x183d10124011079040352004841042c03000d02c0000d075480c103002506035030700d11102081d81d440f942d0180e02407410180d03034001c42c02508100e1851001c1504408500124981420110358402c640e0a5034500e01c1666041141d1100000780080381d590500c502101410140d0f46080000c18611140103c0c008000d2282c0390014006618500781c2600c00e4011000581c440c4040c00b0300003040e100040c1c0a00c0d00400803255620110303460700e052680c1009401c0c02071070090b00800202502d80c400400380d400c01c14070f40f104424406041668070440c200780640046a40510004054488608819000203107680c82e550344510b040c0380b1504c2c0750a104441d90540e00034020652080785a50030b074041e40020491311040c44181540344002c03e042c0b44c260b90030a0042c10300603030341c49049c50046c00c1c02c0c03c5500c10180582c88441009010800051001000f6001c255500d00d590390410000f40300d101900c440342e0300d11841280e03603190340c0841e42000415a104400038041d40101c2801241c0d034089684240810743d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 644780566 1250 644779316 644779321
    0x60e0102311a1201290711100c0501140604050601050909012306040801050a18150e190b011805220c030b04080d0b06090105251b0f090b0603 62
    0x1000b0049900c01c00354034001c214186401c51078809003c1c10260b20802c0707200c40040c40d5003208541c001d84c0c81140020350004a0a00c400c5450310800d84c9024040300380a4524900c944c0b0115005e880c10381c10043d80003000340203944903007004004a2409440c0c040c026070400b00843c070a90301070825a1444007020306021200e0f0700e000c2010090382e20388007140781140d0300c41c010180d032529490001c20142590304000702c0c031400c180c8030000458880e007946c142846980880b0303000042603c0f004418580d602d80e030108020031a80b410f2030622600d0368030318209240c0140794808111111400d2412504c3c1810001e0440200e0390000e810707144120780c801e5a28090036000c00144511600410300140206400304071143c5990710035240341415101521109004102503034902240d005008030940159141c0c0e05010358440007800e47e000e55040102d85074144240314089160440c400b40b00e064029158401c00718580c0003002d19015603001301200302417404008102003419014aa046900203800b440c91355 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 644781816 1250 644780566 644780579
    0x309010c020402130512073219090e010c080901090206160302100204090605091003020102030d0c180b092b020609030f070b0c10180209040f060e010231 67
    0x207500519103041c002690500104180d2200060451a40c94410050010340e0500b40150007010b5002208e021480c06111a0703001f25800c00c4071a943ca0380d0940d0000201401d19040019400203030b0010001d41c1d280088110090703105401c05c1d141003182d40c56442183c1c641032512402d0b40d4480b403020b500200c0c10041f4110140c41d1400f502d003140d0091041e154000c46004403c0e00b6a400b5500c080b0703030301d501d465042c001c0345800305803a904a1090810340190518540c0080c0d204c1c09611102c281c0680d440c0c400b100e940b03000303030704c125a01c0f02e2500c040004242c460396515000d41001481c94011381c0b904180d00c17502e01d880d901d4a0517410610b64452b1140c4515401c001c0c071a4850380101d50103000303400101d0340942c000c011400152811061840d21458080903052416840701c50704100c0501f042e1600d50304820b001103203442d903901030f10b0f0901d15580b203060588100d0280071009110600d44128031040c800190702600b454450b512481074a0040014046088502d0301c0880d41071022010041004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 644783066 1250 644781816 644781821
    0x112b08061e180a0902010305010e0906070503150a0b0304060b0d051b01030e01362d021504031b180903022112161b020d200906030309010c0204 63
    0x40060050090090184081c0040b03002102900e00011042d1034000100456805024880c0500842c4050740418a02024a20381d6224054030f000d09011000020405681d40711090780303081c100213041a08080d0780d45440840c554821142a0ba1043c54040074604034600320982d0074001c0d81100007006035600441101e1a0740c14401860b038103160751307110b02c032110000c280150500d50070854010000c03032141360000360340103004420103092054860000e1000403134811884841040007a0422040760f24900992030400b11001c02942c0507081d01d42d4201a00c11027001082664810440240b4070300307204409080690b00d900a214084046a584070a1aa055401005503901a1049580c03e88241200440d010500300321046140c10024000001c0b500e50071080e80c0200b2140742c4404515100400101941070482c1200c1680f900c0490140540d03903800c40702c0c0e0900b50821100840c070085000c0d0880449102101d1724040c04000780059030750325001c01510500310341a117410b09002d5081d401c1000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 644784172 1106 644783066 644783119
    0x131505041703060a1215060e01080d0c03120f06180b010e0a0614280816110714030a0b07050a0206010905040c0e07112b0806 55
    0x85521042c4139070045400c00c904440d08688035181090028144401c1181190f060041c00301d091000340c41002d0403111000111aa0f5103074035030301a605042c1402019011a254a9a1041002c142d40101701d040102000000c0c2260f19446e081c00b083d8150102c0744030b031355070340d00001c7c085580104249942c03200c22142da07080a40b400c840205800d003002250204081c01107890b0390b01d10708a4403503000600e000e100e42c507050003169500900c1500c00300c3d14012142a08000804d41030b002c1c200c41010b84844201400613103082030014900314404001103500b40c416007a4403008682d0350010940240100e42d101e0b0f9640165100085c50b1000680207058142e1500062000290007d043c903422607080b1510040325640c1c104041e41c0c14116040000f08901400d004001d0b101c0e0300216850a070300c00124044e03420003044904030b401c900f08840e07464100000c800e00308041382455a01c1e52 = true := by decide +kernel

theorem cover : BRFrame.Cov 644604316 644784172 := by
  have h0 := BRFrame.cov_init 644604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 644604316 ≤ n) (h2 : n < 644784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
