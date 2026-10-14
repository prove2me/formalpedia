-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3476
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:46:42.007243+00:00
-- url     : https://prove2.me/submissions/b9b39aa4-6fe4-4576-a8db-0c22bcb8c68f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 625000000 ≤ n < 625179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 625001250 1250 625000000 625000027
    0x609090b0f1203040e071b0b040f0c23060f09060a03090501141509010e07200a080306090c0a05040902090d0b0a15050609090406022101080706091401090605 69
    0x650074425041402c192003600018030000041c4125050740048030041d40d240301d4120740701d81001b1014030f2214005400140803d50094402d60414010485814503141c2551a8595020b441e03000d04040700400b0003c007070300641540c014002d61004c2d540103150440e0b11150f00c91038801d01400c075100f071078003007402c0242522951000445d1a03120008100e40d140000711541045011910301d070481503d2440c4181c0c0b0304014078540c0c1200c145280560860700c0303111040c2c030b26203069050100d030414100300d00001c542c1c00704170720000075010340703100b80c1c0e24244802442641c903800ac01101074001e040100110680e44181254102e40f04009d00585035072403000040d00703c050807039001d000010580705000454440c1d03800448070a9080c0151400d140d078940502445004203240680e001c002c1c0700c0020041403c40e00200b50704480c600d02c9003908001c0459140e212102a04a8052a07001081c1400010b400c4038072a0003520b0000985455002c0b4000002c01d001c145004180800c0000300384515440603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 625002500 1250 625001250 625001269
    0x1030e060a0c0908071e12050a030521010f08010506190509190507030605030c011b14120c1b09010b03070c051204091b051303080c0703020d11190609090b 68
    0x4203602954080c2c1c2d0346540d80c2d911003100340441c1203204206c410000d1002561049601000d5000016001c4003001d0b460a0340e82c0c0d0003007a080807950002914445800d1441601c2d83c1c00b038140802411010740c1400c6c1020b0850b400109071900501c865500512941c680706508022280100c40c0501c050780d904024a244642d0280400c81070b034240824401c0710fa0700754101c0825181f040d012591454054801160b8844102c1c0810400110580f541e90100c2e00044000c407819140030708541141c1c4180101c9a0541e04c0100141981e03001400080c1d11400d000c0d5442103d80411100e0b69000c0d41082a00e0200c1d11000c0c203024140040ba0441d50104201131014965550200c042991901d070340311304a4000d0405031004256165680c0b04825040d030198083d44d04010348800081f80080c1940d84602c540d41c00071020309181c1c0315048000005950b40b18080300e455105042c01c05080d200d800034441c10380b00c407009040141084500501c43c0f02d901500e0b440440b0b4104801169028098002c40c00100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 625003750 1250 625002500 625002509
    0x8030301090b03012c2a13020c0609100501050a0302090601030903090f0f0608010905070801030f110904030e0306070207060206150d02060408071701090819030b1e04060501030e060a0c09 82
    0x5000200160310f05100b20b201e0000541d403201a101d41c5c0d4100d40ca1112101804989803446c3c1c18106805021810640d6008002400409006280407101c9070308924100c011104d00f015903019490000d100c0215008085c014201520a1001a81554001801c0a00040c4814105a511100e600a042c411181c0b04000c14030341c01c420360701d152604103001c81000316004010100c2c8507440000783c05400c901c03d2038440c4000c1d130b4811200ba421a5510104055900c030161000281441103503001d07a41c2d140c0d1280a144030b501c0b81a400d0405406140c180344e80100b0860554021035020072080740c0118410b9070100032400c0d41001300240e034000070100f044204029411150101c0e0100d62182c00080100035101d03004a600030701c810f000001400da41c0307030040050035288103015604c1212203940c442f5489840508ac0442d4080301d00011401d00ca000101d220344051000042e407640d41098800c9401a21085c0b80501c400c0134080348143d51810b014000d154515580da8010031814823800c410400340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 625005000 1250 625003750 625003781
    0x15070614040b06040b030f0a0f05030f04090f060e16050c010207060609021201150504061805040911010809073b0c03060f010c03020a06320103150608030301090b0301 73
    0x2401d0905001d42c0c26030080f21480d00803841c00c40c00d0281840c0c00510b0b920080d025200070856501107503524083d00d10007550441d6070384010b110141d80d294040c006400607004030000002d2240700c0310700120644042e40d02910380003048409104000c01c6032840c004500a603414100d83c2d682126501c1402841044000b500c114030300b103004240920721350003c1c040801c15107404521a600c507403800380b40850741c680b07070004035004210070010706003d04050401084d01f004c52a602c0b555903c089000d403600c0744030444046903001d203000c101c0d42c0c02100300b5801c00c02940092461500f002504001044080743c10014009030088405038080302c0c0c6502410046411030468850808450f8001150829a1014800c0564940071011540304001290b2641e8055004182250664079240003c041c24907000344501d44682c80f99110841d0f0000040040d988607000c0c02c2c1e6507145084c4000c001003001005041103090003800c02a0100020030749040d901104030029040f030707802e0002801001c0101000458 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 625006250 1250 625005000 625005041
    0x405160b070b010b040b0a08150a030b0406200a0e0a031a040b06100503070305100302090c0a020601080a0c030312020405130c0f0f021009050f16080706030b150706 72
    0x10030200c00c080d0a41612401c0e128407240d0321500440018080c9020300710503008207101c070142d19482507a44541044001c070610000f0140100400d80d201d009802c203440d4894482c050000b084076910829580c1c20507410350004541084203032280c0b40c40f030300941c50100300d9500c951b440306a552050050096038829480b0076418803d91802074645c2c401c0300c0c00d40e24408000e002a00f0390802982600740184583d03550340c0b441c2d03100c2c83c099004160103058456514005940800181c4031000028010000440c00301d0712084a210007c1c40d120050700400071541000510000098003200e449096940c035003020403114650a010100a024036070009a0060045620107507401c6a580040070a29050781e8105251200000943c0c14504848010005902613850f01408207590fa00c141201841101a0f40c0240d0641c00c065203810744000214000c1a0307058010051324a040040304d00814072802c0a02000f003403e0001108031844403800c00141c0341c00110b980c1000007651022180b02c0c801c5038140d52 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 625007500 1250 625006250 625006259
    0x12061706040212150703051e012612070209180d090e130f11031015061e050301060f1b060506040c0302041a070204020f030f0619031a040516 62
    0x355160180e90580c001c5050b50080f6a4264000c64030181c0304140b8151950035480f482021401088010800d4009980c4e801d010512804170100b4a8000c0011002d09855081d420310038080d40050090080740e42e52151003035507020030b021002d075400d030b45d0103d44485070307507440e0440c0401c03a03c1e0100b540d0819015144501195940000c601019500342c1c801a1403e66500b441540c401c100e0000301500d44180c10380d96100040c0812407001124002074190b50000c810f45a5217402c1d50b80c010420035080071842c400b0712032680d110080108088030041d40d400201001d40014150348010300170380d000c0040038002d20550764002c456050300640301c03261b1954054044d041100040c02d041d102c451117203080080f0410868482c0c000e13102698510407180c0901a4500c0369490075900c0b00702c049801c03d400f402641d00c080310000c084e42c41a4000c80100b41e29152030001c00c003da2a03003511305c0c03144a000300e0b020b10107e0041c03c0400080048400100303a40d445d40c0c2081458003103001c0c1c0100320301c007402c10040b6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 625008750 1250 625007500 625007503
    0x12318190501090c0f09063201050d09030804050d080c0f07020a0f0303050a020f070807170c0402041d010803030c0316180803040513270f05070b0301080c18010501120617 75
    0x8003183e40101c0c0c100401500d40490100e508c41110400180028054100311508810301e00090f070740905041c51441c00b045030304803000b600c03050481600803076969420801840001c1c0700720152070a051410042521705541d04207000d00914840321617400c0301040490841d1981d40e9403201800d00113480d0507000d660703483d00030403950040c180740d1700502529072020b40d04880043e03440180d070000701c054103071a41403550729010705440140126071441443e16513445601c0d00d00c01080078100c000e601c01c4c8900c01d40008040c4500040e03203c4a16544208200102414204252600008000c500f01c2481300a44411a070114503080071803050210680001511741000004204990303080da640580c400045d11940b007212121000801901790702142d17800744040010300790007240d214000000d110b18860b241c0300d103000d007150020a10f107070001005000483d002c001080f41400300321507540c24945800c41031010803206100312814050958240c81c251001038100038040c010706074071a0003641032090001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 625010000 1250 625008750 625008779
    0x304030215190f020d1506050415120504110102061b12040f1406010906080703020a03030f050c0304060203030423100f090506040c03030f1701060e060c012318190501090c 75
    0x1c07441c00025a01b00e00504403940201c034155141d1a0810b890b00c90608201d8682000e60b108000c00403902041e040c1a621a040c0502c6c041c3c14070030300c003015800c0068540b0710041e0800c004000d100181850102e5804202ca06111148102d0325280d129854159000f0380c243ea80108080310550303070407150300000143c01e8101d0707030019070030310405035944541307600c5560f24000a5000b050511081c40801d005041c015015000c51429030f140c19000400309003181c00c00e0b00001c0050f00000300b03010502050f03803040c41030410b8140401001c92038580d48240c5c0d400c00c028800116644919881c1c0c020751290340009034058101080e2011031410f4034050018903441c1c04110081129814000d0385036108511550540080000c081031690800c1015107941100040040d07101c9020840444184070a00880c4442d2490002d000204882400b07840d00303803000200800d508204d01400044501c90000750b8952458078103149400c40f400030308000c0d0241c0948a03010b49035040d001400103400340181081c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 625011250 1250 625010000 625010017
    0x40b04050c01030e122b0912110a1401020f0403050703021018030605040c120b06090c090d0605041b0609081006060c24180311030304030215190f02 65
    0x156080300074480015000c552805011050a030701400081012103140d00050641d80e600c0080c4103054010110000740e00c807560f0b959a110076440b50350160400c05684842082448181040ba02030b61807122455a10345107500054500150034200780d480c0350081d4100c034140d16440300442d0740c1e030f504d80c00c1c0f40341d5901c0c4503c4101d006a420300625a171246c0304005540340c030341c004440e030303260301d8a10788500c006460301030b006075068550740800184c02c0300d102410018140c4540105020703850981c0130048250300c020088408080c08002c0f2884a954031850702c0c03002179016600141a0702c03582012420000f484158040c1c0291510001c10703200c0d0020031800031110460101c920281c16402e01400b600d41e184942d0011440800c0b1100002d44205010a1221240c507110580d10380242c8041d03065480c0c5544240c03035004203000703180074190300030110741990070038000451560819540c001d503258002c40d0b141100254102c0030580c591300365080340d2100003031007005200442c0e10009a6000f0742c0206907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 625012500 1250 625011250 625011253
    0x21050a020c06010b03012105030906031006020606032d1f142206050c0904060e071403090706050702150c03090913030e01180911031803040e0103031412040b0405 71
    0x40d5107840c0f2070499059441d040c0b480103c2d1f02200c00e0849506e503918a0882c1c09001c2400007000c0f0782c54142c041c40c401e55400b41d0000801c0c1c54110041d040c100302903e0140203070050b40801050083d8507940c02c0f90003500c60780500c10a541300080c5030400081c1c3d210745646800940031607600c0650f5400c006001d200003a02c621850303e60041100c4100c0b050400e0b8400040c0e02040d2801058855104541c007a1882c450340f0b01e860320040000d000c0302d0480d0000c80310b41150200303101120f0750100c1e44220400140c98441d24500380318240d640d5032056486000c003005000901320007103458000d80b400200c000803503d15203488507010751b1a12500601d44281c0141071070000581ca0a843c068000301013a016200e59484241280044030344070f80b030f0b40700d0401125940300c0000d00f00c007452003407103a0f00036005130042c0c030303802c00720003480840500101c1030351313107a1041c00188a4103206d450003504503945030624034408000c0519558460050200c50801890000700700424040c15800c164401c0e4816030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 625013750 1250 625012500 625012513
    0x1c020a0e0f092e0207060212092a120c101d01030c0c06050601271a07031d1f050304060c0206070e0d150e0f0709061521050a020c 57
    0xb08407035901c80440a6846880d8102040c2e9586841c2941c110800c0b1280d20760050328207490341c0c941000742da011030f516291085080c13080045046082c013858400014a0100b0390382d2400340c40b01c801145c94109011840f0f004061247d82801500f00000000141c0150180e6504805040003a02055480b11315000404540d03039889600c1d8880e2080d03003158107181d00d54140348103840c0c031108000d00c0f005025505200d001201100184041070141c3e05d0294005542807181d41054a0048124030703a04012000d800103001040000340c02c003442c4240c400000e0300c0c012402d038003030000440700d11800300104903403a80d02000402c0c2c1940200114820f80c0201740038410b07a808548220780d5040104d1b600c80014610b2600c80d050303458042d902a4a00d4000c44ad0702c4990903c40200604940768408031101c181c0c01010400401817041c403020300141751118041114034580100c1070102050348201c0c50400540c2140c0c04030008a9102d074004880c00500104002d160540d020402503000d00c4400d101449240c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 625015000 1250 625013750 625013761
    0x7021011010e0303270c1309150b0a050105030c210108160b0307030c050c070602070609270506061209060a0f0e1209010903050a06021e070f021c020a0e0f 68
    0x3044030300885e0790b450007070102d1059100720031080d1102c018210440c050b544050b0700300d541d08400c07940304418210b80001e40d0b241901d4982c0ca001e480700101e6499030300744001c0d2501740c0e0f01d0b02140301c05c440003030800d1a96581e0390b601601107446100c0b9108850700f049090309240034600410a8103031218402195040e900c42e8403001a04117051003000b030010810800030789000d202c3d400204070301c00c0c40e0030040e083c0300306204240d042041940010006a0081c0c0d400c104940e4002d44420023807149000fa0004142c15000b15801c0100c0440041070154a84000c41c1c1181c99020031984041ca01c1080d140f22030408481c02c3d500e420301624814030460408210040c0c0922502c915050030000d003004101a038040440144150000121541482046000040802d00501600310854816000143c0e581e541c80711200c03000c1803101d0f0071202c0b58400d201304400201454050001c40b90100e400801e00101040388000c02c040700c00000350002c004803000250455039603034507070203080c42c103c0c021324641c1c0d903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 625016250 1250 625015000 625015003
    0xd110709110a1205060a1e0f031a0105100207030b040314030f01091a0f0904050102040e01090605010201060906141519080a05070206040b0703110904020711030606030304180209040207021011010e 86
    0x544000780d00040a580030400c2c0c518081c1c2d140142901c14500c0c420042d92903d2009203404e650788217a80b03803488e034816045ca4505c440c0c04a8050330f001c8401002e0040c41900080da0b5075010b000041030030310681d010074141030103611886810488880516960b1502d00d0407078255140a01c1004000d070304000b0402801c1366103a02c072404010004e440e071803e000180c400c010f4440c45c00f91082d030701950b0801010900701e101422060103081c56201c04502245850002401c541042d4802d84c4441d24141c410700c031500900c00003000300b5108944084c0355114119803040d15200c0d080307a142841c103101c06240401600410498491001d01108216a81e030300c0d5400c1c0d0300c2d03100490340100b4400442001a0b51140254024a40c01c091324480d1400c100b00d04021030101e07440751009a4404425803840390007071400b0003c2d580d00400541c090340c10245025440c4400e81c1a00d03910341005e1381c0209a021039030300d959050310803860300208440301c0101e11580290580c5412514481c0650810f2100300d0000340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 625017500 1250 625016250 625016261
    0x11d04080a11010b042f041508061302121009050c1206132f0310050d0302070306090320010b130c0c050a060506120c09060d062309011505030d110709110a12 69
    0x15040b2541d5883c130684044a650274010101c036440120380c0800f20700c031030107032010341180d41c1c0304079480d550b5003811510303120804410344c0a0030300359092104001c0c01600c80d0040e10102038040550340d0300e607210180020290b010a0030032036029850310f43c5048001102c00d0303c802c11404e900c07030580c2c00042c04040c40308071440304403034441120306104010400c9017413104400741510b0107031064131101500c0e0741c1e404064802000f0140c00090b00d8100c1040c804009400c48600b0101c1d002c020003070000b4120108204545600300d041042c0d903500e1209141d0360003200300c8410545c1c0b180c169500e004252601400510b000c1d6083c0c0d026154100d610040605d00103511103c41c0001081540300769625801c0210707403568a942203c1180d11003100400145924034175603040c445264841c100307442c1000a80d421980380079088180300058890410540d00c001c2140c0010841c185803404680703021042c102c1c90b0108681c44540d000b840d0000c80d904280340303200948074402595840001030550703801101d05403074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 625018750 1250 625017500 625017509
    0x1209010b040f021201030f030c0804080d0e01020102031506090105070b0a0603030f090303120902041404050a150c05041505040b03331e030705040e0105011d04080a11010b042f04 78
    0x103104d801440803803600b16030417500c20b101e0b140214800d10039035a60780d01c0790016031044c40039a0050003a03400458110900721500c20080c4003c504520f071082400d004054040d45040c000c100014181000d41d11940c00c450003150416810310560400ea0101c000400b4544019400100e40584100707015100d0041c070401ca0742c069503000d03e50080700058400415496500700c3e8480d90b0303080c0c42541510310401061140b1f0281c0042d003003851042c200b094495100e00121001140790203041081d840e00942074034159149154820042d940001007034825110f00c1d00b2107032101502000308502a0010301154200030105204c0c1c0d4414031030386042d0658031802c0c00449034000e00c03401d088404050038001c0207019400c002c080310095030b0b44401060480e01c000000c4004c43c2d458000601c072107080c0c109400d9803282a840078000e54900341d11032140c0c4d4007a082c12802002700421060f80c06075001d41040c206250001d00800c0030418000540c01c50030304051014200382a8183c00345020280042917800300e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 625020000 1250 625018750 625018777
    0x20708190c1509050d03081f050a0308030901090c081e070b03010b0d062105010506100c0b0718060c0b09010905031c1116020a0b030402100c081209010b040f02 70
    0x66080550681820070560100c5040245a000010b80c03075441d586030417a030700c0c0252962012070400d10030041c0c5401454003040341180c0c0c215030070006038848500c948102c0e40c02c07004094607500c503113a410707014081d400c1010b0454176030705e600400c200e0808120440340c070300d4070404650b0b10300070f00c803459865240740d20902c4810b0400b4001040301941e11002450421424400011040c1e1150700000c058036545905a8540c0c500038105020010248500350700580101c0d5448102d4060000051402c4401c070390040001a888020890702ca00686035003642e03116816042e8a01511020300815840c4100c4099070f15820300d8010481140d010301c00d4600310341e04640910314086805010198080000b01500c1c2402c3d0303151040507000043d14064102d0b1301240c0d5214200001c5401006002c2c211900480500041082408016507c0070340004682e106d9040c0328940b0030f403904001049002e00174610b140f00324a50304204031038030198451258424121010002e0118280c404000c9014206c9008d406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 625021250 1250 625020000 625020023
    0x203061906021e0f06090705010215101715090303070e09060a05280f05010f080f01052103070309031b03050a080f0c0304030c03060b061603140d0c02070819 69
    0x101058450b1041c0203c804085940070340c00300b0310351490000100da0400f807542019406002540e0b0610294000311140c408401c001d0401c0480645286c58500c22000004141c0d0055142c1c134905000940801407048001d02c410300d400060162258011100c2100266840408101a2400c0349a4500441000e0002c1503041c1c200000d201030308544025004030f1500341250040c0c00d5a201c06014040c1c00c0c4100c00ca1051860040003424121b451030f1003c040c00100340c10800034189401c0c4190442d081101e1503080302c00d8070035014000043c82c4070b15104500000425006140d040310102c01168860452003644071200035031034840c3c1d5014000203201ea048007002102140c4080003404140c40705204182c60a0a0140c200c1d28680c09507104440d980c6aa030010000d00245120f030449648044c1c9406140c040c04000801d1450000300d002001e11540e00240707945840c09100780c1e010180718810401c091451850040d5480d4111701c1040c00d81c1c0714a1140c0244000100c40c001c0d0f6890b80105420031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 625022500 1250 625021250 625021273
    0x10b09011d06100513180f110313061506170601050a0e12070e090609010f020f071401091e0b06100905210d031406010905011215080d0201020306190602 67
    0x303c00103045262401c010040c071101941d448440600001004016001c03004c83d0320502c03082003030710b04554180c070486141c0406e901700c5501c0c0e0b02c1220f6100e81e502881c80f032445014903040d0010541030120761004050f00d03001250b201c0d04100d0304007601004400e024520390f20305004603800e114100c401000284845030884a9042c9044c0c0f940c100d04442050380c10f11030b00c9031540c01d2500401c81d00349245034000c1081c064141403c0c1b15401084032201d41c25071510441da612090359100d15000140008080c0081d00c0e80280c2c20b5201e1005107601c00c84240303440c1e40b2a08495407400b141a4190703010203142000c075046151100d00da038034100a80d04c0740740d4510b280200b0801040003050101c080da01c261501811090b2007805a49603010094500207210001c01c2441c480d194002016141031146031a0140321340da0f00103200510b2801101c1d00444c1121012003c06040c0c07284d031b031044019216410b1040b20040c2c064001d540b00382001c5c1ca110041d4040e031820310314020a40d10524001da00a1b00e0380301d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 625023750 1250 625022500 625022509
    0x527010e1b03030705060f1602010c0519110f011a0616120507060e03040317090306010306110705030c0106080c0603040804030303050406021c14010603020c070b0a1e02010b09011d06 80
    0x4072549002000d50b8240011034940c281000c2044507110b551407022401c00500350b0020611001c0045244000c00000d100300342d01a085100340031101d07100b0704107003414a4605115051038030076804000305580c000215100e40d14041c112882a20040e009130420381c030240c1c1081d0059640d40f070800711107054110010340718050021104100300b02040020092400456040e0040b05084c641d12001180d4942c0395003014001c007400d11000e00c140100800107120b0070b0340d00146650640f9004000001e4941030440c0e441540d2290210003811404040348040d08050194019022a1003d0098460b172407049001c0119a00c42110000e03e181c0042c841440428466484aa40107100c0c01e001886d100320114415565a52580780e26801c90315002c8680c01074230744603091801404207003015820107103184880c684514030380c040e03201054000320b0301050151007200d203030004281c2ca030302d0100c1c401180800207010304850400580070701911400040c0240c241c000701481c0115035040201c1c075854801c00c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 625025000 1250 625023750 625023793
    0x13170a031d2101021e030a1104180b031e03120c040305070e060418080901091e03110a0f26030906040909061d0a02090a02070209071b060527010e 64
    0x81a0f650a1001607180100040f1300d02e82040d24a0074180c9038a03040c0301032019148144401c000001b001d00c01041014042c1c907030050b04c010081e40110344900320802091505001100c842c40b00001001070150204011004000000c803a039141405c65071034000b001020301c030343c2c4001801c0754080c940c00c1248442d0110b1680d0003100040010800d008980a8440702400305001510032001c001400c0c40c456801904207002042c4d1a030300711200011050109201404600c40030300b03039078240d500c240b0b0300d5a16954048041d010f07584a195003607803501c2c80000f40e003084102c2c130035512004104074003060100009071420010018542850a42000c020b00c028281c0d41324100d9800352680c00001c03848140035480040c010440006000c1c2d94041c1c0100302c81e0050113006920306500c108000000758035480c1c011a4040c00074181341008401c0810200c90f60205040003418045c50502030200c00e01c118a05101329040e42c03c081310340c100e40d007844a070885080c00300c018482c0d480908119900c01c501e8805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 625026250 1250 625025000 625025059
    0x16290105030c28050603070504150f081311060309030301080f070b0417010209030a1101030f0203010e01030303050402061605010c3506061b0105101502060402040213170a031d 77
    0x41c0f2074043e03030fa0000301c0c09039001541d040010507800f01d000e102c4180103100045008c1203500d0041c0081c01040000350600074040d00c0700c000750800700703002d01c2401040401481400b2016220941c1ea00c0d050703150503240d030400e00601c0ea49014600c4198040500000e00509407048541e416250034078116210198001e02d040c84d03c0955000e10403400c0659080c480700f00d4580c0600c0000201c5011180010101c07000500b9020010f40705000500400100c0383e201e9040d203600d0705000401d0b4130b4500000d20b06010760b0b5a4112500d594000582c2008019001580005025103803107800c81c2803c4000607006000480000015428052240b682c102101e040b0350058030150003545801402072502c40c2d908003002c40140c150b9141c009000c01d40039444080401000f488101744d85144507944000c1d00c0c2c4078041c002a100f10740200780c40082c00d40c82c4620708024048824141242c140005c0d105071510001c1c003003980031034041c0d0040304e5440c124a812442200340144121a6940e410101144c210f610404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 625027500 1250 625026250 625026319
    0x1f050607150527010516030917180a08030a0e15031537050d0b190209040519050a05060102150c040b03090f1b060d0216290105030c 58
    0xf121400e6081078200c1c0000c40040d04000b007800c0c600034060750f0510710017152181c1018945800c2101017801c00c1101c030411142d94004580d0303040070041c8030b0500d050214480380d01c11612140050f518500100074828840305407110b6078803400840411100c984c0024641413851400c01c0043c2d40b01c2400c40344116081c100a2000c900440074244001c83c01801c003940e0149400d00c0c03001646401290440103005000845014040040c0b0f03507146060004081e007a560091a03140040490b0086a0181c40800d00080d00c20002131070288207811507200490b00c2c001c01a803405001c510044c0d200e0103503d00c603c4041c2c005002e8418500b00c00f40a5820041c100d030855081840082130030000c9030b005500500d5000c0050001901540ca4142040c08130750300308113900e604031000700d02e603181d1901360703550919401d50046e2a60550726a414010903c2000200188030040d51000c1c508064070042c0340c0200015240c4a03070340e80301d0040c10f80d505038100c801c0e03500070305409610891941004100300c00c0384044a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 625028750 1250 625027500 625027531
    0x250306020c0f0d0306060206102405070512030114012a050a0510050609100f121104051614070809040507050717070212010b0f0415030b1f0506071505 66
    0x2c04074180004660044000380d11032208009041e410040030303420620071103091b0035403031400c40b440809000d68503141004e0084041501201c1e07005034146d990598100c010742d081044000840000c991090261191507086140100030b01c0d40b01d101d11a40c600c00701020000b1048010740500041d00c0105411503461280031134000004200348610406007620503c0031817503041000400215010003042c1032a0a040c0f180d04024021070710541c0700484402040d1104141d4060808410032031011240a801034240014003001396440d800c42040700700b00382e5841c0980c0000481010180c450718001401d00e0301c09020031941c40c50240d00864210406081492415034136a0340d01d136102010300b0002c7c00c2e20070003140600650030144245812140702c00c000b0041703010950000755072409174850385030240c0d6841c040140903900222084010795000285c2c040c0902c0c000b00c9894a0090104105150710941c400008035820074400f6502034590004007040c41c0c0c02c07c00c070208001e11008145541240520 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 625030000 1250 625028750 625028773
    0x338060405060d06080706020d02150c04051009051f02060105091f0303030c0e0607020d030c2301020306040c02010e030a030e0705090c070204140106020a06020f1b030c250306020c 79
    0x910040c0f00300c8441d4200403a5080c03901100505110301c0d030340040d040d03411031902c00605581c00704005400080170401c1c0301c0d507178852500c13110f481c1c000c0d500000d0300f0421001d25545d4994110310390200312038003110007085114880000a18900d00301d018117016038842d038014000e0f85000c400040e44210000029500b051210307000d82c03041081c550040d00403d9035503607002203103680a04801802081910302074070780416540803c0c40c003a0741a20140c1004940c0f41c50341d042010688103d14604c6d00c1049000104040c0c0440074003e500a542c2144501e06d0906070300e65642c018000c03015895031103006903040c407880740000c2c2e01500d03400360085868010590046000d690310480c80c2d00603400c105180c2d49509052041c801141e2180d1034000516024100410441e035001803c80c40055100c0300160725400d0380e410308031590060200181c1d4040c806982e044d14404000050200e551201d4122001100348000400e030f801d41c541080d654080e1910418000b040440e0014421424980115800f02010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 625031250 1250 625030000 625030009
    0x1803040308030108070605091003090f0506100e0105090408090112140a050103030815101214070f08011a0d020a050702031002040f0834150c030338060405 68
    0x30340084805020100051040700000c10480020b4415400c001b0b203041020000508480b022081e140704068582c0c40c8142003040903580d8010351a44603040701c20a040c65161009030743c8503070040e040070481d14000060b00349003500d6618042d50f00303d81564500070415004481c101350070f100e01c2d154103071180000b10003500100c1c1502c1c441c000840001606504500d0000c2121002501c0035120920044458070701e55030307401040505104d6405d010004c111a070158002518405106480243d50b0380308100007290850300f011080d2005070750f41d6441d80c0e207418951360b100c09a5550600004000d0007111a000e999500400480c0c50a0400c0c82c201002640024035002d040069000c0b45500403e003000b04c0030007000403002904d44038003d810140c40d07214455185202200b240c40004802000c0070040d01c94642000000d0702007803070713401140304d071500e8041c0017185400c104500003464160001180086690302c00b2010a80469000308401da0510034503001c40c04020155210101704000180c6a64 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 625032500 1250 625031250 625031257
    0x5161103041e06080109020a0f08061801030b0717010e28020a03270803130c080303010b0a0f080402100c0c080708010b03060109090206030112030507060c030e010e1c081803 76
    0x7994200c2c00c2c2c801d0f080910041c92030b58180e0201010070b0050103c0044640c000d00114021007491908818035518038000494003000c207010390b080704820a0010050040c00b100341ca214641580394100050a65403103e001102c0074818640d4213150300e0003144000c100b56013045668410030502400070807003018201e049038018541900403175520180074882800c0c41c00722254280300c030110400006241e484800440c800141030031280c0600201c0c01080086240b407100240035180c0031241c4961f1aa01c440702035038007690180c808241d50b501c600c00410700ca1011f461080764003608043e00c144140d041a0f907502d03201d19003200d0044d04118003040e161000c002000007011100d002040c10710211040c1030503e030043e000103896504261840b00980ca030300c000c80303045501002520701d202d50281000c840901807160700400030740c1084109402558036810413149244100002c014500c038512910b651000580b071416404070001c820545014000c004003644980380c2c00702640c40100c0888041d00759130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 625033750 1250 625032500 625032539
    0xa020a02091311040c05041404020706020406090f08060106050f18041e060e060f2e03060306141b0a0c1209030308100b0f030402010e12010507020d030516110304 71
    0x20003450a41050005a80b030094030441c041d13404010041d11444001c0c007500c00d5004005008a034081c01d000702c0d4445070304985506420400071500c0310b407070340d200802101d003c0c070032500864028100482c0e080000f2845504030307a469103400d4508652841c0241183c2c00c43c009546860100701c0040d460340c3c0311b42c012114544101b25112040c070780030307e5541c1d00320741e265088100701024200403c402c0e07840c0c815151214150031143d5035812024110203020800480900e40d03030440060b0034461b1601c1c1c00d500540203403885401d0601c1300c201007040a00100304200d501001154259800c1c144850881c002403e01548a01e00b02074417802e240c8a2201d4502802c2241c1d000505080003001416031200c0110303040f03100704aa480d6214588401e125240c00360643d51420350000001041c00c5a01442e4089281d9001505203440b9400d03079420940203081c03ca40c030a0250107075608000c4101c2c464840c452145415802c1c54038009080310341141d2402084104211740d00c420040406c0b1031544565105111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 625035000 1250 625033750 625033771
    0x915050406020c0d05182202040f090b030a020d080f040e0f04020111060c09060d420605030a0e0703140105011406070f03080601180801091a19020a020a0209 69
    0x1070070400c50051901041c0034214017005030621031208620310b81d0f844a003038104104c900d00503500c440389401e041410314504079408140b0004000500347c01d288040c100b190b1000c00e00700400313105582032540319030142d24003d511420511740340000501d5200649550540321103410304298852403803040303021094510b069a411f0544c2000219a40045103940d1003100c20060141400d2007844803446010700d0b91102d100d02008074000b882500d40d175004814948005052440c40d0742000c2d103510301011001d01c041c607240f02d074450751a5000c0e440b1541d07104031000c6a966a1540e0754403d064001001d201c024502c0c1402405400030200f040c1c8410b4803030030000040001455454210f052100030000e220150203034005201c007001050300544d140e01c966030141007001705542e4241c0120341c0c0202c2c2e02c512030603920081c500842e034404154007001d10036100300c101400c14010307012030f42d40303040741103e082c40c024400c6526094680e400f6009010444000d00440380300081a90003d02c2c09041100c0d1800c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 625036250 1250 625035000 625035007
    0xd05120a150f03060f0e0102040807030f0203030d110901030c0e06090103021c02030c0c0d1d010804170c01060311040605031903030f05011706070c0b070c030e090705030708010f0b0904091505040602 87
    0x1760b101d18421810b842030a50300840c070740342c9861b01031a00c4004500c0b003c0c0c01204190452010740d1028000c03103c0500d11074034208204100f40610020a402010000340040d00d072207500310b101030056000c6603502c003004000c0d41c100700c40c24004402a50102140e44510105915107010040d458000346005540301c0102681b180b00c0c0c00c130b600d8034000340000c2c1c000030400748440307040031083c1042c440c202c0e442c02071034800010354990501110a058010725132001c4040080d44031041c2e00190f00400035244660000003150701d580b01080140c0d200c5010341507154010b2080c0008518140c007581207004d110782004212030f1701403c0c05000311a0700b68400510800d640364848240c60b401d02c20294004a68100f001070780001d0303200c0c103130002c90041003030050000021220043c903000d05818100044010400e1b042c901d0400030050003504142c0d0101c0104504500100d540d083c104444010f54180c03410041c18080800100700107003581004c01d0318540c0d0040d5000007220840d01800344218003c0701c0c0580e8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 625037500 1250 625036250 625036271
    0x10305120708221a0f030403082d0a2d05180a0f02040f0218060c10180c0819060507031b0207231e030319030504050d05120a150f0306 59
    0xb0011150384006445502c1000004017891000c8207598105030149040304031503490320080402c4a1022440d04107203058031110094415024904a11400380d900080c003000083e000000c0d45140244141a61700508500c1c20940c0c451962000340e2140390308818149008003040d40a05241c2500001d031121030080640341d05605040c05a42e02010f02c0410841c0750846440315546602c0d1301d210068407914000542c100c045804010240c00070081030f0703082100111041d020003103040b4900341150389201c0c03280c00040800d000300740f009044002074022940c2d0311103541c80c100207140080003441131507035440f041c21010358072218031002c141490b0020480142030010002031b107600c1184a400038a80400090070545414507443d00d91a018480000b00d08144030009080d8000c100040380b00020202034001000d50503080607000d580584182c90303680c1d0740315608840500c05c41820b503407060080f1012070758000050740003204203203c000c08442e28075194a0114680f4074035510903580681c85640340d40c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 625038750 1250 625037500 625037519
    0x1023061917190c1b06112205031209031203100b120406050108010c0c020904020a030b0c04061413030f0212060a060e100302100807050409021b0c030601030512070822 73
    0x24070300c1c0c005044c00350340c2d0f1066040803071441c80b08590003000306032901420100d00b103070141610408180c11071003114807400080c2040142c0c07038500c1502d2280c841c450385800140c0441d000c641300383c04060041c00c0c102d060f09070582c1c05a800079002d605406840c0000281e003900e00c002078607038800070f001c01c41ca0038201420880140e90301170f0808001649015132240f00c49402ca108002e0701035040d60404095940c9000181c41c0109580c03014290416034000c02ca40c41520300001c20550308643c0320b4141303001c0a041d40007801d000c0e600700400ca40f400d000c82071011410b403c5200c55214130003803240c400f51203e855200e0a244060300e106400b40c0d00e070302041c04039042c080e400592081c40d150524140b0742c650340014005000d40010302d0b0a1114a070007103900030f40300348111401740081034020340d80c030120149480781e1002040140c0390725000d00255820340f8900030410604882d0000000c01d000c0300c844564a207541c2c0311070030450f034140c010040d0103403e81d00108040601400c8502e04905245072038003c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 625040000 1250 625038750 625038761
    0x30c0a0818011d191701020405010809010c090909050109060905030405041d120307180602151509010302360603060c0703080c0904060e102306191719 66
    0x210306210342c4520510384420f440d251400010310441c3d0700443c6019016070032110804503001a80341d2001c181030361803114815002081203420a0b40c4891040d520780c1e880c50308848285090400142c00c850003089000c0740ca400043c412400f400000412185a80e2135108440c11110101d4046e04003040401042c6801d214416411902c0300ea48026040c03440104d90302d03122440b1403000b0584010011841039442046142d06031407280c407a514006403030f00c40182d90b03120b00000d0020100d004400085410f100d07103021350401c0c20050298281d0341d09550801603030101c404601c01e20528824202105a0003030002c2c0f105d096031071402700425007002002e050a10f4801004001307046030800c031040001b9170000071950312001c6000d0864450015400040c00342035950b2007200340d5021403092001e44c5411071048400c072404d104003240080e01240c02030340091143c4d20660361100c82030000c0608252410300c00c0b803106481380b408072a0011803880c010003d0b0820b642c400c0d4820070411080d01500300503c00c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 625041250 1250 625040000 625040047
    0x2042003070903140c030c09100e0408070b01060e030307030e060f1b0106060c0803390306190f0b0702150f0301031713140310020307050702040f200c030c0a08 70
    0x1c2c0c02e440c141240481d40e241f400004050280d1240c00c00150a5608140340d80b0203010044403145180c04c10f418006102d812108069071901000800091158060640d403030954201601450510b040ca0b1402d4548240882505400c040104240703c000700710400244030340f0020720f00403100380201c0b20481e400c550a07904110f040c41120f88000f00812180e00a030390f840016184040f0950081141403807a40100c24071413043c0c00300c410701000f500b00006002c1c2d80304050a4400281101e8039803000d8440e02030070302c5041204c0480d00d5041c48a0401c0d10002c14007980080d1401c0e50603042d2081030a480e602c1606890320024010006000304403d0140c021800f0010451660410001950a04100030340388600303031a4411050091601da04c0a00c00614100d03030990f002c64072440c080030003500b103501c42c0004900c51072900084c2c8070810074a2050306081c01010b4401c01640003002466510340c1d00c5000e0f9034400b888140310140d1080320411101c80d1151054094039154120920389406860b41e2180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 625042500 1250 625041250 625041253
    0x80d0504090f02131511120a0215010b18010c0f03080106020d08220f020d03020618030c0d11030f03100603050f150f180f04032a0204200307090314 65
    0x4c0c2900b0300c10702016208268840a00c603100c6250a8884621781001c00e0074038042c0904032944c1050240c0900b0765403a8640950707250a0b9103d0031001c152500740500443c40390f0522000c1c0138508070164a2034024018101941c2101c5107496101603070325001400c5001402c094014402c0b1541403007411145100381c00c18000e103003080c80b0191054083c9108009000010301070803c14045040040700d9031301d070040c0031091a83c4040c24000e440d07100450b0842c0107011001e100403180710001044440b410000b501030200500440c40450300a4031900c403114140c0310902504640841400095001d6030f1840c11000d607651524078003606441d001441c0c4800c0440300001c210400e00300741401480c00380110351403402d1030580000183c0940300c09000c010080d022a0401c14a105004e46450156000340c544080069054481f21907044007500002c202140d051086001410250400b039100b9418a2508844241105102480381c0007181c0040028024500800c2480846d004d0006030a0380f080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 625043750 1250 625042500 625042507
    0x10c02151311010e2808031c1d0d020f1b0904020904020406120803010e090f0a030e060f0a020d0930020402070611070b13020d0b040c080d0504090f02 66
    0x40210000c4562aa0090b240150001d40d1106a0380724500f161881c400082800d010902c90041074600e4188484031384040e4921000d001c5048800041514070000e0b040460040aa10040e40c840207084459550322228140e90303501001c0342010300c05213007401143d500030b042080c40205510f1400c1d04151074a001060301b1030000006480704130303405a0168041c1c460b2206a1158804030340186040e07480982100d40d041003550812025200540c1210040e074120807481d1509002c16840c3c3c0786105d2964460707031040c1244000680142c641120511b0700070407143c00e20150074490400346d03001c0000e600040e003003288283e41140e004000840600034a160350503410701502e440c8035034002e0305103990301403100c0301c00c5540071942d444d0120380300306034401402d01404042daa040c80854010a40440d58280b0080004003008440455403031141d4000305042e00c1441d080e2102c042c0c07100c000d882070350b41c03403000c90012510310303410001c004150302541c1d201580d4a103402d50070340c2100ca049107443e11103070041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 625045000 1250 625043750 625043761
    0x903070605010f0501080708102d09180209090c130c0f03050906071209021305060111030307020a0b09030c07030c18110414061201180c0507031706010e06030405010c0215 75
    0x100c882e9902c10034231304254240b5110b024002100c0d000030340c004019000c218040f55482003041c01032000070a000d00e40382c540070784c40d04c04000c25200048020140d0704804503000025180010186800c442c410054454903030520300410300b03041d10b02c00c00d41040c0b900d5083c1c1080c0e82d94084000c40c0faa100074039003080075040444085440d071a0152101007080611a0f8624510520fa4440307018150f00819812006416610300c0340601411505503000c00c0b064000060000004401c80f417040c000340c2d01a00b042d1040355101e145408018044038020311061113100410442006400c0c05180240d0f4140075244c41c080448201541c00c02e0110003050504d003a003a50404000240e505031158880400e00e24106800411094061909541d100070722802c00000d070b00c103101c0c030400044094039005108d05042d4020aa50710b100b00e100003400180c041000081c030580010312103801c4041454002419003d9000083c0c0c40e030000c0e541a141a5596075485c0c540b640c042065880900c6e01004440607440c20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 625046250 1250 625045000 625045007
    0x306110405180601020a062301031a01080d05030c030a290906010c020a2607060c060b06030402030d11190b16020d0206070c0516090903090501031a0609030c090903070605010f0501 79
    0x103005001988800c12066050030052280d030084040c8042c1448e19030f0745e41081c5040d021030a0701c41b00b11980700d400120b801a000f00301042e035030728113441e040d15503220b040050016070b20081500300310a0343d41c489201c0c0302401000d42d039402007007581d00c4090f9012680410112000141c255810b12034000300d1200103031540003030101103500d51012156040f001c0904401c020203c850f095680e8054048040f4019801c543d0340c203e880d010341010407021803660180601c82c401510701a605a200540560800c1d03c01c504201200998101340d50342028401d80100d240540304000b120020303c2d84041058004036809444090112803004080d4201d440f0406526010302901041c10010880e81d0700c0c013441002c024030600002c0030315034003100555451081d802040b0841c0c0c101c00207480030100281ca036100f80600704002c0c02c03480a04540c5c0504100300320340caa00c134151440c0c050113200380b039049030743c1d07100d4415105d0030340c2a02440d03603034509103404000c485050b044607240141d600790038400e90f60b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 625047500 1250 625046250 625046263
    0x4050601090812250f11040903050409050406090210020c010e030a12080c121e0a060b042706030b180f06040803090f070609060e040614010e0604030611040518060102 73
    0x198188040e589051001810140003000d40312201c01340c500d6090541001840010200558021901000701340600300c108429151003d4011780040c90030f000c2403180f00c0d507940c06583c10a200f45000030728038606c1d5000c0b40098240103082405170700090483d03d202d5800030700c001c064540442c0580b460303286c0c82c0e0301e21400607001c044820800680303400052611000e0300894201f1680c621030f02099284c01c44090070850b039011054641003c084c3c02050800d5414001d05058030340d6080403e003000d06042001504500b00d041609000454010040b0310654a10400c00a940145c8161340b40c0e250030780041707481c2c0d2805692204540c0c0003840301c1c1003013000030a026070080e50200500d1741d2a01c031042c010b460002490021066030090f94000039410390800c044004032007180e103505000e0300c10784003004100c5110348104e8410240710390041002d0362160092500180000380350a003441c0d166100c0c2e03001c1300c104107a0744100e20000a4280642c1c64040b8003005403803440480580d42d8503061000035150507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 625048750 1250 625047500 625047523
    0x3050c07060e101d10020a05040f24031a010e1516061532130b0f0a0b040b2a010906060b091f090b12010504050115020a140106180209040506010908 65
    0x40c6c1c081034003080c1c144aa000c0f07c000b0540c50303006442050f10340405003d48850504c964540140c4c0f04050364045000303014400d0514140d80b4070814807010f090066a036000e085207800d074000200c160a403420404031000d0b0000c40c2c081d45455a20f060145005030031502c5901c02800f1844441004100310850440030030604004540050300c1d80312080d0007a0000c5543c46c0d20300c2e6001d074188122401ca40110341c018014104205c605005801525040c054a620746e40655040c0420802c400d000b5981100c004050707000b01e0030400c28902e00d2440001c90f40c49001e40c8200d0312a512036040e00300b0f2088134051040134040034500c0529005018000403014440308051170200e84c0140780407441c00b40039080050080080c07000466990b002405110a000c8090080a108501e0000040b402c9180d001c49095004015002002048199100c0c03072020444018991581e6484040c00f0403840d0721589425009000c6040150700d44560400300402c3d9000100f580c0d0400051040c10404140002501d503581c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 625050000 1250 625048750 625048783
    0xf020909060f01150e06030103050c04051602031b0c0a0f09150e0103030c0309030203010c1817030702210a0311010b030f03220504230a110a03050c07060e101d 70
    0x1d44c841131042d0b8640e490400c00a51040c80400008203000000c12001444c080c03c450801040c1e0301c04a00c50030243d900f511285c01a40240411440d04c4800480346218442c2c03501100d090904010005400304034541004d59141d000742010881e104040c01800e000b00340311503503131200c14104071200411800c14403020f010410101012810f141c0540d08400180d40c000d4020300c00358190b0075015003400184c44409298840c20100058207044000181c55118400d0b40a91300d0302c0b480f602081107007040a124060600010200d040300e04008100c04050b5a01c240c9485c000040700701d010358211000300349070724007c3d0040960801c841344088121000c1d0f818000c40c0003008020000d41003c141001d403c02c5800514107807189520a0000340d0000c40000c861910382c006a680d20101000e40c0d0742c001e69001d00100500448004074066000141d021014035074481c04c1270b4050b200d44040d51841e40c03020102d40c00c01d9074a014228a1401031613080b80c1d0300b54020203000c080c900e51a948401070b4590b641c1c035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 625051250 1250 625050000 625050029
    0x90c1713080f1306050c120304120c050f0105041b0806100611031b010207120903080d1a19030201020609032b0207080c06060307092a18030f020909060f01 68
    0x303042c562420b40340c440e1590000101039039196030014095031300001c0507403007070b2003846c1858101070a0b6008903880303190311414800803c20520000e030791724040c0c0d000444060242060b100d410410920030948903030700425074007442c2d1400b02d21b2a50b1500760b1b500506400d4000c1d5040054074229405110100c5030189803080c0e100340c2c8d106446046005107000c0d90000c020041440e1036400054000c1d00215000301d40d8202200f4502506513802c10551000071b005420a100980210030907a01c84001d415103805841081450000092001900743c8000c82d03101000b10424029035904211035680645100002d5190440c10203608004045e820b1070f04100e046001841aa04c2c2d0081d019582004e900c45800c80e112a05101d0594440310110f138610701a02c00c0d00400554030120313002c0d00d030449000220303d21701c0d8081e45130819949040201c40a05000d02c1c407000c0e10507107100c40d54810003940902c9511894240070300c1080083ca0001d40301e100144e2101042c040d4081c403000b00c00e411a011014803041c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 625052500 1250 625051250 625051267
    0x607080c040f0b0702090f071209030909060b12090f100b040e0f070e060409202b02040e01271e0c060305070c030206190e07090c171308 60
    0x35120316040030a16404400d030014001c500c003009450304030b2007218100b4060303031510b0342c40f02c4502c0304131464800a1070f0741082600300d920390723030044111070300070300d0a035502c0f640f0382115405803509507202c0781c2c1800001816030503c58850418980110081010380411a8600390b0070b561441c291401c0540e999545003181c00329a503039403107250092041010b42e81c602c0d86030b42d07200703449181c1c601c9100901c0c140c52002440c14a0300d4482c8080ea030b0780c40b070508100540004039400c007032200321b401c0d140c002c001e58407120200c100c100b0009012411001e540030491105105103c00c1d20080010001581e04104450f503e4207200079084082400d00409564101c50b28184102124400b10443c403420680c5880d50040c4000012202c044d907440b514140703c140c5460100301d482d02203d440c054010780003030010a4402d01c1054403d5040b4204e2070010541c00c0440c5050341c1488403580c48040396654030200142c100b41c000c3c0c0181901d24105212031214641700c2501c2c00c191601030f4006200313100001d032004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 625053750 1250 625052500 625052521
    0xf050711012a0e06070605071e020a020907050304050f070906080d0c0b01030602210c03101403070b0c0f01020c0604050d090e0f0601050c011a190b19020304170610050f03060708 78
    0x85170300380c0250041c04141814134022704210380300ca01c8404000ea0074401d492102d1300000f0768041d42640a82040141e5544103411109500094801c581c28000c2d0088402102001c002d024081c1c890480c0001e407032480e1090305407a200d01546410280301142043c180854807020072941100d0304000c1c09aa96013045aa0301d44100354484510350400c001418006030304080e60155101c0e5480700c102103010703038640300030f132017041a085180c0d40e1550146800740b10b90fa2032100901070544405041702c0b0585840b1907034609a030800c08400c405a03000e481000103100007000f01c0c900250150030144840e90801c9400540c80350014003140c0360784040c40200b0200d03446842201d68940c50301000304401161304024408a20324a505035110b820010203c6452190300c02e00c4504848400c1003140c680051490002601140004400309601007400000740040c17502c0e0b11a804600d0003030181c40380c0d20b00f80030840c05015154104500030320300079001160b0ba403000192140c0000301d50400c0c1040d035880e00b4041c0e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 625055000 1250 625053750 625053757
    0x10b0a030204111e07060c0c0f031d12031801090f060311120c03100503010221042112061d0c070c0306180204110c0a02090a0f050711012a0e06 63
    0x183c48400700301090310300c03218a00140031817502c2843e06100075407040d8800c6030403031710f0140f01402d241c40501d00d043c0001d00a41070041da8904910002001000701c40001c0c45120407070300c0780049600000750514541e490a0400001c5280900300a295181443c2d40e001c0c95a90f50301802040c5652040c003c08004442816641841401080000c1c640b03007203014105590000d80c0c640c641c40250880124081c44c06000f620454240c1d42c1c1900900040b9a030701446c5400041c1054030001d8403c5c0c4914140c440c0700c00800071780440c0d6100e4900350445c01425204962180d400002d42105400074208002011140142c01261840110341c9908031402d000040411951004040070704d0b2001d40ea04180060009180031402141c0c1044003400701da042c20814825401d21003450381001c1c0c5204010f00d014129960448510200021040c0350105010111941665100c011a1030101002c4009609016007150700110101c00c00b00c1e4100c400305441c180e01c424070641e040c400806504811a120103041c2c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 625056250 1250 625055000 625055017
    0x6080c03100506030c0d05090a020f040f02161217040302030406030f0e010e0d12050c042714010e06190e09010906061202040e0303010605030f07030e0d020d020d02010b0a03020411 79
    0x6055490619256410056101b4400301c500c1d54200000540110004208151103c1c0c02618813940765501004001c010484142d0007407a0035802d0100210810344400301441d00c078420480c90300390341c250a10142004500041c41d080c010951003c100000742d002c01030f1000c4a0303180c100451520324110100b0090710968064108a41c40e01c0c2e40b40e180640c001500740c8203202e4503201c81180c1c01100c20b12509071349040703664100120080000300300484000e0207000950b507081d20405820160310480405460040b40080e02d41280d01c801845150356258101740c000030100d5003141b40213040403030312a00403554031440030b14030007201c00900000c0382074120300c0c80340e6030051042010986461694102c0352034008241c1c001d601d02070003088402800012281070311503035240d1609503a944110355124960080c0726008058803119503e584040800a107402c80b0100c0c0c010308500038035034038001c0c60400000c03a40c008680c1000d000072401d89071032030b5507400d0300d4059a0100725000000381c115114851041c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 625057500 1250 625056250 625056259
    0xb040501051f06090b0c1509160905071b02120d09090f020a021f061511010f29030a0503040605210402180a1b0e13050106080c031005 59
    0x40008224040d84020310032050880d0500c28405403009404116203180207450100380300c51070030b000d009190030182c10102042c10849205074a03084c070300815800c090b525800c40e540441a071141c50a040c250110142c0b41d1007000300f01ca03142400005080c9400b00e01d03000307a0a03d40410140540d114050003030b1505001c1400c032080703281a0100141025482d01c0b81c994041c0c58900c40c03000b64403042c0202e0355028159401020040111600e4003100c440e241002460740f580c0340c0b00015600140d860240303400b0704a4480780c1069404144550941c0e84031103900d0345841c94103d106e6801410000030320342c40d0f40e0030b4004502403050100820301e08054004003600521000c0340001724290300c54000d0900c003951190551040714064040040613005840082d4801e00e44c00419105240c02100c00380d0010a0410108a20441502001c44031603612103200000d002110701c8405801c0201085000a4071580e00f0062507242010051080c0c6015202c48170440e000804501c8507801d48480e18003a200041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 625058750 1250 625057500 625057523
    0xc060914030a090512060709031e02030a03111005010305030a030b030309040f0b030d020d02100b21010506190b030402090903130b030117030a0207090209010c0b010906090506030f0d0309020a03 85
    0x30300103407560f4428420a4031030440c021005031801408143e29028140f203480b03249a180c01d5643c1c4054000040601032200f5038298070210269404202c80402e10b0f000341c5070584100100d10b00c507428049240302c0c450905e8101001040000c0e0b00104035140c4420504e0001000c4034600002800c43c86030b0340146d50b02c2420900c421958002c2d0383e0000c90023180850448001e40c0c00f420f8140c0e10362080741c11440250300b240d91001151a800e4000410341080200341041040002c03c0070081d41c91070a041e504582e5588041007020309050544400e104000385058503158a050074200c80d034400180001d0040200c0d20229013000410016550410741d00140b100c002612500e6a0200340c000744144155000060102526800044101d46403e00d895000d043c0c40c50418180e0f10107580070408090401000c1c09196000c01d11000802d030280824110100720340346044101d07010340f00c0243c10944a50028464900a0540020503080040c201c0c140410504450700000c0d12403101544058113240c80d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 625060000 1250 625058750 625058767
    0x312090b030f0105030106061d1e041506020601080109050303060402211302041a0f010c141e0d02070b1e0d020c16080111040504020315060f04030b01080606010c06091403 75
    0x10300a0364143c801c117a000304202c5a480c0c00845580d0705505a401401203080302441c483d04200c08441c1d10501441d0780b00c040c50ba1a0f4000c241100c030480c91103802185820300501903168148212401007442c40002d0003800d6031510340c251648005458284215400103d1031800c00324656800c80c40d605550250701749281c00d8104e030b0700c000c0c0c0c1d94070100d1040f0301e01060b41c2d41e031a1440381421590380d0041c0019072803030000c50055418180c08401519000e0010280c40d440b00420441035006d00240081400c00040c001280c5280c111011f45100642d003100d8011f0240d2a244010b882500d81cac11000700a8000c070710048606248150401422444d0000800b40494540065409208c4802212802c0301c26601c4075282d0803103580d490702c10362040c0104410026460a41c01035900318240c8a44030300034a0781c0d40005121079114080b00c40c50f0510205042040c850080c810a00500100c00503226618049000034440c03241da03d0014030250b56401328105106120813611800014407088907a01c1000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 625061250 1250 625060000 625060021
    0x2011a37050a0b0403050114160e13020a170612031e190503011418150f0d140709060503100f020c010f0b130b030618151311060a090312090b03 63
    0x9801705584641c00c0c080905103400803904014482d80303221140e1400000c102508840c003400340d09a02d40d1044211101411380c006c60b200034001015643c070b40c100c3d250f0044012040d12140106010320a90601000c09030811002c002c4620319201d880403200b11000400d084030f007070b0141d03500340c011503240d02d120002d0042c5c1000042d0f050381c80c44001c010445d0603240410002100d00d00d1051208000c00707000ca00209144040181d1041c001064010011b49102c04100919000b610640c0c2c0440c0c21040035440220600451016000064050001500313250110741d9800072210710180c0d2650b2010465440c1009074141d0710706000d0480284400c1d59240c00a0000c3c0802c0c9004038421f00926000420b207106900c03900300d40000103001780c8419643d00c0390718008106994219034550003025040700c09580007482e0148101d10954418106202d0360500c6400c1c01c0444c041280034030300030070594882c40c0e0085654802c80754007644a80301c078041214110b55804c060341c08010090804414040c80504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 625062500 1250 625061250 625061257
    0x5040f05160e061c1730090d0813020103021c1a010207080a0b090309030703082101031a0702120d2007031b020a031202011a37050a0b 59
    0xc90000728070b141d1140300c10081c00c0f030312000e51140280b40d0200c8142c00200914058210b0700394142180d400c2074081c10951602078a03001006403000035409200305407881d144201e81d00b240b50800103000310224450040d20381c89024101c02c642c2c00002500310304580c4a901210020103106586820415440580030040c00c503003405005440d070400d1180710f0079480041c00340100d80b0400c0c014007480c3d004c1d448001c2d04240c040c0120455002c00c100801c4503440030003141009601c00c3c051141da070002900c1501e050380c202e00c0700d1481d1100400041003c40c2e410100c032280642c48000039210764030340c0c0e20207a2501310344030700740508400081022140300c0b54650043d40080360f00c5007036114041001100c2c141070301c01c024005011906155080034501c03c0f80c100c2c0c0300d209102502c40c04c0c0786a281d071688094140d50300030032001070791180d0041c2268a05c2007030010400c0000e50350700c000c40b8031020703013440354038490213600ea03002e0718110742642200021483c0740003c08014001c560007580359a05401c0b20b50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 625063750 1250 625062500 625062509
    0x603130f0f140f060c2203050304030c0303090b120106030e0a060507020d141612020a02040f1e0b031b0a030803010f1a0309030706090221030910021b010305040f0516 73
    0x81a540f00100140441c0441c880d03140701352002d1801c04443c607280e685e00e1a072004545482140c41010000907400c01c0240302071070240010510103032039032a00401000385170f044003901140a000802c400c8417048400c07810340c0d60038280441c810142c140400d160400030003002c1c00302e506003820b1010154010074103501e00450384c0da6013150340c001900d2124940c072801c007070307215403800102d00c82011410300010a4005045841aa44c0010141c1c0000703043da4403410010b103110f65140c00c030351a490b4100207202c2c00c2c240300071428003030b248001c0d0009840c0c503400c2c035030802c202c10345114204056840e421000003540d84403c0e4251a561207a03601c1e030240440b8090840540b1600300448140b1890400340c84c071450a0400840c07070040c20340e4814014058501c4100d80040580d070824a000c0490392030030700380703101c048000c5031100e28020400c2911070181190748295040f216805002d10152040c000d0344820a080102d19501ca41c90034022040c1001405000c600410300c5071041400c1640b40d040840c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 625065000 1250 625063750 625063753
    0x180c0f0c032718050f060d081306020714100801030b06041d0d03052a0a090b07030e0a062127060609060b030f042a03030305060406060c020603130f0f14 67
    0x10140032145100302e82069030080d0b4841000c0f0001409860700a1460016511030f0f050300c0e013462271041c11500c1c1d03200c40b5080480940c000340c5e4140040c055083e00e20105000440c0c143d456441c004402401c016010b00018207610070030400a6100d44442c2c001c12206888000300310101c513034a001090f01c0e040100300e2280003a060102064901956242c031140c140800080761002d00758120051545038813010190050014103640080c03c0740030704004c2e1041c00d0094680c6d626034030f40c131403c000f443c41c500d2708000c00344840c1c022100e504e02ca6241204031a4542d503030000410f081d401940e01807400901e5510001c005c0c8215488080201d660841022280b400c0000c0c00072580717600180300540004c548038981140c14100217804258113200d109120b0041d07102001c04807540c40650400401150070075804030ba103d5060040300c0c01d00b071189000074072007072606004140301d1782d0020748a4440504220311001e9004017140031701030428968100e240e444074000050b900707140350103d14521003c141c0c0c0e845 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 625066250 1250 625065000 625065029
    0x40503030c030319050603060c03040c150f0201200f180d14010b09132003060703091106090a0302190b070605041101020f07050d1a0106020304180c0f0c0327 69
    0x1500d01318002d00d809008018050b10080d642c43c600c1d196550002481544c2a21680a00051191010805c24440445a030398080c00c40700b0050040c1c00d65800301300c584c9071540f2402c101500c2080e01000d170b80a03105c0e2107a445a070fa5000c140040c1c3c07900b4a08094035480510134414508006440300c00189072001c0900038003100c01d03844100044844125204880c803180e81d1040400078456240c02400b13186060f200c1c2000f801280c0110b482c3ca00100e0311074020030b42c1c944140742407200381c50200e01240030032203038586880c0030100445d40c45442840001e000c0e42044071002c2480040c40074510190820300645c0740c84078450b080400140ac01981c080d1000390071140c10540700c1d440843c5443c2400808402000428507000a0041c014544042134440080e0078401e440c449140380110750080107a60f00035a125400c207040792280721059910411028a0172044c5a0196080101c20044000b2070518800c0c1000078181039800903c82c10f014045444e00080108940c040d929110701551441c2016004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 625067500 1250 625066250 625066291
    0x30a0e0f01060f05011101140f060118050a05060a1704060b0141090904110102010b0604180c111507031a03030304060f0902030f0d180311010f05040503030c0303 71
    0xc80b140d9003d0203416626500e0b00340b010b54020385040c1e5010703410400000f402d2110100c0020a06410341d103082600d41d04d6005e1112075a407210350b0758190202110503250b00c81c40c00d0000768010940c0d1041c04e020f607001140101140b0301030055a8003260f00c00602140b5480c007850440005e1080004c064045690108140b82c26411101c002c1380e0b01c2016225100c0340d1140c0b0100b030210390480204001d82d54000c010080494582e4141039001d40c1c801c44450100c1c800782000a030035200880c00980c002c00d000d100810040b0118143c82202c50b0090303800040c101400c41d01210080e240110000702849408038100480340c1e610803103407140915a804101d0601c01003140410b00102120150b8035500c10b01c081000724030254014414030243d6540010200055404281845c1013001d81018582100103100340564204003c00540c030f40101420a40030b0940d035440c446c02e105402480e041150501c144481d1a01500444001d03080041c200e9031100784813003905a9960046409141d0b40e0103401c582e10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 625068750 1250 625067500 625067503
    0xf09050f10050c2a0c030706050408060c03041a070c02090c0c100e0a030518120a0c12020a060315090e030a020705030f0c011b0206030103030503011d040c0b0703090803030a0e0f 78
    0x207140e08000740c1007403c01000700d4405000b200000404c60414007a041810744280c0d0104034010061a40e074039440c0c2c40314a404082400d00c00e00809202e100d1108104002c0058041502390401b9080150450302d252240c0000b181d40c0110200000d4001e100e43d0203000da80d10201000d403001e505010f08035142e000c2c58504000540342010848606580600d540b072000038090009851480340f403207124800d00007007000250088200d11030004c0c0a8210354440800d014903140d801000d00001c04400c064107a2603404118414600d02c554400c2503641c4060390310700e1a4806011008010216013840f011542c440c8031901d9900109503a4003510400c200010142004501304030000e005201402c0300411180040d14100580c05030072300d0300340b840510100140d903940081e5018602980c0e03039989a60502e211420311642e8040c00800d640362003020440026a0040c10000303840f08107070059211885454141c86036840c83e0068400c80c0404010800351035103c1d400002c1c1c803214103045400800d512040517 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 625070000 1250 625068750 625068757
    0x90c0e04050d301b090314031305060f0d0c020c030f150f130f150507081b0a030f0227120706050a20010c0815090402040f09050f10050c 60
    0x9120b25144400b60040a9000a25858101c2c140301d0340401c1d4030034450720b50f601358240c064401001c2040d40b0402c0c404d0103c012100f210050440300250720344020b2000004003c00f842c440c452141000003902e15502d0b04a805031010803014610038030001040c85030180d1109101d500742c50082c400e060000140e960006001c03144008039400594080d111118039061074600141403600b80c1502c800702d42c0000700c0c062100401039005118104c140301c030451840090780d00c0a0009005c03c10742c83d041c401144030140c189203130411b160003100e40e604138040041d40684220317081c86012501c08201c1b0b000c841040c14000030006100358a082843c01600100204208908408861580030850a00038240078100608590901e800e00c04902c9048500c02c00030f0b04a566110666039440d00079030546036404c80e030f0341500b01c082c805441508145100224541c2c000040020f0f00c11915507071a0245580d165016030b00300e94101e41620044842c2100a5507100c400e101040301c8107181000240411242c2d1302070303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 625071250 1250 625070000 625070027
    0xd11040504052a0f0d020310050306040b16030b061b01200903010e01111204080712021b06191409060403030507050c04050f0705092101091a06030a02010c06090c0e04050d 75
    0x4d1820410308452650085d04010a00607200d0310510001c140b59a0030400d00340706034402c884001d0f41c3d00c1e1001111100c00e601c180788030207060030098520407542c0d412040d41c0e090216407882060101002404901500b42000704e041e40440c0030001005c0150801c00602000209074002d0107074240001d1414225007420b0103112101109000014508111140c0c068005001d60100c2c0d007800d600b41c40d00d01c00013900c400e0304000b61b48180c00032801da440e41e030034070390442078111641070810540f103c0a0ba140e264104130401044080715262003105504c9007030380d68a00001c0d003c01c2d221926860060201d40c030480742941c0324030501b5090b4080349440e0003030912600c1c4200074500192508d01040d6055080200040da1024945040d1004e448900c0001d0801224070f40010a01107960708004100101c0c003008004500e40704010000992000aa400c1e000c0340c1c203103441110b540080c20b00800411400c007005058882150000440c15409042c00303025500807420b03034055500292081d504000316504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 625072500 1250 625071250 625071277
    0xa0201020a171e07030e0d0504091401050927160501120e070303050903031c0b011b0519170310050103050112030e01030b01020a0506040b0412140d11040504052a 71
    0x83c241c20900b00192442d0812454180030039054074010300341c0d04100c403101c0082c00054021804000100322809a1000c0d40340701c0301844803a505103404900d0648004241c4c1c001c0c0790001f601c02c045034815100c09100f5040960603241c407820010031400422450780704160004100141c800c001c00000d11400500300346030001040f02c1417956034141c0d1941c021840300b035418001403040b025008171a4100c1d1100d40c03881c800020700c680d503250014041c40d90052007080880c5100204100250b070014402e440c4103801c90081000c0c0c2940d00d05100029601643c4811100c3c010040c0540740d418485050240c030b6090300d081c006681c0300e20354000d44d1001c1e440081e00150300301c41c0c12400d80d40264401c800c1c000f010303c1a541c030958035403142440e1020030340303040714214456000c202c1840200c10f4111592182c0b07145c882050780344200d54a4042c0581c12242c51b18903941d000491848900b14203d6005103005030003800903141c0a01c1901700b0014100540c1607d40c59003040d050b94a402c44101d4806560b075a5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 625073750 1250 625072500 625072531
    0xb091014060403061401080f0d1706060712120b150d09080c0f0703110109060f1b1a070e01051c05040804080102070803150906060d1509020a0201020a17 67
    0x209800104003144140c104004000c00b02c04a1000e0080d103940040d4560020940d500d40400f580c0741210b80c108900c3e29401c1110040760069000700744260400b0030b900641700c191241000a0068414a040244031080190542004603007050002485401d085030810100f150442840408603000d08110710b00f010800c01940740640a03480303010880d01518455041911517031010f854080481580c0b502580154405c2003044004030300c2079030000080c07804402e014a01240030708a43d00e903240d0402404042d0740b0000100c1034854007078141c0354022040400c3c0900b1441400040034060b01d000000503170003210411554000c0040310108204541c0800c000c04a000e05c12000381000741013180c0d507d03400c200000d100340d001d001425605000e94201c69503402c03c0320406007451680f0032054003840840d001c1142130760754034041c1c48100c40c1c142c00120304038510360407008900f0b07115089001380c9403012580d444a2a8154083c0656058603104c0d0344001d6001c015452100408940f400807000c80c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 625075000 1250 625073750 625073759
    0x151e090b0a03180501020d0225022103130306320613090515101202180403030b03070602160608060907050c0a17070c05011112160209010f090b0910 65
    0x303030700c4242168494000b442010a0a913180c0303080e6401403409010080d000309148030b4490241c01d443d1205201800150701d940030719400b1903030344506815040b0b9045245e030f106140c803a50520407136442c000280c1d138100c10a07440707291000003440d004107047c5024101c0074607902c00031a180403030b00208100d80003100c0c070307a5901c00400c1801c3c1e0400e414a2042ca440b40043c3d000110b0400142c1c4503029841c912022030b1802040003100801107910512521a8229500c40540c88078880c5a0341448500c003003c01c0c0da5120b0a064019041e08220240c243c03113a00000107000c0d41c0402c0745054002101e1128201c5a5a5542100d00800c03d50310359030700811101c040741d0030a016400422811140209a8030100210340301e1000d0310302c5a1140d044042c1e8001502000c00141e106400007424003400d103074001d510300b4100719694048407502052413120020303004040c1081a0003180795158001c004030a40d41e1103006003c00c2c98070f184124040d29050441b0748c2c12030b1a007442061311442001800603480380c80c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 625076250 1250 625075000 625075007
    0xb1f03050c1c020712030e0714030309060304152a0e01050f070b06010210090201080606090409050d0201050714070f0b04020319053a081f080a03080901060513050a06151e090b0a 78
    0x222729556178981b1040201c200c81f40c5608001e103200d2801495401514419a0b0b019001d40c0c6072682c142100310703041740b00120b00c1a00720700401c003d11303038914254041210101c010381e024480c9480c2ba010280010489008200000c03d585101d00000ea003691583c001a90305c0800742c0d583e0580c024080b820090004085044c200040c00d00d1000003040440d001090f81c0b50705050035000300c02d000040c2d45078001c105089401c001540050b030171550304107103084d94a1322040d08588003070f1030007043c1c0d1804030041340555404014105040303107403000d2401c2006551500c941d0720650600e15031000000c0401030305404035043c0c14501c8001c00a480e030040000d441c4800c58070080000d010800c00d0358425a218451080780c00080060000f050041c407200032070b418040d200250080290095030f0601d1802c0c40aa12002983c03403603a6000000824962185041d001c080c00f119003000250f140e49190440309568000310030840c229070103010192000c0064000c440c408294018080e22440030054041c41920 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 625077500 1250 625076250 625076279
    0xe0619050f130b040203010f03030e010503010303050d02070309081204090608240405070306050c09032a04020d090f0f0b070207050618040e0706120b1f03050c1c020712030e07 77
    0xd4100014083e07071050004049030004e03000780803e121200428010950440000a010042400d200c0e085602d940c1d0000d00364072408885d00c0d0059000304d681010107000d00005409044810181c1e0320200080c01e002403943c00034800c18035128207241000071084004100309c207480300341c1d05080040c0b009003402c1181150000c0c0048841d403254280c0000490a01e00c1981d005214003902ea940d95001c1c0c00800d807600b8403620180003d502e000800c184180070595440d0001441500d025031070703407e0204188000c01030b0301d0b400307010040300d103103508c0c100301c401c5204d120241d00ca91444400e6403903060040341d6400040c06003a411043c01c0084945584101c02c582881c00402000480d042d0a40e1031098141140c82d0f211001142c07540701c00e904443d8803400703208200b44082da0000c0440010260003c1c0410102d110030003416510000310b0300000c008070840f40d8000768540030410f040010702014000f90300c84c0a0a45d00002c5014041038002c4c46805807900301c5080400901c106821300c1c1074040c070382c030307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 625078750 1250 625077500 625077529
    0x60a03050c0705030a0206150f24070b0f04020316180506040603120f20030f070303060e13020306010b18090709090e0c0a080303091f150e0619050f 65
    0x750910030300c0e00140d000c000411101140794060840740c1045404041c401a0b0301c2d502c1da11074000c0c0c0d0b40c259501e8880101200d047e025142c2540140c0c234084100e50100c0c89244070207098580504200105d0804400005008a01c00d0f41241c0355010320b0410070b00559000c3c0201400c5800c0c3e01c43d407000904458000f15003084004100140c2c07695a40e030b40300314440d4a145488040384014984000f4160880e14021400500410000001e8483c5100b00e843e4070412000341c1900c03801043d000f0905110364810406410342c07480c82c101d0790504851030050500400d401b01c0c403c0c071800001040540ea000305813004500e0a0b2030408140c03c481042080c800c2c4010070070b200300907002c400010100301c24014546000041400b070400c0341a000140f00300658944c100b007103140c0c41001407000080002a950480e80400846440840d4091242c0d01c060904500c40030f00010810320301188034182050710300d002d0041241d402d0000c2d03601e01c40000b09a4128402c01d9405840401485180c2c207210600c2e084a6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 625080000 1250 625078750 625078771
    0x19080d1a0603010306151505040515040f060915170408090316170c040c0e01050a0e131a03060114060a020304050904060207120e10210e010c030614060a0305 69
    0x30040c01021030450307042644203031003064843d40b144030315601c01e0001c00051300c2c0c80000c4120f070b044845806000b03403140d449420300600250703209800ca0503100050701c000d0284000400030607660b46000038003060040c01045008800d10203402405c50203010914443e81d548400e20041d86e5494030350b6038132034110804072a010300a519604480c10851540b40000e407801c0040035408403480c101052420000c2c0306d06502580c07900d00b00d038000316080301d02030004e5442441d116945041d5800100d4400711000c03000c5801c20168035110490300700e41d4020924008800180440106c042c0b81019500c01c4207118000c8031401041020b801d6042510081009003280d0040784e10702596800480d03819401140c06407030f4203502003041410040200003c50390070301c9901d407034050010700c0c00025846d40100d260180501000b40400e400e070099040110390314074003e903410480c4440c9800c20031b000e8007100c2c4030f00c00003914101020442e0000d0701140c0340c0d403010103000141031101e820f5041c0c004101c086c0c200c4484 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 625081250 1250 625080000 625080041
    0x3040303080c0d150b030a0c0306050d0b04020a030503182d27180c01050f04090c030902030322060908120f04080d03090201090609120b0727030519080d 67
    0x100d04c84600c2c000024403800301000d42e2403a000c60200d0031140018001800c26003049400c0007140d42d4490302c01440c40d00003400c8c8000d51128030016002000380e074001882808042510030214500802c43c01c185401078074001e40c4650040c248a81e1200d07041030f98014466515413800803410038440c846000045904070b034114588801e1480402803003220b1060404038003c5030b0082083c03050044080c60314003030803d41d0806030006240505402280510141903030341d40107410016100b0f4212001c82078015066950300c070f4015044080c00d401e48020070b00302043c44200010031f18821040d20302100e4101000d0449210200889581c1d070740304140c502040312081c40085030401c0140444c030003805460b280010105140c0c80003500d078860f582e01a8090210b18101080114802c002042049030302404030032443d0b40b10705c6c05a41c80e000c0304180c0b644001d44904c800d01c02c280b40c51828815680140c04480c100c1081d410030003901e902c0d1180080c03190100380029140c0442c40e42065840f205145140d650 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 625082500 1250 625081250 625081271
    0x40e030307122306150426120d09021e0f0127180606081003120c1403210402034c0f200f0d06030f03020f03040303080c0d 54
    0x1070300c000341c410001c9180e0520240030b02e91401c500d80781c043c2c0e003444000e10b0410b450180c007100c000d0b101002400c7c8460100c050303240b002906218a110010035144074540307400450b42408020024101e00300c2c00350450a0300601d01e00c000c0e40c98804d02c080c00804007010441c040d80110b0310160415103d51205031500c80100c00c6c403131060407060152031519030752503204003aa07403a4000d886180e4004414001c0d41c3d000e100100083c001e00c3d500f541d4010a0160362400c403c4003c03192154400405082010f0f004501400640d0110050405507041d610b610340441d01740305d81c2042c403078058400035030581c804040e00710700c2c408401c95014100510601c5412800f90bc0f030002c4074260364140c444001c07a8850740b10400c0160316101d91790740c0703a007190003c0009801c5107001c0c021a118270302a107a81907001281941c007400d003100032500d49200110050050b20ba60345495202c140c0001700032400742c000c81c180d00d24458000002c0c2c030f00716a01a80d4924142c1c87e01d00c1040741c5540401203004038691240c1000f070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 625083750 1250 625082500 625082531
    0x130f0b030607320d1a030a06061a13120302071a070b07081306050c1308160b031504050c090303070309170102070320030702121b040e03030712 63
    0x602c109516100c0300244042c00034280803903081e142d0f061403101080d00c4100840f03c14082a13451041e100c04001604c080010f441c421a240040340f050350505c1080c410404001144c1c1198040f0f41c1c0002c2c0c00c06011182504031401401584020040d04d03501c41c2c0100a08140b007805161042d009005569580e92250004201103480742c01135451040005210003c1050300380c8500c3e80407030b01c0d140c00242420210700214a40f41000c201401481d16040070410004103141100d0350f410100d4000c4891503541c1c0652500d5250900744e10b500650151400100819210708030b902c1158140031007405c4030360081c200030040101406d00c14030950305008001c4103850800003054158040e40350141c03d145400212041840c48508041169005105120000b9040004220100804030340301e0100114204194518046e4180c0030b5440100c4042a8001400102d00b500d254140300c00c41d10b0113041000305100a41d2890090f424069108000254202c1c0c480d500d442c20810007050b01041c48001d44003d00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 625085000 1250 625083750 625083763
    0xb0f06030a060513020f03070c03020f0703050f0706020f1009050c120615010f0c02152a010c020111040e040f2001020114090d0f020102190e01031406130f0b03 70
    0x88404690b210780030300551511040e0706104101000d019860500b0145c1903903241d02025003101c0912080c0d00c00041018000d0150005201c040c0e008c0750130b840d40e81d0405036a241c0f0810b002042501038800c0c0407030b916101044094051900e080204418016a100980180303514070301038170640100c084089150b9a00702805281c40c54400044c1290b08283c040c481021905041d0381b1f0601c1a07070100c00440c142c0001e40521100d80407a201d00c24181424180c0d1400c1c0702d503030056040b00c60806c2c291101000e070168215580c6150100070004412124800d030308a94001021170714144060000300459101d049000307a105100da0f0804005846940c0e512980c075840104602c885610b5611000307413964248568120805000b40d1007516050404131252501c1030300130b071076003048120000d40e10b40328001d404071460007403420315441d6054980c0d030000701449108505580000e050024440f03040044034122401143c000742082d00045080d400c46e0020300c0300c880b400007403a480352441c0c01c4668060000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 625086250 1250 625085000 625085011
    0x803160905220b040b01080c07170a050a0206070c1a18100204080c15071214040602011b03140a1d12120f07020d0c062706061a07060b0f0603 62
    0x1041c0d80c1c80d0400c60700402e44003d81c50150095152901c001c905a90100d4621303041040940056038810003410034542406000050b0445590002070100070b03a0351100c0104418803e43c0c1c00c3c4c0d08207480c0c07808111a20301182c43d001d8481c0c00d1841d82c84c4a002010481503401507500361282c03480b2820307454558101001050702c80105a804641040865001e01c44406400012101a4200303070310300e0002400743c00b0b8208081d016a101c0c1061070003080c082c540d510b000c2c5000c0342c0000d8565070b031000024060030180c03200f45214442c1106907400e89000740034508861880c1951400e8690702d1441100052404238401703070404005103409016042d00f880840000c0b1407100410f5a03a0111540c0c2d400d5010018120550100054003000307000c550103d10158640c80500d0300e01030303503c0c60382041e0780a002024121545c41c0b011600c0a400520810350510703c240c440d82d0103000166a849280007000245205644080c0c01084400009149540202e9004400400000009415001140e0950021100c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 625087500 1250 625086250 625086289
    0x4050a02102d080108030a050409020901020703020915030c0907050a0309030e0d03171305030703030924020910081311060d061206060e04030c021e060d020d050a0501030803160905 79
    0x4202e0300701a4440412405480220010352a21a110100505c50310481c4150b031440307680410001c0c1f03da80b003401a03400035500100000800c0c14004030f003003c0d00c5540380c4114070a10510b00c00f8011420100606481100191109814440a01420350140490020840400101c0400c500d61540c9000c0e000324064003079925080d8030f00484019404509000c0e0400012402110400001910000440f4a102d0341803401240e00f03101d07417404c84080118000e82500c21100521491040c1c07809a014010b255800c89030025482d1120400340e400c148107131120058450715100300c0011071458040f01c0e0700c00700701800d414a40110302c03c0020454103190421103480140401c4d200510034240105400b501c950000b5050506240d50003038082120317104004c2c014186100d01c0fa010254541031103a000c84081c142c0c2e6512803401104030002c1d4010800c4408403031410010075401d80c07803885860b05982c0e1201e5118a15100c44211a0850054044150402c080c942000c41c20f134035102e40c1c0a00a103803070705 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 625088750 1250 625087500 625087577
    0x314070803031f0e0c251a1e01030b0106030908091801030320031204022707090905060901091e0e0a0b0705092805031207021804050a0210 61
    0x2200c0f03078051509901c50b01800e101c800c140718480409008686014900c20440d05040e0103d846450076140c4000024100041c0781000740b5034100d001d0740c124490b0b401454628a4030690010292440a081c0001380c400d80c0c8100041c40400c0c001e5010b114501d00a60415050481440c00244940c004c840c40c0c16000f01008010030805412020701c40200d00e0001d0400c5035917590407101c0b90b80e406140340d041704220514022074299120380241c070804001080c2000c0d0441e01004001140441c00e40e10000020081c40c80003032001a1442518000c6000803300740413640703043d4510000d48060612003502441d95960300550502c50f2054480d81c2078034a010306080c8003903042040c2030b07000051140302804404c2105c5645030f501c040805110466503100311000c1e18002280504440382030b04115054803548040b02421540c800150290070b20840d19201c1083c2c17058150410b9841c00c0c0c4005010381d210302414001480c1512030186401c00310f01c1c0442086842d41c100448108c14294440851082407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 625090000 1250 625088750 625088791
    0x110c03070311060705030411010c2907050703020a08091c0c05091005030607081b0a0504080d0e031005060d0c09020d24030605090f03190201150f031407080303 70
    0x3a582c0c03040301c035249018104500e07003580c005e09140b01c010002044517404009000d030980c040c1d00311300d84050300701d50320408142442c00402d4002881840301c4800e240c05000040302d5501c03a8044480c4682e250740030b09a10380f032555a03081103800583d0041d0f8411024114500c038808621004d4000714060844d1030320b840e10740001e125107a04094510308410700c010009200300d440018407550402d500380f4040250756103541d40c18600d03d28842980750b0710b020001d00d2285056020300500240c0b41300c081610040f0810f01d4094030100c0124200d03981640010000d91064400303603110315804103000c0c00d45060a8820303540e84c44ca180583c1c1044219641c0803941d0b10202e03045215041c501741a2005801082290740f81c400c604a580344401810540c80c0c00008400b02402d010340303085c081c001030482c0d0303d803043c412003001006038202c1113000662922454000b022003d040000807a00d800301ca41d0382860960700c078001d00584080e810002ca216008001807880401c0000b113106080d0704c2d43d1210b041456 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 625091250 1250 625090000 625090007
    0xd0302031207140306100309051605031e060708041a0118050a09032a0b040305041d0105010f120209030d0306170a0b0c0a170c040608061c02040f110c030703 69
    0x1030040410007031000700d960f86442400d03044980001041300c1c82c91484103800000c8015048043c8014014001c0480ca41c00c035000c100700b0708007035900460544034440303d844640301c000765021403561a15070250011646582c012101c03140c019010748500380400110680c10101e0442c00e90108000042013407040300120924840e1a401221030141800307014055180141600b119000c1090000f43c540c090003141108d035580415082d500c14000c0880f8a00307030078080c00c00e400600c1402050306111500d44100c0d40a020aa4103a440507126800c22051125041302c0740e950072100c03000080c1e0b00301300c1849142d6080040d030010100640d07000c5002d50a0284008404e4020340c458001907228900010005102014042d4042c8900c1112503ca68080304100c9a00c3c0301a60360904600c9800140b14210b840f1000500654615807240c10301c0340c40300414403404801042c03070340c0d41c040e5250030312400618094200350b280e090040342c040744082c88401000500d81c4007a46142c4590300001711001003641 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 625092500 1250 625091250 625091287
    0x20c0a08010b0904020603070909060b03150d2a08160807081506040f1401080c030d080708040210030608120909150913050109140a0318081e010b0d030203 68
    0x240038009000307080090000c15a0924041d0009100b628040300041c8540d1060000703c000b8600050b043c080300e81d03907411000b0a40e00507908034100c80728080d48048a400e00d2000054034540c007407082d8560014403113920005503a0000c084880103000711000919130350400407441f500c40c03a940740380741c810f1904d855549000040c0d030082809801c17000c920406500103259044d0b00c000d00b5180031176400c0240c991000109040281c000034010118000f00348500300082c1d2030f160310340540890701c98144621003030740d0400d000c4602000007101140081e0050410300020a40c000040c10003003899a1030380202410304400190400c00808042035940451500d10089038008205d6050802e00720b9210000c140c12071030050a40c0f045020f2000c582080000952107402202d0300a46420011280c2589540c0c541d0050081500040d00503911017000d00c00c00d05080c0c08844c2110300402001814249248001c403450030002060755a80c01e0810054407208004a151840ad0b8080c0d5a92102408020030020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 625093750 1250 625092500 625092509
    0x11030709110901050306040b03030c1e070f06050c0a050706050c060f01080d1b0b010b0c0d030c080711070e0403020307050613030c0209040204410910151203020c0a 72
    0x1828881c440542403251802c880b4840e00a28283e5682d6440c40b010502402050305007940611001900d070f06445008606420040d0352800450140000d004006a40305094041d074140c7e0710400004000c120700400050503040c0060003038800020b80358803a141001c9540d0700c4500802c0300011040d03180d11040c803105a02c2a518032060b201c5505020f980c5035600800e540071004e12202d07007550f0240d000030001810006908c0a9284c40325030312003c491315190403510080501c1e10540424092090207800759102170302640d52000900d58521108407208145818100520b006074000440d40ba0303152400079110700c3c042d8000315510b10880c50180d14001c0e008110784008800c5102d540300003984080041d48943e0129a040d4564817240000f4004081c0316003042c00e02d201e540d4a190a203c040d40c4081002a4030261411205002521a4041c0c2004407281103c0b504008c0c0c000c40192110380c4900c521483d001c0400880c0384d240d0001e2101e070a040710f410b1f4056845103120150900c3c1c01c030b0000d805007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 625095000 1250 625093750 625093769
    0x16060c02010c120219141e0703030b030c0d030e0415080c0906010807082a0304050705031209060405120f030d0510060e0d030e03100204030309140d05060c0304080f0403110307 77
    0x4810300345840b1003843e01c02d0400704004030441b02805c0d40b0500035100280300e03065800d24040c00402d0081210b030320400b01100032a0500341c400c1410714000c0384c160040369001d404a01d4419031035904560402c807143c3c07a00d901035a92a44052810301d04e10203000074018200c01000910a840c00704002650000c04260400403844104045103901c440c8064220042c1031800801c2948408000c1e00340c040c000c03c0d01c107088000310412050041c00155181220826401e030703009082244842840c1d442500c0c401600300c04200320070800d900304030b4007558000960100b03484020550324032041c1985d2000030407081031600c882c04d00411400c44d1080e400182101d0416802c210120300109103c10700542014044c0f1220441550b00b68505018400b031000002d2030456950f0f0301c07071601030056600c80c0200d1040300c100e05200700c0b4501700364060540c2c2a8010340106180e60362400c80032400c0d0704c020002c440c03620044c801034405040d440b0140010318441d0710008030707420300d5130185454001d4aa01400d020b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 625096250 1250 625095000 625095007
    0x5041503051018290901060b220b03010b1e091e0f09010906080f060408041e03060501030b22260403051b1203190516060c02010c1202 59
    0x4500040c032540d4140d440c0b00201e40340d400d0007214495a08010b00213004030541089489618524105104226203480c201c44c441c1d84030412090700302c0b6100c1c0540c507407001040009401009804100134403181285581c0070080781c55084c40403c5800c2030380558030b014408690442c0c01702000d004141442d4149400c60700304003240c00040d5000759a80031094440740c09141090150704d40c1e1900e2000d642d006086031249596a120010040c00648100f445a0040c260160301542010440ca40659082400a407c20742401482d800d0040802140f032900c44d01103100200107038241c0101390003980644001c08142c90600001c00100400c525613804036548141e03118000b0707448451440d1100c1440d8260301444d20301d50b02c804110700c204e4102401030711420004110b01c0039080c249030705140099440b5101c031a00c0074035203035490142410581d803041403c0845422184a80c0c09404803182d010740c0b14041240c0d68032042e0464030035201ca280141d46452000d002070340c200c50400d41e0a4904c850451a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 625097500 1250 625096250 625096253
    0xa1119050703030c02040e01060303050c0f1204091e0e0d0e10083105010e011112040303020f070615030201031a09010302122508060703230405030f0a0905041503 71
    0x4480d41d40703000080c18010022601c20964481340e101c1404c104008008010b05501e82c10701078159040b122002c40c0510a0001c00740395110013080d0755040e034a0300c0403540e05207030800788010060052061081c80382c00700b00c06a909502e185001e0a00749000d120054103000300c50843c002c00d04040d5071051b6006102d040c030741c110700ba0f030b0098070258800008000580044c25202180480401c00da0740700070b50a40e0140b10806110041d0711001c803250b000d40080001d440c40b0340b075020070384c01000c00403140b1004d03680000d00441c0c0260014a81100360100b22854036803580d4490f422650010204002c440c1c0b408818000c5507010300c10b000240c54406034010680001d98000b0f04a860140030007802100e0b604207442110360104190581c1c0c40b03048030020f00202c003101800005401034802c1e807000d40700340404526414001e105a01400c00200c1214544110102240500c0c03540584103c80300c3c481004040e0480800202401000145540b5101c45034540400c100655662030302940c000005804d0400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 625098750 1250 625097500 625097503
    0x614030a02011d0301020d05180a0302151003080f13080c1509031509032d03040609020d0b0109140109110304021c0b0a0f05100312051b030a111905 65
    0x80312a424a00b410451442000103094402d00076400c0340c143d0b00105803400f0403512a0000351050b1581d03015580b08580d05600656603417105140034000d60040d4800e010002070300c4210580c004070200c00001c2c580e541c2d030f803a12001c0d400700e8031b00e1071041004070340b00031143d940202c80d00007080160001d010014021001030360071001c400c50142c08080005005000d0b131020301150100a800782040300e010320f440c104a544a41c044440e0401d106481c040306d50700c0c1150b103600b0050f9031804071241411940d503a9103d400424007100300b82d0b44018024800e0002803154070405010380900000070400080780b00c42e0308140c0c00107802001070070f403c00a218184c400e0741401e8035070160b01100c0088180c1c01121080700c5a1034207082c094407040c0e07082d0070011403090940060440b000d00c00810001c681e1110285240d550305404024040c0b2100d2420403021880b50300a003444031031643d14551030024080200e442e40e800085140081a0442c039980440c00c8103200201a0134801c406c04e0880c0002e03640c929 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 625100000 1250 625098750 625098763
    0x5041e0209060d1703010605041505120f061c0c06021603051c1418092406030c090306090c10090308030f040804080102031509060d111c0203060c0d061403 68
    0x4502078800d8195200500c5501c15003030041304005408182d495840b128001c0c103e5005004200c0d0100c08520000c80b428030a004072514031503000d0f000142c0c1c0c2c40d080151300700c048011301303555442465045d5400c020041b80c03414000540c4502100c400041c41c20401070b003082c0e0010543c0011241ca12001c0000c00d401044842c21408242e50114425603026016103062414003a001c242c42e04c04161603002c480302c116101d042010440340521140d9032220140b440b0140c4003015921010002005c1c00b4605003880a5074000705125005420f0002040c0800d00d04041142c0342c501355404040d0043c2e060402c444110761280c0d040c50002d030240c0c01d5803901a4a440041d096103101c508007000541884070746e80540300500b911000a55807414883c008104001648505074840c004c4000424200e00d09144221400c0340d00202e608290659682005482241c4c035055003d402d0801c2040401660b0130310003c1d100c4c10042c94400d4882d40d44235564004c0314460382121500b84000300301407000e645c0c0060b00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 625101250 1250 625100000 625100011
    0x5010e06031e01030b01141c0210031e02030f0609070504060f021606052206141605070e07030b0d0b1513020d090201030e0109122303010905041e0209 66
    0x35269692603088040708992111000150000050030010080050080b000c0b812034145921010021110000b0010a40901c20b0700b0080c1010b040b00e01001400c00351035905000c422802c0000c0d083e810a0405030101880f160840103c40c0d00004000d4400303002022541c2102d0251780025040c0390884014140780300b00e001360b1060018030980407049903c2004600119100d0b45207042e2080c1c0d03180030240030340d00f0001d560404480d12480340c40c50700c414250800101d80c0320341e40e0042020b000e00d60240440d4400c440a24260120035010000700364108403100080440d406180d60b0b518081030300400709c0350440c3c2c0d80780c4110102c030216004210f10780c0146401c810000c0e0002624034040c40040c20304606003e1050202d070000c83e40f02142d07989944078403e802c1c000e032014007001e01e0a800349800c0720f42424004220981c3c070402e610603203101e8800022070795444850f40741d0a0309051840440782e0426481509196141d0b030804c000c02c0002c2018504401c001c4884204400042c0e00040040360300616 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 625102500 1250 625101250 625101259
    0x3031d0f151e180f033a0503010e0109050603031e19110706181217070807060e061303082d04021002030a08150d081204060e0705010e 59
    0x25500c60465030465111030350300303840404030309404491459a600a0700004040c0f00803507a90401c24140301c0c1e03260441000040291200b0801d840d540090054080500a83c1034003114492124906910070542c0007400354540c903460750301d00000c03000c4515058001581e51401c0030140552510300006541c00c1c1c0c0e82129028041140500d844031030390080540e0340524181107a41c1d03070b00c2242c2040c1d540080d56401015954101e4030380c075042d00c1d00c0c1d180c503000c40d1f000003e0190401c0031ba0b03080124908203c3c401c80070400c18440c005840c5500c7c1d0030489042d1480d050016042d020407800d071041d041030440803c007800061034080311011940f0502074001d02481020400a82046c82180d0703110540082905a2250503403034140b0190381d0902160128000c0085005041407140000190f803c0142c02c0d03603d0040710f9607180907840c0c80b1045c0303141581c1c1060701d450035000080c01302030207084400c8600d0301c44a420310f41070404006845034840644416046514144540e9074000c0500000840681d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 625103750 1250 625102500 625102519
    0x705030a12110d151a120c040503070306020405130b091311040908092b120c080307050a020c040b0a03080f0705060916080114060108180102040f03031d0f 68
    0x101500080c0c0b50619440e00c1031000080c16000c0801140d11182c1130103000040c2c1d899068840f60b612054a900340150340025034144400c000c0001201040c95005080a005e103091542c0c40740400c0c9054050b0300111803054001c00c3c18801410b000401d05100300c84580c00344000c88016000c260788041c007401105011035100b00020a11490110303c030319410015004000c50107050600d1944c2d500085000d030710424030000d481203000b101c1c01144511006882c82e0300d41c000344941d0350f10000d800704100d0b20180089030700d510001c51031002c0a117115002540703900340d8800b013110f4028100b104000c052407140b03140c0305000d01c00d911a40d140030300f40c0e40d211030025550200652062224022018000c0151040800b0820100c1c0046001c2403080743d842c1c2460042c0f500c8017019070170ba500112001c9070b0364645000282c00b5610502c510317904007a96000c00510800d01c0200303142a40e1194120105498114400308101a440301203d40304184070514200d00ca2912400940d4000b080e25400d03100300c0915 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 625105000 1250 625103750 625103777
    0x70206070e150f1e1306170105030c09072606030c0316091113080304051201140c070f0614010f0602030f030423010c0e0909010c0804082d07060b060705030a 69
    0x2840f2013007a00c0d803243e03400d544400c0c0754140e240343d0900b82e014001c0000d02c0074580341020b0000e80012410b030303100200600700d0302d403100d414001c0c071140051424003044100e00001c001e02c8a8152034480301c040c0201d5075022880c101c4141845d04084410160107a4050241001d81d41c1500102100740d0311030a0001c03d8081c4514007080441c000c4a82c02c141300785041c00c00003a00d0f1720000060044900545030300070744282c4409003600300c6072072550890380340e1002c5000461542c0198010840184a03c20340e01a128054403100200d03900c030011540150709080041c0910152000804020000c505c0118034091104220071411701010304020041c1d580c1d003404800c441c0e240c109039041044400002c001d499015030004082d50401032803e40600300b0b850201d83c04140600035002020400e8403a0000350b00c4603918809294032081d400051800c0c9111101501010800c940303068005040a07940c89040341d08081e8122610b07036546c103200b070f40d040001400060300401980c0442070f079401c00030b4101041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 625106250 1250 625105000 625105027
    0xc0601060318051203010e01080f0c01050313060e06042a12030320030a06060c23010b0301140405012a03050702120c010c020105060f0a03110604050306070206070e150f 74
    0x20b100b8000d1081c010800c40c2400d118890000d503048505000c01d022283c1d994240c1c1c56200c140b00c2008602075000100205403c0d402a401903800008007600c2d100050b000e40c4079402121865001004103030042420711050041c0c15000d04030a0104209118038015540c0c52142803440502c10311540e191030305440001d0500035070204000002c0113480c02c00c042c00c1c000900d0010b900c200c410001c0c01d403a00f140410000d06c280320300448030b1307802424003800035201d0f0f00402d0300003c80514400b09640302d004080b0f003510280100c0d482c880d05042c410b00305040c070b03240050139254101d0308102d083e04d1180e1a418031000100941d400f1180d075090010307103a107403c80b0072410481e11180341d27040d070000011222101d860552006800160580c0200840e456a108000c03100c0d600902c610742c0081c00001c10305c003080e4400040e048c11240200003c1c030b001c0c0d0300e00100c0c2c1450303000c4071200050703003140c82003103c41c1c0d800c18605081250202c41b0340c10510040760380c50780c15000d00117928101030000f09e88021541003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 625107500 1250 625106250 625106291
    0x140f0907090e100e0706080703020a050f03341d010c0312090c0e04151a04020903011b0306050a060c0503160501230a0e1f240b0301060905060c06010603 67
    0x3e1031005001050f104c10015944075124810303440020008800100741a01c00e100f502e600f500d1036034031240341400c15000b070022904090a80030480c5c20700c0461680c01c8202000216101e82007002910b03110307651081c090a02c01c404a0541354580044280079500d80e400341e102600d1661505003032101c0c0a48484040060104501c0200554200907003c0b4818400c507002c1441213224601c641600d081c00041c080c140d0318101840110340507403280f42c1060b03190070340180c0a4004090000100c0110326417010044a241032800804640d9400050146042c0031400501910507414110a00b080c2940c642e030350f0380b192615144000703000c0c401d02e108200082d0000d90501c00b260510301040c200c0c80382c0000c0603040541c1c541034a10300d03050050301d410401244101c80600561000156211b03e000600e014105075000d80241c4020b090745201b00020b040500409003014601503a03c2c0c1d030400c48003403c2c086254005d540314003000e0044030f02404000405c6030540341e03140b03008200350141c0f0741c41102491 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 625108750 1250 625107500 625107523
    0x3185808070f0507030b0a0c1d060d021c0b0109060207030c0e04080408010f1401050d020a0e0c0c06090d080109090b040f02130e062706070509010c020d06140f0907090e 74
    0x2040c90010078464110030007801202c442c003040060711900c1009544207501301c220741c880d44407a150310f0320700317841e01d2b078060038041c0780c0501c000d4540314a000d581003003100c03803400c0035049640d941e0400400d5644444941c0113810b9500040401900b9601c070a8501300080c8140d0780031654030360020f0100f00600c410360300109005002070083c3c000000e45840a071090304407520b100380d101400001d00b880e14500041606801a100409060400c80110b420070002006640c5c901410030021100302401c0010724803a504e5480540110304502c94014000801a40944d108500b0085031201246903c0a21504580d129041c088480a41c0c408940e1112058030700001e500c0c0340c140c41c80401203020610360710070081080142c0d0440b0032940d84c000c01000b42085e000c0941e00500005801030700a100816158505051115220216900181d0000c803084c00c1142d041e5200c0400c1d04208160942072030300003111184c4d415443c5030100c0095920003051042c030105984407001c42d4001c1c10244a4040c081c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 625110000 1250 625108750 625108753
    0x60b1909051203180a0b090d0f050d0c1a0712020a02070906141f08060d0c0312030f05060901051c0206160503270303185808070f05 58
    0x40d040b00c00c0c0b98807500801040403481502d09034400c403500e000b910300c0d03064802d040c0000c2d082500d001c040c812003800503141102c2003900492010081401003141100000c129510340810801e140350401840081c03203c0300e42089598818051065042201e28020b00501103006072100d0418504a1400030701368031040d00d0a1808401152086400301100b510090907030304d408150f5000000030f04039100890b01100003030310b41da020034540c0c94a070400e44c1d071345402200c0341620f10351282c840040d50f0004000400110341d80300c0c05040020040d00403a6449001124411103e40c50203001c00c65049801d243c04441a42d0040048215036070b44081d1003060309550242e18001c01e05103802c80d600e82c03102500c06030840395140c83c0c030003620400d0564140014094050741c00c1a800c140300550b0058411032843d801590842d09456070b400c1ea01d00e41003130f087c21550142d01488080c007100341500ca07244420310486500040781d5041e41c90090081c4905900203241a5207d0841c18a610805070f51100209030303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 625111250 1250 625110000 625110019
    0x20d140d11071502100c0e121b0906060d0e06071d01170901060f0b040305190f0f020616030201050a06120201080115140a03020307090b0711010c02150a03140a060b190905 75
    0x29034014200300304640301344d6803200d108c040f01ca032507665581c0f4106a20203030615048210468104101150740089000e460681048143e00d65002504c1d5130191920035540082c00b000221603001c9a448019420590226164170151000915803694070b81d18142c20083c03040403401c9054250310a00080102e0309114a41940700c0400f860700e80d10600c0113842c01c0c455607070049003601e10440300501060f40010850640da000d503884200c0541032540a9a200b03405000814407100e0b18003082c030030315100b0707400003c50b450044401c604448581d0840f00304145141540320060b600040c04c0b5042d0340c6040ca040061120341201142c024281a0420440c4607011801241090301600614056099611101049030300e890a40301180070f404000b82083c0b070540303251022540908080008240040c01041c2580c001c40044241070780580c08560000f591468900d01d00c1c0040b01c84240c00c505104002d0105501c2c05c0c000350054041c1020340c2d04600c0da0860854442030140c40c00d03400800018040526 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 625112500 1250 625111250 625111271
    0x8040e0c0d290d020f0d0320010b03060a0c020a08030a0b120c030a060e1c1706060901050405010e012a030816020c1017010e010512010603031e050403020d140d1107150210 75
    0x6207084041c00300060300700c10030200c00100107014084042b480070b8003d00007a40d820100341d0107828061914402d501a030034200020130b880c14001c501c206403002010031803080b0388081c80041400c4040040460b00b103208000f00799a00411140b819680081022518000d49501e19013000060401e140c0d900221805403c4525000000c080512a42c18881005542d0f03280902160380300d40d40c4900c0c002a400c004c180415030003411401010340c4103151a0a00c100b503807804070030586840c84030801c40707201e407800d43e0b0030103902c5031060b03602141611203541e0340c0940542c0603540d001080105441412094a210b5049215000010307034401100001c110a50f510706116070305620038003415001c1c454420304030024413814082c000840307034140c4e00e480c160b898030040390b403040000da41e070308007045820040000981e90300b440c418959030188606e0b207200e00344640e405250060004012043c400519002d241001c00440c000c811600712110200d01c002c0d506008070b041c50070501c0c00b043c08510f0420644c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 625113750 1250 625112500 625112507
    0x90f090406050612070f03080a170103050f01150b030c0708120408041a070312050601020109020402070b01060e09090307060b04271106070c050d08040e0c0d290d020f0d03 75
    0x2d009003415110070000d06003291a80351a10241d0046c001600841e03d01040010002c0c001400c507104646010385050f60310f1034909400c484203138000e80d082c1d80a4a80861484028171580320b43d2a00c400e2909201c80c906402e05016010040c800500c030078011407031030140642d007002c42e0302100215280d07149600d0240b401c0071494110380281b00d840304020040b1440115212f00f15800c454141e220f800054811404203c0507000090009045548032106c070401030300e550000d0164103200d042880e034591b060540c0105001160320341284541c0d400300a01c021204040300300c2c0c0300c89400800204509240d000490064030103c03601d600743d500582e403100c5020201070024010644036246000c0e424240404001c094000d410b0003804c0c2d42c000307040400503494512124280240300e03d981c5801c3c943e071030f400741d02c0003441103501e070007400400141108210418032815450a5a42d41002508040c1e0401a1800d40c2c1c00b40c4010700030041a01c20170b06541c3c6550680001003030050a9011100c542d1070001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 625115000 1250 625113750 625113761
    0x212180c031510060f020606190f060c06050603010c092d030b06210312130c0b0a020d021603020405040c0503060712050a06030506040308130c260a030f05090f090406 73
    0x150743e151040000801d82070301c40d1103045259085540105070f5a02ca07542040a0400507203110600b22410031000108088030260f808003e08094640000d64162420a00107a1760004e0099110764900071606006a820a49620640780b12340b44156803102c00700c80421032080e040d0106140030b100c1545c00801c000704070340001d01ca05801c0d81c0140c00d1850000220100615104401201e81c1040c080200d10f0f205401c14070358803450740b0010703142c0d6060030744907036042800a4000100740c00740001c0440d1060380411408007000103030f100802140c031030823500f5a819915404001d10941e00d6002190501800c40841c00240000400f40c920508003164041c0c40445505140001c20303041000042141c4294840c85048a402070003a00c01a56580c0d0103c40c404801840c049404c0032241070300c404134104000c4440a401c4400701403984401100300007501c3c0c00f00c0ca12070007142e030200000c440081e40c0121a18518885414110b85070040c0d58006400751100100158001c0c0200080005015994100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 625116250 1250 625115000 625115011
    0x115020304051302250b0112020609130606090b0a09060509012f0c0d05070e0606070c030308040b09061e0606041d0402011e0207150c230f010212180c0315 68
    0x55114500b40301601c4164103503d5100a0209030007080100231038810628034a4080f880201102e24000c0602c0002d105000d214076658a41e6075520400d000c51034100a009000d0203058490720709180780707190000c0809040d801b4000400c8800b241c50070f05a4014902502e01608011042d04070040345441c800040c808820f820f205842823820001c1d150500e12000040350b134100016140841c01c04012000500000c0d01e99908401d007001900c0c0440c440c0c94403500518441c0d6141c0c031060520307080254499002600300d00340741d0408018401561044108156040501d000380b01c41c036a614000034002d4000c540c02800313441340944c2012490b800d03100c100d504c100d00c00d80303e8010402d4002001c0c20007042900e40c050169003c90303818031400802c0401c50b00382e0701c1549000d20102c14107540c0c407c02c1450000c0011116a240680c510041c3c03000c0c0001e1210500c02d030000c60504d80c0c00d150007000958058902c0f8607d609030640c040101905006002c0560009030817a00a0300c008040c1001c80c0307000305d81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 625117500 1250 625116250 625116277
    0x702130605101e030e150702073201050a05030406200d1506170c07060b04020a0c05011d0a020607020d171306031514030703021f180e0115020304051302 67
    0x190b103e01d0f90003403141e9410014441d00078a0a01150340000c800701c0000f403d88015445800c2001030b034000701051607000581d40300104180290340602800642d0500807041c1e060180a02220006981c13000680360b220b5045a8003292600211540501c1c21405105c8070b15100400150000300224981001250311001900b20201a6490f042203d11503054413511340310f589030402003915182107001030a816402a980041c0c10000800083c040381e00690011000ca10944441414803600384108105e0001c41c542e030740200354080c0400c075180d4000344d030000d105034808105202592110741c1e04220f640d03031262586070410b07108802c005007034020000c0030104200c41800410010701c64002c52071190b9031640024242403c00f120b18010840c0c0d50846074140c801e060b40040907940e006040e0f40c14041d05408076060700161900105105e40d5406a01540f03100e4100800c0a800302010103030448180090314805640d40680c200e0452041f80c1c4801c0c1c1c4940070054016182c541ca500034807503009400b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 625118750 1250 625117500 625117547
    0x50613020c0c030606150a140d09150b04110415050903070602010902030f0721020f22061703070204050603100c02070612051015110304030605041106040b070213060510 74
    0x2d04001b800c2c00071001c0160b02c46028000c4042890064015000c00341c501d00c0450300340441e0a1242c0c040310030801c3c0a0b602a00c0c1e240c409200009284500d107982c0301c05071000d0040010220303019180b842548289a404001504620760b940d1250080e940382201c01000e480d00300d9595480207000c0c0a0f09882a8484e0103042001480100000784150442d000300000c0b1000c5016000c003030440c10b000100a0360000c407035071110440d581d84e032002c0c54104080441842640a058107d20085918582084482c15108601c2580f081d000205481803944d04540c085600c0c1e5501012a0600030005e40340d801150404082c506050f401003400e40030340301d955860300e240d60038048140081d100300760740d10000340c241080180180001d0f41400ca012003403d06040d0204c2a0303211210385507502c07660041d25056502c0091000b0480f07481e08861442d98211030b014106410704900000030b100380310009200c0c840c003001c00d0440c1e00068001d440144001480c061240680c0c1402501c0d440e04e0342040402807100c01d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 625120000 1250 625118750 625118761
    0x2a0a05061807120c08030304030908010b03010b09010b0306120319020d0e0d0b0c040b040906050f0f130e07030b010b07060e070b0708030406020903030406180621050613020c0c0306 79
    0x1c211444007440002c24039585420040c074490741e0011001c2d40c1c0010b10f5000400d45000810055001b54441d03a2060600c034a42311600c2d0031a006800450b109905250020b060b0355109848141547c030b40d10507480d602d843d80360000b2150b49482048030b41c01d000115082e441a0744a00d00086401c07107079002e0310b0076500030542c00c03128943d847c408d81e80e0002180b45600c1c0441e50504005601103800e2100a1905444044069580c1c00a0340000a0345464032070612503400c09403c01e80015801743d501c0040c00050100148000150302c080608541da44c03441d244041e007080018000440d04400f610140d945c44002c02c1d103e69104090986178a030508802041401000803c041201e401061150401c0907030369540020303610161003558a1502400800c100b56801e10003000101029280d508078031a40c92000c6100784010b0340a4800d0004948030101c80c01e41100c132070b41400600c03190028296a4400014980010208011241510104103130100d4800000c4030728071400100e045804680e601d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 625121250 1250 625120000 625120021
    0x105040302060307030c0201090212070501110d02060c030901060510030b090f010b19050d0509030a02070e0f0a0c180e0105031002070f08090d05150f0c0903070b2a0a0506 75
    0x4621000b0740204041001840440c42075220174000005407002144c0c0b80525000a200706030b03020b41e1100c00c0c0d00021800c001944c0c00100e122110510400544400440c0901c06500c80030000c02c10120751a0000c0001d400620070740c80035000d41402003000380002c0c4c030542d006000f46040d08155001d00c9030380c00425000342e003841d4454100c401d4400058a44061201c520760311250076020181400f609210a035002d071480c0c0103e42c0f00f41003200c0290b894103143c0f00c000349044256070040c0031003180300c400c2c490b81c8081323120050703480f254205001c260400601400c903060340c01c4198180016000c140003249040300355890701d0484030100c0444401501c2002200100d1164400040062242c03a80007000151101d0107000d80f40700040140c0220280b680b0f5503401c0075002c0d80f140c56180c607e40104460714011400340c0e60010850b8680a09210b44100070940d80e620701e0081c50120000407942c80c1c140c0c4080000c00341002c48e4440c005d03268440841c5041c1e51890401d070f0450701e1707015500000340c40030308 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 625122500 1250 625121250 625121257
    0x3020909070c0c0504180804080a05060f041a040c0b12010311040c0806040e0312150301050f281503080712050f040923151905030307080d0204050307030c0f050105 72
    0x700420350003106891309080000070961603840c00314040300403040d040441c07491405000141605c0003c1d10014886142250600000400c091003101180c2c00340000304500c80d1040d0020b404005161105483e982042507130702d091030740030700410000002c0da0001038028a440c0c1b8101c4c0e11a04109e80416004401c01c001d4410410144002460200000c0e4070382c54135410404080d01e841041e285020310903902d000c6243e1007100d07001c04a41503d103c1a10609007481540c0e48880c59100c0d101144c10310300300b224002040100709a1908104460a20110f840c039401a10a44a4030101e00c600f42c0c1d8030b1414040c140c20140064400101e610701005c0201d00178401c42d4103002e0003000c0b040c40e1900b000c1e000c40c002d045102d45615560046250607014000e500d00050042c0c0e0310790040c00900400c081003144061030000100c0e00c004100400300720540f4000300352402c0aa001202a85900ea014600c400074000c03603200640c135206220000050001861003941640c80440c049800a0384800c0156010712 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 625123750 1250 625122500 625122503
    0xa090b0a0c0e0402090402070501050c130b030402060405010c020424181401060507060204030c170d031b0c0201030b060301090c021b0a06120207061d100504020d02010c0218040303020909070c 84
    0x4070b4420090440303140560041c911150010401800c01d080ca0301c880e401c48034102c50740b0100400019501003908200615031f401840c072400f00a1a61525502041c45402540700303040c1480f8540b0354540455941d6040700b00880c000345a01e01d1070500c003011140c0341c01028490186d0020100c80c1d82c540042141c041c916a2403a1010198000d91811800725050f910140c0281c401075070030b00021001524640400c0000d240b181204459000090022800c0c06102d48041c002d040ca004e0382000c1d0000070381c0c1e1081e016901d41c00d04503900f52903800141d000c1d04a074100598400000070011400304c4860340081034440c0c844d421103611180750f04aa40f03040c640c0040d440d90043d60f40340200701241c4500350103864010507980160500005989510940300f1280031040c4500c05541c0951109804000c440c02c0303031164000a101d181051f4011503001c0f510180d029040100b0041e4500075522100810510822545286649450301e0705005000b5008068010f104204e10350110b01c00740d103d86031071814207 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 625125000 1250 625123750 625123757
    0xc010f0206060f010516080d15060804020f01080c040b071b060f020a150e1e011a090406180f030804051203040b0f27060f060a0806040303020c010f02030a090b0a0c 72
    0x43c5001500d40d5045408108083c041c18140d460010720310001030100c5000c031800c04501001100003050789502160008400c214000003000050b9a4407205858017080030f08001c80191601d44900c801032003a074120540c541c0f0001070210400000f90304c00d0000503003001c0c160030b00390f8444404440b000685158a0016486a1030b05804900c0c4401e401d52015802040003821340c03c031360749060812483c00c4c8a41409000c569225020380020b0159201d041d003210201e0600f1214400050038040000e4006000503503203e50140fa4030f8100c0c441201815000204c4418180d42d601e40105400801c0f18221082d00440d490649514800d40680380560340c4240a85030396521902040c606d182d008044425170604030703108021000031022034034901244c02c0c0240000b803424400501e2038600c040e04031070081030322a80400001101041440e00194103117405607960b88001e007942d01406c0500b4180c448540300005200a840b425401807203014454040c0c4801642e0315104602207030701202030b40380071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 625126250 1250 625125000 625125019
    0x105041b030e07051c0b07080621190c08010608070b07022e0c0c05060f0a1107091d0609062a040b040b25080a050a03021603020c010f020606 62
    0x40c0d000e40c020248a0700328100300d4032003a5444000441c801c0c0c60414101ea07030711144d100d0708217000d1004102075001035241000042e41c100800840c4001001e030b4200804900003a440010802e400d01c000c03000400015108003180d5414100408040450711a85050350320701403000410440108220041740c0044007503d042424580900203294051031005513076181107260100f85115050f20740070701c0c0580355945001910207183c0b80f207500060b0341003180300d207000b031101c880c01070b80c03000417200e121099150804122040300301261402205402c800406420651843c1d2107a002201448a0014034402c88002d9120a014162681803d171246144a1495640303d1702000e1400c204036016001303001c0301c0d0324043c1c3d02c4c10780e06a00d07081500b104003180000a1010304889152007100410702c12064422150003950703440381c03054812014071381c00344000812101e1a490096042c2c40c86c036a004005414803040500d40251107068140e805400b00e00035008421440b880000e03254824003018020000c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 625127500 1250 625126250 625126301
    0xc07180506090a0f0902040614012601050d15110d060b0315120c06070b042303391f020426031c060e0a091110090f1409010504 56
    0xd014002132130780750310780c45003140c50058071a07119a00040110b10603020210550383c00041c00071841465107603090f030031018080d00c0052500301302411503e085512a2403050b9502d4881d04444005010070180d502d05035084240002c2500180300411009038104403454482c0c0107a0318a000944500b036140442c020007a50b18240754110b003080300340d803500b100c1c40c84e170501d00004c203141d01c504005c0b50003540300000e0008002000c001c0d1021605a000c580707426814140206ea524002d440d80d5840841c01c8907980e410500c0d00c0d810b119614040301184160641c1003c0c501c0e9503c1a41501441e07414a0183c2040300300c5802d03200b590242c032200442504010981110103404480e00140342c507a6010400141c001303030208000f5950141518270001c50210320700702c104459136000030515064030f030912004100180c08000420000c1c90115040b05414175241d00c03c032100d800f540c0000c0f84048281101007000c100519005e00341c8041140c0940c841e03a202c10600095501c2101c090100e07400d4603800e0207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 625128750 1250 625127500 625127521
    0x1e030c060624031d01060611070e06061c06030c090e0c090106170a111c050f0403080403110f0d0e190501080c070602160303021c1a01050a030905030c0718050609 71
    0x3c1384000c0740e4041c1d208450410707802d40c2107a290b40e1064000ca81082c6e980000d0390b0007802884010148414944c184d40741c0040030034418428a0b11902d4000e41b49801c0c4a1002ea855010318084c54000442000894443d81c0400c000d280322001c079480c910a01d08002c0c034624110030602c2c141d41451b0384001d05440d83c410358038000b0001401550f040703a1266094400203c0c8840030b070050000c010782c03a00201c4032010344d00e000c440016080148002120b401c01021940105195401039031500e085a659019040d26509103244012145000d0144444000c3c01540c001c00e050318001c01260b10321004103490600b186816010300c0386034007184581d800035020003d25009402c119010b5440545000302c01d014a88503400c80840c102c0101e540411615009144d445000d6001c52060004004810407d01c0030441032001c03541440c10400c0004003d0072543c400e802c40e001403640042100d03124489001c0c2e031a1078099a01640d20248211007000284081c1801014000d0102604c00c1041d83c44545418 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 625130000 1250 625128750 625128761
    0x30506150910050d111b06150d06021e03010503010b0d0203070e09032206080a140c030a0f0e0a031103180d0309120b0103021302040e131e030c06062403 67
    0x301c09003c0c05008100c21107200e809200351005103030100c1c035503d5419004c1c00c09030340e62650389106580d00c11820080700e040c0c0c1003890300005e802200d05110a10603894040042d201390002501d244446481c0d02281a103134078040c5060703690480003800210007000502441c11981035000e035040e07021500802c044010020601e80041080080d2480d0460003001c03405440d10142c51442d8208203090b042281640c0002c00d80d801400828050050510007040c0310b0b680100074100041007280000440d4002949034040891405118414440c0030700318654a40c45580d290b01c2074001c60f00c2204644400a4003000b1640072200e14044880884150018488400c0c00054110188100c4501c045043ca1020780c24107203443c403480000400b50304601c1401700080b02102c2006485005000501c40d807002801c1c419407140815010000203503a03030426524603101d0000464841b80880080003e160b0300080c81011103014120912506a59109614107405801c4041d01055240c0002c020b030988280c000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 625131250 1250 625130000 625130029
    0x20a060c08032e030b0403090b03040206090103050a0f150e0603010507081f090203090313170703020d02040212100e060604050901120302120a050c1605090103080d060e0f04030305061509 82
    0x1030f4849500100f40c511810410364000341d0380c03060903800700700c1090b50200165020300b004000003030442c00e01c4d80c00305249000c0c440e200c605058851300001d1102099900010700e0403c0400c0501540b1086594001d54a06501a1040360b280301d0300012050b003014044c440c000c448541e40c0742c6841c0d4640c205201504000503c1c3c0000002d041c900040c2104240091801011141c01940d6640c40e00c0c030100081e51070a0340400251240c84541d00b0b4003000116640003141d406603130305841e0002903c0014002d115403540805150009802c0c0440442d280740c00401307032442c001c1c40550b2611404208800c50080380b107110360241c0f80e41300600c000f200c413150702d04000780f182c0100c40ca404520f03c600405a003090b01e00000045002c030301200614402c201c240c021404a48150b90401c0c1401c0100f6911841408082e040d80f0b000249096403484641c0001c0051090001300c501604040d0203c0030107450541d001d400003410309001c2072061414100407150840f16120980c50207440388148185d03144420b00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 625132500 1250 625131250 625131301
    0xf01030b24210105060109150e030a05070303030b10090e0a1805010c030e100e03030c091201050f01050a0e070c0b060d050a0f0b09060705040b0f0c01090609020a060c0803 75
    0xc40c11619203406807014030310302c802882c255107021040304150840e20004c2186040201c180c40410030040301c00c45c1080101d000b0304e4181800280030380800d2400c42d103014000d1141c03140e41c01c00020301d0f61540c030240300c030310045801e6040e640380d200c02201c41c0c0c61140282102d44c41030310042030031480030380c0c44500350000d400e0300410084000d455803421114a11100b1020907207945a1031030400d0103012603515460030315001c22040c2d00a980741f650324000100410904400015030030001c0e80c41c0b211503484503000c00020b001c586806200460303000c80078440d060003031069483c0426a20312181c250b0348030386001d9455141e01040c0b0f440b5542100300c0640a16002581030142e140481c10501070760035042d02070703000303280e0500d41850714095500000703281c041030ba0441001e111400e5402022101140c0304a4440c58480c03440d03c091800d107101e081c0c1d0700c5101d9072038581540204511034002200c0e9900032546501d150f07564110039501003243e100010030404003000001c4600c6005000399500611071113 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 625133750 1250 625132500 625132561
    0x60f050a0c0b04050c040b060703200a02210613080703080402061902010e0c03060103120f120f050a0b04020a05040506071106071a070c0b07031e05011701050f01030b 73
    0x455100000b03205540c1074510783c100243c2414603003420700418802c1902600c0e56803508015440041c100d21483c4c90600304404404003640c1a001c0030800b101c034160b0020a101410b40000381c00956010128800c89414010391000031120041f01c0250401d550b0460071700f510b4060312382d404407802c11000304202d0744444240401d030325040e011003861610041a8000158072100ea02d2a5464400d02d070390500d1191b40030200500001e00081d0901103c94100c1c20041049101401c0c1961103000c01034450718158076060701d503030010b005034010790b001310a0910204185403080c0c0c1804240d10400650801080040200700140d090003001842894010604140c00310043d0000644550009030700795100010200703200c0010f812405c11582104072410b00040458a40e51060300c2c061000300b0a8080c16982c2040c50001c0000300c1c0380170350151003c0740402039583c6804003000c6152080b009000c02d0340c64040002c21120000c2c508a0603070345c012240303401c40e0b5500c0d525110300080c0e004208440f211041e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 625135000 1250 625133750 625133753
    0x60a0905100b0a0c0c05040e032a1b12060f281404020a08010e070302130b0a2c010b0723031804141501050307021e07030b060a060f050a0c 61
    0x2c0303001e0481c0c000d99640b0640c0100b030314204048600583e070422031140e85041801c03100b441d400403c07503500c007005440c2d4580000d030010045100000c07440a5400780e0007001e440c400c0440c1c0100041c030510100703c84044482031031300c0c0f0071a40c9000499844e1140300c1050040b4400311812140ca14115806174016502881d0308610179095842550600070a5501d00f0280011440c2145800000c0d050a0b0f0081052124141c1555902c034110322001e4091114880e4120071301d00300750011400500003800e6001015130307407982c0109101c0d071002201703074800484442c0304124000031741d1f55040b281c00080715428021152510a0341451661210070703080783d003042d1030031040700c1403000d0076605804c103a0b4002c10007010800c0c0070039070700c64850380fa00c0c8884c0c45080011541d0f1a11071b92805602c28a080740d01c070750720502c0a031310300b50486085821019018800080820000a280042da0301c0388200c00020707103800c03090181040030390185d10042981c00d044803090500c00e2000d0001c007a01407920054075100c0c2d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 625136250 1250 625135000 625135019
    0xb0d02030114070e0d1a150d030c02030c041802100201060807060c02130c0f0e06090d0819030b09041203060b180916090e04020a0503010e100501080303060a090510 72
    0x180c20110490344400c07800c000d50726802130302600c0d03030040548940054640a5940040f000d4410100e0324005241074045104c110688070754240c02c18003c3c1c00f8203140c10300380c100542080d101740d508030311910481c0c460b0711050a00d802415441c62802c001c25001c4c440a50802c0708811141042c0021996507000004113075074100903890040c0b81075101c5000c803003000d00500c049500c01456207146d080c1080d6211f008a0b90000f101c4030091003a180000ca0301c0c40180003c0d190744601d200103a4010072f40941c840c14403100d40024124903416240381c509104111805030180c0305480d2743d046e404406a00060041924040d08002c0c05900c0d140c00154561542401d2102d500000e900c0c0030314958000c811b14003410302440103074220090104000740b01150501c02003c194030350151a030034030125404101192101c1a603100500302c028000e20151140c510400da40d4400558803201d01401c2c0b50002031901c2d00481202d004440182400854608115010b009002c010701050b4041724030580c00607240c1c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 625137500 1250 625136250 625136261
    0x7111c0213020d232508070c0210121803080609090703230d030e030f0711031209030d0c02010f052802070f080115030209040314130501140c0601090b0d020301 70
    0x501341c280e900354116000600108500040140461407050703041010b20240000c1c803245070481520789a01c0315621010f003250403070142d041c02500300551a402484154100446807150031428104200b41c40a007250040800301c21b4001078081408040414601e0820310070710781c0d020f440e14045a010607500c1ea01c507800d04101500d9074104002c00c19440030441400d200813451269145014400d028410300117076124400c1450320700b001840050090100840f0060941d0382c240000c05072202e52079032503090421580a070080b86d1203401800c0844d21524081d2049a28554060351101d250019101c0300783d540383e021003584140d1920031a02e003c00303296988181c85041200e580980741003071803c121021009010340110800c0d0741403400a007400c0c8030888004085139011684a1030300e44a5080585664107960105c46d204000000e083c400b4140c820600390443c0d800780ea4140402a5050300c0f480c4900860120450507003010004009864854215402c0041c0c000c082006003c1c0c0360b8006401c50303a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 625138750 1250 625137500 625137521
    0x807140d020d08060d03020721050304080307060b150a050d06030210020a120309022409030616080709030206090d05030d1508010506090f28020a0507111c0213020d 72
    0x34840342c000c0c1091a40440207680201d8140c4007025803000076036000c1e40369074aa019803990444c10441d6511140a810035540b01e10b50000c2c2526641d40d00d80e10030940b03d500902c825950141004085106810440701000b00766518821441c141041101c0c00c4810f68454105094402d403604800300140e0f0f80c8001c00c02c42940c0d20380050000e10b006141406c0400f24028100e007c1c90300d0402c0481c0562595410a41c6030310500281a11002e41440b298100e8001c0c201c100f601841840300700103220740f1103c0c0b0b442074005541c0750744540c0e1780c4244040310b04840c9400000c0d0000b401b404252418145600c01030380a520a81c00c0d2810321080e901000e04580729603410481c01d24921340100007a0340c0130703ca01c0341c2001040d100c001091130320100c4000416805440c442503080005c0c484002e0034143c030054600c2c900c41c40002c3d5510318240d40021700942060300e050392007000d450070300c450300d14085030a040480e103000d00d009030380d100340e40801c8082844442581d010380d400300300807040c0315101d00c210315101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 625140000 1250 625138750 625138753
    0x81b16080c0f090106050906071a040804090f18110f100905090117060711150c180102011b0c0606030b09010917070c050f030a02040c030203090f070b03040807140d02 73
    0x48414104008401d00320001c50143d00c1d60f03801407000c03070703401011140842006d83d1101c0c2d807807100c1c1c9064169421210a0410902e00d600c05000402c61424001c001725060307000140310380c191007222641100c400d148080402c50f0350420035000604010f54220b0b1012005048c00c003103102003004250311101900c2c2c8400000c2c050001440745c2c1c900002d1190260404412001c0086100d030021551000b024180070140041a4040300b090340c02000750007403c1065600c0c84040342007000c01c0e241d040d049000001000103841a0182c0903500c144540610684100d441c003490006400080d510155500c0c0e065407144d03203d900110128200c1240d0324050702100c0000502c080742800c052420b055411421808030008100a00c04030f900e402104048d00e404490020100b440c42000034074080c01c00100075009070a04000726000c0d505980a18070440b00380041e0381d80c00c541086945e440c1c0106014085101605101080204000d080581101e0b88540c100380340400003150520318280c40709107a100103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 625141250 1250 625140000 625140013
    0x6061216020708030c030403030302090d0618030f170a1a191409070e0910080d1106010f24050903030409020c0c0a1410030209040903030b0906030307081b1608 70
    0x203904202d11001486108040c42c103192030500307400d85900c202e110140400d6004039044513295524100400e1456015104001006084543c81160001b40c00145c01003500e80d201c81c1100d07801280c1c40e10340300c2c50b10340d9144040d0382c0726103155000702200c100d401e58121003800c4c00891510344000034654040070038080e80c03075507140c05040606410381100301406100507170103001e4560b410038107442c102d40c403c4400140a40d240040760410303070740079405004035100c4c01c03c80500341034001003070424101a4030161051030780c941d42101852407442c03080c2c15034104060904101283d51524020f9500f0b200d1130028a800d8804002a1842e0000d0704445c080e6a40051421020b010070050706400f01d030300b035462042c10380c0303412200c49900e402021914083c1d8021030100840c41d1080c0e045405c3c0c0380008008012120b1981001001080c0c46080c46014103005004240d040c903001066030f0300d90764840005480c00c03d000c075482d140c032500d00480c4106442094800d107046441d880441c2c1c00340081b213000380708 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 625142500 1250 625141250 625141291
    0x150c06020d0903050405150a050f07050a0b013213020904091a01080c03010c051918080318041802011b0204020708030628091d030c1c0e0307030b060612 67
    0x2c1c7c001c68190103100b180350410140940f150044d0545256000031014a03031180700030708019040c210480c1000b012001c41000114106c080b0740031601c50400b110b601c1845801240e0006440b0071040d055195001030080c0a0000b00c0302141c00411710304d00064004541e40000342d4030560402d44244403456a190800010f22a078081003201400c0c10604900a025060f940500909584204199260099012070b00e540003130740a503c03071804114600e459218081c1e682d44045841c0d82255054041000c000e28010b4440c2c5014002e0080c4090301c0b07541820b081e50180e00645140900c0009044180e04c064510340243e6643e00c040c000b4a40100c100726035902e0a00100710500a100d2140760070843c20040c030818540c00c0c4222901514000b080025140e464a140c54070300025050b0ba01070584400517080002041c00b0440300004400c0201040c245001c44130141c3c0c580950502c1c039501580000c0341007001c9011260702d203812035000b511440c40c100484c0300d040c1e004402101c000c414072081103010030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 625143750 1250 625142500 625142509
    0x110901050f1e06070305340605150a060e0a0f0b12040c030f060209011407050607030f0207140c010201060f1520060a091412040b0d02040f03030e0a05060301150c06020d0903050405 79
    0x90440f000c90411f842002944040c8900480702c80040c2210740c1c2d07400000e41d68002e111400c40c1c0c400c1e00402d440318140d075890300100b00046024056001c0d200e18403000070440b81411900d8255091401111305201451410b44000c0d64002c00544440320004400004600b480e120070701c2d41801440090b03640c1e0380200016122000d11082a010f462040040310003141000c036220307802010b00e05d17000c61a4000e102400380a4010718602525042c0541040d0354507140008021031103100030380083c08081c0e43e41411110b115218440d2218a04400708500c6610384a1401c018506032141880c0031110891004a4074084040724040d50319643d0328442c10900c19046a1003015078002c0c0c00030410400450056502e5000d68450031751101c1c00400c1c4a05d450220340c0584000d00b5066442c600019500d04005004580c4d214840c3d0042d0346000380801c403400c1020899042c0da1815000200003245500200d803100c58114080d07491030786c288800c2c502030805004506d0114060358a80740c03218106030810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 625145000 1250 625143750 625143787
    0x12020c0603070c2f0409061e050415090804090f06380a05120c040b120a0c03150302011d0306150f060301061b03120216110901050f1e06070305 63
    0x4406811071004c00748107071000c1140d19010428203403004100d41c24289401c002801e00c0b80d140c0c150030161031038013039401201d03503222503c55402100c0d81c3c1d420440001e0040b0446040c10030103440318204001c18450000107411240b140e4141c81d500041d40c0c1e075100f000d0303032100381000071100d50058203202c08031004640000480584c1c2500d20858500f005102019240340305000403043c0031441e820011f08003011800548000305481c0740311a54400410780c0e00900a1400c484140007903150080040e00f003482071141054100e021341151401c40c0c116001918030702181d0408800782c1000c600c4146981c0c4090128600840c0031110701d110000c160b600b000340618500300f01e0ba0103617400748010000150300946800500a1070b402503a0440854242110500780540d004411180000383d0b1001356140482d41410344d500841c0d10b5102056154108050110280b1407641c7c4070404800304449880c14504483c2c032200c010f0561000c0300c19407400700d400c0e0341006070280d011502c00302d00c0c4c4d1071410041101c1e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 625146250 1250 625145000 625145033
    0xc1109010617071d13060302030f010509160308070305090f0d110f060c03040e0402120a0302060117061e07030225140601060206040b0406020918071e08010312020c0603070c 76
    0x1c0200c1c07425001c6401c1c03a0f500c6004c1803042c0034851a03440e042c0030b10b82c8820301464000d81590f034240480010075000e00f009440440161103452032070107886680d110070f01d05895002040615210090300d040b42c864000b03404282e404860031105400d10b83d2481c0035500928070540d1000c8080603100200045800c03200b402e240103040802003001c81400110443d015503c00c64122500c54841e400400e42c5007200380d02220781803040e000d8400070325800251081c1240d54103200003242c801584031743d54649505580f0340340c0c40018201c00072801c4240004095003d203a80c6801405d082401215500c90001400d60600031610b11800b0814003030616454814508400000c00380395140450003965810020800750031048480d0103e010440075404560b8001002070081001c078954624100310b00005036207020115190f00702c032070741c250a42a80c81d00010400d449103d160707841c6454185001c070300d0070010f20031400342181d03624040c5d65003c05107000f0f55286d40c800510005500d4051641c9201c1d004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 625147500 1250 625146250 625146257
    0xf070618050d080307050f030a05060906150d11090a0936030f0c02130b0306180a08090a090204080f0c0d230a051902130c0206070c110901061707 64
    0x1000e0240340c403020640d00c02c00f80e0040180e40d803540d4544044a043c0521070701c20038290000001e00110180d03d8102500410040301c04075640d4590400f00a0800506860380e00c0d0820280004008a003455100e980384003034030201c55160a90744000582003252640040401c1551600103540c0d20044107c103202100681070085200740060fa194500803808110043c02c100d1800e500d00c958a1151046150655008d01001d14141d4640030010140c400c1c1c00c2e00328080e100f0000040c400743c2e9581102101c0c40f031608007801c0601c40c01d4450905940c0304064542d0000000f03040003c60003c1c0c0d100a0004001a1010340401b0007102040f80c00c0040803075041e0300c21406260690080b0b60f00d60b90b00a45110310207043e051000c28000001d0500011020103085da000b500d440b9100d80c0803859011041510031a0343c50003003280c541101088514503070000c0b0041e0300210000d4001802a511044c10500858012941d4440000081d5402000740c000d680000c504602d00500c040001c08115000001400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 625148750 1250 625147500 625147547
    0x10030c0b03091e10020412050606042a020a1a0907080703050d030c0314070e0a0902121302061312021201020309101d010203040b01030b0105030613021e030f0706 71
    0x8031055842d42d080010040401c05600c015035500310804c02e035481014860030564803555103a03551408803800c910166628001d28001074503503e040d11401c55102c042e4120b50f1403180f50400019142c034014000c41c400d43c4581c078500c10105548503800c410304446c080d0b0303101441c1380135288582050442c1d402600c0d682e02c031000074000203001141504001000c0d240c002241c00c4441000c0740076159000f100c0050310071781001d1049540c0c0c0045051900719003544c1c480c41c80341d0340d011243c1c124460300301090310250140c40403072540d14464049041d8980000c010505041c058010140326111aa00c80e010610420b40303144114205110200382c00f1103403400841c29860040d0502d43c039008268541014240d0301c10756514620000703491002c1201001008645a150915045801050038081500c03a0314461000103103d04d000202c25218540f44004209009640d6081c820030715500300384419106819210940390782c40c104417030f49481d05110000c24a0a150510107004100303200706003000100100c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 625150000 1250 625148750 625148761
    0x10f06020f061f030605090601080d0f02070b0f0903150a051003030c020918031215040c121107140105070f0e0a060c061104030c081209011b0c0305010510030c0b03 72
    0x4503005502c800100c9003c50707404076a070090f5504458076040140b00c5494007091040700007001034060305031401241141e510070b0712400252003810100210000582c0040700c140507020001c1c014103081107401400b0b82c00c0c804900006414140c485180c0d078000e030419800c100041665004142d003140e414001040040e00350f8a0007000c0354420b50010303003c0c42c1c4d8400810411110a002c030005030403c401076a80325240413134100a40041511130b05954000441d03403103681d2400348100d5100300071a0b1121002c00480010060161049420301e5122344400d12820010504041c0960700a0459200005507403920801c050000079180c101ca02c00c205a80d0030a0314240c4480061006440c201d06040c00031045a1414501800300c0001000d044140450300100300b0855200c2c01040d02e00c41c405440c035241500904840c03e029855540340014452445d180312848071628988505005841008081c2e88075101c7e00c0c00e41e003080c3c80e1203120003c418000c1040c40032040001d40070b42220301c0a1844c50030030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 625151250 1250 625150000 625150003
    0x501050406032001020c100c053f160606051207050604120203010209040e1c020118120512040c1401030216030318150906180507030602030907090e0303010f06020f 72
    0x316480c118a03034a120f5091400c2e41e000b0441c00c608007800521300c462403507061400a0500d00700310011030f51803042901c03084e140ca01321454442e02404d62084241c1c080002042480040c10202081c0c8283d80d007008450103104401c0d2201c54094020003002c55a249442d0610101441d90302d1183da1507084940300780420b43e41c03d81190116180c1180182c1d1071200f500000340207115103440c60b80c2c09454814004040c940c003003280703401c40c07084d1483c5000340d0083d050107034282d5038484110700c0c0900381c451110b4002150951070411a4000e0300c0c1039420182086420b0a141100361001d90b82581038032010400ca449aa2910074803580a180c103504002c0c0d560008411440c50f824014107064239107854001e4850a180310804540d0005100c0080c0c24845280000a10b80c558056440a082a0502036060b0180350f00c0c0d040380780e001c40146001441c0d501c0e00f0000b504041c01081c02c1c0d000380100014480042e02680300c1c1000f229024541d02d525020342c9002400c00303a44080c1c25034010440b0080b01150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 625152500 1250 625151250 625151273
    0x15030803160905101d01051605011b02070f050d03090305150406060605270f0607060507081302130e0309100e0907021f020d090b0403020d0f08060d030e060427050105040603 76
    0x30701602c001e4010041c07005072081d0040d16101f1946640340342c2000140b000540140000bd40d044400136102c46407480d01301c0c2c450712140203c10a1810b40401080301d030401000c9150111701924244182548075624a030420b0b94540d240c0520750f00e208188014050030b88151401840d00e403c015150045000340c1411704481090f004031b0444074400c0c01c0c0d1040c0ca80743c28034008040020708807640c4000514100e001404251b40000000300d81c1c1c000034000d248010324010a40750020915143e821003140201c1c05040302408010a500007032003040c0b0541c5503807150b12440d0106460b0705004403052014800312550052010045520002042c070792544c80c420300700c0c81c000610728050381e0341c007810700310801030000d0341e000828918044040005041e4041210514001250344015001d88096000c54080e8025074400d50300425030b64101c2c0000703016490401ca141c2c005003000d824142c3e00c01038148030b840703154020203040070b0301c1c1340d103074a6044c41384a0940541070480d000c100060460312a10810030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 625153750 1250 625152500 625152527
    0x2040f0611033a0c0c110a2615010b0f070c05031002030a051024090e040b07170c07020f0d0215180103140a1503080316090510 56
    0x100d110100090307a00c2401110f5110003000c001c0c100649040722407401030300100c1016142d5a920340030b0501034900e207004142c1d0740b14540e13468030b0000c0351030f03102c403200300c042c09483c1c1d90700c401a01000074008000703040754040c0310311941d02c200d0340c40c038030f80a0070703042600a5180e500755003014001802900100400d44600c2c805140516458010030b00e03144801240e0f60b04195814401d800d04030382c98200540040d8454007921106002e07989071414200d540d07400500804080320b1584840c5420012940401c564014282c035080d510165101c0d05044415002d1300c2c20340d9130000420800c241c550300302c4d15070029071a00e09204106407404040c010b50314014001c0007440382404e110528001d0351740c5120042c403980c000305403031490140704010683e15448a40004220800c19081044942c068850064034843c1910540155a0b07881d40b5070b8010402d07160320a80001c12000d0103c003060706140038600c0340c0080c00e240d07646483c8140c009801809168001e0b486040c8021601c0c0350700b075100c004200d002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 625155000 1250 625153750 625153757
    0xc06130b090a0306021204020a0501030507090603020d14130b060a080703060504060b04020a0f0305010504020a09090216120801030b0f0c0a030509070503011e0f060b0318030d02030f0f01050402040f06 88
    0x501407900019180115980040d01060000c00c60080c1d0666000c0100e010354802c4400700300280c3d0b50f10065007a200b088a1140c08103a001d201000b499000e60014150482480d4001a800c150300441c802c904105803900381880352001081d40412440c3d801d1681c002c041120816011881c10450070382d00d004a010052403907456002240801503240c00202040381d00800540d21000030990080064840c1c0e410403000909020000030107040c03074030072600d1280055407200d580c0382c1842c49007806035206120b6a405440194072000105441c080c80f01483e00c0e0350b1713448011651642c02c0504d6003100140000155465000500800040c01030846080c012981004102951000c1d407107410304103a9480113406500b00002c1e40440001c180d1081841050000b081028151996417801142e01c20b00030b00200040420101c5c01300100c264911299805103801c0341d14082c208101c45080e41c005503050072486058205120f16a190f000e5441c0c0540b8040c0c0c1d04504142c5016541020740019120341c40a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 625156250 1250 625155000 625155007
    0x30b010b0f12070512010608070f2001060b361306150918110a0c0804180504020103180209180f0f1f0b0108071d09010312020c06130b 59
    0x41e800841a00c0c2d40c02200210744003545801c820103011a84021943c180200042c030000c03400e076000d0130446014070081c0d0380b075802c016102d15017560f0940c3e05807001e00c5442150038812030281024081e442c0a0700380001c2113503e51809440c1c0480340c01b242802c0e04c040540b03181078015140c68038204046000340c2280c03441612620201160000e08030754026019680340e101002511036045a0420304994a089d8482d800c20040043c030412944012070321100d1100401210302c04a1041c102c0e9076409000d4070445280c030781c2c1d5a207011003401c003205501c407000b070321841007005660302b521861310305114060410b05d611803a940000e022460082401d11f01d49400c9540e00c1c0312031000c224500d80386564801719000210110500ca50300c4442e02070f241d90032000e600c20304101c12043d004040000f001a15042010740b20f1a0b01510008100001044c120b80f4806222000740d80b440754081c000c5001e405088450101c01c18000d0401941c40c2145006000401004001400e401248002c8a1500d0860780c2c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 625157500 1250 625156250 625156267
    0xf0e0607020a03032c03031921151d04240504080c1c050d020a1e12060f08060412021e0d0e0111062403030d021e0301030b010b 56
    0x10940640000650048280b200200400d6001440c8030303a05415299501031020ba0003003e190301c000d45284103a0150000e0011a81c0c0d480c803580074210310040c5043c001d00404110a8150201401e8400e05d400d054884461b100555007542004002d4400100b0110f00c041c0641034043d0b009802610080504891328003c407100740300030784207040c8501900e20900c180e041070709050f02d083d0443c1d074104c4c580307002c0c1c2ca040520450300001d01c1800680f040d2296400c180841e24050300a40100d41102d00748a410404000300048100e10503200c4803403a11901c80c111102c4d0081001c80b240d9802032810080c4001c0b0904c919040004c407107611540c41300d0920800039940c0070403814043c41c03502802800000745a98028810007040c03042c1141c00d1a611102030b040c840c001182c041d240e003007024055401c40c2020886400d401d440c00c08d04c400740b0410403041c0d0321903600441d00e140d104511503484036901003607841c000e2005024118500148071401411035040d0381358030340940c2043c07240150000002600381c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 625158750 1250 625157500 625157509
    0xa020408190204022208010b06091c030c0b040317070203090f0402070606050d0c1a031501321b0703170315060a030608010e0d0801060c021201050a020c0d0305070f0e 73
    0x281c1084005003c514088100e003105900c5c0308142c0580f003040d50070b0080051a0342404425110380c45001417807441c45010390295134015141c5082c0640800a5808601010034100e0b002180100d101c0c0c0d956050754071b0100714809103400017805820854004102088855845100303050b03040c9002c0781c0040c5c0c0c0d0041444d08000038100742d80300680049401400d44103010a41c00c1903802c84450040341481040e124010344914481202d00400d00d040719500c030310855115440f02c0408456298000004040442c004500c0d14400102e28480c03a9000a8071202104140e0507054107628000c01001c2850131541c86101240418a1a101c141404800100c1820454105d558090006445140c4d158074420303009000e0211802420380d00d40c01c0004030610b004bc009a1590300c010140e550a140f6428034400320b9110450003016680314500c0c1d418464800c1c03003817040e6801810081d00059441100d81c6840341413140b031004c0042410b00d4070080210f20b54229a07507042c03030082d03480d00986007203032080000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 625160000 1250 625158750 625158757
    0x117210d1d0703030e03150105150a022505040c08160807050d06030f120e0f04020d0207140d2c04091e0302010b09090a0f060506041b05040e0a02040819020402 70
    0x40159201e0820008203144e003241c817008030510141c09a4040b90720318a008010300c030702032145981154490703050000c24078040e0080c004950480c1705442e6401810445c1e68240120710044945141603c00d080000b072609118001e920f640da8141014903290468450f04000000002241440101400501600e10650032509180304a080c204409616410300c24141208036004440070003c1060b880541d50160361200c429a00003403000e0f0f24a5009420310005e50400807039281e07031503000d12005c00014035440040c0d2990303e0075030041c0981240820014101d070324504883d41c42914003540075525610750769890030205000d139004a0403051510744902c0e07001c1d81d8949484a01d40301c04440b42015810741001c8910101203c10100c507448244a072900c50000e20700c001c00b50203c5000400015645400c290380c07108008100142e135802030039490b6900c4005d0042d03000000d070006800e01040c40c0d80510542c2140c600701c002c6040600f01034200e03583c5c0800b408078038194842c482c0d92108564544d0105c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 625161250 1250 625160000 625160051
    0xe0a03021005040219030c0303020114190e030d0204090e1c023711030606040e030d270302030309010507080609040b1911040f090504022206030204050117210d 70
    0x1e0038405c503541e00301034035080038601013140194241151440d0000801d5403413406040444c9807820700c20801211a8020101506078030202d010a01c10401030201e1880540001c1032411400b040114070101d00030305000c2d2480d03800d0506d80a4184010115500242241c0f80341d11603400506030500040300b03800c3d07940b040d80d100907406104000300c03400c0204034540ca03007648406a04032000c81d101c040070071058908001e103c0c00381e94000e2103500c1c060302c00c1e074011100c0413148039203a008210088140c218a610b4249040c0e015910000911003048824401d082d80444a8a0845018280400050594900a80094044d1000c0400319500d035620400181010802c1030b410090f4089c014590700150f001032061400b6010032410005842541c2d0080c01e104560051110492203d0496003c4101e0440c0e20851100c95540700d0100058443e84602e502030941100d1980d060302c1e030060a50b20b403441068115031a045000003000700142c02d4016100902030115010520315405041c491035801981c18 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 625162500 1250 625161250 625161289
    0x10050d14060a020a080f091f1803020f150903070305030603010e060a0b0112061d04031404030602091f020604021e030a0c1d15191e05040e0a030210050402 68
    0x6001da0100d0300c3e8000c0080307078626204c1d4600c1c0d64410140303c940c098125900c6545400405885100d80d0b64800741036031881c480d4400180000041b9600c1885669185040740547e00070740400540c50800c01250104040031103481c401031820b05400c603141d00030f142004003480130100108000b5542904000c469548085c100d82d01c42c5130410769000641006440303a40440d40690302036101c1500c900801c42543c1c0348010414445180548010400c07200030800c0d0200406516560011916100100000c500440c4d0143c1c0b140f6203c41007081001641c04a4000302014a5200c0342d4203130003203020340d07219070101c031445020440100741d021400800c00060760b042c0210400d0750100228036518074140c801100805010b420004265555000c1c1038840301c030401b0030260400301d20b14140d0001351040710102c24401184391380300109400110316903600301e425101e4007014841401c1c640f00d81c03103200c4081c0009280003282a01c02035126998200741600a6480d00c001a042d5100c129064600d10760284 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 625163750 1250 625162500 625162513
    0x21c0e01051c14160c050606090402010e06131a0a0f080a02130b070605060d2301060f080d0e0103050c0f07020a030804081501050d02011209062a0e060310050d14 71
    0x40c3e95607a0407000f2541d2004d5004010800780390345114078600031010303500400400f101e0320b0300e40801030283d2005104038104a02103281c000507480d80005400b51021103c1d030366024904121010040f1454100c1c01e04a00d14140116400c580d03210080380540d04260411a80c140c0360b041c08030010740b00c0c1442001241e181d0440c001030940e17130940102242401081c0400042d201e080400c204203610246c00340c01707107842001407038507040d07a050b8155039507015200000307400b5039800d8a41c070302e6100342d400218140c001d060000c01c7c080e007005030781d0b0890300246420401894100c10011040c09111031141401c2008212201151a1995110041c680001c1c02645481d6502c031049e56404c0c410108401c50390100d00000390380d040010b40741c102e180c1d0584541c0c8840350043c0000b0300030010f000060f107020b502ca410480801d8400d001c0407110004050401d170611004490142012001c805018000c5c4004c10030030010f111000040d034280c410071a103400f000b81e440c0c108220700501c03290040d6461701a06 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 625165000 1250 625163750 625163771
    0xd02060d05090a0203070b0705010605091005010f020a050610081005040309060c05030d06121707050a060506061b07050a0828031701060305010504140402010c060506030f0a12021c0e01051c 83
    0x7440030302340003882600240b10050f1140705000c4041025205a0400d01e1201c1c2c007030180d5802100d1540340f241d121310445400d0081034640604d860310686041103581345849050001102c240b0010070204a04a004d001030308144e41d000303148506901c150400c0140488925080007824011a5807004802c2307018400c80ea10b44903500f84c038007050301084800307060f0b1108450f280c031803100584084c2c0390080060207020032280c85041c05442c0080655500c00420002c0164200c2e400e14480c4081000c030006140d244c2c180403c0c464045000d0300300f802658403445103d507108a407407c9a80000c0d200b42c0c80c1e24100c104034641a18030448812003c58008c0004001041e000d40c194000d9041b074400702d9040c842c0388a80d400c1c0011600003528080e000854040b400c40204074150031070b40d004080a030441d80f00a02d241001810305800446c11501505081036107440c2a504102903c0307216260001ea071342205800102404104019030018140311022400c0001240c4911512a003441150001e000301d1414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 625166250 1250 625165000 625165019
    0xf0f020a024006170c040513050303240109050d080d0617010b10080708040f17070f06050108010b0607060c02031312031107053102130305010b0d02060d05090a020307 73
    0x10701c03410b000710301d01080041ca10001e01c05038109900020003600e1354416420500020301002080d010008007221004000540100002c5100b07441121290310400b414824000c0102d804c21892810840e210005001031743e00c2084000314141d00040941d510180c20fa40701c0c000c1d040a82c4105901489813840e05989041904196510401164218490941610180e8034040256a500c000424500000d000500e103800c03040c800754007030381c02d1850200e411008100143d1242c41d0445165180e509070304208561802060b01521a180080c000340b056403000c1501ca0082a2015205a8603070968018281c001d2088440b061060044000c1c0302c0e890305035200c4010b0b60a00308800290b4200954244410041804000d80301d00030310b1210303d60201e09504d8a11420700c54100309022001299960300d81c0d030341c40104039420180c1e4000c202c180c44c5050250850f0900d000309401446840031403030041c0d03154000c0382c0107140c0000300018a615011030151502c41185802900362103403440100d4182e20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 625167500 1250 625166250 625166359
    0x816030504110414100807030809010806010c0618020906030a030e06160b1302012606150c01061409160203030402060c01140a15080318040e0a060f0501060f0f020a02 73
    0x40c00c9840085c0c540d5582c03811030b03170b8400b24070018241070300c1481410401d6204259913500054140b401c0200b07141d15448110441380551542d000d171040e072010090840c1403c00308958045000c40140032810f1031f41d00d0140004501c0032016200308400210000e400310300d1106e4904040e00511100424075112402a408402c5410b0a034040f4091120f520031030408a40000d105c0500c08030044181d86401d030500c0400b001c80c9071450b50301e8600303100b80c08100000348030f20401440c40703001d40342e103080800c003d001d42280050320300300821401701c41a82075a500003046a4002e0b5050381c1881d50f40380424400e42c010b02206c20420500900c600c00c1c4041d00d000e80e00100840b400450009140f183d46014141c0d0340e100d90240b0211048614220030040d1416610403104a02a030081e640d00c1040b075aa001c0803503007040140f00d041d5039138900502a40381d2012941042c0b6200d13044c4840619624a0041d40d1140380c848001e201d214044030140180b02d611a0b0001c1d000d940104241000407480c040c00c446d4074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 625168750 1250 625167500 625167511
    0xe180a0606120203130b06060c030f041e0305030f03060a081b03010b030f0c040e0114041a07050715110d14061e01050a050a031107210816030504110414 67
    0x3001c0460120001c0c120340300304c0380030b418614000d100c510b40c5680d811440c0900180b185a0046c0705000e409081c082c1803009010000030085030a6035242025110540c0a200c090b0000401a0541c002d0000400c00822503007000400c5092a880c0d50303a43c400107a00b07807007503000410305008545801e83ca500c01280412a005c0c0c00318020300c20700d50640306140e40c50782c02460705102544803640e01c3d07590f030a140d488900840181c070008214510801d0385258600410744007128501c0180d4007181d10340049070356240c0c11091601d08186050302c6600c1d20580b01c01034112004c040b640d644103060ba0100040112440001114006e100710b846803d0842c40c907280803550b00b03008104009004144580b2031401144030a0142c541c03508040300040125110b401c03c0c000750040c969214808440405545d0180c400c482c41a083c404025861800c0118000400d4000300103101c00c98081c88840c0c0942090400d6120319840d001030382e581d40381481c0348801d01d60503015410a2408000c610b400220449091294 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 625170000 1250 625168750 625168757
    0xd06330e040b060a02012307021018140a030306240e0a0e01061d090601020d11070b13140f06041205030f07060c1e09121103060f0a0b030712030e180a0606 68
    0x44500e84c40ea0701f80c0d90440e02c0100681100c04154003281c01c541c466140c100e410800d040413401c59035502d0803003080a002c0381c01c1e00d0340074048420405501d8080e1070301600d104482104840760055100c5010501101c62100348800d040300d284164690404280040980340060f18155035141009031400044042040354601a0464002d160a00030700b0b0301d00031038040c0e0050a80000740c00c000c84035113120181861007802134030400141611494060104000e111707039050a00c0d85071103610044200e4030302e1030720b02945406001a48582c3c40c2c07800d580446644bd441d540c850005403400754110b200f40c90070701030010b901061071010300225038060540703a14544c5480c51483d1310600d80000c0c0103407416502c0c0004c0c000040c06d00210150f40004594a84585d007000c0120202c3c0001070304109084443e0600d40c1840ca04005151800f409025071907102034001d00031440c10030702e0780b020114071460082c0c240308a03101415559151895814003031540107054048604201500c280900700c01c1c81150b002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 625171250 1250 625170000 625170041
    0x21070c0c12240b03010c1103030c07020d05011406040615090302060a03060807170607020a0803011202150703030c02120f1207020c0315070e09090606150c030d06330e040b060a0201 79
    0x303d400303624510807c945820040d8210794a000d40c40c1802d921028080344c2008540d541880002c6090054000016054400325024070b031138000d00080b5a01644403140c01c0c2428140000c591303412008281c160303501a90090b54903840c007078042d0b019240580c0440010320031160005950740c0c0d030f01122016103514400396a640e40710003508980e40e01e400b01028048070010001004070f0700c4806500c0072030350710241c0300e215002042c0e941c101054108000a41c0420f4039003805c41d10095040c04101103d10b000c10015040c1f070284031103203da03809810b030410000d0140c00d020540e140d00030000c80d83c001000a00b10303010503403403040803e80d904007030f50354101241a090440f04035107020b1005610800d00107008200c0c0c4c3d90b40100300400c1c1812005000d02000d03003080750300085070040c0000c0001c040c601c0004503400d032901650881180f13815140759403030740d81070a407019040805a0080641c681601c0d00402801150000070002c2c50000000c0360f0060700011880301094040d04050a00380614549410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 625172500 1250 625171250 625171271
    0xf070302180108100b1c1401050606031e040c030203030415020606010f12051003060e0106080f0f030301051210020316110109080901031e0221070c0c12240b0301 71
    0x1200e84007070080c04203d030044c1c2c45500184600ba030180c1400c0900404036045da0010440c0080d01c040d510b1001d031408419a54040f01d003110900845401035400d403050380ca181f0740034060b00540202d079020780c4805481a0045401e00c100000e015018580003000da07035840c1d070b580581410401c801e54900c805801120005110740d8043c01d9280e60356841601d4641d86407141c2c42c480c0300180402403506c40c1c030141d01900072010544130701c242ba1002c04248000a001410000c079a49041c1461944c108998421441252400c0011003500e045a400f13480c06402e9036601607207541001c00d0b0b100004010b17440402041203001c2950324620302240191a10340308001503070211400c0e118041c0700900541010040110203503c290f00c04070b04004440008201089003040c90702c140d0f0301c04004640d001c8010038408802c81850590f0580221080c00d100000039099a10003a201d60345100301680d90480140820030720011001d4400c1c1c03604000b08500543d0f14040c1410020002c0701d01e4039000b903180503c02030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 625173750 1250 625172500 625172539
    0xf12010b0a11011109060d021c06180203010f090e120a0806091e041e05030c010e06011d0a051519080c01031a0904030207150306060806060301030201050909180f070302 74
    0x188100b0840d10010b185c1002182440242da02501584400603400c0101000c0301d4032081c00500d0101600601142140c40e0460700300d0f00032840d0a0001802e0720400040045054004100040f10f10815001c40c0002803c141c650910301c1888041a400c0e900007450115160321640f000d1088100722807a403030f00d03101e80c11591221a6040c503808103100852001c200451507190202c011840300790500440c544044d51460b09540209401080c0e0380c2d16841005030120301480218090100c0e241d485803604c0c10801c1890600d038000c0c007407007904c2c0c0c1e44d0000b040c0c2400c48900708015110b00178001140015140c2a001d0722244035102c1c0030210b0003107a5100d02e00758440e004601a01c1e00b014a0750230308921850800401110161040b03042d4854041d0009182030000210102454580c0f00095510b2038182c01500c0180c00415452058108100500051b0707085400d44101c080c054035442e64070340c0c8103200241e003041385210000d660300c03401114130070702c800025284003078901c00e42d01d40002103640174020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 625175000 1250 625173750 625173761
    0x20c060115080a0906060f0b07050c010305090d030504051009080d051602030714240f15012703140c012019050a080a0e04140c0a03020f12010b0a1101 66
    0x9000003054840403070980b10fa80d801c4403654500813100010350640d00c8110742c4c05034074254441604614007051800600406104040401000382000d21840c60400200c0c1d40300c00c0b50701c41d00414140d65101150a1101c10045a24503884c5480c04000c0c1c8107030340c204541c10b034010700d841c0040c050a100c000707041395410000070b8403240c001350020760500744695607541e04c8101c00c05070310605e0f10515012090400031080344001ca540c0e626141081400c00d105c0490444000078441d00c103064000058100590780495065010390049200c410507034000200c10a103040d503076001805005040d07880f54075920003c034a400581c0c4098071003101d2400d541942a00d075230520303c2c1003219a0001480c9041d40010300c60b01c480c0c0d035440b410981d80400150390300c048860300101c00b5080059482c09204000703041c00d04c0380181e03540400c1b0f812203440c58101d60f544240d01c02c0c02d200c5d604041c5c0100e41801040b40c01c0080d1081c2681400040e1255038603041d82c0101600020041000507482032020740e070603101841007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 625176250 1250 625175000 625175039
    0xc171005150d05150a120303180602042d0e090a050d02030306031501030803070302310f05061201061d040519150f051e040e1015050303041401020102070b0a020c0601 73
    0x72451042c54405900e0301c01365106e80c00d4040c107864000c4540503405540580f00400c0c4a00700041e00c803820080440f0034040c00d0220398903038a4000c1c5020f03592400031181442162a0245400401e995440c0b41c6803d010003604000c041f4414282e0801009801101461042c0c0d02901101c1249030306003180030b03903454203200190850b8801c10220b41d24900c0b0740c00520f043c090000498032055403504140c1d011004d590700701e105c030240482d401c2c04882c00c03804002d002040111041410011104201d40b00c114042c41a00180880449800e00300e41404c0094050402e00402c100700034608258810360412101171914091451b008a0907500800b40c004001910034070120301a000f070800060080114500c1140a004aa800780b40307070b40d0350f546014801859103060064585c020707030300c1c00d0002640c60b42b0508019103454400140442d84002040c0c0d0200e0f200100018010701952005030700910400c0c8003c4d00d8214041700300100902246c00800c1b2809400040b95026a0b84000f00300d0140c2007001d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 625177500 1250 625176250 625176259
    0x1030902010e1c0821150306070c11040f020c060c04060504031704030b070507050c031902010e18090a150219080402040e0f0c0307090c171005150d0515 67
    0x1400c00050a000d85003000c40a0f00c0f007014070085080d5169800c0c0e981254060094200d02481403600c0107140010780c9401c00c1903080007004100150001a4658100401540800c44a068400e0502c503101e010800d02120203041000f0042c00c0e240403c0c042e501102d00d44c14248124800304940c014020102d500300c480a43e182401d00d400c5541c1c46030b49603001030003030065004c04e00c00400400c41c5800700c98012030460721025900d925619185042012211304c1d18440e802c00c0d1650502002c3d442c01d12a0a140e092030590801904e100000c0d02e4000b40c0280e103201d0b940d0030f404200c1040c400040c40003034107010740d070090b85146411907568142d01c9111000740189440705040443c1900a011494025200400c00b20707009450702c1e400c43c80c1c2080402d40750303400d0348008148070f014282400301300c0c09810412024403c014040d000906a808032005086140b4070500000c0d4903051b0041010002d80b400074001104501c001401790b140c0e411001004404528240c085010030190300142c0344490000741 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 625178750 1250 625177500 625177517
    0x12090102071e03050106170d090b1818010e0f010e0c0409090503091503220803040212070305061f1d0c1c110c0d09030b0c07060e0a0b04110103090201 66
    0x4180100c2c0e1011601d900600c000b880c00040001340d028002c420290140303601c4002804c0c0321180e55403610184080da0018801a000188000790409040300e20100d040090b4407508030030301012a080000c07029000d40c81060441c000704140c010300d032005024034900004a280303641c0f42c1c071080300324200c141c0700e400c5000400c0108101c260b00b50b4100c6800240a1400c6c6e80c100407201e80400d103508500c030f00c0380b003c20070000108007203408420354400720140340e5400380c500b200c41d940d6510303007510003d0006032269101c0e0b10800081d903406c00008000d50745c880c05480c03503814808080c604210301c2a0b01000362580d1403001082202c103640c4211006c0c0c2c440c0d482184c80e611003020b400d1140c0e1100d83c52416010710a403554481c00c2003400ba41814482e02c100d040e50f503402442070f0a080c030780700c4081c1000b04000428100040781d02d0108003030b0051014001d0f0f40d40c842c654500340e00202441c25101526008110b421400c0c045680c02440c41103008008032034403540488011811180b0f0381d080240402c4444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 625179856 1106 625178750 625178759
    0x30a03080601091203020a060b040e030c010903081e06010c0204021306050c100c080a02180a0b1201091e0e03040806010305100b01090302060d0f200a021209010207 72
    0x301d004c41034915542c02500c414250601a00154903030038601e05d95070321075100c44810458a01129600d04210001071301038981c600c001e6010451110000b140e880047e00000c0c42c44441c2d030070400007650b80c800103480c0e122401700c0c180c2c0c11981c20f0041500706108252540007812250702e815844842c0c80f045d252401c201d50029011450500c00c20010540d003001c02260020720445025846040010085074030604440240d81d020326403440010714049407000401400101150790290360380c0714204802079503141107000742c524028909400b1107041c1503001180d50000a4140c03444c03c1d0341e456210386007050030303001500e80d03400805080b11030243d0392044020240080c2814494246140c0024000740a03c492a604598070307007840c400e1219041d403219a0540d070418840c00e900311010041c15440e0004e900c6040035114a214210340361a0a605075140914140d00409103e03081 = true := by decide +kernel

theorem cover : BRFrame.Cov 625000000 625179856 := by
  have h0 := BRFrame.cov_init 625000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 625000000 ≤ n) (h2 : n < 625179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
