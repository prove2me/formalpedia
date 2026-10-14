-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:26:56.430218+00:00
-- url     : https://prove2.me/submissions/c401a49d-c208-4ebb-8199-10be89b7c412

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 361690647 ≤ n < 361870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 361691897 1250 361690647 361690661
    0x80c0619061a0412030c080a11070906150804020a0f0b1c0204031e05030409090501020309010b0303130314031306020303070f030902010e0f04060e090a15020403030c0b040807060507120c03110913 86
    0x1f110b159a1551b01c10180038040210f103881c2039210f4010290049940c1c01e0a1241d40115080348003c08200c61303144805440440000d402070b0307081091102e0108200c0c3c01402003000802030070780c031310342d0390351a64441141104195101400c804e00408c07041002c00c42050b88140303001e000302c4408d01a1034040c074241d480c6114951050301d01c10700700020182403000642c00742d446000b011009001c074802075000c00d5241c2c480d10720740721400c000c10042030010880c0c01d1440c0c8802e5042c0001c40389000d5034800700d4504c10006502040050f031002041041490380010003441d29005820107000e454200c0d800648240800b4009500480540040d1074186d40e51333810400080400070304818950600281054440414440c1035502c99043c403c070028500f051b108940803a1b42694405015018544c0c030010400b2000d0001e5581510032312600c0b02043c0c0c144038050160700203032100c1c40d918108124039429100e6404140c13040c94035201c003075400b4508207401c0301c050000884038200b0000d440b00900c8014482 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 361693147 1250 361691897 361691903
    0x11010f1815050c040e1509190c080615070201120e0304030302070f0e0a0209010c02180a061202090a09140304091505030f1b01170408030615041401030207080c0619061a0412030c 78
    0x1207c0c144500c18000031030880d10880001c00c10310010103071183c19944040305030740d4503804c130242c00d40240256884030042e2150794414500005480c0381001500191407030107940c80500e400c006020020150104110380080030061541311305940b030301c4e03c0102c070803c00804034400c41d40c00080b1050168418180c00407080d07801481344001303000700c660191842e0411900d4045040c640704c0d01003002c5034507c10024210758000c0c59481c29641c0c800000c805803014000442d9050341039119400e03a208140060f0018141e03581c40000c5031075165034018121102580041d0094110b04100b07800d40d41d010505a00c40e00021418800b90481000101e03400c18280c0801e004151100b0244810044200015401030108441e105017008546400c442d142c407a911a12020303112020313010000354002c0c3c010341041c48c0502151800c2a204035802401c000d0116a10054041c500c040081a40a94498500135004201c1640340d8004000500348183c805d501a00302c24810140300b46082611505264902981c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 361694397 1250 361693147 361693159
    0x31f05121005100321020d020109020607080703090506030405010b0411180d0c0b040303021f020a0906140714060403080c1905070203010e070806180c06030711010f1815050c040e15 79
    0x5004076180403601c0d45d0036031240c010f01483c407079090814814062041c81c1034000301070a142c4501691110721a5000c14411010320041581c00074480da540d034003541c400c41c060000451840107001c00c102c01c42e4284046821040d0702400f8491034070025541c948444402a24110200d01c418200400c41d0300407a404030800100004020041550101e0b60756500c0c203484590209c000f40044000c001ea01404560b000002d1401d8001c00c50644242d1190008020b10700002d490441a900c0b0030a0440e0351080804c0d066000030144010194842c5c5c00316030280d0040702046c103100086052400744103215442c0307800c104001c00c6041c1507507000e41c45034102ca41504101d60186544000007912444122156174003120b0002c0002d00014002c00c4100669000074011461a907600800303032852184000131225a65840111000b0030009103c2d26080003080450401d03143d0a5140807500c642c08107000380c507581c0c20082441007210400007650140c0e8a00c4003049199620f0a00b0110301402124425074020303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 361695647 1250 361694397 361694423
    0x70b16140c0d030b030312340f080f01030b0c07020120060f0c03040b0112110415181109010f02150c0301030b01140d0323031f051210051003 62
    0x315000400580c1c01000392402c0c080e1307a801c482007684078040c1041c80192841040300144c25001101c2c0ca032044100120300003c1d0071210601400310604443d1541740201c1d240c014288800c0d504510b206a1194104d03418681940c115039650144200181800c5029840131641004581c05000340c3c0084206c05450b0f0f032800c40384d80480f2a0751310390031f85401442c2c40441000c5107440340350b542101d215981060101113564078007014142008820282510300460003e0300081c140e40324050f110b1008910301d80700007541c1c00d000c0d050403144544003080042138582040c0300501d000d810140c4200341d1090a1662603034042500030b0b41042032501c550504000348000708103c0020b068040d6050781c2c0140e82c00282e41ea2a240714408407031000208030780c040c1c084103010000a00c00e201d03402001c10050311450151050050341d4010340c10030369686928000b881105804521041d941100802088900c4101442c0d082d00c03c0341c886010b050301d6040c1c3c40d11030b030000f9502c1d1031100301d5500860740310051400b50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 361696897 1250 361695647 361695667
    0x3100902400e07020c0f0a03050a030e0328080d0b090a060e070e1c031404060908100c09060309050c060403080a030c03151215050403090911070b1614 66
    0x86400c0907400703000700c1c600c100890b9074a0300c4031115120344030710b07001840340b00400c004110340000034140150380000e4000c001b1001550074000c6030001803003074070703001000e582100801d0305042c824190360b00c030401d04000e2100140c040280d8803503042d8006420540d103550801754040030700701c42846140c10a03458018412400050340c0074a040342c00420407088992108501100e6243c04c01100690104100c2080d04000401c0c0e031424090a2180c107001c0503060760101c0c00c05113904a80c0c01140421201c81d400c009001050040c19001c00c9018030420007180700604c040d0144400c1d002d039004042d0340302c4000041200802515080b070200402c101e85580e901e260551880d03200c113500000090601d99036a0000d4081d018800042a02c44e8080b00384500307060a0210b100b40c10402500c0300140c03090440c0a8800b80c0c820746004a020760348011081e0308104486043e1491036200d10401c400401083c2c0104140c51101508141c4c2c83c84e22500254604034101d400b060603000c1f696003d6000544440c103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 361698147 1250 361696897 361696987
    0xe070312050c010b09010b03040b07030b0a081f050c040605031e13030e0d150f020706050403081e0c0a03092112060f0803030a0506010c080c070303120203100902 71
    0x2000840c000240410303054201813101d001c5c02071091003c1c1c07040c148040360000300340c60310181e03001e0054540000c04580100001c1d8480d10741d036020054a82005080b52560101030140c22040b20080d40b060066040c02074291000344560b02c55502009000300100341c0c8500000800380e800050071018140d0f600b01401690541043d111007200400e00120311841e0900f00f8055610034107800030a400000402000c01078050051202000900c507400c104100006005100b41d6002c0d0307000c0c0c1e80741412031a084100c64000c460250204215001d040e04001a80d80340c0300c11500c1c4ca001a10b804129004946403103800401e0001101c800e105020000030030300341c5d03c882d03039000046500e0000c0c05055500c2581c070004135101e000321689908200000341e503c0c01c40741c0106801030f1061509240d07810781d50b00d03200c0389600030014645081d040b24a080007030541c020300c60f8400754902d00c01149181481c7c072882c03854a88611441c52181e4020075014581c000d0b80d500c1c040340b800000380380134810550f01d400c540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 361699397 1250 361698147 361698157
    0x519080f060f09160308030601031e06170313050120030c0a0c05010c0b01090905030c071508070e0603042a080c0909070b030a022d090a14130e07031205 67
    0x900c0c00c05010000303415200c001400c44080d00d0a5040c4c105140c01c549030038010b90310081c0780d181450f0700d42030004070761035295924190080700901c1c0041c07000c0c148821100d1650001440d10141d070f0045c00403c6095912883c0681120400d0a110605851402110311140c521404620444c000840c5004c40c0700800b09000401503c0342d122400c034684c40f1001540d1658108101401d115584001403000b205240e0107858614000c004403802d14401c0420f01c0d01d4024160481c0e80020b42520701c42c401c0c80d0700302994940100c1641041040100b410000c6211400b000b00302034604588080041e001c00c5541a4150005145510300341ea22a15514519658643e0000301401010b1040001e02c2210000c5100e030f05942d10603102d9441d42c0c990242c0000a50844295030b400c041e0900780c0140300c000340301a012404039401c6943c44d00d40181c602048008100c640c000c084a0415810100c4c0503611441e91070400b6100e8280040c045282810381460f010141c0c10080940c0507100c80030140c9070b00032010704 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 361700647 1250 361699397 361699411
    0x1f020109320303070e0409050102040302040203011512061503090c031e0213060803040612020d0f0e0609122d12010e0108010908090f030a17090a05190519080f06 71
    0x18100c8410032441503900d100c120741301c5000038030780e0074141850700c1c00b6000803000714007540000d4109070303c130b800040407039201f0390241118108030711001c54002c0d00a108001a4000c8000c1041038620f001004410800342240d480b080558401e0b11600b04841000d041c4040d50b00f0030500c0f414204046140c0086002024081e03101d018048510789817640c02d0301441c0b0035528001c0156040c1454030901359002c100d100d2241c1c848039001d104030903940600744103440e030b00d000b401c101044003004a11034504010740600400400e800c407180004240d00c450b02266150742440520001c013810450f03044503c1411069164418100011803c101c003544503001411385804414445699903208446400c969030014020107140c42446018036500e0440c0e00e941d403000b0054281d65041d049903841085030314100c3d504064822012402804504007146600054102940c0c00031000e42d40c84a11907101c0c443d8840c507071044000e60700f611195040741b40101c00600c10241102da00071900c08000b030300c0c1c0e00101ea1070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 361701897 1250 361700647 361700723
    0xc120a02030108100501051f27140402030603071413021908010f060912060608011805010c050906090402030403140c010c0314061f1103120105150403021f020109 71
    0x1040c1d1301c501314401c06048841c001c103001d032071404125807502403514034000d84040c44010f40781c0e0b0b59802101c0410750141c00020240f008601c0c1820850501c9181d200c680c02d0103a4418000c01c9a66100003500c0e00c10f4a9503c005011000038980c0000e000754000010100c8140c00804c50f512162030a90050011043c0707520303200a2070f0b0701c6020580c006151446140001100350ba82001040c2460403418051801204042041c2da2201c0d00c3d5400c1d41c283d004a100c845c03416210712810301000f0711554040050515256280440e14400601180039104000c0e103e10b80c00004142054000c0c16100d50700c4c00302c401d08948441c1c140340414028101d01c041c0c0d00c0440e0905040f41d41d41450f0041c0544a202d00030481d050403051031010480b86001110070800340880715413400c4c4015010800703050f1340c1e0410f0080c001d00b036040005126003401c0d895180d8895401c01e02082c40140d031003a050010f10301591100c1900010294001c901400742104040d00301080f110311075214034603e64030714000100b440e00e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 361703147 1250 361701897 361701913
    0xe0307030305190207120302090609150a02062811120f041104050112030c0507050a1514030108070b072a05010e01020606060315030c1203041a0a02150c120a02030108 73
    0x1507030917841064801802d5071041078100c062640207030701400800002600d1681490001400314244c0508043c6610040300042070440d2039650410841d5844004c1400314202146909510702844203e01840b101054a405c428040c00030751505481c080d00c0c4d0b640600250741070004542c0e404203820340e1b081d148801c1c1b403a200c0d0414103003802424104c0c0c1901150015240142d2421130700d40c3e11b18902112540150100054582d42d070044080c040c1060300310740d40b1a04420b040140c8081c1e00c62034402c240d28801d00c01003002c800c0c0440c0c6142110103072483c007a964030391450b04c900003058820407129500c405280030079859040d02d100381c4c01d60b00280c85808600324000010f80c0d94900854103d07600c160100002010720a103070b00817003a100c03000307800c640903101c451000610601039121240d00ca548003040030080c45101f0f00c85101a04048003440b4034140300240300a40302c0b1010a0745501400303000002c580a03030702010407540c08821210464034282080c40801011f036200f03210703030031580c459194 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 361704397 1250 361703147 361703191
    0x80a051b0106030c0b0d020f03160f0f0831120e09010b0703140f041e060215060f0607060513050706090e0412110316051e1b49031706040e0307030305 66
    0x150b00ce1401d455074171400a40d6450a20011800400302c060b504400400041c54000400081407000110700c201b014aa18112a101c020902c2d0b1104515600c00c406500040064400c038000b105c002d240c0505e072040310300300080d07140841441607090854041c40c0025000801c008450280524200c40c0c0e906d1546407540d45000320b0341e880014103410186071401c00854481d04d0880820000a10054100c9040031000d807a00000c540e001c4422000801c40820b003007040101c10b0240c1030241c002c0c1c0c2005c0c0034160410303804509140c001840202813680688a07075074914000c0440c00d202d00110000c0321b950b80322a101d50b0156480010007113401c1d100780d03202c41c03000c81030810080341d071008504001c001542c40d01c4800d05010355420401608451030b6040f403108407070802d908a0b840d02c04940c0801c980c40144104c020220005a4161a0000c60b9003011000a5120030728491038075000d90003100648a240025000b172000c01d80412041c40000356640815816420152058010321031a03500310200380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 361705647 1250 361704397 361704407
    0x210080603010c141815160506130b1503010902060d02071205090d0f1a0c040f0e130209091c170a140105061303080a051b0106030c0b0d020f03160f 65
    0x41e03810150141c0502c0450081a185608152654401000040d80340406d8030414019400000c1c5401130007013079028003040c010104000c03500050481401da00a8440b82c03201a0400c00140c0800181d214100480403d980d00350010f0540c40c2d00105450798460100c8000c00c02903010010807203040218007202d880c0d9a000d20142c600c40c00000d450b440c1d51080540c1c694150f181018412154075030b80107035034030302c0c008128041031240140c6c0c4400c80c7d9a41c1060791152801080e9800740c10550754010410240b84c41050020400941c151032410305515002c61131400c1c030000c5841c51650740340300101fa1070000c6e448017036445001010402d0491503100d10301c00c503090342c140b1074090301d4581905c40100214140740006103821003503800107418560300e0f991030070fa0700c0e40813407240400a440801c200340c08440202d40d40f00c030150900c00800c403503031855135400c0c4150801d20585000c01408075902c1041420b0390100c8600300304c10343d0410303034074076201d1542200f462241826500045403540d02641003801f071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 361706897 1250 361705647 361705667
    0x6030b0306060d051f0f06090903120204031109070201330501090e0f1b0f03060406120215090303090a0807030c06020f0c09180a0f0b090106050a05040f090210080603010c 75
    0x70001d03041c5c040c01d4040c00e20512010000301410b0310f40d90000340000b64420320914018141e40b140c041041005428020400f0f400e0175925440b992041000b0400a031043c40f0a009004003510b0502595503001c2c0107a005108072a03e561a640509440810140d0902d07500e03405000c0a0074400c80003521480112031314007550082d804002d6090380422070308103076400354991103a00b00015030304155038504008216040351440f4412108048103025a40c0340c1030003000003804007c58000c4020b89950009098180560f03501a0340c804001565401ca440c244112500c80784003500480341155602401a5148a6407006071911040e107000850781500c0480d0a400700c444100050100d0303200c810810005140183c140c3c4140d5104540001c10044e060082c0103510740168800c500c071481034204000301e4000240441c00c1130345850001c0c00b05039903042c0c803042500d01c1601c0020313040c25203026040c02041c4140b8080c0d0300401161038208803503407281c89144038400c01d0300240100026407105468100c51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 361708147 1250 361706897 361706903
    0x5180c0303090d060b120a0606090902180c040b0403050c04061203050414030a02090a050a0e01060f062a0503031b031311010309080309010603031412010b2206030b0306060d 76
    0x7048501d1072481e101079008100780c0903081c00101e05d0583e03c000340000d111080022440e4100c080300d407082c8802841500e00805070094244144103441d80000c1e495294aa0103429441982010946a4540b40103813009000f00c501d12581c0d8980341d040c055520218030000a110700c3c00c2000200d072211540417030f1080d2341d600d030b103943e401d007800c082c10310b01001c4012041941501c00d201d070100150351000250750181c200031310001810704040b18040141c400c010110700340350f81030075402c0000c03404054004080f20060314000081e03000c40340380084000070101c20341c0480c446403561101400804001540101c000009491144a00101c0350020b0300080718860308444052800d44085900d400c1040f44030b035014500000c403001140c2d100051a04240c50703100c41e503076469400341f04064003d4440702540013442005420075001c5040b1244440050041c1c070780c02000801d0240c40080c151454603020760703140341e0040419850700c00040060001d0410940b00344230300d50104115040a00a001000350 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 361709397 1250 361708147 361708153
    0x120906030c18091006021c0801090b280e0a06080c06030405010f0c0918060b0d110712030b04050f040f031d03010603120f020f0709090206071505180c03 67
    0x81d400781511080e4000610034040d1101444000080341c0d507480c0b140d8411054500b24000e45818607000a18046c188180e108007903002140040100350001c6560f81100d06084002c20000d0464010440304c9805480b020345551200300400180504d8902440545031020180c15150b07039a13003500c01c140c0d0a2446410743c86e801034078404003e4200800111703070041c0a00c0002c101240c841c404202101d020350300100c00641c41d01c00500450540c4072100498448010003072003020f0030034445c4016407044c2d01d1004ca50a54400c41a006031030b060040d10706258001c40b07110071000941d00064013400c2d41d03880880c400c502e400001003040824011a6002e240c00001008800e0581d540a9070b03ea0100a07280300182540c1c00146000e5409029140180d80b00340c0808050750f042c500060701c1613550415a00070b542004030780070440c0a000981c40220781c2441004a41c100003800817480510580a016007244010460310b2460301e000d400c0203004000c1105800000105440c401d621840e02424103545030f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 361710647 1250 361709397 361709401
    0xc031e0b22442706030412030605030c06190207050306070f02071703090108280608010b0627150408010e0c041503080c1c080a0b030d14073212090603 66
    0x400e4800f0707884a0000c403011268103060800002002904202c0c0d00300c0705034040f240603203100342c1e143c05001300801c0281c00038140811381e01c0010b580c0c0d01807101002c1440c100d07100c0c00030004e8820044600240302c09803d4540741d062800c0020068a4540700f1030300548112040011000d600300c002d07501c9124640c3c05135041642d55030045500384805041d08170b0b0b4079601e450164201c0008201104100e084400004d0b00034a42140035003510901d0b000144140410321071151486103401a4140501600c84501020390b9401c0005a808109402c0080003910105020070002415440050168000800c4903015103d010412003a03443c0080a83c02440c00c410040000480c00c07405010000070850035a001144000c005250b0b07001524020340000d5424814807410f100c06104a01c1b45440c150702802d00b008088030050f1000c019070520a041c0c0500281c028240700b07000100d25035500845000300c10015810248003501c410800f45600c284c080c0c00031004825190780c00300c2e0032041010301403d04507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 361711897 1250 361710647 361710667
    0x10b09060612060d120302070302010612020a12060e0106030f02030c120c01030b030102070204050921041202060a020f0d0908070603050f1b0c0a0c031e0b2244 70
    0x69001a190f02d0b08420001300c3c5500048851300810410400c6660058650311142002425a003103035219140844002480b040582c407440081f40c2950b180e0a42c15012035250318200008000708900d003902546400c03404420030a0060014084a000700d0031152420310400c00c00c88010015050b41d03905502001200c9915406600401609171000380014289501500480c05580301214212040e4001000d24400d000162410320b20103081c40f049142003906001090000b455400c074040d1054001080c41044148200201c042c90744003034054851040c281d8001410100c900d0240c0d42850103003000c0414002d10900c501442004440442c80c0103490343c4031a440400b0b013411003031080c0c0d0000c0007600b8040008100c0610b001e84940d480345070f0640303942001c606104c10078410316821121101c030680441d08480c902da0b046040030254a40d0006660780c1081d81640c0014010400040900d0a00c44512110811101400c00c846200e000300e00301050b040031200c4411141302c042400348070200344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 361713147 1250 361711897 361711927
    0x80d0c020316021e090c030108120f09090c160f020f19050f01050f040e0907120201080a0506040605040f1407030b011413090905010e01141b070203012a02010b090606 73
    0x40c1802c0130300d400c0d140100500480c052039400c49004819020000040201440401071155910381c0521910300b00070102c0c80c4000c99104e2001d400388100c1200700452020f02d03481048520080300c410f445040703c0d8452030304c80903603400c40703200340c0c0301c0e2200307246800361420160754006400400c081034804440c244001c00000748800740c203903810000d040c009019003001450060000e02002c0300c0d001c03494600440701625020203030700200b404000d440f41060050341c01042264200400d280c0200b55a9212000b06000309490b603c0a90301600305103500c803a401803940f115900040800a07080c06a031041c905a0640d00c208400034009064002580e00841010b00038010000000c080000b0160390b5502001c10750701014400d4590b40d40d10300c0c0450700401d017441122a03410401203c000e651a020400200c22502c0401c008400340e80010450f00310754003944004000d21174010a60a500401d102c07071035007101c044001d800990b03e84801100103145c1420313440d1107803600030180d0749801d04a03451004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 361714397 1250 361713147 361713169
    0x90510030620040807030b0702011b1b12030c030b030a030212030703060504060f08010f0c0225090f050412020c0d060b03152a090f090405070b07080d0c02031602 71
    0x80702034012102c1014a500000081c0010b1072120000e051060440c00c22450b407043c050012015a03161003d1034501044015484000703880900f0400b4011540d1000b00720f880c5095440103007040c80c2850b00b450400e8140e44070003880d10703890790200600300a21060590300d044042016015901903104c82c13180c403800700c008551210651502142d0503540d4004981580d106400c04541c40b440342006001a80003445500c0c0060408030050042254010b0041e407102c1c01051411201c0401c507520b04262098030050320010a20244100b00d08071100c2803840003000240c900321503482c803885817014281d10005e103003010f4103001400d9003038466207555a00014040d040390785815010b0440c4e566032150104042522540c805684036042034410700304d81c55950840e00d0012074600781400104610740701e51402c00030340402517941505980359402d142d45401d505500104540b6000035a0360100201072001d08407100364602c0c01d00500118000c00c0c3e1322030040000001107400303000860405482d040d03180034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 361715647 1250 361714397 361714421
    0x91808070b1008010203040b04020405071d09100f0902070303060501020a0c0b40051005070803090f06090a0c0b0909040609080c0d2307080a031104150806010206010905100306 77
    0x11280f50f803040c84034207a8004490580c3c6146a4100300401d504290003521340c0140e0b58034051246004005641401c150100506030050205a0005e90303100c4000d15104003400445c02c2e4110381e5961541b400000e58810a02140000d007083e000080950001500200941d407100c281f00c01a42011540041da1300204a401c0104506000d4491900d4001c20380b00e03101d074481000c0f890007020340800718546031159417200340070f1b0070860080440c1d11b900c502995007880e4031501a99413503d40301c2d0107510b000304d2803d00206c05d00440e401d102240c1380020700281400d104141d6503544640d60000d0380c5090040350078075904042c2660004000a0142d80301200792803091800e2400c000c10310032220700c4d025102c204980881e1180600c2c0c02c0c50148100c40f5220300628101031464003045964109160050980e140d060680b20f0382281412076411082c3e0703003e01844040c01c0b0364212031a0000f07003000310a80d0b090f800b40c05000d0000c80c0a0000d4026507210310f5002603600703901480e6685c0c01c0d006000d028244 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 361716897 1250 361715647 361715671
    0x150f09290f0c04030618020a05100507230d020f010f0507080703020c070b1303020f0604080a12140d06210201020705060a02030f070b01030203070905040f0609031110020301091808070b 81
    0x10000502030720817120148080103104c030506d82144140140300b00e09400144c810650360600e170b8940d41e0b200c41120422540001010906940748007002e06000e070703040101d121070146444080d0469800500803004810420080c00f4540444110501b101e81c16141000054103c80c005000d0300d00a400a005461030b0a0885010641d218813014042c1c010404061413000102010002d5140c113009101c5650b40840c0e007a880c04c2d1411601c40d5441c041c2482c020840c2c00385120311101e850080904140405481c240c140d81e40c60102800c1c2c00a1000f03000303140034800c50030480c25440e070700540b07044110399060b0001c060040c00e14042000fa908035150540442c48200000e100e00ca1000d005801c42d184130300c42508041d419441051300f40085074004a000314a03240820000c58800088006a19003210300000d026400382011203c80e44e45a030720b41e0084c407802c40001e19221450707000318122884923004200d50b04080c0c0744207290004061010b800141c00340700d44004281400310543d0000c3c1c0e0a142 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 361718147 1250 361716897 361716899
    0x160206070f0e1507150e010608071203081306020406020321070906080c1c06052404090203100b1b010507050901230910020c03010b0a050319150f09290f0c04 69
    0x6003150301d05c941d400200c3c085864100a4058200901609000c4e0081d03402500d804e50400c080300c00300002c01880074003048910740101c1c423841045907811081c0c5030415000d548d070b00c1e29518045d65a502002d00d07007039401004a07000c0d499041d266585401140103581d440d4009240510864410b080a01031074880c06003003143d100200384210301c03451000c042a4002c102180380004100040d50b90074590044250381d45e6a00d440c1c400480c0854003901c1c0d83d4034005031291201c01030505030b03185507000101641d50001c0d6001d640800640c0c44844495a000284215079814500b1030301c034002c81034031601040c40200804030440190341258100d01d040002a82401c618000089011203100200ca001d6000685409440d04003802082e00c124010f80d80c0c0200c10b4130b00004650b80d8000000001c41d0100000e0b0080c0c00c12460b40030071041c0040c804001e02c80c3c006d80433061401030184c084101e0301403003885042000007417203a83d412040c2c1c3c502d080f401c6c03495464003031800c0c03084d500038140f14110b002004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 361719397 1250 361718147 361718153
    0x30510052e0206161211070b0f01050301060503151807030c170d12180818010e0904030e21120a0305090f030a030b060d0203160206070f0e1507 63
    0x40d08a007449080e00c040c48503140c0554100300e514007040d400d6811908a201006401e180c2c9030030906841c10f4510348024481d10444414008002c55449100020400100d000a0100e034003409070007490400d111030204c1e41d0707400405080b20002cac810701790150464184203000c1d644100314960310850014100c02c201500c1001d40d810301d6240d0f003084503200b0101d401400740c6a003010801c207180c0358076801041ca85050180180030307100d07a0f281032101a40c56503802c4400111700c000e1000003a134440c01d0680c5900c903000440c80855500c41c641d034000b4029484103c214901036003030300d01035605600d41055440e4078005201d0b0141c0391140c801c0001c040f649030016001d00410021400c4601d0840041d29408105d4000b400d0300e401a00500c5598801d44940108210200403643c0103d07039400c000824a510801150703182c05102c0e801600c003440481080315410001580100c00b9140d80e090350b080390703030b07050701520000d95541e030840000b0440201c2803824101119101c00108100c0c07130503428171aa981e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 361720647 1250 361719397 361719409
    0x3100f1b03020c0610050a03020909010209030a030f12050f0f100812030105150703091815150e010c0c0b0a03020c030703020a0219081b1503090610050a03030f03051005 74
    0xc42840040c1e40020070844406061004c150401302001c0600c07503c84c0b1340740020b210480c00c5d01010740301c1c8014202003200d1110940c1240c001e1900501038508116141c1070183c4070b42e8180c048480421148082d06040805910850388560034201450700741d40c0390312103e410f960a0040ca150340381440d144004c500f00d44200818440300c902d2851460b6250304210a02000c41100004140001c400380880e800003500903005030151501c546003440d26030503240c3c00030050100c200c8603070000c0fa1098000f15010001140541c4841d040780c544194103192100112900100d4601c00f50007010351010034810440d2000041110240030b02d805418010741d02000340c1554840d50b0300310b0150340126802c4046003820307a069000300142d90302c4d0700755061802d18800e031a07010802e1060042c01004002103550782d98408104800d241c001207094a0303260030810319564200c2038801e20b640d40c1c501e180004d100c0c03410103001410303645c2c10707581c06d00201c9850f2400c0c0d0103803501808480d0101810031020a09e91105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 361721897 1250 361720647 361720691
    0xf030c020901170709050105010e040506041107060905010b060712030506030120070c05030303090a1e0507170705060a0504050d020d060c050d110301152111070303140603100f 77
    0x5031002c0e0b02c1690f080c0c800149007440d594000e00c1090b0030031004100c5070b038004201c90409401603801098664900c4c0c0060005d084022603800c0300c0c0b4001c200e038002d000c1d842e4020041d040c868002080202e401204000e001d024550008009840c035400d6100c1e00b5210b5001103400010180001c2403000ca1020003d9a0558102000901c82e5004c2072010070310155031018030041800760061840e5042044a240d103400b40641d000d440000d0341c2040c01080030804642180c1c10313410802703465500b61282c2d8100344100b00300700340c0100761040300b4000c5620318104048521682142d111036103024900741c20b020910590700001e136804110030301c1c40300128090b40a4004892415a42c07290380c0d8501d03200c1001141c0c200310403e2104107080c001417040c178403000b02802145546040c83d14200720b2000e0b000d09e00400c2c08120001440c284040400d4910305180500849403003910f0a01c40b0207060703800300303a10040881f40241c0c0342d800300200e0484241c180c0d0000c480c0142c00080072882d64140ea0310320650041d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 361723147 1250 361721897 361721909
    0xf10060f110a030509180103020a2709080c1b0307140d0f030201020904060905040206031b07050a0501090c0501031401180209032a0901030b040b0c12130b0a060803070f030c020901 79
    0x11a0f05007407600d0603649a621041040760346d2194110b4000c65503406182c0503550b041c82c0e07020800c100001c07c08074500d0211100090078031620026185c20b41442d045050748003800d1007583c4400c40d841c0100404a00c8840c0302078001d00c2014a42003106254845000300c1c15004501d41c101203001c60003444085207020f0080d0000350307641500310140b004441465110f2000146000c05200c0140e0302c3d10212a0450301c0c54401c9044808590081144c6204554008006106203440c040c00c0200640007400f0306800f4201c0b12000d00d40c0c980c010b40036500c2031380e400c0c455282510700510031610241c40307403e841018a80010b04048000010a11b80812200b03c03000c80c2840351500c50051002986080360341c5e0054900b40700c2c552451759400c500400280004044644d104002401651400182c030401821300c2814041814a0220f1072081000f240040d60401511800982c0c80003040c0034420884010381e00940c1b4001d142c1c2c4900205100c4030b41d080b410844030300e68190140e518070900c0d6020b042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 361724397 1250 361723147 361723157
    0x20a0602070309082505220506060f0c010605090a050f16210203090d02030a1d0d060603030c02030d1b0b04080f040b03090706030b0906011b0b090c03060f10060f110a03 74
    0x2191728107810991106901051244101c01c15180c2c180e110607130071101100a031103001ca21602c45000040c507038001d16800300052000443c0c45180321105421140c21108140c410000c0768950195500a50380201d8420350084d0340c100102c0c650b80700d98140c0c0040d0b1200c9141c42c4442c000c11810000781d03242c80103400541c66802205000b40e001040c40007c503024035a00041d445c2c00d00c1040d000c0d09402101021030341080075090303502c002c0e4032031605590106605c00010132440da100d25000c4c2503030381d20301010b0b40a8400d040e0f01110f141c2c0140f042c00040102003845070b41d5141c1680e01e04e51004070091003110b03090b0043c000f55040400c540054030190400540294032417610a44482c03400460b54000d20802d400c210384c180403600c071408034540203030082c40c000723915000c088040001911091701c0100301e000000304010740d81d8408105042105022000e40351036886070b84100d52100f00944c0d000399506c1180d0810019280140c0b40e030a80100c9506020041081e604840c509080307071900140d01080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 361725647 1250 361724397 361724443
    0x506071106070f120905010c0b10051f0311032701060f0906030b060a03020303030a1a0d03020105040210090b030c2b02130b040806070c1406010e0106081e0a0e010b13060503060f07020a060207030908 87
    0x81cdc0c0601030049001b20080c006425498000401c4500c60402480d40b0140e8403111900b16428000b07400c0100a012150f54008400c0e948100010040c9110b22043d1a81c3d11102c0214a542ca40544000104c0ea0002c000390b0541c1c0362054018002e001407440c0e0b00389200748918078081d40e201c1c4040d6031b01c500d00980001895141900521908040b490343c44010846845c40521a003541070003565006506804080e40f60007244444a070442048103410b07a043e8032505d20924100e005030000c101000141040c80c400580d1030720881035500860040c58600c1d000400010002882200341905250146d2244c02041107290910307400d14400781c00c41403034000c112005100c0103800504040d00310b03000607108841ca00c212108402c07000400b401d02100a40c40325119450103909401000c4442c3c4000c0c100a40c110601c20054000e084038400c00c2e0081c001c2c0400141c408260201c2c2c980300c0c0e40e203a0090401c0002d0340c0e888070029070010300d0440502005c0400420801c0d800c122604900303400e401120200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 361726897 1250 361725647 361725709
    0x801360c0305010903351902070c0f05010905030703021e090114010f08010e04030806040f0c02030d0c0c0510090c09020304060e01060801050c040506071106070f120905010c0b1005 79
    0x90004e07410800b400c030600701e290074061020811708911040c0761b85c648001919801d01a0f07581d504101c0d455441d0500214000c8203101150646404594204e03407031441c1103654500540d8807910320b1144a03850380200300c003023005d81803000c05e00e000b40c0c2c43d44034012101220340b400030303440e0701c020380280f2001ca50703009041c0115600406450804022410201919031400c208180e0440c0b0041c40181001845404100c142d1155001416015007001c014880011141c10083d0741c0d401440d10b03082e11718140a50085139600840120050640150181529140a001c900e018007071070320040f124001c0050001801e02d0ba54030245004900c14a400700d1b000304c50b00030060070740d0299040052241d140109000da0718045904a4044403000c1e030f421610b5441504010300d0701a0030307a4001c0d8101c880002d010080000c071818060220f40b00d440000d1100c3c0e800c12003290400e846d8051140842c0c14210103c01040906a4060344200c025010008068039480811400303038000040d40d2010303041241d89000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 361728147 1250 361726897 361726907
    0xf0a1206050d0809120c0402031f1706060603071209030c15062108040801060806100906150e030a051203180a0215090d08070c030308010801360c0305010903 69
    0x4020854032042e03405625111030245100d5200110b204000405038942d03030401c00d2186826020b80103008544900d040e42840792620401460517129130007006021070710300d204407030100240280d84000d000070360300c03202800303401d61000c0c00c3c00f400d00100103000d02c8401806e0207500c1c54648a0303903d955460304140707401c849002e0040c0c1042c4a0a00300002880040b113081c500714001480c501d6101044001414240036510450304421195400d00307101054203400014801c0c055807001c50003034211540c6d0050b0310129082070141d0222441c8025000c2c2c00300b44140d9001030081c170008c0641d40c0b500155510146131040070050080c500c4004400c00a52a07c0120340300401110b400152030207800301d500250b16540681e1110340d0421000c5455041512202e00300180f40364003240941d501c0f103080c10b00301c80407112480101c00042c41640040b90002d81805171065104802522a49005d50070307190b207400e20124403076140300c04110440312021940b0b50b0342100c015805400005031000c014140100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 361729397 1250 361728147 361728149
    0x90f0c030827010e130e01050f1e010f0303050a030608060901050901060f2936010c05030d0906020c0a080d0c0806150a020106030b0a3306050903030f0a1206 69
    0x1410b911100301005940d0f00641802410001161141d900c642015070680061419011000c50ba41c649010410f00214003030303c450048080c003601e400034088840c49038088100034010090421011102080080c0c0900040c215602c8135003800304641e6160a80d41d03190900c00c4a60000e03e81d15402480b4082c1404c0c070452014180c1b011495041600b000c0b91074206004400a800e056200400e4000000101c1816145034283d840c030700d440e0410030700c69100080190343c903851020340010100c0241543c051300c081041aa4490055801c1c982c48002c1c40c4000c1c1600001914950f400704204288017a090102102c030034030a00131551140da1b650511400c5a80c611524800e21200009102c2c0c2696500003d01341d1010f052503481d030f00c0030001c00c12405070445a000808102294091103c0e419064003c48010038048075043c0c1e00e80d0030b0004c10344112280ea40092840084082c0502a2501c240020001c1000107002c40b4900141200c1c1c400081e8020246c1e80300060740954013824080301402100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 361730647 1250 361729397 361729447
    0x3030504081b0606212d030c0d0e0d020904060b0a030203070605120a050106020303130515010906081c080601050d06080609030c061f050f0f090a0b030c0415050103090f0c0308 77
    0x41d444624248a81b17544440d914064060f03040c1d0885100d1034541c2068001ca45044000207490700e07001008980399451151490110100c0d02000d511003403030500b00380c0e07495500d8004141c947c00d82ca0780c0d282d030001008136001854014090321004000b6031000c01a0400800450340c6403070f0742c1c0c846010320340004d62001d40000c40071402e01e4010080d4560000039213800c802644030000e00880d40f480d00601e04100b0040c0c1c00c0c0e0780407801d03000060401882d4041000c99034400142c500700e540340101600c00c40795400c42d11b4003040740400890507552142014140c025204800000d20944460300e21b0300c0c251003240e030000307141c0c40040d000d81041018800c3c260400d52101d0840b4400b100c4400140e080f544901800d40191020800c1140e156150241d01c5091100a00755408a091814040c2c0151402400d105d00074401e10105001c1d6042070300c1202024001484482e00d05400e000044028211b1240d043c0c07800b8484802d50300114000c02448401144100103583c0d65031000854420309401c114091 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 361731897 1250 361730647 361730689
    0x61c050d08060a090c08010302010f03050702100b190b0706060611100507032c0106050a03020105091509100302030709060c0f03031512030c0b130c0303030504081b0606 74
    0x40001880c4048a005410031205582c1e40308081004031600d41c1c00700007030b241020145420f054005d106281030724005e80e0b40381c10095841d01c060382030324002c0d00c0040050b442484603004151240c0e002d001b4031480109040c800041030003100403005da268200501001d000a40304042043c1d9118100045c0500d050291000540da556240c903504454621f81d03410b82c45030005504a8032944c040c00d80040100b14151000210049083c01100002c1d0074070a150310340540400c55240c10a41c0e181100d605a403130074601300216084c0000a50303807594568001d5424458030361170b40e94041d18000029a41d98005842c2e1500c104001d1034948568480ba0a00049003045008036440c0000d0500c03c54150a000c150300090001c0e00324140c0a582c03000390691002c0c0c20313a01c10560b0010304a982240a0240086039440d40303a540d104612407600c000700842e64032001000064000c1e00403680c020300030440d080c01c0075480380303048015150384e801c10b030200d400840805c02030340340c43c0d410007a088000d2805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 361733147 1250 361731897 361731949
    0x6060329090c03091c08060103050703060510030b0d05031c051e0610090f060f030e0106080703025a0a09090203030c0a05071802090a090c0519020606 66
    0x2082400401508200402e400000000c03002001040343c0b4030740071062404000511004400100005070680e202030010f810040031038290f522034000c2c403065620040a442d06448250700c203a0003403040bd010903400134089040c250221702c0600c0a031124920700b5001400e4480602400812150010301c2110408503840d90040241d0705100f01d076900410656601f4118079003494140c40d00070a60740030300c2c901144800003059066104440d03e514140a4034144140d045042c0d80c1d5080e10b04034001c60745180d0003d8410000362814911024417010100b030401310648800100c00d210005007100314945e00301001411601c604007803410703600e00500d03101c0c42c20f4071442da60005205245a108801c2180c1e00da10003101596418000c032410b4141460440345200003610349a91141002e10038010000318140000e213a5000900844e5608038004002c18502d89c1862028001058048140802c008080c00713111034400d440e1042c442402c000703400503c035a2034182c04009900b40c0a1000c50040c895043d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 361734397 1250 361733147 361733149
    0x20f12070201050f12090313090905030a031e05070203040608060d2f030102030405010b09010b040803070b070e100e1003060e010e1f1706010b030103030512100906060329 75
    0xa803103180da4240303042581e6550340d80130000e543c040c03505000b0f0341154903800c2c00405c8800100614200442264407020b5690f502c0c0044215407c01c1006400c9070000c01000d40014880c1d030010312002100d0039811621005140c2c80000c42d10100d49407405680002428042e040d0000049076010000f241c3c4e00d00340c1b6460b50384180e002d04802080d000720001d010040790344912259583c00d40340e80c014008640341c1c602030a01d01c1c043c02004000700d0044003144004222200500c044070709403003461005502e091641d907074091026000400200c10172500201200095071811040384408103142d4036a000b00c07039800304101180b10080c04203018903180200401c05102e1160380d40d4111610040030406e255160000c45034120000c62910b0001c4000140100310082040164108000000200d609907030301c815460b00320380300a01002e03011440501100400380b0320100ca165111100d140000340036940c031316180301038908a800c0480482d8585181c2400010440c03040000304464040c3d44100c01c864cc4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 361735647 1250 361734397 361734433
    0x103060b0423030f2a03030915071a1e220809040209090408040303020c0d03080441010509070b03060d08090607030e0f01020f0705010f090f060f020f 66
    0x2050798001a61405980340d50f805100302d40050140e03c0c240e42c607074013078480d11404016005040700c88601990301042910300340003050740c0b40341001038505050810081034044a5421102c000c55030b81c005014030f0f002e06ea12000b2000d0140c03460400102070404c3d1000c158108040051103881158890121944000008004048400d4006502955036a070820104001e0f100350088990000d40820900c810042d440004200300c1e80a58241c4510030300100800404000444001d40041c1d00100814041406a5041c0d0f4088480205083c5000c00c0143e02d03681804404800c065010915071307051155040a008041e031184803200680382c0581061100d586901029012a0090000903d00420003505108481200c40010020754a405861400070050071280d04160300408911030040d0140d4000282c581c3e6400515025000090030840111040f00040d03604c0f0040052141002032050180001c070400b9002559814a0300000d07104080d01e0115115940d035010340c00500b50708a20709003a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 361736897 1250 361735647 361735679
    0x31603261f08060907050a06080408030c0c100e03040609050108060d0303020c030c031204020414092a09090f06010e0114040b010905060a210905070302090601090e07020c0103060b04 80
    0x150500050640480c203590007038680c160441c410783c1c418034081c4011000c000560f00304441007240c20454a80c0c5420040700d070a242554000e080000a2001c14a031b422940090200c210300d007811a81c90a6160207018140c5d00a648000400c0e0030008050050550014040014150a0070002e1705400c104000c14004100180050205540131894410700c81060003164030428403c01226180c07004a0b107140410a4292012032207185040c014081440e00320304150304c500c0035040a00b030070701d5a03a03481200c1d403410f80e299512070441d110400000c603034500751124040e103010f00c002c210400b40380340213914056068110080c400d04030001001811000000148101000c0e5400724030314280c000143c4180c1d00c250001e0307510000104500700815444201c0700020a12000c0181d004084540da980440300c0300440a81603030802c3c0c0082c0094201a0f0040e03400c4401854001e006c030b65200b40e5910703031940a4403900010f8015000c1501c8a41e414044c0c00042d01c0d040e00e41c0d5141a140c00b00e070a0400500d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 361738147 1250 361736897 361736911
    0x2071e0c0518160c020901030c14010912020112060b1b0606010e100f0507060608151005100509060d050108060411012c040e0102030907080f01050c03072003160326 72
    0x180c4641d164000d8804c001a6002e150701514280403035860345400384800485010f035485d00c2d1100c6491441a6200307005443c00c030f03907109403c03440802c2c8a40044501c02c6050075002c00c03a940303803c8005490b4110070300034003025510720310821000ca44041c0f00d905015001d0251030400c542a007003600f456907003d510000603105810003c1d054208064140c81b01e0080c400c3c0a440c940c0350110000c0c042030041941840f0080b0701890581c2503480c0d1400c404181094011141c000c3d10f04854058550300031402001502d80060601d8140b0108404141c16990241c00c41c41040c0c00402c20b0000700880c0700c08a107107980703090904800300311414900c040c1814082007142040c244040d04210341d501e03540c0c030402071040c0f8900259900d1600300200d40e9284645d101c0c21200b84180c40b004990183c0600c03c0f00d0190100d01300c404d1840d1a88002280c0178010081a0500720070304441618241c00c1c208020310311444818518000008282806040b9207c00f03020380f4940b4902401187c605000040d0603035110007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 361739397 1250 361738147 361738171
    0x11090a0902120102040f12141207061b090b1e04090615030b0d03080a02070b10180e0c0d21030902120c01080103080c010207050f0a0b09030f04090b0402071e0c0518 72
    0x11f0b190401600480841140c40e403180901520031140c054500700806d2030900910050001030344418400c80e41c1703914070300e0000000d92009018001e206440c0024030351003c0b41511341c0ca1405a60441c00843e604c9a0b100910041e13441d04108541151121160000c0c040350404100051800011901c6440750706c034003e080216400001d42804800d0341603645880c1c10415245007032804030030107408a069400740e00070804003801120388140345070040010001c8014050840824903809000c010020104100c40c69604807504c0b1401c030010f424585200c1c01156000f007180085401807050303c2c401d400c3c1d5100f050700300d26420000c698100840383e0440b94031410043d560f221400134140280100f036002003c90180040920781c1c1940043c101820131302448000c002c40d01c4410180d90b4a200d044404461010188020460b55600f5070002d980c152020340007510703040040d83d40742108038a591000d4040880c00712130009002c920901c0c280074040665071401c1500c4d2460550b00f51040007041526504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 361740647 1250 361739397 361739429
    0x3090907030609091109010b0a020a020d08040b0307050307092c07110d09170d081503120f0316050a090522060b030a1802100c11090a0902120102040f 66
    0x3900c0781d0700100c0280302a00c41003002c41402e14021203081036003513000e403041810800204880e071a80c411100b54191070380090807040c00c41c1d400e1185640348604243e900d44c9060000040c02d4161400643c0700c0c005a41d40d556807850f00d004040d00f801c00a4010144407185d54115030104c0714074821403911a00c5109000c0142d03510098100c4407002c04048074009806001c007051801c9803c040703010300381c3d1410340252104c80446070704960341d110003100d10300008402c5004101240c0301c10402d40c0012401800ba62a6401c41401d403881a61020070041c070885000020850203699082c0c5240a098503454601c0c5003407002c980050001806008051143e008100842c2c21504074024226007054055800d1081d0303641c444140c0c401f6002103900700c41d0107003011001c8103608407541000003141e0740140941c00707c0342031440446007500811340840d03403079189805481659851440161084020107804142c0c4041407061024050258103091307030303680c01072100340f0561034008280003d44100180f01e000c0d80c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 361741897 1250 361740647 361740661
    0xb090406051905030709110406050c0c0a12030e091506160c0305030301030318060c0b1e010f08070801110409150b0304030509090115020606060c0109080c0709110705030909 76
    0x52038107034041c541c000d2442c0c40c0d40071103088210b4031004481e02201a40c1410344e440146c00c0a8500500b025407005038100300900c0314a001da805480d2a80d1020100e500020001c00851174076001c54218600e0409840308980030103510042d4400da003681603650343e00504240001008a11002c2800d0788030f00c20100e00c0300155440c3d0b0926280c00364001380b205400c02c1d5a410015282c6d0300078002540024260940d00700c00700d11100340b10003298001e43d155604c00d10315403564100341c1c40c081c150b25140045103410720794012080b0303100341c0606000d2414095007480d1004443c6841035550000c01264100b100840e0307001e170540d0030303a0b0484120f8040451150000031401c61504070039006032041000c00700a03c0300b4164020007601d140c10341a51940d0a59888101840d0b40045500c40c090060780f00000080c458100503018204581342c0a00208038507041e07560311a05c6800a40b0100e08650008104003c01c550900440b4000c410301c2c61410300d403100e00e44501d41c0324426012806c0c0640746607000f240d08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 361743147 1250 361741897 361741901
    0x20721080402011b0602030c04050a0f1a07060b06031501080702070608040f05011104080106090f180201300e0705010e1503100f080c030705101b081e120108060c03010b0904 76
    0x841c4e54080d208666a152844075200d00750414010f09e801186640f2010401c1501015040190b0715240c10380303046401840b1030701c85503034002c02c0c0480349291150b144440d1600ca000c00342d0f0048440b41d070640f24039110440010030850700100207000319444461308104580e00905a00c0d00b1941180c90a1901c04940c105140903040481341d8851000300002c0c0041c410340c066202406a840d003010600a0100e241d6034030b0186c0e001e844186000e40c0720044100c0056002d04400d840b4058200c110500812080780850f400311484404256210f4a40050300c18540040c01800081d1800742407000c110b01a101c0465a15641c82d07401501d080000004a8210514100844000c103c0c0da510044100c1d100c644e144d07128007410069500038820403101007120310b405121114407021031b80c1d40409180070011000541104501c1c280d451650802444824500702005101c40e1903501858641e00c0d210415680d191031816440071445130052030500074050004812a811901e00315081a00c42e2400c2c5e0000300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 361744397 1250 361743147 361743197
    0x2f030a020c2407050703050f0a09080709020d0501051801050d08040f27050f1909060c050403140d051801030b0a09051006030b13240902072108040201 66
    0x1440c8a05000c00e45280c0c11a07120442408901c01216103c1e01c0343e403419285401031102c02004901c040c000080000410805441800e201d8035240c80400d0b5100c0c0034604101454000210700350700081c500c400f84540c0c0c042c0e103004000c00e460750349460401d050f80d00604841800f50500c00c08840a00b04140620b640903039028040401808421a9a840781c1100c00051521419100c0500c0910030030303100c2c00c7d4030546201c1c502d0300503207015070f82c0d400c0761032038099200302c0e00742e0a40d43d44e46501c0400b1800038894144000074a880f042d83c0e4034250f080058000009202c80c4000350b00c8074036282200703584281560410307002601c25108028103200182c0140980041c4581c02101c640c0340000c252000307810140c00350703c10002000c109500d070a8110309503030145d200c0c56003040005410804001041d88421001d06d400b200030810840d01c65003030120a512944a21030351600031030040180800084030000c5903081c0400840c0e00881c141015048003401040a070600c002454411214180700d18610 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 361745647 1250 361744397 361744417
    0x9180102030a0609050603010212011707080708030304170a09030803060607140a02040c0207050d0807240e1014041202030c030c1e070501090905060301060306060b0c012f030a02 78
    0x15441c2c0c9042d00001d4010000c07403080800c458245004a00a401c0600c00c40f000050300b611030345490f80c00e008a9405060000050313824034400d440c0300241900092040d0030140403090003650352820541054041400501c0041607052420040c580c08a43c2085c010421254888182c80d103d5407040f0009085024049001c0d02c0b0080c0d0071100f194102020650700c00c02032003210f04010740142d0103402c03603880005000d80f5030080722040d03103071000c100181c025191482c81124400d1126100a02220b0004110301552003100e03111040308092003170034401e0941134004008104882014410030b000c0007030000d40041c1041101c010070300b0600b03100b84120b41d98840103400303da070b8402941c4075880e40e81510f06400c0c0c205010001004035180400700d00b0004849050755002401401c0c0180c01000f414040c001990565907160000006031150007448001c1c045070a03a0b40d224180c0082c007509413070014907205596400c46580c850038880c01603120011007140c00700c0e141c0340d030b4a0240c01002031003440d80e04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 361746897 1250 361745647 361745651
    0x302060a030c030608010506030703060b060c1516020309060f13030209010f0504050f0c070b09010b130504031e0f05070f0f0f0309150516150608010b030c01051305091801 75
    0x8440345581581103000d010840740d500300301140e9070361501800c8070030a60b034032541900058800c1010130044c1d0480c815240008045514226845036444c1c5030883e40c004100031440c0c4501001441d0f40c1c1903241000e1000140080c600e421039040000d10244130300d50400d55003a00c00324060710340303070800c400c090f02071507014003000c9083d6110004400042c503544502c2e0710036414240000d604421849082c1d018200050116042c403155917a0180010310080400c00e0b0f40d03681312141c41c1c1b03540d182d03441a010300c0c44030413001525080a0500800c52500f00d2a080b000d0b410721031852146940c00300c2c241d01e81e0780d11460560f071240b81c0751400c1c4155071241302001d44100358502001c014130400e940c40740f2200d4443d84540001668039108031850030703800041a00402d1050140481c40044001d0f40010f00348201d6074140e500d00b02c078007003d044800c0358200805c241e40d60b40070b0000354141080324044501090034800d040009021300040c520800b8000e2a02818040380810032a02c03400340301504041080c002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 361748147 1250 361746897 361746907
    0xc0a051501052b02010c02031507080f070e0a0509070e0a03060b09070206040c03150e0a050106060e0a050306270d08060f0a05180601050c010905060105132c0106030206 74
    0x100040142800b60500c20000780c0040c0b007215948040c114403140c3d141181d904080f03039a40041d41c0544030308509980601a1441c20300c42c6110301612580300c0d46242c2c0301c04501d1b0401c000540340c0000c00a040405020f5960001c440554500031010111241129010910390302c0310003c4800010840d072071070f040802c00c0408010845950068000d405040d00c1c911203680c0e4812089a440c3c405a0300030b444e4000c104000d0021541d6484c2c0e800070031054440100f907441c0000405032518074a56019941a595014213001c0707541d006d40f4559140c181140d514401905000c00a5140d0740b000d0308050020640014000c111403440d5584038110ba042000c0e54068070b81101d02900e444411143d503486100341c0c00c4141c40354988036282a00303580303000c0d144a2480d8a00034061807a001d01808142c1840406d00124902030400d0050345107151041001d4070065240c403041c0800f1501a601c20302449040104d19142e4240c2480c00c0fa00c0d824406000c203002c0203841c0f0b440ca00402268102030b4200701c001039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 361749397 1250 361748147 361748173
    0xb040905030d0509070e040f030203070b010b090a0e070e0d06090f08041806060f180e09070302010e0d020609190b0706020406020f011505010f1e030501030b0f09060c0c0a05 76
    0x40c1c00d0344402c58038107024558841000790703262180c07030066480109201d808100411042034140074045c1c401c0c01143d03c0c0142c940ca40c8146007409038403d500545001078030143c9030501100a500610780c800203c1c4407403c190102034240c00c01e2404550260259440a9040c05002d4121007101500900302c00da0b01e0006050044142d402401000380303035a4440070304040381620384210070440da0036a0b524803030030310720b007034225026030780c0c41d612107020803d103040415950458120a4080e5160000600085255100150c401490f51071140d01c100a16544c0c00c1c09078031460300304c4044030740864035200d503005100c54500d803081d0b5a030454050704c4d5012031401c040044079801001a42d000350225850412041a0a400d031002c000c82011084048402017009500810603c0545052420881c64204c2c003050303401d04519a841081001980f910010018044d040058a4100b00c02420000240c43c041c03c3c125900c0d0b402078084100e0140010340743c3c69101c1e040c0f1212402a41c02010b1b64811500d1706d07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 361750647 1250 361749397 361749403
    0x16030f11280611270603071d0909030c0d2c01050418020a0e0913060f020412050304090b0a12080a110a0f050d0f170a060e162a060b03010b040905 64
    0x194041d0559183c00c1c1c103c040b5a4080a07260744c650340140b0003480c55660302c0c011240004840911181c0001c040380a0000380e4440104030710992144d40116281c5c83c0c599500c51a04400301c41d510280540c2e00b40052045038840820b941c5c00d81d0050f4000c00245800d00121880d1041781c0c0489001030740603041c10380a2645400402d04840c01d6a59400402c1070748007004840e580c03d4511000d06801d0080240c00101a0307003244998400c0d00c040182400c0d0b0b03852813415980c2402c00211200d0700300090034445034984e440742c2466000169625140a0f040105104840c950b03560041c03c0e030072001c80c0320301d40c4610418503480c0c0d0311540c800740e030104007042c41c0c18800c1000701d1074101c3c2d548c01007280c02c4103040d22450343c0405c8141d0320341d41c080d0084000031040400c03080250180c0300c42c989039030020905020f031029084c05074143c0c804c002c05110301000c009201c0f0020140340714040c510031802003440030100b0038003000b4940201001071080e5a4800183c01042013240c0070707030814240039070402481804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 361751897 1250 361750647 361750657
    0x1b0f0a081c0c080708041704090e0d2111040f09020c010f23130605180d03020711100c02040e071404060e0c0c070b16030f11280611 58
    0x1c40008001c02520076110003681c0440c585040000c03001800180070070b1280c0000342d085030042103406070901a0303a644000355405504894100c0d5200c0300740a46989040044040c0300c41245085900724446404070300e0040141400c0107400c42d02c0c1d01106200e407003420200d90090240c070000080190342d40b4100d0000e0f4100c2c5c41c00c1215035207070040d012201201409422030055412070110407000140c0c020b06840700c8041c044038a001d07c0300c055140001c5091040398004e100c0114001e085445150b00c4034584283c035403800701014018000707880000c600f804005072024049990100041c00180212036a108042005c2e40c405d05060000c0c0440b503000c6030f4482500c1c03030200e01001b000303201002c3c0020740304640700701040302d112540000c2c003c0d00d2890180c4a13401106050b03130300c1180d0b9109002466001300c1000409244581070b02c40804d034100080c090081d10074241030b0b0452040d03601e000e88a49100e80862a40c104031011040c80c40b03d400c200c02c11041c2d000030308101c0d401c2d4541c080782282e004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 361753147 1250 361751897 361751917
    0x15090f0d0905040e0606010e0618030d0203031b07050715030207050109150b06030c031317040303090e060301140a11070204090b010302010e03030301080709180b070807021b0102031b0f0a08 83
    0x42c0c009800f00d041340120302e00d8403e00040e190020350480c21000d0003d541d21000005000c0b4001442042c00342d9414015100701600780c3d13005548074180415100c941c0b60044800c50400d03442042042d00103180407030402e0841c0c00701c00d40144052807803401030340a4487c0150041a65181c44c11150400c145444400c070010303c0c0320b0b000c000450041081c00001e200548103940046802d1000030445c10406404800040c411011000b40c082004000b2030786400c5500120049058120309001000d51003890f2944900128000d01000c0c0e400510900c03890390240007902801d881e0140039a204911200700c5440325400b82c0204400030703040c02d01c52010170082c00200e0024a481216a82c64900041940c0c140e801c242e01500c034003403801c1011801054084040169620a40444400f240140d22480e02c10700071501c1d04c00c518900102c009041c0002401d0089031f19038454002505a6400429545080641c1d510301c029228021040d81c07500414590b5403040e4400e2620050800004d00003403c001301e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 361754397 1250 361753147 361753151
    0x20d0b07020c0a050d02040b0a0e0123010804080316021c0908160b040608060d17090910080706050f0c011e27060b0f0a08011409060915090f0d090504 66
    0x40b61508100c215419442480d45c001690300aa03000340c50540d212038003000004205075061540c48a0303178103140209900940358070300403c000c0f84040090f0619040c03441d01c00d2803c0082860325503a440154000a030075041a9415a00b820392054000c01c200766440c200a03512010f99012400700a0440e038050044410721f01405014031007954a00001300152020480f0943c142400c01d031040307441241c01491107a101c200c4500720000b003003690510441201c05550384550b41d10802e8148000041c0c041d00c08103c0c400b8042e401c11030140c000c9900c0c0c1c295003240c50865501d141d034414081841c000d0f03034548100f5508e8465010105412074020318000c88075081d05001001807a005070613041401100365000160103840100010b4669108085000004203401c065066450110b00c56000030703080551507030340d1090503010030664400e026900440c060010310103450031222094541c1c041c089843d034801c1269021030f07030843c0c0c00e011360810130300e103c0100c400d03500d032420b4018800c2040d4030070140554 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 361755647 1250 361754397 361754413
    0x2150a05151e0109140312030702032a061806060d0f0203060a1506090e070e0301140906062812140a1a090628090204181b080622020d0b0702 62
    0x6517110300ca050070f07104004c020303100c016001c075900c21080d800103200108500040141c200826450300c151103800d00d00f41105c2e040d946070a00702c030345010000350181500b0100c060303900c40b03400d6000403013540c07001d000e540215600421b850310b50300562200c500258140110310800c8400c030740c03c0e4008201034200d2030310985270a545140c165081385a40c01100c280b000c2400000d0341a0380145501c10801c1005400003401c04e20762040d034080704000341d44200303658004030188002032030030010500c00302942003860845071a090300d207403003e50342c9485045095940d8840c00b0060200c0355403100c941c201c40f074050b980011031a02e4200d90700c006803542d8800081c62600031131034044000540ca841410105245180c403e119080b56582540a40391200c40700d0301ca88041c001a2035a0003982000c4411030380f088540c411b6403625100281c208504510003030030180040040746000600e4503001201120400b00241205220305203040d95110040e410884d001d00b03200802c2800850548107a0141d42074440c09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 361756897 1250 361755647 361755659
    0x50a060513030203040608040c030501020310050a0506092202130602070503061608070e030313060309050f060f0103061a040c050a020c04050112140f07030807030201050702150a05151e0109 83
    0x40040e41c0300140043e030090006008940c091259150001d00941555000550301d645e4a07003a60700485401d400f0f001449000c01090a050300d0160241100f00e98040c14002d02c0c001280d2111030441e05021a5020b022101c125600154111500d1030700014443c403040381c544801a6541001e071040c2ea029114110020fa4002084c9038000c020792016030b41d00000c0e4440e92002c03120301c03400c2e89e45240c1c14041000040c03100000920f280c80102096240440d0b4005035013040b5040c02c0800003c055035410030010840304815000d01ca60559921520005204071400a05a5481d114501081d049840c2101010030350350880d001e0b0182d03102c29400c48405400c800c00744070a0740d0b030a1140e101200034800c42080003415001d66a80040d184404980c02a03906890952400c16a40d000303a45e4400c000600c90181a4203000d46584001c1c0350004280003000750b05501da08040041c440c1042e540c0d180c01080010004180d296a16403000b04007400844109405044440034040ca46020500c16200000c0c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 361758147 1250 361756897 361756921
    0x5151b2505041e0519022b020a020c060a020f01090b01030b0603070b09040e1501060903120801051309030507060504150c08060607020609030703050609070f060315090f090f050a0605 80
    0x1000c82c020b0f4500741a100444540c00070303203000361080d100d011002c0d0b04064104480c1c4050058820a5900c0948042d10407145c02e40b45040c04040b822003d0040041d03420090300040c1080079034900b0f507043c695031b0844040403420309203260007001c0e040d401d010f035100a00c0755074010241a280150015402a103d603001c040d5a06030034821180e0060050004080c2898554440c0c000080c05800f60b80c4d1485000008424020f400d81100e004581070900c14414448002e440c0c545035015400c1900719075040800041c0070f0701e403a149155030181ca4000200c101440792041d1448180d20950a102500f020b28005810740d02600d0000300c0240741c40c1045a103144103508560007280054403e600c0c020060b02401210307032018000075014860301c1030010005d20b080008610030004e9901402d11541400f05a8481e69440c5c2e001c0c108250130304141816081c0b8640c6580102c0c0c010802c00580580b4140c0030300058850920090314070505000050f00f07000e00030450905041c842c0d40100322035511814410701d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 361759397 1250 361758147 361758161
    0x109091a1315090b06041d180304030b0105150c0607030b030c0d0201121808041d0601030908030f1f03030504050a060c1703070903021201020901020609030405151b250504 75
    0x350800c2c1144040100b10401e0b4803c126440024207114902901e6103c1d0851004403041481969400d01c800c104203d22028094141c06000f500554901803030364a840c070312044180101481113848400780314010809104540b001403804050307484504c1d02a40103001004a0783d0707154040e001c0c18104100900e44008480700040e03058684000915207654044020700055100b00315003805d0082c9000400e0120001e00f0003804440d00324a542800c401d414a134008002d04018141410004544000b03441102600c0d0700955510303c503011940c5104600c2c01070a580f056614138910569004000d060b800001403090303440c151a55801c407903a480301141e805d03101c014023070105510714800701c15092208005542144040c501101e01640300d40015524200c580c0202d01d06a500140501c0c2550301480042d130b0240ca0740016504051605010421a1190440c0e90020410004a1301c80c102e0040c60751440205241d001c03038261a914404501481d203003410481049440b07054000707901e03d01800703221 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 361760647 1250 361759397 361759421
    0x60c0b01151209020a0b0c070f1409040f0302011b120e06070207060c03050c010c08010e18061303031b0906020f0a02150d02090d150f1503020f0109091a13 68
    0x2110b660900b4081000403c03008000b26405014241c0000e006146200038280622422000c0d00d0028600b8810030190360080e44410b075981107024900f82c05645890000e07a1148d0040c0c42d4000301c00240c41c089004010300381c6014424003180044010f80b56001aa02d2000c50f0800401c1000082081a07140d448004840ea8030050b80041c1c41407100500c510340c0d10713800034481e0070001e00f469203441040b130070369452481311000103802400400c02c0e00c480c2c180035504940034050b2a6803186800e080c41d915420001d00b03203a4070810314454030301010322a6118000701140790024100b03604500390014904c10b8144a0300d0014400c1c04107200c1044004541000840d40c001c100c540011101504001c46e608075000451441f642070118801549030b004100400f01e21030b46138007908075035907014601200c0f985506011003c0c0341c0400c1c401c0d1800c0500c001c1c015650100c68030700e8280c1c00000100c44102403600500701d420300b003440004107400d41c101207600f441d50071100100752a040d08940d1003140ca01d45203103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 361761897 1250 361760647 361760657
    0x901060336020f1f121404030f140c010203090604050c0312160303021605210f0301030f061e02040801140618060f0d030c051204030807060b0105070c060c0b0115 71
    0x1070001031502d22502461104043c001242c2161001003140300009503040c0301021920a003890b045c9001036119083d5142d9241c2e803061041d0816460040c042c01c011024401400203102c40300340ea0100b032906440a061681000390358914150034266100c0c0801d550403211803050400c2c40d006450301060301c4100342e000d008034500380600541c0002d81c0c91850070341070b018164200250310689214400d44011107001e04010910301e1a03840820010340f8007c0030540c0d2208091102041c0041c031b08003141e0440e90440c80b024295401c82c1045002800e400d80002c0c0e000346841f0782003103083d4094001e8421640780f003000f080900c00201d507080696204407038103039000d5541d01c50b549650b5058407880c0e400c418094801d400c4903140c20045240c50403109410303808560b0049600c010000100018441c00e07461403001d900341031441e5901b08141c0250103000f01080c0e00c44940d419182d209000b514000d6070048151181c503a070b40c51025280e13190540302540c400380c84a00100302c180803103400940aa09960328 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 361763147 1250 361761897 361762001
    0x5010b07030315120809100816050906040909030c050f070b120a1506051b1c0c030507020901030b1603050603100e0c060f04060207090b03030f071109010603 69
    0x10490007490303418902c600b010740e000e1010881c44c1e4081c080921841c840c2c048a66602070f500f04211101c40098000d07000c1026403010882d195942500c900043c48150411540b61000000080c22034050b51704050801c5152140074170a0590055550000358051713026208924000348034240c0b985294025201c00c10020803003001042d50344540325030b0044010b400003420f101c101203c0415030071a58400070000d0702c08514001d9080c11003079402c0c8104000380080c03c8108070b49030b1158480c04840c2901c414080c03003100d0710040c540100201d4440541c002c0c1201d21540c1c40349440701e04220300b03803810b00560041c442c080c03034250b0081c404d0900031807000380103140b4201b012490394040c1501041440c80343c0038001544c459078840c180500400500410100d44990422030b0003403a080403544007080d47c504102a528080e140803040b075208a103c00c130060f81d54601800d040701694801c02109401420704400016400d505034806550b6800c01e410090000308111200d404644040392810000546080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 361764397 1250 361763147 361763153
    0xf0b090d02011202090a0b19180b071e0606030303241a09030a140606060304201c0605041209080c061605060405060712022502030106080d0e040e0105010b07 69
    0x81440c3c8100102d45000d4941050b0b800030484960159000e44510b04002c11501840301c0240008101c00c0014609102c82071081e080503440d040440c03185010559001a01ca028007003a100d4000e0010903164005405120a1600700d000306030b039200503000a850701c0480700048210390030900404030b20007010b441160400500d21110b504281400c80c2102c001c100c44500c03500c0c24043e120072075028000c40c030800802c0c1c1580314140f000043c2442d01c252010030401000501c0c9240342e0707151214a4840e200001400700200782d20400c85c017460403010205d070000380200951500028425482a01d440d20414200581070300c10200328010488940c0081a520b940340c2042005081c440d0360302141c60079861100c2e180c050a01c2c0d401c0ea8142c8264001e02c04108601b90401c0400100314800281185082c40c500d90300380314080540040b4800400c1e1021081c29540c0940055014042c035409031080001882c20141050080c500162300440c10300810710705030f010610034035049800c158485441c00506039 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 361765647 1250 361764397 361764407
    0x30601020d120e1b090a02030105011409040b2d01080c0409020309070b0f03071707080402010c05070816060305010506040308040b0d11030c03090f01051021060e0303010f0b090d0201 80
    0x301e0b4402019612845101246002c0082040c004c0b0328800030408500ea840034015403850082681d81464010001048140d0740701807201d0001400030320003511805040c0000740034125150380c0311390004018044040141c80805207004c02d810040f8101703000d030720980c01594082c4040b19030a0501c0d0003800108124060340d001950312a80e80350907200640d850312903411454200f01c410f004010b0020040141c501d030402c6400064118a0001501034500b440000b403240c940203100904020a4107a0441009410009840905881d0742941d0900b280d102500c0750b100c0300b074400c402c0003034100710000a040c00d21000322405d0300d802c54501803070142040e01015081e03021105d00e84d0314960340d01b401a0304010900c0954002c1c0e2600007041c0c1e990919440365490207400045a0740207902d007100b40000d0011b032000410860303014003141d0352102640072046054000c1c4000c06030201e401c21200425a10300840194103907010341c110581c1e42074443e0112080c0d03000f01648a41c20290031031201002d1340c011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 361766897 1250 361765647 361765667
    0x60402010806042a050c07080102030f011202120a03020d0e06120106320306040617070303080916080a03080709030b0604111c200703090302060307020106080d0203120c030601020d 79
    0x11010ba0501340c4141c4c00c82e40c0e900351038140c00d800040300420000e902240a11418005010700f400030b60460506800401101c04184940300e841c130803414142085440e5207802407090303a000c90a5415400d01421301030740303c48140070f400000440c0b12020390180e00e406001c0c0e5010b0030008240c00026030928200351424513000345c80907489502c80000100c0c10086a981c11200d0403007548a41d00c03424680140426541a501310f1402600301000a2101000004d01d20040b69054501141ca544903403601500300b000e102c186440305401800041140c14001401e41e9400c3e20943e0761804035591440c0807502d141d454080284080d00203c0030460314586904015010060311480910300781c030320701418642035003c0c044141940c4d11440908003040d40300310340007035240c80f00840902d000c88a5900a0400b029808001d02c01d40000c4042101140b00358060f40152030719904840720382d0107912029550350040081d42c0b5003000c965000130f1140e0b402c00b09881c050039060b001050144190001583c0ba03901d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 361768147 1250 361766897 361766921
    0x1502040308032712040801060b07080d0b040605041a090a0c050a140906040608070f0f0203120c070605010b120c07021807031e0b0103110315091f0e0708060306040201080604 76
    0x5a05000030004000e10202e00b0f200c000e541403541d45c2c0d2a05002d142500c1d0603503c00b540010b014000040894501c004940805003003100000b11101031400040c02026903800c03c581103440c20721240008000541c514000c1c15007151104a25914123031618140c40c0c1e01003011001400a102d1a101280100380c1007003207000c90000e607414015160040303034058205a00610000e0290003c0c040c56a070860455400b0b84003500c0c110500305081c0c44040e40d40d21130500003240c01c0e0b0000e4001041402d070601980e8440d64400018002965110b800d011203400900400f042502e40001080300f6403e04c004032022f95038007400d010810200078501c1c40e6080ca00424007428140c03640a8665840800380c403000756821848800180140981c1c001011920400e100ba40c2c040020030a114100c1ba001601945c28941194020419901c403030546a021b034184030500364116201c0390204011400d1508a4400c5e4003c6d0f46202c13039942c0701000c0540c0c40400341e80180c003280c51702c80840c4682c209a00b281240a035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 361769397 1250 361768147 361768201
    0x9030f05070513050106081e07050d061a090a06111009060905010f05010f05061e0a0210020f07020405242b21020609060105010c06090209070903150204030803 70
    0x595078012070b070f4680d8001d07400c4000c1c2d640c401c018000c06810514950b001381015980ea08104401880d19101c614007801003002e2040201d1650f284d40c0301a04408040d01c10810510a5648400301414403904068000ca1160708060004600c043c4501c5d40d400c1c0072510340c0300520a9080c000c0500c00149950182a908192140c0241d030100d4401d006046607003340c041c1c002015031601c0c6498070600b480d50481c84c41030710704124804980701802c07421021444c0d65241180e96240001081c0d203848241c40d1095007080c00444c07030034081003040000e491140e00a650910142d0b03554109101035804505900181021134078039803070b0354200b09000701004c4090383c1140300e081008140100b20f070130b000c010403a840d40303030018140c11580070f101010f03c1e8004940000c0040c0e040950241d51a00414000c150420810000d808148102038000801d16034014203204054101030500a0002251780001c0d1050f007032a5103095010003881c03089a00312500031002b070b4103688859096100340262101c064903401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 361770647 1250 361769397 361769399
    0x8090c0405070e04090b1005041e2d0507021608060708070504090e0a0218010303140306061306111c02150c0415051801020601060c0305211005090a050709030f0507 72
    0x41c403130740b01d41e01203170380910703c829003034a000c00342128003c4c641d8100c5402a4100100d6115003400444407000039903681c1004504621110aa00c201d481c0900c003160314040d044210140351040c40d44014094001c82e4252600d4100001c0340d04401c0e1a9441211101d9110303800141240c1e01c14061582c01c05020f1030460300d420b5581d40c020081d607c41c2c8079144620340001c04180d0451030029220a2282141010030420f98516280176008a0110200803801e400000001741c0d56690502260b500d107100003182401d80340c480d08024192090500d2180c4c030b5100b002d80581d55a4400e003050001c0024590040450030780d4000507801042001e4043c21030140140404550f02041114103008031a06545290f04c400030b503000030341b04012403c0080e05640180700140070403507010b09503100c81600350a04a94881c054009840304841040001350152440c50601907078072040e02ca00c1c02110803c4940740090744030039181e1001c4400640e001808a1904803003000010000080f00402901600a071200a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 361771897 1250 361770647 361770649
    0x70302150a030624020124150c020d030305010602060f04170a031104330f0c03110d02060601030e0303161103070f030903021302070f0803060307120602120708090c0405070e 76
    0x441405004d0f142c410f0002e094607070065909201c2e03c640381c18144c0e000500c2446078045440c0b400524040d10401d0111079100c40d41c5940505c0502c07402d07cae4060000c501e1658203042c020000c18003801080018010fa41c04030b0000c99540b98114000c030340040d01240d0341c100c0303c4405c07000c583c010428001070680f41c09841c559041c280010300010b0544044a03107031607075030380900c0303400b800140c040f5016142d40c0c0e410141e08039400302103400032940c1404c104903000301c503003403c3e00c008900460b480c0c890312070306c0e0b04c4060141d07001c25403038080d040a883c140a0b0103102d142d59170300d1f404125124621000002e894041c050f201d18003502c880c1c8003220580749004240d4956444140104030258042414004100b0850400c0300042600c3d101c1550110304000e01c03507032403002c81205148043d04c003080100c003081d80780c0d030107201c8103000304596449400e944802c0c0c5403500103504140c0c551440000c1140004454030300031440588105507245c05428011840720030030004010143c14103080000f028600609 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 361773147 1250 361771897 361771919
    0xf0601091517010f141801060807030603060207051522081e1206010f08040503030a1505181f030506010b0a090b0a1d0a1a1809040f0b0108070302150a0306 68
    0x40d050b13422042d00b4160424121103600050140424001c0700c8901000d620320421400035819a6002e00e0302410729103a01c08200c0241c2016040504100d100082c0e030400c000c400201c12403550070700740c2003020a1340e0f102c03650501680c0c0c2c11000020003400b01c00342070004951a000b40b801140b908607410f01d00c2c4c51100700709080e402181070541c208070f04505002c3c156800070610000f0901ea45008082e504d003e694264503400041c0c009211507441e1004502010348a0f90200c02400000d0401203900540741511182914203032940c030000544000159541d80d030090b842419031760040020482079281c03102e840c220740c0c85480c0e030340e0400685841c0850995080c1c8004c00f180d29185c0e88001c5403440c2c0d600c8500030840070070f1550348500c10038102081560f4820050046d071034940301500c1d441b407000c1061509a031014880c082d0f0303c004c45204203c208402d140d194a0054010307480100c55a8075a9211540c2c0d482c036000196002c41101540402c071446e55009160790031a03894081141c55940e0040c2e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 361774397 1250 361773147 361773149
    0x90e0d2a0b0717100e06032803030b1e0111031306080612151506091003140a09111c020d0b160504140906010212040308030f0f060109151701 62
    0x74801007a0024040c92581c0903040500c0c0249100e14203026050000d64111402e07414410303010b2941e0004006003842e94180000c0980003034490440c585010361010030007144540443c1180483e240a071b079441d19040c03034003c0c021421004607144d64086003080054a043c01440340300c42003403008201c0300008040d00041d980081a6503200c42c0c04508000040101ea0410f00712862601c1c0e000c440101c526808000c25a90401c850f0b00004541c41d20010114400e442802135690700071502100c2120355a9241c2c1c030814400751041c048049a494500020007504d40f0940b01401100d080929a9410b1400b181401c01aa200d201d480494040790350103c2d408445d109010748805684004226400d080c11806c1c1450703800d40d290480c0750a0400034105021214041d41c6400340e0307051000079100c1c1c1d0080062000c082083d00915848940d00d15004805a0003242c410004203410400300380314008049095000305016100c429800c0d08080c0b2680ca100a00300d8902d00704126122122000107903005203034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 361775647 1250 361774397 361774403
    0x604020616151d1b0112090501050c07050c0a0605030712020405100305060f0d0b0a0203090106170c010e01090e0a0b040605210706050901020a03030b0d022701090e0d2a 74
    0x108041c0f0042c43c1c1c440c0d512524070302c140c4840e08038841c188407058290310750b400780341c0d000d0a000d4000804000316400a180c0c07082e000b0318941c13801050216030b0b00090042c00c41c4a11980460f10b40d486a1801c1c44906190740c071403c1d010810600100340081d000d12400c04016a06510050070180c2d25030000b00c0e40441403d407480401c2d03440c014807403113042c49201c2c00c00700d030740c02d440400c0d10340e515541c0e0b5071080034000d000c02103899021012503410003083d000100201604503070000d2141d500040d594595482010690105803904040c0c41e90754021a1031004850a22a241145640d142d00b6900500141d0b2401c0c1d52003a40d40300301044a03513800f080b140004103080042440306640056140c5422180c0d000082404002e000f034000c02d80e4000380a0303202c41d904d8500031610031194408030318a01001d0f44025880214007040041d0b100d402880a10985400030790103000342da031803244008440960a038201e00da04a8421000d1040c0660388a5140e10404031091045800d096005160003e41030411 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 361776897 1250 361775647 361775651
    0x106151101271a0114010c06020417072903041412040b0d0e07030f1e021f021903020304090b0f0d0c03140c010806040c120c0203040f06030e060402061615 68
    0x42d40510071000240c0007105503041d0038010550501d2016000d2120f0010190304010502d6102010492580c041c1c4004110b401e6030b9030346c590903403405aa1103110600070701241201c189141034211340003884615400500c1221149552150745440c01e40e21058480d5507400e201d1102c90707080c0080d94400400040c880381c0b01054844034600801025581820003100003a813003454107001044102007900000ca9201c0f02c503141c0d20320f165411900c400c11403803000c0d62044d50705550710324080040e10711100340c40c41942518601410030a8500411106680c0900141c1c0140002d00c44400d143e8800e1044030001000d441c401443c4400083c0341740300d108812940740100701000c01c10080000405107900e04110003070081070000200081081000804051046498100c005c1d01d01e0300a014403901d8001958050146400c03400c406941c0354040d01c0307504a00c0d0301c4450000741e901c1c800c0c8919490811031030054100e5490b207408000d12508105000c82803c0e071000901400284203807481468030b4002900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 361778147 1250 361776897 361776971
    0xb0c0c010c080115050309070e010905060a05010c11060a14030a0207051603031205060f0d030201060e0610080f09030910030606140c100f0b04060f14030106151101 72
    0x21034291000c22580030240807503a00103112400d00c80042d0118015140703483c9407269036060015240821030b0348405641c61800c000825800160341001e0b05c07840050300d070064032595510044800141030384001d0300b01c0b03d00704680c51807403230940c00030681c1200710300d016600c403c601e818004d807951050791119501360380003c00342e0404c0300c244800140c0450100c0030000292554402400001c007080d0421400c0d9514000606140d860511580742800084c01e0850b0016140c87c01034001e002a00913190400903a400140740c5141c107803000442d0180640c0c41c0001911074004140c1401b801800840171400203011080254954400e4a10714005590303001c40c0403440c0c11405414510807801e80e1801c1402004410f55003040000d00020100b1040400030310b00c1c58950050380140207444241c2c0d03109003000000071300d800c0031038000303419a020b084074204143c5500013014201c03142c920500c40600214a0300079000c80c0a11740b152420125040003080302040004819655140915680c01c5008528a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 361779397 1250 361778147 361778167
    0x1302f0405040608010e100b03150a02090f04110a110705030f06100e0705091903060e0109020a05030f070e13050109031e0918020703110d2118021c0b0c 67
    0x41c40700030540131008102145590400545414a54680c800102d44800c4040c0007601d0030081e000016400690700c108604041a00401951100307440ca44074404141030100d01d40f80034481c00c119070003241c41c2030307107080a00e20080e5044035849490440c42e004448000035251024080744085c0325600c006802d05191000d80c0f10202c1220b90010350b8034980f00020011617039041406c0304c0034414126813480131844040450850040c02c1c0e0070081c43c113402c15420f2807a001c4150407024966108681e101286a01c400505070343d43c045641c000b4080e81700c44410880300103180394443d0010700ca580d11740c0e03002e41603444141c02c0d100c0001d42100054049918911041402500840b00c103d544c50048c0c0410301e040f00c0c1e58925414813500d03005259002442c8070802d40125a00201416850103a852440001d18060401f034100c0c550b0b034000f04450082410012054440c03042c11780401e01c5801e00201e016028021803505810710540c0060b0040c5d00540880c0c0790b00c400a100d02400d85c81259a070010724 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 361780647 1250 361779397 361779401
    0x6060310090f080f0c01060b130e0609010306090311030a170105060c06070e030705040905010203010501090b251403030405060907120312090303061a04030201302f040504 75
    0x10a1484014a42901c0c440021240c4080e0072840d604031204507151001603d2010840c42100140c0c9010341c81c0590010303190044d080a4440c40104211901103642d4036005000d007982e049400300d50050700100103200141c442d5210480103130007842d14440140018171458039540c049090344001c550303254294080700d0311241c01c55001d82400d0318001d082103140d040081d6501405080c01c41404aa140d041d101c0da14108500d0000340700003081032110700c00f50f04010307000f94028044d090000d5010000400c880603c5c0c0202c0750071081c1280c420341d00400303030300900f80103003400c0c0b404840c0780c0141248445030a10820246d4040c5024002a048508099101c5c42c9000741a0b409101c140d081803080802080d0040b141000b1000d04000100f5882003916040300108040c0c0c004405010f0406034100707101c03d010b400b81c41503d200ba03d4a0f1404000c81c07884807141c40b0000c0f000c280345800c40c04031603004820340d0080030880d41588100c4211004441c1c0d10541059040f8442d010494003080400480c5024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 361781897 1250 361780647 361780663
    0x120f02040c050a02150405120409020d0f020f07080f16060b0108090607120b1f080106030b0f09061e0411070302011b1e11060c0306030c0915010e0409080309060603 72
    0x5800e180c0d2a00f0f4090324040e4132004080000f4010a560070009030a100061141c209844c4851404590700c54469540c9002034000f0043c4c1d00800e032400021401d908090700c00c4a0741000103070012418000144d50b07208840d803014016000206003407210214032440f4192808045100c0c0e003000c1810302d081c800050102d031004104080691000c41840920380d0401c0c4601c503403812200c0003080c40c81c502008582d003c84010030f000c002c104090301194482d940034101c02c3c142c894960341841088220810089070a8940d644a0351000078040401e006180c030340458001c10200c190700c810001c0c1d80200140c01c55000032500e900f08040000c00f00105503080c031420301c54011060640d0b9008046000007018002140d10100700d03840c542803030a030a180268076070302003e00d100d02282c04c1480e12400001c0716401c146d1f0410700034441e10081140070300c2c4c01100759205103280315003d0310b42c01c6404011121840300810854001d40d4480b00240401c064200840c4984411001000c49040c81700c185417400c000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 361783147 1250 361781897 361781921
    0x804080607200c150a0c0b0408030708010e0618090109060614040f02070c03030c020625030e030a0b0a0c050c030304060c08091f0b060408011b030c02070b160309120f0204 75
    0x41070403c040c01d66102030040720b0210340c810300305448108101c01135481c41100b20307000e0104180c00c41044100f2030004001d5200341d20700d540d20a440d91f40e03001009907906055880d5588002c40d01c510f885d032044520040d5070300c038510f0800405d0440180c2c4824040701d03150340010b01c4d024150160906242083d0040d4082100030507805c5180249a45403142800800e010007801c110b811a41c0800b55507481064070240101e0919808030007596454002c40301c035429908a01060160350070f49002c1c03130041080442d080d00f202030a112956071401c80c000401c0c0e103014000038044141b00b40c16080c0010000b541c0310f00d1282e4000608060780e00c030042c0c40480b004103c4d5009601c503165407542d460302100301c9207046407802d07000b041d018240400184980140e4202ea41690b190419600203801182024114448151000c01560b1200c074000c81c0c490f41c2e0760181c80c556441c10040c1744405540d80b05010103403402490807086264a9407662480d03000109803d503a80c080010140c410b514152061882d030141d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 361784397 1250 361783147 361783153
    0x5072105070206060a1d060402091903030201050601050703020d0f110a11031c0c0809040609050a0504150b1c06020403050609030d0c0203130b07020d0b16030e0708070e04080408060720 81
    0xc98101c45c0c0046401a00211001039000004a002070b102d80d010344050881c0100502e906812f1099040441c00300362000f0340066092801065203540107800b110200c54050b4081d09807850b808400303031061581c903a1940200400c40c04200c0e00340100340034440000b8401c00e01c0010401403503040501e01004410080240e25941180242c01071300811000000b0354051092a118a904030009004010b650b001640c49800e020420004a81c83d60140784624840d110b40755010304080307180c8044031f0982003859040303170702e24208034020301c12200c1c1f01e404148202c01c00b5107019125540c07141020800d8502c12407580c40407030504036181c1d0074000c0c808407051604c011410180441c2c03100004600610030301054400c00181c00080d510b82003100462203400018140c130724100004400d41c0c034034502500c1400a4508039850301d0340f0382e01080000032244900003c0c08280e060075032641100b83c0242c0211078a00c010040000c0351401848818811151500c40503402c45003e003c0c900c1948015400c1d2417150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 361785647 1250 361784397 361784399
    0x140310050a151e02030c07090902041a060d02090f040f0c090e0411040908090d1214090a05100210151a190e03121309060b070b0a05072105070206060a 66
    0x9980000211000b80501510743c1140700303959826811403107081103a0001d03019494000ca090300c0c494021101c2c4601c00e07141040002501c0101400032004e40f41c0d1660b00800c10040510402002e030050607000c21f000301a40c00c00c5c10504005012100c11402000b200c0b40c942c85505078a98210f4071a00081070380c0e540001c15480e16950760006501d200020f0f901c10740e43c4420b04001d0080701d205441481c40003a000c8180000e403401c0c15030704007540b100020005404940102c101d07101c2a800e96401e10400740060016505150800c116170b0040e16002d821886184c145100d400264000c0c03144140c00b9180301d030500760038980c1c6a0071001200242c008501d404005c040c49643c42603181440d150b002c2d107000100e92440b480040c1c10f1035400c11401d104030401103807250711800341c50f0300c04080b0b604200c000c10242d542e60000780c0d00c500480f40d024000e4030385c0c036000400d443c0141e0803296000d0014070b000e00441c020030b0020109540d8810b00d94035444e944100300889541c04100460300a101103c01408003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 361786897 1250 361785647 361785689
    0x60d1406011106220f03020f070510090e151507060c05071a0a150b0d0b0d0f061107080f0d0c0206060f131803020f0723090601140310050a 61
    0x6200143c44150440700d82da80c00d80c4050002c800071130113158800d01070701c030444045c00c0080d943c20b02044066201e008403140040c051034000a1919808035a803109010180741005035425a140180324012200c2c503c1403060255542d200308440341c2402d840c0f026240c103a00c1c01d2001c1150740c0c262160045c4101003203900086015104d40004d06010f14901030459a44d45101801502c1e007820101d20104881c400400e803111104040c1c00c10f5038242208001c000315030010000c81e0071040c08082c012203001324911000c03904541040100340b805406140c40e00800e969041c0269205070347c41c050301c001c042034001540540b40680022011248010907442c10500002010107030340206051044000944104404405405c00c02894914203048601c0342031908019469240b020100c007210b010f80d010100e070884001010f108601e5400817004040c10941c414400c4008000d0300c0681400782c4c0086004185070344100440c400c100c44042144520f2800303040c4402c082d0550004603084250721051000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 361788147 1250 361786897 361786903
    0x41d060a0b040b0307021c020106080c03060c1c1103010603020d0b0d030225120305030105010917100b012102180a03050c0603130f1217070f050c0705060d14060111 72
    0x80e10078103141142c0c0c17519046800d178944040d9900f040c1140031030b08001003240b5010b601c6202201c000d1420344a4070302c041820141ca440c07080302c04400204e41030103041c040114441058070204001100007030344000701c29082c5800d41090f0f00400002e070700000c82401d400114041e5807400882034514550a481d1a54041d403500080507100103001043c41c944018040a0a0307810300410141d203151143c00c0031814010300c80c0d8400d0086a022400e1940000303600543d41d000c1c44540307044034000d40f803201159520840580a42c0c1140e9040001017050459004103001c0c0003049600340c2e140060792004840ca6450442180709000f0344680c0701da01040000c40d50200b0a070400c03041c102c0300c940e031781d80e2006801181242d100300c015040c241e40840e103004000c2c440e1404050550307942c5501c00307415903d409903104098101c0d040340c00140780c0c81c00b64040034000c02c068070482da116810b4405e02920344001c60761542003030f0b072000e40707103501d40f0600710341c50769141503140c6c00023130a2802d43e80603054003042d165 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 361789397 1250 361788147 361788149
    0xf1a0f10031e020415030509030a080403140403080a0f0f030212040221030a050904050a1e15080a0813050604051c02010c080c01020a0801080c100e060906041d060a0b04 74
    0x185034a0700107040d0030142505070880b9041402d6800c5442e5615400c90f40c450314481c54125000c02d15002c0404c0100d04000705640c19800308ad41c4000d0a5a9a0b81c4e040f910815144203102244030f09000100018500300090200c00d007090707071920f0310315031040e0005200904003004c04091500c104480d44000ca0b1501c03401e580b280d01607401e1401e80c1496003130f01900e0b00781c4020b020700350300010441c2c07801190320500814031048119000d00080d00ca101c9408110781c201c18600e01c038090400c2c00d209a40400d0340060781c0511070082880d601a503520750781802d01605450844034060000307428241600056081006480d080d102c5c14181818500480ca030115041c481e50b8250540f0b110032000c580c4142140302c54180d000c0c00494464202ca034002c2c0c080d4102800d03160110b00b800d4004110301c0d10005500e00d018400421795441d124810030107907141e210b181e550701d4001d03104008042d480e403200030080c8000c0c02ca581180c0701c4034425900c60001c889019144a03c84c005120080041c10713050300503a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 361790647 1250 361789397 361789429
    0x10031506081302060c21040e06091302220f02090f0d05030415080f090109083c0406080c030705070305180901082409030d0506060403060f1a0f 63
    0x100310750b01c0b862840500b290765030303034000e40c444d5000035076003020103001c41d41c1805081d490300b10a403c240c0310060074400d4001c5008441d9202001d400040d054503104068039008590034441e0f04211070150045080c00c1503c4503a001c0c20221210300f00c01e02d1031540300314003c0c00c2a00c00118105104900024081c9441c50900340c030803c5041c0314031003842402c0c011140140400d4000f0210381c001d040024007a0481101d282c0c0c4d01004240c00281c410b041030046504050b0b00c001400d241c903500c45844100109000400e5a50504003aa140011340b29100b1480d4840000030045442e07900d800c40080891000600b620066082801885082c9030000c0a460509905040090703c95484002c2c03500d011030000100c5500c0048a0300001382c00d4404a041c402520313a10a05024071010307100b581c00756003401d613551107080c0d00c2081809101031043e80700c15000440100700501d029504d444903001d0340c46082040c0521543d4902240060380086080c0d41c404006454201d090010b00000944601d000c0e01c100d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 361791897 1250 361790647 361790657
    0x50405060108120306330a18051903061a03010f0902030f0d02060105060d02160c090b0102030406090b0d06120b0702061b0a0f09050a0f0510080f04030c080708041410031506 76
    0x38031000c401c01c1050f140c040a00e101d01034440d04c0ba1440246403028110303140231148101a004180f900b08070030610f8100c01d00710201c2842c05e2960f82c400000707040d22411001c00049850022400340e0307081c02254101c030f400c600c0c003240c42e00b50781c01014280007400d005840700758001211554181e801151050443e0022510140c494040d1010030780a0300c00c40009450414800c840402017010144858081c5c501c084000c010f10030b80000160703aa441303a402010b001c107043c1c46003000313601050801010801094440419140ea03641c440380d200e00c43c2d42c3d000301c0300c08a66904120b130041e41001102d611002034400d02c2c004031105100d8075810703c1104002010010b0f51104410624022440200240000303030400c0c205035599107030510301c103d584c02400c0c4103c40302d9001007200c03442031070b41c40e000704482c800b80d0f0115150707982e094844034050314007101c0040040c42007001154284000e08001c05000d02c0205480c4201030402c80d006508000c00424149000d4207040340c1c003200700285007510450300f04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 361793147 1250 361791897 361791949
    0xe09060a050403050403060905030304170f07060902041808180108060d1506080f070305120f04120f020d06020d24170309090114010f0207031505060f0301050405060108120306 77
    0xf0494440c480e0b40c001900070b60a102210041000001c011442240185a00130f450303404a01240390901c2040761540180c01c0903c5004040340380e40d4400c0f0005072004000081c020030944121111018102c0b0540346014042042070590000d0b8000d0520f003a000d2910300c3d12403410303d001800c2010080300280a00b01400300f218214100c940c40000900f003500200c4049002c010007a03983e4039a5800221603500404000031142d850382c0c81039408000150b070390242010b041c41e40e00101c1c02d00d00b141c190394040052100310b0250310f038441242a064019080540d856154109550a82c3c00c3c29a6001c0507802414002101c0030784038001c0e40030380e80b000c1c203400c2c0c1c41911905818618002c405026034008481000020490701c26114000314420a0b01c0315400039155403c141c2e1280e01520000c3c144c00d15400d05207440c0c082c0b075440b6030381c4044001c003849a842080d6003c2800c464bc103d40841d01e950000f13005005a8404002110801c0000802149589050808580700002c41b080c21482c00e58480c003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 361794397 1250 361793147 361793153
    0x10203070b15090a1d070e0610090b2205030d0c0803191401141002120d0603051e01200702090703090503120f0601030c0f110708010f02070c0e09060a0504 68
    0x2204800301200411207511030030302c11100300080c041c5209814070211204400c078924500854003a0840b07c0985d903881e15681c0d001c081c0a0720800310083e1008001900b4004501c801052000c0c02d040a2542d0a05c0e50b0100400c40c4250341462540201d0b00c41d0703105201d100078465101c0140f0310700c2c0d903100507059203039143c03020300c00780c0c07501080c0000ca50a07042c02000d500c0065030581c03803812100310035044140c80851805214401ca40d00c00322000582100038241c150f070b1a950000c060503142d8003000076a103540c907140d02e0f0400e4088455002041000d44107081c0c82a401d001300c0c4070203041035140d000c0c40108c00140c842107104950009008098810004152038017a030301000300f0582100c181c07540c9a00041c060302400c00d04807000420070400c0c5010498a500c24414211211002e84076003c600070000c1080e5229904100203541d54403410f100429841003e0041490029203440b015846080700d103000c032400781158010075100c4509000b00100a5400680c5a1300404480c0c0001400d480d241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 361795647 1250 361794397 361794421
    0xc1724040c030209130203010e0708070e0604031421090910050a0e070f0201020711010804050c060408030414040c090302060f0403050105010b1803150115020114010801050402130506010203070b 85
    0xa40600d511a1030160a0700398290150003c0a81903422100180b21401d08855001240000e000d4103540c034802100190159000364120380c0c21084e60f0a06591203052030b4002045a445501304440c043c1c04044000001c00c800c21440c6001d03010b0a040c0000d03000b260390440441d008815180d841f65800700041004034003e0340c05071b0b016010140c600103d042e1112641d003800c0505a030604000307420500d610000034810706c240d40e2602e6000301305c6030782c00d81d011004455400c3c010f00203840e00d0107a40b0400d003060380c4903001000100721840107075846900d010403000c50702c00381340380682c025070501010a40c1c0f07a5100c82c0210603039134119003d907103401e003280ca0802d03640101d4200802542c64903002051424004014044100801c0c01c03107000c040c2982c083c146c54190300c00382d40012812000043c0b005085203440000510403d10002840c400e0349020320b0005130081c0d10659650b5524018041903080c20410010810340c00c00c4180864202500002d41e02d00c2103450107000030035100c0208100300201 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 361796897 1250 361795647 361795711
    0x1503030412120f080705071109100e072a0203100c08090d0c020604030605180d1701270209012106051206041e0206040e1f1403070b070305040e15040c17 67
    0x2803d0300c2706524100e0f1100780c0002150252400303051428000683d014464807070f014030083c1400310b01285c0c203001d202d5035903d451200c40490b80b50040e00c400070f9140126100da440b542c0c105540c1c5821905100d10485e0a0600d840c00038000c0142d60075544c00541c99550072074003241d500a200054503584c01e085540804103e102c1032a850140d4068140c1c0c00303500051600c140f1a42b410411800e903a03504002d032051140030002c20a42c14110038100094100d40d01078040b142040c14000300012140401c20111a40c400312024201e41d07c08041c0000d041040c401d181070b590b08402020203003001e403074811201c0c06024503640e111062420801c11521000203480080c20401041710650a1016091110606a1800840307032480500005158107071200d0407407000a0141c040c000d490f00b0b1020b030140d90340c011036099052000420002aa420040e1030300b510521005202d4070105100e48200019602440d0a02c8104182030041858041f00341c182c240c1c1214000d41948601c541c103030154400070b250 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 361798147 1250 361796897 361796899
    0xc0f040902030d0804060c0c020d02010806011809020309120703080f07090909051f06120206180306160f030515010809210a0e061e031503030412120f0807050711 71
    0x81c248004186642081c202070045c1d01c00e50060042d03107200081110b50062081d0080d51007086641304101650282c010071f0342000301032620b220844015181c0c6000c000300d9903c01424582e00100b017001010040c42180c80d03200d00c50411915184190f2401030002c8405030003590b10841720008500c042d40540c000400410206105000e03520660508a896250035110902d0841b000d8244480c202403510505040e1980d4510000d540401602480fa1035004110003082920060040607025a0308028007032203020074a2003e1300890015800070910070400080d50306043c2001c0c14880e06082c131407204c2c0b02c2c881007031034500701c50b03565850380341d107010f03030215141e024029240400383d5904a40301c01003e0300c00b46600c49d25046104981885410700c1544140d07812000ca18042c10641c2ea010030066030810005c0400a0700bc0b500303400020b05580c881d9000000c901d115002c00810016104001d0031644641e08002c60303d9448450094014000180901c0030400000741580400003121004040d501c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 361799397 1250 361798147 361798153
    0x402060403150f1d0f150c09010c0c0b0705100b060702010e06070c060207050109170d08041506180b09040201021b0402070614010f08030f1e0f0d1407020a050c0f04090203 75
    0x8a115000b044c00c1800301e4942c40a40a01098111189400180324005002100f810b038590b50314102195440c6d0820130000b410496060610f001280406100d03c01601c104c0f046c00c0c0d61450246881c0f0f15000c000e0301c16510380c900b042c074058681d54801d002d071172960750282802180c00b80c2d804001030981c420311500070301c04081302002007685580095400305444080c1c0300c2540c0305860f00320804240510010020301540700350408030101f8804c8001c00c3e0131030300c0341111010000100e070160064440c0ea800c82c15212994004071441010f20740580a114502034039586c02c0b508107500005e4550703003080311205079201c00a00e40e268a4a407076044a104940001c0104000800e00c180244884d800707225511203103107a20400700d404100402298070944029030054500045280e101215240f01d03a4900f11904050040042050700d803402080c0c0060380b80800a5140c402840e04a950300000d00a100ac640c40800717520000b0318002000205000d00300c440c480c4000341d140c0010041d240e400340094143c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 361800647 1250 361799397 361799411
    0x206073906090f020f01020a2001020708100f050112030215040c080d052a071205070b0406030207030201140709090b060903030705100e160302010309030905060414180402060403150f 80
    0x1016801402507403a200702c0c5c09404003d01d90004a07600d020030200030307000da10580d9040345c078400e4285040c1d01c40c402c1801034a62507640d80003801d0a05496140c090605c076200c62100344940340c60b118890140002d0181c1f83d0700040c0c280c900943d106410000c5100c4030b0b15200c081400c0c0b2003140c800c2d10080040740100d5408052076800108950840b4080c2d4400c03400c80c41c0305407061800c180350156000100d03401090003910341242c038400d24111580c140d601d4050f600000c262036000c0b8008001400350341d280580c0c0c44c0d4151030000c2c03c4a01c00c514042300c4030114010f001510f94813104100407070313604440c0420401800000600148500d003044d0ba0b1511001890760f04000e0040b4001a400001000400c52640207031000d81d221b607c018201e00112a1408080c40158041da0081c03503490700078a00303d07801c04d07124008241c59903c140c0207504114091007804207507280400d0201d90302d0414440011711401c0ad07901160303060080340001071170b0b00b8aa8642065220007a03000016240c40c03104140464 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 361801897 1250 361800647 361800653
    0x30503040809032a0a090e060708070c0602070b01031101030c05090f01170703201305060d1517071e03080a050f0706060314030a02120c0712050d020607390609 70
    0x5244d015050056581e001c0c00a4100b070b05108085c0038240c1400074140725910020100ca0301800200100c00748410201310201040e028805410b0442c030070300460b852941107003070201c0b00004c24402d0030304050800325070090b050f601a0035198007480940309500d40307000c05801a40d06d40e00b00c900e281c0e0b4080380b80040145056054101d0780d44c01c468042e41c05010312075803501680610401181c0d59410f6080b800030405030420000500307034010383d07840000790781c0b000d080b1a040c2403540c0d51082c40710500c80d41000d0f0240c01d081c0f050b4801003c444189205a2001c1e03038a240802160380b0000d4022840829400c46440c000d10448213540c0125244554031641ca02d0808010300e22404255941c2d00b10254100c032002c0300208590904200350000d2081074005002503849234007601c101e03c1c60b8011041c00244041c642d0540c01840303071245000e0b2010040c0c1000c02840c0600040c001c10030864046a207003400400d48807500301c0550b5150440451005080045006240c62840201010b141448090074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 361803147 1250 361801897 361801963
    0x111f0e0708060f100f14061309050a050402030c01090f050607052b0e0603011805040219030f120306030308010306053c06061c0f0f02030c070c1203050304080903 71
    0x7141108442d01c000a90305c416445070b120126004a44904072801c2c540c14a03031805202400480030040c5080220584840c054400e5a0303090301d03281c51131070700d41d0280070443c034081c41030344015242032078109500351030704020044125292090902501c0001a210284001444042d08040c501e00c9082d11607800b070b0b10600c0b80b0340e007079a005000288082e4032540700d900e0f00c4000c50f412200c002d0404940d01036480c1450000700400340040360b0101440704881e40320107035210060700960141d80740e020301110a0a182070100b1005581404140c03071320f80244000313a0881c50840c10340c2c3d0421300c00a425681c0507110101c034002c401c0740130120204085940105c02026500d02448110b0156031034041c0c8076030003440801d021304969044058080c0701d10003c10352f00e550040c0210f181032040410566880b000d607100700e03401540c850b85a010b0010b009428031103544016001040a40c0b000352003c4103a440003011030002900042c198400054580996541003125800b00080800c41303025010b0b0410351140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 361804397 1250 361803147 361803151
    0x50405220b01150306060e04020309210a030b06040806070f050702031504151e0908041d1b07050c0d060b030d02010e0d020c13180c09050106111f0e0708060f 69
    0x2003e0303a0341d800440c403410320901644003198080c1d16a80070400b0b8842c01c21010b07420081c281c0b092845a02031840950045040b048618101c80254075583c01c03c0800040130385402c0d410304d134040c1508000c104a074001c0003448960041a0f03281c00350040c074140e6021601c0d8495260040e505114412642c070b55004205143d031300a40c4194840340b0440705550014042c0c0310324100940c001041d40c80d03030702140ca80c10303004891510301c43c803451403410307481b60b40000403c44103011001048200d1000c11805403a200d4480100203c2a554107003000b90940e15107564505480c6410300a00442c030b900030800010f034009007070058004003650004850500028005c3c0f80c0760b003840c40d02d841401c80f0250103600218102d00005000b511000f00408101e20b40c0e0050303c04d40d12111540850503119002181c061400c0d003001c0d10740d060000c501545400002440704032001c0d4041c9090b040040c51743c840d16000c00080c1d403000b80c40180820000301c3c01d04980c0c10128660300c40c84050013100208803078003a1004181d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 361805647 1250 361804397 361804409
    0x90a030f05100e0a02010f1206090f0614010c11150d0f0510051203031f05060318100204120f05010e0f03031b040315111b0a200a050405220b01 63
    0xf1068044a0340c1c01c0e03403000709840c0a80031074a14050079903c079100d0041124210302c211000303c1c03c40da40721003600444405100107070059030b660f101840b8a005000d40040131583c03d1a05140c0080d5230348584d107500c141c49984510406008610f0720b411070f171a4003600d08d5054001401c0140c0e6045d1b01d00440a400b044038016036414110501048914011402c10700c4440300d03400441c116520604034440e007592919440054056400e00050f01e070380c507880290700c02c078140c803000d0703484080c100505482c12440c000b404041d5801840203102c03880c42e040176071200681007214003032858030a0421900501310701c40d02c030800340602030003d07801c0e003030020080d4007902080c050201000020b0600d515240154080100700d8540813005403a07039180c0d6003100e07507003c1a0040c0315180010400102440d9400c100700900e0f150405a100d10606c4445640c070150307043c00da071500d4000b110000004041520a0041c1e038030499440d804280b0b203121107002c4030400c08142100048480b5036051420032980300744505 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 361806897 1250 361805647 361805651
    0x90109210c090c1b060b03060103031205010b040605090d02010e0402030717090c090c0a03110a090602010b09060f0d2301060806250305060d3903050303010308090a030f0510 76
    0x141c458107501c112440485680c0e210315610658481589006843d0981030701c0781603d54405900c1b075603061203064000c40c40394851240b00109a20210141d8405a00c001c0800350180010018540c005c002c41d008010301704c3d8a64484526440103a5003400142c003c2c0b6001032000c000c00c281581c0000300104004103408400c0d2181d40c2c0c01c0007450360b61841c0803081d60486007810120b16140003a001610f0441ca41d401e01240f080b07030b11181e80d5400c5e000441100002541c0a008220040d020700c91114143d000355007242462424502003014003920145090003011b10301c07080424400c0d40c5c4c40150010001c94071040003407050011003400b1300580e026005041c02200007040d4a500400c413081000d903080c010800c0d4a1040343c20580061800a1500c0d400070300c005408000281d017061010380400c0d40c0d00341d03801e02802040580b07044d940c40c55141421345840e42002c0c400301d4000000e81e411640d000500326640d12801000c26000002c42c5e0006040083e43c28500c01041008220714107414114902 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 361808147 1250 361806897 361806899
    0x501020114010315020f0f030903090a0509250327060e031204021306030b07080117030c03040e150607140105070314190b100215010510080705090109210c 68
    0xd81c0e0191081c0700003084820910880c0748800c0184d005050500c0c1c103160b14504007070b840c40203005907600480752001d40307400009045820349000c0307603094007600302a20320440c6494900118200340c0a103403808d014188611801c9244c0a110703400800c145003400d8070310007103110644d80c1c02c0517800e80c511044550b981003241c041c59080e0008150b420a0b920022800040d8880b0380034005043c0e0720900c100040c40c1c8030322010001c0f44161440a004000942c0d445d0724a602d002c030b95068840700d1030824809078004100583c11403d000003510f094950300b18140b50a80c4480080f040900d148054561b00603802281c200144100503c10200c0141c00070000d01a66965040c03c50850f001c0c0050403401c03486900200b64031001c4c22100781440f60003084005003030038048002440000340600c00400507807120060f20382d070600c05a252401060181c81c944420014484081d1440703c0040a2100b04013010409844580c840c01018005142447d404070380f8240c019600440c07243c88010a80380c41c0c1d007403c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 361809397 1250 361808147 361808171
    0x50309040b0a09090308010314061014040f05070512090d0c060506030f0a050a1110051c060b0309010b0a09020304020303031321050406021902062a010c03051e04030e0d0212070902030105010201 85
    0x2a4ac5204d20540340c040c00c0f205d4202004400b01381031b0142c05580142d0354607044070a444003482290b000301400c2d200c403030700c548250380c8544039248000d04400c41c903000403014089068002c5108c1d180c49600c1400410540d41c4e00000c42d280006401c038510242c8220310382c0406100000c40c800c00603600034a080e0700384003601c0041c84103807142c0386001400103408010440800f0411070301c000007200c041e403010540d141da4107040425a0000d0380c45104030f954a071064082458030b0700c280d0009000001c01035056280c5a000a80c480c0001400f080c2c080f40c122154400704000010522001c4540c003003510891181c050000381940c019000380000b41c85007006980110002d0022110000d60041001d407401c2c807920060110001c1800081d940303100b1811400711041c1b02800740aa011810f56000a400e261000b0300040301080c00d0308080002c2c03e48400e22020039804090803400341c20a40350b0031960840d070310100d4489100350311040c0e07031070080e03440100d8100c00030740041d030480b48240d009020445c0245 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 361810647 1250 361809397 361809403
    0xa020f010c050a0f02011812110a21050f0310050a0b0304210e0a0905040203241506071509020a1e150207120303020421050309040b0a09090308010314 66
    0x28400381c0412000d224802001d0710889211605074810300c00031540881c030914a00410b10b003542c00311021131a030304005c61021b40c0038608544e5110002c00625031b8208a8650089100c0b8029040e15400a038030041c100703260040040302c1c00e035002d01d07030074980e646401d15014444110500660b4850f24800e480002c01aa4407810f882c01030b030b005540001c0c00c40076031502c1c0307501c00e80640310700c401c0c0004c92680d41a241e454000c68002846001350114562030302d44101030415492801e280d0102248602005859031000c1c90301d0340c03000341c070160481850f0f005000501070b0301070018010400205984825071150154100b13101c643e200341e030500d4104d41c0b110034817800d601d001081c40002002e22038080103941d160f40080c61f170841c1c090064451041e19194459958a59102c0c1074010a400090402c11005140346403280142503076035007141d41300c0c1942e600b0349a2044801e074030f00c9280c55985140c03031541c496402c4801030549640c2000098403510300a405014240301c20f0350400130305002da400b00c6d0008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 361811897 1250 361810647 361810661
    0x14123103050c041d0f0115060302070512130e130b0a1a151201030b01060e100504050f01120c020f0f010b0108190e01151404090c0512010f0504080a020f01 68
    0x18010b07092611942e81400020040503581058910030b8134800c4168600901004550b03640030700000c00c5081c051020f580310440964880420584100f007800b020500c04030b50305490f07100ca801219035862071500400c10090032a040840d245144006000000f820360b040b50041c03030b20504d90078196544545001084400390703440711384000325503085980796150515011000c140c22003480c40c10301100c040e000710320790400d8004441030800030005024041d04100c5518041c0c1c0c00f2107030400c003d154460000d0641c002c91041d24004c500c0009440d203030b81e004a4400400031050001000004a5004020755684881e0310403000c9015403802c5108000040c010b540010806071106101034688001580c07500301d40c19126200a5078400c16607400100c28000c012202001c0c00b1110a40340c24400d0002480001281a80c4140c0c40c00311050005455840581c003200c1040705d039854400402007442d405403101d0001100d030945080304000c100040d20025048020160f802c8502d0140c1c00c440039422500c0c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 361813147 1250 361811897 361811903
    0xf06030c0903031d030703060c0c1b0510031a0409030e0f01230c030d05070903020a0504050702100203060102241f06020a0b06010908060f0f090d090314123103 70
    0x1d0802c42c6030016560983d0002c6491301a00311000d0568a80b15502111604903001000815040007842403140202104c0710809003a9554640d6a15040009490003036000400c070074107484c0d203a50050300d2025081041000030103041400302a07103500d0000c140802d403950940c40750b40c05448a4525500c1400345400c40c1d043d910031407442500d1420201c00302d030403c80e0500100c1c48100f03c0e0380007a10541c000c06011b86000e1315000344046c210b01c100400c0182c0c3e5000f841c051458101001121640001c0c12950a030340d654005135640c50745c00c0101e04002c00c0b00d00c00b81d500304440c0203a0815009540000b4401e0380709020450003410b20743c244096408992240b0703c016400307001054081100c84e120039800440c141088515280c2c2d501c05030382009c004036241e01640400000304058001c05003c220b43c010456405044841c0460b000070340500100d002c054016104140c429404c5801008a525442c0750070180795113803107485581002c80b5210b112101a02455803008140b208800203804003940e038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 361814397 1250 361813147 361813157
    0xf03060506040308130b0711040506060903060f040524060907030b030607030b01090e13030210180f0501020c01050906160203031b031e0108010c0314221106040f06030c090303 77
    0x720b580c4804056405c54005100c00c1c5110041c0040c000c10140002d20000c0e00c514900c0404466207000c010444000a00450298408001c1d800c4255000310785c45901c201c10a0100080740c0310790409a00e0321003103c0725805524034503514a41000c00e07040ba04d40c462001100c030041d103981c03507020440945d484400c1d4a60142d02c5000400c10440c06078001c02c540304810301d064040d640d0b462503800f02e95401601c0340d101c1d4400c2302c100c6000303040c1d050106204021042606200410040346038501091014130094840c45903040c07a0700811400b0340450b90500304860007030240e402c21905668030b032002603900c808001024920f60310558000b00c281d07440f900d06140340006d003110119010907198002413402112500c0c01000f0381014042512990180680c000001131010410002800706c90400d44e0010790075002408020b6035014189400000c2841c00c882408070645614017071800d011520340da19400030003c54042003400744444c1c03040440d28582d60500c5030201800d01910541424000503001034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 361815647 1250 361814397 361814399
    0x60903090904120e0a06030207051905060c09040f021209190c0e0c07060908090406050604031709030709060b03040209070e0a0b0903030f1b0f030301150f170907060f0306050604 78
    0x200001c0309641c2040300ca0804c0380440f0607280000700038607481e4206c071010940c04504003052260410000803d812402001d103403465180e200c1582d5480d005000c5203d8140004480c0d403d500c0313517000303120703083c401000c2552945031344620034030111000c45522a4611450702020000940303e419191865003103060328260714201019046d018000030064070407140100306041c00034055110b8201c0356801080400d8544081c203041100703942c41680220b00c203a00c01d01092000c01c0c07000c02a203035103201c41850b80b075550060201090510103280e0110903200d1400c0000503c1081d80c0000798412071086400d501076650301d1405644c10700321014425004000d040003482030500510041160701c10060840382015840000003055910241050130285200300480b01d8001042140c2c400c9200070001860540d03040c080061481a100c005003420800c03086480352005006212038445554408a80311641c40d2000c801030340c1d5116846100d00080f114071a0a641da0310074410b010584000071300301d611b01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 361816897 1250 361815647 361815653
    0x10e0703110f09040b010c05100507020601061d040c110d05030603060705040e04020904230f0f1c0318080a0302130603180b10051c1a040803010b131a0c060903090904 73
    0x280200c28105e414000100c6145021841c01c2200c054011a0100040f0b410325004c04020304000040e0301c02d02c10312285244051050402070506540c0800c1910005521105450100e88400082000c03d40754015107010b01e030f086034408003d6124000a0741195a26251110103d845210f18492200440304c0c07040800c00600d44051600c0d0401d004440380c02f01c8003a1564401c07040004035132009103070340c0b15015034085210300b07200300e4030035607010f0010700151900320310f104d018000300c03050720006c0540d01e85000c0d000c00d120280100c6030325048059a0b80300e0301980e102500951016000016004240c507000407054800d018249081c5140001241d4484841e83c13504c00ca100081d082c040604404003010440d030712240348040c40c0c605010002d40006d00b05003024141d080e40112071000300e411240c2040040740844084074111041001019074440401c01003a402010702e800030380e42c0540030b00250300fa42c441d240117007a0164100c019901180c0391849107680d24424880e181d600940d00100203004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 361818147 1250 361816897 361816901
    0xb06150d0b0301090501020a110f0a051c03090b040606060806040e070b1303051b100e060a05160204060f140303070213020a1407061506081504051509010e0703110f0904 74
    0x114405000814aa0413640e82c1c542682c1007041f2200009042280032020305400f000141030140812000d04190034035611f80e56207820414880da03408030341007512401c1003846680041d400c0758102c0d6450a0b10700700345c42d200c406000c1a00c0b07610001454080031601c035103407911610305000190801405102d00e0503240008540003010f484541a25008000001c074030309005a4016410080540d1140e0011004001d01c50b04c848038a40200000142c25a0075515090220ba02c00c1c0103034100b0503200c947c450314000c8816803100c40250030a0034450001214000040f040094410640c10124034180031000d1568900480801030361280d42c1e103076042c000801c80d50041c62800060310f4403903240582084860615440740c0812915130b0f86e02c0c104100d1644031502d901e0090143c910b070040301c40c280074104c04030f0001c080c01841d100701d60340c1000c2030030700d44043d040c04001580500988100e6075903600740710034088210390000200341050f015603103000d40c5008840c9601a5a4103c9003400a01814040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 361819397 1250 361818147 361818161
    0x21303120905090a06060f050a170414010c0206071b110402070215030108030306210309012a0c080d080103020d12030f0f020712050a0210240e01030b06150d 69
    0x1090080700341c408103041d2211180244145064003012032004d2524100800c030030f46940d186400c1210600204651a500c000d1143e84400711448408040e212030400c960302201c1d45820103165868240740701916030700840d8241c810f410340e8030354117420b50181415241c103e50600d0006c0880904100007209407501394003411295001900b10345503244040c02c081c070306600a8000c024207a201000f044078a00d0603649503c007138010b400d224103034925600d004580c0e078019214814144480d04c400e29501c00c0b042e1200d804098507881f542420b400c03c5082c02d41c5020494043c2980743d0050341c008902071801184214100d940c0580600010442515a88014602e103014001016154848c0c181c042805002d8544842c14040380140d40b140c603858846910b010b580640710901c00c1c180150000c450300400c160b114511002004100074070314210300d126210711404802c1e05800349020200f4112030b40303c05181070b00d205034024610380e20fa080800144100000700824820350400481641c5800e86d00311035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 361820647 1250 361819397 361819433
    0x60c0c0a0b1c0509150103030215010b0a05030a050a0b330c060c0f09040507110c090103030230030901050714040b040902090301151401090611030304030f050f0706060513021303 78
    0x85e204a0302100c0300140c0450a070700942c016449880d00741010185d030b01c0c4060060007044d1000d4908151000003529501000745180c14466982f40051090865034008496212000308042c00c03481502c030700902c070f051071030541c0c550b09242c41c041011600e4207803040700c0464040300d008003400da84a0302900c1407030340b00b8105d0b4a000c00c4188840480c1c4e84560050600030406602e451f2042c490349840540307010200302c01244103041c201c00400111b600425410804450000300c045029400000c032801c02d41c0744e10504041440000402180384410350042c0c1c01113010781e0315441301403141c40800d507070741c0100d0085014115042104108101040d070003008854070180000c00c5034420340b46c1e0b081c1408061350000c0031004a50000750762540e401780001000e000e05041046601c00c0140c07441d81d41c1d00009000509100b15000a070341d003540030360161103014801240c11643c07a111445c00300060005c500c0b646000307051038014085038000600903280c120b84184d02031009980b4589407800d402501d080c401d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 361821897 1250 361820647 361820653
    0xa150e06100212030c031603090317092e0605031b090714030709031101090f090e03120403090801060506030702030a080a1b0509100e060a120b060c0c0a0b1c0509 71
    0x81c6000d0f54243c000b440c407404903440c0d06503d078504084880f0704203102c410f02c8800c00d403810031410300094101548085100c101c0f00504559654103060300d2a021622126060092012150660003c9001030191140300b0403201448010390381c0c0181640e400c1c80f2258034001e4079504c1484181810a00030a691085991800c4004104000500c00d11580190741803400603840310303014803d011104c00080482d4500f8640300c12568138241115266203a41d010340c042040d100c1000341113240c410030640e40c002c860a6031070354080c10300c0c0c940a1300580c414890680d9650800500180d03614020007a01c0c89082030303401a40c9441204c90f03003256044001441e444c0710381d6a801d00362800749154012411101c2032519451b903070310318007401c02012000b0105148200000f1042000b190344401c801e50f480c10056061a500000320a011031004d402c00c00150307a08050003007400e8454038400940c2040d158419228003900584a1120301d00d43c1c482e0a10300090441020044d4a00a4007684440d903c4482d800503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 361823147 1250 361821897 361821913
    0xa15020a0e0a120b01061404120807020301022101080616081e091006090221040303090812060f1525050a03230403020d0204020f0717030a150e061002 66
    0x1e202840d0729041802e08561203d4242e040120040516024150505100c1407101c2100c240c540984902c1c0149454102c1855100c0d041101080c140c80906030700600039522000000402c0c819955100e5078650414032403400020050300c0440c6003801000058035034102609240701c2505e008102821210105040703d12615440d83c207409a58040c8281c400500b0001032a13a400b04140c50305508100025841048100c120118a551801203c0301048070a10a0342d600e0406500030409210060250b800025001da004607090590074403600046401901500c8810144102e407800300d0441d000100c1c0400080d1070001031301001d281900410140500440e680b03070740b92824003d16aa04401103641420841c080c1c0880808000326842c05036005070406145070002004180ba40001030f000d2a40080c1c00418604088110340d47c040d04040c083e030411104c0402ca240c9507008860b004411458042d603400840606500e45081355101d4003425596180d4000b00b141300451400d115040d03100d1100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 361824397 1250 361823147 361823149
    0x90402090f0d0b0a1a0d030c080d05100e0901140a0e1e070302041b0909151512230a02030c07020a0f0513020c0607140c07120c080a15020a0e 62
    0x42d108440380d00c10300514001e81007218140c0d00f40c42c14540300c40400714081018560b1a2650461444110f030903151070300c100d91560a288186119014819000b07505040c1007090250090540e032044510040c1280030558583c0c8945003244d0310203030b0b170b0040b44078510040b41e10410342c1e4001165515242082d510110440240a01030810340421143c2a4002810410651502c3d216107003200d0b240a0759200400d05862005001044034002c031081e80355900c110f0440c032080100c01e1800380c0b03400b0700040c0d2040f041504c0a064500e41942c2d2003a00d9041240f461500c40901c0c009a54140010715915210348540ba17079100650030040264140140c184815000350342e507000b4400041003940811140303141400280704401030b8400c03201e40017500400c8042502c441c0041c0041e8484181d190101c0d840454640810a86c4241c00049480744507444010a0586000c0751035240140710381d226240d02a0b60b50a071700c0c0c5501040350050107078004245c500790aa20300d50001c22035a041da10b400c998400f0000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 361825647 1250 361824397 361824409
    0x2031513020f120103060b01020304050d0312090b0a1d0c061602040b060319050c070f0b06030708060114120d020a0f170a03050108100b091503010e070b0306190803090402090f 77
    0x80c242d2024090f1000040040c0130051090342020780081c40076500e890700344800704040b02c000100050810804140841c0320303000f2980081192940301c540040701d0b0a20005082c068541c40780242c04016003241000380c021030005e00382400d080c01400356400c2c03c01e48030403001400003008041c0c0c0c2168444c002c100d10f40d9a40d00055100d105042451442c20b8403010f0444202c503001807812a01c2c0d40100702c070001280d9401c0940e080151f10030b002100781da98100109041200c80c0d845060a4401c0000100d661141c50240011b282400e8800403000000a00b60950f50907065408c200540c104125200c0030031900b8503414070700c5000e0005050410080c8070304441e40c3d40028030000c0002c0c2d1ba0350050207102007c1c49010110102d58005204601c06030001036010310015200d8900460540f0218031903450a4001307a89815003c4c0594115968608003040ca690040380c580d0302c1002c1d0481005501d40c41d06c11801c054454040c011804c1142d8101400700130b520021103280d0060242e0324a00541d9191 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 361826897 1250 361825647 361825657
    0x10e0111120106020106140609120d0504090c0c0b04061d070806060120070e0a110301090b01081f0509070309060e011a1e0d03030204030f0309081002031513020f 71
    0x203501465503012500c10040e0001d00c1a0003803021a410103108010070380240c00311140f07944040303410560361040320f00040c07480c85526032400d04d0b030700980c00514181500715010340101c07410035005000804038044210345c1080741310001011086c0b5000402d01186076948240b4503040c100ca502c0010000140c10189003c1d100c0d409a00d541d44007a04224040d40e1110302c030000740d9407031b0f21743c5d4000c4e241c5950300945956140c01040c11550600b400161a0345443d00200300e0141c918804075525615511044050301c0c5143c0054049000e00700481e51403580d09203c24060921041f2a035402400c0c88200082114080c140108160710b8409000c00f0620602c990200400048000030b181c0c0b03040f41c1c03208201d004ca020054032403d1401d04d8088140c9c3c00c0c00030005618422035400300145910701c0e003900240100d130030152a941083e010034041540000859003a0b81d46441114035445890081d03c0a82c401110705440364108072444007054100340c4003110003044440000760922100804c807480a80207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 361828147 1250 361826897 361826921
    0x601090905070b03010b0a180b0d090c120203060112021f08060a05100e01030207210207030311030322150e011a0a030b18010603021c02030c011e050c010e01 69
    0x184100d98820440c0401c5198010100b02c0002411589021081040c40c05515188818056651094062050202114000361488028158483e0520100c140080409400499458400c0a808103040a4103110010309075030041c004c007601d81c03d01261206603551114100e07042680b980c4039403160720035502c0854100c96140d40700300b05032800408020000702c0550020f03010300d4815407424007041d8400314400704141d01f0708002d641c42503c1e103400b510b11810000c03180d5415424400070072541d5404950042228080e541d801c20813094894001d45920007078403583c4c1000909000414180c29280200820740d006145000019a10201c4d001c19295210b429100c00c1c0d42d01d90b00a940980d0b240d0080700d8551040c0c0d90b2080c00d6007195100320141801034110b8010988646400c40d00c00401d4020501a41c0e01420b51000400040170583c1d01041c013031001c034441d006150244005511903590112003000c00d00508150b000301d4441500c80c0d9005e1000c0c04a15501e801c80c8050380c900034010f40c446400d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 361829397 1250 361828147 361828151
    0x6080118051603050d031a04020705030304170903060a0c020a12090609061103250f0501020d050c16020f0a030f12020d090b041404021c06050a0501030b090406150503060109 76
    0x403191500300d0402468901402c6004046401800443c400142c1800c101045d03040c0015400c424074000706130900c004034020351007400002d0780020080b0110156000314030809211101520201c4400994028130b01186e401d5407282d0000345407002141c100c07150040c03d03801641d03800ac0107a21190309500c070000b100d1010940000042203210751240b08100140281c0c50445e011030318002a40b41c0368811185120a80207141d0780100407100b0385161030340a15404402403480d400c091900601035081040c03240c0d0480e1603d00010b01ca1107001c4219109100540d28596021000741d003044a8402825a0f0540181c5a00d40110005080343d0040130b81c6409050344003000040144003d107007403c4000313a0b10422040e8101002a0b02e00c0c034083c1c2c3e06490181c00c004400900c070001080c024000e1240007841d001d482a401e0740c0341d501d598003800c10394a06803050181c142c5c65000641c01d4900e07003414581c1241c00c490005003c40c078554000040c2c0e484e18441c590079155030704002890700ea801e0f000110156 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 361830647 1250 361829397 361829441
    0x190c1206090302100c0206011a1b1f1b03090305130e061009030c060c1a0c0d0e01050702120306041404030f0905092203090504060b041a0f1b01060801 66
    0x5404125403040724030141c5080c00131700130040009403100e00600c81c4021102d0040507030f9007000c00310030540c0d001000c42d6110203e15030182491940c0c0361140300e80000d0040c3c40519107460b51525010705506604401107a0400c548840004c8005042d03c0d41c0a07020030034244200e41e140390712802c0c80d00040a0408210b40c0b00d0500390100104817154001000900007401d4041000400c401c904c4811140e060818204a920b107041c004c43c58004054003607a12442c3c0720030806001c001c0d0019001440c40704030100050b41042c42c0a500f00c4034140c51780303405648510540400c80b26840010340e4041d00140000c1076030f01c1561018094100141c0e03085000c180840020b0b6003455020010030005c010841e034610007820140640443c082442d80c8501c6c42c113440c2c0b043c000a00d8016001c00004000c054010002c1d01d0395111080340942103401755480810703c00d020b013110340030003905030342e083e0158084880c5455001c25410070700c3d507143e103441c2032555201d03800000c40c00000c9c4a1112000c4d5840030a1343e100c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 361831897 1250 361830647 361830653
    0x80d090f0506030f0402060d14010e04030e04090c05190806090703170301180e0109020a030b1f182a05030a0c031a0402090f0910060e090702190c120609 67
    0x15180d1900080d0068000b4420840401d6026801e10b4100d90181d440741e5503500c0c50510000030380f127010101e00100c61900000940000d0401c241c3d44a40d00965034581d085140c4800c001c151440b8040c0904100540b200501c41441c02c0c03404203030f006219040040c0340b1640ca1004c281001d0045405039103c1d0000e480c10014803020f8109030000e18800400302e861981084075102001c403110001ca0109a69024111205002544084c1c0041c1d00180a1500310380e1b00e1400500c2c3c0c01d000c03120f109040ca2071080035000d400703201c2c4504064032550070420106038045290b85009100500152582c0e8021340641c41c0c00f0100010705105849059a42a075240380c054801e2041e40d484210400030145480004500c4021100c8400110102200d0240c1d403801c0080004150840f05241c603a4000c28030300a104c14203d01041c0714046a41c80e40710100402d40b01c1c0200442144107d400c50301507000034011203080c0034800c1c01e801c81c1600c941007011000c1d842c1c065084554443e200e01f221704a946401080034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 361833147 1250 361831897 361831919
    0x60b0f040f050136050c1b0c190e0f06031f061d010621020c070611060f04050319031805010b01020f0105060a031103010603050d09091112010311010207080d09 70
    0x94030b1540392140c1080441549558042c00c120100588555a5070041b421040401e0201c0d10309001c42c80d41c0c66040141d11803c030341c40c1c03842c02ca180ca120740310002c00382400c0381030132030504115501280540b41c2039071007108501241c0801010154107000f54850300001f030104400014450034050303000540681003446a500401d200d400c0c50201804080040040d40d6004101070031a1740480c0d038800501c0d055400d51030207801103806581c068043c5000215103264001c0603a40c5001e903440895a6503220b00200c0000c1050640c0c1c060459002042491112540e0301c034000c09005240c82c00161040d0380e1580e454400545d010200d034183d4441c5d084c0c0442d50703410000c103180050141c00030411420018002a02c402d42480020703d0b601003000c1c094580d036000e45c8004001d540004c240d8500340105d030070041250b035080c01b030000c1e16407a2071160404019080c00f9240342c00030002c40c0f201c260b420340d01d44280758076012160504500c986000440c00c0c040c107003c0384071902c02580b603c4000354103040e20996 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 361834397 1250 361833147 361833179
    0x50c16050c121e160b180a0801090c09020403080f0c28020102100e030306040f060f03030c0506100e0601052203031e0c050a030f020a0b040b060f04020c0a060b0f040f0501 75
    0xd1503101801941c4032040b60744504017222840e6481c1e550751300c1101c5c2d520f54210440f2001c0c95000041003400074292030190031005900344100e8402d81e10f07a80b00c0c1c030540104d003c1c901000e4401c810a1042e00c1144442100030503488a4000c01ca030f208000e103665556994425481c0356032440070000c0007074111750b0100145101e1002c101c005205205074414074540d00d000084c5024030172034490500c4c06940c411030b44510050440c0410700c0e11100e442e03040141c440380c4030721001c42c0c03070748a0440010500d00c04200100e0580b8404440c00c130a43c0c03580401100c09410181506410401d071201c2c821a00072a5031188000318440d40351000c0c442c40070f40401d400c0d40801e08030001031015194412000540108509103000c1d85030a0107600703c01c10100c103c0c6064681c0350014588407400c010701045c4001000c403140709240445142c041407840c0b2090109078018003c10440941c0314071242400601190400d610b00345c2c000c1c10666912740f1400000d4161010f40c0e440b0350500e070780c500042c040d031812014100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 361835647 1250 361834397 361834453
    0x11070f03110418030f03060e0a06051005030f060904060605030604110103051305030d2309030c0106050607030c12020c0414040b06091e0a060f06030e010b04050c16050c12 75
    0x341a01400d081240314550200804204000c0850f000b05d60003544454060119075019641c030380b42c10507a100c014412400b649105007a07035600342c46000c0c49002124499501054080c103992110300900104400140044441e280c480f0408101520100145880303980151081c1e40351072420400901280d078098030000484041d0124040801d400104480c030031055120300040c40041100c1d0f100340440c0c071800502404c2c4040040c041c4a0b88000b0140001070200d9000b0030a1a0303680f4100101480340a0740100440d1a8006280101d0040c0310f10f1604200240180c0e80400003010004044038a401a941d07405403898050000f400070311640e141e40701d01e00303883d030b030459003841110540038201060320328810141b002e00290440c2c0c0250811001481e41002407040103441e2400980070f00080103000300c440d840d0450074001c41c0b92901a0034040c0e10300101d81460041d15007945140245808000e407207074480d00c010040d003612042500b003d41c1c00880040e212403500314294031a9003030300321840 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 361836897 1250 361835647 361835651
    0x1090b0d0c18050d02060304021305090601080d180b0d0e030f04080c150f07030c0507091a04150b09010905060d060f06030c17090a050a05030301090b06072111070f031104 75
    0x20f00244d2111071a000015804a4030680c89541d248002019180c5441300303071901c01d00348418420f64020000e400740c161200e14003503e22031020068125820301c082e1132042030682e4414000c11012040200a0940580800d0301080226228041034610760040e4089512a000018104502c40b014001e0032280107044403e5034024981d102201030501440760380e25000d032800243c400405004184c0354407031030ba0120958000e00d554910100042c03084186590817020540359020051800f880343c0540c3d554a05510b894441c10500903440d9900801480c1e414028603400c041034035030324030028081030343e13524501060480c2408500c00030000217520000905d070404170b400d0b071101d030412903030070b940402c52904002903501d0714090780c60411030200240c018080c60254005200d0080003c50686410300c0d010320085081c441404124031440d0320103443c1070740e401240300035100001110040030400d840c119840d1061500c0150400d001c1e54080e040d88009a03d0410070402c1da442803141502081b501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 361838147 1250 361836897 361836899
    0x150e2a010207080606010e0a030b07031a0102061605030901140a02130605041d100b07050c030d0c0804030b0705040b180f1c061e0603050708060f091b01090b0d0c18 72
    0x20b141d900e13203000e048541404240241c0141945541003c0f00003581c014441c00f180e400c0030030002e402003100902e0030707841036500c5080340143e5000041d801d0042003040010500d02010010844a0f50000b80803d10079540f03803144d40301207004030701441c0d004121801c0c4c010b81d80c00703030304035420982d1143c2d030b208506000c401c2c0010014026000c401c0030540d1190381403001030f6600e0302c00703041515015405c40018403a01040740300900a0008000107199800d6044a4071700c04120b0090780c83e82000c0314010300b5408200020700000b201142100d80141050038101c0c103050315084a0031950b0400100c0003e12040024003a1076840c090313511105030003065a0120210480c1400170200e410742d00000b4060b00e44404400104000d03010030038000c190440001c01240742c80c3d18100f03403512041d1041034854802d910103e91409803e00e00c2e00d0040b05044001c10320026140503c0c00c8820640041a0503c141c0c04000900341d60394400900105c00e81c003100141c0c1025210010301040c003100c181040c1c0701c042d564 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 361839397 1250 361838147 361838159
    0xc1103010e070f0f0b2b0203130b010f080d05070219061106060d030903020405190f02040608090c010c170c033402010f03200a0e1507020904150e2a010207 68
    0x101c4040c06070012000346c54164400f04403500100c22510705034400e20002c100142001c14400070500c4500c281c0c2510542c3e43e80b1210700b064020103010340c0890350030400c88110090b018a0040664620103047c2034045c1c250a950925482c180b0b1703102c4000718002074a07030103500030103001d4640d0111701201c0040380040310f030314010308211040c040203000700c0c0c0d0f0700c010480400445007940520101c2e03000a01c107805a0114050103904a84200808651104040b034154280030071310b6918480d040e075408e0340b40601c6171220070aa00c001e90180c0b0341e00004000c400c1000c20103000400200d10a240d0340d0440c52030385840841827940b001200c041c0620b8242a00b40181e91288002c200c01040303181c0800e03120520f0494081d2041c7e1103800117000040060705c1c251050704a00180202c010442d45e8080c106c1c07410003200040e20074203500039442269200010002031000300c1c0d0540704a1814400121007484161840c58106280307110f841d800b618200b80d03207841440c121400104582803002e0300302645424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 361840647 1250 361839397 361839419
    0x90605090c0112063c0803130902090906040216050a0b060a241d06041e1703121803180a080a03020c060c0f120403030801050d080a0c1103010e070f0f 66
    0x4104c0c100400900440740c4070110680000c40e200b0715070b0a411014860b5240b40b001c7c0d40781c1c003da80c4405010680710b80007907420220310a41c0c4403124082e048000396075840e01084002d501810300a558030400010140104000b0071510713442d0317032041d04248110f003018803c001c555031050b800360805144a1140407603054400007009105100381c01d01001c6401d80c80760000a0507140412940c1100b004035001541000d44a95030340908410714942d20955115500704000d80d91005013404158410801039603c2c49a50903600c0e440020407082c480e00701a01002c8600b0340d07005503000c0000c540700c00560f51041c580701310858000d2208030000c007541c86966038003948922a03200d5451250a0105803450340c3c100601c00d25220b12482d10585440c41121107401c03207160071501040d0000341c030320310000c90b403130420040200e48a60001586030512030003050445105c51032003c21248034020700c0d512146504d00340190101c42c8400c2d00a003200a0034038110312022180c507070101c0102c0110090400207101a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 361841897 1250 361840647 361840679
    0x106091e062c12060f0f040c12020112061206050a020307020d03150302040501080f0606010309020a18060905130b060a050a05011107150e03011505010819090605090c011206 76
    0x140203016540403240c8100c000740010040c0c5660002c900801001d42c0c0c03000491300601c20180240428000e442c4c000c2c0d52803001c24102d40080484d00c2804040c0300d00800a148003090503c1490720480105d01d07550a00305840d26607000500b1084414455800c100c01801030903480380c0101d40c00c43c21031a1850000b0754071045940b2001c2410b0b980e01441c400c02500380c4280c8091074015006101550f50f07a052960388004403901c005183c0100004580c2c1507100c0d01883c400c0d9600140035690072424000440c4007c3e040407000404256200400102401517014181c803078118030400d44400000da081c100b0040a0051465200c1d6030031030400e00a580d58a0003a00039030710280790000c40100e107030070000e25158240e044500b00c409446030380c201455120451890050081d40240002c038951005642e80213807a006550200d605080002c590102e00c1d000c0038031046000c1c00c00300d0843c14984a11088480a0358040c1d010341140381411074950b003110142105110180041001e40c0c60041c4100c054828 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 361843147 1250 361841897 361841927
    0x152a030c0e010e0d0f1707020108070c0c0e0c36010305011a210405011e0c020c0108070302090a0308090a08060106091e050909061602030408060402040908120106091e06 74
    0x511604d482401111040b801820341e00040e001e9001080c4c43d41c03500103400000080b80001c40902c00145024401c06140c000158440c00d070320803013420401d6040034000000e2244104180911107204507441d1280e021491107903052100b10141c2d13541101002c9171850200c001e0606041900402141001c541012150a11200c200380c50740700c4180941d50407140840080b030741c0741c0300009000c203002c8107500120008201500c0344c0d0712000410314003410b0702c4c06104288050303048000440909d501581080394040314070310f401480c140300c0c0740c00582801656042610414070100b0145001d04220081002801c005c50041913290700d00079000b0607041c1203014982403a03409001c9030342040710300f41003200a40300091850a181c40c14107646903881d0021104145c0040041d0000154680003008031810782c4c0c2ca0401800103966550240310240601c9903007261000703010042d0108441d4903160050180441d9515280b0003807825918001e0741d40d480a40f80c4048800c11010007010307030404001024030b62 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 361844397 1250 361843147 361843159
    0x302031903020f0d0e010606030506090f070210091a1003022404091103041713050105070804090e060103050708120a1b0804090c1b0b04152a030c0e010e 67
    0x40c44aa00300c1c0603004603000d0780c480320404149210b0410072030300000802c0c1300c1e0000801400e130b40c64000302c0640d20191405074124002d40c001ca000301003017190940d84040d85d40100d80026091586d0f0104807010602c0079600300c2c107103080020060300e8030f01c103207504070401a00c01c402032415900020740543e1a03051403040010300200804580005100f5075006224886041000f0902c6402c2c881c8182e0080342c1c00c9030402d0840e400c070384280000c00240d4850000d13608108120900306001543c8079407000d0826101c0c44810320000880003c0c6014607500c44200c180902615459840c0480c1f40039100e0708880f0103500800b42c1d035641403003002d040d41c078800c1c00342c540106404055854281c00440601000e4251a070008000c0781c0c02a09820800c8100e0159403584070707007580c1d480484001c01e0b56500040c110140b000200d0f0210b21000c406508000698a00103106c010750814183c00e482c172402017043c04c14001c00034070140d0b40c251142c60021a03041c1441e00e000402070340001d00c091008010280302d18 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 361845647 1250 361844397 361844437
    0x6020c120607080711011103191e0b01050c011a01020d02030703080606030414012c12030a0504020a27061e0302060a030f110301030506100602030304030804030333060c030203 77
    0x45d10035442c150401450303030001c100c122288603001d0800c2e403040755441c1c0f4412407078008501c8072041d881801c0040c40d000c1000d2219504c00102e94002e07200540255040000511182c0c0d42c50f1028821861000031501c4514034120300308001908000e4151440b82c1503410600c4140b0209400600c900d40c814011100701c0e070317682d84500d4000d0303040c0c03100d0071400035640ca401000e90089a8444a00e00c0156a03866458511f074110340405903030714044152607000354028000305403000365581145800502c010501400305855000c4100d403030402c104071414044041480700e844640b50710580b0041d00301d24807118040d0401940d84600103046100003401554009126541948070f40d004100702682200e06011001048100400640080c042594140141c00100c4c6080d0603d144000403680e0039005503085a485440c181c540c5c0000500c16020715440362240c00c00907103242068045410214503030385a1400b0008035001d00e403016041441072008203038065002c0381d0000107a50b4600c1041e84400140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 361846897 1250 361845647 361845661
    0x80f1501050f13060809070b040306090809060a0c11010e0d0f020112020f1902070528050904050d0905041802060f09040c0c120207033807030606020c12060708 70
    0x2500c2081c8841000e0003000c01e01061041c1c0d28841c082c00c80d04130340d0710181a0788070091400d071a0f481d06c0c80362802c8017800704401c000180340c07a003188080310f00540e4401d0600ba146000309907546e005d0280d4400081024882104100003507840c44001102840c2000010020301e0114510b00b00845010701255080708404046a214440d046500003400e00255190014038204445c26004042034102d501041140904468030000b134000494100409050b200d5202e05810390f0b06080d40c40100d00f075004201c00209031034417440c507901d0140f0301c40d900422442c0144000148060659040705208500705000c400004040d040d101300866011100990340764800045e09403648030301c41030550418200907442040a802400e1605018050215025603603c2460201d0725011035000082040c489041c06850b0000c480c40e00d00315411007443c40000c00704c01044902080001110414000394861909008940d81400182003241c03058442e02406c8450700c15541c5c41e054001c0c145e00420016500103104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 361848147 1250 361846897 361846907
    0x80a032604020f061c021b1504030f0f090e070f030f0e0304060e01030f110a0207140a09021617030108190b060409171603030b0f100e010210050109020316080f1501 72
    0x1001220001c55179400285a00285252100c205451f94041c00c48445011410401060300c12580366440451038200000c041d540344c106180c800d0f0400a00500c045100b8030066000350207090991102802e10411101c021305590100e101d0b0050340d0300b0506810151007000055609803041c0c3c0c1000b040c0390300f00c1c44c0101c00030f0240300d0f1100042400d1450052042e60355000504401e0116420344110607100c0e0001580340034165000c1d1b4000c50b40741000c200000d80759010380212004030043d14100301c441d80710400c401c0710072954402c0e03000c0e0020040114510400c00c82da400004440100d05c0d05442e5100c00c40b1070007004041c1402280c0b01c00c01c90b01000300c600a12520a140e03112026210980c40d40410740b260302d048000c50101e40b40404100840c80c151f50f2000365150010505400340d03e4017035045405803004260a81903100d210b00e01541818503004441c00303842003050040c0c0b00d00e0315036140d000c08080d00240d2404d00022106026072410500310050f40a02d4240c0390030006c120000040742c1d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 361849397 1250 361848147 361848187
    0x20c0d030c052206140c0601050f012601062303040f052406010f031413140a0317100308070803370507020c030a110a080a032604020f06 60
    0x181d0700c4900c83d440403038240c015003000b09840003581c43d0440c0002c8681c185441c1e10444600324002c1c0e000700f004101618107244501503021046c07411202d00d1200607542e80e906205009002941e409501c0103014a65001c0c9080b000e002406c61403140300b5030307644402d4020f44001381000d88145840512241404001c10804404044101c41068030150584007040342d00015078100d80052246104c1c0c0c12032a11030f014101c0348940f003441c00d1405890740344642004074034030320b41107400a4045182c0034003910240007442444c0c0c06a1039002a41406040710a5a690010041c5100420070b20080c0003217003510041c1ea004581c003444460340c0b0f03111141c03040e04101611822458030014101005401d280c0050308448183d820701051142da15004000d98580040e82809074060384140d1401d00403442844120901980140100020070307120400642040d030041d0b800e8010403400c4224908000d0b245c06c440f180c522100c05000094101940006c00111102b60000d1041801140c070110040c65804000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 361850647 1250 361849397 361849417
    0x160b1b070803031017060601050414121c030f020a020c0d0302010612030909050601030531150606021605060a0c2f0a05010315120521031504020c0d030c05 68
    0x3601c1e131800c10160000e0104074011894900d41044400b4030120000550500801c3c058460a00b403074200100c4619942c10040700302e911101460b0742c51640d0700240f0440a40c0c140b10116071035102c07507020024094407a448122200d0390700c100580d50095034085080c0150b10f0f01140c90200c89500d03400c00300d01426050300980700c00b920500010040541043e9840d0803180f80400520440d61004019421110300710340c03080c80692201d2030380408281c25403014002400d00c0030700c00c0117002c080d160080d60a4226a40d11a03440c0e0380c910500c035454040010314a420b80c40100c0705401c90416000c514280a0703008054180480400504100b0110002828030b692010300340841751440320010740345148500340c0701d6010314820300e004035465200c0c0c0901d100b84014134125524a500c0e107140c0d070400900301002524503001d4080c0503a03540004442e0321203c0e103000760185481b400d1891400c81030085900100b03204500c1005200413142000c1a009884401c500b00042c903090315507401d41d4a481001107107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 361851897 1250 361850647 361850653
    0x10204060906170702060c0f0d060305030c010612120c0c15171f03080304020f0904080c010c050408100c09050a080a050c0906060d05041703090c0102160b1b0708 71
    0x414420350003401c8100b01e07400c540e00e807003405004402e90110550184c403200010707080030f0009104110180c0080081803611020b851411036202100c0702125810740048032107400000781e5283d001402d00491010b40707120300010b07944000a5540f40c003210300320112042404011a840004e000c0c41503480001804504103003100c01d10054001041e6445c0c1440c8070040c10103500100300c192215003500801d0040c2c000401c804182540c0b07560885410041c009c9a0100341036003690100d03210700c4800c2d070195108042c43c1341c070351849107251800e50300d94a40010070400d003800100410200010a01c2c49290500700000740c0343c201c8081141e644505800c0280c01480200000034903074400141c1c0350909005109640c0e80002101c01c10040160948509500a1060100c450031154a07800550058070604005040380d18200941926030411605014590024a2207640300e50f0103100d10850020442c004941850802800c1200790013100e16140e00c4001212448104035001c00490018000c21022 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 361853147 1250 361851897 361851899
    0x30e030706050c0a110712020609030705030d0903060c081302011b02031917030103171309060f1508041511041d07021006030c180f06060509030c0117010e1008010204 73
    0x4903d00c43e4402c0b030861000444401500220f25070110320302c41035500000c0000300d040c0b030382e40811125420500805a07d03000d00310700001d143d035040003c50754621194039940c040500d1400c2c0300c0210384850107850709010404081008140c07900f042214810750908004100d13030010898100c1d0f1030040c0400a4042c42441014202083c00c11201c034903862141c951000c041c08240104900e81c0400c0c440240754209044c0310080c041095005007014081c441510043d269944a901094811036030101c210030849080a0003d500401c04145105620f42801c00c1d440c1455540c0c0e03004906400e0025084540d5500308a490501d550300b16001071001da911650580c0b04958000a013100550b01c4070094441c5500d01980d0200311701882e02100d03089100c49613000d141500c140030b03450100000c00061a910049030001e070300180f080b0406845030b551803688541400050503d4103d03c081047e0600c00c20798011000d000c3c00500080c1075481c1c250103c080c5807901c01e1404a0030f81c403904120155400072030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 361854397 1250 361853147 361853161
    0x10804050a02300c060d0207080f2a0c0a05060a14030901020a030e15070f0903020d0605010312050c06150301141302090106050a02030a20070905190b060307030e03070605 75
    0xa229007541040c99a4a42d0a400c8083d081d54441d410321125812807001d0104a10982840d4040d0546c1405004800d01d03010310f10030182019070100d0070f8080c498240d807001044c0540315558541c2c050f41c0140046c018041c450001a03d903141c42d114007880303600000780c1107015a00c2400e203c030a281c0c10ba03e5040d10b0b420030380441c50203504159003d0002030700d00400c0100c010000100c20b51102000c0d441c55070a0f0300c80d103c0446e5044a0302c00e4103014403900050010050301e85502c050145405040001401c1d4114546146514a40c034450000c203c401d04c035414480501042090700420341d8004c00c10b0700411307000400e0242c0300700707015400c0c2d0b10a4801041303464041d60a07100c0410744221010103e682c1c071800c040e121030060031b06020042c0c0c01441214221800307491010788031013841c030b00350030b4038000b05c4040340c5440740c59000501020380b04c0003885450309074500e5108149161100500086145001040381c50200600c0e0340105a2650203a1404100500803600340b10380180080c030007450094 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 361855647 1250 361854397 361854439
    0x3220203281104110304060209041508030c100b01050a0e0a0306050c0d0612080412030c050601181119080403090305060c0318071a07150203070c05070e04020609010804050a02 77
    0xa6800d45a0340c00c00e90700b850a524091049080d41100c00301c10908646998a42e04000d4000990030b40d00590f98100d4004c00300045ca0071310006004a40c000c60b82d942c034401c001802c0080706000c400c100f44c102560f0400036a00301d001d582c46044680381c504901c288400004a65403403940c0045c0c07078030749080c09000602802c80c004060001c0b11007018006180c0d0f80310031040302407010380b028081e00010310040c464070340302802d081e209501078501804100000d844480c1400420b034400301c8541d0511100014030b114a00440103100d0803130000720700345400702c034013410f0f0323040b9040c1128100003442000600301401340005030040c0d6001000c841c5c00b80b51000da12601b941c030179910243e0040c0d180d20b18a10b150f400081c2c060995581801d541d908025904521546d40c205050440309a08100903ca005078060300c0918400e0303285650f0f4250340705007810800d0600031789800000c0301007000c00403c0007684070780003141c480280030320b019001591181416810b14050383c400030f46c003031808051909814209 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 361856897 1250 361855647 361855723
    0x120c0b07030e24030f18060f01060e0f130209060d020a020303010501031805150601020a02030a060c11061e04061e090c050303070b010e10031b031703220203 69
    0x10703900200f608074008204022480310b1200c0340e5000e042040000c07000e42522510503080300a548020f2100c0e648242c00324280724013160b201c2100e605030320041011683c04003201c0e082c81d03000c4e01c0306004080c1103408202c415010100300310800d0707000200748900313071031f030000300c0c0c0030303044542c00031916961407110094496000f807160500203824200b0100100f110005c5100c02558840b0042050004a400d0001030404c01020181507001d44121600513850074481d201407148031b03c2d4001038a25014101914505d00c0c140f500e12594003000800c165541035042150402404141020302540c407454034074003904d20070b0302007541c0c1c42504a5001c400382444d081902190b01c00d2045070340440e00d0b4000d1503900e000718080500f80281450040200c00041c101d01600074207a1040000d0840e20394a80e41c40220780805121f0f59011502410000d20800c98401c41131107160030101881d41c00c1800701e080d12103075011400040702103000040411541c0401c030500c2c45103403480110f5860310b410085c01500d6504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 361858147 1250 361856897 361856899
    0xa0503061933080618100b1303020406140102032203060614040b031c0c02060d0c0818010501060e0f01031407020a020301180203060c220308070318050901120c0b07030e 74
    0x590745040700d0843c05000030600c50440a004142e00b40c20b019100b10b01d100002d004c80700c040718000c80c04221010400d00a000c402c1442d000c3c40841442e503c10320088400f260f0001140e1401d44c4001e019980e8040100d5002c803458449141402c50b402204202d0138005a10007021103282c020b0001d0f9140c02400084d10711002140c1c1005180c000b20306254071095010529140d540d46101c0c2c40700701c2c0d0f000303070815418a80080c10003401e0180e0401d007042125803454071000810142400c014045034400002010444400021700040d45403103009405441c42001d02c92207003080110210059120707500141310401d04001100040c100914040e4980d08040420703030081d4203042c44688902c4614001d015a80e0b805001482c5035903c030300101d1540d400c41129011840140c001015821501d00f07800c102440c062054250354490074540030b8480c0050a8224040c0c5007040b0301000295a900b01090450310b6003042448400e14510300904910125081030601003004030300d41c024590310410280080320 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 361859397 1250 361858147 361858229
    0x10c110d02070b041710020d0b0a1d0f060112050a0b0a09050411040e0f0102030106362105060117010606020f0a030c060b04051f0b0a05030619 63
    0x16244400c0382c442c4118002e0101c00c9100300401c000b10503001d01d002c81e28904050680c1c444044210f60541a81c0c03210880b01c0c1c901e511000c080c401840c0a03000c60000b88011074540c0309152a030341201007003400041c83c180d88a201680003403113907405050486401d00402034100054a4000e9483e001000001c01450213408180400f1810208502c10300c0e0059401040b1504a0402d0008000182c511030b01f180c0d0540c05195007480d80e84e0b000b4006103028145030b0b203821014040c1c1e05401c0b1070071100e440007408015001d106003140036401c2d00c02c407416903503298024035a50b4a20b80d01082d0540303210b0b13001403851113a94000600c0c4219071001502c2c000700e0000912125698050407a41c40300408413510103504410b000d0340002c0c1c0071b0700800b81d03a41c1c42030000ac40c40e0b80301080028101c0303008440d0724030380600c3d601051800c160224141000b0b8440c1a00e1942404001c18000f086400000c0c80c0302e0040c0c01d00740a0f840702c14410017481004001400304680641030309401d1600c640440209906405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 361860647 1250 361859397 361859413
    0x30803040c080d03110409050702161409060d02090a0b0609060d020c010c03020921160608070215071b08090a080a0c09050132120c0906150304020603040c08010c11 72
    0x24400e0080d98074118081703041070b042c14200030203e8010319026001105522508a116100d5030059000c40002e10900d01d08004c4802c9200500120101c018030b42340c030488800500ca00103a556280150700182c64445c0020140b0340280400c40e140301c3c4003202c50b80440f01181e58507481c0c010f50000e0100300300341b40003840000745039036041d001d0f40550f1034a15402154988032000000d0318080805081c5040b00446820240303030080c5291003980c68110700b00284034002000500c0b83c04021540e00c3c500c2e040104110340c40e1491008009588003501d2190707454020304003509006200080ea4100800240700d044603541e125002603030b03a400d040c0100c07101c107440c40c0c0000310340c0180d02c1082c4c101d4941071151000702d0180b41400c10b620031180c3c40d4080d410343d5012000c50945039400e01e52801950345005003060003005042000040c4002d10303091007440404590740c005540300e82030301c1d0015416142c89450f80c54600d40752146900d290880001c0c1c0d0718015001403801c0d4009007003841104030b0310545a00d6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 361861897 1250 361860647 361860673
    0x311506030c1403070f0b0f030a0f050703090516030c0501110307060515180601020d050912150604140903160201021c050d06053c0616030f020f07030303020a0306030803040c08 77
    0x4c5c6910310031403201c070b0414050350824a649500640d8440b1071300c5400034280030002e001c40110b032810340d0924002a5104003460410104000040741910460003114a003440c2d0755400c04070400c9409058100038407000c8001d080300040050303c0355241d02120070f00440c81c003001c03804034440c52200d496100740d94030800c403000b5425540d01140554010b074040c155080210b0000c0d240d42c1e101d00c200c25008191071714019907500042c444040c40440311400d1980300d091010401c029500d5461000b11a401441d0038400100000022034210140c090b0381054681300d5400140d0401e44038006041c04428401c01c9014003c1e484401060f803503000440030405147c0391014031030700380c0d002030150100700300c0051a4ec00b55148550849040c0d80050815a5201180700202d4191782104103211b1f000b0010080410806401003080540201c0b544014003000d01441600750751a4560312001d41410b50003e41c600c0420700c0394000d000916008580c4580e60b05241ca06000c8800480c8100a41801110314103144 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 361863147 1250 361861897 361861919
    0x1d0a1509090b0a1503050705090402120a050d030e161202150c2803020c010320070f050d0804050a0b0a020f181503062d09070503311506030c140307 65
    0x661b03400000803c03000341807005000c000000504266844098038984509108040000410851161010b001004400c02000c3c06803125954076540380e412a0f44a001040700c9145090122904104452044121030010403503d511406c00358440000c00141261031180010320108408001204003000800006905035034912100c00100160030034141c0001541c402c4e0095071f00902a0030340001d0b5401e07000a03668940d0700a01c000c48614443d000b6102c144207042c80444590482810000d0b844e14141e0354082d1980c0c040c1c10010010b03000d21000c580e880780c5642c107480c004903905002580e210300401e40c0000d82e5000308405031003072011403003402c0d0480b528000e1b640601009080690000500c800011000b590855100d0305890f400d900307203030503699001242d8041c416980340c0c01e690f130400e14100b14901c4503100030300c400400c61514201041204690000c00c89802c40d002d01d406091181180018001590002d04181d0740c15101089148440303401001040b0210111000c4c180d8038000b040e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 361864397 1250 361863147 361863149
    0x70801080c010215010b0d1515090e0121030903201e031915061e081f020c0f0d0527130207081c0609061d0a1509090b0a15 54
    0x441c01c0500c001041009106c0303001c0d16050100c0d21010528a0034001c01e003034000380d0381e44103841102407001c03140401500f003494000608030703a0051004640c1481c8689464a416031724854803030b10382e151004203043c41900000c01a561000d14049071482c010041c00b030402c2d0440f444c501c221880000407603681c40760806000001e00280c060907916003804412000d10002010548501c01c200405010b41552441000082c1610400c0a640c4200013a82120700d20381d5a0019180c1d58402c400d00d48000b80d0320b01985500502c1c0c0d11000d6603901030303149000d083c981e00806681c09441400a010215504180640580810385900820740345111950103188014081040e4025010340300000c480d40710790300280b509502461009103014107174109011024100c031906c1c5082c03940c401c0140302c0780015000d410010b000b40c10154001d6504d880c4003c030304c0ca20141001c01036039507410342201c11031081c020100040120401c01c000012141c14580c1411404032111030102d894089400203003856064800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 361865647 1250 361864397 361864423
    0xe010f0305100b2a1b010f0207090b0607060e0d1209080f1e030106050705060f010302011707020709020d15081c120f021603031d030d0f020c010203070801080c0102 72
    0x10b001140382c0300c00b109450f4000030940c0c0807040740c80c04090850300600e8500203840521402490480516001a0305008180a11904020450b200045801d600240c040140c4070282000100d01034039400041c01d520600c4001082c15041114900c150b04000c244000d50392440d1311600b0030740c2510141c07002203d010301c0009105004c1800182d06550340e04002d0482c0c0c0c81d483d50303045600021020424801c0e0401d0384000d00040000400800f000401c1c000d103a000300300c008101c0d24650441d40068201410090348000c140e9281340010764207842000100010000a03404564409070030140c500500b0099000300d105005203c000601080c2c0081d411240020900207020740e0f090942c0101c0305010031922840446894107406144915988000c0c60755011000c0d05541e128aa840d010f0151074582d0322041040d580c9265412800358048100c40c04050b0b0100700081d034140b4992100024002d0801c11446c035131021080141d04c54208540b1810b9440e03440c02c0780e110030300c402e0049a6170f0300c56200b0b02c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 361866897 1250 361865647 361865671
    0x30b09011a0d061a2101140d02031f020405120f0a02011b0b011512110d020f070f060603140f0c010f020a050105092a09040f0f0f030e010f0305 63
    0x1c4490155903018010009080d58041001c0390784481d1404c5a0b0145030305a80c80100000d84180550394040f414050580c0303901c84100198501000390301c21080609050b401141e84034840800c41d60305004052000442da20590042d0780c00348240d0740250018001c1c0e5000c0c4420140c40c0004450001d83d002e4180c031020004e01c50180c0c90350044400c040c81c603114101d8150103402e405c00188004191030701900c09544180b1902c1c8017640d0090040202e6081c1c8480646403000c80e10306804c0c044211503074010700000c050faa4030304e00c011301580c0e40b18412028040388690308c850010404c0c02d0304202d080b00c0c0545013004a103080e07030300303c03640f14000d000400c00e540d0721005a00606500450340802071942c180159401403881d500e4860130b40310704440d2030701d058018a401c01d000a080044038101c100c000c2d140704142400e00404100e503ea0041c1c000b52043d01310303d115204200101c1e100c40c1c4141e91080001d0088441840c001c2c05000c0b840e03803400e0102e4050303050521500c0c403a01c01c0038031403e46a114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 361868147 1250 361866897 361866929
    0x509010909050f0303070804060c0e0a090c02071a07030201050c130909020a0513050601031d070b160c090204090c05070f0b0702031b1b01020d0909110904110901030b0901 75
    0x40c04004251010040321580034190003c03559601c03d10156102c5c48258403141154581481c020045460b511513142c1442080704202007240c40d050210015109005c80000e500b240d000c00aa103400c001e0b0740f144a6000c00301c80d1a6203800003907006400000e22a40080c05a07840301003810b5441d02451074050340c1c2c04841c0c20100080384807504007920035400034250f081080d44503404a108030201500d80541c80d510b81007485400d50341803181c0c10b4085c03c0762640d88101091415a9a12010a845041c5040c580420503c1c0c40240c004a803a50082d444210000e0a643d02c2681d0000307908075214124066203001104c00c0e1300d50040049420443d40aaa03988108049035641c000103070b00a0107040440c401402150b021626200d0081c03250030103180140649008c20342103040d60362003500040d045401c000380860314103402259407400d40704001000316010a00300c080d50f446000d0b00807010740c01410080c0e07200003800d514000700000c510030b0342c0a00c0701c0c44a031000d102541d0005e110700e0000307140d42c0d070b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 361869397 1250 361868147 361868159
    0x150106020a1101090f03032c030a080d060f18050609190213050a0902090a08010c021515030d0801150f1d1c0b06011e081305031e040807060207050901 66
    0x680d010b40c032101418611013551300d903501c500c5840501e0f0822004a070389090f501d41050f40300c9080c51404001c00c6045107401030340302e0120f034903146030a01c001d05504000c10a4a01c072407890304080d01406240740c40700d100e5682c9400107d0b071112146d046035065031400780481d405080044800b1300c07414614044690507102048004001d51200c600f08194024940c4046910790790380c0442d10003002e06a9003da1520061030070085d07542c0c400d034003205203a854803400d0712020b500411003000f4900c0c10165158643d5034a482c461003146500030142e170502a0a259980d126008011b00381039890144102c01ca0b02407590066130502c40210300400424440e005000b141c0f4014090b107014400e001c2c1c080796500c101c0d81c0d61070640102c2d41800b200c20001a4081004a581c4030b0412028840f00380c42c1c200799040d1004020781000320203441225402d113022800c40502004000302c4041c2c4600480b0b45080c007071140e1031fa0407550058000d84219004000001800c0d0748001901c006980c8020140c02c1d20780d10740701c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 361870503 1106 361869397 361869413
    0x141b010e040207110f01110a05030409051e01150207120f030807170105090606190305040c06170a0e12040f0315090506040210030b040608030705150106020a 69
    0xf00919011032010303034003011040005c2e600e41d080d4040c0140102c4175070710303040344200e103911404152404000c000002801140c10b800c0c800c028644030040485803205030507076001d91104280d0010702545041e429140041d07516801211012561407001129500c134000080d912888001d001e40181a0000000c0c0d030702c0920303840c041c980340a040581006030319042c0507a90107507440d500001c000b510752004950342c020f940c045503060f50720a404000c0152800b11822100c42140a40c0002c0d035074081c07006005040c03030000c0b82510a0703441c07265040007000824581a1140300c2d1400310b00c002400c03c801007002d060f9604600210509600b070030900c0710318401c0140b01c1c45240403005c8020800c0824182d4015a0440381e42080c5090041c003280609811040c051f4058a41100020040030020042680c24412401e9a5808011169190a683c004d20402001d6040254043c0000e0590 = true := by decide +kernel

theorem cover : BRFrame.Cov 361690647 361870503 := by
  have h0 := BRFrame.cov_init 361690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 361690647 ≤ n) (h2 : n < 361870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
