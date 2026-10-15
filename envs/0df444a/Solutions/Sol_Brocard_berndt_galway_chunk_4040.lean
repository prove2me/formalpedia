-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:55.257019+00:00
-- url     : https://prove2.me/submissions/066dd1c7-1393-4e1a-afbd-ff6bbf465163

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 726438848 ≤ n < 726618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 726440098 1250 726438848 726438851
    0x11a070f0c05040f020912151609270c0e030d0509030a0b07080423060a0c0210090303020a030b090405030f0306010203041203081b09090114040f020706022101060e04 73
    0x11820040032541d40e90080c0340041041c041071a0740c1601500952000c810b041c42403000b80200f140c810000306101504022002e9246056550240c0031000c1d0b02080c0c42810400440017804101140c0200305840540050078904640031241584c800c1182d03610303041902413020750501c40e9160b990006640c2404046031525544810002006c2071800b0400000149078415407010031510650041d1190f01c110301a091290a0300300111000404e0b40c3d02c2c220315250354000200140170014036400150758404030340304603070306c1035075610b128000c40780c1d6044200c00103900050040c0c1407c0e414051211b4450048464503810300386940e80c0c542c0ea100c0c01450308500712010000940d603038003d00030f588c0140403201c0b000c200341d200c0b441d000b45001d5040310649500c080d080d600c1a82c4075010026181218000382400d80e1a90801040b144018090030382940e219403159080800c1410764006410f0070391180102603219002d40c1c0c42d144c02d8280030312010049401310300040055a5200d58602c0103860305580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 726441348 1250 726440098 726440123
    0x2090f040b03031303060f0c0c111c1a0702071508040b040c03050601090e10051e0910020a0206160f050a0302070503070b0c031e01080a1403040f120b011a07 69
    0xb20f810342c02401908110b2500c400070010600005410550801100840c10003444002c50000da07203040c403c3c078014018081e04108811071741010420320107001f05407600000300400a03511b00d02c003404c62410707a402c500000c0040c0700250303404104a00181c403400841d4202d080920000501c05000104042d080314485004a01801b000b240d001010f5500a025184590303181c01340900902070400112440b80b281621640644099100300ca01580e000e0144038801101000c1d1003001400240c99a00240143c403950508440c15100400c0d200c80c483d0003802c820301e0240e0403007056054181940c010b101c0d40c90081086503901004940800c885402c0060720b900b1141070a40c51409000e0004049078100307024030000c0821000a18440d1500f010060a011020034810311601400c1c0308a200e2944603485480000791030b0020700210080600449007490755609a6640140003039100c6200e00503001120310074082c05480c1580940130301c9400e03464540241d1640c1c0300d20321039801c01a1503c0c05006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 726442598 1250 726441348 726441371
    0xd02071a1803030f030702150f0105040924060602070e010303020303130503040f0909061d0304060302180a0f0501020f150109271119030b070c050708030c01021c02090f04 75
    0x40000c201e040003400303d0751144450005901c0c542e0054603004003520480c00c05030412000011410b01c50520000944a144d20f00360901c0058034148400703c810010850b899125414601d5940c00716080b007120200700145400300c040d090540700e80102c00d64200385401400440d40000889800141c40c045001400250f07040550440c044c0d90000c51100c82c4407007000400e40d1071500800300d124083c800802441c141c1c00c1c00401d0f800d00410031000c081e007084c8020406580241d001e4000b0600040c80c0010362034090780000e07031400c40c2d50880b044103203024009020a5904008403400d590b20400100504e5140582c9106115070500c244000d16072035003040e505151210400c410440f00030112040404081d2804038922000249072a0003400801c007030807070142031124400c04487c5c0151a1206948034100f048801030300c064411346013442608000907913810204000c1203030290403000140c0312510100820304021220b15078200060061000c5070b441d0303031400c502c5c60003200100c600284510a11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 726443848 1250 726442598 726442627
    0x10617150126010204180e010902010f1b0203011509050711070b031902030a061e062309060304110324060904030201290a050405040c290a110d02071a 66
    0xa0b010402e01d940003280000307092114200700300681d20a90806d2108240000c031080c220b9511420190020b802d11250640c1e00e07004494220031041e011a880c4401c095540110742901d20001011801d40e0341c01004000b00c41c0701d84503c40e00302d05a85412149010402055650f841c298043d0301c010140001c046410f0109122060315946884c40065440746040c14207400140307082c2c46017051a54041d080f041c00211690508e909403201902c880348100c1d810000032401641c0621005840d0004000083e0780c1d1381d5000c0917510445c0309506200c0488544814135080182d21443d0702d00c09540b01090000c0c1c2d95100c10291f0f401101a5041e030010b079980e04080340540b4248034081c483c41038074002d502c4d17083d074070894041c16400280c0d00042200d95440a110485504442c09400070b4035000060110b0728107044243c201f0a04010100340030081d444065078564404036268011491441030440c5c3c510091105800501e114006010030381d2801c5d103281c07075141110100d03441e08000011343c0035540c1c041c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 726445098 1250 726443848 726443909
    0xa0308030103062d051929060f07151a0d020d050c150a091401230408030409020d0c140904020c0708060f040c0e01180e0307140106171501 61
    0x80c0c85a9800052020007000b03020944195403285801000405c218540703009090710181220840b40c6c1d2801180c140040340c5031f0101c440d55100d801000368014006188028081e882d001b42218200e00c4c040f1017802e0225408010086400003103070350496980d40e074007446041a40d4040c3e4041030321250f545002410b100e41d591481c3e5220f24030365041c0170f1101403400608504a41500c0f000b11890f154600f418025a90499003400185100584400707002c0c01d02e444890303441e050340344508198480d200141103800035040341c000b8a0307001c40c0c100c40c5d544090045410240b003605018603010354900d10900301d48604280c1c0f900503600044d15580000d020010b1400400540080c0d408a00341640c2e003142460081d40c0c25201e50588100108112150100d030f0b504807048001141e848590900508010f480803a400c412203010a100c40004902c482109182440340500000383d46401c1208201c3d180042c041e5100c1c2070b80c0700d2040c001f503900480c0c0031141511003040c0100c1c18182e18080d02c0d03628004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 726446348 1250 726445098 726445151
    0x14010c03030209040f05040606061b050d0f051c02090a0b03060a090213050303190201241203050405091302030d090609050909240402030706140316022802030c0a030803010306 77
    0xf510003080188408c40c2c1c04607068038859070b2400b002c0e40c040c4810724a031500024010f4025040944415900c6000e01c01e060401075050030b015003401002c1c1540c510000349001a10340268000a0b445510b2900416210150114050a50540c1082000318850051a000e40301b00786034001529900346a407000c0305001018000d0441e0741e10013501c03180d43c1d6160290b00856000d0741c00c2c80e40c2008149600e04a400c2280c540d1010b820840746004404681810795070740c290309004080201144945904865501ca54400d41e003400d20964148141403a0840550403070f0200001c100c024088203510054190803140c08880003c1662204e80c1c5460038007805031411071800d06840040903005000115192045000720143c810a5655203010342e000107030701080c0e4080a0040000450407002401300313100d1a061441283e0068403e03240580d20f061201001070001e5030362015000c11441d04005d82803801406075441548149150b507608100e00041c00b000b40311680720031410312040307034490003c491400d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 726447598 1250 726446348 726446351
    0x302030c1803101a090f01060c030e010c020907051306020f0307110604050315100e0c0706021b060a0213140604060c05011103100602100b011d010203070501090b0105030714010c03030209040f 84
    0x1400c605061204d80d5603100001d000d824450001094042c540d0850f5040307542c0c94640c2440c0d0311030b99a0880e6807000d101901c41c140042000118090f841e40030700c15101340030b2900d0b9680e40700310041d8820484e0781399911201c215030000308503803e0700102100340e0301842d520580e03080c006405880054500d0143e5040242c00d4855200702c4801404d0b10f0280b2070043c0342c40901c81c4c00c0191a14010958601d04035501441254108004800100aa4000c0107007084c807440c00108130400000c50f5003810801e881c41c15010790082802103c500e45201d03450000d2241c481008030423500003011407014000e51250030240302120000c0d01c20f0110a4100d4402c0041034070081e07540c0d15184140181184032801040010301c110981c1941d1454944110150300030161580c1c041c0e84c001401305146410300801e5203045010900101d03000403400d004000415100b121202225030415050602d00280303a817100710013140c613240070402c03a60091b00709160340e601450007581c1e407402c01001c18040c041c0f580480c0700a6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 726448848 1250 726447598 726447611
    0x51b04020f0a09180b0603040308090a0c0305030d061706060103050714030106031e0b1f030603021305070315031703060d121211040305030913140103140d0302030c180310 75
    0x207500c03643c0a03040c1c0d00612030185603078003000b18000c00c0310f8000b650290402000c0011901190050000d20b078010008422944580d050340c2c2c1d00b4449034066401107074503900126a1120380041030180d08040c0c408502100125030f5228409990380c41d0280c60705061641d10008200c807140724022503031500c4100c44e071569907541e603002e0003001800044669801044003060045001409019480308460020300e16047d000b045450301201007106d00c82801410340d160030010040c4c5030584165982452a01c0009240c80d15000103025a903074503040415408652106000044211952300140101c1c0b00000f61642c0d2000b0100341d6030241e003140038107003048148420070101e900c90803480451603210b0003480a0701490a40c90040d0046000040c2690814000a001c2c0e04056a4108080c0b040040c0441d15400341d8030094100f12003a0000e99001c0a02e4050082820f410400c42c81d03803815601e4210702d50310302a0246071543c01541849030070724202c43c2449189503001c100100012520074420041d6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 726450098 1250 726448848 726448867
    0x9090f051b01022a101107090203010e07050a02100f11030405030a02070b090f0402030402030a060615030b060f04140d0b09010e12041202060f040b0a03020a020c030703051b04020f 79
    0x418400740c07122801441080041550741c019a07200001e451054920b41d8181401d29080003e0b11a185007250108801c00740170101018041000000a00442c9801641c13941020b03103c00c0903540090075a401c2c4001000425541540042c0891102d00203c900244900e124860080a400b0b502002c0c1ca28500c04130902082c4440480200040c11194085404880d03443e039010789180104480b0396030003105403d4410840c1855002036512520080c1658100c044a6441c4c038112203154014160f29543ea40d032410300e0300c0c0c05200b18640c00c0f80c01c03602c1300e00344802c0c64160485840340d40a08041c021007203038844015181d0707200075000e0aa00298801319480e084141600806030307100c4100843c89080340b41c068840d220800c680075207003405480c40e02050907070240300290f40314402a40302a6000c0000040d103000c0040030380003c9040d55000350b40c82031800d4000b894401045100c6110303420981081001900000300710070803101e8102e4541c481410000002c00a01804190100302c1a001910180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 726451348 1250 726450098 726450133
    0x41103060111071a030f071d060a110a051f02270d020405240603090d0e01020304030812010e390c03070c1502030a0f080c0412030e130c020709090f05 66
    0x106202680b42d44545595003507003164a14240741202321000c0403850000018144600106400c80e214203040503c2442c1c0f404003481e0030340b00e00040d0703031503000180040740c0351460100204950040b2841036041c080000101c01110710107070103040c5030950200d44071500e1f0702c0c1c08580e01c0351a5001802003000380381480030507513845000c0e844440351030310b200800403580c41c10b201a07a01465802000703003441e10b4550000c2c0d40840c11034004a0543c030080c0000000a48a0001411070300c01c7c3c101d207440ea030352400550098489000d00000d045c8102e44004a80030700342c19031421802808030030010030200c140e401601c4144900100000310f400300090900500c0f8417008042c080302c0e240403201d21180f80140d01203031a40a41d846100020740319a03541000244217401d0542c00180c0d44c1a2585081c2c2d4501d255440e01340700003022404108040c036090010300d00b2500c403d90729100d026061103c0c1450820080d2550b00c540550b04034141e03134014a0041c800b42e01c9d00502216809821031303064111a40c601704 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 726452598 1250 726451348 726451351
    0x130b09210a02035505040605030f0a06030f03030606021b03031801120608030702310519020301090f06090e190f02180a05060109050117061f120b041103060111071a03 73
    0x920040d56404042e00b0305c4c0306030211411182940e9600c2e0441d205c0e284500700d0b403c0003809662800b900c078040400811021000400c1e4a482628000342d2685410004ad0400900e14a00186416100d01420fa913482c0030007290070000c112200c190034070301003070b0051b00c040c4410102220190f142540200c1c0a000000042140d107000f103510846a1003650562480541c11845122014003400341c080003120241c0c00145e042035a00f08103c940c405003024000c1285c00c00d034450483c040d00d0780080b02e40c0f480c20b803103080080c2610810a20250f040002030035654100b1034880800383c01d00250101c1801005104900c909500800381c0103400d014410381d000c00f500990f0b40381c42162030080480c000d5801940714101300c03901030b1202460305150044440180c20024a1150084010b884244078011520301501000d01d26444502e03003050041c543c041200e2444001d0b40c0110324120003842c004811401341ca0f8400360074a406a11810410079042c108052a8800714510070a0403c103008941190080c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 726453848 1250 726452598 726452737
    0x7180f080f0708060403050702090c04091b030c18180e010f09170427140a051b031909020a21110405040309030605130b09210a0203 58
    0x342d5005407106003450312038006a1340100411320800c8000010f04100c84615444010b2513001c60605645440e4101a0381b038008407541e000340c2c68101c4240098046c419018640e1203480c1c0361800403000c1074007107441c2d2030314041e138041c654076201c3c0301e185200c00b5040f403034100302494024890301c810311300014003400d108941140c013075020102040a108080301603e044400b00380c5003080354000801110307140c0341e2540d000740a0507140d20203a8413002500d00c40f0350007503090003c0050186400030301c18154054104808004072400c0003440bc400da15404030381102107850200086052061000079082c007119030042c00d002681841c011040e481c01000409254062401c0600c4507140d0401c1200300c0e00c04503070040105a0020060001c00c0310380d4852070307108907403100b00329062000ea150030f55025003c850842c0d099100310003142501541410301c103040c5c103010300741e00c0c1401c001c0c1e034002c1c0d01c0340111a01840b51482500c0300703400b680d40040f031440b0790f24201c03a28580c10b50390401055400c809940d014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 726455098 1250 726453848 726453853
    0x4103070c06020f0d080703090b10051017060f0d14030301050112020f070f030e1801080d18060804020103020418091709030d2105010b12090705010807180f080f 70
    0x1070481c0040303030038040350761050003400314002c034500281c3e24440003910040406540d040b85000191000034080d000e4540704c020800001e1a1804100580d02c05e90140d170704200141c404c585c07855031200706864102c1d1044403503041c90022140400c180114010010304158009446500710a07400300007141030355400e98078000c4041580714018280d00c10800450107a1b1020414900418814074108540038401d03c2c2c03220004100d1030000e211075050b0015034507661301010041180c6201088407880c0300100d42030091034120038440000e4460f074030344152018407044400041c00c5a00c00da0444000d01b800c50006a120801e040c4140010301002000f2104c0f400840150f20a4544400c261a071542d001401410040d048010031111001d0240203600c1250001300c40280092013400b80d18003030b048000c0d116440d0707012101da91a5804000d4080c0d022500601c03014402641d00458803035001d001e50402010826a400922041f1080c580c03184501c003842c0000400c0850703011034944040f00100c000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 726456348 1250 726455098 726455123
    0x32c630a0e070308031801060512010b09011a0304021002030708070606030b0a051b0a0201020d0e0c1c02010c031407050a0302060106020f0102090f0f0a08010504030525410307 77
    0x78029a100018000540520814400155646400144854900100000840e000796144042014044220003680c140d9440c0d107400710b21810004061030041003c0f030030f50140c15201402140c1a40310103003001e4024403600241240d080d00800c00c0b103803580d0f809209990380c0e40f5603050407401085a400102c0d003814540f07000c9000110342c3d01a190080070b0501032001598121b8480408a9002114000035550203000502204502d0303c94101c0d0014048081d100d0459044100100c0c10f00703150203144038103001c20103407000d41d80c0180c1d81d040c0d003541407e25012498000c80c100020780074483c0010403a03ca64a020780415601142e158100c4840ea000c494500c240446050300f82d005101d42660001000c104110007442c005408504100002d001200107076103821000d401e50382c04450a41c0841c600242445403000814000007150307218062002c0023000503920034031024010220700c440b064108003003010500518004000e64416182e44840b5000b01c0000b09440703410220050350703a010320b081c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 726457598 1250 726456348 726456371
    0x15140415031a030d0f0e0d0c05041b0219020a090914060c0a140f1b01020304020f0906100e0f12240606040e04032c630a 53
    0x1040b2060480040181180540554003100c0152114611204001c42031055010545a103030482c1e00c540d00400600780181e0900c018041560300ca8007080300400a4a500301480e1381e80800d0300204140c0c1c2c120101540502d5000240c440010750708001062803402640c0010000e4400ca5240c9401c2c82c00152801381e0707505003000641d4000c0b40a844040350301c201300c2403118201e000052000b61700c80320301d0f1828046140c800b682d8002c182800c01c0f041c4d039070000a020540c98080100080c44500301d0700e58006141107000310741d0315146205608180000341c07603203030794941d503010740c1c10318001001e40540621090800b0540d5910000b0107450603220200030001c043d0800c030084540b0030300000c0e2103145401e20749070b03481c030100100520680c1080396400da1420002c2d907603034030700314035140b0b020403016500740b030b43c00700642d0100703001e2000b648040404000300c0c5e50090b440f00700e1101c2100700c0541d40c1480580da40c2801c108185640c1c018905000680c1010302e070201c41024015a41c0034400c101d4141c90a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 726458848 1250 726457598 726457631
    0x3060f1b1c0f0b0303040513020d0e0a050f0d051603030609021305040b2b0510140609090105010f0614190908102c1c020d030c181514041503 62
    0x1400765130190020402885581400c009813143e407110f0641c01031070301c071211440c801285c408051600441d0003410f00c80d805e01500704010715504c14444058041803c1d881409080c601c51469880d018940b0f60061000b0700d030003907200000a082c00c5c4400e66440380c04a01c03507a690020707800360621440c50b01c8400d50aa082070a18440f40301d10410b422a03000045503145060801303600c0c1d04440c06d1040600320041d4610a000f60423034030f900d01d804e6095a08202c1c0070004001001000751240b0b0703240c000100009000401c4400c21600c042c03c0c00c98040a85c40142074045c8540307203051f000c00856100040d01c003980000c008048440401c16102409a9010040151202800440d030042d00c54020844024880f0703005400e1000110205c481100c00d040d407907030600c10012421400740e000084e50903489500f41c09072401c0d202d120b04d800d02d089070412400b0b1520050381c0c008c4400c8513400f840d510004a01030141c2d07034500c40c0c0d05004181c803540c0e21804801d100d0126030b0100002801c042044075011040c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 726460098 1250 726458848 726458861
    0xb1b0f060718150507060c0c050a0803090a080c34030305160b131b0302010519020309030a06090606050607030c02090402040605040903020303060a0e0603060f1b1c0f 73
    0x4409054961154102201d06480803200390761507802c030000c006400c04912010000801194a80341d844480c02e0900004845160b02048184160b0700300480001c2c0001c140d104205a00101454a0341c0790400518034100201074010800c49002411810791740c40000c80c80051511a0384550100c42101540006002e89901c3c1c455200600481032000a008001825171142070460b000451001615103010180003a500d00ba440031104d4100700a0003840c01c840b01003491002e114003140740c51035000070b00074440c0841601c40c3d80c0802100103c600d100b80111024050003c080341c610003001c0c100500240800041200c4440c50034100207241e080000aa60069405071140300d80c4013000d03000c0c40f2005000400c102d0f8000d030b560401042c01d07580d5200303011001c1d000740d00454880c0340003001c1c4010071040350407100e09842444104240781e50000743c503590110600d0400f2a0716201c503101d9503d003510780e043c88401180082910011000800600007600400c400144940141e4140e44012185e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 726461348 1250 726460098 726460123
    0x60411180a0908070c0303030c085202070806010e0f0a0f20041a0702030d110c100f080f07020d03180c08030a02060c030609010905090c04060b1b 64
    0x1104400190101d41c15402250b40901400d60381e86450403d5462064603a2140c108501095840b100203000d81e920241c19135000c48100c007035807007401c81044540b204121144a00c0c07200c00030f210a100508110000f084846010101015080c3c10301344ca01035110440e500401d911885210000901c803550300341640d000c0c60f00400c1c10380c1c55407610703501c0c40c01810851000111a549828210345500000110341103115040100d1035102ca0400080604913440c150352020307640c80170b00c88200035980101c0d80740b03489551401c0c0a881d6408200b03c517400c209001c1045035020901110010a071604074004a0344c8440c00d60742c0744503e80d9580c1d00503003041c03001e0720241c0c010380c0003030119100740d80254071100c40071054080c0c0400245250769102424038076500b01403459000418000c0750242c04020154000c43c0540390241549031002c041064084144601513103c0e0711080402d1100c102888118040c071800781c0203000443e141d0180b224180e1040c0c801c0409030500042c0800e030207a000c078041c0d80450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 726462598 1250 726461348 726461389
    0xf050301030b0f092e0f05011a07021306030b07030e0610090e16120201083102040e150601140a09180e1906050a050103080901120e0f060411 62
    0x100e540b2030148190354002c011010b244180d005103040c9130440c0a00c48542030745411a006511317860b0b10810b0548007001d140c2c04110342802d00500100c02c0384641d41ea07490840d03400217a2581007500002c1d05220a4111000e0814500780780802441000c0c0003142c410415514144100c45150302081e540c0c1100700d0f444a2a1005400180103c0308650418103000199004450458101c010a0300e198200f40d801450300081c0b5240d240110350700901c540b90700107181070762071995448040d0450302c420000125040c80d01c075004000011540c0d07590001207000080d1040300c40050704004030300301091055a100f40841c0792441640038000c804007c03117030885815030341d16814a182115030b15448807180d100d0040c003a00c404800d1b10598007040034010301c4031002c003c80342160040c2400022584007030440620740b405e090040c808594007504645a0740380c01c1c81e01030140754251721104010061162a400c45010348030340800c0703c003000240b03540500c0c003074080d00394100107103030420038900c030310303000b2080c3c2e60 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 726463848 1250 726462598 726462601
    0x15030605150a0807020f070602030702040f020406140c0a1e0b06040506060708070f12090311010e180603010603060204090b031b030a0b1816090c09050a0504022104050d0f050301030b 80
    0x62103008031079040f04040c011070704240c0890150b14101f0f645038201070010f910106550040d17240038091444070310004407017185054184000103040a00c0001c10b107400c210002000c0703c603040c0030005840102d0304898015054801001c20555180d40e644003502d8040c0108040b4040c2e140074882c040c00388100138119840d000c0f084d5600720403508824400d0741e010001d007801702d022401c14044518a200d4035038038180070a080d072408601d41d190300400d00b8108510070038058060f440e80700c0010a44440802100890f03035600c030001f03014042e1508010f080c82d00114002461907e04e400c1078007520b00860588080c6c408038442191001d0010841d20b51551040f0f04202c0030554070080d45401128820b0003a425006042c9402d142510b11840d00181181c2c0020403c003c2d841d5108030704449460349440da04091420000404051150045900c1036600041d4071441e01c184606092140e2165101c004040c60a82811a1114122030311100440d00120906040071701c1501141c1c140c0e41c4c40a1031103142e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 726465098 1250 726463848 726463867
    0x111b0d2001330801050603030313110d060c0e060f0d0e15040c21051213031502121012030c03111b01091512050a02131503060515 57
    0x361400380164295542c5550014441a64441520780000181e040001400490310809040c1030755520007481d991400040c84031540d008000c4070f4008050b00c100210900180c24035a8010300140240d1342e008401100120400400d0740040912a40680303681401d500c203030003407080c244624001d60400300400c03ca8403e410180d40d002d043e078140b25208a6510010041c0702904c40001914141d4480b41c0380f8400700007501e82581c000041c044000c0a441380e08006c1d55820f5030301d80b8804561444040041444121140c0070038414000f944c1182155501e081018081e000941c0700361220760380c50241c140000c9210703d02013038039400c079414451140f0300301d400c5071001c0300d13511180e40003102001a066982034008000f0002c0041d42204841444003280c0c0713040c00036190405550100300c800184844c5e00d148150441c80c82e65040805150205440e40c502030000000d1050b2030007020540740410b0041907104402c4100030822607603842c01c00c1107580341c00070040343d03a0410b03511148800040011710032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 726466348 1250 726465098 726465137
    0xf0a0e07171c08010905070509010c20061204150510090f15080c010905010f1b080909180609030f09100c0209012702040311060715111b0d 61
    0x70340400341020b0307031100100604a141c29402080880b00003e08080050100580c01d01c9030640020490400b14a4030840e02c0000c0e06026054602400800400211511024003940814083d820042195640314003100842e10710b0310381560b05603a0b40302c500070944a041500d11450303015101500140303e0651500e146407001d0462050f4042c000c0e034681d0441040a0440602c0e24083c0000074081d06510032000300043c40d810541d072006040000009000f900940c1060002c9280c1e44454035904898540f07041900030b034030984c80380540000c0074408024104141d40c0c0d180c0c01604001d000d443d0240c5960002c556070780201c002c8031005c130404025101d11841c00000c44180c00021b0b08090022030041d0700000c072018000d03440855246080302840b01051148661100303d25002801103041501799103500711803c120307207502405030b500001c4403c24031244411401c0302c0d5601090510400e14510307a0a801c541100c00e582400e02c4a1003c046034419010071000e40c0c142065075040103482e40d1284048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 726467598 1250 726466348 726466379
    0x19090c120509160b03090f0303070903060f060e13020103060305030d02120c0f03011413060b0a0f1403040f0221331501110703110a08071a0f041d0f0a0e07 68
    0x251347c81443c49a201003881880594846c49064885161040c0f070f60601d60190340c1130852803941d003031034680180310380c081d00b61415412030b0380e607400b44a8488440c40143c000307080c0c6820207407480c840030449107003107049500207100940f420716102c8420b0711140d00c2c08405020f103042408410030284018864440d82401c40b550486004001d030841d4165048080308950701a000f8912100c40014120540ba40120f807840e0300041d01c2c5001e90380030080d04801402408041c000800c91074034172034007200390340c3c801c1310030f903c40410700c24140203242c110a0800d64495407110401d121542c0100706c0030411100381d41c02a10440070301c41030000342c0c0c0c40300e04440001d035400c04150f062110301c04410440400401c84603019500c1080d540d5100f119603010810984100e0b4020f90086e80b00050900c00803e1262501c0701500384030840075214500551112000e00440d040304e400c0d207180e1369410301e02000c050321081c02140701440c030040079115403c00c0b8040d50125130b008801e40d4030081c0d080141e030309041d00d2035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 726468848 1250 726467598 726467611
    0x20607020d08130f0602030f070609020607080f0a0f050306060307030e0313090213051203040303030c030605090a0f0b091b0d1104060504031a1519090c120509160b03 73
    0x10700c245503241e51902c640340c101494803500c40f00e00d001d00340000e051550305071010b4801c0c1d000450808905103090440307031007002070040590703072200949011521200180c42956034820141501e44442e80400c80b155000725580c0c60020340c10801500d4442d014104683c00740e000580309600d541c3d00e145007039001d80784036817445005d07100821100156101d01a09100a050f520002503511031595520a291180c0c5d078005030311070151160300000e490000402c490071a54036040200e0407940c00c0c1070940081540ba071116400c000004200401c02031103030310511035a040a2010030001e001181030244a2108a0701030040801408400c0949490759000c0d04841c00403103030100d01c0c81c65100e00c04e2141c4d0000c1d0300c01d20220300040390034020410390940c0809c500000803507500070740c5003102d9205445030549580900800241c40104640500c8044040142241103000c0c41049454203004098660315450300200700e24244c0490300c003900c04035540152080304010590b680e07081501c0b0210940c00039044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 726470098 1250 726468848 726468859
    0x605130207051507030b091006020a032d09051831050114090706020303070e040914060903090a08120f0c0304080703050d08090d0c061e020706090c0f0b0702060702 72
    0x1159101e012a55240320310f9095402048078600e240503c61401f2024000030b20324089414203000056000440d0180319401d464045404a448101c01c9600e040300c0e5215046900d42e01448011907030440552012104203480b51303180c00b0240c1400c1e8014170300a40748240c0340c5003031024550b144003900c041108d011070f00351040010303c1306607550306007114130200e441c03010005018200002e014003448020001d020030700140d861031800480040082d41403041d480d1040390380e070b05240103010340e0242e4601000b0070b440803141d40d030802c0c851180e075075007062918501c1004003060100d0350b4440442c81c0341034a4003508206042607030340a1000001e80110300041c56030311080c807001521080030048a00203600440280110303040c45200201031400050418680c0d5005136032038240d06070700c9603603524416000f610000e20681d120103464880001040f0017455280003050003428804103906c19001c1c54400c0c0880403501e03664080480e180007480c46408105c030024040d1801504204d40105a8644010700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 726471348 1250 726470098 726470113
    0xf0c0304030c06020f040918110904030813030e0409140709020f0304110f06160318030f02090903040f0608090d0207030b1f17010f06080c0a0519080102040314060604060513020705 79
    0x55002121400110254464510f170034400520002d04a00e2204101c00c0cac07010141b40c81c2c980c40103488041c016010400380b1895503294404d141c400d24141600c40c03001002401711407203038280f0140d01858040c80612074043e40700009a0004144201c03003924002e50400b03811035407252101c400450140c01d21a8008070a0000880303103a480c0c500401032000e02a5070414040600e00b402400040c01c09954802c0711480c00051002c01d0028504000140e41145d030001c0356a644901c00d400c0d03015641c090b1000400e40c69020a1650b04a0380661003100e14104032000701c41c0c0303068201ea44640c0707440041c00a0881101042044942d00002032501d5465408150300176958412045100250001c50411741d5480c040408c1182403030184400404a840042000c00c044000046490807107110361441268007103088181e070700c1c81020200041c070041c0d0003151940c0c2e803814900140844251004801d000e010001051881d2034401e10341030343d8010b040940710603070581e00000294800c1c901545c46209016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 726472598 1250 726471348 726471359
    0x40312060b1c1e090c030308070e0a0b07050a0b13050f070e0f070509060a03020d2f0903010b100e1206070206040f05011407030b10030b030d030203070c0f0b0f0c0304030c06020f04 79
    0xd180006116041c5c4a14552030360600409401c0054221003c01c1600c2c03907000207035914072084809450400d42a030341c0d100960720300780b450402c8500b001460a0f6044003000f46600c0c02c02080120903000382c1c2540c40343c40c0c0c000d840a4645403503000e2115a42d1030320021034040105154580d034450303d9428002c3c034085414000a02c1b54120798081c2000039000100c00035a0201405103920309603041d06801d9410704599144c0c04401c91026030320b0109000030424203910b42e000d4002c0c000210019010303088954113028010011000d83d4641e5015000d0890818447d0800141d4644501c0c0954090500750b11503503510b41c00c0c03400c030140a45a541d00ca104051042c0f414050090041c0e600e40ca001841d10b081c40d0074805a0041c010b40c14041c146800903442071600e000c5088405e06055103001662550703000d0050321042e00c0034802074190f100d00c0c100300042140360b00303220b401249030f801c58000c142c1d121b100020403484119002000030321315100420024416401038014004030305422800c1a45a5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 726473848 1250 726472598 726472601
    0x102030f04230f18070302253c020409140c010906030e07050d231605100c06050411060c1e0102040b041e0e040312060b1c1e 55
    0x94000007001810200100040d0890b0a40201d4600059034109260044400010420750501c580e1a8000c400c110010b4001c4e44030b6811104812569408240d039603000303003031010460319080300c216180d551a100b080b0103510283c22842c1550050300c0c17408010016203444103403a5800c80000c076007050301c41c1080d50000b1001c0f4068224a5101c800a01c40010740b0f01c00108800c80c3d0f544000b0a151425100ca041402c011424005450303040e101c0c0f0042c1d020038607111445000c6004500000c008804903810081e00204500000c188249800018240c49008000510100000c2d24000c030300c06002c4100008c005400c61580980644a03d1f40b41200400c003013204d030703402001c4010360f41e04904c00504032803140c1c1180182d185960703030085051901b855106502840317180200e220980c2c0706800d92518100d140c0b00c030000b405145807985524149440c020301540410300c002d174806d6050001c0840c003610070401343c40c0d40e010402c40c1c129158000c1902e0000070802c044002e0700c07245000e0b00f08003410555 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 726475098 1250 726473848 726473857
    0x20a030902040c030e0c040e0304090506030712030512060f1008190e0c0103050f0601050f07050106050a091d1f0e071a03090d09060c060e0a1b0f170607030b0102030f 73
    0x1c984000c1084004817500c03900f401c040684042c0f040c3e06d4014185030400c00041901d05468250700005102d03120300e000a4a0040303942e000210b2003d07410b01410030180c0c4600680013040701c0100d00152610742208203d078084854000799005152040c0080c0304038411003090742c0007080c118071786620440083c3c4810030b0743c004200c55213455000410000c500e50349441481d81c07180c03070440d080340c003400d1007000200035101d043c5245502d110082501002c1c070400f0742c001002444014404004540d6940c50398018088000e00d000102c0b02034120b00c0d0707500c00c0c00701b581d0429000110710a985e0380700e43d0040c1d6005004049003000c051190b490081103001c2641800c03000110781c4008103882c1e02c0e0800116240011001e00e010400100400c100026504a0780250529a02410100340e03400d40c01041454940c2c84440a8040b401c06140e140f03056460102c01015038558038041c4054689481d81c940050402580220341c961281000607146442940450f040c1704e414415646045d180104000d03d5422 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 726476348 1250 726475098 726475121
    0x21b070b0a140403020f120313120210030905120c0a021c050c0a030317070e030307060e010c030902130b0a080a0c0e0609060607120302041203091a070213020a03090204 74
    0x1001401020301c5400491411440200031045842e043c1103034007182002c001641d105002c0c04104036514003c600c2801030301e83c2d2070600c0d0010301007070f9550302e40d0381c1201d48103c1059004042041c1ca400c5c100740b00b0f000340d0129a41042c02000b5407960114038000641c44424001200e001d004000401a542c0f80a0100c0a40c400c0f040700042e4001420f00504241c0c07000d40892150305017490400001c2c1d00200f61881d000405850aa01961100c00039101000800350b17481d45170000048070b8040286580c0082c0c47c165038034008026040c410101a421156980c9020303502161000740d4a0181d080d54010503004140540700e40152507840f1046894200b14001c115040c41884109002c403400ca05892540134904441006141c01c010010591601c40c2101c00f42111801580804079240a0f404841c01414040582c9203e40910b050003480300790030380600c00f0030403a441e8503c1c3e000603490080c1d0340105c1c1c0040c2040c00d54110307040321030003e60010079894181901c5080c4040503070364911038180c0195 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 726477598 1250 726476348 726476369
    0x1206050d030201140109090b070806180c030f0a2708070c0b0c0c0a150c140f2404170d09020d0f05060a09031e1b031808120d021b07 58
    0x110351940341138030482c0580240c0c20703c80c5402d808201040302c034500a0340201060503e0400c0b51a1600450703242401c1c0400c16944031505820b1000c2c03482e6402c002c0d80716a0b02c81e280c602181d240e0407410000c0e10b07004003041003401341c2100914000c02500b44421005c034440c5113224039202113a82d407140000140d0780100c00740360001c10f0b450203010050101040c8050100d8403032207014103203114018500c52859a5134100035107000e144d0100300303200c5019420403d12904a40c800c0803400d548603a20300303466225941d103200d1210f10180c0511503482040c015607000105a04c0962502086404d82e082142d61140b060349440c8500056114090034824090040c0340d20422400741c0d050541ca8205d0150078021000d00d000c04000c042a4071010b0a1580310180481c2691500400400c650600b8200c0400801076030944a00c0101600b00940c001c034030025907501030150780d0340d050741d5480f90007460140f08003290070031043e41081181c2d030040c40302803410030701051424106241c0324034014603900a0408034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 726478848 1250 726477598 726477611
    0x3011e050702100905030304060b13111306080c041205120a030b010908160b09040906020f0315090106080f06130f060602070b1e0a17070c0b13121206050d030201 71
    0x442c2d0501143c42003010b80101481402c010f665850307660f11000304043c0c00581d4913007441c600eaa40741c2846030010000d41d41d05009070400c04490084075801360111070201402030100040070380c098072615126041104a19052a14080c8200c800b1480360b6421103103801352400040442d01400d002d800000260750780083c40c1c210760000540308601c0c0e504115119405070030b840707ca0b02d4020240d04265500402c0075601d0309401e1002c20b02401d0710010040030700740081880246a240803014610414408043c0c0b13415840110038021441e40a00925001070349001c00541e125a5181c082c0f90820000b820154a01034086662070071940c0c0b9454040041d51685000c1040795410401c410203400100d51705440e040e5420740e586840d20f50b00c00c4410141c1c0b07010a059080600412549035100000c040a030712619141d82d00a0a01c507406800f1a1050108004a000000c409144403089a4000000320681e66148d100ba5890800851110305007901d40c90041840e4070f07501030000718203109800100e00b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 726480098 1250 726478848 726478861
    0x1a0301090c11030d0f0b0d08031012050d0f020705091905010801052403120309060403020f030a080109090f050f07060801051c02061312080d1505090c0903011e05 71
    0x29118050141c074100242c0042242c1c1c900380200403202e00d404000380024100300d903134050744054076040d07440c0b035448a42e07050b00030244003001c0c5c01103201e254040440221982c861040b007910b00c0d40910080c1256129140700c1100ca800b800640300c4000c0365004450506544200003064883c04aa1060800c50030800d05820310a4902542d40542100c0000f070120349042e03c07418501c15214070240704100340b006038039003981d1030901c403c180141580c95016664174001d20183d03682d490603101200184200c40f00030120980100c150b64010803a03030340711070b0b142e403030441100094181400141d030900348801d101030000b00c007001008038007494140035103491f900d05900038020301c0050380718a010701a80e42c00d0119000d00c29481b00480c1c1e40c102d8006849401c000c0c074085000203107030892103200302440300410511041402811420400100500407160f010303019482c5a140b030701c00d984c0c10410442c04030300e0b44400b400241c200c03020b000c4c00001d0188c01d41038441600d0b031900c04042c00880c2d07581041c00174 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 726481348 1250 726480098 726480101
    0x61712090d3e0d030f050d1808070302070f030b010302042d050106110f0706030203180109200f101116030c32060a030902030607170603190611041a030109 68
    0x15111000c44100141c0543d0741c40103400c0f0f0048040d85020880005480881d00c281540040c011200000010042c05d0540c03038804c1c0f040d0321001041c2c025200c0c141002842d064640c03040b1099943c450101d62159282d0350a00000e401000e40d54414510088451208141000215409083d4641e404034003945480300140100c005408241103c2d0041401584a4031000407081d0440385180790050b03486c0c0e100b10403e02c1c0480d0941e1400782c11750808403a4401d02c04528202544184840d407803081d8940b1841c100440d01584c2c00740e40750041c42401c800c001d507600880902c90f0a0000b0410b4030750150382020181400345003600700300d407001070740030303040c04514003681004281102c0d0f034000c00004013288480c00c0007028400e201611840000403c0400d580c40f9070080202260701404551450501c000c0141c440812510031201d2500704c080020031500e00052a440805400345030004204a01c0d150140130f403e1246100c80644010000000c44141c4203c500040305850a0990f071a0350402c4147d90 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 726482598 1250 726481348 726481463
    0x41506090e0307140f03040303120c0c020d020f0105090411030406110c07091a100f270504091103061006030e1b0904020112020d061712090d 62
    0x4100d4681000d04200c4140001100c4190340c010410a2440031400102d07441c040f201281400c5038003010a001042640011011488400c401130034070100c1c854081c100c0e8010a841c801951003038001c6558005814034140c04901140c0c180350451034050000d002c241924000800d401c0c41c820000100014032090388180074603040700407142440d105490360065520724450043c2c10f2883c0c0c2c0d41c58805020000a030442c0316042d80a010341c081e10050700030160624030034400a50200764644600c9280703940905001500110201440c03600b1030400c1c06010082102071011280895036100c03011080e0b408229040c4604050781c1548a140d0030900000d05682c2c0861580c81e5680c0594030352001c0850780b5000100401044d26070300031a503902d000486d01e9040c01c1c010b204e4641d10024004030318030200d811040686500900c2400c4080f0000c002c541e0355400002e0444084a05201d61840e6180c01082c01c21030038002c10388200141e64140d092600842c20502240f1101d554070841c1290541908011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 726483848 1250 726482598 726482609
    0x31103072105091b0d080712090509041103010c090326040305072c0c07080706021209070f061103030606070f0b0a02030a0b040c020604020405070c0f0c05030610080c012105041506 79
    0x340820113a0742c5400031801200001071005c0d400060041908e0301c5002c0c07010040c00300a121110f07600305410510101d11704d151099019500703140c95030003c04d000d003c49034200d940c04580312945041841442429140b030750510340ea5079008120000100703a0400200d000340540d03981149201e82846803032010329440350b49100e1048c46e401d04002d502c1410000b0b880c542504034070011f5941140d403400d0300c0207225125070000301188040500c00000310010b082e00070303140455408080241c6810042e00d003c0d800d50011409940100700241080c10114050f16440d8420380c0d07500c82141c42e03a0380303180303492008030b038001d01a07607011042041081143c000c2c100a10400d0380d040081ca40607280c006c2d2a01030040000c0d00a41d00d0f00041550148522201c4890a42081401d07400c0285407402d031b80d818420703120310381c420f01c00c0001080301103110302000c40440c1c940c500104800003042c4c00646495010148140074181a0280120045040e010300b5128600c80d100202d01030764120b43e03c3e4122025034011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 726485098 1250 726483848 726483859
    0xc1003150810331215050a0507080604020c0c0d1106040b0910030c05030630010209190609120602040b1c14090c090a020f28031103072105091b 63
    0x3200d18041450091406a0358140f400d14484c0384541010300300540b01801d10f10301d1350320b44410405007054a81c0003502540d0344c4c1da104180c64444c00c00b00800da00a07402c10100d9900000300031120f40c541440300c3c140c1d442c41111481001c0d0b0252000071860f030070541c081810100f0000d0002224030309100414403c210700c0c00d00f002001c4050400a0007400000c11041c003500100350300a400b43d030307501441040342c403c0401d900d4000b0351a000090203500f0104415004544100045a100300750800f2002610225a070305449145410740707059154944031401d0780c255a080002203400400d0740000c1c0107401452496804140c3c056096004441200222280c1c0840100c2800715240003c16049200c044c22112000b00780c9980d40380500074890103080c0c4030303080d4000071120308001404101078035496a01048550f10855030506809442e44a00701c080a0030013040000c4c506402206158130940200b181c16403200a180f41e503104859055410002a038081c4040100d050080060101e154030181c83c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 726486348 1250 726485098 726485171
    0xb0d050d0f171501020c100f020601051503070f0c02061209060a050405060c09060904090c050909010902010f0c1a070e0307061b23061005120c1003150810 68
    0x64001001c000502111200c0359000000301e0030341c0c0308003d0042803142c000c02da44608410101f0242134590648042400340c090f20000180503d0140c07903c105451340c812195142d50344011080310a000414114024405543ca0f06070260310341401030301c03025240b41c6041c5100d0030031100d02c52400000918000600c0d040c9010400041d00100325207400c00140309042d62a00c15880c0081c40078000c038090346800c40d1070306a00e141445052a00e06040791320584a50400b515444889030a94804880181c0401c10541020b078265208007880040180154440000b514100170310000c408415903800c4c0c005003001c03c01078014a814421980241910300b0074210b0300c00340700c0a2048440b0003a8001e0107202074502d0403c607008040c0510082c880103c816036000d0718181c034850040306454004c070741c00390480c5601c0100c0c103400000d80d0400034900600352007090301140800c8028111881e14000b4108001c400061084030070440840d840c0440d00c00440d502c0c80c030100300e8a45804842000000c0b00c008907 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 726487598 1250 726486348 726486377
    0x506061503061f02070302090a05070809160b09180702062401080c13030c1211010806031506040b18040b0a05011503020c0127060b010f120b040b0d050d0f 68
    0x903043ca608108450301c100320003040368010380c10701183d94000380d00701c4a00020130a03001d1156010303c1c49a42c8946a28480d500c035030841c1981c40802d008003d200d0048650240858942c0704007034240d82c1d20081000303142d14101084070340702c5002a0754010140c0e011005001d4010150145000c1d20201403034400c0622450f100000d204070710117081c1410b4076600142c00c2400d01003240440000e950400c0200c0368040d903502c081500010508030640e6078218000203e0a40e40c86842e05a0152038000c000b021002100c100801e03034010b0180c49541e00ca5130740d415003002a22150f036104601a498401d0488038a0b05d0700301044c40c5603004021200507840c0c030780148052201c981c810400140c4074640180c40e0303c0d1000b03d050040c200950b03c00900c42e03040e40340c1c845051180c4100c0620320310440781072104200c0c000041d10341280f0544501d0200d651016081c1d0f00040036440011026001403010031410610404904020001310b010380310b9810200650540c81e8001e003880d10001c0003480c01e908030b01c0030754 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 726488848 1250 726487598 726487609
    0x200310020f1806090a031406090102030411120a0b01060e01080f040b01121a042102010605060f090402040b160210090e040f02030c090f1906080312071b050606150306 73
    0x1c1d040c0140c50140408420003580301d04040d144c0000c00a48846031039512404c0c1480c50f000e41d500030198a2150030002070000e90180243e0780690341c0001c820050000f40010440c8003031807240001c0c09403041c44420f034080766111b007540d40208801d85030032038006416000180141c01c01451001c0110441c01400006020482c0682c11101d0004507491850200c0c40c14560020042c0d040503030804040c4244410300c80481d4800611000d001190410711141c00d00c183d00b601c40e180300e141d5003c4018484084020b51280c01014186401400185415240e4440c85509c1d04007030400100c3d60a0b041001045080203014080940803c1c105003042900e001d8008180a01c000d00040000503006e0010046417010002c1400c002c0000300840035a00e0030400000e6488402c44110511044141d480090384000340300d05000c1d03920100286140002003a080b2549400107080c3c01c08004070179015070910a208000c682280f8440c01c090407082c1440801c00c40407440a41091204000030004d0000c80c1c0e80d40d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 726490098 1250 726488848 726488857
    0x5010302280c1704050103180b010303050d140910060b130306150b0a0e0922080a05090d1104060b0f18011e0c021207120303020313200310020f 63
    0x21003454007000301e400181160011110103004102c03050111070849111070300b40c00707041582c0c801e9030308002c1d0000080100144e42c41a000103800c80500000603c08244030354000c1001520b001d0700810005d800076002061803030304a842c556a6048040204240311941c0141c00007081d41070340035800c00c01d00301501500f0685174031000700704035030301d40c005030304409034200301d81c024001c61503010344403020313840c001c2c10720303000e15032010720840302d0000260440c034050715240c20311100389520030f0703c1e199542e5802c04954811580794050003028030041c40e895030380c0000e60662a12444030001c0141000041c8800e4803042e41000d502c5020611200420400341c0c03041d99140491307282e600420f12403000c01038442c8058909214504100d000a96503900d800c141c0026440348252054035041e0030724141540c4030032081c01043c0b0800c2c003482c62003010174480d402450300a01c011b900004141c0302542d8408402065419142c0200c0303525101d003c65240038020f00d001e02258590652420420782900c8103d80308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 726491348 1250 726490098 726490147
    0x2010501140a210203070b19140f07140c220e0102040e040f060906151404050402030d0807090b0403150c0c11060d0b0d2d1115070b0a051005010302 65
    0x8500f107403415590204100b070020320201408540d50b11000074140c858402c0040c2010110307000c070410301e140f070a560045650f4840d01c10a60743c2030603415035902a40c40c000c0d989104003449192800c0d5043c0e07a803802001481950700d0005001c2d03020241c04101524895180103070981d10502040008802400d03500343d1142d4070600d00921142d1600d0325800405040e10090140b6141c4a0750301d10721804001140152100c0d00c01181240002c00c0c20002916000c6030003d40503000840441c12680c00344000d10303000340300b0b801c002d100c8648540c00d108881d00300340d2003074800c04017840d0445a20815845141103027405450009000110760301da50031012003609020380191400151040c156481c2c0c2e0140c1e00001005000c0359031480182004500e41c8503c844002c0c1c018140e044c441d28810112400c0540c89034402c07003c1d251144960108003103000000c1c0f034000005401c00c1420009100c590500e1703c40c0012480006e07090900b900182c1510001d074010780c1c141803042081c40c40c031803500110049c410a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 726492598 1250 726491348 726491399
    0x1c08060f040905070f050103060f0f0b030c0c1b010e090f0c0a090503070803040311010206150402163c0b04110102010608150f06010905130c03020f0a02010501140a 72
    0xd0108040740080070b4440700649207000b40c02021848600ca038a80b0310895100760303010b1101c00d8031016286146401403044e140d05005c800402c10802c6200d0002d59400311007000072600300180380381c0c914107104074101c07006801e00c0c2020901d5215030f0003607884010030340300380c800780001d02d40322125401c01d1101034031100b82c101010070f80e19100c0c1e200d00740010140c20064141d400d210390380c02000f03540380c01600003156100008020b140e0780b5440052664403941a4080c200c80042d4154203200003944a11101181603400744221004280134a5030251303103e80000081c1280c00d2840000040040200a40c0542d0030140c840c0710040741c170b07150800c3c1d0801d810510000754000d95500607030040c411036100e0541d50080e400780f528101210030041d449401400c00002d09903450354011900140c450152550015001c0350f24260085d207540301024020b0b1a003401480c10303144856118494003d4205140141e44610062011005002c98940940c10a40d590701030310341481002406074165054400900303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 726493848 1250 726492598 726492619
    0x105041503030e21070602070e1501020703032a0305070203011103010506090105180a0807030318051804030c0b0a09060b0f09070c0f06050412110f0706030b040e01050112051c0806 79
    0x100d07040d040001e0704130000300c00c83d44016a0781601944807407880c46455046541500060395810b201c18810004840c1640a80f0802d41107030b44c240d550100350708008017045650081601501c100140308034260f402903e80d503032038031158410107081d29051007004401c203506000400403030711140192481407509013041600d030794404060800080f0002d115903070140c2101000940000086903100a9a0083e0f9035580d41182190401090490500c5003039006071242c400042c9040e02240340d507401c140309140803c202d0302d20343c44d8440307408400e0700c4c1e8035241c3d0368a04100f02006100e215218020b001500c100540080c4500007841404006046d40b05000f10281c42c45c04100350840500c0b81d20368003003002c1000f0304050070b10144203003411003120085001609a041c0000000510070040c00401c00240010740c20400100d010740303010342006801130345820510308105820301035a8043d180405082c036280c203507810458507081c1d9489002d0074001005145a003030650080ca0103138000401d90704416034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 726495098 1250 726493848 726493879
    0x3010209030601320a1503180302070510170105100228140609060a0c0309020301020c010218061e030c070602130512010e061602150a050105041503030e 67
    0x180c422425a164540100400411014926124414014000ca00f150700320036880d14a494420045148607034080114281000384200508075000040d00a246c0030803081d05410170190b441030030010440258000c0c0c0c50612141c244000c08040d0350780720389040704420348180c2c12048070740c80601036035020301c0340081030603800d5000f0409001250510012140800301e950000b844992a280040301e9801078800124020f00c00000c130940036228400c050b140c41c0e2a00c009060003422041c0d41081455100c90040c80507030340c02c0c406004100802c20001d6a51940e18ad0245840105040001d10841f401d02c502d4449850b181d6250000c403262545d00d55aa8a8400c000b007085c0c010346800810860001800c8810440a130400c4402c517981034400c91024544440c001d07003030707034181c0c035201c4001d510000004a90300403400e00c07044810203500641c2e01e01e400c0428441c411070002c40d0443c49103a00c030790040180d400c00c2c1c0302c0c4090500341000c40c00301c0c0c01e045a5006121011940c0810310a90035001c65251 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 726496348 1250 726495098 726495101
    0x1109120102090a0605030402190810091713080c0a030f110607170c0d020316031b0b0c03150406050a060e040f020a02010c0e0a030302060606030711100203012102010801090b0301 78
    0x1d00000c052040f0726546480c018650303401260102c4c05152a41808481d031721005400f1002d031004d0a0103800d96a0514410000400c1c0008081d503281041000b040300010415000340303c4140b280071160741e134034204200340d40342c038141d07100150058001880c20008a03038110319030445154000040800384041c2030010320140102c601c0070744108000b540b48111812000700400d601c1c400142030b40c07000c0c18140c000740e0704d80c0201c0f1421a070708403104a13a140060b201d002805400c00082c440001c420066850b0a24102c0c0e0480f5a14482040002800b505000506000040400844e400d0001034208404034820481034814007041c40480708400341541c0d6a0380181c10458055842191a4030070745a0090190480a0100010500145012042d03040109001017030f02d4058008011503114882400071a900060806003001300c00700075a28196030501c440c01d181c0720a0040036861354180701406141c0c180741130000101205400c0e00b800140d801c4900541103400e03400f400a0300c40754050102c2d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 726497598 1250 726496348 726496357
    0x11090138121b3f06040e07031b0305120405030706030c02010e1f110f0403030804241e020a090b0c1510030308010e0906060f040e0a0c0e0a1109120102 66
    0xc25424010800a910004012490a65145600c240540c2003000c0152614900200d01403d1890100d440082c4441c01c16410100c400c44420044480c02c0e0b80d40c2d00d0342511083c0401d000ea603120880002002405010403801042003100e01d401441d2516080000c1d69801c00c500c078540a060710307800301c2034005000707501000307410203410f05442e502c121412044044083c405030054506280110b0901a8200c84007911075410b081c80101e4502421620240e400070001842114a5108030002080500400c0500c2c1c5030301c0e03c0c2120100340524640545003102e03541a12101d4442d1062110704e0091703030b00004400071a00840c04890f5144c0045049600b49050101140e480005400910409a11060104c01140d0095031200810303601d4940d04214134000340d174420501d901031004184540360414502c0c04400005100040410005500b08d0178504115410f44400c20300705000c100c24401244119130003c0301d0303941089415058900d00e0f415002d010b400d24000c031145074250705a8642541101e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 726498848 1250 726497598 726497641
    0x5010c142a0a031106150f0f031207150518060a0902030f010e0c041a090c03070306030c0306020304050f07061416211701060503070c1109013812 64
    0x140d6500b4010304000d003c546503402c0004461158400099150300c83c03031044151094020000c07243d40121404010005c000a003400b0b516008980000c1031465480004054141c410003508018980710400c1c1d200701da00040041c015004c0d9016402e815440102d40a580844c4150340000c2c8100300307001107807602c261222134000941c03238400c803c40e41c1900025001e81c590000c076030900c540ca0384180500d40307082600211927000b50038400411000000540690381c0b118407840c002070705039500e40300c0e40f84109840e801600c080d039002042c00280031042c086503d04141001c000c1a0103403a04030300074072024960107484605600400c4d46035081142ca5000454582c004041c64010300c58105000072070182c11460002080c03106207070715100c1841c00016070482c0e10b1601d44a00350760341d441040e990700e109610110740546040001882c29034441c0741035806041e1201c0c0060702001422b1840d0400032004110340b180d880d40409030041c6482c5a000c03150740404042c486240c64445400f03c0e5511880303d07104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 726500098 1250 726498848 726498853
    0xa0b010b1305040f02090f030a03230f21060a290f03070833010f020a0606030302012301030f02060f041205030304031409030a060b0303071502040305010c142a 70
    0xc1d80a00800d07a005810500341c211f4003414081d2000f0200b5644211031030004000c161b10100000d095017546071030300c000c202c0c404003036490503080101081407503000802c50003881c0b504199070219013881040700e45c0e02c00d4081d9940c01c0010b003480150104c180c8800c1b0100001d1111246034072800c113020742500c140e07072480400c1c42d0f140d0412600181019104413203013022441250104056008001c0e01c480e8142030410900c80d003021510011039414800c2c0d540c04042d031040c141b000000031000d12410700114083c0d030000032084c40d0101d14050891500d203a9003010000e42006002064141070141511503040b21495070b1030050b140d01d07280341c3c040c40d8008031b00c0d0441ca450030000d0050100003035204a100713540c0e181c1c6072202050300d20014010f9040164056020009650024550303600948080c075001b000c480c1015040d507240b07904a2a00b400c140c2c011900890304104000c0c0074000d0441201c0c0d01d040112400c5100b9444101c20300419a0b450810016541400b80401000a20700ca452070700703105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 726501348 1250 726500098 726500111
    0x7170c0d0b0603010e1218060c1507030b0102070609120201030902270a050f040b040c1e080c06120f060f1f0801090605030a0b0c19020f010507020a0b010b130504 71
    0x4007601d0070481216054065400d0040441c1682c0b0040364405a080100d840340d400c00700c003000201030071004294299003002c01000b079034088201c208003104130174a9001420300d2a140400f00181600d0100d115203040d940085010701110f60064414030540349040620441130010703000403030140c40d00500103500030350b502000c481c0c1d04603078602d2040c0c0c001c070420a43ea11620b07410151404c80da02210300f900110711100c0400d001483c4440d0b4541c02078050b885690200352180081c00429402c02104c6000d09084c020070010789030b0902c03101078051404c031342d018286005880840b6003a08020100c400d9114030030002071680d074803243e11104001018003071090000f6640000720f00380030100c64003000309840c01c0001807841c0160007400b00313580740540a41410f240303694032200c1e4108003409614412509004450a80407200f564a142c3d0410758018001520509911402c6800c050140000c54103c0c4282c500410201c5a440d070469150b500340c03a0791241040110307004802c1c1034101a511908120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 726502598 1250 726501348 726501353
    0x20703020303010e100f0506031305070f1409090c010818010207030905040b150f0703110d090e011d0403051c0501090221041703100b0c060711030c07170c0d 69
    0x166041e50050210306080307403503000071042026442d10407006e10400d001018006814041c02560300711032900d40300400a8072640d0340f10b0500d88540c216002e60403c0403c00c0181008010140100720029110600c9500f094409213807548400d03101141031040c00d10200740340c00e120105444075284010000c64440c0c2c0d152400030041c0040340b08040c421801c225400e005890700c00030386898002e4441481e850407800c01e95240c0f443c0c1011006400307202662120491082d800d201e600e0f02c0519594031030403407a06020b01c1005000060b000b20703034010400e0010051000b11890304541098050500380d40b91501c41aa02c0420403280c030318000140e0404000062195031a0081e10ae801200320301030400440056030804002c07001c8501070001d0746620300051403001540000c41d0031641050320400101d071900045035090f0f000090903091079000c030040bc0722099100a13000d19524464000d10316154602e001700b5a01c3c00385003d0baa103407400c84c0480500b03c01007000f0000e410036018015a0294440b0b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 726503848 1250 726502598 726502603
    0x120b0109060801020a09060e0a08120912160302130f020c0109051e060103080f0c0304032a060c170c01150807050105030f01120c0909060504061b0906030b0a0902070302 74
    0x2842034856460070304402148404040c000d03a29180c502e913842d011030f10300d0f00004680304903400b10210f420207003900d000326008805001c6030084010b005c1f03159941e03116404c188100645902200201d507013120240c610302c000b101d2111421a1b4040380c41228150241503984001c1040780611002c482c400550311200300d406401c00b503030f45130050b02910220041c82c1009c031116a4001d5801d03041e0303006038006100144004001c4c1c48500c036102209403d00380c04040082c076640c4650800c0d2689101c01240203082d440d2042c216040f00200295018003910f4964098040140703000000c200c401c4003010010203110190a80f600081e4440c024070141d50107281d9036010703480714041c0382900e014460020800394026004c4034000d90800c120036086138a4031100182400e012941240c0f2172020007030000d1400703550300880400700c0c0941c10001d05400c4ca4504502241c2030b102d03400c00c100c000c1c1c0751054070958200c020101101c84900f0045009402a0001820b840c0127070010200144040755042c01e05600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 726505098 1250 726503848 726503851
    0xd030201051602010c0e060708040f0605130803090915030f07141516030c06020c12120f07020d181806080d180b1602090a0c02010617100b0307120b 65
    0x58040b0007404106200702207090318a0100301c0e0000c9807064020701c48a080c00c4004001c42c80c0070b0551941416103c0f10081e02c1221142c1c8440009100410601c11605000302007800500d20600118504070700c2e200824141c40c0014050340044440c1d1100b4050340d1400e2000300c00402c001429a02821380780c030042d4006c401d0b4854400c0c0038070321081c4042c48580c0c00d44101c4280c040d5074503c00d40300300d0b601d80c1c0440e210000a1022900d840e006d01446100e8602003003414103a00a0009150711507985126202d01050000c180504030601070040c091440e40124200300b841401d0300e011120040403c204a40300d80b20b6a10000f10614030048007d1001055840342040d19600c03001c0c0c80010508140c2241c0000140b2094401c01c010150100301c9100b140707004111031b482c01c1c3c80e4404d11048a40016611203000c680c0507094507201c44040310141c0e1b080c421040a000080c420451244030012241e56030352200c0001d41c18950350310440400c03560100410001000f0f4001031030b8070f14502e0300e010007a0b00030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 726506348 1250 726505098 726505111
    0x105070606270203041e0213050703050a110a120e03070b04060504020306060907080613060510020109111e04020304030e130212100308180a0f23061c020f090d03020105 74
    0x38a4060002c4506008490207075802c0258103400d0004485c2011400603980d00c22640b00320346003000180d504980c082d06101c1d44150f1800a01480d0840c0101d0950741c1004c000380400704100810681241c0000c007a40c034011000750009041050341c0b80c40351551181040280c0311040c01d1040100b000030b16041342c0d205510035001d0380c030355403580004e0200c9200191401004118004002040ca040c8085006014040c2e03c00120700f0a41e51070101d54040c080f40c0d91a40140d442d02c0026083c41025196030009000c20740f07070710803864101c0c5070029240380703604189445640c00002007010b00d88602030840e41904c009001c003911002814440d802540b05441002c1c0d0f0416a0740000e02c58800c103909141244e41000d0304500c0e005045010003010083e070031400b50300c442000800701395441d00c0400000941900d2190700251344400607155900305054544a1240c001000305040003240c1400e51500e095410b04096100c54000031000c1d080d0260380c40b042e42100448010405040e8150007040c010078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 726507598 1250 726506348 726506399
    0xd200a0503030d1d0c130c05070b09060a14070903020d1b12051203061f021213030c0806160f0215100504050a1b0c1502040b09090a0e15060105070606 66
    0x2132a5480312134903445011141035005400d5401a5005c5e002c0f038010b980c1b09941443c10381c4c030300611903507080d00905050b25000d6059000c001000110b800900c16120003c2481d85066201d10f0617201c000c0007120140070081c01250320030100010002c08a0f0810f201c0c101184000034213680310000f01036054500c0005580500c640c06907001452600c204403030040f0b60141080a0f42e0303410411aa4800140114800840c45000d80f01e11001081d50050f0100d0f140951906600350300e5030816001c400c10f180c2050308190851028400010007022034058440c400c2d0078030382c180c6422a801607007001d0040d4801803900140904111410183c0350441060b102d00315010081d80e1541c030804c07400c03210f5044034125041e4107201800e801034000e8483c1c0c0c081c2d6200b00c002c0964060030048000036a0055032200e00310000c040356800c00351604080c21a404107a001003082220070000d42650348000c2c50341034402020f409404140540d1180303045903842d581200062003c1903440e28400386801030303080c5220109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 726508848 1250 726507598 726507641
    0x901110d02060402100c03090306050c0915090301060509102c0115030c030b13050a0b03030d020a090b0c070b0a0e120a110a0b0712260709050d200a0503030d 69
    0xea0080e1b0b000e40200d501580c65070607907401e60f652107000b00b80150444820400500103080d00c0d644203015038010841a0103c1c584800101e03040c1404d640594001920030481a000c00c0342c0e210b40c4a030250100c1d800234041d800405140200c40003540e84040e800000703035040400115078803030b45000c68038400d869940e00b004000380c8202c044044032403a2a110390300c59042100060400b000741c0000b038200d055600f00250031124440028a10b502140e0b0060403241c010070607440c4640c006105030010502d00b50020b182514112415071242c400e070040d811540404150a650603100788220565a42c020b4500728000885da4602c55031040c00f0502251142182403410201d41400f118001c2240e42440c0c1050500205940b051411420360300c5110030402c6004600d43c0b103089290000d40a28000500e5079058202203400070f001800c0340e004180100d007035000020000d4076600751842c481c0c1800c00c034a1180c06a210020718446000c0e4802a8180710115078400c0c1126143e1116810240c0031600500c103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 726510098 1250 726508848 726508879
    0x302041a03163204090903030b030c04050603030318070e0403030203190b060702060d02130308040e01060c030504090e0f0f030408011d280c0611060a150b0901110d02060402 76
    0x250600c01c03c880207868140e00c9088800325507040e0884100c2c90070f0f143d003401d03244c680e0601151028141030740000d440d20740500a60405014440c441349040c0e5081c4598034181d404655a444007034041d80283d10b400910040100d4180b240340003802c0c25819141090600e0b080080107500255021500035108400d00800d01c08203109005100b030b0054426401d00d03000d5020003020b44c02c00f400500c000d540821505101c407000d102c042c0003452080700070a84490070542031000d03408050304500d050000610403540425081415a000c071952400d010551040c118140c50501078400f1842140744103410701d0700ca070388801101410030703180000020804600042c0c9102c000074030f07141c107071301c81900f00002442c802d608640c4006078003081c049060081710b030140c0da090110441035002400064100c51002c1d0149024801e254006d40d80c044180700d40580c904000080c15803510aa041c2c200e40000e03200c9040e409582d450b2040c010500c241c556003d800100a034445030f044070200c2c420385290003580344 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 726511348 1250 726510098 726510107
    0xa0c0e030c1003021c020301080a1202060c040b030601050702031606030e06060d03030e071509180203061503180f06010e0c12060f012010151211010302041a0316 71
    0x4a90740090020b00d14a01c40a0154001c1d03200c0e50030500c02c801005031026900341030b40000e50090198000909040385242416000c8900c140b5103c0110741004041c0207080c0104000e441c290380c04031200c5a0b5a40302c120058130240b14501c07009400d409515889421801030800190440c0d1a50b14144050904e50f0421511000101c507016808010302e200e0802282c0309500031440900854105d6103910349840d003404055209060000019401310030901500343c1d10360740000c071010880c0c029811400c210001550300c003882840c0720444940030000900214a81c1045450700c140f00f4240c2d620314001207070060312030400f40103030130a8044140101c0e10380c5205200301c80c3c0103405041e01c00170f55164401040b440c01c003204082410010400c5007500000c1700c1c0440c442005810301c00824050390221071000a0700c2e80d0b815084403460a0800811941c034000c1c4038850381c1e41c0d0121904481404000068000b4040c40e000220b1407550f8260744886020b41c6401540111407954074042c0d8035900d1042110b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 726512598 1250 726511348 726511363
    0xa1506050702031b01020a02030f010218040c1710211208060303030117031201080c1201060812030a020708040f03060e0a0c03031b060f021305030a080a180803030a0c0e03 75
    0xc3d003660000c4445a20601c1c1e258080ea04500144181d40c003440150300040c0c642030406183c12503c1e54001606400c002e000c0c4c0403040100030503a02841090301080024182402207003d9102d0714120300300080c544220300039044081c0003507001401424018042d58048468851030031200e4540c950f8500b0070690042c030301d4900c5584014011880c6a082c0595109900708082ea072090314030044c016025200800400d4601a046280040c0f6031000f00c58200080301d82c41c10b44901e50b0380d140c100140050f84001c2060031002d02c01100482e605c0e12441030b108003d02c210718019181580108001c0f41c060030310031030802200d004081c02d000030344568401c2038603800c19010003840380320f00e4082003001a000d500a5003110800a015000f403243d0b40e11454140c4854180c100c40c0940c1c009140c090b07074500e5140d00d2016240640042690074038030341e1420744034420040c0d40301c140a8040000d50341c0906042100000c1c00e451005d03281c907400e00b0100d00300540361112000000c2481020f20620a040009008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 726513848 1250 726512598 726512603
    0x809010b060316030f091103010b12061f1805091213060c0f060e010b0109170606060c0304030c030503030f062403070c06061d0c0c120d060503060a15060507 69
    0x1851500c80c03180b04083d600106a0315028584c45101d440c00030a480e01c0349105d101e004200101441c6004020142182c2000340034521841c8400800d581e1010300155041c0c1c01090103420254101c3c00d041960090440b0b903010508242d01421a0703c0703181290340103240640c1d99003003100c01d9502c042c003507032046001e000d00010038074010300d108010f0f00f880381c203481401500a2440504140d00780d01c606c1e0a0310704800520240c3e03911000c2800c51964000c90380e9004004280010000c41c5038294283c1d25060054070082c403410010940e070088005c2442114002c503031200035040500d43d2464059120b0b041101c00706a1000550001009420242000c5036042c0c1d8603103850030410b03001d8444645581010b000c1c04100128088104005243e07880340c9000f520403140b5842c00e403c28603403d0b8800303c6000b01050580e890a000c6010b007184001035005800041c025140c0d01c41c2c0780303c145c5034010003191f84025450b00c540c1c400c0c041c01d401d00340e002e224034030011000384800f1a00c1e448140c1c0c55200e1000e00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 726515098 1250 726513848 726513859
    0x11503030c150b04090605010f0506090904290702010b09010b120a050a112b0b0d080d2a09060806031e01060f061e2a1b0b09010809010b 60
    0x9000004203041d1202c10039500348007000808079240c2c40824211181740000b1901155150014806140c070b882201c0000c280864080e850074019401280c203482e80508000c001d2890103a0000c6541a020703400b8019050203181c045142c43c082000070302a00c07518811f40c0c02002501c0000c9040a51142114a00d8108810004082d1601d2a1080003810002c0014810682e10680e281c0207201c0e4000500072421024250300800032584075483c4c0000311040181409440c00c0e0000e21151200c10201180c16000004140c4468560a80201401000c2900c01d41c6480d2042e280700d00e82d0000c0c101c00d4403030400b6070340c0c0d400035600c85c0c0c0d082e00c8007401030368020350590060050600c1985a0015000c802d010200007260036540d07201224020051074004d0130100c1c2d00400c0b4014084030790064540f0346407941ca003144424040304803440c800031085801ca0f007141c40301010f18041c0700190282c189104285c5541e141e14542c2d9002d14055904079800f013500041c8010040303103884005002d840e003003e000400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 726516348 1250 726515098 726515117
    0x3010e0103140a02060a0203090316030b0403081b0a0f080f22020a050402070803061305070503070c06091703100603060506090f01110604261612020a0804090603030201150303 77
    0x4440b200110030070703500010362282c2410710300140c484801a08003c0601d4000319182d074411402c240c03c104442103410344012081d130080000c81c5a043c4d5050b0003d07014180341c0d43c19110305542040001d4000d00384d900e9403100184000647e9400071003200000c0e1140c0c3c41c110580ca8100100c03044100035985159400c01401030881340c00700209856410700d20007000c0c10001c580e6400803600340d070040d1500303454032003021080109a040101e038102c105001c00302c0030002442e10f41d001034440e00000d000c1c5010000112000420400140d002c2c140c4d1704d800c4038103020382e500f4482e004e0101e64030032030b0a40340300c03c5201000a41940203019040a03a41c0003071020b410800c2c004140300500b808442e4080c100103061a52014030345040c441c07180107138082c2d902d40c17507910410726048004c003aa0088059040c0d03420008104429052241e1040461744200240d044c046204070486c9009043d10b4042c00c0d0050000b000505c014071580810308482c442d40003400003140300745c400705400002c0d10016003c50071000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 726517598 1250 726516348 726516353
    0x41a0d02040b010e120309121606030f0209040e0604021f020c2709060a0b0d02090a09170d050603100603020901031401020f0c0a050601090c120f0b0301050709140603010e0103 77
    0x1000700c140100185019104101c100d00000d117005003a4882000e5038100145031075a0b0308040946010001c1941c0091210309160091840b040d60f452049004061356800307100e050403910f0301203508150000f4004e01281004c1c01c942c580f2803100340c2c4c00300d1141d0b02c0034014110000a03041d50481e20242c54010344100402102400050b200010144070104003815914280e064404502d600400201c0010b09503460658814800c4030440c02e01207104400304c6c282000140e40c0e40c2d0005a000100e000c0c045080748080c682140c01d109080100b0070b041d5004508020116042e03403009100d03100440072210640c0d00010f00004440043c000690001400c500500c0842c05552900404c4030462000524207956101c01c0b095503003000039030030625049204500c081c0a82041030502502208600700892421424040c00010711080c5003e1410b40310101d1001201095000724800c01d806802030041e4500044c00808d60a03250086007003001d604a8142c0c0396050040607a410f031a100d03a84915031fa42182c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 726518848 1250 726517598 726517601
    0x40501141c05010c0206150a030816020a03050105090d090504060f170304081e0105070201050105090a2325020c0303030408220f090e01290612010e06041a0d0204 71
    0x3241d008030040d00c610080c000140342441a2801c500e0a03501500c81410620701c0314150f0010f56281a00c038107200802400841c1200040341c840010100443c2d510300803d02c0805d1100c141644054025441c09080200084010030442c01340d000f240d0f19038040302e8503070040100b243c4007409041c6140801c40e40a2262000b080514200345030b140b01201d00b031958400c65949003031071403c94141d01e04c50031010643c7c3c400e0240501a00400e141c0002c0c00550f041402190070710300014081900707252228205076000c071410a020b9403c00c160041140070b45014850310829102c2c50795413541403e0024a0010317480e2002c140c108025400801845c5561960744a6002d0b03604001840191059001040358038001d52820503402000e20f03881c25a50175152144c0b00c801c60718150030501443e41009441c10f2940200385101c2c1c41501404039001d900c558410105080380a00415880705844190001c0366217488101c08a04c102402c840501a02802800d1210010881303180250445c1000340343c02d005203800e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 726520098 1250 726518848 726518869
    0x521070906080f012a170702150604050610050a091e2619140f010911040608072c0103061b050f1c021905070b070203040510050a0e0a081b04050114 65
    0x146d20380100d0b490030342c481c005010b410545141c1c025074001026440043e50303500e04140d10a000302d4007007145142900100300708850304034039801040f200180c5864240d0142030590b020f4030740c2d60071078a1030100c030003000000c42403d80510026004042c1880c050119a00e05505038001035402030702452929081c49404980c44403421148510303500c1c002615650300300a100c2c400104000041042001800e06220180b4401c020b04e00440c1044000c0c07100c21030004100c3d0403180503410703151001d1040140c140703c010501036400403411162000009004003500140201c0c1ea41c060410756448407900180d525104400d0baa00f0016410300c90074000912000c42c441b260980f58101516000284486803840c00712105640c0c0803450204c2c02d9803c0c050300e0142d15078400c43d20f000071342c03416080c040003a00c480d4500340c1030380410900158a030a680c0c1b14910086801d24050b04166809488803c4c1c1c1e03031550510f042d41b90441c5000d107100301c818500390241d00c0c102c0c0c2004d4032580c00810b08005001d800c044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 726521348 1250 726520098 726520181
    0x3160f0b0a12090506040215041a0d090c06082508221b17070e041b0510050c060601021f241e1205070521070906080f01 53
    0x580800d54050188902070b0402840c4201c010317003050320f481c2c410440c216a55071011308030640305000034844440915070600120b016404150789a40c01c1110f140081e00407554005c102440561001481c0b9070007604d424020305141c0b0001c8120410889012816500d948807c00019040d4011400c1040c0e40e048245011401e859800000c1c00242c5446e450805444600707100d40d04072034070030400b83c0003940d1507a0b1020100405030240500c2c0880440a1420181014003c04000c110f03c0448010b030900c1c20000b080081c0103e90a13015100c409425508052580c04c2103001e0032001841540c80070071340160001c0403940c2821891115140d4800071700214110b003081480d620768036540010300940d044024000c007407000c90084141404040300e40c1d040d500170761450008617480c40000d580420302d41c050710400d5914104100d091000d40701c041d50580c0d03000b5428000c0c21070119080c80c09800401c156001101221700c10030304060564200d40ba0701000c07503103070140715010321000141410501d04510 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 726522598 1250 726521348 726521357
    0x305040f02122b0f0215010504022b0515120a03030f021e070501060812030109150302091812120a0b210106051519030506120102040906030203160f0b0a 67
    0x40b01034070030010f980c124a581200240e050304403469800d0303010031200c032501d010b440070f00280da030721100703242d10401e060042e20704c1507401284030000321104c102d05520001610342611040d96440e950900141003ea840020790340494440408030f0a1100981c100c003101070008042c107090f070740c90490040070644c038480f140c16020800c92001f0b002100309101d081d03070151845980c0d03040318542182195110303480301301c480d044050480044c200c0034040d28112044083c0224890f112480e1012203002c49030002980285401c0a100540741e4841d0301075840d02090702110005511018000704601401640807060010b010020f200e400c60350700050034044014215908004d030280100c00d03030044004010b06580e649903c100518600154111041c401a103010f0785081c000d000081c0400e468201420145920f90012442a0f00c9010340d100308030542c2d10085448079210362400000c0d00c030900c400da20074070900307402c8540b8050002c60306080300e541c000074015513803628100702c4c02038004007481c00501 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 726523848 1250 726522598 726522613
    0x312060a1d01080708010e031611100518120a030e1215070f031104050d050c091311030d08130813030b0603010c18060c0f050a0f020306070305040f0212 67
    0x400c1e06000328041c02091000202543c1000d5400c0d25000a82d400112180e041020f510500c0b00d0204c200d4130411030719591250071032280c0c18481050f41030311303000e10341080134420424021903020014110070303814034800d0460707202c1034020440ea50810310440c2c00b50360400040f0800080c00354248440c2e1aa02800701c0005a104c00c51840c00c1c54180f950707141c140c40c690800c00c505143e021070142558902e03804d040101864614100000c0e0089019050003404000540741c140721003000100904a0014034510700c038a0130341044040e505854900b12207100c1c0e040a070355414035011070050501022039490800d2582c0f07551136144800c10148003910003440c00c01c801d4484120180b400c90103140203801080581c20300d50145400c49075034203046010050030114008081000c05000030032140e1501d481407a01000c7e041c001140511558000d12511480010030100700c903e50351070325114021026140e0540d030346441542500c0c82194004c2003050810007080040c901103c83c0c882c1a101c1c0c00444503103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 726525098 1250 726523848 726523859
    0xa0b06040e0c1e090109060635090c03070f050f0f060c03030907050109140a17030f04122d2d0308011415040b031e01060302030103061d0312060a 64
    0x4525010030640310843c03c110030004070303080690440b4010421910708000b902c0c41c1440060001542e544c104952865203040e1003040100b401044101c001e4201c0c1c0d50140c0c1c00d0021040740e403140f503a00c03500c0c000e00501100085810302000c9000480c0e20140105500f0360300001000600d616904e0010b03030200007481445100f11081025500c2213014900501e070320f034213040c00900300600c55445001c1410030f202c0007840c182caa00618000300e4500685050b200e100301d118072819401076403905040c0110106000544403225421982c882d40200c1503001058080000f0340da1201003d904042c2c051a550120300014840b0f54440030b480d044401c88640c06102c50350241080c00b04042c0a60010f00c002c0f0041c880c01803d4403610401c03440071500c400205021001607270440c004c900c01d940303901c2c001100007406803541c00384280340c2c0700da0494803400b02d60310343c40d001d40203400a000a03201c4c54034001220618400441070301c2c84408240004505200e400b2034003c00c01d40005011a07002603107090001413 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 726526348 1250 726525098 726525109
    0x608070608061302070213050402010e130911040203010602070b0703090e0a0c020138030c0d031d01210c030b030706030c140a080f0c0f030112140a0b06040e0c 70
    0x54046a60307144a242400c01c1005440c115850300c403005039204001881c0140d4800d525082d0040c02001c002c40e00396514001a24907004c07420140d42c1002035a144008a040e280d4400c6015600c14404101d0b40511003052000300e002c02d000b0040036a01011302480009901409042d00d54440e01e13203c51525110b101c4a1125142564040406510b07800c84e924015028003820190214040402d0012810000d5452500040f0700c1d405501071003441c443d602548060024620b0f524002e00140c800348180c2c64018a800c2c4003002110010200b500761224543c412200c02181c0d84401402c0c336002120000000003c1485023014820716075612a21281500c05024590060500d0307100011604c03070010b009807840800c1c1c90f44a0300302004100100241c0d800503009600700101105041c1c40d80e8980c10b20402c0d6104404e01d1072900b50022000082101c4143c10a120203440b070302c203951904615040c410b0741d5410790301005001040d40340c0014881d08240d8440306d203898001d011135240c0c51086003c200d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 726527598 1250 726526348 726526363
    0xd0207080702100e060405120304080a03090509180304030b15120601080c06030610050a050d0501030501050117010509120a020a0b0a0c0314040b0a090f322e0608 71
    0x1a10300c88041140d90035450000000070700d140da641010301d0080000b800284e014842c0e07008017486568500981d1182c00010810f403005020040102d620b036140074100600b140080d442250310507180313400051a8840402040355103826500001d600302415980c0b0a80151401085007407100078004130b030074096071215030b85020081d908000e00050b506140301c0b036087c60f580c980120300500b03080042c4140380d02c5600450455060750b00c0c040ba01e60306406e00440c0c151082d0b0315803006150804002105000701940100e04036550030203220b62089480f030810342a00c00858060006400c08081095102d4005000349085d54480c815118911542d80d52a4030b40f00042c0c499990b406e41d02c4030041e03c3c00d60103108482429000900e1120249451798440949000c0144400c40300c5864000d42420050040380b5200c0059111558030107111540034540d003c0400074140c1100d042801000c1c80360312002055610b488241c00c89541d104404410310341c0032183ca8a00343c00c007065620340002525000034850303c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 726528848 1250 726527598 726527603
    0x6053709021807080109150e090304030b180c0d050307060b0f04020708030f060d023a0807030e0901150c05030f220801050f040209091e030c0609060106020a0f0501020d0207 76
    0x2040b0301d00385010010141d510582007010b007103140c03c0035001815291811368040b50304100341072a05599158a690a60085520040621105c2c20610807808c2c3d4840c05813240c42c80d000700308c0d00c0d12030200c010000405924880070b80ba1b80c20400c00b24001c81c800d5001011107500281c43c80c1a00c5400502007000c07a0311500741620305130004010300c0415074064010300d401080c11680001104059000118010000d10268442044004840031070b4413104804441002d080258146012414180104c0c03941c403902040f8000750104921030064501404c095040e181080311400803070031820300541d010042c1c14803d4505210034414010b481500c603000301601240415200700c00c0405814044421000d604004041d9041800700500d0500c1b22481640c002d030100e0740e800140d12003980c030505001e4250400c402140401898203003480002000700400419401101e0a0f50f8071401c546403100c1080c080c0c90016040710b50307981c0206403221b003544481405080010301d003218140b0303a103049070300a0404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 726530098 1250 726528848 726528889
    0x10b0a0908031303110306060102070b1308010903090e0a050108060a0c021e011407080403020c040b040b10230301050603060108041e050606130212071b020406120605370902 76
    0x500170002d6264480d080008150b000f0802e074203006001035114100ca00902046031030104100342c240c1002c02c100002422440005c01c1000c040f030034001c0100d82c00c0c1c00303442d81c2140340c07502080d901320691103598103c1d50108041e003015245c0380000303805482600310700c00031403181c8881c0804c100c1c0f088589401c0550050000200e8040100c10507000c20801008013040c0f081c00310410010030b40100b5001d007040d20403100018031800120015000f00309084080f9001100c04841c0213901c1e4020a61140010007100b0f0321807410305e07e801c00d0702c0c244024000c241e008502800880d205500902c6982e402070300c1038104c02040c21051584c034007000440d45003135032198001c02c140100e03030034492041d4503800202d00c0d00b9440d001885050118050003c1c003100c081145040012016030b02d00b40d000441198000c0003407021650340d4080055840d84030300107031442c600d001c0103e4400c62074000b0050000818421711480820503448138000010f10140c142540c0e0346030392901c0f00503a034611034000020541480c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 726531348 1250 726530098 726530137
    0x206074508120f0301060804171207030e0a170306010302040803030a0920010206040f0311010f020403021e09010308090607210305010807060207030f0c0b040323070509010b0a090803 80
    0x1c042c0381101655026200c072804205014445400b0390881c0e05450050801d080360740c560b4500200c016074080c0501403849804160984003424007036101d409801544c0c0c040c00f41c2d401d008441c6444099062000b42080c0da0740d085220400200001380d58000c1c0c05040060816560384200e07410760340304562100d50701e56182e1902007040041004090030072034000b50200a03c54402c000f070354503040604080c1c60710300c9144100c41010301c0780883c082c0841c0d11034000d100e410302100e03020000c0d400502040b403290a0b03e0540810480005000406416000381041416407035500ca83c48550704c40004160048420484030020400d1502507130441100030500c009061b641000c001c0c02c0311010b0f00012807941000004009440c2d000850200340c82c0c00c081e01c900c09940c0e07850b01d8000b143c0d036036020300181c05000c82c00000340b15900301030688031101100080c010083c0b00300310310303115505400741d0350388150090014400107010350050b00100440e4106580742c1a01c5220700342c5542c018507000c0f5074190300103a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 726532598 1250 726531348 726531359
    0x109030f090f0b0a080628030b0a1505011218030c140601030521040f0e090d090509040809010507020d14070909121112120f0702060745 60
    0x107400310002c1000302039122160b4108124603110b0b1054070049070401802c1030115040742d580c000d41c41030004181c5403000d00004949600c0305030f81c60500c001e0724204400400581844000d0280c24690400c40c46544401800c10700199011500740c898500f14554940b07140c07041040c55080ea04955000b134a500121466501c0c00a03070000d43c01c180400f0303d0300701c03100403c00030b00c0004480100360881c108042100b00400740200250280f580500000c91500e04000345000e90300400c0740c00360701c4036402d481e40c1e0f40d060710051ba40c10320386109954100700058001400700c0d0a0802505000c40f051414614015a80c2c000541a011054003515496040f02e40b04011707100c1000008024640d00d0301c00d0081020b1516407041320340100c8070310f6082c1700c90320501c40f280d02030034408a81c1080c0b09980d400d4807683d42d0301a075080000d0882d00c0c461028200c00100e0a000d0000403280e01c83c4907683d64810205002d00c65050865070f40d040d03101c900e0405080c0c6000c5800781f80d00b20403051104c0c82e50420a491524 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 726533848 1250 726532598 726532607
    0x8010e100f0e0606040209120102070f110105180907141306030606030603050c060d2d060609080c040f02041a07051002030103151e0f05070801051504260109030f 71
    0xc0c1c0041d0301852810031040000e420110305607902c540100d0303006031102190b001041e0841283c4018050395440051418100310401f080340c001a40a41c4003031050301482c2c1c0040d5070b1485420f0341c0c1c5410060381405002245000c81086034014441d143c50700301d80d400f40103d58540e4200c280c5015034440302c0c3c2e074180015581b5205950040100d46002c0c005189035460303068039459034201145c05227400149803036561031250001e200901e03a6050b00342c41255000345001d104007031606000c071020305000c0d000603428880c85110342580e1185000d0925032214a0412004106411000940c01d0b000e200000e075822003c2d919100004651820399aa4125860400e043c02d5800c5d224500c0e00c0d01c18801030010440580080c0740d00d007402c6c0380001e10008075901401c19043c65a01c1c04a02600300034020400302e1854003c40c1c0107070384075116000242d03212010018489440301c0f142001c00000d020030445030b50f40c4005951020f403050b280120f1299080304c61400d403100c00100b50089200042d0640304c0c584e10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 726535098 1250 726533848 726533861
    0xf1f1b03170c03220c0f030b0114040b0f040e0c040e030a0206100f152703120806090c090409021201020310090612060e01180c0512010902210708010e10 67
    0x504084078a5441c04600d048000400c50b4500000480f444410302c081044017103c600103807207900b0750030b020280d891614a109103400d009007078803143c0940c1c0441042c1818040c48244a80040c11001580c0303003002444014000512035161038821144812565111840390000004001c0003460717a036201813030081d243c180d0241101b0100c0044281c204480359840301c1c018152013407030070348090070300e40c00c4021075030034500100054501c1891409286101c0350f0041c1d04c0c045030b01c14001d02d81340a400c0ea20130384059104480742c50708010a0030014140b400070800524102c0c400410000e60510282c000c11410081400d200d425031394004140070001e641a100500280400311052001e0303400d018400045050206006100585a00401c00802c40c207400191090340c0c01c00c1c46090a092a06041101390414404d0728014035210010b4032a04406005180740260058113410200001c030040721f03a0740804102c103018501070042d0201b21518280111640d200c0d03081c00030031a00c00811070b11003c440a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 726536348 1250 726535098 726535111
    0x2240306041112130804180b01030e1f0b03120414010201050f070c02151215100315050d0503090603090f060c0a02100c051b01090b060f1f1b0317 64
    0x500140340c0c00f440410f0031a0380401c06900305000102146040c00b018025a00050088000303400c0c4400c28004580c400c0e40d5030b030000da805001e1500080b05903034403030910302860301c200540d000703800408003240d412030032407410050b048940140d2608860510390b04284c000240b810000e010303d100035a8240609500514400ba0b001107038206400081c05401040300004d000f621340b603d008603003016800541c0da4000c5580c4c2c0700c541b00d140c0b170681c01c80c009540a102c98407510350024034458540c420320a080d80c010740c22492550075800d00d0b0030030440117603801c8101c505110800ca140281c1c3c90b0306010b075001d030a01c40000c00700108a841058209200201007481c80442800b1701103009600281a0380302d0340d0081000280400c08900840341c622500b021126a040d680ba44c00b2242201580710507034040c0162190407158407405d0800c901d0304824540c055102549800c010b00308101303d100c451222283d420300c040c10034007d91010350b10074100002900412f1201c01007500c2d000c3c4051200f58440d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 726537598 1250 726536348 726536381
    0xc3507050402181201050c041404060909050307030906020118080f041a0309010b042c01060e0106020d030e010b060f0a0315030b061c02030d20060c040f0f080601030f0224030604 78
    0x190910442c5000d0003a0300c182d40902014054527181a02c0ea0381c030601c007a0404010502503100181040c070303503070b134049001140010300d5031100244a920603c514040d4420242c01e42001d11403d80f1384481c290021030300340007110170403c0000341010fa1014600e03082103400415644900d080c04445013100c80020300180074504100a2031116001c4009856880e8281098420810b07078207540b0728014440760b04404a641044400400d41c1900014504500000c981d801d0003a03440303140c20075007601c0307003200040c0c1c0044062001c1d8181284000c0a8000ca04081c600002e410002c070400c40d4031404140c1c000c0d11190f40b0202407190303504061a42ca04254a8405520721250642e4046550340790a4844107003080a202070301c4101001000c59254102c82a508503010303410b0031046007a10360702a105401d019800c540f00001e83c0c0001941d00802c8410700f01c080c6c01e80e40c0c690780307a491000e411058100d03400b040748494a10b0503202280c130042d250070041c6080ea128a40801400211502140d40900d1231 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 726538848 1250 726537598 726537601
    0xf0303010f06050c0a15020d150b0d09150c0c020f01050307080402040b0f1528120c11030d0b2112070203150a05040c350705040218120105 61
    0x480c01201c100044452602e800c994400b2407501490801c03628600092607150100f124044104041d0040c101c80303100ea4030104280105032080c46080c2c1c1c0507103d02c0a88030014401004c40700038681c480341d002409940000c4010440803e00d200b01c0390070801050104011160203803d40c108401c05481108003820000e20f98104000040c0102030002c0000748201d80390200c1e001c054981524008510b0005040100002c80e214500041604240324520406100c030581308510481d018800410321078a85420081c1170203407413090301514040381d03510244482c90310101c440f040d080004003800896401c0c0058020b07001810000c01001a5248003020304511011040c10030000c034500841e4801c00540700d0343c0700b00510200e81400c0740c0c00300f056000310b0040c08100544855820840c0301d10700c1b5110100c001600c540f0b2105000c05944040100c0800324105182c465200403c90030490000d0400c60f40c407a1303507844c00602a40d010641d804484220100f08080600f03201c0075025818070341c076000f40075a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 726540098 1250 726538848 726538859
    0xf03040e0c04050f1002120f19020a170703021501030503130905090d2a1b06050a090e0907050301050a06140a0303230d020301030b1609080d050706020c07060f020f030301 75
    0x1101300d00b0000c03522441d00210226181d074003c10030a801800182d00c1151a80e20400e0700344090b4000140040070708064007100c400482c070126690310300560001c1c1c04000d1411b8240c5101482d00b200400301c0079445461480d444802c2c480d500725000314401c40045540d00540c150790700c0840c800d039100d225410f003044240a0500001301e02e41354403241500d13006803044a40e03140074940382001e16209145000ca46441d130244250103003460091824604100c0c00da6a9580080f103c034810a10a0f00001e001e010082c09450000840150441400c07811a04440e0303d400000782141c10031303030308031944d190750740020000d41d85503010401c4825821601508554699100034000c622a42c0c208031044080442d02e805c61840a4181c6040c5261001c00310f45940e100d16000f04a21410b8030003100000b00080742c4541284544441015520044007414001d03001c2d003030a65054011000032a0442d8080c000243c051600304504402071aa558562a502c006420003038100340c00c04a00402c0c681007000140603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 726541348 1250 726540098 726540109
    0x409050c092403061002011d071e060e0d03020f010c1e0c02060d0c1101020c06070909020c070515371403190e060a050a050105030a020306040204110702030f03040e0c0405 75
    0x144070f60241e8502178005020301003280104000341059000c68900d8039040300f05a800200030040d1850740c81c13000c8108a40c8810f04400e40b40328810500064007100d440340060034482c6031001e4040c0300340110703100045ea00003101d0039903044100f0711002854058500342c1000c9020f13a0081041c005013081e9044205c0e50300421400e100740c4901104030754407100c1e070003070b010300c6620003441c5800070030001c64803007291501c000d07102c400c159080c02c00a04080302c0461078800e02d02c200c640c2c1c1c408130b0004140741450034041c0400390b01030382840e0001241c00d01c002080d000d140000a6034400c00c40c0c12416108541e04100e82c001c0504642c19010442404801c3d081a6807100849030442e9400011915064503d4a640050a20300c3d8209440380180030900242c15902d0304070038040c0f5115041071100e41c1e2180d003071650312040248040d6060b40994080b8001d42004d520854055092120f114500261a0003007440d1200082100c5055070000408003c00408100d00d190480c000545603803810346044005031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 726542598 1250 726541348 726541351
    0x315121b0f030528081b0c060f1803030d0e0303160c050d08041509060e060912040e04020a0e040804090b041a01050904150909022103041a0409050c092403 68
    0x600d5041c900c03600821413029405484603150b0040c0380a40d83c00d118134256402d1020b14007491002e200740608520145068070a0758010031106840c0d074100b64041c410080c0a0000c1000c41e9018081048547c409000c00c5c000c0c4405501450003c550340e0410b0540240042d20040480c8200910120000001040422650101200c80c500000c540c5c80380d0405071040e104510031030700da084c0741441c003004104542d041400445101d506940007595003840550700d0360380300c240c0010020303c1000b0521a1141c040d00d510303001070020301030041c51503c3d1256101000f44c19182a2000311001c00c041240880030701809000a130f0960302480050000440101c1b00464030803490b050050229150800d5100c82e4030806044580c0300d00c2841c041c0d55151850014404004246c1c020030007560350030308204201c1020728805039020000e518151900140425800362641484186001000f0005105030207028070340c080c1c00302076a8590b4031b0a07c0c008000c544000212262607018101c0c42a489482101c0d013607a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 726543848 1250 726542598 726542623
    0xf1f09030c021002070504020d1b020f0304060f051c06260709020c0a060c030b01120e1209031204150e0d0201021f02070203150106031401080d0315121b0f0305 70
    0x2000b0f81424140b0503424842c06411058201e4404036840b20042d032140c11411700402c00a0300605c005031325600c103e848510900c900071250744100010008503224030640340f1004028a011400e0202074003074242c0e4076107821290000d50744c03100810300c000700e4001f0b50340f10804802081d0000d5001d500d070405813a52114403801021503401708181d030b52004240321814030140e11082c108143c94155002030021700c000c0d18250300054805103600748880461242c200400c411100812aa0701000301103080b0303503c10303140642c03d80600442c9008103400000500003600001d0000c540c40d40010000600180c11100d0030752040c0152020000940d8011607107101d0220034440440b05044040005c80192203601c10080d0541704030101d683d403643e40983d0f144c0c183c420b166020300034110704420b140b2a9010a0090510a07044103d900b12510700a620031040380c0d03003005040e41d00c0c6a0303407040f420414132130b00744c01d540d21307100d054401d08a0001d407a03000018004000055014a0a5840381e03591100d082c80c070b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 726545098 1250 726543848 726543859
    0x501020a120c0204091a090d030213140607050a060c1d0f09150a08030c01140601020615040f020c0109031806090905130c08030a0e09010321110f1f09030c02 69
    0x300941d00d49401410905030030002e001100c000200c9001b010750030441e5074160318000d03c441c0f01490762190003200c680f50401d21012460504003074080f4008001135011700d50025041103c40d00149050001e0341d6500c0c0104800a442c11403080e000c0e0006111881d070549104944050070116600c86201288111f003d4039282c0c6035960360318500ea801c2d2440c3c0c58980d403040200c0000070361740c0c03400001041c2d0b0404080080c0282c03180703070100381c2d1407010079258107015803c0301c00002c1292480100c0d41c10300010003880441e284c10940700707030012a4800030402c42c143c1d44403085042415004000d0705512042100880c80c000d01c0d00000400708507040c040d8056064965010031901c45002424401040d00032001c0b9000503914038441d560382d03101009150200c7c52540518080d1314202c4011030407079402000e103420440c0442c040b42007404580a4000c03e008400c40d90303d500c49000c00800100030f19260041040046a00200051100902c15400c0b11030810480300002075011a504540c10fa06441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 726546348 1250 726545098 726545117
    0x50105090c0403141011090315040b07110c1905190e130314040603060303081b0a030c110a03080612161215020708040e01120b0f060d0515040b010501020a12 69
    0x31031801c00850245162900e401c0482190301b42544100804000c03108804440810f020031041c002103000c11500980004072442c0003c0c80940100c0b44803801100d48030030754001d41c2481c0b0004220810900c6041e00344074203041c3c14801410b00da507007030329122500000090054944211030804410050140e02c0590b0750704030000806000b5180b907010003d044050948950301c0c0c8900074014445480182c000070304e00004242400003546038400c00b05010306007070f071501c0d4860070142e02a2000c42284010064140340c800d0040000b4010401014425507803000c13182850ba041103510b09000b50081107a802c0740035000072a80f181c5a03100c3c04c0782c2c40c51546100c00f91040c240010849044c070301920000b80005240010400501c00510981d040c42c5404241e50f40c17035100742c108542e0303c050003d0407156414049503404c400b0540803540000003c000002648aa40d00c0c0e6081034842c40482452000d59800c0c40304000c40300d040301e80589020320080c5807400068484121400780008802d007408000381e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 726547598 1250 726546348 726546383
    0x90c0f0607060f02090913050322050907110f07051804080f030c1908090d0e03100624020f0327100c02010e24030a0e010504031101050105090c0403 65
    0x506540d00c40d500b240082000c800038904801c041d61100780000e203e030a210300001e0960340716003040d0b091b058100e0010341c00d150b02d0040900100800b000e65811004080b08002056542c03e42d41510270302c000d030307540501c01e02034020a92818014990302421034110440074403283d25501401031141e5507442c0040c0550b2030f94180b01e1868899206403a606038400001c100c1a4492800203010440c440100348049011540c01294a54000d40f10504903402c0104054042c610452031400000710090540d07140450710040d0804035140c40d4400001101c0105085080810211021404019500140c5541c11038107200c25100c0c0b181002a041c1c1080100d40c1c0440c101180d01302e00d03d154009800b049030305032003043c06071480e412400d040f8000303480c10000362950300b803600341290007062042c40104402008640c0042c207800082440c0c1038542d4581400344515400d0090501950081d125001c5d4680004c85041c01c0d204140c02107070103a020541402804c249840c116011a42c016010990318030301003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 726548848 1250 726547598 726547609
    0x1509020906150f03060d0b01030b09070f0308040e10080f070315050c120c130605030612010e070b0c0f0709090b01060912060218090702030d18120305090a0c030803010e07020303090c0f 81
    0x800c0c003d8000c447c004000b00c100501011054026010041140d00050b912100c04103841035600000b0041c0105000c01c010703200c0c1140c6d00c2c40d00840e80f0700428661603103c020840c9458038444a040480d80048000c006101d0b040040314020b144c508018071030f6140070282c0032080d108058503000420512400202c1c1d00d85100300351811910031008400380c40d40c2e903503402802c1d900141c8000b4480e9218581c1d2a69a010501c98107040c946141c0207800964500214a021600914665001c034007400c081295406424000075010f0804010005103444446c2003000a40703034160044014401c4601d401d0101d1040c2d040103001e11540300101503514800c070b02149095440d20f00506401c0360440c0203001c4e6464021002d0700030440030700003c000042a8401e0f206203580c2a0f81d0213031894150110ba012000d11135007080e1307408501803049581001d4590344104424006a006959407040030005122000c0d003a015076811203250310003141103050844245459405038005148150240300d0381800d5500c45 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 726550098 1250 726548848 726548869
    0x1080705070602160201120207030c140709060f06110d020c0f041107030c0201030e0a110d0809100c0b01061412060a080114090d020304030b010608131509020906150f0306 75
    0x2900543d1a0101c01d03144d0107a28901640c104c0c085118400c55828984c002e10075a0700e000d406544d032114608142c0c803003008050343d43c20568043e0052034400b00d03d4050b02d0084100801410703000004107850240000c260b1201200d81c51590b40011074241c5520340d0025105640d0001103840220180c048000500202100540c00040150200e8120140354110710881c1a290003030f2018011030395205a0507865480c4a90010b003c401003202c40c0c00749090502e1b036441d00a100e8141189082c550a00003064801e500b41030740c0001c2d0840c20340d4401c21048100303e43c01040036081255615504280070009400384240d09520f1031070050020340d056496168400040c100300d4000c11010b180e060880c4004502258003580c01d10844010305c500502c0081140c044079040064480180d00305039040b6110748014041ea4502d140c0072420300045480d04c04130340c0b03805050311400a08d0140b18414031400350302c018880740c461821148600c229041e0352003203072191041100e001d80d89030b5490300000d003072908 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 726551348 1250 726550098 726550103
    0x5030d08013002100e0f0907140306030f0609060106091505030a02070303111303170a05070b042d03020c1e01030b01120905030901020f030a17061f0801060914030c0108070507 77
    0x20f00390103010350b04e03422680b60211040e080e1106c10000110f6020710202c40710680e1031200144400d07090002034030516014640086004007560344410150b1083c500c0c00506541543c60340e0001001049000e0708900010000c01e00071040c2a55800310b00401740450100500030311129400203241420144070f5400031490302c854010451b141c8515000c5846110351034001190701c1d42c401810518016004016240b001700966070701031a0181c1696602140c0c400036200303c800c2c540c3e10030500203100200025a181c07040709070700406041c0725410002e103400c01c19015140119611b840d0204090296403494244080a0130702107490103c0000403141000c0b484400c5904038035111082e41004000b000509040d10701b41d080300d080604003085540c8902c81c4c1040c00c40441c01c00450311041c1c0311542515a44410001c06940500c0d440d00011106050b14409403000245110018044036811191141c09455500140300102013400c01095803242c04142d5941884042000100d0b0784d44941c0132110381d2035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 726552598 1250 726551348 726551359
    0x616140f130f0510030902090414030705010204060c0c1418070512041104050c13120804050301022229030a150b0309060c030934030c05030d08013002 66
    0x580d503485142a00b0168011a84103001c0e18210080c841d200c0d01070718054030780051021980780c945a41d1880b02c540285140716440c04140510b901003542880030f0402070881d52181004d021040c40c258108013034603007005c0590b48803802c500010b500c80540d00d030302010b401800140e140c0c458100a1b10640140ea08076591445581d00300410031000c420150401c5409403800e00c80d90302d6424800c04103011b140350110f500c44080d41d04220200b0000c040c407820714043c100040c075160316840860b01b0781e8001d80c143e41d0400807040c8541c0310001401d40f690010f14804c0d480c2c0d04010140e5180030031560300041180705801c00800030902d0000640e01c0160540d10080c0e020100312b0340c0e00048002c0c1c0c2c0084a0140c03582c000c07040001c20a5407411700b02c910450604010345078041303058a1070081012500c000c50b03104032126000141c80d0b00d1078030392a00074502075070802594910300300c10140b500021188040412641500400a088140301c4211440d40510301c2c40000048800d0703001000102d241003e503200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 726553848 1250 726552598 726552637
    0xf030a0b06090d110a08060606180402090d030305040b09120901181e060206090c011707031512060f091e030c060c030219210213050d080c0616140f 65
    0x55001c008844d80c0c100b52507000c21160350300021912400c0032240640c0151003040400610280858800c08509004200506003218803010801414440d2000c84c08648d6650510050000c064521741c0e0104840b4002d20100c049648480d0150140000c000e0601003011640c110b510001300c07203e00980101d801d1641480988540d50b001c0840074400c00002d401201c1c041092050081603000d80f941060b1102900c030115101242c0b072005001b010081010b0750380601c1010010390448041c0104543c5413440c0c4250f20500300741d0100c81001c04000091071400708684006100300845007001c00c0c4001040100501078201510601403044004202c01d02e424000345400350964080e06001d03480f508000c60410b1407190540b80250700952001520300c2e10410341e01103110035001026000c0d9207440031082550f40d0742c04904520911141103800100c045007002881004000a56000310f043e2109540035180c1c54001c1c0c400031400042060304117000034010750034201070007102c1c000b00c0b01c1c0d8a5000385 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 726555098 1250 726553848 726553853
    0x21f020d02072f010e010c0813061d09130f0c0b0c070f060f0909020901091a0d14130f020d082704060311040209010c050d0909050105060f030a0b06090d 67
    0xe901c8400310103241d40011940c84241101c440c3c00114684406844006000c0f910900540d0401e5661030101c550081c04c00416410306422a40000200050384410b600c00e030040e100b030b01c1c01c3c8103000000b5000d0f180340740c10800c540b48040c810100140e00300b041d200c0b0a040c01d060922800a807a00302d020181e10020300007902120010382c0c4800c0b10007a45101740c3c07003074580c2d100f00c40e4400601c9130080010039440d4188071094240d03004100c2c411050400c501750a590300ca5805800230b10800d10904260301103421552042d0340c3c0591411051403061040003851303e203001011549004602512525a0012550441d19180c5030481384941160005441e52072080c80456640045a034200c20310407081480c11442c2028005c000a99500426101c0741c3c0140d48203010094001d107611504108030611008042030781401094082030790740c0d0b02c004046041030619004e485042c0e11650041008000704001e52421905607900500c440201052f449800305c00168240203200c14180d00055202e40d0004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 726556348 1250 726555098 726555113
    0x1030f031b0b0105090c07050a2d0303021801030e0703140703151a041802190b04030503040806060a1d18010c03020903010f020408070501111f0b010e0f01021f020d0207 74
    0x480d641140d1032170720756550412020341c500440070000d100342e00404c254800070b182d54640f0050241d601030314213241e86020035000010070ba4001c0680c0400c3c1e000a80d010b002c41030f045206910402030070240441b540d03240c0c0c0280e444040c1d04c40513001c8001c10b610f0b0707040b640301441418000d54100722504010031103800300b1002000f110504c8078071071008a68481c842d003828001c0795020b4007070000000300c11440d6020300c48240003940c0c0300c0b00c140345070100104d000031080c40a0b20145005d44001c588550502e8010313840d000000e4036a41c07050b0042c2072308102075a418258002150944d4000e100c082c0c407001942e01c8004c82011100e912942417400804040d0342c103034068a42a00d04034002d101015122400c2d40132845a4018030301d441c4c020f0a41030000e03502520394449036502c600121000310381442c110b252110710305049240c0958480501c03a0642d0380c400c440d0b9180d140b04031000b4124802440000c0d40d200401c400b14038920079452005403d1001983c15200161031100c000c0d0350f24030891070001c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 726557598 1250 726556348 726556351
    0x2190503070b0c0f060c0f0901090b030a06150c080f0c1609050702011a100f02100603030201231e060102030702030604050d110d120203060a081b011101020a02030301030f031b0b 78
    0x2025110300304d00c142019200050040c041c03404c0034541868038484224800c1180d20400419052151010000520b0303001d400003107215840da01000155113060950700031410340c1e1900e410041020030b00c1c0c1000803c00c0308040701d0b014641c122410fa44c425036186000d051020044110254807d0544001039480594018601c284459402000510054009180107513852008103400c80c010742490030010707024900380310f403881d0340340100c518880400c0114019982c40350011001070351903101002c409c00c00e0340c901c3c2c1c1d01800725605950700d9141055060340039840900520100c402d00c41c000c1030322a4000d0048501d216000b40c1541e02c14645810101d80d03540e003000c9140005000301c80c0c1e440b520318000c00c445000c5400f42d501d003142c050642106901940003e40a0f641c000b41c851000261840100400035070294079020303000491f03080030009030801c0c03020070b500100d60740100294042c55a02204481c1565400720111050341c41c1804c1c103c840d800104d950350b00c401c6082a110382403111400c0c205 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 726558848 1250 726557598 726557617
    0x3050a05060a0b06180d0303060321090b0f0904090318080303091605180415090b0f0702030a09060507051005070815150403110d080a0509030f0109050a02190503070b 73
    0x50000804101c00e010051161491405c0c00c4d0700c3da481e4280417881c01c1c801501600e0300905c3c0100c0c1454030b903118504284032481e04500c240a846202d04405130b0002c2e10000281742d8070455500f003000301007907900c280c40f5090200e84a81d42d61a50304003010f0049c00369a00d900b9101c51001e8101392280000b50f900c0d803007038440c00303907600c24254400340d06210080c44205030359001c5d154900d49070907407514100c01c80024000700d9124132414200d401c1c4c1d54003441007002150103000340c5603060500c488420385541d4050102800c40d00204030303400d44c85801c0440c001c11908540380080c0d440f403642c1401410034050140a0720000c0c100b005114400703038000140b80c001e0015055450b1080104010441c5140406c404c040d1034034401e004c104085a10f100a0805100300a0207810501086503105d51440e4060749048020490102c0e101d0b0943c2420082c80f0f041402020080042481a895031a550511504000d01c01e00e400040c9a95041072210104010700c00902114001a01d500c010b05568000000300e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 726560098 1250 726558848 726558851
    0x1b080d05040501090e01123c060507030e1b0f0a0f0602060a02121501050706060305071d011409182e1e020a02030c060109050a0c081506031003050a05060a 68
    0x440c0b440f200c144517504032182c40c1c01801114081d03030380c0c4480b50700031900c0710036200701020601456260511050080c00840d12800c02540580303103841002c440700601140e003010324010307696035241400981c019981e5410401301170107514800c0003c8642e08160403103a080340501d040060452256000c2e80b05840c4036400703644540da05c0c210742d401240182d02c295080c81c420600822102c80803051400c03010172040c540b880c941200c60301e0344026102d407540102e0311030b808908100581e030000408610501440030581072076514040c0c2d056040040c2c0862544030741c54020100384059285504c4c403221403260000e4490b002d8110450f817940c0c0c09103444031321b9038020001c2e04041d680d10f03070b10547d04100d05048030b40d103005048526110083d04084030300003c0d480b003040040d01800003000440d000f02981800401d6070716010b03003000290303465002982c0600c2064024800d00c3c00800b121005107450030317030701c4035107136a1081c201e210303811110b0340050064003541c03a43c1c0052000116220b071044009260 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 726561348 1250 726560098 726560117
    0x41d0f0d020a051018081c060801150e10082a0d0b1302012f0c040203010803120a02120103060b0405162c0a080304090f11071b080d05040501 62
    0xc1ea1540018500201250025403500c54003071101c0d48940030010704010a49003a1440d0b59a0350101e82c8803a515203190058896051010f100c3d0b40120f002600e20840280710a40034030292080100e03030707402500b00241208000610038107408074035038000c0c0f070b1010032254000350501e502a00c0311041100c000c140240e075050001c1608015101c041351940c0b1907009443c5a50362803008a644406a904178100302c0c203618020703a141d19101c048070807920a0384902c11a444052007040c2b400143ca140c490050f401480100b108d2107020041d02c0040240302c0206a290751204441c800a205903c40001c20158010000c010b0040c25030003050300d108196803c100a461b0004650241e900c941c1c0e40800081c0c1c08081e40c2105480746044a024503d1a2501c840344403605002904401168204441c1c0b41e2000c80c080050000030302441c49000c05d081001c0002000381100203846114034007024040c080050741d10402a920462a10010502c01d400d039540d100b11080018040d5209100b0240081c45149 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 726562598 1250 726561348 726561373
    0x61201021c06090b061b0f010c020c01080f0403020c100e060a2001051b0c07030f031e030203131218090605130509030703200708010603150203060307090b041d0f 71
    0x803d4004054000705003900703104400d51010300b040d800208046c443e014940824610070424003402c00111100e402038000440762a000400314000144200f040600c0f45c018040800c0d004074152403803c0041c1c1e11414403004509060322000350764035515400c030700e0005080e1040d540c082c03401d110740382d14580b103450301824800d100f50036194203441d1082940202c030b40325400f8120020050072405c0b110300c1900c04150381d98807005a015021b00c415408661a800c400d404111501c04982c200450f5050031415170070802004013140700101c2c8014800801400e14000b11790007150010640703000500c454441c503444540040152030b0601c00c80740a10454185010440b556005445c4107e041030000c41c1403401d503440c11110b4071558960351039070f003403464400c3c3c81010041c02500060b0400d00700101e1542c1c130f58541811801242d80704808054414810b0005aaa020801004844641d030000c070b508856a40054014407241c80c02d848003410340341140032500740c0800c400750129a10310950740084880c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 726563848 1250 726562598 726562601
    0x801141518060d02221409070311060403050d0903120302040303050d23090631061d10060e01050d030903060905010b1503090c0f18061201021c0609 65
    0x10380c0d540078028041e1200c4600054444950241c0010918015250740d038021900e1001482034500d2650702c022807000205045000c0c1000480581110501030300d88602c180344c440002d0b020007040808101440c003015038944d0180da02842e003060036200702d4116148040c1a121807031000302c90004908143e07141e854020b03c26078080300e805031140c0f850002d003507922a00800c00d4002800451204d0861014029a00e0700158402c20840c402868035040c030008060340c218213046944002040f800480642e201c035242200a01035000030041580c802140d10315003902441e5001084904c40e2451640c2c0e841d4064001c102103a00300b46030001c01e640c030307181403040350802c0d4007000d03004c1500d04804200080199012015550103200002506451600019058240480781048029001c014021288014850305201c1c20f0101c0704103400800302008240060456800750181ca0080400142d050b21a0030340c51210b5401da070002c5599180e86000030b211102003e000e030007080e00e00740000c20710480a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 726565098 1250 726563848 726563881
    0x25050c100509010809010e01051906050306010b0a0c020f030d091a0408062e1d0601030506010f03091406040813080607020307080c213001090509030f04080114 70
    0x20340d245441e102c500c400554007100c000d0030303000e0150b5886101080f040001e108060003001d09004041c20031a905170444291003a0340c0000f4400c1c0c20000040000100000031584102c8990600c00b0b40c6010500006070f0440981c200581c05000c1c1000c00c20215034844516000d95001c1c5094070400b6041ca08440594020740c0500610b43e0f004d00080384846504642c030400406040300e01c51100c01007640d50081e4511a030340985040b50b4601880b407208114036020982c00103080ca0104164a021000207180402c03c01c02d040a240da652140c0301803103c2114000400580c2104580b418140351030590060350240340d80543d080f9400030046840200441c2d454000d00c22540110709203000703030315562401c1d40324440c51000e0380719154110301c64000360000c21240100c4610b0751034031003c1c110745071040050120070350609071503414010808120950020350541e024550000b48607513440209030700d507114000c4403411100c004100020503403015000301703485100045603003195480e07505030041040d91 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 726566348 1250 726565098 726565129
    0xd0908060c0318030a080a0c020c09042a0e16170c0a0905030a050706020f0a03051e0906270105070b04060f020409090c0e15031b01020325050c 63
    0x4540081a510309040300074640014003ca4804104003000e840c00d45550300c85694140400c0080040000000c500c1c4141c8102d1652400076220b000000340014000d002e005100400c41e18074400d00503480030b50101045200c01c03140321143d411a84903071404441e400120364090102d04204900a01c1510176a001d00014582d00d02040c4070391100c000d000039a4100310b918004104140740c0000b00c5542c1007120465803402200585121803c0900090914240441d000400e5018040440000f60700004a40303189083d10003026480c83c0d09401d4880d14400c05403001d5000101180c0408020310140d45131250b210283c8101c0c280341201401501d0718003400c000038201c001683e0001d8081030003a0880e40001c0000c800040c500364459214004035050039a0a031031000011900340400c07504030048941049110507111400400c40f070000359100e10400384c5610001c001c8800e54280c1e4001c0055403203480d0901000b0306070708084520300e1190b01c4c0c0250203895138425661700394182d00705182c60f40840c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 726567598 1250 726566348 726566353
    0x8010f1b0c0b0604020d0617060108070b09041509140a15063513110a0f0519030c171c021c1101020336030703210e0f0d0908 55
    0x8000c0c2c0c40380034a001c40105060b0300543c08106452844c00588210000307010996102012203030704941040c60514140c004104031340c4000c40c01d02c211302c912010f43e00c10a404035404a400c482000f40300340408401da00c007105a5081100900301c1c2950b00c1e104910400c480c0c60104076001c042c0d102c0c031354034241500c96000410361910300c102103001103e45001c1e821030298201c02910030049907221492004039001c2c507403004070034417210412281000074855507008440d8002d201e070401c15400a0390819100b40c0e4400c0440444403002c401009140700011a0802c1f510101696503a2441c0424258800030303400d42e0140c0c1110740c00e0044c400303551610046803a401071420074409031407001c00c1180440004144042a813a42d2a80ea100340001c620036800040b68000000c4420b00700103a0f101036001e01c0c507249400c0000d0900c3c0c00304c008162501d081d05881c1038407001103e906801208a203102000d0440350422000800d9020006000c07881d0b481711200310b4032800a003580454441c104c40c00b40c0500d070f4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 726568848 1250 726567598 726567617
    0x1e140c01050a0e040e0607050a090504092a0e040804061202130e0a020702091005010e01110d0f051b0a0323070f0206190305190e0c040f060f08010f1b 66
    0x280c0c480c83c590200240e000d040004d403000854000c0d450800c08460383e1002400c0000c00662807070340482c0c40e0f0014a0156020f108104407665840d01100e110300200070303801e0140441d006d150020b0b2000d0720040a01602d02c0030780c0d05060034080721070350181c0210310100341d0b00e0642c0c101500e418401c0329132a042ca0024900028200032071404003a070090400c480340c3e030f0240256005a07542402c144e02480902007100d813942e2400001500341c1851500407418001090204103c00b400466038001d40030003071611480b81e511182040d05c441c003c642d00e41d40066410400300498000002c2e900c06007500030744036200b109540707401007941d13048808507803081402d0a02003880080c00c501c903848a080d01c01003046080542d48100c108450705412100f02c0040d80342c0c0b05001c1610203524000d008001810018403c1c0038240311259694915001554003d95558594100d80c100075800301c0c0107400e03a005d1940c4010741c0c0f0003030b00c1e010784100e443c03011a441c82c01285210300701c4800c1c800c01e02142183c9400b040d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 726570098 1250 726568848 726568867
    0x100e0904020d1106040b0702030d0e060d0b030a0803042631090509100e01090b0f070905151e0405011b0f0506010320010e0f060c0106031e140c0105 65
    0x580c00c003403000c96081c20585888003040d92550050406414901902d40e1a01c1f102e004040c517040d5011440c1060140100c5503d03003540701c050865050798419600825100b44000c0806d14240b007498015181030008411711013000b2840002c440b480b0101502609031403a500c1e440305251042c02074800700c103886042c0014400f1008840b043d25480001009284d540e0b449200b0820b6900459204c460741e00b080789013202d02c08042c443e10f05003d80f60b00c005c000d554656071310701c0081c00003d017141f66503a94440010741510702c111543e001808014203445250036040801031410340021a80b0304000e0011039004501c00c03101e4065908441c0d050707440c4200b00e000c2c0b148112500e804c042003a203250441000c1035000c1501041030b103008600c1340381001d6620f21110040b1210524a00f0030031304100718460700c480180c2c1c07940f1011440301021500565101c2001c40c500e401400e0591006203140ca0354103808500d0364111480121080c050ba0114822080b5042c406445140807215980480c00074440c4c8103a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 726571348 1250 726570098 726570109
    0xf090c01030e030405060d06150206010302090402041d010e03131a0a0f05160506040c0605190e030f151b03010303080f040609140a060e01060311090702190b0105100e090402 76
    0x842c000b41068a190039104c10109010350f000110070741303290f61504001c0000308040720b0404904815407004d803c0e01d5040d41e000a255140c00341c40a8459504c402840c0103c040000300f400d0314000650080041c2c9241170205034880e0400200c21001716610040000c0381a036580e9614014102d1501c3c0500d045545602a40c1444490310754004012040c0104001c8a40100c50200001c0c0a00d00038009480d092070024000d084940284d0708100c0140940031018486101400d86596181401d003038240002c00401e02c0c017450f04009007030511885403605140240009801d00446580b2107408030048141304101040c40288001000190108002515040340803007480e0041d02c1000c001c2129a03e40c0c482d805900d609407020700840d08002c001d0020064144034440c0814030000003070100381c0c610344519004516040441d800b40ca00715000860540c404e1107042c20b210784c402e801c440801800d007461242c50009014032401902c402201018042c0503a0452941d200b0003086817105a03034a500740070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 726572598 1250 726571348 726571361
    0xf030204080a0c151b08180310150f0302010507030c030509180412020105091e03120f06040c110c06070c05030d0f030f200702010309080a0e0a17060c130504091a0f090c0103 76
    0x605419001c03004c0c503548d041c09940c0c108170074010085040f040342c10810341aa206035106004000c0005801c00c0140d80140c280c94030683c142c284004e0389042402c068805204060560743d102c41d20120b203c18900d00c51405078002c41c094245000c1e10941c0b040300343d08a5506039003204ca070303602580029840d08803032404140c2c0d4400c00019242400381c1a00c1e2910464010fa8030305501e49100401c2001506107842143ca91403001c0c41d0500c1420400f00c0103507180c81c80d01a442c0d004180c0011018144007100c01440005c2c2406011100c18058000c1c005110041050b400000642800210204641c0754061048032680c000403009004441c01c0c461100c9510580003241850344602c03002c000f280384c59011340840c40030f907114203505500e40c4040041c402640d4015510502c95440701c9844010002410303603020003140031060b80c0b10a1889100e021407141c0c0d0000342e02c2400c2070064000c1042d001c15031550713860344107150b80c101e4845900754041a042103911041c00d50200742d03030028540c42a00004c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 726573848 1250 726572598 726572617
    0x10b07082b02070605011706040309172404020a0909080901030c030f05280501081203060d0804030f030e060c0c060306010504081c020f030301150f030204080a0c151b08 74
    0x62001c00036400da80740c1640c00010f4141c2e035043d42d840c0108000b00c598030028070300303403100806003107036140954026000481d00d0095180c2c440c10035650b005446d00411040e010a420443e402c192807c0b01120800311070b604a400f00c5c0200514900000c24420790b01940c4030f00c0d5408034001d41404501c3c40118018010080705c001010b842c1d035a2068035900911a09000e400b484840340c07242a00c0c0c4407905031100034800000320652030403004000303054000c40c0740200702940208080e42d0781c43c0c80f00069400400c13150301814045c0001000400c103c00381100385a51417003500d0744450359110f201000344c10301030360814803566000880c02003014a0319400869114505042c51130a281e02c501c070040c5003403151481e406d5150310362012048456010401d4000eaa59604020745c699070501003d8210060300e03412070f8040c8021248150380c124003d03016100a400f43c0005c5440054060800a0040107603104a00c030042030059020b1043c3e1080a82d000180240a42521600c0fa5a510000f960b403104158 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 726575098 1250 726573848 726573907
    0x30708030411130510060c02010e091e01090e01110405010f0e150a0201020c060f04020a15030f0e030306040b010801080a110a0306140a051302011413090606110105010b0708 76
    0x448443d5442640144560241c1440003840346006010402c0c2034480d0380145050102e4644408010707070340b02601c1010102c00713880501480e01e40f10500c00c010000c010301102d020703008a00218000e0b2056020740f2110308044000d01c103000c3c4500410400c4d20030ba025540c000390000b087e6504640c080e51a81e081443e011740305000c1d0224004005600d90840d80c0e1950060350000b507103414143e41000041d4103c412010346c0101c41c10603900084d101d4200384900034111414407965107007180643c2c801c821410781d0480034461048003c0700746480344c0c41120382c0c82c0309901c1c1c1820701030194411a40c2034165900103005102c04c0d180c0340c445492180d64440c1440d0b02a094840c0440064940d02a4000009110401c07501d6401c0000d496400d40380010814046c40300074640d43c0015030382c8108082c9134807512540f01503171000c40507842c081d50302030b5412241d03000c0d040c0300380003031003680c80f146007100c3d085804020081644c03100300d43d14440c0b10b4400051300041081c00b59070190195030382d8203540001a4143c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 726576348 1250 726575098 726575123
    0x90414210a03051f08101505061b0c03070311011101090809040902040b060a17130201020c09043f030e0303040305090a031b140402091806030114181e0307080304 71
    0x3480c45622426800c01d0800703030040984034008207038500a13400300c1d101d2407c0380c80700d42d8107010210740c23180034480c02c54002c42d4070042007608010303081c4040d1019038001340507154441c0c0c4034100200000901001e560014500d00400c861a150610900030f00c90f5000e040f443c03800740b0303400412001d0408510141d80c4503586540400e40e03992408028020054503454111904210321000d0b54214001030a41903005800c0c1d1100700183e902080300c52942004940811603501c1d50309080d4a40b12020b403540d07034a5414500c0b0088460540c0b40704000485c03c1c100f00d030080c2807603d14101d0039140403c521034001d600510104000034050300250102102c0030300707221803d96403a00d400504180c038044169065665490034001c04d8800d05100d8051707102918154a06400c0c0c0c40840c0402d642d0340105032074120700002180300d0743c0e03080d0001c01803454441110b900d0b900f04000070189031a440440c04181340301c2c00305052802c51030000d6207400c2c0c10501d40903508010b25030302c590781d0720303030006008807850f40c3c0950 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 726577598 1250 726576348 726576391
    0xa0201110c0a080c03060105190519120302010518011419150f0906050109030308071206091a0307080a120c150204140f2202090a05090414210a0305 65
    0x82001854600f00414910003020140340c240081a00030320700401c070303a2803071105407071181040b4011101c081d1005084c401c01c40040c81d620794a5904091102d81d805202102450f074150003446c01000c05041c1e20750900c100442041c00c0310800318645158141420000314403218030740540650000d0024082600e0f5104000100002240d4026208180a400d001d0255880d1841614040c000a09110320440d086071800b03030240d50014014000c2200340403801c4031501c4107400030700050524072410f0111070352050168a951059244450180c4280000082e02d11700018a0b03c0415030001103080c00c15a4651040f9980031001800b41d814042e0381c18841e811898601c02030002f4010450100d40300c0e89000200128170880b6403401c0e1003030440c0000b503400400400c44131540280d0480d00181d80d0103202001ca6240c02340c41d4003042d4030030000e4040000b48035645415405e01d01070032043d03d101c0388c0e480400c040340d0800700c0c280001c0740d41c0034840c05c0e84170f600079846190007507120480f2030034000120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 726578848 1250 726577598 726577609
    0x5041a04050601060e0303030c04050d0f082b051308030403270510182105030a050c061e0c070201020f1e0d1b061e06090c1403040201020a0201110c 65
    0x80d50225036940c041001040342c140e12184004140324220f02a40c43c1d404e00074000f03c0b46026600611340300c3c0c40c07a4407030402000104031148e400030351322070705442e102c09050703442250399411818030b49115003004c0d00459204041c0d10036075118202c020204103104440380c40360000f40d01b00a0003101402600900d10510030200c8581c20240d0118104100004e400d140c103020300c46280f802c580341803240c0300c0c8116040ca5000398402d01a51040018900007502c01d080340441c0c041c1090015106020001c1c8856565512800914800079208200e401c1034541c40300590348140b1010840060242c40c5012407a401004d00082c282a030051044403190880c044c0e0680c14980e000b0b400c4001904805c0e540c80b880c0318140b200d01507000260506285000d030750101d800640d1007030100108025581e0381c4040c1860b046071500c0500715590f4030100509a250813440c40180109861540400c00c0c2d442084e41c40b10410045900c680e9060307015011880c140d03801075962401c400d007880180e003d000c403400c0c06511030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 726580098 1250 726578848 726578851
    0xe1b03010b0406030b0d210504030c0f060306080604030503060d020a0504020d0516030e0601030210170709030b010e041a0c16110907020610271b14031003030305041a 73
    0x18100c02d981d286440c00240480d003105041c0c902035480941050042550700742c00d020500c40c000c81d19404c0203100c0d0720072591751142d50001481140010000320b0350540c0d0181c1d2400341c42454504118554940d000207941d172404850050001e542000080c4490404581d01241c0c42e1006c4e194428842e112800102070380c109104018095540e04200412015501c240008040107400d081281071000d41e0410b17280c00c0f0501000c5d004041010b80c0c58000d621403078220b080b1071502111042c1030b0804180046c882d8015100550b591088000049019900b00f01428001c40c4d00409a02c41d503503c401040100100007440c00b81611801d0100c044404148407110b003401d827040ca030001480300c001041003c010400303004407007107601090400401e4600ca03000003054802c48110030b50f003180962642005481106010440c0c02d0502c0c43ea030010b402501040c4070154400d850780d140b60f0807070034401c2c240c0e8042290740c0760076103d60030380420209009a0206401602401c038511865000f5000f40000120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 726581348 1250 726580098 726580109
    0x160c021c02090a0c0e040509030d06030c170c010807030c090306062606010b0304032706170708070e040221040507050a0803090d121b03020c040f02070c0e1b0301 71
    0x3140d40d108400c624001481c540e010308004030030051446001c000401c0c00c2409261940100d5599020800a0100b00242c41401501000c00d010a54907481e000c06000104e02c142c0760885445840a43c43c01000316050001102c10b944140c60759035680800c50250a0480c81030050103407601001c00868854014500078160340704000301c2e8011f5451041e40e00c582407511707551013508054018443c822501048075042074141c0340290b000c1c0609110380048040741041204050900d000004d40c054100840c3d0b07900401090030f240e01961901c005507110307401110341000103000403640880a1038103901030a03124480c030028074500001c01d807004070031a000350f0301a01c25074016502040342d8940407001070003a045440285040c1a500c40200d0070110849000030070310306c0c5103508085107510410b0038910820440072140b10100060034083e45501024006a006604004030440900568000c07a015a50f00c2400c0e00000d514110341d020302c1c2c0074050052481e021000b814400c3d00740088019501900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 726582598 1250 726581348 726581389
    0x16020904022d0a1703030c36180601020a0206031005061804050105030d0e0f0112050f06010206090c012c0d030302030108060a110904091b08010608060f0f160c02 71
    0x79407500c104502c2d8a015405200c01400244420613140004415250400314003075216486464010110340148207800782c00004800d40c0e844241060000821031108800a5480014100303a0301184400401c00b1542c190140e4854551072006007466802103502000810741e02e0b034501c2c1c890002a2555021190710180311000d140324051030302c0c1600c05d450051004600502860314070b0348001e42009200b0720079034400c1140c00f040e00e515074003a840600002494010401036803400c556092292001920043d0042c4104000250b540000003000100345405846011408020414100b800e02c0460b101c06000c45205402044640382c8206175440c851081e2405038036581880c8456180210050030740300c455003444242010202c072001110740d250003d9034007091141c4203082c00c50000d0f1149010b0300c04d6142602c40010404010340c00035042d560884103481581c0c40300411011504c5c42503032074020500074407022460841861013107402411150402c00c03003179007c6c0c1c0c0024103410b240703100303070150107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 726583848 1250 726582598 726582679
    0xc0203070b0702010b01120f0603020402030c030901150803121e0106020f0d09030f0206181c0326070c0f0203030406050a180b09150904020a1e02031602090402 70
    0x128012200d501c0200c0d031000f0011401c0303500000700001980421446060723550011690228202d8200d41c015503006041590740782000701c9406c859500031607049005500c0c00340182e00001120341c902e400c903811600114180380342e02410b00701400c0d01522865504400d2840c0003460f50110381c159000300995009099903070b880e6040c1609061a10210008021600c441840003c001c0b905400b03100d41c050760201d440f00c0003d06090030040001e800554844040c03840c000d0100c00d04150b1100280c8280c3d18101c070706101412855071902c00ca080c00009001010018518504c1000140203403400359511407001e03040b6401090035031f40301c3e40180d8000342c40050708a0720307660408840e00b6050050350718a03000d00d02e402d1030030312140100101301c2c2c40380d441001d0458201d1858001c0d0360503110024411540d44c0281c00025100580708030b4944003a600390451040b28034000b106480008110400c40740c498201a07081003d04800108200d900400c2c80c100e1030481943c00d000064a160201f4954108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 726585098 1250 726583848 726583853
    0x306060d02280f020d090e090c12010b030c010207051320070507210201170901091e030807110613080c03400b0c0a0215040e0c09060712020f010c020307 67
    0x30000c1458150013598840344505000b150b001901100315031044000410540b42c003117082d41800600301580350320904251000004510641c0915000e00c000c8003120000001c0c803005988464591151a0340204107140a04480c0f0460b081140507182018a24020b05c02000e0b0180058021050a403202d6120080038403031101d8aa58910240803060035204c080781c110f0f4002020040c118003280310b01e0240a0105110082c250485080503038032020084191100c0c0c003080903c1d0b200717904150001070b40760b40800da0060103101d6a00145820601805280d40d5080d40482c0a2a04032800c0b96000d10030000b070203526000784060040c0320404014114203041c0c05d414400b80b02c10003d0541b282c40d8a030415014200c014820107012034800c88901529443c4d0780c81d03a0741c01c06c039403080040c0d00142c203c00300c101c04060070700080003604d01c01960140c071078640b001c84200c035004035482c990b0820b1003004040c01140c41580c8100104000d40b040301c8a001e1048626800e4421110824016038000f0a81d0400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 726586348 1250 726585098 726585107
    0x91811011e1809020c060414070f06120501060e130c020307080d090b0a0209100c0213060e090111190c1112010c140a08061507170301090e0705060306060d0228 70
    0x1d04128509504103565000c6154444c6e6000c0c100802520101001c480c0e050300910051005000808902081c2d03681c0343c1000c0c1c81101c028242c00342413468880049200ca004001009620402601200b100c6c400c040c18000100003803900101548018400d880001d14940d0080032030450300c00001c2050b00070340c0303400000300d940030b05110703009801840080b00a403112071940d100b802080c5842820204140080342e450703010240084e41c00341c1480000303c0c20222107180580500c03945da000300110041081003182c580940d403074609244580010420460748220580140107000300240209500e6180008900111540c0301c0241d5945460500b80303882e400100900740031005c241500c0c54652100c000401c0c0035030041900e40700f0080700130700c44403182020080d1410715506c54804211403c2c030401c0c0c1d54543e00700744100e51b5001d040403810f04140402050301021180040e107024115201c07942040324a40148900880c103a9007070152111055589010000c802d8089805010b032418a0f4070040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 726587598 1250 726586348 726586397
    0xf0d020414040e010c050313030e03060c220602030409020306040f150518010302180c2523100b01020a0503030f070908030f0409020901121410091811011e 68
    0xc090f403604145c941e51035000401c9070352004401e0700c0d11b004452245010749142c4c1203400000d8161084104205401c0238242c02040d41220380c4c144581564146d02024108a04602560006130000d0200f0000600560003940e04070348000c20105080c86e0581d1010100d58100c0414641483c058008000e46d0030f00040c0d03003010340d180c11001e0031598150740114200b00d04003a04000ea00080c000020455072981c8103886410030903a040c88480c5905012888080700d003c1030586001c030720540741c07903100700c0f0010300304610a02410281003284200000500246110403461f410750240120300310000d10140011072040f808026071707106508080704000e1441d03403e84c111601030380c402c01c000300c4110249019201140c061190150b650201d0000480d91400f5512000d0841814820b99103603c10150b201140705080c545c4089407101e54802840b001e0ba8603524910758034450750008600400e151040c001020041070401c0e120101440480130b08040041c048540050f610304c036503840c0002c410040c0c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 726588848 1250 726587598 726587621
    0x50708090c0105040b030601020c12010501030b360708010e1e07060c171b100f0c0c1e0c150f081605030421020109060501051c02060f0d02041404 64
    0x1418550a45400607043d4030480c000c10001d441c02100244560b80b00304000c250216001c4c0043c40d0351101c2184040c003915081c04101c42804040c400200006041c28070948a840e042460122130400c00c6403800301e020184200ca20140111080890161002d0145115a000100c010611104038050750034022850b40026010b58000200170088a0351001c40380c0c4a80d900007007102051600c08080d10589e200e00f85814841000414603480c3e283d102142c8082c50040700b587c1845804c2e40c00305003108441c0241091008107002c49400c40c00b064200003c1040803011007160705400f54603444480d5495604c2e0b20420703044041c203141030841c0340c0c0840b8205130541d0a052603821410041014582003240e14184810058040000703414020142c010350322424103c1d401c8594040b80350300082c00b8008500042d94583d042800003d6907041400111080c03501c3c0d0808003a090420f40d08024150340200100c0003803038030900c0014101e40503440100018840ea0b4500824a940d40082c00705548800042 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 726590098 1250 726588848 726588853
    0x90515030607110f01110403050d0816030c050c070f081e060703020705010b100f141204020103320a0f0c20010e010623030304150f1b0605070809 64
    0x298942a14001949504402c090400b8164550b0400000d454080c1d42c0d030109500f0b60030892044000710103100180180d0340240c0c191604820b00c001c0035100018140c0d062100c0d90003050400941d80c1c407960014001e02083e140c450301c0c1104172811a40740041c0b42c1c01c8154000703a03a03201040768100c1003010880b00c282003400f61350303001c41c070654045d103400703006103a0000d060300010302d1800c1013001c0d0b01040c0d05c034900914070700c0d11002c0840c0042885070f9507040c01000c00d0308202c0d1440b44a5510341a10251250850030b80a650388650046000e042d01b040b0801106241110f58015011042031702141a504e40710340000914141c240d0783c0613501e0440800684a00e045121211954005440c1d22181c0d854190180ca0600c08160340b0f00421002000202c40d51070f2000124070b580640b1000d01544028070187c100000c8075408240d03d80c420307445842c135445103220b022203c0b03078040c0c501c901c003012032410400004a0420002c00344550f80c500100c5a1960b24010042d1440d0032014803a00b11040200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 726591348 1250 726590098 726590131
    0x825030e150403080705060708480403080d0c0c020d330b030106170303071b1e03080709050310050a150b120615030c09040608160905 59
    0x10054032024030100d0041c0150340c40000000714203580c07800c8800441d03102c4c8105030340e600c981c00c0464503070788192440400910400c0c00f040c52140c112a200c1111300c2c0900202e102890902510101440740c2510900c03c2036141c103107142211703110742c0900010b501540d21075540320361a01d004411580340c0e4410b4030a100103d40401d02584800d0303425002680d104200707003800e902e008113603280c1d00607596408680c1541040041c84070400c540200c6184a03064000b400440e45174440b008403c481883c45d41100c1d88240700044195104003c03214495454040d0740c00c0714461501c0301c00308003040c489046160920340c95540e003015403000005501c0b0341c0d40c0c03805586983c100000039855807041d61307000c0c20a0341c54001240c40c00c100c55005c000c00b1580282a5000c003695940c840540d90007494550301c54141480020303000d41031102da140810300040490520315543e8041c429101d030455030300247c02c1a90b4080100310310710100009001c1d180c048294480851622600e142940c1c001000d0740401ca840d2070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 726592598 1250 726591348 726591353
    0x307090f062106320613090218030102030109060807150509010c0f06020a030b0108130b01050d0302160305210301050a05060c01021c05090712050a030f170c040f12050c01051e070825 80
    0x1c41b40401e0350405000969030f600441000c18401c100c401d9100d915510010000800b8411a880002140d8498081e42c40d0543c0d200400045400c0a041d8000441c00c100064070856200340c03c1030701050300c40c03121101c0e10030464843c84102d810009070030b00881da03240c0302c3c3c8805681008002b980221030aca005071401d0b0842c3da840c4030b4414103103d2240500d03501d03500001094001e014282401c2ca02400507504156a414041c0e911903021600b4102d4818100c20301f801610781900316816110040c080c84d940c07625080c00c1c80543d0303002d403200b15595513080c0a10201c50494801c070701ea04005480000c6028108000c2207410040c066000e58130703c074010107034000055408540240100c2d05400c02c280303e40d401e0042900d060b01c0c044619550a07909070100130240c0485c002400035601d84c0712140c800c668032004400d0201c107000030043d00b03d501440d50103036658442c40003002007203a011410400c0800d400000041604608011a8485004035008030781c0c0341c41c5001c4442c40d4601c1c13070380010301900320b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 726593848 1250 726592598 726592627
    0x9050a110703021c230706050907080619020d0e0d0f020313030609020a180906050114030a170906040305100e0a021806010918020307090f0621063206 66
    0x41090f0410b14130240d55046902a50100c240103801443d9944000401400c46009602a00049620364545000f0915541c00040e5010aa4641c180100032039201c22030030310285c0702c541c0c01d50700003540c0801261180c200c8900414880443d4140104000010031201a010850344a0b1650131544144904103149451201d01000c0742c0d040000020303154598004034841e910a5040f4041103807034500c184c000e41c040740d0710400000340110400c0040f641c030f405015040032801c0c03220540c90713031049645c2d101080e0000d03444140c0314401e4040502c0c200400c40400c200c5e820030307031098665030022070007401c503151079015140d1900a01c0c1d001e00111906ca50001d03c4a0000143d00c40070074641a00043c13090f4000e034225005810304c2c00d200000c81b402070320390f0800382d8011a02032001803130007000007032901c200741e5090f020380d0740b1521604101c5841d0100306403103d102103082c226403602c80328006840351904118258840301c0000c0c603075081c020100c1d22039104481c2e0405a01600080000c144100c400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 726595098 1250 726593848 726593863
    0x110409090510051023060c061f06121e0e0d1202040e0711070503060a0e010c080417070f0807030c030f090605160f021e030d050c060a1805060109050a11070302 70
    0x10000107845c805984001c081407551074803820f50007002c001400000c00400241880c0301c3d030403611001880000030524507104000c1031090402054511b8041d46540c103042c2c2160340c604481c5c019002e080d8005549140039034650300e203001c1e1280c2100124154803903001c80e01c0c3c0310f41142040e00b035242615191005000d404001c217103404104042e002c030060701c4010710603400100002021100181090f200f040c00804054031304080315803030410103100a90007681c107a80f0807a00064810050740d511100081c42798001d0743c044851a4076014104006006400170f03008403406580c3d640c0d5400590316002d05205626100b0f60300f4844107400c00c2040662100464107502601001100381d0704140c6080192000300c0c40000394022000c1507414200d45081460018000003101154600841503070144e86c94483c070091507000c1e411010018501c0703240382c1c000105100c8454090240c108441d120f15060080a07003000c440c280e01c52060041c510a540038009145013a2030107207103054010381c0c020b55594003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 726596348 1250 726595098 726595109
    0x6020d09031d0609100804023c03060403090314031b010506030f0615040911041a09060a0e1501051b06011a0c060708150406030302070f0b0403150509011104090905100510 75
    0x59800001c0231521048004a261034520340340c092002c6800c4d207240e400d4005130130024070328031060304503007102d1400080e0f1030b00498054540390f16150450322010681c22042e01e006c0b5107848100000d940c241c0b881040207580d000b44400000342403c1c00c1c0201820302c130007a418842035920080511080e4000c044860740403080480e030000f411605c0e0310700ba42200002c0e1034156402441d203055010304000341440c040d4038003c05ca030b8840550307032240c042041160f401c0c095441150300440c000780d50000c2e6004282c3c0340e180141055410042c0c2c2e44618003c40214640b80390480d00198010001d0300f00c01021030b085d07400b1424481c0e08080240d11000d42d5034a00400c01c10401061201003920350a9075800740740200ea0107002807009503100d06000c0c1d40c0321981c0c825100080c03181d2200140041c80541501c064030307171100200b01c0b40f90038403051034007078000035101400fa950394224003442c8040c464000c1c0014a80e481011480561a05015040a0f0081c1030441c055041004006501401d4a004810f0347c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 726597598 1250 726596348 726596357
    0xc3007150b0a0504090f0606060212040909211101060602030a0e040507090317120a0209030c01080a0f05010312080601031b0315030b0702070510050906040e0406020d09031d060910 79
    0x2607241d0000340600302a501a90700540f07802c1040c400d10482e035105d503542c24007604d400e100680d03880313104990b101030204211485070310602c000c0c08862003e412812505000b2a04005203080c00c200c0c1114841c00740c0d00910100300c40341c90900700c115083c01031800501007400954181030003c40c0261000e00640d019a209995500000d40002d0044440702c0207136422040318840f0850f60603533184160700c5031100b0010105035000180f10846c241c002c4504c00301001e000f4001244402006456003e405888110356a440d00c210032061201445618021409009400e414841c60340f0007800070310029052604250800c1000c1c035000c0d03200310f08490f41615500d80068408440e14204140d07070545d8000a00301002403080c08034150340094210159601103828900c0340b0949a0156094420007407132070380100c0203002c00c110101c0c91240b40c940c4a4026200945049402d014200c1114a40c0c241203010038a17140b090040804642180300200d601558003914201003100019a401c000054032001c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 726598848 1250 726597598 726597611
    0x52e290705010f0c0e030c10050310080105090c04060b0304241113060f02030403170a09270b0a031a070c020d0b040510021c110c300715 60
    0x690614045a02554005000300304010303102070084007070320780072004000262007243c5d072000340c1c82c0120f50120180b00090021010400c20342098a09401c0100b82c880343d040c2100000130000700070f014043c0710b030b0120b801030003286000b00d013000100e40c183e411450381c02401780100400a08407510010603007000e844c07042c0c034803041100300700050f20341413000c130900c2d4101040e400460450681d095081c1d4566884484098840c42d20403a036034022032002a0440740111038000325880d9102c02030240b15845d240c020f440c151140384030360f109481510424000c51201034120403504244c450051444400c5134a0140c5034519106c0b00e020142da000c03041c1204008001190340d0310b0244c040428a1640541030084643c0d0504200d4000641185d0507035141c0141d51121000200500c215100d001c20740c1c8000e006110110706200c0181389086c4070381c040700c03800c0084281805041040785c1c00e200780e800760084944910580da404a100003c0a6814440c0500071513001800000640e403000e940e0010000c0c45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 726600098 1250 726598848 726598919
    0xe0f0f06100c0606120812010803070f060506040b06030916050f13020309190f0302150708150102070f08030c2112100504050a05180d02070b070203070306052e 70
    0x100310079440b817a2015802c4d40c14204200303840700603102261000c2070007d030903a612141c0903200d2088081c0105601410014040000d810394440c6801000240c00016194034038000710310198000c1e00c2040355540485100c0c0d110020558642c030190800391030142e040038042000c2251011591040c070a0360b0b40210001e024110100859124801e0150454030425440e041900308400d12800940050049002d0071842820584415000e201d09941d0307041c9507074503d401c1c071140107800410181140206000001c00000c07505406000d05151000345569a100212181c5003038000750354407201d40d1151f29481880c5035982c0549429510070b0a014920340d450b5482043ca140700d0382c0001d0703030251800c01030040e114010303440310380300740d8480a00c0b079250345d00f18800700d035603000003800d00740141e0201d001488008000809001024406822034400c95160b66580094800440d55014010b08041d03c05540507040305005a41003503084419142c1741c18850154000000c80c000c0f03460040c20005d640342c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 726601348 1250 726600098 726600101
    0xd02120f1603090602070b030f151804050303070e0a030b281e0c05270310020c0a0b010501080903030a09020f030129030304050109030b040f0c0e0f0f06100c06 70
    0x20301c4440109100ca40d6206450040e1011006025035001441035250100d03294900da422a806030841103503d000c580d68084080154600c0141882d4001c04510405145420020f01481c0264491805941c4074505147d00500882c50740307410b271b40300365032905041010940c1c0b00003142d08800e4003000d02c58070703e48500c0c007821034004030560382065500d0503041c00c541126270780c00400020f1896005010007108604112a0f6010b1500c994100c000c95555004884910507074034502540c015003550201c0c1050400342c006c0760081d9044150540140f0450300400190f800728034094082424500e85031b042c82c4800950300c0c000149424202c40d901c1001205650724540010681c0c94014002c3c4440c1c01222543e80c0c414018140c02313801420b190030075a0aa00e0003100351800d0318010f940f42450b00d0f2440e03c0d07100c1402805003058940d5498500240c011174160300d284d034003801003c4058003003030500d191030200e921030080c55100c101008000f446071603950152000e401c4980c2d40b502e80b07410601c074100b610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 726602598 1250 726601348 726601357
    0x20d0603080f2206050901030b010212070b01030b01091404110d0f030e03120901020a03031802090103030906080c07030c140f0618070518040215040803030708180d02120f 75
    0x801e105000314411000c2e6118a0003861480704844000078040b000c003034003c104450b54004c000100b1010300c90481a54425031250440e480144103d814400590000413100d5006103410348603411504010305c1840384005200b030042003000ca04100c0d1800b01010600241c0d4064001070010012003400d1841d030f6581a045040507810403203800c480c1c0c046c0c3c034002c1d0141c002075090a010340268181c0d0008032031600f05403a00c646040c1c01038010015503076800c078010400481c3d415001c11140603c0c01c00340e106d005610f0b020f540710382c581170b01c21420118040c02108005114581c00903040011800090340000420280341d4401c99111184070f54044840c00e180004480391801c4c0300d031404200c060b260078500d80c02603000d03d209948003d0742701c0061284642d1401d089800c4440d030701c0007080c010300f0a5100b01802c0b08184a02900302502c1d40c03201d80c2160310907110000000c41000c28062460000c0341001603080c4030000410031920b00748806501c5c0c4440603680c014000010543d0003000c0e041c0d00442d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 726603848 1250 726602598 726602603
    0x15090c030414061311090603060714070606090203091603050c120118061506021b120f1b01270902090a0503160303020f070b0405060a0c02090a09060e0c06030406020d0603 75
    0x8902c640380c1901d00f0f41002c544d1900c141d81018060b08442e61904004811038002c0c070f0003078043d03c00e0342d903400f800392410404281e01c0700c4543c00030481b60000c40c02a11803100a01001c410159a0781080c54440c0d01e08142905840c01c46e02c0c1a420420000304000795070368400409480c0010a08032810a49005003041681c0401450402001d8000c06c10300740c0c00081080b40304d0340940202a01c8403000c90381e03211050b544484e00c0c20040040f00c15458442c0110340c84815803c00c49582c002e20358190350900e01c15130107a54401c100750396084619a08200040d840c8034040b401c2042004007502c1203800200ba9204450081d98006108031407030302c0c0d0340c40d0b180c05884058100e500d131042140c135182004010f44800e03401806100b882030410300011403000103c1c3c003058200703410f05050608102c0d0a602400d4500280301c4080c2c40c540058039910012403203008034810000f018076890a24000755042590b0981c45a0000c0d24041c805690f40070559800c99040000143c86424543c0680c00078042c58201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 726605098 1250 726603848 726603853
    0x5011d07083d0f0606030b01050412052103161b02040b06041211092211030114070f0f03110d0e100912090801061404050403020c090702031215090c030414 68
    0x1d1002042e11a004101c002c0601c2c5002c200785a90b03a40100c0444520120a030300140b000c1100b004100324404800e524280900d040d1031625240700d40320300700d1882c80304440350b000e08040300300440c2540104003e1224217050802e12198a02440c10052403800b07008000d1159560390003252098a41c2c006440150941c89800c1800c2c048604141082882c00c200603446601c1c40e80c00198100045034011400092034070312801c90080507560705031801e803103a141540640d80c503a41c410540c15651183c0d4090000d5895010703915a43c1000207240982c11460030041c141800c440700c0400b03041c10103d075a81c84960b100024052410304500f410114504d10f1180640d05001d181001d10503c54003964054034503440e40b02400342d80d035610300c1c20390f01a4443c1c2244059046001601410140c100c294020321a105449201c3d1441000542c13140d01583c503c0c0061b840170a01d100705110141206400041c004c5042141f6040c0f08002410150000c100c40e40c05100440410100058454011a0a9038181c103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 726606348 1250 726605098 726605203
    0xc0308130c171603050304231e030c10140c070f0603062103022a030706020718050135010504060b0a0905070e191205011d0708 56
    0x20702c591a050b4203451074180c01510420219000d2140503141200d034400c010754201464039021005101998110600c466686c81d20292565504240318081d0610016040d0811401c04241854001c6400d1038502a00a46404040700c0780c2190501002c1401890701c540d841c83c4065001d801e010156000d0400605003080110b005030b01508690151030600440d002c1c0e4440c40028800740d030b0044440a03000da045520640d90040e01038016074201c0342c3c04001034403204544c4022910700305051b4030005c01604080c2080c0660b22846805042d44103190038184040e506190303c524403c0984500268031620403060600140390905074160740d068104001c000614240c2012005080480083c6e80300d038241500c0800d140d9800d210342800b8003915902c1c035881500c00010320486514414044007d00d845030000a00000e514007000300c100d20610001c2a148034001d01110000035000c90104583c0200b070040c8503400c00016004010307850001e03000030400c1d1109008803000507250021401650881 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 726607598 1250 726606348 726606359
    0x1911030307060e0d0f1b030e1c0605090c0301020721030e0d0e101d040b0f0a08030d0e0f060403270306091703150d14030a0206090712030c0308130c 65
    0x540d04072190005e860700a113a800400c4101c0307143e080c00d66070b4a40c810100035820b0100b0700c00c0365164202d0b00c0181c142d00f8044a80700c5120f4065800040407100103499404202c059003080c8200302e842c8000b0341c020b504007405a614212115943c1800d06200450b50380541da09c0e5210341c000c07500b4490341070103a0361400c0310f2681c0180a0804048031034040c0c0d034200c4140b99400d224071264042c8004408801000000400c1048040c00800c2401903109404200750902640c0d4484554000c11788030b8002c5a40d00c120300c030b40030150b90000c45000e6164110900d1410003910104182e03500c1b82c1d1520b4100e0302c10030400240c403402c90b030b0000b00c4240045142c1c4044200143e03039000040440c01000140c405404030400c20030944811100400d2503840b50b02141c006040c501d0102c800701e0301c1000c02488501401c3d207901d1454200c8000f0780c0c0143e000400344960383c40c0c20700c0720b24098072040c2440055440580c601034a20350503034a00070200701d074090018244580c09030428007080d80c080b440855096032030303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 726608848 1250 726607598 726607603
    0x61a0f032d041a01140613050a060224040506070c1506060f021b01020c010309060e121905070f030c0302210408120403020307030609241a01021911030307060e 70
    0x45408032981e243c1900d005074211843c0481e0f9040707400700c2e00d035448824180418003d0b1030b0082c04260309540510040030500b96100d00c59040a801c103039000b0518580c1c603500540c0b80e00001d02c40a0110b00c9a201400080342c400b240c0d0641c01592400d02040e8514649421000f6110140c070000e1a00e01c0c01c075010641d071b40d00c10031100c159802d560031601600402d410455000c40158111340c05684903100800c01d5501076008002068010080051051800d100840c100f00407400d0325110010000340106014501e400140c054402e14a442418080140d5410b005d20070501e1029050018480302401010b1003002010140c528400c905900c400c100b0102458a400c503015800d4203001c0c06050b684400e14410580c2e0850707400400a00c066491038842200500201c2410b65001d220a01000300000c408420124210f0359031000040a1055100e000440c034143c5100c103045400411113400e002541804061105170018050425540d80e01c0c0001c0c030b0341c03007091002000c09044c00e400c1ca507201c001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 726610098 1250 726608848 726608851
    0xf09020a030b2707170a020702011b08270402120702012f0a030e120a021011030a0506010504090e01050405060f01030f08090307030c0e0a061a0f032d 66
    0x2161402e021a60801040000004101c2c0501c440c0c180008400000724030101006a042009400c01440031040b002d240c200c440340c122540640b85800080440841d41d0040e40d442640c403000c00000702c00a110760741c55105200303446c00420b240004038106200109201076041c071148004000315074401800040c41c45420084515102551a0107030078140303c0c2940c10181e110709030317084181141d00604403407001e490300217048aa041607903c400d9110764040400061591883d49011680c0341c4020001c000c0c40c1010905d1800742031410301c086c015807080c4a0040c5d82d00a003048001180c640e8640b00122440c1c0207e50002110300d00f0300c2003400d4a07a4040d480980994014401d42d082981e811030102000790082c07200a0080c402c045030007000c1780c0324002504100c40c0c001c0a0f180c016503030761034015a11301103401c180510300384c01041c090707554480e2161030001c104e241950b0081c40024140c0c840f00340603032911110307903007400400288040000c0e120100c007000303210200c00e031044001400c5040c4500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 726611348 1250 726610098 726610117
    0x403030b0904110906090118110c0a0c09150e0a0c0c1506080106050f0d0f05010b060d0608010c030515240c0106030b010e131205071709040612021f090f0902 69
    0x14130340840d0340c034200380c44098142c03011420400b402a8080d40410001d141001d842c5141c41014090420208401d101311005280107854400545050050341c1c0100d426184c44040002a60503080082c2c40c4e29603003039a03100382c05d050005178124844900340c2d8100c04040c00200351020b0090101000f0743c00d80e006006603040030000f049425141c0c418400e0481001205a91040c4c8400051002a422080b5000301511a00020494010740e501284441d0019542a0801e170f0302da58043c06030301070900c01c80c0464101c5e85414070450070105c130f1031846840700b80591401000c242c0d103120400c40a0a0084a10000a1720201d07600c0c11050b8000d4000c05441c00704998060400000107096621440601d02410000740c9410901c14681d95181c80003001100c40d0090020600c2001c01107100605114291142c88010a0303071071448100b040102c0e1041e4009203e840200490b40016031200400d41d0030700c802c1d03a6040e118422034880261000d00c00ca43c0700c0c404c051600c590100b03007280c3c281c01502244030f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 726612598 1250 726611348 726611359
    0xc0510020a020f03030105180618010b070b07080f0604051509091b1021240302010809070b0d020d1e061e1202130f0e1506030d0f080403030b090411 65
    0x3c000801042e1240703c2841402c6d80280c1200c00308000d800c2c0c1c15005030704940c009160090b2503200000400e49260f09a0100d0058200031620070705000303554105503030108040c078100c281c61425403518801d62a025044501a50356403001601300d440e100c0990a0b8014000c0032042c651412400160781c40e440c003034840e010700b1551240080203044c058842ca04088032903c481800c1460059601c3d14030007240701d4090300584440c496102c814450084120a00546001000c0302d800c0d400058109080a0480301940c1c0c030000c02001302400c1142a02c050700d0742e030100507a40380c8440d00a80d010704141f80030789152031140e0240c0003a03500c080c1d0004046550a10452900c40780101c840410120a44148070446ca03607064248018605920303030300394113842c81400096141d4401228000c40300c8a41907040c981d070040140043d49881c60586950010040b401400070001ba1580108038214202030141072100b551b010a041501075007029010302006801c2d03c505e450103041400c2c08990c2c4114090042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 726613848 1250 726612598 726612613
    0xb070e18100f0e011413090f0b012301321b030906121911040806010915150504030b0411090907030503220806010e040b130c0509070c0510020a02 64
    0x321560812000b00c0e43e480b0904909a072a2250303c55624200c11182030740703c2c2c400c041420304000b0a01c14180414001d40f07a052501c2030502c1c11109180d81a00240d030504680701410400d030706505000b502a0800307290845c440c0309058201b43e2210201c5405890014070005266400c01c1203002510311300ca41400e0f40d00c0d600d00c0030094641c5a129140e01e564010000300100201000d00e58000c9811000d01d11406850741d8440080c41e00300d841030203505d0f4100303500040400c41400100126800741c68402c0b0708204030503910908401c40e0900d0700c0741024002420049001090003001941c0045410a8008925140c07626041c0108120f1f103110500c504039820202c0c034032200004030602980c3d840700040d440d00e82c038403142c034450400b90450154012210303080458060400d2140321b0082128001c860300904180c5040ca00740036004000d0800117a0800c0200702081d20307068450120365090320b51054685850b4070403244048020f40284c4140300342e0300c0305503444169900500200f4080d50a44854 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 726615098 1250 726613848 726613859
    0x6080403120504050a03030903021905031306080c04141206040f021e0102060c0903010603020d0f121e0c02040f15030b0c07150522080306041b08040b070e1810 70
    0x4460782514003030455405810f1010000340070742e1108940e00e00900484500001170703030914822fa41c039444111a0354001249540310a646000e80c1d2000d01a01c0c14902c10b00e1030404d10543d46401b8903c207410041c1c514080340d40d40b54444603c26006200f0f52815a0003910f041d08140d00322841e140000c03405840300c1c5040910311420f80c540c5800d00321050380074103000d0f2103858036400160402c0803102c1d07043d5a5901d0010050b43c0f42010591141c1c4940703460300c03082201c0c0c18141d0075000c0004191061110170590040c04a9002010303042c083d40c5400e0810550a06001040081410146019110303181c000078440c481100e001880880340320f0095480d0903034a24007803400da809581e500808641c5c503845040d028032029004a41c1c090800c2d0003034100d11012a142403240e1046002c2034a01880000510466041038040e1500c141711990b5030690302680884000c0409070004c0001c1e19044021022a05081c8140c501400c10302008282945120b25210042d04000094a20100340c0d04226000900c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 726616348 1250 726615098 726615101
    0x5060103080903101b0c06151d07020f0d0804030c0c08060a05010803090607061a09070906090824130b010f05040b092203030905010f02041508061e03010207060203010608040312 78
    0x140c07020000e4604224007030f80300058810074000e860481f14035032503580c082c1e115a803444003c1c000b8243c00914034a120622178441310020b002922000440d040f214400302c940078002140240b8012901d03042d0450f0303a4038141100c0e001c609843c000c110284a410028039550001000c60046140c0700d410009642d03200d0100f80d60307108481d80380390442024450780d000300703105d980102d22041041c800ba04110007443d0001d080d4440803101c11020800308030040c4102d81e0301907509409046008020720f42034a16842c0034039100e170007a01034100c0826040003c0d40c5007100040c2481c1d00ca5000c2c13140001541c69800400140f0310b107014043c0250320701003504000385031408160740030313460064403490549903400c0c010000115805059044c580c90344403100004809120342a02011812401a2260f050203480e0609211801c44101003041c10b02c284a030566541c1e00f1601108010050340794501180c1d000720b40a4010b1240150403548007000000300c054001d0619403040d48690b80340700b40001800740c02d80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 726617598 1250 726616348 726616361
    0x50f0c061005120619020f0c03030c0a0207080307020a0e0c070c0807150c1a041a13120c050706110c09131e1a060a0e1501020714030c060d0204030506010308090310 72
    0x205e03075016500710141c41501c5134000d08102c500d10718402e01e031004120aa91071640180c42d02a49410002201c104007903042c0032003000f5016040240d03150000d59000204041202e02070500380c10440404190b0300100d01040340e05055118071a0036100d942d401034540c0391a11440b946403204030554044296511a4040c451040c2e0300446003500c030401d074010059200d0004000301c3e0001c0301d5807020079440d10341d000003d114064400c05000e0106031490040b0b10450404900740c2401070010a40303001400118170700c4152001454000ba110f0410003d842c9001d0754a00c0c51070f0010b004006008558940c8500640c00c40e0007100044c13a80182d8880c00c203010380741c0c0d136805010782e12002124414106580045900b0a0b002010070807000d44031400103503140c0040d5181e180311511141e00c3d107120351f0180300c58070007031040c612442448903c4202182d110f01c5050901489000c0000d0001c1580070076905a401031508502190281c3da12864110395950111124078802d10441000c10041c000710700610 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 726618705 1107 726617598 726617611
    0xd090201051e0406120c020a1b180f110705030a030f090c12060b0301200c1623030109030e0108040f05030d0209040501050907050703050f0c0610051206 67
    0x1071710007804004030203103071405c18056103109a0003092154110fa00a03d0f00e40c800d0450b50f07113041c485034264111007550030800b0520201e44044c3e5001403048a0310990402445240b510200c02a00600e84000c183e035108200700340c01b0f50701c00d0b04207a103000e851030400b00f16001c8503a100401c4004580084802c2d2048942c9030003800107500a80380d0800058000308442c000c09801c0c2c040030980f8103050b00b030380c200001d000702e01c0d400c0801a000c22004100f40c8038143c41d8503406038031891102500800845414100d0031036042c17a040c45001c2039994144ca0b4480d10307040700401503a8880c402002502d80d0107906000a010500601c010030714103407141e20040e07407444540e00308030480d401038002030301500031482048003040d0810205d5a50a400d8244035884c1c03000400025141d1041340d0100c0510f00869060001d100010745058050ba00304444e0004262445480c542da10102114031 = true := by decide +kernel

theorem cover : BRFrame.Cov 726438848 726618705 := by
  have h0 := BRFrame.cov_init 726438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 726438848 ≤ n) (h2 : n < 726618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
