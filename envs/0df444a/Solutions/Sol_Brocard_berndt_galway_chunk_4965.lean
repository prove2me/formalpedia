-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4965
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:18:20.506797+00:00
-- url     : https://prove2.me/submissions/da97be11-e080-4205-b258-99e9715c44c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 892805755 ≤ n < 892985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 892807005 1250 892805755 892805783
    0x31d0715030204031e0303021b060105150403022d0d03020a02090a110403080f1201180e0a0c09020307090905090d03201903090f0606030b1503030a0e060c030a0c 71
    0xc03280c001c03642540d50000300c815070200188403011076450314400482c1455000c9c014080b0780090341d055200018040d0b40108202d51400d0244051440c0c8201605c01107881004180f0258440440c2030945119000c0881c0000742c0b40381b031880d02070000300f54050380410b8400d5840249540000c141ca00c5d14000c07140d1420940710900c01004585280030350103510f82c1c09101c20001309140308007424003160604909440c11114031103030541400246c110f00e0607148a2521400310101038843d091440000900070b00d911146c42d00c64031000005440350b178107502c0e00040007030011803180355000d0003030216850500540c103043d07900649a0f0001c24a40c8006032074018a60003c4009141000c09001e01d83c58043c40c1c245c103482e91240007081050700e0390030305858002c3c5500040610459074010b07070081c400040c20909510b081c0700840005400850380c0c08101030060803598001c011188580c0e801c0c240300e6400c0b4031398400301d55540100c541781c19071800041225085140c120303120201181c418100340e00242 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 892808255 1250 892807005 892807007
    0x221a0d05280b1206010e0907150e0f0607050106090b0414010b0304021c0c12110d020a2108040b040501090b0c0303010608100e07020106050906040608030316031d0715 73
    0x1440075110640031031403540c105000108941c0000c1c60110054040310100c2003900300c0038a440020792002e81b0000703540c002c02500c88010305c82400039005012070f8603080c42401300f0003490010624a881d102e401c0c1d03030200101d2540e441301151841d550000c0244012951016680c0042810502540c042d81c204452420003072980c4158505076800801030030308585442c0c0a01c018015141c0c016000c0790b640c0c00c103140102d0100810900103010803010781d91030b01198904095030b5441695103d00561515403900c005a0703035024080140e0382d60300045980b80104100100074030810000c040c0c040c40e0000b402107080281c42004000b55102a00c0c3c0a810f141c4da0681c0b500203101e001500000c0d07401c1400140082c80c4290b0603d0b03000807889a045038100d480303c2c50292100303000c0c0e402d0341c0540e42d1048104440c0c00c002840301c0d44400708803010000c4074a041c01d52500d030f00c401407241c20446a48150640e40340d00a0388408201e180c0c107005440c0c3c030244054a5aa038242900a001c8102012400c1520302 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 892809505 1250 892808255 892808281
    0xb01020c0307180213171009020112051b0d02070b010b03010b030a0207030210020c100501050306060a18151502213015190b221a0d05 59
    0x84050000c0901034505070f02444859000f404500c030564080000b0310141050308002c1000d40070b01c4060380d0300300c182c800d141071030000141034409019040c4003030034000d41c0e00310810403d200c0d101d0102040c517542d49020b041c5909480c03000782c1c036180c0300410003507000820f650181c02950300c0303038085050716601c621081c0f074240800d2103000305180c010000104061a65005410050f00c603004a80c072404100c540b000c260f80040f4402410356001d10700b00d030072001c024091240144400c2c2e0203440341d401c0c62004078280d50018000d16440911222130000c0001e46688408103170002e11108a054540340c004495212605465070001841841420701404c20242c0300c0c04142e4014458413840c1005460a08100f00c42e04480d00c88038002000080c0006480c2481592080124031141d0700700f56540c00820520b40e00001000f00c00c192200300600c2481e0450040314204400136905120b55030740700c508507403440c0c8181c202494040c10700a141030a11010000780c501c4a0702d51005004135502d4404800350 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 892810755 1250 892809505 892809523
    0xe120f16091104060f03020702030106121e1119030203070303030c090b030106170603010906060b03070f05090a0e100308120a0c1701090f0e0604051c0206070827011b030b0102 77
    0x14103001c10081100c280100340d00b0a6405c06400d000d410905260002400c41c1c400780d00881044680168041c00c1200701c0f40001c400c080616000e1b082a80d251300d80301585944000903901980b8884141c01145144440081c01568010102c800564480c5030080150500da8601c4000c100d109601192403000141500c2c1650704690f501e800c10060340b02c2c030400305c08000c1c0c2110703059541d42c84e001d000305002c0c1c01114060803500c0d09260b541d04251a000b07212005003844901000310078410681c003a5543c039820b0044403202e011203600d0382c4481801c1c00d004281988003c050360b00c00951840c500700c7c3e0303c04051151042030401c200060f010398060750350811018042c51800c0da600d006002d88005030740705201c0164022400070b101801504814a02403068405590a522074200100c4840f080716100040340042d00c0501400e04202c203028240320005400031151500b000705904001510301c11017100048800020b0001c0d45042e00181466084074000b2000641040d055040a500018030400c1d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 892812005 1250 892810755 892810781
    0xb150301020708210f1e0c09030604030e0102060105010e0a090c1403041b050a06050706110c0d03022208100207150515030c1203090609040902060a0f0809011b0e120f1609 75
    0x74445144a0382c1b038081400409110500038180b10343c08080e1420449248070324441d449002000911900291519030164030050401010100c5a006a10b81510700801c5403214407003c1f9100c84000400d850034502600c0100b01003a01008010030700125140c800180d4076003840030800f19031980103006040401d80070300004074070100440d10000c0c48070741c80003840e515219025420604140015030a000700346040034006a008100016401128640103074000360300c000340c10107140b800e00d050ba169003074100c944405680c042004803d011114100300350803e01500c042105180a440c100d039004d01c0034070107501a120b44003000e50641485070072918100902030086090008601c10005190301c04400e0680094641440c400103890300c00143c200700f40c040d16501d07002200c41d080140383c900024018421030b03040400c9000440d01c048180a034080486c074106104804180c0800c40b07401d400740e19201144540f41e80954003c030041141881d110b840c41c086000c05507610718283c1034030783c0c0c00f114003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 892813255 1250 892812005 892812031
    0x60f03010914060924190306060503030405010e0607110604185004111017130609020d06061505090a1202032802040f090b150301020708210f 62
    0x200e07402a00c42c01c00c8491041d04070484281984880402c4540d1002480b6140f8140351070307010702c100f02c0c5500a20001c0c05c2b00340c3c02541054900760008005041401409001328000914002400450365151440c040060456581c4503a290080e00401e860040ba000d161842c0043ca04507580302d03100c000c4890b40b010000c1058003003080740c500172040d030340d0034115604a030041c046042103841194075505c1503018954089891101005109040e02c52441031070801c40c8070744500003a441151001358100080202d440d01d601b415161090040c031200b54040e40c003000e10b0b4a034900300106a000101070b200400c0045001503d01e01e0180c80c18002c0122040c0d20070340b41c0405000c40b0320040f02d841c4501340020100e60002c1500602c2081d6507509101c60503d12100400f5402941024020034290031603d40c003c000701c030559100e040c08040041c140c101c0c110200c010030412981d094040d10355043e08441d41d1a6030b0b007402000c3c1054841543d6403460a46198000110300301d919008035803045503080090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 892814505 1250 892813255 892813261
    0x53f071805040e0304030b04050a0b0601091d0c0c10060302040606030605090c0a020118050c0109150e100216060e0909010204030c0b03270f15060a0b1602060f030109140609 76
    0x400a4900070480300b000e88405e110020108040c0b0b00b010b40603900403000b40c4010000381c1003403000341308010022810f10580f500100000490403210103a0302c41803640746c072215111503030b0030030551090090400c1d040c854001a2100350810b9404071086a00c201c0b020030030580d9440050381030b11b4480c828661300541c4407000940681c2c401e0014001c0b602944000a1a104a2281504003801d8020207880d2a4440ba40007402541c21000c0e5101501100803c10030003002c91400402180d849a02e690095048401e002c0ca014000c0003040340302007800c40f4004030785481d440700424800e01c00e28070503c41d00c095004117010590601c21202074a4104521996050a1201f2131103690310140040305075044800c1da500d01c800c4044420302da8111810064103040010102607031505803008441d02a0b01b41c036806008807035480c44030300c1c0d0480d810a048a51280c00141105640441071180a0340007180012146030314284a001107042e103511460030481c0820041072003191002c00c4882d960040d83c12008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 892815755 1250 892814505 892814509
    0xb010f030b061e0a0f02011a100e27100e2206021201080f0d0f2312061207062a0501090b06040c081303053f071805 51
    0xd03005084003901d0a80740007092483c0100409024950036840c400116144020982c46240024003165501c001e110307811400d0f001e11a40200d8614075442625204004850725000382d542d03050b403003001005401001702c0d90350702152100d40c114460b1405034010000500d0007552251190903034021809101240d512100340d4041001c2480c415040480380c3c540c00f00001d815800105140062181c8003c0654903003a9481d14007220a0407812840c0c101c03d101d2940c0551000010100c1191031802d020014a0050f0b6443c441a0f840c0c9610026000062a15000e9508140490103624292140486216074a0b0a01e0700ca28403030041e1000280c154102d50b480740030b403051440a00b181c08003004aa008650303501d0342140e24a00044400550000403c0050300e0176200b103a5103075659003040c411a2030070303030007607c0c44a800b06c1004007402004500442c07804141e4031038228180824194904039844e02c103200c0104a0340319004142d03c05008001103503e88911950b0040044030309840c40c0f46401c00382 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 892817005 1250 892815755 892815761
    0xc130f0b0f13080f0307030305061e040c03020c011a1f0203030105060d020d140a050c0a12090f12050712030204050f0d02031231060203030a020d061511010e010b010f03 74
    0x810911442c4008901042010080c07003280c0480c60842c004641d10103103894040c040e10710060105220340d10081142090300212600d8900c1c50070201c134000340c01109508103400901802c140000d4962a0824807034038003d42035813940062808a03502d014140c28020703100010580030308908010380041c0010000750401c2e2024001b944100c1c18058100b0142c04090801c036050340c081821703508188418011102c8543c070450750088000c040c11490301c08000409852000703891258243c0390340c1c0b0800c64090108400940715402d9110005070300d08112144003e106130448035003511218074146881c3d00721030081c17084608458005c0c040c2424602044108007480d06004000c0c1c0e058000c41058041e90340c40b6800404000103c41e079800740040310018008010f00d05a69084002c4031031031028800f60340c000040e40c0c1d0000a81502607901c04a80040a01501c0140e1080c408208280d5110000030f401400c0c1c10440c2030040001c00c00050524501c6003603a81494100303000c99585030304c40c002c80340b080d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 892818255 1250 892817005 892817017
    0xe0f030a081302090420030106050105120630060a06060e060d060b030903270307030b0a0213090b2d1002070f0605071202121206010c0b0c130f0b0f 65
    0x100b94408141464010441c92401250120f50410403410081c00401d0f451803a51300e2104180c0c02005074a0800002030310510482c181100f102c200d00c0e00003400d659446500807088816103214000e014603503142c1228200c1402030a031f00c0d9005200005107510746a2141c002143d5055446003500c800803400c1c40031603400b0b041e1400352592200d00108843c041c0000650091142d1001143e581e145212400b00300301c00e0717009030b580c46802c40510340c0d1543d070001041d0003502e40140f40d0078016100c00c14140f00038480c00101140010707a0f043d000402d040e00703520400da122002e482d0b0802c00310081004210980d0505030018581c1c00300005659241801a03126451041c01c1c0110750b100b50b00c032003416800041543c0402e001800001c1d081c010060950520400d85840703000810054080d510642843e0255801c0200798141420004031035070300c20130000d14410340102407800c142c1009540c00c800c590010704000001c0e2080a0700103904c030300c4c500d145030458500b103c980e41001170315420540554440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 892819505 1250 892818255 892818271
    0xd1d0a510912020c01020705030303042001170705031918061a0405040f030f0504060815010c0f0309290706050a11040e0106030c1409042705100e0f030a08 68
    0x500c815000160440c81c80405902c4030307400070060402070314002443c1c640ca40c1c00060180c2c1040c4244000070380c60f225210302c044034101d001510442e030000102d0300c0310403c0c40d0100f0840210702c00e002030681c00000541c0590300078881c807000b40780c085100c07100751600500c1c40903220a0b100d0941022841b01d50003080000e100f940ba00c0d40c80e910040000e000d0701c10641d000c0d954075a082d81c0c02801c140e00000c01813800d910340e08010342040e2605001500e40b0800811840010100740e4125401e6031213506031f90080346d448039140c1481401c42c10020300c445124001e4903040304141c00e1015034005401c1d19030100c5800140110310304903c950750040627110140a04807620b45442e00302802ca011800a8030161108543d4100349600d484001019505080002d0303003172050303c0004165908030b00013159031a20b4140c9000c03c41c1c100400502c44200c1140c030380482d5207034450112004000000c02c9a94502c0b074049c00c140042030340b145405898819111000c08147e004000071030199010300400f42c2c3c01005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 892820755 1250 892819505 892819511
    0x3130519060b03100b09190615030501230a0e040812420d05032b050a06050f012d03020c0f0303010f260613031d060d1d0a51 55
    0x40e0b003000489c4c0304164542031002c00c1c1c640c00103100d417400322610316103040558482c0980383c1c100c0d070000c941000a10b0040e00c400303402d07510002e07090003040400c031508200c07524290b112900d000c95078956522100c1c0d004032044403e0783e11528070f1300c00040c52019140c0c1540c0c190940c6824010401800c84100e00e030403a80c60106000c0c5111111503505501030f4140c154200b200c1c0201d080c00954100e03031006001c10324403031801400707001680358101103064800c42800c01c402c86e806030003441d224a218990180701604c0c0c594201103185681a00a043c0c050172400c11a4048801b9a038113607100d001c240510240c3c5201c10500700301c4001c0000c0502c00c8252001c1c86218903018102c292410a071702210b118201c00d00b42d076000020940c0c0000d861081a0b0b0075418402e11900d03100005403c4d03c40c0c42c0098141c50b40701c45809122424800d80c0e950320703000407400c4909425540c644222030300202400f600d0f04002034a10721b0a00b1400700c81500500224081c541000c1c04581c100300a055000c040e640140c030740e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 892822005 1250 892820755 892820759
    0x1030b0a05040e010501051302070314031f03120f1106150d0c0308090901050904020d0237080610030c06030c05040b0309070f081203130519060b03100b091906 70
    0x11184030f1005840c840300004281036041c102489010800f0070021481c60388100301c6240402e500c456005c2d80e10645654242e50780e03c460090104072084010310002016504100004115100e1f40d1441041200c2c1c0f6000d2200724411030075500030044040060310b5400290000c3c113081c1c5101c0b031110074198004c0c11242c1c80c4019843d902030b250040d800c1150180340c0024582558a4101c401e039004200c111900101071802d0b03400f280108540d100000c0c0038447d903014000002c240d45105500c120b00f000e44003200350040c50a980110381c010700c41c8c1d1170540140c80120740c01c0b440b26441442500d803c420005c04044c80c1000480040103403412587c10070000f8440031444807420001180112032000c01000740c6400d000ca81801c030300300769000188903030041c080241d0f44102c4005881e030140301401c082184802e5810120706024040d007110340c413091101c0a000400940d92b2180400030005d50444120b01202d91000c400c0395840c425080d40000d894000603d00141960f26080c0c0c05030704600030448139 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 892823255 1250 892822005 892822009
    0x3230a0608100c180503030d05331003110a050a09090612060b01020303101e120f060b010804032c0406080d02011107020d0b04050c060a031a011103030601030b0a05 72
    0x107903002d0240100369460703a88000c200b603842400d020712440415002c1001034940400079a4238401c0e010035182803511040000c03141184900c010701c4200a181d0203a03004030542c44814003074005403070000d10440c6000028980039103c0e115101c07050003441c140c1d600d412200b210036500e5800a000c040108a5009004290301c1142d01410004020b02c16007101c10044a140c02c906075007407242c4050440d80284200300388031051748001d80443d01c090321448000c600c82410b04010010b5074014090300b115140c0c020040001110341c007a160ba004100c10000c50b010381c0c0046030200d5040d20041c0c0010072100b494000301c1007200c044450303058010304020356a0042404107007598656400001d95030050206201515028003c42021000e41d030f40046c40e11046500142d90400d0129018003540c401400150810000b0040c42d01c600e4001000c4589036000e8442c02000751030b07030108140e59914400022941540142030503001b0484410246065595110045000b41103510459912865200e0001115 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 892824505 1250 892823255 892823263
    0x2070c050603040f231b0a150504080607080610030603110405090a050a080c0708060417090a032f0108090a2402040b04090e240c07051605030d03230a0608 68
    0x14840356000904200181d480c0d50514040420244605c0039000e9035254036500c8101f444151a00340458203036600f054001211680501e03004841c20307204920901a100350001c6210f0b224080840349107101d10925401281619841d10000300500c41407100c0f40187d151a400643e409038200f400c80d0b00e010341c07039100c0703610b020802f0360b042e0f0f50120000740848042d1170901241010340200401404107042907952003011801001d0390103080000462610840d0307540121007030003150840350318000890908012156000c4010780c0c42c096031103c00300001d90354020f520749407190a03048080c1a401c182605d80d400184600342540d04120100c56000d42e142d1111f1020303002030140c0d0540180c5a500b8510000c0495110cd400e00b00150301501241a41e0104410040011b00c4481600819511986034599450007103c0300141580910a0302610b40c161008081040300d00803400c403540c0042c0c0850030b078100d619022600030000c0200b840d10124001c2401000e0300261f8942c000200d50355035194250030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 892825755 1250 892824505 892824533
    0x10902030a0e0a11030f070605070602070809030d030219030c120b060d020a0c0c051203250c12111212070512070506090d050f04090f0b0619090902070c050603040f 72
    0x4d038000380b210b0000981810400080c05c1c1e1080c0c4c0042030706500f402c40180c281d00071000010308603a000038009082001d6030b410f5460800f005401c54030a11030035680035020350403641c1c408040c07495040582f400c491080c0100d028080040c0c5519000720b10b81c541450103802c2140e241031f0095020072240c03010301002d2005156402e410350340c243c1c1d00512840c1800403840c140d40424130a00f400f0420064901001c41203070344c54a401d2107c03160701040704100e20300415040c04041c1941c1c514520004001d00002c1c03141100364413031041c3c0d0034640040c208120300384601d070024500c0c0e68000c004d191038010b172241c01482280d00607001c031052881c4100e1200f44680c010075040714181c000009220b2001c2082040074401c20081c144141440003c0d41a051207004610501c80f40580b280000510b02e075507a0b1250540c0c28009e0906030703a030841031440c10030620541c0c49000c0000c0b4540d50016600307085100395082d41e9806841c4800e9140b81c0320401c03100e03410141c4190354980c0002940c1000550300e1030350043c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 892827005 1250 892825755 892825763
    0x60507020d02010c170d0f05220c050a0906080c01020607120e01021b1e120a0311190f27030b1b0403110f030303070e06030925090b06040608010902030a0e0a 69
    0x140d00d080e07106d082c5017a60810006039440310305120a02c030894030212030a0610032000903c100d080c2800f820726071210405a40000c2e046030342008045528481c0350454400d9032178090407642e12402c610012030351a079045454800003a00c04042c441c1103107058124140d1100ca0070000b42c10302c0b100e203d00320b882c0e0318250340d0342e2201e9028a81c021015407008101071411b01c0c80c0c401800036800004000600351080c0c1c11007804141c0d8418903d0f10f000d05240070740e82d10401040c80c91080e1070790ba10000d0603504804441401250070454031070240c00d0300c00c06604007a0480680f46152524582e528100600040e040158908200f40181c8010380210040d20040d070141c1c4c0c513500d44403085002d000035010700c03040c03c03800ba07001002000b04080d00451040d158460903901e040d9240d4078510b07020b040c800342403001032026100500420341c803c20340c0890f40075100852802c0150f04400c000300003c0d48100d00c1060041000480108101c00c044c0d0702441d40403214200116802040c2d0310b1190a00400c410102c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 892828255 1250 892827005 892827007
    0x1112010b0c0f0327011403040302060609090d0c06021305030d03023712020904020c06040c08150c0304060902090925140f03030c0d08011e060507020d02010c17 70
    0x20309180342007242c03541100c280703405540b90003d000c14005a81800e050b41c801e1074410021490031a0344103c0108103400e400005094a07818640750094403203900303451040c807402c104400b05041c2d1700049001c92601005443c0c540210409640e400b029402c0088a441d428011042c0000c0a80b018003030b417042c0101d01d58006a40e0300f0601d0b400c411007001c103424117666001e12a1620940072852148242e149050304040340040c01d98480c64020303200700100e0702d801c07074004500070031003100004400d40a184601c0c90031030744644076802151744035802005d1031306c240c021901080c000e414400096801038083c203404190030600c2c4c0c01040e4a820b06840b010100c1d8010a941c1c0c3c1203c025902404a10003500313a90310034a0f1402a82c510403512086509104050385910799180b513500308200d60303240c0c0c502c0060b100001d000b888082c090007024440e88140050007100205a2460383c00d401042d103007140c0b10142802090703024007081b2a80e03070004906104400140c0d02c0410311210003c5441c3c81c4003c5e210b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 892829505 1250 892828255 892828267
    0x625050c0612010e1003121101061a0a08010e070504060804050a05120301061806081902040e0412120b010c08220806010f090b0d02011803060203150f100905041112010b 74
    0x4c0030000080c40c80c01c02a400310414030000302000d070f40b038000321040d1408100440d40b40001500400c0d03540d101c15201c400c02044000f005031301e4806400102c000da154041d06a90320071941c07a2003541200c9000014004100504c0030074010a5101d400030702030001c1f42c0200c0e40759519540340c10102c8488260110002c80100a090f80c80501c0614a6001161440045d0724241010305200070181c00d89070411440c0e00c0b50820410360f030f41540c000382507406101c19a81884e081c040300d000c003100d4440c40001d0918000119060f203d000d2556071100681d180507a902302520b803860b003900a034412201e0501355007040741c8003240007000d042c042c1813100060912545040010801e524455101c0001c003810a140e201c01a80d070282621b13005a020f0808100a84403141c90384a01d03e10341c0c0000300401e20101c144901807100095452030040c00782d80d5014017255400400c150384c02c00811580000f00c2d16a03060080c4e08140c2c2184030001b08544510b410000504004205800260043c01110b2070200300c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 892830755 1250 892829505 892829519
    0x207090e07030624090b040902040f090302011104030b0f130807050d090f3803010303030504020411160f021c031106010f060507080c070906030812060625050c061201 73
    0x62580b20035150304c0455482c04121000c41c032141c0c940d01c40c50a525070366801d0700f1100d48890f00f104c03400650041c03082084220100705031005203a26002680158605520301c0c072421072100464060341d8121120b03c20b580c2d42d10990110075030b0010a281d820581c280c041000144000003c5c007009441580580340004880400402c50780725540004003c1641d16410400b51000d1240048004074000c00240005040300d0b032a06003e80c240300e51180e0341c0780040000700b8554564041c1d8011351003207030140504865014150802d000300740120b84000643c28000f40050407001c4d5031800700f44060320410308011190b904d500000e08403102540070515070703c0c1d00b441a003014450140076041600d0700480341820980001e04500070307034800415901000852a00c0340004204140060041c28014410b080c1c40b4a818640c98000208200c80000e040021403500e103050004d489403030212001c2d078040200a00d110001c851405d600c151600c0c02080340070310b00c1c0d07112072000b00101e00b07000400a50311b507d0044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 892832005 1250 892830755 892830761
    0x906090f050319050a0e010305060f0a0303020d020105090106030308071b080d021b070806010b070804150306050f01080c0901050708070804150801080f0303040f03020c09010816060203070b0105060a0207090e070306 94
    0x43d01608200040241010b03203504010444503000b0203103000200e541c2d90f00003061407060400d800c141c0c88000030300f0002c200759001804026100c0e10794020310154039005a101c2c00d0701c07654080200401c0d04000040c0c000c0d0300c591080000c603101080f240b4082c24031350322415526400051941006900069101c20b0000e54080181c55a0a81001840850318144000340c5a22045c01028040480007a52400f4412000c0070360b03025000c0c0711302c5c820b82031400c96009002041c540c851580550481900b09801d0f40c00350034410b02c41c15289072003a280c003c3d440c0044403642e010315030840d10703408144030710000f0178400409000a801b02c0c00d240428100307490400b408a01c4140c1c0300030310070380c484840b0a120f10300110585c1e41183e482040d03103100104514069060001840301c039500060107500000301180c1c00104035100e803c0417844040342e151101ca0498492051560213030115901d00c0c01080760f030909200600c20003a20744195064952211101402c4d60700d01d5001c8882940000d4042c82070000f644 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 892833255 1250 892832005 892832047
    0x100603060c1d09040f02060c070e040c0503011e1517030901110d0f08062106010512030c03070816020612040b010f08060708070315030609050601060c150906090f0503 73
    0x40c0001020b0011000111002d01c0200b0050085480d00001e004544a400981d0b002a520105035506180c84048a230005c2100311810382d4014040200091207040621540160201070041042d070141c400072002c01903d6512070040c2c003041a18000103120b044c100000702c1c0304c5001c3e400745580c2d1280c40001045040d482010311003d4010075614442603411003000d118205d181d040100060ba00c103030002701d41810400d60640344d1400303200c0006100c034000c212141a0b840031101408504101b6103c96600c1c069242250000d610420a0b40c010072505405000700c03800500141200b01c080d90b010540345d030069a444000015007006003c104540e980655015201100c80071750b5962400c041250b949078007074003c105101500c03000c204410321079009182c0c0b008000c1e082c42241550380c5080f4006184452041d50107016100001c41c1a0b2b00c80c0030110700c6280c003c0183c1c8070b5500c0e001158002010190400c8800560310704e10318000505180041d204c060040015584581070215a00c074154004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 892834505 1250 892833255 892833287
    0x18030e031002281419031d0f0d0f021b040608160906060224061f0c0c0509010503030307110f06040309030203060f0601081305030919170d0c0605060102100603060c 72
    0x1d54010404c40d0740100607070704100c600b0b075a1007103008203a04080c2c00030003100d580c49804c201c1040c0781541d070400002c2e00d4200f000c2000125103008242d508211007412000d410385005802c0003500312646034480c98002c6226000410005d0000da580032a03a11b01144251030040c24030304072000304810384051007a10b0040000e800902542c58902c0020202030380c2c00d0103180f00901c820300100d1415201c42d12070f5180c05c440c80141203044d50703961070060003040e18240c1c1219290a100300210346410301e200024100e6030060300841c1951140300040c0c07940001081003400c1481441c40f01c1c410303841c0070041d06000e1030081c1c551052960450043c9814a080144070900a040902c10302c070560360306c41c0d003e07540320245c1d45003025004464074009003548540150181c0c000280210040a0001810724400719030490b0f0410400c00d9a14003543d44801150010001143e901459a4003092950b040750781c1c04001441912210000c0186050444a0640041c1c4459076124107691095800400c0c504200c01d00f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 892835755 1250 892834505 892834517
    0x33030316030e090f310f0b0619030b0705030702190308060a0e1506130b0d0b09060307060e0f150c010507030e01110f0f1b06060f0418030e03100228 65
    0x30200d091448801004822800040e01c081c03144001440c405100142c0e42c002e03481e01e91241b6070b0500e610301d55000c1e2015441110019040c10b00f9448410750f0804403544110542101d6689080907501a00b00034192419030041c807840c021071302c1d05000000c607100d2003a1141c20301e40c2054000e010b42c0508075000b0310079205480c0c040c0310b0f00b90b00d01c9240300103804044071041c0c2d40d02c10001e01d0861140d00740d030050a0040380803d1165000d00c480d00059040002510800c00e1650749000f050f0b0380303080074410070002c90b00c021708038191818a810340120860000d030450881e000d01420340c51081d4406000200b00c1c0c1d565034180820141e15010707540d07007261004000c0c0007003840c0100c024018858050040c24003040069008401e01e51101130b04c00c805040428880034405403500d40340c80300d0b41280d000c1e2180c008048841c440e40b400703100d65110104400c101d24045409645c064680b0000400100d03032602c203012030b402e250202d9000800421034200c5908040e00e92040c9001d96004c2154540014404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 892837005 1250 892835755 892835761
    0x2130207060b0a08190606180f0b03190f02040b090a0f0501150509130e01060b041509030c120201020a060519140106081b04030614010e33030316030e090f 68
    0x290003e5100c10140075446000c84002175442c00d81d00810340c030350110200c16120a5031088110305c6500541900b040c0740d02c14030800e460b4070700f056200c08014102070307020010300d074003000420b07030b100d42c0100c50b01d2018000040c0302c60640005800c1020407640321444075103031240d0b5548100f141c09450300400505602d004500d00d0020098620b018442210340161503441d84409a4070b07070b40d00b1052405008070001c101d0305031503d80c000480d50250240c2024041d503021000380d554450300420007120740242910b06140d0615000959141c481401a0704622a28440c8004540c251113031038041d0051000c40b07031074000f002003808240c5000d00340c0701a141030301a00400200f6000103a1503882541e000d40070035004403c0e06111050301681c0c00c0075160324134000704074510290b5081082d0507103045082184990f03403840107000e01c06a130050728003010000e20000302c606914032030508140c070f00014180d03410680c4ad07039144001e0364600f81040e00006e00b60220b03d82c25041854886800c80354241040007149 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 892838255 1250 892837005 892837019
    0x3040b1b0313032021010914060714031003060b120d030e011d06040b040c12081c090f02060a02120c07050114030f042009040303050a050109020a02061f0302130207060b0a 75
    0xc01560704010100f00450400510302c100b98000350626030b00c44548d101c140607030054140c2e034081c100c40e0003020030780310314940605030601420b42e4890b001c2c8034001400181541e8424002d0134940120940259807200d400758010000e1201c89001c590940c2c001442000c80303244242918580100c8140d90071146259034080500841d01035070094101c1c00484841c0c4842c0340401c0b014547d640555100b18040e4840810090160020500000680060410400b940365443c00b11034007880c0042010144000f00e0006040400180804031482d00603034002010113910000c0769480895540344036049a07105002641c0c2001c48580383c003100415190451030012143c611032400907201409075141045800070a585039035508003510400f9009003c1824a441c0c00f07405010300750f580106240c180000810902c401e4825118a801154010310312500c1d0f070901d8290300b81c172910b1410301000c000034002c00541c68000c070042d01a032403c400141c3d2507006051210441e0002d8002a1250a1140080003d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 892839505 1250 892838255 892838269
    0x703020a020415150807020c011706010f091a070501051612020705010b15090a1a04030312110f0d200913090c0f0513060803040b1b03130320 62
    0x40da0705030703000148400d12004240c110314180d88a100304803071540c807040956600036032290051109400310742d00041c2450040d180c5050200b01030071b44c40000400600e07298440d90602a6112450408080032903da12124208039113031556005629070004441d01000b0007407107496400044015070400c80c0008500003840107940300304540c103c81d00440c0704401c1c030001b03500010804000400e071559258901c0703c140159080403402500c1070340035010029080c1e800030b41203002c00d0741502c3c840c1d1420b0f00f955003e460002511000360007036550f0390703220f0002d454080300400600e061804407944401c4001d03004030035100c05600b0030a40380038006008602000d0a000c0d14620741040311a40c0602d000c1800b00300003000005805000440700b1840091701c10303014a0441c050307a1007913032031036007100d0b00c480b80c442520558441c440c003560080004120b10b81250340580000301d4541301c00e40c2000158503150b440c2d81c104681c030000007455a003040081000c01808181940e81d0502c040340c101d00c40c00300080740 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 892840755 1250 892839505 892839523
    0x70b03070e010c06060f0e0919030f0507110909030c06071e0f030f0912030e010b0603040204050903160501060513090b061908060c0a0e010203120106140d0e21070302 73
    0x1031210f00d00e004000c1141c1c94110a02402d00548003125465841d5102010f00c0420780b204890b40c0a01049084074499880b0350300c864a07016184c0c00005100c8a4040ba03050384100015205082504042101542c400c01c299004000e4080119140c0f01220b2285081600107400042070245803181c050310111041005501c1e11010704142c6800c0721405c40580180c8003c0c101200300900e003665001c20003807820820801002c8a9808001e0406000156400c07130320080d00702680100c044c00050010303c1d1540002d0762242040040d00d04050740d00c912600c44905010080300e9594407244288168180000b00102c10002c044c020301810410b0b482e1059403541c05080310303026100e42c042d107906c42c034142240c40009100e000216101c91900160fa076095801c0950501c1c001040d601d69442c0540c8000b00b40d90080d00d80c1120300400342d00e002810b0701d00b00302284407149880d20520200380c03000320500c038901c00b0440f4100034049490004c40c0020385100d800c03228482c1200240132140c04280c0c00a10248 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 892842005 1250 892840755 892840757
    0x106020606100e060307020708010f0b011d030708060f010e06220b0a050a090218040203040213050604090b04061e150909020f030d020304061e051603032a02070b03070e01 75
    0x1070740950030507046a8065900340c40f16003088000060010046e030005111046a402000030042c480780c010411054800800615002805202c0c5120740b0b440114145212858000c00b2182441d94400d0164100042200c078504d01401c16001001044c404070b411a600200c1102e44c08900b0308881403641d1001080c840c00c0304265922102c000140d10b440a0100c040c2800404075000c4658940c1864040e600c9860490303c0c51025009a25581c1494020340c0e0150380c1c018160800282e252513144001c240082280c1ea204d81c071254003001045e011203d0b42c1c065400b80ca0b0107d101260054001c079080141d404114080e4945071004042e0700e0748201c0101036842e000070229103c3c4031030001403450801c0d407015980c140541b540004200d40c00000034011101540c840380140c0b00e0f0f0892510748182d03140c4480b17011030010407090100d181c0341c59000000360b20074280000d00807240c44400c0700114941d02002c5200d00e451451508031501002180c00520030158030740e14501c2c005c0c00082c408843c0500080c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 892843255 1250 892842005 892842019
    0x402091008060d1704140307120b09101401030515070f141b0303090d030606020705090601180602060a140108120a020a0b0f180c010804240204030f030908060106020606 74
    0xb07000c0750703126000c5000360f6030060006280c5400704129080280e0203440b4131410f1003180228503860782800b20725070045071059030800182c003a90751140c000b88d400082c4164003a000d42e0070a940b0420440c03182160304844002d45840035030441c0340035440c020701d450040889041d11004c000e4030a502c000d8041090040e8030340869681e50211b10030416009802c05100603c0241681843d6803030000041c40c8940300540c2101c500c20f52020003602158098000ca4005030060b0000740b050b030506218280d042072047c50607180703644900081c2c19186140b50481e40050700081c040c00b400070598010801798104010000e956075240c08507031680c1c0e0b00c07001c0f55112030711008604452000c1c0280420319900d070304803c5809062510302c070141e0503144201c40200c1b0248071110030030864600011180c0c0d80503410b84a0001c25100d603100c0d191a041c08400c8040b505480741100d02c0c210080e40003420007180324140c89800c0400c2840d0142c80311481c3e410050881d03005000408c045030f80000e07a143c000b541500c000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 892844505 1250 892843255 892843261
    0x20108070e0a2c0415050c0c0706030507050408011a0316050d020f121006060915120b1306091512080307080705160302060723090402130305070e040b060402091008 72
    0x2a0000f04600d001164030740c01024100014440100c00040e90f403249010100178683e01c0360780e0098107004001076030050b54442101840064001d03071255030001d0103070400741e082582c0c0b198110309481d15130040d241241c02101003402281410006102080f60464100d100c042c10280403a0940d004264007a01c900d0040c10080c2207512480780b2130304000030f254250b410010160403840080c180c544120b800180305014001746c20207a603810320240040710380c1c031044800701c503070120000360000090880d801000c21401e080c0c000b000788242c40c0100310b406004502c030a00d414100001141a51100c0f0404030300d440c4c2080082d00740003c8940c05409810300345800c0e2240c550440d81801000840d28540020501650500d6000240039100c1e8406640310103622040c50810f94080f41c00344c1181d1003000c0700340816806031510b90080c01c441d840c61000300e440f0075902d0700c40c0340c40d1094643c004c4070840c40800900c02840401e04a1769032211064500350b03d03201205000c6101d45410402da042002448008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 892845755 1250 892844505 892844549
    0xb0f090f0d080415120b011b11100e04060b070b040b1005041109120106230121020301230d030c080931050411060a110f010603020108070e0a 62
    0x61200c4441c0c0101c2107646507512214180444c280440c00c0c44003060740d072008441251002c0c001c818803010107a40f00c1010f0720b42e0060810181c0080f46003202d1060718016001042e40b500005003040801643e13035030364171214040074042110182d030400300914008000e41000b00b2000d105c03850308580e00100c903060701d0303482a014003888030a580100c0e0780705040c0408006822001c1026101d0503d048840b43c0c05d08a000d4200c81c05c0700d48a1040c0c400d042c0304542c401200e41e81802d100750b004101070511030791030034010800321205a81d80240c0040b042c0d001c0b0045c008884541e2070310150344c0060022911460300700000424180c0440401020044900707400d104000e158030503112a0180584002001c00322081c001100c5110a10942c90188000340b21b488005045e00030b4070301403500042c0f11600c550340c0200380a0540d121401368003c0c0141904030b0405603e0410010400b40403a000004429055200042804901510104c100f2200200444581e642c0d11240f50440e501d1102403407000c245400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 892847005 1250 892845755 892845769
    0x7110f060c16060f06032f010503060415030507140a0b04090c0306080d09030b090d09090c0309020a0308071205040e0a0905190b0a140f1302010e09070c0b010b0f090f 73
    0x440200181e0408032229041c0c800e1750080320603284651425488000d610b40d841c0c81000f68a01d081c02d0308915514202d0040d40211300450b0001c03800361001c01c00700b289038841d00381074400c0d500803901540b01c40700400400440101301d802200046800f1038525241c0b036120500340c001c85c029803000383d50358202007030710700e00a07481a0004d0060301d0655203082048131016104203200d1000b95a50b100d841d0010355020030100c0c01050800303040c1c417051984da080040010017800c49011050034503640314601d0002d03998100400b4010f501c41e40790141c1e501c217280751003040f40f003407100c001c0c00303201b010f0009125901c114480703070394800c0002d1030000e002c2c032440c14850324010903403d80b43c0c4200b1082086038140040d043c0310901c13a0001d9a001d101042103050303030300c0f0b44640443d041d856030800c950105002c0003651000c007980d20700500d00f001d6016076450025105c03010550786034000c0707080c0054442c200a000c040301c80c01022182580c5040901c0c4410800d000d10800c1d0b003d5100f00103081e5440175580d2418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 892848255 1250 892847005 892847047
    0x305010c05271c1401060f050a0603050a0213260102090d02010509030a080a0509031507020c0d051f0903110a0b0703020c1c020705090a050c1204111807110f060c 71
    0x3000d60103c9611501300f6521040500d00c159405500782503000c10b00c034802c050140c0031a20064040d01c0032520700003045000348000b40034150340d03d4082050080c00500101004040c0c09200410002d9840300441110015406442d88280c0d900500038504140d654115001c1d0440d0282069547c9503403000010b0b0400c01c03141c4c4000c118020202c0c0b00824207900c10045d00d12101c0540441d51301c0c40756000090400030080718110b006921558018071181000c00c400d0780194480e20403100303e4010711200b044007004410030504440c1c1c0c0c80310304405169000c0d81003894001c1c04000f60841a883d9283c180603060001c00c030800b490780018190300108010401000c101d031105150400c1c2c40d607242c030001c2d140c03800c1d4410170f40320302540008038000220a21880303001e1003600e0012071a04440b0982c008641000801c03e4a02d0401440940b1180d100c00455414481d940f00f00040705190100d0054054003c100e03441c1c046134080803083e18010000191a500003c07050f60715519030f45c5030f1906031642c04002e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 892849505 1250 892848255 892848289
    0x8030c16120305070207090212011a040b0f0a09050906090f090307020406080706090b0c10110c01020304230a0f0609210801061706100c050709150305010c0527 70
    0x4018440ca060785a8003c078042c40030740e801c0d6002c103607030341e07070070b60b09900078815142030405400d00100315611052140d00003030319000d6a054286a81d6040004081d008a00010801d2400145035070070554030070b0380580075080848602d181e500f004030208098100041194072111400790100304450020400d5544460740104240401511088450344a208a10501012800704030000c40d521929a050301d0040d99003030001c0280300300302403510b4041c02c80814550918281004040e04005080c00154496030289114884024078045085122035403960501c203039030450039180d03000944903400d10b030400d90400004100207480341444048140340d0303a54644c104580038001c1c0a841c4d00414000d0490300951200c5e00500c07550285140c801718100d40301540440700c281c1070246180100c12211000d03004100b100d80130b07a2100301072401c0790303100c190340903040900c00e03020410070609011305090403450b440c12a007007103180390307800349842c0030201021090900c1410410440d168010741c0350020f81030f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 892850755 1250 892849505 892849523
    0x30c0f06021b011b020304060f08071707110d08060a0909052b03062c0a0e07080a0c140105030f13060915050f010e01090213081b0a1208030c16 63
    0x10b4028000c00d628105002044215040c0d00c3d481400403040d1021a41030743c864600d82140e0010480319544020032150604c4481c0710820b00342080c040b0b00ea0b1241c0d100b078480c01c0032004900402485d15040768504c50410191b001005503d8444031038201c120340c80c182000c11400211f2410a040222019450328820742c09028510302c0120040401490351060320100000d5803a01280c1c00546c0394600749072588550820804020740850f56080e034011407299002615000d040c84042c00c0c2031041c0d121082a034091a010340a00c12810956002803e04018802021462000103006404000c14110070300c0100b800003801700121a42000300b03994010410043c0d078140c1d1812082c010308070051070903040d1504c00010446403451604c64140c2e03000020354075082c0e281c05013a0020358080780404006801501c030001e12804100843d071301d080580040312050703800035806d000d41d20344582e1041c00280030340c04030390011415140481e504400b070044401e650b1105031201102e01c601c1c0400003029074403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 892852005 1250 892850755 892850797
    0x60a060905010c150509010506120c0901050105211510090e040f051c090315050403080610091d0702280b0a060b0c010b040e1b0405280204080118030c0f0602 69
    0x65011621620007203843d03a0b61108583d00ad03680d00c13898007207c6030308106000018803056005401500406500954051140450300b00e101000d60055802c4013400010b40060040f81c5005421680b100e0501d14000d0142d03807030311204230b0381d05030090000340882250040001c288001800800080d625004101c070340403100741d01c0240031102500c41a04c0308140101800c2c28110329005080c01190103a03620030031900c800042040e404410911f550500030b1201d13001449503118a035500343c05d01008441f94107458005806400c100090b40b11007018400703c844860382e503500c50703038401c0d0141d00280108203a903120848100104441e4110340003019010842c1d1003060f105400880f0a040150b03410b0003103c60524880b50350703c002031081c10000c4d40701c058060b06402c0c10f40c00030703601c800800003040c4480643c0740103041006110004e66200f41c2c0005040c0401070090040d030400d4401c10440560582054030700410441801000412080c5203158207804c0c000c164040d100e0039568a22507400d42c00b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 892853255 1250 892852005 892852021
    0x10090b06061b1219050f0723010603031809050403020604080a0509151810121808070305030a05280218031207021e0319060e150708060a060905010c1505 67
    0x2410140c036907402c1c00d44464203551380e01c1c420415114054001c4c260f490600c891aa100c0c2c94002090003415901c800c8804001d41d060000d0050000440c021380b10404090070040030442c0c0c41d521074000050080c140f81c1400700003903000401560040c0c1085015440701c0440408a500d4406d4841050b402051a500040001c120070010511400c00c00c86c8081c022400c5001d1103200c1000307448110101d0b84400c1d80d0968407032181c00c440c1070b220051007500180304044e43c40c1d456a820980e400c1d400980302004100150400d8481c290b00010900900c0a038002038010a413980a000848802000d802251040c4000807030321283d01d02100040599000c50030b1000000c440d0b030000c0000380e100d40c2d04c4100e807140b060000040f5110725880a0080c01c0b07e018500c444c0003000c0e40300e0b5000c5848d1a99044072082e181c0c414440700140d0810340c0f110600900f0076480c02400030001400c01c2d481404141c20070040c81d60405000c03000c0302c1702800c140e42c1180590419030b50007400c0c2d140501500b402e02c42041825 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 892854505 1250 892853255 892853257
    0xb0906013005040c09050901060b0d0b030a0c0e010f0b040b091c0b0405011b051309150b0313021e030c01200601080d09060c05030405060313020d030207050310090b06061b12 76
    0x15030081c040c20410f039030747c0800c8942030341d81078032520070503803c00c01c0400800032054000740e0003501c001d82152105081c5650351a01c040072580140310700c10320200144803030349142004600410004c12110f0800d0b04001d06500366200d2540b03050712501464411126000f03811702c100b03201d5500b090401e1550315040c00e066000c0e01d0f524100b4825480c180b111b54507014040c0040c0e50b01000828216880c0303900300102c02d0000e0011824009040c23983c1d04001420340d4440005500c0703000e10103003c0c3c4588034288103002210103111a10305481c03681d10380b0034486031000185030014403000d10701460080305076500c3c00360100000100507901e0041600101d428100026407c40c0d00703603190340e4120182e643d804222805040d045000b4100d4004000400651400d040990303005200212080b40d10203003680040c083c140311000840c051703045500100080d2409100c8a40e90001030801407200f443c0541d00c2c42d645030401010a80310751070214007141020940040c074080c0380d0b4814112840003a414141d950a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 892855755 1250 892854505 892854509
    0x301050f0f03061f080d0503060d210309020a060912150618091202070e040311240403020615061b01090c03031e091409090c030d0309060b0906013005040c 68
    0x4500102c034000501740e9400100b40c81845040e0351880c0c29030322044104420921a40320a6a603004a9509210300c84548440c001071a000e40e18001049100c61051144d01e400b0f50b4403e00501c030301c4280802a407000703441d07505162603000b003182c008120002a000010422500701003112081da070284810860107174006803000b07004035501d246c03031044800100d0740d0301030b0303409003441c42142d00020400090041164000c200d07842001c0d2075442c03c0b250701210044c1c52800880c034414961009103c00d058040c000590050300d144041d8420805180102c1c07c40c1c843c607000480c182031141504001c00c482036009541e8a80d100003e40300c1d0b595241030080c25050051081380e18a2800079580050714015880702084070070f60788506030900c120004002e40b120300240800f01c5800748024800d11603800340592508907002d0340307000900d952541405001c0342c03901c0d500c40e4080c60031001444007a0380c206190f01c3c82114014400341030001400d020041410919083c03122150800090200f000008500002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 892857005 1250 892855755 892855801
    0x21c090801050a18030c0302120a091503090302070b210108011b020102030910092901140406080705041e060b1b06060d15142a0f0301050f0f0306 64
    0x10454031008210002c03901c2d21480011895804000000020b00500340105503a0184c0140e0300310b00200207271020340c1d034021004d000004000c40024030480703d0901c4112152038007441c00f0401e85503e5036001e90349103c2c90103541d40c060808070f5401448100d108080701d0391b014100d1642c1881d44d40d0211076010300900646820304800400020003035904c14800e0b2440703000c0c4d02d0300030304861420030b80000081c50944010380c0c4190320408810f9400704200700302c00340c0d0ba05591100040c1d40c50244107804070006241e43c00e00c00c1c5e040c014204282040080d2590984400700d800040d110a0240c03060344109403030230300c02c894605004000446400d607a000d861071914a40400e0301ca8400302c2e1010b6210380c2c0440e0a0b6074000c0741d43d00203c020034101d1600e0300c40c12285980c0010265400c540107840e42c602112481a20604400c0c424852124005420041502400844d0078a0501421000c40d40014011580118802682843c1550b41d240100313210000c050280c501a0a00b081440044284801200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 892858255 1250 892857005 892857011
    0xc041e0e0a030206010824041103030c0c01090b0a08040602090a030f0b040213050c07060b03030c07080c120304030b01140a03080c10060807140603091014090f120304080901021c090801 81
    0x69000740460318803240c00312942050b8005940d1001d03480940d00c081c1c802d49030009227514a41c2d40341c50400007411b41d070854400800d01201c907000010600981a0001b8820220502c540101c85030051496500258000405a1100c8802010031400c0300c090380087d1682c00c03001101424004401d2199000d00c0c0261803c800b401e004281e80801d80e201902c0031901484100003803004103100e644a5003d0071401030959152012409015140c603505412404080c1c111140491146ca4604036003110707280d80902650600380347d901c8074813807848140309000110940c4000c0364241c0c1d44d00707608800a96440802c10307460303002400005685040344e4000701203051600a002c15124400114207007110f2070075414440c40b09004040c4000754001612103000361140c0794500480241718000c3c00d40034051030040043e81d00d0080038140c50308a00811070b007c25006042c1000200c0d000000300c81e401600904100e0b0b0f100e11a40040b840e14511900d45003002d400c4076006c0304080c0d070003107600040f5840f100080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 892859505 1250 892858255 892858259
    0x15031f06020a02011e022d07120c0302150f0315040c02010b130209010c0609050c03100c08041103030c101d01020c0304091e0203041a070e01020c041e0e0a03020601 72
    0x50ba40c0d02034000c80070b80800c51660241041c5080d1400603444550988151020f24408a50302c01d501d0038188400f41c0210400c0c0d000400c90581040680000c100e004840903e5000c1501ca46540320402c2c08060b005140355440382040c0c6c82d240040b0741c180845140c682d81c0d45d1801c5401503c8019101900e075208909242c03c04440c03620502807641e002500500d003c80013140310074964029403184458606120744051079002154032485020419070080010345103120500f02018144480d4034241c112a501e46240212201e501c00203550b40260b2002c205112940f035000001e10318010099645041c2c07140c80030180018003140c0018088010003641a002c900b0440e11541c00c0c0e01a4003c0c10035107074424803080041d540030360808034043c0004d40a07002090340f4911700e2002c2c1c6c0e100325419500b040b6541d5480b8084000e0350521a0300030054034141c588040035100003521805081c00c1c9030320407901c0b40f10800c94001403000a400e400f9a0350030801c80340c07031000340c804e444510140042d40940079902c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 892860755 1250 892859505 892859507
    0xe0f040c06111b010912060906200409020a1710050108100614090111120702010e0a03030e0d08090a08070821040b0705010204030215071b180b15031f06 67
    0x100810b207411076018082c03d0040e02c0501d440350f040c100c1030394100200b071400013504040c02280188824002d200210b10b038a594103102d02070702e218500c103071880b140070702443c09610b403620180c50a46010010140e5a50320a82c0c0442d0131310078850a01d05e0750306075001800800d0f40c546074460f0481e042a02d402c0503550320001d1041c0d18403c944500c00114601400c2d400403940104010089001c050400004080b07440503003500d019520240d8540d20040022100c040d0340c1c000030402034200d0101c40030400c6500b1a64001d00c0450030070011406031660804402c20401000c1c04da40100300042d05a41060b580c1c1c6101c0c55560390240b081081900072132040f00d920a41e801215100308510101d010f24283c508440300c4c18540c00f05000796120355080c007010005907030f041251440c00e00d20480a548540c540d04050745040d003404a143d0400060301d1041000244400c070718207014000b8040020009400d001040c400480e404002e212188004200318640c11501c0c0440c90000b04401c0d00600d15031a400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 892862005 1250 892860755 892860767
    0xd050a02130602120a0819050711070b0a090603050711030a09030201080906040b0112030504180c030b09220c080703030302030718060507060509160305030a030b0613090b0105040e0f040c06 83
    0x1a9540501c6010040520103d0180c0c42450f00051f002c21002d0061191a45201c201c9400b034030b03104000b0755140d03244010f03800f0411600001d011400d11840c174298040d074010740480400c3c8984414140c8070300002d039802c1d00500c003103080030035918103590740c4000041000703103a8000da0100320f01194001020030b41541000401603c940c0d07022580d42200e9080019001d010f0406030400c40070401d00b0440031030201e040f00000c520402d0036a9003c10031080241025003503541c07030780185004100040400540a12084d143d1010380010003035070700102c031182008138010040d0f41260380d45124040c000010580e1550013180b042e40c1c80c0d51828400800d00d030000c064000641b2031a000103805000e07460124542d544210b81259510741100d0209100c281c001140c205264800d664030740020911044941d00b50082600340c007006c03940316292684920034551514028021801c4d040d5880c403080143c0d0340644211006000c040032040c00c54074103003512543e4014111012105001102d400080c1e584c0610 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 892863255 1250 892862005 892862023
    0xc07120203030a03090807080c1b090412050c160e0723030f060f0301050718060e0a150203131403100b06071b0b0403051e0a021011030d050a02130602 66
    0x14099850083d411a00f01c010b080f610340150f0300060f007005401c0001e60300340014540d400e00080601a43c281001480c0ca440d051b582c141030107400c50314100400203a4512010f8403104040c10400e072102d44405000c0d2501d810288088210809544003044070f0684c0e2008500c141e01c1680e842c4050701000c10704965002c907440035600300380020b002040c42e500903007040c0c070380c44000175104095410b6110b0000c1c0c2034800a440d030340c5c0440c880000c041031b01088080604c020b4009810220090503203070003c51203000e403a1103014911800e000005030014401c4c0304860392a55041000021240c503040801d081d4181028064402e2050a00300b42c0a501203025600550400030001030a208441e181c0e551418060131400000e9184000c0102d040e08544018002540c02000207206403418600901d4401c802da030002103007035022100c2400169510307414003510181d039241c0101c0c40c01c411a1910b2441c018811030213920fa00302010040d8036542075016001d944407034802e0b23100a07941d030712003a03894640710 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 892864505 1250 892863255 892863259
    0x305040e25030b0103111603020f07081b061306111903120b030709050c1b0f06040f0501060902070f050c01030c05160807051506101115150d080c071202 67
    0x1c15603801d4900903030002842e458181004240e00c044020b282c2203d90080001340d02a00034601104181541000052816051200107000345030614030901e0381c4d1440880c402030a888244c0c4903001c0c83d15101c01741d6110354500a003000d00d103503c6071005802a1959252500c2d244660750105505040c2c060701e01010a4060b161802e40f074034400001c501500303a803100790b605441000c2d0002031001085c0f141c54400c4902d00781e19901c0c0d0310310701500f202808810a001c4100d03030050380030414181000c5901d540041c0e0000c0c00d500b1404292030310a01519451b4000c3c00514030102d848c1c414010040b01403049144540140c40c10144950010340c111030040e103407000001e00c03e02c60b00c06904000c2c1e208040c003a0068464900341240355550620f03001600c0403101402040e14103000c11410400d04101001486044c0311000c8a03c4140140d07845000f0794200c00c0c01007850020480f2800101c0c0c80c86504e03140644601003040c864100240c86501c1821100014491118000b0324103104590540e100da0b80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 892865755 1250 892864505 892864561
    0x50402240901030e030712050d060801020304050c0d150903080105040c0810060f0e0d0c0302121f0b15070507031704080c1e13051e060906090c160305040e 68
    0x1c80300110000d00c0c0307080da01000b034401080440301080340780507200390503001c95452590f6040785452807015207645a01c180d61580c014000c0c403000400100d120403000e1010b8440319107610545c1032103542c001c18801810807040c501400380d0706040c1d005a0490694600f6141403050a07401c0c082104d10071011a2400c2094460b140e0030f010103442180000c0c14500c6500d004401d540b096000111000144001110b007580c41c10310800460610319074811300d0340780500c0540240e0341c030503002c1d20840c0c8098146452440d13403660040300c0380ea604404045203a110900031500d5084070b140265407140c96020603541007010840036a035a42002086900340c5031114080e211540300481071010b00d40500310101d0016000c070223000c0d000d8641810800c1004d81805000c50a0305107070440f1b109505600c0501d035080d900310800c003c00c0d505ca1070744ea550070100503107803440581e950369520406030040d500c8162010401141120516074014050010ba50841c000749080340c90b100481c80c072448070148040c0381c0c0c1e03003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 892867005 1250 892865755 892865767
    0x1b0e0306130302011d280503070b0c1c020d060e01290f030709060e0603061e03100e010c140c120c0a4103030109020c0f0a050105040224 60
    0x808140c03048000e51107400081615218403d00b250703c00c5035540800180d90060786c40e90309104514180c608a1103210780c0c6078501081030b0b1039185d260322407107030007800c1c070600b84c004104000601e10803245d0503d0301c0c170a200243d100884d0104003950120b90107800b0036080035000f00303880c2c02c082911812030702e40341203041d40d0314140204814120030805400c0241c800600c400404815108000d511400721a82c03411082820050050029030910f0380c0eaa0080c0810301c10041983c0b102c01040c0c104002e541d1070500d11340200e0000a24258500203101821401c0c03407152200d41605400c01d400c0f581041d1944a0340c0169148440884d000c2c817a001c006640c018010340110b071410324000c14020a1100981c0c440c6011910350404100b4094031030a00c112030032194040c4d00c2107114104c800758100e0101d0001040b25021540e507030b40010700402030050b0380083d10400c555401c001d01d008080f00348080d183ca82c2262b0070800d000b000212016401882c2d81c1c10102c0061619031910500001d8420450781455 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 892868255 1250 892867005 892867021
    0xf0f0901060e1311120d0206070e010e0121090303020c0c011d0f0a0b070c090506010f0e100c060f0c080c07120815060c010e070b13090203060f0909011b0e0306 70
    0x445000029521080c2154140c9130740e4952003484041c029509004240036466004024138105004044508000c03840950401c0f0740e03480310b40d2455001e000d00c2c0566a0078030446840d0050300c5180788543c100d610302003c00c000c0503010f4014000a161107401c0e10002c007005001902d1204078042c135000d9102b01c1040c500e80354a00100342d1782c3c546002625098502d616043d5980c9030b544049815289010048030400c0300708240d00400e940300c0428030300b050b40011018000340c1960300c078500c50341c85100c030344040c910380d00c0c880c9051182c1c40f90810420b1120011400b2400001c25201400c0d2000601c01c50004202514820031a1041a441242c001e5102520b030001c0f1580c4802502000e05094180c40c4945540d5945e805410340c4603041c00001040c0000c0c44042c0d02d000800e80c0b001580080c24401c0c0600042e215440600700e4255110260703603540d964000600d000302015210340d00c540507e0500210450540c00800380d8500c000d0902440c0b515014251000018110b0040e0b142c0d0040000070030b14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 892869505 1250 892868255 892868281
    0x7060801120f080c100612020906090712020a0c050606100504091a041d0705030c01090324060803071104090f02040902013510030c0b030408040e0f0f0901060e 70
    0x80e004400070111082c1c0c5984003c9203520400c00400542c0c0b007586203c6190015105840052406107010000c40b90769501149002c6001004e183c0704660350400038541a005100d0300700d0760005000d0440d514603607588090a80381600340305840510a8400051050404c60b14451400707889440c2c9a05280c582035a42d0054481e0101c00c0300807040401c15003206488a000d00035401145049102d101458010310519040e004da00c042d20907402500c0040e8266005181c1c00141ca41000d40100c186d440d080011451002c0068008541c500d840b50018500728040060050b1622400d0700508103840755041000f500d100503409000c5040003100c2800514081d40444121031041c144990900c401407040c15240602800d86000b84612803049401010309a0100c2c3c2e2241c003800c0740000c09815500c9130180c9450740d00034030f44510320000118060100b90b8050310300804c03034900c0141c1145845000310010301c00c185e5440340340142d00c901280f1001c006001391803d6400300b00d88800c055136039a541c2001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 892870755 1250 892869505 892869539
    0x10e01051306030606090218031c11070b03040b01061707020d08071b060219080c0a0e03031b030406030c021506010e13021215010912080d11130303090807060801 71
    0x20701e0342c03144000005161402910000c102c0700740d005032100c00c8101035455071106c03d00740c0c034460b42202442d4002d02c03101e0150403c2c612550b140c48010b00c90540300442c43d041e9550020070f11701070701200300000c00c401103051a0596110390b40d81f61100c00d0010f9001c01c1402e080c1d070400096000030349000a09072040e004154004001d00c1d2540c0310003508041e18425040a96094034081c2c0c0020f19510314a1168403240c1032800c041c64140f80c40c0c90321403d500e403503000e50b44001042002e032580e0003055550130402c0e52005080e81c0d4080004032611000e581d540da000e8440e03c5c011a00304400c400c41c7c24004146043c0c18501e540e1170300110360340c0c0001140c1c3c3c40b2012000a60040360160041c1540c1300d94409006a031400c015042458105004c0161815551904080c100621414140403080076006481043e9502c400d4154640c202c0d1070405024101c0ea9003103a06580000c20100c400145021100007100c0c00790310f0740b0b000c0a4450301e070142c881980b4090400441c1c1c5900040240300303034041000d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 892872005 1250 892870755 892870789
    0x11100608030309150f01031b1707032d140319021605060703020d0f030e01090302032d07300c0209181906020c010c02060109050f04021c0312050106020a0605010e010e0105 75
    0x111081e100c80b212020349d040310502c070081e94492202842007262502183d80c0342c0381d03094815040c0703114081c1c0121496140c00d0380100b0b0144c0e040425030f05800100240c2c0c642d150758008051441024000095841c50a2441070010201c0c03038000040904128045075446601a0301900410301240419110081c80f00380050800d0340d1840d011903e19000e21400f0000c40c81b90b40a50780d210b800142c0450006c1c4000072080030000301c1002145000c841108132400c8951100103500b48031003040000e0368200d0020201c200c08161980501000c0380c3c49000034864500c01c46500d2229201c6d1000349145450041d03c2400301e600948407802ca0007110100c2505051048a000d4a080c0c813100b00242034030300060303a290140e4860350040c06680514001c40341d01401c452544080d134a02f540009007014521742e2001c010300c000c102d005080c1807041c60b001520b45419101817105503500e400095a41050300c9040e28244c1c0f50100209004240320600c9048a50750002d07180030743d01701801c11141c0181110680 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 892873255 1250 892872005 892872053
    0x2090f040507150c05100c0207031403041d0105041d071a0906040f0e090a03050f09011b030e01111605010e01050c0714040b030d0f11100608030309150f0103 69
    0x510401841c4480c030729400d813036413941004109403a1140c542100100601c0c1814101000c8240060307000070341400701c9421140c507506540c44254135609610460b08000400440c0c01d00b0ba101a902101416040f1002540c0400c52400c0382c011500e40c01310a0544608550446c1e0b000700410040141c2c000305100703a09480500c0d150000000130015409603102c4098400801000c00005030b030080915400070001014100c0103000b80e9004065105201a0114110300401d4001050344076201d4000e00c0608154141c24209880c20081e00c03040701d0704d03502400141011078100308150007107900c82d640304039902e42080040c148001901d40600030020581080003d1000b07606130340040090800038080b40c800c0c03c5621a004c0203200a0f60800705019000b6444080720140c000d40c4480e182a500c03800d460304500d0b540e0030410203800e056a8000c003803481400c009001c144800040002e6028004610469901402141d46024020001c650403506c94049000400c00b2954503030f6520041540c00301c00c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 892874505 1250 892873255 892873259
    0x1101141b032817060f061818010b1914070b01140105040b1c0b0d0f020109050405010605120405010f090b01210803040f020307150f12111c02040302040c18050103020702090f040507 79
    0x116986e50404907130726500780da8500e05a4035509100030b48a03000141454600318542c184541140144207008209802c01200390b0840b007020320810211102280c40000160b0320605428420621082030007144862680a508540190b00034000c5404a9070910007a6003401a41309003c2d548884000b8001d55494462000d20b07034603a10340340c44d032000d5440f0701212404000075000042a549464000786d000d00d21f05001400301581240035940c0040c050058039810341d45a14106001d03100154800142034203140c2e054040018880185060398450540443c660a1559030160500741016001e03143c1c1808001140104084122261100d8000340c100c904940e5602008040d05d580c500b19000002d450885c070404040d4020a02c0d01007021114051081102c029128215481503e491740c80c10350035034040c0300301000b050f01510700440d001001007102554040c0090401a6480542c01c105010300501103585d6001c1e10a5825032600a440320307126580d81c040140008101800590b1148124000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 892875755 1250 892874505 892874509
    0x305090a08130f0602060c1b0f070f170309010512040c0e01120501050901092114040602010b010909060b0706020d020d0515100306031101141b032817060f 68
    0x1880c002a6140104141c107182070511060714400303402060443d001b44080c80f12030b00800c01900d09900f104101030754000c000742c0303506180003032a2100340303602d014504000036501c40c80700556040300c42180846001c11011000710b034580c403e4030603460210b2000d0203001e40c00445202c003035500c03511400000c00301d283c43d0b4a00c001c0d4240240d00403005402c2090000d82000020700803a504000740c04002c1c00809065601c0340c20352482c110780c3c0085054046011800c0c2031184804202c40180010350654950320b4600081c00f0340308640007240400c0507914002640c410b0b038406d2404598070120814140b800c01e030781ea0b4000c0d52001c02045000794007030292030410401c2c1c1c410306c2d011b00d043c4501614041e000005000745e15a060480c3c030203142c0340810800c04142a80040080c0350003d1030f218240b44580a40151240110481b000e00501150303c0c0352000031001009201010021210600071600e1010003505a0900e03850341d0300103400720110078910002400c0700e941187d0018608440031100c3c41c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 892877005 1250 892875755 892875757
    0x30712021f200909010306020c030f0408010603050d050f0313080910030c09080d0206010909020d0c0b0319061503090804090f1b171816030503180406050d030305090a08 74
    0x20340480901d0350350040340740442d010003a00c0702c800100c50405080055030740c000740d9580014072000c1c208a07000a000402160305104850f6211280b10784542c44a40300c5902c1d900800c00c5d40070440c0d182c490103180400c005c3c000d0090303540110098141e180b841e99030041000d01c61403480022103843c0d20a000c000a00d0b81d9040450000c18401c1d540081c2d4440014001820006142e00c401c506800154110b19802d6004c20b00506440800d80003050025451010401c95004118080d014201d80407001c15100c4090004600402e448224030344480c0c074480040c022a07010388140c25103440c14035250070030a8001e0300410a0790380030305a80350074256980c00c11410b68010170555940c080d60f803050701c0300c3c240e241d4224105061711881e040202c13403280c0042c044201005003609840031810031020078080300070003003070081d0950f50b084a5401592443c203d50f89800842c9482c03016140000d16003010b0030140f1401044680c020701c4070030310340303a50b44040d00100303005445454640a5058ac1402082d0214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 892878255 1250 892877005 892877053
    0x5190915021c1d0d1d0a060f0e0906011718010e010207020109170c1309051218010305150409111f08100e0604020f07120f03110c03071202 61
    0x45581095071400210940440d071116010403031202e0b41d00e40302c0040c03540c00a0b201130740c0300e11401c02a150100c0174029510000c9950710b52644940d45840124138542c5c41440b10110342000d0b01c41003601c1c8003803410810b98180458109000600326041b10b41c0c1c1002004985411051030010312030040e1003104141e0940d124040c80d184140c2d0001044021540d010002c1b00c0103202100344003020705c800502440d20703092404405445150114400d0740314003940d0b40310325009035103d0100c1d40d120003181c080b00340503007000300c0024001c440e620940c0141c0d4028000c0c20f104403c42000d0700d1191002c1d604001c02480880410b071502c0501040d160441e8654100b0419204d03036070b09000b614004800c80007005203000800d584945a0341c1002041003520384401c141c0c009904440258407008103070342200c180c1c020b00001506a55880b152550b00a4001500200d207520a59042c400b0710800c0310b03108410300c200d410300201ea0b0b008100c6400820b11119034a6101130f00c1d48140e44942d0074244040f441650f2038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 892879505 1250 892878255 892878277
    0x1a0405010603051e011d07050c03120a050a14040318050901170f0f060408070f0605040309090b0607030804020906030715020303090622060506060d06030b0108100519091502 76
    0x40c60501000c20210a20803001200d0440c40c80b03120b60400f01c0c200316400448643c0d0302c3d0b04030540b0104e844c3c64090409d0f47c0c83e060070102140e45821461030b11910402d0243c0d80700d80801d00d0400419450310032402a64560140f410311401c8949403590116980503180003111408050128089a0307640c80c036018a000704060b108001d807245c0710401c1c56080102001c0f0022203036200c000101c0c900f400c003041d0142d2068000ea1001d89407a2942480b038028a1140700062020380380c80100020036412007a0001920230000041001c61050300920242c1e00c5040c401070082006000040c0c010318151807120341c001809010b880303040d0790791440784103000c00c1e0000310170250b0004401c00c5003502c800c000b9181e00c58030001714445800c00225100188154204000c1c0030103484000084d503944a00003200e1400c0e41c00c0c042041300d1a0344e070030035031a881e001780030302c0303500d4000d12238103e891801c07a0050b0307801050600180306810b201044190010880070100b200c8a5203a40349001c0342d0040b91014080e0303506c2e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 892880755 1250 892879505 892879511
    0x40f0201180f030614240a0308030a020a02070821030603070e1e07021c1d10120b060f041806030501020711090601020a0c0b0904020d0213050a120b0402041a0405010603 74
    0x31071500704251000b420211000c080740300108003240010411324600c0300030700781c106e0f9101255840416072114240d04040c1603007074000107001100c141039000f008040031a5081d9100303103848924040d210458813443c907181003e0310032016440341881005542116006085504050780c80680c1c040c520422905c3e850400320101d04150342d1644040580c1d401506403018015039048001100c148800401c80101044140006103641c100701c06421410000700608406803044402d1703005180e0020400305010240c202030f200c280c20f0502c0700940e2822824054104c0c1007074240103425a0b050101100801040d80342c020010100c0e000384000c2080c140698080c104203088a014001d4108028102d5811548010b13808008100c0c00e090bc0c0303007517504c1d9450a65807000808002001380c001d0301100d80007280b001030072015491040c00c4000807240141c0b83c07007000559490300d007440189c040c0c0c00508a00300303400020300145403c0c0c0c4800c04800d00c85803031690411041001c18105c0f60300740c00403c080ba076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 892882005 1250 892880755 892880759
    0x2010e10051b0307020a150b030109050d18050a05010c0302070f0608060a1202010c08031003050f061806070e010c1a10172803170a0c140f03040f0201180f 68
    0x442d02c006204034036540200a8a18105803400035a181d01d00d00c80503241101284640d60540c0960700148540c1000600910000301d117420207644904064518801145000c05844044462102c5510031954010900780c1d0640c541401941c4503540c10604408500038a0404105100071a91110260407140d40d8820117181000500124100c42c0d00120b0f21a08515004001030381c2c80b0700c1ca6001c00f1b91003c0d0880e200e490310b0005400d8645140c00c010b10174011000310702d00c040f5001136142e205503403903000b01003881007001119407509400c0c2d9001d00011a402d2000d4129405100c10351480c5100340c0c1d000c44100d150020900030302d1012b40d0301071000c1c07111542c1040381055540704500071010010181c8031038001c01b1044010b0580a182404e1032001103c0c140040c117014800556541c1d0500075448800d1804880c050700412a00c82c0d01c201258a42500e1460480755806650134101c1c0341700c02501d9529981c40b908540b070094502281040f088045603210a030780c10350050000c00460040c4c0c10001c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 892883255 1250 892882005 892882021
    0xc15010b0c0705120a020d05010e030406050d1413060e07050604032001050a05090d080d09030503420a0302060a0309051207020607020603180106171603050303011502010e1005 77
    0x805600c96442244d84e100c1c90f104814011400c0c80155038100d0b170b0598046260300d441d602504039087c2c0703840d070382c0400300c0c00103010342d0007400820441c140303103401300a4114018450045100b05582d2400124041020780000549030391100200115040c100d13807010340d0b2100058560703445604115013811a90504454996048a5000036850309003040d03824454091030040c00c5001d0b0102e00c2d481082034058480034400481c0480e4882001c0c50014060072585d400c02800030360041e030f80010071940e41c0041510f241802945164030b12000201c0303030a01e07840a5410140c521040c4551a440040c0100c00401641d039040204202140380e06c000c1015192303800c055041c0005d4020540700c107801000001c0c0103079640e0048035103040c0d044940350748907107a40c0400742e8942c4480c122a03600350b180803008125180144507207203d12400808607000702c10740601d6481400030740d1000070080d50091005011022500349078000b5040644000038006952803c96032605821100c82040203a555042c03150036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 892884505 1250 892883255 892883263
    0x1903020d11041e050102031e070b10030b01081f0c17090d171603020f0f0309011a040b01080a2004090f0e030c0303040204090819030b1201061a0c15010b0c 68
    0x1041d409180a0b843e504e0500040d484e4410195548201c0d0380d2003d041100c40d500c0c4040d6a00c40b500001407100e10700c1c028411090300d013050301081d140842440000190180005015010010740c018001c0c0d04240e5a0800344c040c00441e0401824010071b2100070440046406405200740d481c04010415001c807080cbc0039110030050103805442c01c0c42e040400c100920940e1822030500d001c1d00e00141c0c0c448408030b01078150300440c1e901130448c080000900010600c150840820400008e000742d040d10740000400045955101003a8045102100010342550032030f88006540818848001104ca9003188100c09540c029040108000d03904d400c0889402c03003504c640c0090040c010000c2d0b2412203140b100940d28040100000c0c8902d0700c82010500b0000709ea401e690000b08491958481340f4107031400980030b814800704040c05007860080c100080801405244100c0b03403110039000c6100e02444e40440e503070b48201051082da00c0343c506040c0a11038072030001402003030705102440d100c40140c4000c1e420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 892885755 1250 892884505 892884539
    0x320105010c0b0c030403020f06010602070f140d06050603010b060c03271825030b0f0f0a0e150a030f1505070905130f020406230f1903020d1104 63
    0x4001c410718a410010300000e030210b0704001030b89100d948a5459140c22440c0c0170000e000b1005502446d000091503a4001800c08240d03006c2d078241507229501d9001c405615a0401c0d829548034200e47d83d088040380641c0e10054000c1009400400c400c9039080203e2065400740f0072002255100140d01202e5011411511203910034540360039100c11100000910a40650660309519502110124502204071403c6800103200300c50301491501e44500080c1c000d01d05a11800e00a00040d80703058283e01d0701014624041500606a180c82420a036000300014001040c1d91181400d01051041503a1030040d00001103100d121410410743c036074a09003a11411040d40004080c0c02c1c2800d008419401c9241c807401c0e1242610188881714942010301c001d010485079645205100140115045501000380004409858040e2101c500c0e10105003400d407150880c207000441c0309000101c80d0705040150040542c40074903026050600b100303110b00c01c94100c564000c10f44940050200301c200341c01070309044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 892887005 1250 892885755 892885757
    0x6142706180a080601060c12030b090109020a1121071a0f01171f110712030605030f0a080d050402180a0c0e060a1403060301091b08010b0a06021f32010501 68
    0x104d60b51416201901f50340303501c44010a45c04504031507448881c481da114a50100c030040c07074859956034444114000354000d41061001442148003104402e40c00501c80c0359401e080da0509080c2003507108445020780080c882140c580c4014083d4001100d0071804070782c018505060302c84295450030f1000a0350441e00005407c66411010150a510403428008880f107005108040b0341c1403464400e04100344600d04c001044000c3d01c80c0c880c950aa0305078400d00c1074a00c1030701120045529038070b0196030380600700030040000da0200040e061212182e0081a013241c03019044440242019141e011a2034084072101a950ba541a81100075a070189440c4403480058a0051903c25045d400511a001e0300d0b050761501c03400000403c0080e10b09512842c0300710b4200c0c040b0040104032040d0f03a40c2d13a03207003841001100d43c01c010b01d00700341d0706c1c200201c18101d400c140c00030300c1c107103071000c11700b0f0125454103692002c419034442c2910303101c010712085003000121341001d510b0a0441c4c00c0f42c44581d0941a04014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 892888255 1250 892887005 892887013
    0x801230904080a030e07060e0d11130903030b030a0c21051014010b0301050d0308250e0a1a0415020312070509120f0a0609111f020706142706180a08 65
    0x200940c0c000c2400d203610281a12506c0052202b420407400e031442d07169000360001c0d58404012100e104c96031106103114401da0301400314400e00410180da9041da801d001e40f11502d00032003002424400c20178207180600004284a40c001280c60f4141082501d8000009007a00c0700c410b444070002009030540034200d211083d90555040001150340081001c9005062043d25000318800c134074040c810745040300000c0140000c95138902c80082c180908400c03007600a6200c01c0c2c1c04500703a0440380c0345078404800800d0f031605003450141d406c9074400a00356440d081d40020030594108002011429128810b103407501a601c9019a051048441c51140c9010070380d00f0900b40b00009610108109100d1b0341c000340e021521090700e0038003012110b005120701342d02407400140ba040e41c40400d04c100c0c514203d903800703695059035680029a0b0303402c0504101c031002d02080154142e00003074800ca034a581e60000b80035401c5940700e14085801584200070958920500207a01301171440c107000b11304050043e11001d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 892889505 1250 892888255 892888259
    0x70207060903020f030106030c080c0f04270309080d080114010908063601051b070506061017070e03070611070306241e080d0801230904080a030e07 65
    0x300000d465002c000e10610807441101e002d65400d410aa01458002000505859650b00c60075502d001c8000c4d0300d405258022580c040c0b51900e0f220303085908040744060810101d8a612803401c1e085081e600314103000302d18002098110042200800d0301007191100480c550404034410000c0481c41c070742d241004504a42840710074004262070341c02c02c280140804000c8140043d2007140309444042c1600c00040403640c1c01e00900c15003007103002c0c50301500070841d8860f0220486260348290350000c1c2050348050045461800d000304914540c82282c60010042c19022081954100090700e980000401403c1502d0036803809001850080899050031804007042030b520540302c49861002070315850759850f440580060b0300402c40d899810301c03030140c071000c3d4807074058160026565070107840e10210240c010510000018440e0503094480d2100903107a8a411101c0160001e14116000c0d1a603a0340c59001141d120035001078082c521454982c1c0e00d861810748002c04407086070803c5095076001e01d0b01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 892890755 1250 892889505 892889507
    0x60303032f031003051b100507051b04020c01050702010501080f0706020c0d02010507140a170301050f0f040f0c091805010608070309030e0904140d08060609010e0312031e07020706 79
    0x488074075800044415140d90724100c0c800d02c04120b983c005046805120414203854000440003c09a60200d1706c0c0c1c141d11443c941c08581d40d004080d0024010781c0000c0c80100903c021140c0d44441c0c290040c0050b1402413a000ea0f20f00b5658180d13003a50160f0f440344014840800184501c0e0760b501c540800074010a450020025600d0b01c014030b006004100d070002d14810340e4452070071901890741003000144800c100044903507071080850001d407094407808803150186070641c0c04480c101c5000401b00004c3d060312004214a9040280d00b440d401a922040c1d0700c2c815a290240543c066040d0300c0300f140f6507190945680200c0403510803440c5040c60007005120094128801a400005038540080e5450300340c50305480303180fa070100c80355100300414208810050701203449681c41c50403005503640846a58026150580d00b0b40704c83d81e0101c03003400100d01651150101f0f6081d8000141200c0401051a80d044555801910f6141c850720404090310000e01c10708044980250700ca10060288038a8040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 892892005 1250 892890755 892890821
    0xd1b06030c0f110a0602070507080c0303040509071808060a140a0c1b0303090b0f04060b04090510110708160201080907050607060908130b0a0224040825050106030303 73
    0x20b88000388031083d01c01c0050030208218201c45135501800071550b441c0941010b035582c072120b10951241d07102e5001e0b40000c03030a000c001c1e03c04039080a8030b1000240c4030f0751001d48800c00016680f10710750391000000100840100319507405051401d00004121082050b54560110000c1484050340c4c24050700b031140560040381440b45696410340015403224610b4114050700180d90b0140410848405000464401e4000e03140034030301c02c1c0b40411203404100c0c24407013900c944900140158102841c8102c03590031b13940102d0340382501d485259181010f82d685440d143d40110710880c0c3c03151121001072045581200d141500403900600900035585881c1c0041c85c18807510074000e0030369454220f170504108800040d2048203412080030302d5000e4842100721119045a801c50005220b40700d20014140b40501a42900060030070140506540b40e03200d061095210030300843c01e10003a408489504056103040c40d0302c40e40300728000319003207155050040039144141040d204501c10581c440c85081010a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 892893255 1250 892892005 892892027
    0x120b03060c07051204090c09050118090b0a030519030e0d0c090b040209030f06090616081f0302090c0d0f0b18060f030a0b090706030902181003020d1b06030c 69
    0x50780256140054680f403402c040d860800c40d44820390105011607510280e4100d40c584174900e0342c0381001290b8503401103521190b0071540541b6501071020030311541c1040d410aa0f0040e102900d140c00d0700b83e580e5100752501b19890004001c98001402490400d58491032540c6540021181c09602c0a0103803119000002c15104100620340d1f580c1c0d5000385034496405440007800001c003a509000140c2508603201c00e0308940c0e1402c02d00a107000101098507410460704050380968502403550380d9210703103a101402c0c0e41c40c070100321a80004000300603510500540d206040003040c0948410000c050802510403a055101d400e506046030841661100c8402d01009550550030341c2c0c507611140041020980040c60541e0107000e00c440300801d0000c0c0141080c01406a00100c2e645c66607540750440881e04c002074000d502111003000c050205400c10100e40e01700c9100500081c4080d9a94005901c00441c0501142d80c10708072a40b12240b010760b107103044010310050609101c03480c664040101042c12071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 892894505 1250 892893255 892893271
    0x1209010b150d06051c172703030d0510090c091a030402040e0106150e030d0206071d04020a11011a09011503020708071a1e04060c210c120b0306 63
    0x402c00c0e2549080a400400090070094940c4032911030301106291080507005050710803528000100c5019450801180c0408000040b90010b050031400182c0c4400f0854400303552501c41840300c4200c0e400709101d00f900400c290410100c0c480d1800d001c1000381c503401c60000b004c0c06180242040380c048100050b02c100100030000640d2941d81c0e02c0017034002c128250070410700750310340180401c00f28640e04d000a41d11000e9101c640502800800b0180c3e144420406500180c00007808903903800e00801c0d000c0708481c01e10b603030f104c5419070f00710110b001c90300441e000d074000642600400c2c01a00d420721444103542980c8101011140043d008105600811300c15030311841e1241e4800d5455502c254159091580c1c0070304295036a180380d08003904044c049100048011a42c0b00210301071200c0a004940c3c041011460000ca9a40d00c0d1281030090207021800740a00401e00c100580e285140d030510642c442d08200c0025003000441d07002440c1c2c415500d00e00c20850303d40702a105007941c0c0007421582c00b07108 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 892895755 1250 892894505 892894507
    0x8011e1202040207050105010b04050a050a140d1514040317060d12090302180a05220201030c200604050601050a21030e1c050105061503070804030e12031209010b15 72
    0xc9840450020f105a480143c0300c1c5d4079010003c5003020210b002481141e2003254128086900e80c001c00020402c944100c0030141c4166100309094100845c078001200e01910462004400301103020f410380f4170707d240c0c106000d01c024040108040e00210041c4100403003510300d965520f002c0003c60754101c6400c60103403001c4440a005000f0703501c070301090f038050350780a01090420140481074480c1d4407001da0380464800d00304800100a14038103c611010030000d10340220710700803103030019001046100d0f01030040092103001c40c0c1c10380c0100c5009001a800d000000c0c06030780b1b17050a00c1d904210040e00120710075500168100000303450040501c01098012004606114151905603603d402c0790601d0340e0000b11280310445000500c00e0305c405000c0c0106c000f8030150341c842c000c10030501d54004201100100500c04611041d2180c001240d100d8070a041c0301c00452301c07240001350110200c414101c010340c00007415071086520a0591900310f88070704000c0c04030001410000304000110711007680a080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 892897005 1250 892895755 892895789
    0x150312071a2233140f07050c011808030403030b1918021306090f080106030201050f0a022a0a152c1503061c021e010c060f050708011e 59
    0xb040782540c0f52480c0025001103042041c5548041d4501c8945080b0140c15140450041103078040c00d41c020f2051341200d09100c410758031046c0c01d90f116000010403103030a43d0ba40c049811480b04808641082602030641991285030526004050364442d58403d402007151481d0352480308211003402007603501d40704110b0b04000d51014504002d0045080e02110808482800180d15030403403c000c058500e1000f88a15441c2c44000703032030a031034142c4402800101c0801c06407018951150180c200300364241b040c0d580c0584062103182002455149000255041031000d0f030781803801c0d4100380c0060040c4d0000c40340303d58003100b029064041c0e01c0a142030000c42d01804500b00146400003c3c00b102d0001c2c4821a54001441006560307001100c0d03050003065890800d10403c07903c11880c44409074001c00040c05400704520110001d1100d0400c00d061002c40c07260403000406034010168191149040001c0514000000401c5036006910109140106550240c2986003e07000041038a02c0362944940c208 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 892898255 1250 892897005 892897013
    0xa05040b01020f0106320901060c08090a23090603030306040905070815010e06040b0a062307080d110a0e101209031110060f0e150312071a22 62
    0xa855103c48100c55441d2000200380b2000d0102e089051a80320b4650703200101080d80c1801c201c000701c0340656400300d610f0004002c02c41c0b14110114034584610141402c0100900200f4a074800540019207c40c0340520043d82c03031140b444204c0c1501c2012038480ca000c0c2850400b00b6202d110150440d40541e480300400c5003403001c2008960000e180c4007044900c000c40012108160794028000c03800780340000d0011900c54903183c020b2501c07000009007010441c61404c0b00503191081c1c0401114040d03070707054410a40b02c90201014003c2c8a002d8079240c5d580d45055252074080302c00e0305891a80c010000d100700040180c0c400c0690102c69420758070012511085d003800d941080c0248a00200e03070341866004400c00d80d2044100710f008010740d00701d5802e042241045001c3e12180d001e440741030b10181004100d040314149045801a08030440008400c4441c00420709180e1500c03966000301d100042c00340100507402c4544d1043c40d111a003500c0083c1003010003c101c40c0b41188040000700d04d243c0460043c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 892899505 1250 892898255 892898263
    0x10030903200c060c0c040b0f01052d070807020a050303040b0d02070f020907020c040c09050102030703050d0b0a1512050f010b07050f032d0a0e1e060d05180a020a05040b0102 76
    0xb0801003200b80c44511640c5400c1d0707503049150100b80074608290254050341071400c01242c100005854060400c08041e00507044048005610700800c4030050204184600740c0000b0a850740c0140d100568840140c01440307004139541d409140aa40100002c01030f402c40c4c2001e480030100a05400b60f40c0324914141103450800305100a944026940180301d80b60350001034910445100761810301c12055214000d42e81c1ca421440380783d0140e0020407000d070000703120701c00a20490031559000101051118080385000f401500616518100356082c0c4080941080708003440c1c20f040300c2d080c8160701d40860340c0d00180d4018410300c081040c000c034500b01008002d01c140e104001c41401140c3d240c0401a05940303401c8d101c03c803004606001c03560b1200c40190b54408455640707409490325422601c01b1028418548007190000401c401711540c04011959040c1c020607450480d44404a102d007064011581402a52100740d801c40d0b0000f01036100586480c0d181c1022650100c40000b00d8000c513000603820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 892900755 1250 892899505 892899523
    0x12050a1d09060d1410050f07020114070315080604081c0902011409030c1e0a0614030f0903210709080d171e01090912180e0613020a0207051003090320 66
    0x115000d000f00c3d14058140682c00640307c0e060140d4a14099254414180c0c01c0701c1600303c04402080c41e1900103200640a40c002000704c40340c6140b00c01c100d55071028010704100c0251001c0700d0071000014062991400ca003002c003032007158a0710400c612105540064645903413428440c460360004217030b40c0081c2c0e40900c0005002a400392861382949104403003041052007984c99075100b9006032602140b100d110318070384100b010f216138959185407202c40048a40c0400181802110f00c07007040708050728425045100403408007248544254201064084c0081481c1d40102c0c07100e6100803001c0c080b0036400444100a82481e00d81c5903030b59291558481c02491021b0302c1e15580d005150000a15824039070700c001501c1f03000c1c0044050885080c0b500712110f1241c0c80d511030134030a2510040c81514580d8904e40c2c1c1040c0e000b0000d030f8640340c50144e22400c3c0d03000f00c110000560031120f0200001e0070181d200040940b003614081081c221380c2da8000d400c450003500d001c1390701c1d405100e40c61241e010421002c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 892902005 1250 892900755 892900793
    0xf0e0c0c010507020109060c031103061207050310090c0506030609180f0a110301050f040c0b03061c0b07020c0402031902090a091b0e0a1809030c12050a1d09060d 71
    0x80307a0f1401d01c3c0701038040c110b68002103514078a4400c514803498440c0c400ca0301e4a4141320406803841c1c17a03020800084210070f02d2084840e0140c1a000907840e42d04110b10262044050000b0030821a9401e180c4908605688075500610301001009a43c1e0b0f9000c682d50781c4144d21950520074404285005450500070424074031040c4a0000b1820900c200017801d2111188220000e00403a59028004020150b00f07036001418640602d00900c440c0703075210090355000c08050001c510302c002020340c00d00b0314800754200f641d10b10711100c107101030301ea41400005012441034a0541c918208500c2020110301c100074032030100c40c0c1c0401c55a219603664a01c000080030220024000308104048104801c50820901004200102c0b544034103800c0024034a022241c0c103201110701908018102e4024103401c007070807020024818105000504042002168400b555031900c0c2c40f030301c18807405011414102800f032544400d00e1459101642e41c0030003580c1c401e00941d00c10782500c10070310304100e44c461140401d007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 892903255 1250 892902005 892902011
    0x40c020c1005041e0302180717010e06030c010311160807020604080715020d09050108071b050c180103021f0c050616031116060b03030409050c0c0705010206010f0e0c0c01 75
    0x62460b8414090402c1e41c501c1d490306442c0911103a1580030740325681c400250400ca40c01c240d15460580c070184950702c0000c9003040c3d50030310a088205105600c0076080002c035a400901403001c030b41000c100700e2100d41400c1c00c00b04506004007600081d03602409103003900c000540e40c0310108000150058450240c2c0c083c00c03240e103c1f034a40300c80c0d5880c0c0c4064000c1c210356008040d824150725100160608500f103031912202d001c2400c0c4001107802c8075000b4003540511108044402012030089460000140600302400c8003c49600800c034003041c00e510b01c22030b0301c0417040041c000750b607a1180c010f920070f070100c0c0e64011707032404042c0c184c07000d0400000152180c010310003003190002001c15402d2845040780d03000c2207500101c0104c0c840c3d5024080b0070343e4010840f928800d001070710350b0f4030100e2203c0c0c0080482e41013660b10503128091740c0049880690307c0340c01048504089200300600300103020300740040d120540c100500d0004606142c441c5140481201700402c200000ca80119080b00d04401e0080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 892904505 1250 892903255 892903279
    0x30e03030412020114100e07030603051006050102062d070219030309150603120311130602070e0117101e06080c010f140406120b040204061d060414040c020c 69
    0x5a0301103800d29101d07003d542440c0840d40c400d4100c050040c8140c440d10842c030101410107108820b00900100311205041d52100e0100c01300380308118a406100d0030a00c0801c090382040002418810301500c0d8020103600302e43e14003008051044200ca0350240b50114400c4c0b503030fa05000301c1c0351684104103507c2d800d1904590800707140c2d05810000240e4040d2521011441c003540c4c0d00421035410707200142c0301e000010008400c3c140300ea0494440d4002464005050a21080b40c2d40130b03c003030a80c03050b009a400394208011080d9900744460052401540000b0780150041d03410391180f40028064002d01d03566002c00d00e02620180315014008081841040907980f140300d525034681c2c14000060101d00d1211810f440c0c144a10454081c2640d113250040c02c040c0345c008181c0c0c0c140008182003071000d89441500216856620241c00107080a0f079800396044034a0300f02d0b00d54540145403850250b030007044240301c0075108156004004005540000e65401c010a04905100b50080c041c0d600202c10030203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 892905755 1250 892904505 892904513
    0x80d0b12102405040902031e0d02060604112b06030c08011a031b030307120c0210051213020f040c030b031603020a26030705100b03030702010c02060307030e030304 72
    0x3280301c071400351075420051040081040e45110b08a8000c40b00d00340394900c01807195040c140c102c24445407001d0201c50800c4035600c1d280500900d030701c0c5242000c1d0702c54080b0802107a8104a803d810030b0301600d040104c0e40c0c12a00c100d80500c1005264680c11000c011110f041000000802640d169001c000300801c6031030745065040c102052180b560a5801c00354480c0322895181091544494001c00805c00c182c031110b02d003c0744a108904043d45030100380040c00c0070800e00001d6004032215581d881c003044001e403040091b945814460301c41002410701030040400c0b40341030f4041e00017032041c05024a040d4903100040c4004482c0c4800c40c3c1007401d040602400d43d070940c122004005080b41510741201d501c40c400c03078243e0341501c006513009003041c0f4100290209802c1d040232030012020301040403240c041000d031840d803150301c00b22285d03804840c19650a0000307228050250600310701941c546801d90300001c122460804019124510000208a40302c1c0a94400c0303402060150030b880d01c038601410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 892907005 1250 892905755 892905763
    0x1140408010515010806030a02090a0902040f140916060e04090812041e02030304030813050907080613060605270d0b012105100e01060e090105070f050a0c080d0b12 72
    0x845200001504407503c2c019805520b8103446410060001c1c9055480c680800c00c803110007a280082c2c01740d5510702da4000d6142c40c018841c180c008480c01041c5841c0f260040100508001c00c149200d0b044a2020340c4141088240c2104852007440c20f400034000210001300205a00328009040c600e00040c8034140c22414034985110711b000f0001c42d095040110801d100005449000a61642040200f40001403d00d130207402c0036400149107000c0c80e9180d101250f20242c0940f0b10748040780318181046114a842041c80c02d00c60704030003050007000c1c0b400344003902c14040d01c043d83e002180c8200360340c204507003003060314840c0d200010b01080c0c01c1c20303041c1003145024a0038005c00a405603000c0e403a41d9030a0790524510b255951103c02011604419a1400024406c1c582c049405540b2070130b00160341408840716501071144c440000600d800c14142c09094600003488032420300100b0301810701700940051000440c80c1d005044296180003540001c80204008039516600c03641d50020302c0c501503400a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 892908255 1250 892907005 892907011
    0x40c0e06060d0915050108030a020d051b01050420041b0e030f03180f0a0f03230607050c0105070908031e0f070c0e0a1503140f1c0f08010320011404080105 68
    0x30f135003005aa600d4206107a00e03403207414490005607218010044035584a0740c0101180b041511444030f414810f6140f40c0c0c2900e1003610251450305140095000412590200d0b403d120703001c40b400c00040c100d0480c0804480c0071107501c2000e110030305840b00807a440510800d060030403504141d03035540000703001d000355450424203014012800300129010f03c0c240075603600143c0360002e24100300c2c00d02d9603a032005000c000943d042c101d4070302c030300d081c06117074038204a441c0c080c40b55600e07540e450300400d117911400c45100a00315420000c2040c1e0030424540040102c80d87c0c0f40540b4203c1290b4912612003203041c1c400c1c0007000b420044006120410701c561405004d060711011180b549d000d4481080740720589482d0418408920f4000904000003646a20002c00c440070f550281c0ea40d149050329800e0a00c0760201c401c00c4201c1c948440c0301822903102c0b08102440e101410045003550458643c0c0781c1031044110094103203102050f0800d8030345e010f801e200640c40c0814204a40e41d13915402098080e000035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 892909505 1250 892908255 892908293
    0xf0607030c0c240c05120705070321081f090b04022b060e1605090f0405040f05010e030f0d0c0e060403051f09150c030b15130806040c0e06060d09 64
    0x10f00d00011800380325101c41200781e43c01500400070450004400c4040354060301c801c44141c8200c1070700000007941c1241c0f441880740921040c10440078a06805050f81c0f100070500b9910000b017080c2c5618007400c85407440181c503014100028900071540c003040c001d00c181d038002e084101691038201d4522445030152842015144400e00c80555519086511054245c2c0c0c4d181700394844103820115107120f80c003c0d017148071004107036180c0c076922900460200c45081d20240c0301e1090310a082403e0000074050000c10040d24001145440000b1041c694103000d078a4a0112150711074040b604510712490700029644d0000b1301c601d5445503a86007030781c1c0d82c000311201900324281034140104441818410042c240d50400341c40480b4041c10b202410041101e50045018181d035080605500e4403609010046c0c2c0700c3d20a40035a0398000403040340e503501101d61114642da88514204000214502d0b6400122954a140744a582d259040041c2c014040c160b14141c1d054905811501804045000740d41c503c005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 892910755 1250 892909505 892909559
    0xa021e18120d080703140906040c05060307020703020405100e07021c0305040209060d03140316030e120405061602090f041b06020706050c0712050604150603020f0607030c0c 76
    0x2480060203081822030500245035080041081e601c2d90158240a500500d10310700099140c60b018074100c0c00c9241a80c0d0b40c4042c0d8040d5040100b081180114940500b400302c403c1d038250f1412000081d512078081c00000d02031f40e11100400c1a08124242a07006460070140303a08040c6006280290f40710950500f0482005155a4422016000c5c0c4500360069401501040301c558400d000d0060750301c0711002c100c0410100994110550075220061400b50162010496080a40c0c08004050368281144400c240e08490007468128030424100c070204c0e242a141203440d03103540200200c00e03c000210103508049042c1c100b04080c0710448003503100d235200b00020040202844c40005000c1994003803c009a4080c1006000c0c0780d001750040c0a0550000c012280100d4880040062440c200402140c2581c0b20b1001d0104200b820b40d582801d12031000c1c000c014076442c40c1c000485850102c4a11400385070300140c03550a0502c01c64411a0707180c2c00c0108030f20300e5582c0c0d9405200d080511414500300d4a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 892912005 1250 892910755 892910797
    0x302030601081506090603060111060403200f07090b060d061d09010219031d070801090c0501020a0c050105071e110909121e040302090c0a020709230a021e 68
    0x80031010003c0b00101c0074021a081080136000e0007407641c00078100c9418416041a12000c0c0c0c04100b0280388103610a40e04e28030403000e1a16a28178100e030044003419240c100750544024002c000070004c04903050301d8000700d05006640e011030389a10401da0240040707814040c0200d603003c0901d5407400306c40f41240e40f42807150b9842039000e08030b004004200442c078406010081d01903120350070a0180030288255119400c1560500520b0031032146c1c403456940c0d46170580001800b80d1028100c00400c400c0c0040c0005100941d42d10800181758000d4034188000800d0000c184050208910701c2c62240180040c04045582040216020a40521403181e10000005940640b012465411983d20400103a003826040c0704d281c030341840a51240300e04c01d4418080000541c1c0d507070320000c0c0141130083e50b0341d03591100303190000d042840310340000241c20b0918100144096883c4030703600b15a440940f0303a290b56110300643c031010b40b255024001100d08071000c9500d100c2a00700080801e442185401c1c160b6070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 892913255 1250 892912005 892912021
    0x110d1b210b0c031015052a0c040b0a080a0f0c080606130e03040513140c0414042f1b060c03071808030d0c18050d0807170d0c0f1103032d0403030203060108 68
    0x1a46110f1100071f0380c0c0160000c07007118100f64003c40700c4240d00812884840b901c03031100b185080c0c0036040a454148003c5d103100c043c8034031219200007500115010346510300d000c00101e4070708100407910f5010300381d503560240010003090058502400d0010216100c1031b081c4980700d4050418200c54200c0007410300007142d980c94840b0216401c0341ca89a0890426500550401c40100700c0108041c00800c050841d83c0007055481c40c6580c0300c5005805020b8985030810101040000c2501e03802d44039512500603c04c8070552801a66448019481d00599582e0100709151032412164802c004520001c16034080069454220035032036505a0344004d4250780a10009514120f18400c00fa08481320342022800b0451410041815900401806504128180e503202d01ca502071a1098506950b41420703c40640d400040c141040c10b05103840503071000d014041684a2002824204040080c841000c52991048100302003c5044c003a0440e03c1340741c03905001c3c02962040f00d586000a000500080c1e8031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 892914505 1250 892913255 892913317
    0x31b05011202090a08031b0d08060906100c02191d060607030e0a0e010e070f020c2b0209040516050d080403110d1b210b0c03101505 58
    0x1248141d407060810589444294002d5004030b40140c0c00400b48100480c1807801040104400302035426a00114180c8500035803c148490f420f15003084080810b000140c0d5517085899003281084502d0480a00300d01015500c00c000810001e41006c0741882d1484005420695141201c031146100c491191000440c00c0300001c04881c0140e00c45010f000e4580842e1040f01a004540c40260120301520303100e40c803481d06088241c0c0805850300040041102ca6944219000a10329150000300b040134420400103000ca541e156074583c4041601c880d00d158200c002d04614080d9401030b041b01681e0820703061450310395401c080e03000d4400c030540c000016541411400140c0e519000b03405242071900b1956109210381e0300f1001c40d80e012102c0811400810b00308050b01001102c1c1080184100d450615802c110007480e504000e1030141c0b100d42030300801c01c50b41200f54021003210250f86d83e542d4914108030303040101d03044207071091002203c2220b02c6030468001c0c407240c11176184501c062800320200c0440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 892915755 1250 892914505 892914509
    0x18090c0d030c1407080a080405040b04091a040521090a050a060c0602030702030f1209060a02091c02060c010c0801030b0901110a0e361602071a071704031b 68
    0x682240032090100b502d80f0102c506016903801524080340d5250a22440d003e425401516100b000140400c01e42c5411b03c2502202002070341c090110040070f46074041d555640042d07010b414030300f40002a041000c140305003e1140340c0c1f0080003081d01040328100030513030424103146004000e01580810280b90001c02803007225a41c0e40e60801c250983c0e40d65002941003d8460070a500c41030000c5940d991100015200100000114052500c1e0101565162246c080d001000ea54810042c0c00b085880350622810110510300314901d08044610210704107100307110928600b07510f00943c01c0395450b4440d801504807070048400c0243c070784a510295003210904002004000010800d19461600658105008031401045004038a0003000b92802604c9d4400726810001c0f140d09440e02c4505100781c440b9008840707184a091a17621201300a0755500c05e1740076580845400d1401c811558140608661103d944107460347c00b0380c0c840c14a84001a00180011521400d200f14007500000c2c01410341d4003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 892917005 1250 892915755 892915757
    0x516170309060a260414101a060903120d1506050c030316050d0e06010f06020703020a060c0206041d0f0901020c0c150408120d06080607090e100518090c0d03 69
    0x32400c000300c00282c2d40d80b5003d134040104802d041c0c13000c1a1081c0311804040c4510301400e800107195640e0707502c05003024500745010a50910300f580e050254544249681c2880e041501c04a0742c0c0d035a20400245044000308080c6400c541c005210600c0c02e07196001502001c400340c070b40c8034000344c403240c042e1071a004083c2d40c40483e81c03060001130101440036060400c060000d040c442d203041c8408100005440d02c0621040782581300c140104a0654451640300c0101f1140c40030301a454255400100108410310074202000038a45440b41590782d0001100c000708004100400c83d503181d600541c901e481c08890039607081c6032440001d40c41c02c40600803100405108000ba20700400f151040240c500c6a0511717040300305009010106510100300320980056080340c0c3d0968035103019408071403e8070001d40090b10385030049000d1091080e0032040c0d104c20f9030b012803580d607070b90b503111040c00320141110360140740d110001000d194508018403400902900d940300688485011031002d002414145003030080c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 892918255 1250 892917005 892917007
    0x316020603060a24020c03120d0c05040f0603090c06030614041d010c0903020f06070305030a09020103090b0c0a0908033135010c12020d09051617030906 67
    0x10014a4884029903002000421005000d5200d06520b04201c54540c20032260214203a1a80350b0580c041042003120f002c2200181510b0b03c6170f02d210f0005000302585030030000d4035940340b201701c1400b134170585010307000010359030b84245c0d07035504010050410f4400c16565007001403008205640719000f458165101c00b110040d03200c0b1070788207000080840100301c0400c004841e85c2000d005100380900980c0000641c1e41c030ba60a819401006004c01807601c42a2203844100300080000f03030481d007a603a1058040b10300190314100303800180c01404580701c00512000c2e192007000341c04140700c005091401179541e14170743e2842d110481d081d900d01c941929081e004a4800261400103c4450700440d1000a20040c405117566611141040354800300c80401241d042080d201500d4442d824001414258400074041d101002d040500500b140e414007829491300094181c03164481d54004e06904c9602c02c0c01c54000c0c81d880140d10b80d50a105004d55411403aa0804022751560700106940c000c3c00010302003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 892919505 1250 892918255 892918297
    0x30c0318050607030e0120150a0506100c030c0206210619090b0f030607020307051614060a0302130801020901021005040b0c030910022205040905070e18010e0c010f0203 74
    0x540f541c50b00c1d041004e04025a10204a1701c0c0c40280005010305401c213002032916110f071180d4140c8d0385000418900f955031416040040554031200080ca000f151400e02d00390a800302e04041b190140042c001a4215500185030344081219490428203c40e00004107604d130f8440b0000c011000c000c1e40c072021805008081c05001c440d2a55000c0d030411103008007101490b03d00307800403c0c1030040466009004d40c0020035900d050050500292040b030078200449400c0c90708150346801d080622a50181c0519000307e52440f001c0d0095040300c10300000c1480c1d101c42144c1c0c2e2081c441c003079030040c40a02e0050013107004880750681a401070500840e480940b459480c0c6d5501d900c00d810750401800d421107803150002c01140703004140300400e00d0019098554290001250b25101d00520300d9200901840c50118043c2c00304102007080c8040d2540b900031a94540ca95088800710040d00c40200c4045528250541e0784101c40020141c124641c281c987c17200040c0400c1d0103030b8aa014510004803070750401842 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 892920755 1250 892919505 892919507
    0x90c09041101030204230a051203040b07080f07110a080a03080a0b0f06040803070303061401080a090c05151c02250f0618021503091e0118030c031805060703 69
    0xc001e00e141040c500181403d95880030105c0c0b41300780d0324151402802110760143c0a082548003107020307050030b549d0003041c00300590010b41e49100d00c1c411109003070781c081219001c00500d20704840552000842ca140c40340c940382025007034840754061075031089401c808009006200415000c00042c0c141e22000b426503500580c00000e0140040b03096840310385081c031038089588000142010303100c41c40007103440d00490f00c1c002d0101d40c0260070030b200d51070007902c24001c0341e82e012103a242e016820800114041949103012605030120360080d80d030110181244143e001e00c1d050140c500c2c003091030320360b070204004800503c04034030920454020101d518404194001c080102c07840c00079200c0c5400340c820342081d88600085442c1316030303115078010a503905507087d0f142c55407000d89403c0b03044000c42e1440c200b011000356100728042202d528007803041419100d48400b9031144284c20070600300c0c3c18600c523640c900100003042048003200440d011800300b220520325044884143c03280680201d00d03140183d24 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 892922005 1250 892920755 892920773
    0x306051302030715030c020309090406150504020f09010e0a05010f050a02101515020106051c08040f0902031e010501090b18030706200307171608071a090c0904 70
    0x845846120036102803401628208105070042c00724500c1c4c4614104000c0e001415183e01009401c01c541c01880185030384e41d0782107510350b0000c0e4850b000003400f20740000242d4a50b00c0d5544450344c440e00c0825101c03807074401728000b00048403091f80c650340715401c00d104000207400300b8000c183c0043c2d0991009980b99000d50001d200307504440c011280c4140941c01d481064812200b0b041d10407501040301000160052810000c141c980d030f0000f8000e643c1090040740d40c5140000200440d001590348510030700c040b82e02110090440e0403230310b00300d10f40c440100c100170b98402e03240d844454034241d4200400540000109060740c90507914001c0d00362034020141c0c4035401c880c441440300181c00001c515203650820082c3c0c01882c80b078495a46201c140b4103410002005131400b0200c90300100141d1001846107501801039410f4460f2454413000380319100d03080746050101c0100071040004492003840a40072041c61003200c40b0345a01159901c410312192101004140c0c1500920030402103800a80105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 892923255 1250 892922005 892922011
    0xc02030331020d080c060103030906080c0c060712020906030f180f0d05070602090d11030d09060903080a140a0314060f1807030b3003030103080a0f030207080705060727030605 77
    0x4820300c0c209011001046d003000383c01e82c01200480c0e05003400700b001c50b8100e2540c50340156903000e61f07030602e410042901e48851780105032000304101c000340d2526802c610713410381d08100d0018009070384a15000c017202e210364105a8031030403c41c40348500c0c0d1103503040c0003903d00c0c2c4080354000136107000e40d2802c105603050342002004a8602e40c00340000301c103940b1500716549500d8010800011581c2c811000d00d402c01248101303881c10840c40342010320125400c6a1441e00300c0790300000c429924080800c049900740e542c040015428140000e4143d03006178035410003c0c4c0c04000e094064400d480d07402c00c100700c2101e0020581d4104d01801c001c5811160302c40b0b40998492610b040100321200c04200040c40301d00c240c101c0495a413004107405034105038280c0d07801c2c00d0a903c0e0f4001c515650550b240d1001501030030801c0c004000c036071030204414510a80684010b10b07848487c07140c80300c01a00d0610b4480000301c0e644400100400011035407682c001d001d0410160303032100c1840d040790440d107500011305030007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 892924505 1250 892923255 892923263
    0x203040312030603061119030218190e091e0a021003230903070506010905011d040c05041a0f031b0609221512021e0f040c02030331020d 60
    0x380c04004003141245c021041003071b00907004180d07508404403000c01031001d0b6280501c201841071040f861009000900003031081ca04a803000d0300c8070301d1008800051030494001030951030700304050050451700003508101d01c1400000a4a8180383d11076007542e680c0c1c80341c80295000310084a44240300e0700030341c0a40c03490103118507c00c0050030500712001c40e014041d2407140300c0d60300000c0c0000500100344030240c050409100140041c0d40340075400c0d8a07030b02c0041e0740095000407101c0428104006190310308010103000c4d1041c01115035000c1049500f90072140341c82e0254065401140441ca00030850303d00340d50a8008021080c01e0070401d01496400502c402900450389040c2408450b08004d0400017501ca10070340864074003050040c070050740f0f140d5800340d150520a104c0c0031005a0344d040342500c034141c804202d02c401e02c1d000d00019143d000c1c2d881d1030359041840c0c01020500c02da80400203610a55909403004e07092901030050082ca41001c1414038415500d0083e07180c018a425242468a2806 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 892925755 1250 892924505 892924511
    0x1a09040b120d0f170405030a03020a0210090305030105100807212d0c212d06030b151c05030405091008011a0616052109120d020304031203 61
    0x100c20702291500540525850104002900a6800742e901800949407122803400d283e031141426518280c1c0ea0080c905c444040c160045500304203980308100076281c0d002c42c0c240c1070269400d01e090180c0194000e003c0d803030041107040c1548140703034024180d007801807840b030b5109417040b0040000b03100e000012500340d0f6002901c0d0409410320383d4152a101d01043c00e080151410500d0307003911170742200c0a4032080d009201c011403c000000b421030003820010421410b0100d808012000071000064048010031901c00c0444e030314070000b0000303501035419244030300d10402c50b07902d9805c24112640c60600200398400c0d0b1141a071001c405c11000b0136541c2ca8407410890b03042544540c00158200b104035400aa14502080101f06210007401038a80c0d060054002d800d58804450104550744a54501a2292170703444124608104041112500d031004903141ca413100100c0003032840d9154802400385200340c1d44510540945003000c02c4201800595030000c40c94140756644127800844890002420301d55 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 892927005 1250 892925755 892925779
    0x60c091c03141c06080106031716020d05010c11012007081b1606230c150a0e010b0306060a18200d0510150e030a08040f0602071a09040b 60
    0x24080090f081c01030ba4000030a030f02d00584110340c8120f64159019074041d82c140041000030999004201803000303a030f81e4603e81e03a46000000201401c80244000350070000707140303030703041400b0040d4007580110300d45a490504491040e40d42c0c80c00d032071412540c184828002e8500700c0481070960020701e4900d01c281145418501c04004240c4108a0200074078266001429410108202520f00307070080c00060400d170058074009501c540c010280c1901300c020310000000c68080d07da404002c03000d10704001410788100c03840c1c482403110250082d80f590014540c00c0544903c80d61601140d2144501d10260040401a203440c001404080751400071001e2959100a8881503625480210300b5040d400a0401d41d601c82050303008040340d2006069011b01d21554605011007820042d0200c0c42004a00d4000892158000020304054910b40c0040900030300140005403200c070700519604131503a5030242c4451582e01c01480d844180202c0041c03031540420000c0c00c5281c40c0c198448495040c0141c480350340c041c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 892928255 1250 892927005 892927037
    0x12030309020415050108070306080606010e181906050f130c0c0c030b0711030a0909020c03130f051005120402091305100b2404090f090b07050c060c091c03 68
    0x1800f428030f81440e0400b200d00500080d40c001d814190042ca6502c0e04002c2c403032508050949943d00030703112604200c0c105d0319110196841d1185c2c07819001b410300308170b055410003000c0031b07903070801c0301034202006030409100094928041c00560311a05000d0814030200703030309021460082c6085580c01d82804059500d44000c10724213031404001d14800d0140c8485428403034805424600c0e05c103840b2407564030410480c07403120703803095903041220f00104016866403e5200c078142035010300340309018400140500000c0590704006008121003043d5092a00c0c0b8000d04011036243c8a40010380c107513110f0a1300401c0060401009055018801c80c1c0d5904011400355034590502c55110380202e002d940b0382c0081c05041c5020710552405626510150b80502c880b0041b01d4514091072041c048425600c110300650301000744c20401280758001880e01140c07a0131b42000d0025003082c4014202ca1068000080c160100c001c2201c8484400400303841d03078890105220703001d1003c0144220f04220942c0501c19440f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 892929505 1250 892928255 892928261
    0x1202160c06080613110d090311031812010903080f13020d060507020c06310b1c060504090f02060903011b0201060e09061501180b03101e0b04120303090204 68
    0x81c0603181d031500310300d003000320400034120413143d0800c1c9201e140216180c04240502e045500c0d4510180c130110b05d2500b20308054445409600c0d80d503800b40400680790052110340800c2444001c42111413020f41c15134981308508036401c1200040c040f42084003c18400b551105100ba0701a01c140c19490700751400fa40410600c005e9080110389140d203500c1404030700f40d0140400c0450810641d0b0a50a000e9510100a0003a01d0384421140300d60580482080ba0606580314101508003e20aa60359101e420214020310120f12129000300d840c0c42008151b905d05802074086c1640c104032540ea151800c0c0c0c08001069000c0c4c13140d00d030b15640e01c011840342602d9003a40e42a00c21003135000041c59501c1c0203006400d0a40c01040e03600160000300800c0490910b480f02c0715200e840a20b052850020003580888551990303400c00c40c00140e01104014441d041c0e007110200342c540c51124849006100c030100c0444c0740301c5003d54040010148824401242c0381d1400030b18042c028030700880d40f681650049005c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 892930755 1250 892929505 892929509
    0x50106020a0312021c021b0109050c101103070503031803030c0a0e041d072904090506030a052b050a02100b01050702090c0306011403010f05091902130302041b1202160c 74
    0x1845e900803498020f240050000142d040040b071000f401b09017541e548041d1507a9003d0078551003140e2000265402c58070803200b104650b032400007180e940f5969030600c3c5503290412149480140466a13401c5600396000c01501c3c0640858680542000080da0042e501d43d034134a041a90817650f01c0c0c1c0c40c983c962141c044c1035203c962540d405458141c0c00c01e020442d0025000c04c10846c0c83d120112090300340c45855080394101c0b2002c0100250a840d40e0340000c1c140345440c40d02034030b64440d1306500001030070343c0240041d03020001864038140c42100d00040e94540161150306016070088007180098000d160011000b0030740500d401ca00e060080e81c002001c040302500c20554078140070041140340c1d40c100c420000035079645100c150866142034030034801031040703004503801101c074000030954200c841c5110200071541008155261488464003c0030f04886e8401039101d14148030402908900605a85103400901d82c1d61908104072076801d04003a40c13004c81e0490340341c103600e000000841e404d80d0303803400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 892932005 1250 892930755 892930807
    0x3160b182710030c03060b01110a03050406080f07170603070f0b0903010f02040509150118060309110406080d031808030903040609051f0c06060e161101050106020a031202 75
    0xd000a204855041800c005000c402658602c0c6000d00100b0700101c0280201c0b82c0c0024081214a40300c00100d0304c001001c3c04c802900d100310b1390310104240d0080041c0060310007565613100540e48501f208029a036081e030f124004626042c1c2c4881c08240761816aa40c4400e014044894651b900d01d0002690030b041e5012021110011031000003524007070158070706907040d0a00c15070815060000040d031150000e070000c1059501d00c20715805030f0740109100c803120212007182410a40e66000c01030054403543c4012240e0351032034005c010b610304d03080c0300740000c7c0c5040340001c00c15804031840680090640b0309101550b0580080b141c00001c008100442c42000f03010b014503126450883e001e84100724a80005110790300c4a1190740814100c4400b4207440000303481c00c01da802103103060240080005070000c042c104818801c200321602640b4584042ca8101e9a401c450440031040315070032240280100c1006030803003240c0d140442d2198150f4500c8040c002c0340145000b038111481c9409510b02d0700300c06 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 892933255 1250 892932005 892932049
    0xc080d050c06180c01050d2307030b152218020417030c101a03070e180309030c27070c0c120c0b1b1002071103160b18 52
    0x3480e600c1c10301c040e98100c02246414504070300007142d081e4803a140e01c1e034100d04014011601c1c0403002a5a0005c8010031503034020340400e0726400c1700242c4654812101d00022a0a04501d504542011a0702c2c100740b0340340381c071038504080e1069040c050444041d0f00b40c1604415010001c50b802c034041800308240d50b10030b000141c2d114035010702a00c0003e901540034400382c0003442140d641c100080b07001c010a2850007400101c2c4800141409003e1201c100c82607014854044080348036040741040d2401032041ca010b405102211034010344da07a20410301c1054241d041103405100c3d41c10044264020308200e48000c505005401240c2e503201d400032540c6500040d601c1101d00b0034040000052009002980e502d0100010b030b035220500035903514824075224981c000745c03603034410110710342c0f807405030007101c0a0710b03c0403106103403c4000e5040010159051203001448403000e2500141c40050a41c851114500107031500090031150f0300201000e20120b032460b05401910341d00d0304900b51240114072014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 892934505 1250 892933255 892933267
    0x150d06020c15010807080304150c1a010e150a1505120f0f0106050f031303020709020c010218040e06070309020f100804030801090b240705030426071404090c080d05 72
    0x2d44659041030340f100a2540205c24140407032403011044505548040d41d0b42c00c580305210030220b41015501002500000c100411940c114042c580098101c3d58042400c22050301c4001c400360f10b801c2409030440c0d00c81c0c1300010400035144600420801102079080650411821950241f00000105c0b60000011281c008000e034a8241c40c55403405440e891400c0d6040a1261403d10018070005d04012084203400465804141c405c20928010700744014046d9160021401e44a002c0d4110410a019440081da41c0c204941010302c240d107007442101f001801030f034440ca00203800a006d1000280e0304808110200783c0c0075100c00350740725801c4545070b0f0740e421617203880d050050030b00c4c4041e00154050b40c00d090315000c0341c1e5208480190a80c00301803075051035800021b200d0849100c0c22400414901001c9000110344400703182004121005c00b00d4803021690014070740303807101c8050080c039105001c4282450a103042950182102e04e01c115444913003240c885603800e281c05901044100058400030340c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 892935755 1250 892934505 892934533
    0x50603010906361509020d05011e06050d05060121020307030804061209030807180305060711100506030604080f0c06190e0c060f0f040b0a0c0210020a0308150d06020c 73
    0x9a0f06280119007607600307590304550790f69104040300c800c20110740d81d222481c1c0001d542e20040e80300201980800200b00c0f821340046189200250b050707003041541d140503000035241c02c12310703080d42d05158400c01502140e030801407940e0200e600742003109408102880140c005842c01c1051801131801401d040e91118a0014001c16280c4402441e003409030405013807200007a00400f1a640256050404041da0342ea030821500a91156610107041841110240304210307401032030940003414458161020741c50614030400aa403401e4807010340591110f40068082901c203c044c10100402801c1a450b010182d241c25103051400e8400c0809003840c1442071034044c40034802c1400384403485019080750340900b000241ca9003d8001c43c986401000120030751003050700c900725006801441c0380a030b240d88508c0c3d802006544014022405006440206444d00d400001c03441040b55055031103000329602c040740340c5804c9404264891300403e1510400c0006583d034005011000080002800090903501c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 892937005 1250 892935755 892935821
    0x30313081e04030c150e0d170f120906060603071d060d0f0b041802010914010309020a0e0f0705040e180c03100912051c0b030a140a110103110d050603010906 69
    0x1110309000b2017146c4c1c4042c80c0c50300460380303602e80c2d08036945484200e607048040d090791060022401d450031300016000d804001400740d06010b1615001107581c2c2c0c0e920501801014841501c10b0408035000700720720000b003aa80d0307400502c42a13010340401d0130b0070034000c00741041e240548519114252118180c0c8890f092522900100d00310544454000c10400c0c0c001800c07010040c007511912181d042a140016406508030b0003419501402040826a88070282c0c0c180c40c0341131710304d228000c10381c40c0800c4541c2e00c184191002c3d030f84484414020b1b510303040d00440c9031000c01c00e80d002142c0140300250341150390a01228030180c44404000c02e80703c401d0b103051902243d07a20700440c02d11505101d40c800700e400c076507c11103141e240250006501ca9650b07001030714180340800000d0503548140309030701441c400401c1c04030788c46101b200d69582300509000158251202900345103007001c000d0040c55411210794200c15041040500000781407072881d1598005d540c0300c0c003002c2d1b0180d1041c120050b40901201c2c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 892938255 1250 892937005 892937039
    0xc3727050601051908060a0807030f110a3005060703020403030311191b240c0e100507060f0203130209010b040b0327160f0503030313081e04030c 64
    0x4038210303103460b144456265013021140c03290000c101e125030000d100c80d15041207820107006000100ca410300d540340b910103022100401c00f11165a0280a411458100450f0082c1601e483d045c00c0001c0680560251101034440c840102400f00d100b81500b000c540c003030007218051142950050396850960038040e06581c0c0c1c42c190328490703110800071600c94038140c0c24140c0c504116490301700c100c44080e0800054400028101420403000300d4402075000181003806010060b50900500c0116030038070081d2000c240351040c803608189014034071100c1d284100b0081659a1080e84002034a05510349000200d0f0400ca41c030f42111100041c0348804e62070010004c0f40108001d1184525040c10284030078194040034060340c24541c4440490f21b0384a000307004860808040c14210345040f051000c90940c401014840d0300001003810b44c0100306424080101c901c50040003280300c0508480c0c0d56108400d03404918107001c10f05582c0402040b40c0b000d1001000110300a5a40a90490a0072141500d000280c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 892939505 1250 892938255 892938257
    0x80d020705012f10020a09170f0c13020408060103051015080d050d110d05010f0617060d0f080304080310171903051e0304050c3727050601 61
    0xf03a4601440c06401e035080080800160658403042c4505004146069050f580e16448140003083d134841c06948526a2011101e14900700a4100c000f840003507280c0300b4400b1003011541200c5103032801e500304241032900b6800003071801441c05a41d01b40e141c0c00c0007802c0e001280d90f0780242c0d8040c040343c4801d00600301c0100004009a044138032f0103031300319695600c80c200321040c8400070403200c8409000380e11200c00e4812182c4170a545521303000150000b0300d804d00415010152285010804606c1601e1060981e030003420313030300d10a03190b800410420011005c02143c55189045031800003c8104014500403440703aa04140c8a0401c0c581d040c1d150880d91704004808029200300f841c500c0350000c2c100c26882441c0550301c55200c29410100c58500c607090a20f110f8840c89602a03a41c04180e0000303602c500d015205552480710700c01e08016448007240c9401009124148440c100213aa42c1c00601180700c41b1000004060313900d4044007680d05000000d00058082204140311015031402071a03807224003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 892940755 1250 892939505 892939517
    0xf060306070801060f120f02030a1409030d050c0f0a0513140f060d1413020103061514030901090203120927070311040302040f0516030501030b0105060c0a0c080d02070501 75
    0xc45a0000c00b01c07001403180c1c000f040000d54241c1012402542c0a08204110707034410700c030742c81410310800040d500507a699280307103180080c07958807200300d410114040e1a09201561402c10402c884001524000d070424010300f10800550038510251001080380e0341080e244d880c1c94aa08040440380046280c0c00082c2d081a40e0240402035520382d1814000c0a6040768010340303038030030f4400c0c3c94000e09054200020900e2034406000000600300240c44020f40300b641c051010720b45942890380f890707505000728000b20f011013142401703035142e080265600540235800000c0e190080d800003442c0060001c51070303666400002d14a4200d0603c209a40e0366a00b040ac0340342e41c684900c41ca0794841200080441d02015a501e00155482d10a041154001c54004006010305481e040e0b08000a040a44425407251580040054a81e02031700520381201e40000c48401540e103080c0602c0581da2103c0c2c0192020b024a5100c00c00181548011902030304610300108050348201001915296842e00041e040c421 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 892942005 1250 892940755 892940761
    0x14071103030601050415020a0b01030809031204120f2a0509060409020906300706021903090312120207061401300311060a2021040309080709050f060306 67
    0x10700401140e01b01c0b0300c8050360303c20040008804a0510b100000c000341515042c4000006104018001d0410070404601b07585801c444211560000d2003948a20003040c007040401c2c0021414000c0002a0580103510b2125003184a0f01480240c00500740c0e0f0581665640c0420710032410300684013940030382c00b030b1002c000450090700041c806002c010038682c0f0503501c01c5100d600b40c2e8042c5100041c42138103130f0342800c03139440368992190300c0b0b082901883d0018030403008003100c1d2041d03004281d4055038046d250001d82c0b41c2140c9a03400c106001010341400e001c5a02001e44104a09100070201140035900004803820710b00482c1e0015103069200545141d48801141014080c840701c040c0900340c4200710108800c3d10b45020b9a400d410202029042e01554041002c6004d0641044499046d4591a5441000b81c1801d510b594041c1c812001c03000600b05000e074000c40d000010b040d400c41e000f400d1110580c0c1e503403031406180258940183c0302c00c640b19010f011420030409480d40d000101107014112900d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 892943255 1250 892942005 892942007
    0xf07061d010c021e060f030906071b060507050415110f1b06130504140406060614040e060d020a06020c092520100e160315020708040914071103030601 66
    0x40c030b010000e44a041182d13078214580440080080701c80c00c010342aa41c45151442c400342280d001181d01c15050f0103001e00150103203200d0f0300c803205080c0420400d6992a482919850000c4c440200b00d5018010200700100d1f0204041c1c08103c0844601c0e0f440c0000004c1540005081016074600da459070340c007021a8901e00400103c1d0302e07100c1c10003500c040d503c4000c010660403441c3c4183c2e0007250042e2511809103002035184403c0f038410350007582e082c003441c2e50300d01d400ca5121240c4810b260b800d040c2404180701c000604010b07903070010070041c203084580d0710640025180c1c4056600031805a441002540600c0c10441c1409030b205655102c4801060000a5074090ba051070040b2102007100100100310580540d90820519280300343c00c407038840ca11042e40e07030700801400d00170020030b02c950b4200314100c94803038041c48243e032707032040c03107a800c81c042400300380c02031740101204642da83d0040c0000700d503000c400c2c07107038081140c1840503a42d80c50a007400040d1059800d03810070007060f04200100728003a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 892944505 1250 892943255 892943267
    0x1204081c1b050708090616020307080a02010210090525140105070c05091e0910061401120b1810050a080a0308061c02040903090504050601030e0a140a050f07061d01 72
    0x10480d8101950b41d5040f920f4804494418a6074403603000320702090030416002c0ca00b003020301d40c510175400c4031800780c0c607800349541d111300c200070080c0160f100d40d0354a40e00344441e810070811a803080c0102c0d98903c0740d031b5108071410000e181710040c1a0b42411001c0001884080d48260705080a0801c140703824069190362246405a0141900807060303100420000601e0000700301884010700404561401c041c880c0701e454000c031041141400f030500300017082c44400314581200c00d110584a40883c20702200908024000740281340d54805101e00242e48401c0d10181414400c441c58802148464100010014900055041b040c01c1e03910823240308002a41004680340c0101040b40c1c00d5000301014008041c4d80c07903580708003d4006091a4a61301010b410042d0441615401c0310180926071321a0011411554044184a0070341d010106d00400311b0b0a10381050403500541096501082042d100c2601e807500381c0802e00707400d0b0310035401008504d500030040b00c0e0484004109400f103d859200007800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 892945755 1250 892944505 892944551
    0x30a0e010c091805180307030201021810050d090312021b06070903051e0a02120115241209020315011503050709140f090c04182007081204081c 63
    0xb140c0c1d504007081c00171011010000c0540942c0d41125556411850024080c4d000b0070b4907081e002c0c20141d000c2d40645400010003480d18540e80d200c0741840d0380014040f0261006401c15424002604548502e400c014002840000d94101007a200c03211104802c0340380a80040100d010450050018000620041a0340c80c01c034249048100c0c040907202c004500b0514100c100030b601c0304960012040f0920103401c0080c94600c048403502c10107585111441c2103a038020824243d441b921150324501c2c038040c4c040140201000c03c40003030ad021503030740820300c0c0170350005113560380c200320500400618000540310341c01ca00c9940703024080c03400e281c030b00501941c140740070340c10b0052078880b040c100b1030b00c4402d42086150001000b14081e030400505100c425072050141241480c2480d518000020190150400038000001003482184203100c584000b0340144104845414041103026421f119041d209400303140503584c0c0e280e40f4400003c40036080c1c407403541c0b959440d5091031055018500a5052070072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 892947005 1250 892945755 892945799
    0x1911521505040512031806070804060b010f02030f07050106030602130f06022409190615060201110706020307050c070905060405070e0d0311010e03040807060207120807020f0a0506030a0e010c09 85
    0x1440c0c0d10396010484201e04451503400c031b180708510401880326030100405010300e004034000c2010014007401104c0d4a4203002240f80540d00c00c002c1510384a5980d030040110600130000065102e80b07a94441080e43e200003150742036406000030520503c5084010407005140030300080c0022040000d0035566540d24801050056100030001084080180720740d00c103a03240b480b01e0002280052401300010444079400092200804034042480c900521a100055400c0c62080c0d090039543c5c0d0707524001c2c0d40018005010001c050140c07841002007040100c024000b040c4020031503107071035410f110403a0b20042c041400c010340c642450501d0b40341c0c0f40031080d203d034042c81c100f020128500d100502408650445075002e200009000074040c0d4081200e4003511029429100d1650f40c42e25001400107130f500d4068000c65003005a0801850808541018201d0187c1216840341e42c6100056903038004071072401e041034603034040880d208000e109003d0080601d05100f5000741c1410f5007030f1800d5240c003a13108 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 892948255 1250 892947005 892947007
    0x10e130602090609060c0106031b1a0c03090d150c05120402100e1c110301050c1602130203072019150b091911521505040512 55
    0x10800b500c0b01802c441041360003401003070b500c4500c800074900170101480f054401c8481c1070303040040c0f80b10031000502111028410b00c4800300a4001e100c5069100009101092000b0081c02d0078545440c40c041007607a0081c04020001004095860b045c1c43c141800501048410020f4022206201e40c40300d8206030152034044c0c011131111070548010f602d21041c984e03c0f480750f41000204441020900c4900c5200703048400d5402440400d1500b6580706454032034000c001400380d05800310701c034502c6070305890004003100c0c07100010100c104200e074815241038002800740c440b90025007800902850002000c08010300030360803200d010460000440000414140305030142c00c030400126003041200304c0c40204403041c981050303103004a1084001e1a22007000d4206000101c1c0307105110140c03415010015100614610003052503501094004062520040c08809030200b400354000700210070f60020300031800d284031604004809103944442e441c9040d04140030000042c001041d0303c010100b22007811 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 892949505 1250 892948255 892948267
    0x801090513120215090f1207030e1023190f0219060b030601171e19030c05070b0d1104030f06200c06070306082b030b0d0602040509010e130602 63
    0x1c904150f0441040141c562044d0140901070784042000b40084440104403117415640d2001d000c014054000046c01042d410340340c5100c81e08101700f01d9584449a86011451200000803401612030100c42c003044642c8042070885180803201180c142d04001c50520055000c4100d9000b903a42c0d0614000100317000340e403c518800c124443d00900e513403100042c1618810741c1c40b440b040c14421510034112007a0310600d0303080001203c4140100780040b00503000b5203030440c10744040003d0a08100030403000c000104c0030035004107000b071001c100605071350404107954100d0303012010300b90b4400d0102800001d400700010000500500884603103c0d03400003010942e1900c6000b1084041c202c840c00740c0c056030000a207500320120100e10f0611403180c1d61810010684c642c2c010598030440e8903400c0750111200e46207188008403010308060107019510740400c11510000203c0c119500d9007600b240c00304e030042002d00c900d1070030060a03805046180782140b03041c035240c5000d10350b00c03805080c041d003160b5000500c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 892950755 1250 892949505 892949507
    0x20105040659010b010305070c0b0c090619090e09011a3c041a091527090d020d020a11040f06060e030d031e0e0c10050307080109051312 60
    0x4008015050300b01d070450382900c094050103813a210400c240080d103000700042c403280c0141d240701e00f4140c0080f0100c0c00f80d601c2042c190760541c0140e4900b98010b10600c540c00c28a40001468100b50300180c0e034000306030345003c500311841c400181100402e64101501d03e0200c946280c1100310581c8210b42815001284120500404246020358241160842c410004902c816414106035510684041100c144482c8454a48044492149502071655404641010403440300001d60f490010401c00328001030384414001030960100d400500302d801020450315400c2032200c40f204c40203a00242142c9480004000c1d00da1017031010080140c49240c884180d2502c0759400100b080d100403404000c41e030f403104c2010b850040201d209501c20310030345c0c5070000c0c024801c0c01181400c0c0f0700503195a685014424682015108583c3c0385000382c070900f0304071007080d60342c004940c014980c9922101da880c1000390000b024078070141c12810485091005200e17410801018403010b0b983c10602c807500364018000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 892952005 1250 892950755 892950881
    0x50901032304031724090402011403010f0806060301050907182405040f0e071a0906041e170307080d0e07030606051c02090c030c0706020a0201050406 66
    0x203404184404200700410150030404994040105110088055885c041403a040d400d190303030010300d001100642001d03603080200d41c0307540180c4141800507401c1030000080e030058000342d11a20802c4006042044003800602406811650903002440a450710b0030244c1d90f00c8403070b403140064400a18088103010407007644410342c03010500b082c010b0b001c001d100e1011740007107280c01502d110300e2615510015010662103000851000c42c409844024504080020300c46480250820100d10400c0200c1c06580c1c0c81700148041d007032070340f115190315040e1140064410703d150481101009007500701c5081e08000425900c0c00d65000c3c14580c0e4604400c00190040c00b41d0101011191141c01d90110070000c060700040140c880070703510710b1800c95180400b54800d80001202942140c0c1d4900800c510490050045030b00c42c0514080c0780c500b8105070f950004036401400441c0041c1d5584040c0800c100c01c1c0d0065400300818000b409140380741144c3c410200c0d80c3c2c599131700700c2500c4074886c0c1c0d4090503040d81c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 892953255 1250 892952005 892952051
    0x50d080f07060e24040302060117010902090a090b010f0b03010e0402010c0f03111b06030613140f0103020a060c02061c150b1b0706050703030f0207020a0b070b06040c05090103 77
    0x600c2805210104041a6554154138646043c01415102c02c148401c14043c4124030442d0150300034009a4a0255150108011003262035142d54942070100c0150302c0380715019001d0b210308400051400041d04040c04c0c40b01068000c01c8019010745401c025200f949000e8074156451030b500c0d400c20340c03101d10040c1c13441e400c080b000601d101c000481e8101456080701c0311100d046220303c2914a83c1021070200008079080c0c0c102a0790000342032001c149a400c1030303e19840d414803826000074050b0042e1082c1d91414204441400b40e50b10958014811820b182c1200c10080c021070a11401e0250702d940045d403a07010340c8824281d008103944d40c80d030303111945800c0381c1102c803281c2c9001c1d55001e84a0b10048092751140404d41c0c4051051283c000c8400030001d80201241d84507541c0b20304002e400c1c0e8003140940100310012417076a4080c884440581e5520544800800b400c02c0081d40d0f6421924080b488000010651803080740350800d40c8081e10b4100c0e0445907000400d190000d10001403865520b048230b070038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 892954505 1250 892953255 892953263
    0x14011e080c07020a0b0c1612030503090106260111030708070c0f1401020a080609090705060c0c04060b1b210901030905060a061d010501020d0e1c081c06050d080f07 72
    0x7034130001030030f040035400410140c1000f0003500c1060012400007255501e10b0310540c2a600740d04d10b2408082449400a1a00492080c00128415682d50038206188401c201914400c0c0404c0007071405d080802d1140b00f01c0e05060582e86030451900c25009000240010017a40c11702605565141c10400d1480b8411840d03907101181c80b514420002900e8002d4200b070305103801203945000820f80381d280ca030504500c035240540091841909201c07d000e21900000c3c200d003081d10415905409994885c0100c1001d89401c5a42c1c80c1c032101448503441000c0802caa802c80c0c16040990342d2500c40b01304140015811041280c0c40c5c0e96426040012001460000000342c100d001d501d041c0200d00d5002e400038011141903081c0010b00d10401100c2881005080c440d1501503413000c0c0042e10340b58098408445e02040050100f24410000f00025800507410f030022a280c01c00082c120072001000403026601804a0808009041c24a0046078000c03609420103030400d1000700d4040804481e1104998001e0b503c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 892955755 1250 892954505 892954519
    0x170a0201021227010e030412150c1e0302090a141302070804170d0c03080a110712090911040504090501230702060a09030f32030114011e080c0702 64
    0x841102581d0168a0491030b20f074800480316000206681401100e404028040c091440c00707140080e04007580040001c11900d00043d070b902042e030b002e914030412413044e4075901e8140e19401c0101345c0d0749014402005440a043c8180042c90ba252100b084800548400307500000825111074000344001010007200c503035440c000140079040114210240040324003a890644080703142403552620340840b072800e240010f600d15100004644103900c0140c0100c024180002e6000c005152803074a580050800d0341d500444a01c40d042c483c0d48240d0010050040c00010000c6d03095690051039244038500c503040c0300d01c0d08d81404c04140030081d8050b45068103141d6040d4181e0801c0490311050540c222800c03009802540c00107064940300e8041c410000364142c0e1201c0d50702035a0071081c1c2e00b44a54001c140004109542c50403031404041c1e0b80b54044480e0144a603481e50f240c107a6680c4881006075055040201c0100c0d00c0d2a140c40300002485070403d54149203100303030fa0b4100f04400070302a0340d0703000e980050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 892957005 1250 892955755 892955761
    0x20606120f01111305010804050d0305060a0b0406050903060a05060102030405130609020301030312050708060901030b070915090f0b040302060406080711010908071101090308030703020f09030a0b1012170a02010212 94
    0x350006010111204c546000010781d9000192444c403800c880151058100700079400042e4404c0c0e10041d80010020411004141c491101303c00507003054021001007400080c02c1c03072061404200280c4e000c640d10005015910300040002d40743c1c083ca11441d0b000c1d01860048450308416904500c0203070060420864581d039513810028890500b003280c00a01c07910304004946240c1c4109200fa100d103c0292016009902e1075464240d0900024004810810407483c003040120100b200740b10582c903c0d40e41c4015260400760421008042944403150f462410881000182c8480c030550302200c45c14100403031183d98031038003543d00d101c1c0018000c016500e800c200d0350411078468042c054940c01002c0054600320000c005441c074003200c3c0006844040c00b403001508035440380e00140481c0c0b5140c0941030602000713002080c90048801c1041b540b2280c0041003000f54070310804440020041c10030340002e88445d5803100100010821503400c0f4040001844082d1076000350104d82110800e40c07000c0070140b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 892958255 1250 892957005 892957031
    0x402090a120f03080c16080c0c09070908071409040602030405160b1c051005041517010c020d08040804030b04020616050c120109031713080a0203040509070f020606120f01 75
    0x2c034512070100d01040c2c644000c1501d40029100b82c4041210746038120000185a4039402c6054019030f5500c0c0141c1301300c00c45807046445400c2400e020391540d4450186850524001c14101103c94200da01d04003208007a50403181d0f00c06800e907400c150040001650307034689003059800e004030816030716113100241e98009103510300d000c02400260340308851140c0500920b50110700359081034441e40b030020020300c814080c0d45002c0d40500038891065041c040c08030f40d01c4106154000003c240101c107a5994070018a082e9018441d082c210070051414600914140d41e95900c1402103002c0580250103201c00a03086450380b000b140d030290448090180c907140c40345003c41e46c0d01000c25000380100d0400c0c4034484250070500414196035807544540405500081900d08041c1c4010400950800b94650305d102040c0c42c01e00602c004076013035010b1680c07641040140100349502900542c100070034282007000c0c180d400300304c25420200032941450118500381e2200d141404864a04441e9440c19000c144c0034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 892959505 1250 892958255 892958273
    0x12050903090a080d080a1407110c040e0106030c08060402010c0f050a02090f100609150e04150b0406032d050a09021908150c1b010f0203040305180a140402090a12 71
    0x13845035607490000c5944c504c0520300503124a18001c41603140313808041000140103001030402d2500c500c049410520407000003800786d0322055600405659124000e00901c80c8220080024110710380040c2018206a400204041d218070000b070b1850180300c00300010400b06219458185400510a140a092410441d4056501542c03900f0010642c6440000c025020305461012101510b030007458043d1100d80c1501e640108102669006649104081c40040e1030075152020b454107440d0301d92034509148001d4210740203c103102c035401088080e125044649803408100c0b1325028040131038252265501d1034050800110000d5118801182c04442001261210401c9071004000c507000781d40e84880040b0728480c20f80700c00410101c2004000310042c09959420103903141c400c0005000c0b882144c50908980094070100d002440002c0e09020002c6803000590710701c0412545001003c3c9414140000b4a2000302820302454020540384142e40d1401360744801422010404802945039203464204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 892960755 1250 892959505 892959523
    0x807031406090c0f010f0201061e0e011a0414040209090c0a090b07120f02102306040b0109090b0d15050403020118171303061a15070312050903090a08 66
    0x903407154100044104000160ba0700074a540034203120f84585165004481040e000808042950740340d0f03030300040505500500e021400e10000342c22161904083c40c010801d407043c0e0106500031003240c1020714000a80f02150201d400b030701c004100d00382000c0d0104002e40035840110303900001c01400c00c840f03003184c0d800406031081c0c940d80790404203855001c010154081c440010784012210481082880e01422911034a041d0b6030044400291810300c100d01907a100c82101d8600816942981c0f20034003004425542000003103c0500c0503000c4030700004e04a400f01d00c070b0320725041d4949000c3d00c51030315004002040242c00c0080079514900915070103000d0720041e50110f00561801e00302d50403855181c99110f504541c0030340203070040410151800010340181c83c4540a142c8041000000551184500003501d030040113045001d0707026400308441c00000f01241c0c80c000404019803000641c3c0310b8409100314105c004001400d49400608504e14010380d40318942003004000b021440394000141030003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 892962005 1250 892960755 892960793
    0x60f060d030e190513090c05100c0b070e120a0203010c05030f0403030b0f04090602120a0203130803040516140120030f1b0f071802040e040201031a0411040602010e151f080703 77
    0x31f40b0990f141c0600040c1c1086ca075011002031001a580c0c80007030200d02c1c000e500098685001c040d010036050000300c803411a440301e03840b1588103440d080e08500f0207008180c00c0f141d45041c09821441c28021040c400d6000400081c20907540e02e020b00312079501c07513210440c110f4003e407040280711010300d0800000e501c103c0e40485605049400a40180f800c1d0003100e100c1c8501d80f80003d000055540c520782c00fa00090021140c0c1d000d104100031102900c02c01e0480103102d942c50b141000b000e408000350958422002080034054032110790412840e0000031602d6003225040c00e20381e0b491034103080da030540e01c0401d05d0703652502031000308051044000440c1d005a40f0704808034810380003206540c608a10551282044984100002801560003035000d8440d108504070703d0400301c403078000010112180512141030f03145c00881c050040980c240b054000d0344405000400a0000c003407a0350386c98440003003a071000040d2244880070501140e620103001410b4280403607040315200c0c0341020750076060ba11000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 892963255 1250 892962005 892962023
    0x80f091e0a0606211502091507060b0409052805010203100e250c150903020601090b030307050c121002040f09110901120509031308060f060d030e19051309 68
    0x800c1d030400c5040407050307072103014030410703164081c1e40e0360152859100540100003c1e400e1090450310741b070703400c8d4040b50240d1002005030f444005180c00c0e412294807051950085180c00500710000f074002070000907049080c012564020040701c0480c044156850000300694008002c0c0001401200812800d40d4004202c103070a80d580d845440716500c13000340703000c0300740d4045d0100441110300540889220078019400106c649144270071003000d030756001c0011401640301d03000400402281d88110300c01482e003140a50701d0018180c4031180c3e00e031480b2080c3d501ca1002c41e05803d28040042000c180780008045080d51617641d80c808440000c0618401d8108450034490b42244031700120b400c60340d60000585400500d00f1038007005600809008200343c000703100030422540a5000b00804200821100d4010041c0346030981d280700304d03070b000a03201c6401107a018000c0f40c006608400c404005070001d0783c0f40c1300304120455030024011a560301c00340d0040c0d00280140c0c0c3c1c1001e660014614580200644 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 892964505 1250 892963255 892963259
    0x4230f06060c1002030601031803170109060b250507140a121a181b0a14010804030c1104050412021203090705040f09170c0c030c01080f091e0a0606 65
    0x211509109002d07141100e078102c1c1c1e94000c81c80d04198055500441c040c90005403a5501c102c003480340465130103040d0701062800c242480d0b03001415040343c0c050201c205090001902d01049000310f4000c8603000f1240c0309007021060320103085031031410103103600002220a919a9401240040c0e010a10011b000b400c45035008504015180802000b013a4041c1c1d2045185500600c141c040120160043c000c00701500800030b0710410800203c0b180d011041e414192510084080000060a035480102c03241d00002d8010540d03078000b800e007a0b0142e0142400c40b50001d8500c1c04070035041c06200000e41c801e107000140b1045c05034114881c40400f800d5001c03900d501340c001c586e00510307000071100041e190b405008140b0490600360880702540d40d0201c0301040440d00c541c1c403c0c0b61210701500290180c0c001050480710300ba41000307444402e04081d030103882c24000c80c10000300162002089010034034690008210080802c0204000b040742440c9038807a8402d042c800343d0344400c0c0c0c80c00195951400c6c8100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 892965755 1250 892964505 892964509
    0x412061112161205060d03111510060216080a020d03050d02031005030c2b030309050d030507021005100e0402030a171902060906070c050723040f18060b04230f06 71
    0x1c0d09014650007803070511110340e6541c1c2288d42c00c918801c0d0711b0f264001c825549a90703070030340c80744240a83d4200404015803800c004000b403420013820000b10040e05411010050b404c070105003a84c44d1038041e10407400491503410155007500c205400340d12404d00c008100003004406040f10003c2d1030084080d100004030318800c000402c0401810711008815019010240399285844103c848c0d20904010484a101744c0b82d0500b0515012602400729331904100441d180d4180005600344146da4001c00c058284184d00b81c1603c00c15003d0b0444804888001c40c0c159a0104040748030258065004034000242849122180d040400503603040150f00c0544024170b400030840c14481d100040041049644810b42200c1e10140e001c0161094007800c4408946a9414401040c40005459080452142c88401d000407258248403802e60031b490401d4024045d810002c46918568001d00041030480c034880000d801000f100c3c207803070041000184c0400b95002550615031282c400481c2c03021060752400c007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 892967005 1250 892965755 892965761
    0x3030c180501031d0102041d0601081509100306090f020a09060806130804080d020a150b01120e0f010f1b030b03030307050c011805030d0506010504120611121612 71
    0x1061002911038400c0a2180394800e43c0005100c01c0d0814045640c40149030203a422684290841c8650401e981c1d5098860310648412035042007007840c04086901d815460b02034890310f4080a0741c0725010300b80c04a0020324200703140a0146410040820500d195890000c08013100002d00300c2c0500904400090010040d01c1807400715050a00600201c0e074881400c2d00c000c400b456001c4400381c9050201048a00d0100151504d648886d0001d090030b0b10303e4140b05864641e156804540705040201d070504503680700001c80d407400030000c800304000b04540d205604024200389004100c0d032034000c0b0580442295048a44001c564103840d46044410540071016186907840b880c0d016031080000c5410184a44020818500b00400000c0c10400541810222250801c0309032a10351000c51015a10801031040a81182d001d00b000b80c60689894101c1d8101d200a00340034002c250340c1c2e200c0b520320300030480c2200e800c0e000000404480d45410781950f02c02412511103180003595401040140c20b40f684 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 892968255 1250 892967005 892967027
    0x1050a0204080d05032707082b05030907030b240a0509061c02030307030e1305040b0a1d010905010c021c050301140f0d03030b040c0806091b04080a03050703030c 71
    0x18002e04881515039801352280d03800503140946102054240010340c039020040003480c100800050124a85045030075407405801c0b08010b404100003e40c0c3c082c1044000090381e1500825082c06503c90b6107501c40641418a07540c4050034000d9000100582660508450700300c07405282d40083c10740584009000f0390340b001c2c0c022903401511142c08200705e881d00d15041041a80600d000144c004429804641140c2000804501003080b40165070042e00c1c06c0c0c528501d400500c01400c2005180c05c0d10790321190940a8940610581d559441c0a100240c00084800e408000c0001340802e00c2c0c00e02e4614000d03c0312581000040c011514004d01811a03008001c0d25900e40383c0c1c6143c2540d083c2180b00d1101002d540c21036030b00c03006d140740d400c40d184c0b01c0c02100680300380291000280710000400344003e0300e0301d00d0b01a00401c000312003005281c0ea51004a150000c2000540808070080c58070710354410300c2140c000103c54811940f08030700f0194410028203000c1d01c255070610400243d000182c0340c5142c00c0e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 892969505 1250 892968255 892968269
    0x41103390a0f08071809170c03091905010807020d1d0103060914010504110705060c09030c030334030c03030e010b1206040b01061701060806010905150c01050a0204 72
    0xd0500d0440310a0390300c0c0102a411001030088800940d40e50296002500303c2d407082185400c060300c04c01c12006455042c0b880c2c3c0301c1c440c1d01070241444170f90341c586501c2008482d14014040100c1e04129031a001c100340d501124003d8466110010340010640c044101d51142c1d074009004040007400d2548041410703c00300ea4030380c0f151200c00c10300170800c03101c44840c0b034851410550b40c0c4c440000d410b550b0740503130320b43d101ca201003800e0203505040a00c01a0342c40702d9014242721804000780c42c0000c40014013203074013006045400d6107a6003800002401c1c207150241c0c032507140c40b0108504a9010001c0e0084a074042c40001050b9401c01500013600680713039080c0041e0100b031465241c040468041e4200c00301e060849000021242a84400118800c1c140340e50351010f5401a030800c810020401c07071351400f420359414005c7e140286e0710790b50400301d981401031a041002d044007050702c90340600074030006810006c00015107007010358500c000a0300541c400071182d41c280404500210494801c0b50140c400c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 892970755 1250 892969505 892969573
    0x121d030d020a050f0d02061914010b0c07050103020a020d050705010603140f010c03050408221e0317090616050a080a0c260301090b150f0c10050c0a0c02120105041103 73
    0x9208944031064050742c8480c080151505540d00d07127411078911a60282520006060312841442c2e100c5291036181d030401814540304002002c041900041e800b4201081442c1056444549182a901405241c2d0004013003d50380e6840700c58460012600001e1106010000c014200e40650110f056034801d03103014040750f204006001007450082102c0488800d4194800b24996032401c1950142c6081381111210400c03086d0103004102c210107000040b62084070000b801d0080420005140b44a1035012042421250350402c01f08a81403149000064200007240d4480c514240003810003400d403601201c88011000705c01c2095607544c0304c12100684480e500604583c05e00c0030503402041071103001c0b0ba20203184000c004810130b2110040c00140700010440b61500c22040c4032074a032022610115080905000412943c5c41d0414103682c0108014500280541d18138000304094204100159015508180400084c004680da00d0040342c0d601f502200d0000041100d0400d88544402c4041d41c5e24403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 892972005 1250 892970755 892970761
    0xf060f0245060712080601030e1c11070e0403031e140609090a0f05030a0906020607020a020915040f090b07030c08010314150a0f06060507121d030d020a050f0d0206 72
    0x100341c2164016080019260b10b00c0c141203a15080c0c082d03d00c071611000015280e4007003203080d59140c0a00c0702c60221000c0140b070001c83e500d000340c80302a00c010315001000301d9840c1d0030035051030411990008009501840002d400c1c01d090060141000300c1d990b01107180016680c0c1301e21b03c001c2c40741c07481000d22500484100e44030001084000b07000a0203542d6540b08511208021402d800c41098940d88150011542d07110707240c00c09071000354107a1103a000d540010041098a0390003140008105030f0440e80c0d8000f9549051104143c0281c90000c07503081b0f0705d002c40e000f07040600e90f4000d40403540605081103081c1e0310341400320700365010f03841000d0026104100400002e05030090314140040d13481d043c0c484200c900650b200c00d0398000c4031480700064561130101607103585803141801a160910f00b440c50044640c0710700c0100c00c1e060000004003c4000d544040c50f80042d035141c481900300609a90003a044948000e42c0e80c5591001a00d481c0240340d0031050796500059540f02ea2600394002e8401c84e5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 892973255 1250 892972005 892972117
    0x9050f03031b0c0a09020903010606030b010c030305040c0e070f09052205190c0503250f050a0210180203070506070b0c07080d0903033804090f060f02 66
    0x200600d0060320303144981d40f075a0000b80d81c0c800e00d80c405800b05480058540111404050035115180d1100c001d261034035460b2130607a640700001101403034040c00c020426403030314541540076400c01c1d4440b0b0003901e0201d00f03000d50540c0c0640300030701003180da59403841c0e480e84130010481e1106001c2082c000b800c052181e0036804501582007c1c3d0b20400c40c20500d2a0328044075624401e4616802440700050400810442d0080d036111108807412400303044503c006820078805010112880b0606007400b4001c180ca04005208001a12290350364810500940d6600038403281d0382e601d100c004910900803840b01141030f0034110240ca080940103940107000707071035000707402120391f22041c07040d22542c0e420014942d254045024181c4ca85120307990005c0d0851207403008036600c2d0f0f55203070890f518440400c6054007411080382c0d25105403204450015004400d440d20000034032800d50020101410941908020b00c0035601400301d402c441d4000b0078130f040c21120b4440404140c81c00c124042c210342c1c11130103410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 892974505 1250 892973255 892973287
    0x19080720120f0c07080105010302010c02060d0e0703062309120309030f03040f0b0105031c0e01050d09050102090109051801060f0905123304140123060109050f0303 72
    0x40300d800e0056801c55524140c1e010703240d41c440500c1d80e061210000b014000ca110412041c1c0c01840140700030080c0d5415940000d000c88442031700680301d80d1002c02e000c140030703540d6480300c49d42541c084200d840c0c8030ba032461300c10003070156400032000740d0300d003190380140c0801900b0005129010f40030283c0201256090b001c0c02e5900007500f42d5140e8441808046e6a0050000080d0302850040ba400c0d040a1040d103818038034004141c201034004d410108264400f182648401503101149040904004c00300c180100c070540590034020b25228104940201800b2041d0300403c40e40000780d030b42115940d1540284140250040f485202c2d000840004004482c81520421a490b005103040500d8903941c0002600c1d222804a09025580000b11020b0b20611141044104030405400a1710901d0811926084d0044003c0c005451078402140302e0b08084000e5001301000142240c41800da00f103500d40341205242c040341c0c0e0358003007510b419003c1800e04e090b404095200e44020000e45c60325500551144ad1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 892975755 1250 892974505 892974557
    0xa0b0d06050403020111040602011b0912060b031c05041a070203070e06030c040c02030901091413020f130303170f0f0115030905070605071e0201081b040e0408190807 73
    0x1c65503286c82010191103208000c00007000e0b01c0e40003185000101039107c1d8000070f900b41030000d104006008009160801c4c0120606e00d802801c006100740005000c00d0800e55650284954504036100382110550010b000e401501c3d14103075144c103200f10203003915015203e154006945540401d00c1040659071445130950b00c510054243d603042e01c041c50114044d070700c0c40340a6a0140c1c00104410086583c0003e204004100280001e80e00c8a20140411000f0b41da218100d10b120382c001070407600009160003110011525480c1020741d890b620700300246800601100d0030038105051003c6070030320030b034141c01074060780c00d900580e99070782d103082e016085013201044100140350702e48070040003044040c42800000d16450719169503c909911301000c1c0d1000b20507107440127410829000c00540d82c004be215901c9030511000c0d004084000000613403e01440d440201c20070105810041040001c0010301100442c0c44002c2c40303608500c4800307482c1508101c030301c100081c3e8a0921346010300c541c4030340700c45 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 892977005 1250 892975755 892975757
    0x15060906120c03060a06030b0601030510060e03030f18011d0618120a06050702012007020418050d05190e010215071107141207180f320a0b0d06050403 66
    0x40b00b50900c0c00424105003044071650140e6a403218104117110300000740302da0200c401d01c0d0400107407502803000040c0c03100034002c01d402c00c000d081520500d501d013081101d0070030381740300080382c0c4030640741d004a83c0141010b40414009280b10031641c0c0c0200c800860316010000050060742410024500100403243c0071071125070280054490012800003400715482a03400384001140510344101d01900752004101d42c011580811001280c205920200303442801d681201c0105603070303e504d42003020b0490f8101000d8824000c0582d4414601d1f000001440103490904000c40b41140e00802902c03480c441c4140e140c0035070040c80207003035149103411038240e0215640c14038030041c003501301c2c02c43d140c50340a4201a60084d001240490b03070380340c02807007407088250200c001d003202c0d400e00c3c090000107080b04c50b2100040b0784800c2d96071300c2001d50347c209200895004001c1080e034000e09000700044030240c04040c1c00781841d00d001ca200781c0040d01549001c0e003406001c0d48030145507aaa00c4005100040041e4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 892978255 1250 892977005 892977013
    0x5091003060e040b0105010206130314030a110a020d1407053a021605060a2a02060703020303060a05040c0e01051b070e01090f15140a090609020c1506090612 69
    0x1c1107402c003480300d46000318000d0000108035810a000a4036100c400307403034403481c071a214140380c001907072006104048418054009072241c85200404d0090140c0c000340d03194010300812000301041d400501425007880e1603550240c5800d0381d01581240d44500d48014003640c006900d8040320300048007040d1030340208a84c0501031907552504004500c558203032031000582008000e04000300301c21420001038a0700b114000d1604448100144c0506103441e01402685000d01d00712403c0c441e04040c1c480e0580d00903026603500e600b20701e0002d45a9000702c440a102d515040c0d0082403608144c03244081d040c90135201c000080d052040103403025041440358920b503070700c0c1455002b541003090150764000e1200030b0034107946504201118099412000e04807a000345000c1c0c0e0140c078000f501010604079409100045100fa420b0404030314444c400e504400d004508003080002c0180300359001301030450030711007079828003ea5640354000904095030510340c0304402c0d101107003061408144081003072414000b11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 892979505 1250 892978255 892978259
    0x2011b02131d07090203070504050108071110062c07181208091804020d1e1709030c04090f030e0a151e080f190b090108030414010801060509100306 65
    0x300c0300340d030301e18003008202c6041c50206031040c42c0c042142c1d03405009641025411490031401c0280180500c3c407030a810408101c0100d95003a002d5000184894580d009507010250790580ea130b1f0281860b03102d001d40600707074000303d10740111a0500c06030080030f0a5280c0015500c8644040b903c1c45400f181c610080d100203031000a0005c00209003c440360702c15148641c03100e0a01d0304004804042444071003140c00000100070044e540d1003203c401d190760142c40c10000c8016440d00d24020b07028094002d080b2008040e07180704102c0d0b018090440c0c1c03501102120311820452050200b03131801c44400400d010b10304440140042d02034401d4041c62403000c5c20380384009594200034200403440902e80c5000c14031901d118448209904002d06160782c02e03061400c054200f40b18500d030007180042c82e2100d5003001c0b1030100a071000c150440b003082e020043c2007030035951b16101059140d500502c620b0600d0403090325007a6065020341c442c00e041381d52030f03250b0500700700e0080c0034400d5840e60b40509078201b60303440ca00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 892980755 1250 892979505 892979539
    0xc090901050d05060a1d19030e0d0b07030c110f070e010821180901030c031506080d030902040b121608150a0c170c092d060918010308210402011b02 65
    0x44440c2c8044803411080c8842c7e03203401e018100110211060340070f402404822030125070303001825508800c071340c038000914400c20f60040b40c074948a0711422000740510010410150400a03d050a5a15022082003180d9803108402c0c0e1310f210b56600703d8200504500848100710480003d0507200a241c034403490021159000910741d050709030000c40e003142e07400c41c050041c400801105482c0c002c610404001c024100852035a461420112890030941c4900500085464a030040480c80c07801034001e00003006000c9885855000101600b00c812000c1e4400284500c00081c0200c8880e501444000381c42d100c550b8400040c4c007406141c0c80c00d01443c0d0700a0949401030400451050110100043d00c2e4107a01c410000954010401980f0602c01200c501451707442080c0e0741c00143c4402c8565540d9a403404012600c0c00383d02e070380343c0b251301300c480000041171100c2130300107000c13a00103060344401e5408020040070306141d081d10003074009250502080240803182c41c0720740116000600c1c0c50b035840e10100c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 892982005 1250 892980755 892980763
    0xa08010903091509050612060409050f0c011101150e13051b01030f0605010e0415080f0c010f0c110409320708210f07050102030c090901050d05060a1d 66
    0xc0214009042030104200d00c1844180040440c2d201e031900340c42207854200018454020030005030b03004000740010034426a210380c400c00e03c0552202c242c601601010b4041c50316040718020490108224000d01151287d041c070a4607015201c0c148100b40d21030410002c21580c490062404411884903100b4001040c003c02c054035454060020303030b590b40e50080b00010700399401c592500342901d04160301406660b801c031142c00000f040540d130016260100d41c00c83d1030320707000940c040c00190250001942c3d4042d00410780c910101800c0c0c80c1d2405100180104440c0e201c02c0c81c00103010402c0701c0003400c000b49015000145614003c0b0007803180e2007040031550714243e01c9070420501c46200b0003821240508140721030001000010054030341e40707a4800790115a10b602204250600c04005031000c0d0008145d07094608245c1c00100071512854624a20070156106184042c030800e4141300000303182c584107946080407a80400a4003039030311402080c2010b0684044803041502841e5041210490100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 892983255 1250 892982005 892982021
    0x31202030d0e0a29010603110702150301030209010e01030b0403030c0504091802032a0d030c120c1104020c190c210b06010f0203301302010e040506011d0a0801 70
    0x1000740c000d2400d03524040c4090502c1ea413000c02c40b94041c40519442e4510482c50720f0451380c3c1402c000c50f8212046102c1901c034030841030000e40c80081c000100e0101c06035140954140d074402c1d02e0004699032204500101e000782440014241b04c064800500024466003204100f0b8510342445810562183c0814060b10803030b0780340e04000c0c41e058219106520341001601d2814200451200000c1000300f1204003003040319503402e0280c10f5000042041600c161500039082d80c12030004003a60201c030300010202c1c0010201070304d454102031100c1e2aa441c0510840f10b184c4800801051443d04a000b003410042400c2415103070907074608000103138812005110340000006640c80f015584a0b8501001c010401400c118100142d980c112402c1c0d43d000001c031175559180c030980120005003807203044c01c0d940344c20403540700780407112091108080d0407960000c6454800d0301d410b20100106001c1c0b0080f80c02c04c0700d8050025a00458805640c8000d143c000c184100103010901100d0312400b1240c20b41c0c28074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 892984505 1250 892983255 892983281
    0x11404062c0c011413030f02130608030a021b0105030601031d10020904050a1104170705041a040509061b09030a0f0c0609060e032a0415090c05070804031202030d 71
    0x40c2c10a683c810140c0c41c0c2d24130340c4580f03c1c1c20710920b16003000c05d040341408018241a1404041d40c01e40d03176200012408020541003d00c1815290000180c072a040516000050300c1121181761a1882000e0b114101040c181e5a860955a400c0011400380c40c07121690b10050b03501140603d9611b03024003041c480c4d24103081001d030b42c41c102c550502040f0343e0000d203d0b10130f66203003100d201c0020044004072400c0301c50940c001c810503482050703071a090118070ba20040c1e11030301c0c0c90000c0d81401814030712842440802c541c10031250303403500c40310f40c1c0b43c0c00c1c11140d01c410540310039000d0040c18101c2c00a002c41050140c101c8650705001d645060440c0725100d01035400c0c0705481820065503a01c01c1c400d8010707000314681400d155240002080d41c60900e01c1c00e02114502c4009404215543e0341c8103114a864001d01c10b00202d4040c100d1b1610b08400e5000c0c511080381070060541115010b581202d51481c0d20030b003c2e524040c0740d6220b0306241d8030f40001c46c804500003042902c0d1304030403600400c0910419 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 892985611 1106 892984505 892984513
    0x7050a110f21090f151303080c01050907030b040807170703030e0c0303040501020a0206030408040b07080d0c08070816140a0806090603011404062c 65
    0x40e880049914410508040e074086400100714111085112006010328000d4440c0c0e44280314207180755812014004c0450a141400081701010301c0e6070080305410004a010480210401944196203a0701d002c0780c00e0a04030000c4c4501500004843c00a03c461881c0d03940e1039011080040c409451820046413035024040041c20504c15410300c0c81460b03607182c9540c64050028214a45004e42034442c0c0d21160015040c008220fa06403074050300248998612a8200030440d0b0004108a40030072040c0303c0010303440c0b40400a050418813442076603850f0102414001b0480e06510170240c10070080d9030921416a80041c45560032403000703000e020800f503011006030307804241601070010003000000c1c000d06043c0d0080300c4078000c040807240700c4105c2c1c407450101400e07101c0700741d55140e4600c07962001c200001d180754012044135040d400f0043e00300c581d01e01d500010020300c241a1040e500 = true := by decide +kernel

theorem cover : BRFrame.Cov 892805755 892985611 := by
  have h0 := BRFrame.cov_init 892805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 892805755 ≤ n) (h2 : n < 892985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
