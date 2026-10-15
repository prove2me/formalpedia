-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:13.929057+00:00
-- url     : https://prove2.me/submissions/459f268f-42b0-49b8-a7e9-4af823388ec1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 725359712 ≤ n < 725539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 725360962 1250 725359712 725359727
    0x3180706020613030203160f053d0e010609060f0503060903070f1a010e04061103100b0f070f0506010f060c1518062a02011e020906041508090d 63
    0x100d4006030480c0010480100c041040402c03098003d204a03818610300c50690110f40c5513141007118502c070240701003001c128080c4540c2002c500388100d9019080d200c3d134011a403100c510320147c0c24000000224104815031503020302192075016008000158a601081c801040035008140b040c1454540000765490300282c05031040c4a103502860511015681da254034503102501154412690312209603e0382d007191501d030003402c11100d01c07080b0303081a09200301107071800e48400d01e049800300100141c2031881004c50045940600c540c42c1d94902a2610b00214000c401000b0003001c1b10310300480c01e1003400034205e8103a550210080705050780d00c5400307a0381800003000c0109180c2e4440307020307140c0c002158400e0700c148040c01c1085d0990301440c2c1d41c040c03c4440e2240c02c040a42500c14031001c840a0b0300071888003490080c0000c02c00718a0359031f0140445051035107813042c4070382c0014512249403a080150350003410111042000100007207030144c07404a044640711142e100e242041024070344102c22 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 725362212 1250 725360962 725360969
    0x20f1507030f05240409052107080c1005060a0510110f12071221020904060e07020115060e0102120c0a1b0e0604051005061e040611160f0e040c0b040902031807 70
    0x400620b044c4510006103890b6080745920a500244841c5021500002c010404bc55003480a0f00d9040b48881c0604102c800c050002400342180400038400d94455a400c0300000400d0305101c410f0404011055140640d08404210240680c1c1c075200300014105025100452260b951504588119807040710280714200303601c010508030245401220303d65900804000401401c00f03d0761a440b400d802d42c840b0005c1c1e5841c1c1c0181e6468000c10035034201d200001002e00140e1416103543c40365100001d60350031000340010102e100020b0aa458070100b00005a4002da00507460000006c42804040d0302e42d509100710000c24a1103400540761785454421184903501c90784d10990f019040074203015032781e003003c020110005c1d450074241004a208101a000420707540d80d0b0403015a80a5070316504042c00b42e900001c441d5000320007800000200d004110664108102c004095079590030040b0303281c15942d108000f06140040c0101d100001034006502c0303100b0381d0211809072682c0104140d624040c610 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 725363462 1250 725362212 725362223
    0x6150f021b09070f05130303050d0c0e060a44010911071e02040f051005090421120509011b18060807090305190210020f1507030f05240409 61
    0x400103214039006030664055201d131454540c1c01e207081d540b8a500407603980d0300280c01160300070903c0c00d603500003802244892041890000307548a081001300f6600c0c001e802c01034003400304518201d12162a848000a058110881828413540c1c258030030304240d12082c020f51540c541700070004210000103024206400a840c0c040601e00805070310360801c040c072400986140055100c58600240e07445008003506240030b0b00300010b60f0f00380f04082e10400f41d01755003d1802001810200808204038020807030442c1d0079440d02c1148060411001c031000c031500d001007105146000d0070703c4103860055105e110259030520071803a003002804810780d00406001d2094000000c03411043c0700e0740b07204904494012081c1c0c2407910485480b9a1182c1c24455a112458030544288007654154907001c03036070b42c21140c410300203861116800501c0c113485111f200400b81001000b803020487e0141700398001c1c43c1003d52840c0c1049035040c81e000b1041c04200c05030740c01000c0040b02082001618191240504156014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 725364712 1250 725363462 725363479
    0x80105031209010309060f02071506120c050f04020c06070504030203060f1311060405040227120303010b070f060c0806010f050307170615041e080a11120106150f021b 73
    0x2400110090f240d0b82c0c05c21110140c03204104914001c06002820300d80c0d00c60000d01e071100e007810000740121003450b48000c03403c40000000d84c010914028071881640c0060700c400308200d04050225000e8030607561002024481c02c010080002c0d4050007920a6910072400c4d241e40d522401803064440c00300b80e0384000d41c40d8006000d840041c480c801d5051031001c0182020f4180340d604c50004c0c0072600149024644020b80b43c03400d420200340885d40c0100c01d1003c46600081c0b98200d50415036a02050003101c4940d180002d40c10144040d0191508207254000800c3c45818000b5200500c141001d90f030300b03130101d910780601c141c070540603000b62881180c107951a800601040e10340284c2502d40035282075080110000288403813246c400003840500002107a03441030016a1140705a464a82d41c018055904501c4443e00021005200000b100b074085400b5010880c1d80c0034801d00401d50381d40402010f075000302180c56026004540b000e00e400054081d41c61180f400090b030300041c7d9150700c4d266841400d9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 725365962 1250 725364712 725364727
    0x5010f08060f190f0906051002070b0d1416030b0d0503091908031218010204080703060f0e0a03270e0c03040c0e0a05013006050613050c07030801050312 67
    0x441071400c0140402032114902052203202e42c2c2400c40b03143c0040c5140e40d1810000e110000c420f0007146c009180646075014003600c1404c00079110841070051401c0c0380c100090b0000c4c00ca144ea00522004048003c481d640d07803d1000540d1121900110400040383c201aa0441d4526110f10401a00c60b00440a50700e0300840d40108160310520410182032094034040200300008100080d1141145100300102c441c10100d1081d0041d040b030324403034405a80104002d000200000c41d01d1f008076a4440b4010401c6400c08003118003418a07400c07002001d03c1055580020b25600001c11881805c0c405043c003901013100c8a1140542141d01503240000d000c04003043c103490454008651160141342400350307190311510344401d0540c05903040c0c0100b80c0c0320f80040c8629902500544c41680e071121303440144103001c40c4441c003840403c400103010300340d803003000070035a4071100442929030f000710700c0800003864007003c00841c64120b00f80503000100328900100315402d00180c24120401c0c0011000d041900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 725367212 1250 725365962 725365969
    0x1f0909021c0c090c091802070b01271d03180f011b020904030315081623010c02031c0314060a06140904061502101b0f0c1a0c070b0105010f0806 63
    0x28030b282c01303410040890400100380d141011b0405800c6404807000da0360b0700050520182d5084181c000c8000d540000507600740011681700c0c20625040070080103c1d041d1f401c08070a003814480e00703240880d43d000008600c903600e20b00c18010750036820110707400114400348500451b00d411400c1c9a601004005241d00000342c80e0134002079510601c2840c000c10318800c40a04d00041c920580d0080d203d40d4848804010350180c42c00c40e610260405000c440c0b140b140c240b28124218041d036038010705219080842105545050100000000c54549100c0a021005900900803c5da0020351458440040b0214000b0314120681c0d42c201c2e011961000c0700000150f0036404244d001208180e4003503071f107030000030f0a0809030410503141c0381240c002e402c03141c0d0041107803016202028038980c80c0d107203203684135003409412103911400c1043c1c51404481d580035501e420314030040905016100794000d54104030f40180d640c001496030a11403d000011640e8075030041d9550002e0a0600000c9a08a4001010381c02e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 725368462 1250 725367212 725367221
    0x10060b0a0c020d0230120f0901081504050c090102070506041a0f0d0906091a0403140d1d010e0706020a17030411040603060209030115080604020103051f0909021c0c09 73
    0x140000c0c2401c2c0700000200b42000742004684600942c040b03a005c9080c1d0301241480600740d1008901c0301c5900c0d15035120340031400342c4034101200b03051004640120310001311800050340000e00241080102d41401a02c91605400c465001070041c441c42d5400708035410108261002c480106000d904d20302d10300c8003034481e290444e68000784400c405006c400d02051480c000c418032540180d500041c03581e801e0400c1c032201d0000426030110035182c8001e102c00603074080e11001a07911010303c442d4031440b07180b00c1c4402030400307a0040d034540105000994042e40c0103502110408059904581929030742c0c1000f03a0312044c80d05005004001d6452404200006030801907500600c10261810308400302c000181c100c1e10560820384540c3d60100d580f40807424240700390b29046034842c0340300303440030314242c10076030f40380740c0244024105504c840c0854038844203c0e81003050580400c1546081302d4941d943c3c1c50003410110010781c8601d541d03802e05a000030010002214990b0400b0b10040300a050114090142 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 725369712 1250 725368462 725368489
    0x11d030409052d010e070518040e0f0f071e0b0d02070f1a0f10030b04060c0314040305030609150303030a091b030c0905090d020a030e010207050d0510060b0a0c02 71
    0x11031a4100b6958014010030f986124400e410200390419410512100710080700180320307906225082002c280a101004216610768208460203e421046102840d04101d61060310f250bc03840360903140c1c50b4880011600c0410b80f51000c0f541d4181c11240c0185072440e00b41c62060b44100740c01000341d01c0342482c0c1600101040e80c09010380528083d1a80d41d8402030051000c0d104100c0036008050280090048101c03540111a094291050a0441d2a12140d08401a01c02085141d4030150082d5480c00303030700407080764a00014182c0440c6001d060141c42c41c0d1046641a21911400300000c000461100641c041144c1c003400071819030f41c50026040013064541e600745e0f8a00c898281c00c022007000c42c6840c001035031103904030040c95031070300201605440e00500402155045881d0984c0c031303d9400500c44075008e81502e000341200d03c8840040c1c0c2490555000182c120045094400a2240001c1d5080b08070344a01d404100080c1e5442c440c14240c0289000c1c0400107980c007204c8400b501c1c0520440040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 725370962 1250 725369712 725369731
    0x90b0a090809060a0807020c013f0212010e0a0513020d030908010513060b0a050f0118080304270b010807051305090a0c090b070f020d0f06110903011d03040905 70
    0x2c1c16020000900f15404c842c00c0840014144020403001c0d540c188480140d807070003801c0030079101041082d62210b0240c002c8803c170a1700c030701348810301c050720101a02d18840801c6050455071281ca8030b05158030b00c042401140c00404c062404550341100b42d1003058403a0f0b45400361000d50112a60822120110020013502000195a004900080700f889990b020340030002001a2840140c81d00d6025980f1481006214182c038400c20070a94803482c00032003884200b46000c200e8072440d1032005400300010703080641c041c031011030042542d040500e4006090a407001160045028081c68501617592510040f40001c55507000700c2e041502a41c094907800384c501c0c18114843d40c40360040303000d07600201d07902d0200e075446501401800390041188405081290502c518062083d1101c0f11204219030009004600502d6014107000d507501d40140b82c543d00201c24040045411440c0780a50081001a880b030b500c0c20b0b00b18410010410b003513000c0404000055820285072480d503600500005044029 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 725372212 1250 725370962 725370967
    0x2d06010512090708070803120604020a0c17120105060313060509010209090f010e01240c111c0c05040b0108160c15021909030807061a1201020304120201090b0a0908 72
    0x4141c14440c1e030551040c42084000d00609262450441c501182a8480403080d0410090720143d604010000b5074010019100542c6c2c0300080d400c210341c40c0101d15809414400b112400214842c007110007400b6417410751031124010798945040003220b201c192030585014051758065800148503800c0380e40c0c4000a4000107040c04040f8000c2030702e08030b0840d450902d03640d074180140710b8488018201e07030141c916080d82e04803409104105070403440300810b951042c0010b0140840c2000341d1503508080381c01c005014102407204503100c2c8600142c40081c00c5410020203640482e403420144918920090305948e07030900e0b41ca820089100c410784040c6182d080102e0f50000300c002c80d11186040300160202c1400684e1003444414400703010000074914070801c000650100003244080c000d40d01c3c2c068010070f00203644504070107802c41100c0c04610742030700071029074084003a608040d03000c4c6100b140100b4003400310100400d0300300c0c01c0340d908583c020601c0c59205d01103400304906500006990f4490001d051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 725373462 1250 725372212 725372227
    0x30f06060c0109080304050d02030c3a05130501030b0d0f0c0317030a0b010201090c03140f010e031c090b011205030405090a020a300b15041403062d060105 68
    0x1800d60f500a10107a400c400004140410400204225041c0e84290710280d800c0c120700d60203940d00c03100c590131105812118440080c64415401500790400204055000104074008601404030740115202c1403501030950300001e52540203019000300e2100042900100c525155900448405c207500c05035800c01e080803010002480b981c082502c1c01c140f042405440389840030880080da1101a074003411a41000d000300c0016014815500a69034480e2000181400503c01640f51600b40d8800010942c04c040b80484c0d0380e580400102140244c001511912204c01c0e60890309a03807070684c000f80b10703941c0d8000410000080819403040c143c89031041d2450b003039660317000420641065604101d507136800600c1c0f12041c1d8102d03284503c01800099181401048810481406030341710320034070704480d16480c206100e41d0f15240640d9280074103441c000d4480f9180c41181492030121141e450081c407030070000c10500702c91548c44120740c2d03072462284d03611103168040e0005008005021181441810300104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 725374712 1250 725373462 725373487
    0xc091206050613060e06010503130609150c050f0a18030c030309050909010915020c0a0b040606030516081b0406030605090606030d03022104050a0503030403110c06040b030f0606 78
    0x20480903014650100322824210200b2402c40d20702d0302055030a5103041410400c405020a13402c0d031000d82401c14644070398803030b01101369194254900502c0246062481c40030001d01400301c104101c00848104024409144252035a1003000c2c148110198280300c0152002c3c032440c3c440215681c810028001c181d82c942e101e500e0f14515803c100d0205d0b0000e1018056400c0292926502505e0200284074220803510307030040c20b080c031002c156400b0b0f400080e400000d4800300605418030381d224544165900d0182403131b400901490004a03128016034043d620112524111076040d541c0101c080e00101f43c00300c40c882d981c0100310003816041920340000102140d80c52007154442c136102c802070105440e0003420981026958540c15083c1881800b40039500d00a80b100000240000b480c618495111401c0c840d1409406030002042480008200810160701007070041d500b5814901700c80245c85500304208550040d03000340d103441d40d01840040c1c01c0038040d814142d0018000303000380e45000c00d40ca001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 725375962 1250 725374712 725374739
    0x20c0f0918030403240f060b0a080901110a020a0210020c030d03020c0c150a030c0918050a0e01110d050705070b0c0d09140c090a0603020d0b0901230106020613050c040c09 75
    0x580711790300360340010045c2c0e00e8024081d68000c2d4007803000800185007082c0404185000340528007040000039400604000d009502c100079003030018178019110b81a0000c004c3d50b03030348400300881c0590084540c0c410a2800092640000400140034101554001c0d1044000b0340150030300b5030b003a124041646189840d0804840030841404203560345c1c402c10b4440c05000c3c3c1e1540c00c1648100014540304125000180b1054140e20f000c0c07179404a070540717514a00601500e15200c0005941d481c06510030105182c203001480444030ba06000d000341e0b03a5a0701c0540d100e000e02c241c00742050901c0e0f0b0019110701080d100402d45280450350006413542e280e12000c849070510540b00820381d12041d1020400d06e842c0e0341c2c40f40c1c0b02510201c02e0142c0c505650100c0d8440d05030a400400d1030340502d000c25400002034000c4007000f41e4418008880381b0700d041010743c1815080c03090703902601641010844d9582c11a503d0042150803400600340c205602041c44001c1181d0b43d449400c0140000021448000d072110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 725377212 1250 725375962 725375993
    0x7060605041e0c09080c10050c06150a0602010531170c0f0303090c040902061b2103160e0d050115170d0206010312030908070b07020c0f0918030403 65
    0x1c1900c400b1260214115807904030383c2402c0c441581002c1000079000901c902c5419000c1d00c4040509a013550107076811302840c41c02212030b009407420826070b841840b940000e0f5613002c031094090240e031000240d0894078162018000a5030b200c03801004a000c0b402c103458001e03903401c0500b090380115180c60750369600d01c002160013410002080b00e000b0008021a414141c0c0040241d4a142040700711180d031904880091030056850b6081801035586810990303003514501c10908041c0d151040c02c2540b0348500455400001c101c10348044100302403c400d0342e2190841e00c07481030003080e00d4401981e101140c41d1266a102c419000c00f480000d900b80234161400030400c01b21010f06040c0107803403522400c0c0801d400c0490b84102402e0300740b640e00240b81411680c0000b420000710290207400c40c0030b0601d181003d844a500000c1c85400c0042038001c1c0e6104068507426600001c80e4102004140c4107402026540b1003501d0307002c00e40d148200085403009106138400c0300d280c03541d40c2c1d840076604000300d030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 725378462 1250 725377212 725377241
    0x1050406050901062411061503100207081c020405060a0215060303070201020a03110a0f03020d0906180501030f140405240c0d2f09150a140706060504 66
    0x10501003040418051680c01008200003800910300701002101807554202c2502821070740640100000d034041c0303441039042c0022100350382d090315026480c1c1d8180c040203400d4502038840c036910b06400220304d1090b070301102e511200c4079140c4240514860310f1606200c1e00f840181d9406c21001900d5a1a88010200c92020350042c3c4901035181e11031600c41000102014069082080760400503079000c90100f4a40b41d00d818140c01c203481742d0b80762602d4008400300081000c0c0551a41030241134000600c0b1040d040b940c0d94040c056515208101d88205404030010002740300014180065030080e00704840d017400341c803400514450015042c1d59002c005880035034868010702c0400c00c2804070f0340c80e0b044d145100c0c1c3c400e048550901c0c1842001d6407007801c20b030807109a0303100490541008902a44107100000031030080281c01c0c01600484190710480100e48149008500c19505504d10400c1d181c0107441511004250110005c4d124201e9000c490b046903031342d642d0303000400c841e5100e1080d0200c440100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 725379712 1250 725378462 725378471
    0x71d1914040b18040507030c0314100605010912020102150109060e01170706110307050d09080c010c0809010804141f2f0d1512030323280207030201 65
    0x50032684006540e4000c60190341400c50151042e1920220100882e81075580000700d40c1d52810000e041100341d8000800c043c1d00c0c4080041800b194009140c02240c01c8804d4039103c103101d039070b0f50044502030711919021600d803803010012208190f4034001060f0043c019241c8803d0800148030a070507003601b011104554520b0280072010000102c540905000b181201281100303440466403181180f06d51003c1003192b401d498903c0341c0a1050310107042d4444100e40b880c0c100d40c1405020300116000d0080c0705d200700b49080341198814071050b00f07060303005940306180c403940500440311500300400c161820080b2481c441c3c580203040001450303440480714409890102c0d0303c0d060701624407a50035205e605000304a924006200140801072868500300c556030340d0b07101d1001c00b00140010903405040c81e040d55500003101c0c0160144002001c0c403d80e810498242005070ba40c80440c00c20210398400400e80c0009020140c200d02d9036007941038130b0682000c0740c0c8240c0000388160380c0503460490060f51103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 725380962 1250 725379712 725379719
    0x2070b0d060e0124080f160c1a04030e0d0309090c0504050a03030201060302010e060c0316110a08060f0124050c07050d0602180f030c1302070c060512070e09071d19 72
    0x2444030319290140a00d00402d050500f449080031100020f8030a0b003401120b0084140c41c00d02401c01c44494560144036004c03d0809c0204081443c81d00715000c1d00070508103400090700d8a0b003034100c0c0190f40e905841d5104a50304020078103004101c0480001c040c81420003000c03480b0740e42c2c1d4580324000d612a81c004030301d5074158800104424403400800740185014000c01d01d140d00c010061b620505032401c8030292615942c100f0b841000100700704643c101410540c003290510011030030b64420310403035078071003181c0c0d0fa54180c80d940d6400c5c1109030f403282d2012855502010703225200528000007000108c6902c0c0b0b40714000160704c0c2c030724100222080c540c0021991040420584c0008c481e550032280c0304800b81c0c000703000c6521035011001f201c2c8507074500040b5500d40089036040e00c0c03403d6041000f00841c0e54035030344042d10b070b035005111a64100d160440090800c500c501011280038801505010860f2180c080554203403607030b02d600c00c07802610400055502c2c6c441c0c0c8081d0007200e24664003918520314 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 725382212 1250 725380962 725381009
    0xd03050306040b06300402060901030e100e03070501050f070206011a090301110306010e040e0c040902040f0c03141302030a030f11011103070e01020109050703080319060b0d06050904020102070b0d060e01 89
    0x500c4202d0715940800b20f080002688d904815540801e0003801c0214803980303440c0025082c032021004200d801450182c04035481c600c000040e048991082d0020001a1109903a52240040882d442001640304c20014800089403a030b190070034a80c80c20440e820280503000103800d41394000d072480340d858404406c206079507902201d41c2c00d50742c90580d002c0100c540c1c0118180c1e20342100c0307202c0e0f6001e2600c6818060442d115640510080d0700e00e00420080f00c01d00c088001c015222140d414041481107001040004504810900d003040c0e005009100d003200b155425695100410034040c1484500c4400e03c82e409d40030b00502c1c0780c40104007880e5507286000300c0b001c1c2a0100b0001e1042c116803405079a14002800015548140c80d0009140d42d02c2e41d81e02180b4001c282102241581c0c90341c1802030000e445682c0d04007400200700144000d1000360b403501c041c8640c10404850203401a48400000c1240c10201c400520000e8503840380071038020b48510301d40750180420b9004000400e0460021000e40c107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 725383462 1250 725382212 725382277
    0x3010e0c090a0b030a0221070822150b01090b12010510110a050f0708120d050a093806030307020f2b060e120a0f091a090406050604050d03050306040b06 67
    0x10745e0807031f000700070300b0405401840107500902c00403500c2d0101031848a10b201c2e500d4000040c030751209503100d0144605250601406200e2486030200d068203001045410750001a64040e808091440120740e190004020020800c411a042031140c41c00c0e101c1007180c01403101d0f8500d28042c3c0300600f1041c080154152500c8071a61055031160450500044e800401c1c608842c09501103c1021030181c462080400080c0040c000c0184100c130f400304d10120b0804a40e021040002044d41c403540c408100143c2d207454442d00700c40d2207038103410401c003800051a10000d249990400582510b82807040c2d0100006000181d40b003074940214021581c0040003002c0c00360002200e1b905014090b00c00240b20b03600c41f14000c03903510000344101040f5031924903200340f280c107004141c50141442da08039006100c1c0b020340d0268502a000d0703400c10314049420300341141203908071603024100440d100001d4900b01c4242d007000c2d2210f988152a0a1100c40d2a40c600d4042c000c003a02c0b503009800d1a040c82001108140d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 725384712 1250 725383462 725383507
    0x1180902061624110a26040b160c03050423040204061716210f021c0b0406030203100207050304050a17071d0f0406020c0703050d0905040203010e0c090a0b030a02 71
    0x65040c5502072644000b104282c0340e0a12060520301c1b00400581001800030324a4084034096551900c100f106110401d241980a08130030b150a064045c402230003140d9110842c50040e000c98410081086016561003d14601a8250b011140c05040640004050340c0c810340c0503c0000d11003442c40d0310014119100c04c0e0300440002200f08000002c3c52000d001c1802c1c031800b8040c5041c2e4a031802c0703552015504002c5c41110440821036076440d01410b21100c56944440c0c400d0075134940a01c0f41c1d404e081521512094940040041104e09540458900a9400b02d9422038050105000c0020f16846010880e03001e0813620b104000c910000880181c03410f24103a02002452040c0c20703401c1d6594203011002d40c1c00001020807a00c0d43d80d00d9090030806813284110a00701d40c803a5400c0002804404034902096034140d80d01d080ea0036039180704000c1680020b000c2e9032100c2c003820000c907002c82551401007805010180c02007191720754030104449550170440f00190f0281d0000b5034141c8805941e000104d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 725385962 1250 725384712 725384783
    0x23100605090d02040914070f060908390415031106160f020604030f110118180e011e0204140d03120e120a090806010806011809020616 59
    0x4000c12440000c00e0b48044141c06801150b071a8404d005002480c40ea041c2d81c40554421520940d540305045521000a8460440050413111006c034171f400c80442d2103206483d04a45501741085050004840340114082d40c1075664403148884449403030302e008404a40d807040000f90401891820b0400410344500c0f131083c800d28082040c0c83c00030002c214072400d641d4100c4443c42a480e9588040b030580c0c4181e0304082e24a400c00c040f8481081003500c0c0700014900c00b031f0384c1c00c809a40281074480c40380b0102e005c1c034468a000d19503c2e649900e0160b21041d010007a400020a0340c80b1052446035451000d0a1921152a000141482690350785c2e104054082d0007a80e00040910864600030912011411006066078841d0780d10001401c042011151078502108031a5442c2c82d01c00c0050080019403250500c640900310001418100200d4520304a401c08010310424100c109802c0d00100701900049a00c030800f885001c00c01040008000c81c1c8602c50303000c00c2c40c140007100d900c200010151240c07a03032307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 725387212 1250 725385962 725385967
    0x601030e0c092a272d060301081b031c080a14100801060f031a040203010906020301170609010e070e0a021201060e090f0c0d0e0106030b100608071b08090423100605 72
    0x102d17850b50f920070804010040401c036009495040c032074085180130300005900180200000c1150070001c1b80c5d00405554140640034403091203400d06403240c200d1180d00c0f01d200341094200110034080c00055500100c100c00004001c8d40091344000d08140c00e4580f030a1105520f141403000180902c2407901800105540101961642c2d0f0382c1d000100c09541c0b0109200340030000301c4e0449d10250046015240d001c001903450713603110b0a1020b03185628640302582489803802007003940034103102c0c25001e03603035a4028041031401c2892628822102419070045140e00b00103007040c00a0580105e8081d20315965910350b5120107c08001c1240d00103000181182a0034050144101c0028101d8041e02400b03500440c902c1c041c4034001c1e0041502c2c0c1d0000d401e1411a80c10030801241038480d07a401c0c0c4a1070313200e0b03088a84600c1400c564000e0100e000d2000001000340c1840440c0b064005000136980c02440800d6986031080b07442c3c01101ca2520501803c104003060180420961000c0d00182000b0b181c50750 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 725388462 1250 725387212 725387287
    0x12040c061d06072112060f05030d050a0215041505072d02010608010f021e0313080322061506030b0a05040905071205030d050601030e0c092a 62
    0x105007885600286105020018482040000c1100542d210440d52003c002c004100c01c0b4015115010844070681510b140c9400490200000d0740c0080a51740c01900034401d00413000380581d2284e1002222405601c50301154601d00100054241d00c210f120f602003100002129403405d0a1320b40243c1404d05010800c5031000304083c4040a2144500d880c4506c464147d0303640d01c09a00400301c942000302c542d4280761800340546002d40080000410080b440411412512183e0300140000e9501d0544c2000e1152604003040040c4003035900100e00c0b032450142250444602e50864410301e00444180342c9454810650303103070503405500100079608092060a00c0240001d50400107400740502c00c940c1c2d41aa8020f02034108a144054403451052400580060030310540d01e800034440c00340c2071814031000504651003130007000c1c100d03203850006100201c030400400c00340404c0246440680c0760040a404107a070b60741100b004107807020401c8a030761204041c01ca140c0b1114804250007840300000b2811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 725389712 1250 725388462 725388497
    0x60b040506010f0f090801020a020303060a0509040302060a0f0f0617070503070609120804080a0305190912061a041805010e0309030a081804060e0a150308090f030f0312040c06 77
    0x3c00d4040307061903e00d201004a00b0203580228554000340d519600c04282c0f03880aa400000640c052003040b0340c072000e131300d40d2030042110744601244d0040c010f030401c070701060f03429421750802242c030190707442c0c045030000c1c50b454240e080300c009d548101c44a0140f45050182d0b4403040c0801c0c0094803080c0c0291907a94107100003e44030f0201481028992180d10300414240300149043c2c030080d2107490190380c415045d07818000c00c0e6030030044105072040741074065541c000d8041c070244001c5861003c2030303600c030001d1500c865006110300c1250185924080748029800e6032540b28034414020004604000701110707040c41c0d030031120301d00b40070107140d4410403d10a0341d580009a0b1014a644190342681c7c840140f440360306100c0c0000e0049400505205e4003090018440210703901ca610740034010000e0400f0343d01a01440d124612020304803010401800e0000d00303290505404035100542121444090045024a158452880c4110301301c0258244010030000c060f5100c010a02c030720b00082c0111140569 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 725390962 1250 725389712 725389727
    0x11701052205150115121b110c100302031008070e150319050303041106071104180c140f0612070c110603071713050a060203060a180207060b04050601 66
    0x211000821810345420400600f007000c2c0c8540400185031045a5941e0181201031110341e92181e40031840c510480303846c0180c680f048005403841800c01400140c40b0080a8a4010a0350300d555981e000b075400c1c0030400c5c3c41e0b00c40300e0321080849540041e03580c03601e190002d2070882c45820080107034000030f2040002103660041c0076041700111840302c00f540000c000103442e2030f4410f82c8442e0340c4140c520300352017804804009948114000d109413500011140c040080758411904024030050a001c01d400300340c00e0a9004682c00d05108005d244041456201c0700c03090b00c0386a110041c50350200034090300a0401f0440080c05600c1a592241000382010505400000003004d001c10082c0c0d80e10400c051084058210041c00c2d0003a100a6907400d003201c0060048450001d220031240080010030100d415800910740000d80002c090482c001103940c03858040c0d400a48442d074051091200442d0304115058003840302081e212005955450301d02e040007d568100205a1003685441d040144990700000d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 725392212 1250 725390962 725391001
    0x1b060a110a080c09060c070b091c020112151205010e010b0f1f020c13051b0306011409040e030a0c05100203010f1809050303070917011109090403020703021801170105 73
    0x701d5521103010b800451028046c20f01e6509262040350000620714000000a12802500f07451260703212180b604111074030100d00c14000d0018411100b201c44084183d8032241030034104002c004005603441d1000d1045080e0110141c3d2076035502c45070041180c03400d100324900e4641c1a104007246114400c0000d10406804821140c6c0f5600113030f031010642e209003c484144000106004003a0200200321001000304403180f402041070350f07001c0c0100d5545d043c1a0f0f44590030595822002903aa80400d000a82028a10f581c10544628600e10088020310281101c81101d81e030f9441400f5860a00a00d028824282502100d104200501c0140103000000741520241c00100e2601444410200014855107102030960b000210a00100c00d62210307070a0102d45008400c0e440e1454910505070072542404100c164052080008171050b090104081d076110380240196240c02c3d070307641c01284500c4494444101603680340001408000d04410714421810074030f00c0204141d04d895a4076005102c07c01c007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 725393462 1250 725392212 725392231
    0x1505040510090e1008060a05010506190201061a031b0403050c1c020d060209121518070f0807060311072a0504090b0601270b030c1b060a110a08 63
    0x16924900180120032940080c40d5203101d4507484d00d04105207001c880114040d015903801150702007800c511040c011981030329801400d141c138001100c0350428000c02002001c0d4259502e0341000100c20321a0001c50300d101c404a03c01c1c5030f4a18000c0038080310116252041c4451034820b0009101041c0c0001c5c1d9916441000d5841d5100c100310450710b1003049004e9140290700003450f1040c0c000b00b107041d03006408002e80a48030528600480e001072034982401d51110821003a01400189200c0110481c402d4988081b109680030301c0d440e409400c030100926007008405071300100d01003001d940e15104094050184003082c0d424070541e607643d26541140701d510a0041205012900c0740c04602800303110007000003d10802c0240359903d08100c0c1c21004503101404500740b020507000c640e860a0b0361054040180100381109030802048400640010301070710300304a03040c000f001601254510a0304400404030041c11a80f6211104005603000a4110328180409021011102d42c00170304158000900300d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 725394712 1250 725393462 725393479
    0x30610110c1905040903120621150b0d0f12090510030e0c1207180504121d040e0105040506011e06030b0315010b07030e0619030207050114090c01030615050405 70
    0x1c002400c00c060b0681006071310a281042d410101034110601d201104503140c0e0600c0000d50782c20f01c000f0192185111400030401505095001036040c4018407a96000c00d00c1c005540b00c1003601046a40e400c2403012205822007403a503030280b200050050101d020f5910305005a6818000810320780325211510406058403040c0407001c1443c18071003036080c0107024255403148015032400d2980e1341c01a108100000809070744400c082d00d4a40201441150010754040c0c00c181460740842d00088404800b00c07408030003600320341c500e54490080501e13611550b070001c070700ba0519080c02c2e810490306a0240c0074003600c1e4891100d0f41c0c4003024848080f60020308000445000250201e0b05200380b50b20000070003030b628000071801c00d840c0340c0581000da02035682d604414201c4802c1c410503100380b406492640303101e6802c13050680d01c41d030000c0c02c0e828481c900110f480c110a07000e6041c540401d4a1100301030300042021041c3e940d0610032030700100520354036908124002000506984224001c560140002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 725395962 1250 725394712 725394739
    0x30f140c0f011218151a0a0f030305030712110c0609010902130905030403080d14011a070204050a09020d030203190302040321170c13170c060310090203010803030610110c 75
    0x1c0101303d0b0325070f070b004100d41c1c0420500100c40350041031500d21408180c00103203010800b80c2000010401903030f400c652804d07101c43c00c60310151465040148003004004243c4551050a02d050182c031000328030b0804880c0e240c0c0180d80071709080010085ca0f60b15683e140040c150056039482100413880485442c0c00904450542000303030840c070507034201901401001034108150955540051446505032141c0420340c0d88503c0c3c05c0ca16807081201941611105000c00005440e060340103a8008400810000d00c03407030340340e020a00960070f840094001d41c01c00310304500f00c512100c040c0010b080f11403030700718505070031540c0d40b800104a448a40902040340042401035500614602400851100030b405651a20718034503566a448a090300480c008141d400103411219410212159913440014246c190540c006100d41600010000301c070745d45500030002442c402a01c000c6000e07003142d1000d559680340141c00c0c08000c00094080c01e042082c429080b501180b400300e40b1132400c91088030003100c40341d403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 725397212 1250 725395962 725395991
    0x3070c140102090315150306071202090406080d080604060603110d050414102304030e151b0303010e06030d08040f1b120320190507030f140c0f0112 65
    0x2402c0d9020f4045c030440d4a48040301d83c0340c0e51080d00c1103400b20b08500b8000320204c14540c83e28010340b01500881c81e42240c2c54140d09217a0064802101c01900000c2c4081d9100c501e1490f240d10705140344042007014050040c1810140600b0380a41240c0c2018800f05120751503811203031090390400304140b9580c0000c2420440050010000900c1c4481100c403840606002100142403150324802c26801ca00307840d5100c1084281c0c036601c102d0301900c07035201d009418001e1101d449030040584182d40d10410443e0513183e40301718220b0320190045d00850f120340c104000140407604c0941610f110f9808005010b02280c0d0020f94554407607400f503885c0d9101c07845c51400340c0c1020100180300072000c0d4400e0f400328000b035002c0c1d10b4958850007940d41c202182c5400800090405c01c0741d1450529801407481c4804c2c910f031521400c440349114100702c4900540d6522000c1038001444011540791000800b080c00403a000c00c100c50b4402c10840340407041da45410006440d074400115140880740d11030285c0b44500c0f6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 725398462 1250 725397212 725397217
    0x30f15030f260c1504020a0501080712020a0f030b0402090d200d061a0118051212130305120310030b0603100e010b030d090e0403081b0a0e010e01030203070c140102 72
    0xc0600d02211844858000340d100e8580008040d4490f503c2a00c1c100643c034008060742c103029940161032146421706000c01100c2440b00180240140b0554103142d0301a0152803009023042e1603d035440240c40903007094014281c41c00e001c81c00b03100c0d0b80180240e048590f200042d03010103a5100229114110134411160011560881d520303601001412454040c0040c603080000d4070441c0c02c02c0c1c40c840c0b540140c015281c2002407007030039503034a8070040d061010341030000c0d0110800c040c41048400742404000040d0241d80210120360103044070010400070000200071070341c0f20005200d0802d0561510000c100d04145040c8070281c0030300c40c91030100b04961000d128089085075410020702600152a10487c0a007201c400007038045c1c800e0300c0940c403045200742c0d12041a0b495500340590a40c4481d14112200b840c090700c2c2150401c80711a82c0c82c01007a20500402d240d420340d4440e680c64502400024190880c0e6a8009060500410401140ca6401f0314494003a691106414000d076111071916030090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 725399712 1250 725398462 725398493
    0x181d160908070306020304110117150609040f0e0f0f06071412091b030c130911101806030e061303050c1b040c0207050904082d0a030f15030f 62
    0x24014100040f041c815203400840c869401540c0d034255000c4c1c40c500449101050b6090760544060310030215401c0140c0c055014015040285814240848a40010101ea1910800d00c0009598080160004005120300c1440404080c0039050088908420070b0300d8220003841c01c000c0041542c134a460300000042502d51100107114031034003600c0e10441e501d680c0c9000081c06181e00300302e42e02104591800281c804171100e8041d00c0c1d14280900f11010201401c0036100c1214060360743d240282007074503615a60081640d20303a0300c2208805464103508040b080540044082508100c0003494648000a2250300702440b441198044002c41c20300303e500340601442e150503805201c00ca4821042d00e000082003101c800c0784c04100590a400e400d030f036150740074802d5a0300880b0601c0040d000c5202d9801402c0c45115461320101c2820a100c0a00001044403ca00e12003140100700f0700f00c900c0c0e00d4030600150410801c2c0070840d040000c01e0200880c03e01d4480100011544000c05c01002003000c809a4030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 725400962 1250 725399712 725399729
    0x15090b01121a0118050102070306020f0405030d0f03110702010807121e060503070e04020307060c2402030f07021f1a060f0a11030702090105060f19181d1609 69
    0x10029039002e070000c0400400c0000d00080c1c8581c8002a800d000c107045100f290b1050300201001859941c50707138007070b40080c1140e8805160903c000140c03510144542d451003202a940e41c500f0031544540903003181ca40d064003140205050080c540180d030008000d50b008030a07400c3c82405140c4020201c000780860007114010000c041c0d400c015880e00541115064510450a540c0d00300d0300e030744022460080494010f981079111550400825014000307201c2000d0040503030401a0f0b440354000c030f1910008240032120f45a0010801ca0654004000d02d50000b003a4070140540c0c412940001d200c010010404012039030b138480c07000c94a04060300321441c041e072018090366110303010255005410341208003600085056480100c1c0100008421078020079070003010803110340d0818040c001c094100d241d0207a00c0340020800921202600c240f030305005845682c906071a2112586041c801c10440d610290070000d50040d00182d500d101c031708003544807031103c03040000310710106401c4032003900c80d41c0034201c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 725402212 1250 725400962 725400971
    0x60b310e06040b180712021c05061314010611060403021c0203120c03010302010f05190e220603120f120f061d010f05010e13050709051207150315090b0112 68
    0x340221491113a03228400c0360320307070006045800300c14070103921034400704000340c0c420425030b1142e13200c0d65031009803c084060580d00c0903504100c0040104da11400915026040744030040116503030080c88140d0841c580e03c0505040e0501d81e50203941da40300c03161112210014961207003005442041030301d03000c440d240210302ca242021121500954020301090780015855102d080000d40114120740c907458500040407030f240200c400445000009040c42903001000c0d03840009001c0300310403180b0804c1410240003642918520702580b202d80c608170b60806001c20441014451500901c1c0624440841d90011a61310740c4a20351600411050f0007480e408030740d00f001780c40d00c1011101101c0c1a10b001111040c04241c4400065895a00c211401c51b84070083c540d050400d40d241e034011682284941c148541219291000600d403074808001c0d030b0784254850396041104603030116a000101340c0c5402d081150038080040c2840d01000c0c2d0081012180d141d0010010300e034405c080e40180b40e84d41d13403400c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 725403462 1250 725402212 725402239
    0x40308041713030515092e2d110a08040602090901060c0c0819020105130b03010602031c0504021507030203160b090114102106060b310e06040b 63
    0x1002c80103e02003a5442d202e04440049440e0458903440c1c001d1440600410302c45c205110040140034240101d003491030440d00c89000341d14480d002d407544031403106210407043c01104120714800b40c0500d111004072420061400e4079510201c08a4840c07540300e1900034455502d40c108a40607102c0c4904a50b0080d20350400000c00d00e03405562079030740c2032081c080d064815690b00c180599528032400462910141d400e4800010740c00341d801016500800c01c654000380b950b50400c116903400076408100581c02c0010780003a100342c80a008840c02d901d0040401c40c600f029008a40340e0152034003078050201001886000b0b150080055800403220018408505030300303854903405003036050b60310154541c281410034000c07140d0a01550721800940e00440c612514010784010030076001d40c01202c075804135140350340101d032080c003864000e81403641c80c481c0d0716200340c21401d805034200d010395410074069413181c203542c62007141d0b16070442c0c54602020310251038140001d4010450702030002d5011100f1008034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 725404712 1250 725403462 725403487
    0x4120305040f0e01140112140c09012003040306020906070503041d130210030506150f0a0906090303020705010e0a05040504060b1e0109050d08120906011406040e0403080417 76
    0xd000342e4000b200410142a5212541100c410080c010241c0c1c800305140c58103081d5100300c2c030070050841c40c4500490340e20814107443d0714220091b0303107110785180700203892085560440000505580c0d041e52100b03c4082c03600d41151a80501c0c000244000e40009122031207036900c1c0191014542c1040070b803503485a40f51002c20b1302c946190b6012071000240e1001810061402040784900d81c1c010b8a546100c00340904114000d25000b032445d9404070b0013044001c40900c418025107000754501e508556a4604048007500304070081d07000208100134040c0038000681d020424104450007030030300748126501d5100107a4072003156041307540c102d03191008010070303c111500105860b074000c3c2d8410f00c10042a60b566054024036032041e0303021581000c410403903402c1405501404500842c101c1e0304220902280000d071107401d0300d040403aa800140140008001010310500c20b00c0e00b08e40452810b46001401040680c00600250038072040741d00040908c00b020b140d201890039401d5801c0e54646041914 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 725405962 1250 725404712 725404717
    0x40905030a0908070605030601020636011e110712140c011e110f030c0f0309060106030b060a0c110a05041e060e100510020307060c08070f0c030503070c0804120305 72
    0x19480355100368540017500d180103c0c116409400180c0c02390105580d03182120959801d640300b21000401c00200a502144150104000c10003a040020881c102c0c54941c80070b00c80f1a084074a01d2041c9040d80c10003000402408540c0d40c00e60000800c0200c01d0110340541d00700341c2c140744072401d410002071220000c2c0e106501407003514950f0560680350415100101048410040145000c3c075010081c2034066520040910ba1010141c6a002c0c64030a44107440390072500265044005540103070300611000fa014029221026020346803076050a401c843e0081c1907808010001c0d20000c0d554a07101a1603c807030b4040d1000e00002390040c441095055003440c4441942c00a40078440d03e048000310f1421001d018031030182525004020a1700c0c20a410451000003002021082d44420032032040015250f0007030000382031090b00d600c0a0b528001f40050210581031440004001d00710042400094002c41544c0d048840e0307103482200c103d20f42c82d1001d018441d5800410032160ba03507109104040d0300100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 725407212 1250 725405962 725405969
    0x5040b0703051005010503011701020903190c0902030405060a0525020d1b050a0206090a03140d03060501050703021b03030c03040803032e15030209040507110d0e030c0f040905030a09 80
    0x701049540e5036100c001c0c003403120328090b01c1d00040703003000100491024003480305401d5540c94001807a08582c8400645440160f030352000383e620a0804220170b000c814159400100980c01c001d514614081d5032745626100d0003400051082e070f03510007044200b03d0400c00c038110000700364081c0120920500000e507481c0e09881c100350000b0418200c80031000c841c1d0700441b40742a440002001600641e5003001969080503079071640012003944000302040c241a0314103482d60400028082201e100301008040e1046030304124180b03c000c1010100007980000e00e11400014480c6038003140c82c900c00000c1c218410441c200341e4a12000c98089001540403000310301404c0303280301e81204019800480c0d045404105603091034114001e0040200b007010000442d509402460010316260803a40024100c0d4419200000013031540d5030340440d44030042088031300106290800410300030620300000e64440c0003401042c095400f002d00f0401503101c640002c2d9415504c0010390343c459118202c002d00c80303c1d1520 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 725408462 1250 725407212 725407217
    0x180a1a2206080a0309090f1119030501091107060f0f09140607020d02100c05090a14011716030207050c030a200910140f040e010623011704030507050105040b07 70
    0x500014a5640003e51000096054070f130705540b146071112002c000d000801d00703504016150040c01c104254950001c0c00c0e00345c0361682445410f4850000201200c07416044000b405e4688041040b02442c0002682c95071030b132001001c11507451245c10309000d8041c4148030020076040c6581d450800c8100d592420f084c0c50020100c8500c2c1e52450b804995440c1d000b6200400340e0844001e03000050050303001601da000b528100313580340806a50202d0740b6100700781d000b05180c00c409418100290f178018110310304113402c241854554100101030450900d0805150024141e0008480040120901041d024040c000b41584c160346242e0410b00360804070400c04580350794200f4038103039962504003035a1b80600000000e00c80900d0030320111040088040c0340b0705a1116030441e688000daa614042d401c0300302a0080040341c5107240c03000071003e4070300c404c0c04a240d0800c040d2403900943d070b02044860001e03d8103540b0480c9902c2e02e05080c0e070b05208181d805402542490300b04001e000c0340e87ca4050064507140e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 725409712 1250 725408462 725408471
    0x231e12040b070f140307032106030c050609151809070f0504050d02011e120b010e0306070c080f120103020907020d0206070e0a08010e0a020f180a1a22 66
    0x18590180038416401004a900800c1c400740b400b20340340c90344141180b449040f00410b1011000704007031464001e981c0032800140704034403410500b00005101c0b40070000f0310b0740500409056aa6041981d00240681401181c0116440003207503070f2004003040491601c40c40d00e98a01d041d610f084107441d070788140f19024400000128424512801c1010b42030844c65813010309050511081100b03464420314140e04010f000500c038070050071611204001d2070002e8030b40208440840a0344c000361000f0881c220306020070a040500713103440100d4000d9102c0c2c228985512100183d24041e8501c0c060024030071012000442c100c0607849504032050f050700c0c0211007541c5666990308040781e070b58401c121501d00581001c00440e0b0008d02854803000b5030320004102100c500d032100f082900710389032142e01d51030740e43c03005a501d0258182186100609101550310000030342c2c40c10070080100781d01a1080312050b5480041601141c240454079406680061080001176495103200c2c040d1551f0103002c65129240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 725410962 1250 725409712 725409733
    0x6020c0115150906091d0406021b0a06150302090a02030703021605010501081515091504180b0603070b0a0e0a05061602090a021c02090315010b0a02210403231e 70
    0x85c4030103200300c40100300391502c410b0039074601380701168029000301d4002c0e03000d2060300c0701030421011104080380303004020a19200720303041000541d01640d280c103085040d0004140050b8035a405043d5000700c3c0c02c280560707a5101c1074000c80c004d100d003070740d00b8181070000b03840c90040050640006040314410740c110381c0b40c440200b400301110801511044510b62590f0314903003250601a40ca194054003e07044102c1e010308500204080d10703075045403000726280581a070b008004460f07607a150400005d400400800303041201c1201d880c402d048080082c0203c003507100d400769641e910030601804010304156220038800410181e050038042c0201d1061007410000380e0840c05500c2038482403558103003140b4005400c10700b158000d41c80300d4295600750059442d25a400c410f00c0f008a07000b0700c04036500710358070495184020f042c128880c02c070009000d0401d22458503e8607e10079035042c2ca401c1645288a6249600c150360400810503100b6554000c070f00c4803a000c02d10711150a0200e0040c60151031b0352096 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 725412212 1250 725410962 725410967
    0x411091b070c050312130816030609060b040f1e09080433050306040506032802040e071202090c0307080c03061f0306140d0803130f050118020f0d020d06020c0115150906 74
    0x183d0502e031600d400e0823680800229a0300d80000034103900641d0700280c0004068003040c15909510f0701c44c003417146c491b0307480d400d503600d00350300312003a801c1069081245070083c0ea5040710900c940c0c807419401d2101603401d9020380c0c8101c0b00c842c0007020fa0030100441d64070f000350003415175007040743d146120704d151a0020344076007404910000e083c1c0c60091005041c0c20310805046010340a408180c1c0c1055a41c0301006081404120040c040c00c208003091000c000b0520400500320001000185d4080c0309005000c00190401d4115030412111100d098882c3d4882d004541c060006100c00d2502200b1004000040380c0c140e072021040e10540d80103840f210380828280030f44180d8640c401400c0050801c00a85280c102c8048810554801c0d4040d00c01084903455903400d440611450a070150300d40300148045241c03032480320b800d030b103002c2c0c0c1e00885003030785a0001900381a040101801d40394000580f50016242940551030341c1d502c1c849204c44054450171b80440f071410f0f0a4a801c04580c05010200b0401d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 725413462 1250 725412212 725412223
    0x304050105101d071b050f03030906010f03051207020111011a0a12242909060d0305030a05060f1002160b120703090c09020708030411091b070c0503121308 68
    0x12071040c00c060b9962200c81381158000000c0c0d045000d210b00c0980910005074043c0600d010300b590309401903841e030600c00902801c01006a02000091000355410000500e0125440c1c4200c0d140c049095215407450006845210340210442c0f0346518003809400328071504103056510042c2a140b0341400c03610381001d0015100400c10107000c118125441200c070050015020030f6094424a0204a9144101c0100c2c03484c100e05400200020503008603142e2402c0c0062410351012013200d400802c82541e44002c0c140d440041c040c0c1020070f03201e4002030034a0716511001c00b0320920203044603c213100004002512080c501e0f2491400241d001c0000511008003002e9070084807441244014a88a81e04203400030075440c0c0c4200e9050500600020705407140380f000d0b0104078060b04015a40349054640194070100c0d00c9001c0380308003d420140b2108607503000640d0701c012960107141d0f0355800203080118980040398091a0305125070f80010401200110250900309444124180e03c1d81d140d1301c940c0d85a9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 725414712 1250 725413462 725413499
    0x2040527010b2d040504080307110d080c0702040908040807031104090c0e0712140a0e06040302060a240b0a0f0e01050f030c0d0504050102092412180102030405010510 73
    0x1840b000b04400e41e560070064090300b400144100f00c00440e0a00c081000c0e03030000c46054480b01004000c200ca101d400804020007024400080c03c00d0030048000500203003400303400250381110205040c1c0443d1038035441a200550400410703a190303991600c03031a07515003050004031000001c010384103c15061501506240c164801100c00c00a41000340390004002d000700b4400800c11100c600801c000154407490b07c10106180550030145882c84004094840c401241c0c14590300007030801010950104003140c12800705c0300c01140052039901d1481c14440807110000c8002c4d0459000102003600200074174014000e9100c132890002180001e540d401003103d281400b0500400100401d651000020366000e0b18044405040001c810001012158102d600b16241c0e075000450844c54580000000045848546c0c040030310341a00040d4001030044e00e84000c01035035540701044c002a071034042d440030514001d008546901e440e05016001e44001e90350680c80b820300c04004136419101412000c100d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 725415962 1250 725414712 725414719
    0x5040b010905090f043e03031309020c030d020409050103171606051320030601090b0a05040c05070503210a060b070f050c10020709060e090706050d020702040527010b 73
    0x85556090145211100040088450150034a40e000450110b03148080f0f07240540c015925040300c1003041d101c1000c01503081c0d0342c801c0e4014486040c0120000d035000c0c054ac1c800c1c400247e20383e1040807400b07146000b6518210604da00118011820b41050361165040300d0003225221312400220084030018861803507010400410108008040f81c2c8030b8001d150428410203030a4031800664031884c0c040c45561242c81d01d8680e0505000e4410316003002070901400e4035400400040c4034110009014110301d2140c0c50042e501d8803004803116004009550b00320f42c0182c10b50b55111603502011625400205189824002c5000803418140c1c0e10b00c9201d0030340750041543e51616005444400350384860f00811100380c800c46041428588030901c2c0c1c0d2410031540d80040c6130f034a007000300050139502a5001929000041d0341004500d41e07001400c0c000300c0f00c080c1452651a4150310201c00030384500f0101075005400d2030284906043d540380038402c2c20220000f088644503900300420300341c5081c0c00030150b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 725417212 1250 725415962 725415979
    0x12a05210c070b0307051605010b09090606030c01110a0b010b030a150b0301031b0302120c09130201020703030c0501060e0c0a0e041401051903020909031306080108031b1009080405040b010905 84
    0x400e10380c1000840d0017a20a003402401c00b410350248100d8000a120119400d9444806030421400d110720326581242d1034401400075490308002203540c581d00b82562314104698a0036001641d80e050118801103034110f00e070380020750303184e055a548a6005440c142c40041c50100400e00c881c048500c40e0b01550710480f11180740d40d186403207144149815003d071078011960410004016070340c0d100413081031080c1401621102e2400d004020300b1000080400c400c00118201c0100141c1e804201b0784103403640b605011910714400d041c030700e006044680040042c98800317000d100310900c4400113085003405640da488500c40c11402030000340d500c1403a02c00c42c85604800188031f0b51510307c014030942802005208001960f9800103441d806066034540041c0d080042c2069501e2a984410030103030184e81006102c55140403140e5a0740e2040f202a042d101250600018000c0002e1041840e4006440414016007150b0300744408154010f01c0303018032662a2030490130702c550144121000b100c1d0024800e49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 725418462 1250 725417212 725417219
    0x1021905030903091806150f0d0c110d090302040e0312071407050106030803150d15020304030e0d03021b04060b0f1602151806120402012a05210c07 65
    0xd6103608003070304501c003501061180300c20075216201800302a90b0124070192607400d00b0350601c003014980500b0f040c40c41d0310070010f0091200755001150310280d10140001550780c080e10003180d449a2010f120f4409010702080c2400483d4803601d04019280201c0c2c042107440c41c41008556a4442c003c038680402030740340c1c00100e8060186420b05c03054800c80c1040c600d0240303659500f03402c544641d003046556040100910184400c58a49001d90507030584140320420055290910b451025161011890707030000000744c1058403403400c50450308005804110302c2007840c03401079280d0b00c0c142d615808032441d0100600039481c003401140102c80003020f19500d00780416201030180d40c8a402080280b180401c5071500584903803440303030512003240c0c04460f2900b80020054821610301c1c0e900340d114600900c8480c070109030316a000d40d0411350900745a10962011800c0e682000750901954034091680c11001d403d1010229544044100400050082c03c0d9134801c2100d880c0216850400d565104ea0402d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 725419712 1250 725418462 725418467
    0x601080403020732010311070b06040b0a12060e010b2d0306090703290a150332060405030a1b051204031a0108060c0f12010608090f010219 61
    0xa03600320703000b8410344200b50348905002d0f500340740407a01c81d0741440031035441611540d8903001c00c000060003480d0078000c040c02070358140f90314002d0020180200902602003079869503680e00c40c0b800f052001d0828080f55a556480c28001103042030192141400e01d014240d001d4810b1080902801004011002c80520840265a0308803941e8821844c000f046107084559a000c000e120b11403203115000b0103003a800c625084490185840c4880e281c685074a444402e062090615640d20100040c000142450705032030b03c4410300d42c03c1d800a044540800700d0a00d8662440807510442c07490000c2901d484003016903e030303a461100f200c5c050a550001c1c0509e103201803241c001040c1081805080060600c00c03621218180403280742085406400083d0410400440c80b204014a803265200305405601d000191034840380c0060410700c1241c40020740c80101320501e0251001b0f0329000360300e410b16607196400607140ca00f05440024051080100014071790105000b12183c00c103503501d040b40c1900c07404206 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 725420962 1250 725419712 725419727
    0xa09021507020415030813060e010203030703272a03021f090b0406050304150504031d0a0b0c16080d090e3706060e030c15040f0308070203010b090105090601 69
    0x2c030703800741c0c49222060024650a485001031801000b00550740d903100f0040c92410007090307020009001d103107201501aa03070040160380c0d000a00c0e08021034440d104041c0c1c000540049010200124103542014084c0f01a5062003420385450125410803035800a0140ca4024860f100081d03000ca42d20109c20031901c0a41803a505905041c20003054098559404180b1034015402050008101004000c10321461000b50303801c50800300c20412a900b80317a01d0080843c2c0d48064900031080001d2a01510394a07059120300081804030842c2d62594903c804850700d90213544034101c0c141c3c04900c00441e100b5004500c24080192030744030b07414072502e080802c01000100401c00c59821600c2044850140403005500280300c0d5079002501c2200115810001160301942000d0100301806160102c00e440c0003440444003102140d40c1c0e0703540a00c15001c0b1a080c4a15001154100c1c844d007800002c11900300e02030032100d84210000d101a9244800b0302488400903c10643d102030604042215540203101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 725422212 1250 725420962 725420977
    0xc02241e09090a090201120b0117071e11060f01050d150b060307120c0806010f030506030f0d0503010303022a0d02010c1202070303112d03090a0b120a090215 69
    0x11640d04040403a40082c2d54028121030310b4145940f901d001d83c0c11507070b00403034421180a1000c2c1c200036014400b80000c4c10f00d80002a100030b518281030108041c54051031981d00c0050f2040f0b90748400310090440103240400f03500e8052158031131840441c00c0c20000d00382c01da059500c05814064810070316210083c0244075103c026010950344d0700300c48802c0d01c41100070b520400268407105400c80b40026141c040b5107207013800340100420401401a00d170b81c0501045102a2181350200301e030b4445034006030030002e09843c40d4410b0b11a01c6143c0242d00d0300007004d181264002c2d0261400319042464405203c0e0702c1c90414140b40311a0811030500e40352000169801c280189442400c4558555410340300d070f0740100300e035030260b40030a408100b050b134071180d03603000300805030050441c95011148001c04ca21801c0520343d1443e008941032103844400300140d5a10b000003d11034143c0c241d961040a0700307540401c0c410040442c40d0000a1142e51080c0109100a50b003d071900004c55010f01e0030709000d41040700c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 725423462 1250 725422212 725422267
    0x70f08190f08032404110a110f0a0b01030c09052a1209060a0f020f07260307031a040b0121020403020d060c0f09120305130306020a0c0224 61
    0x31070950120315290080c5104041194015250107078511400521003290036105210f50f0a000741d5005102c08402529481e00042c244007515907100c5411300e08050701e07056054041d00c03c1801602c2449100e001e000d049900a00c21031410548516407041038800880d00c0e030004200030240d591420045215260310080c10009590170449080405000c643c4242c0e01401550301807800d004142d0366600c20b658405041820071450b00e101602246114000c006001d0301074560840700031038a490a01c030200704030350305010a9a492406a41c050024000e40e184004200544071020f090b904203440754802405058698048502c05803010000d0014102c000310b01c0c07250240400401a1030321862107252510844000ca02c60001e01030080103250041308140401c40900400c004100c00b604a00f801c2c0b41c0c0610380544c1d910214a80300003040620380c001480113100144008481e0b40c07020791000e10034801c03900803e120f800c13860460400c081a4030803a01c60711040140204568000d55403451020241 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 725424712 1250 725423462 725423483
    0x50d0b010e1008061003050c030d0909021e0f0406031a010816110106030602040810090803040b0705090a0909020907230d0e010915050a090f0f020a050a08030903070f0819 75
    0x8030056420040c017942c070f000c4000c114807014400c10030144500b081c80b400503002044500e84244008024070020300c140c0c0c03503071540004c00614158402c075880040011401411303555099401c0c0070500d075806803040c01c001910b050400003900c107940310310247c40c8a0581d20784040b0345800b00e00700f844140d0104c209050120081700d044007000e01b130290390003c1d4020b510040e100e40c6441c0304507040440d9042201900e51501c120040010a240b080d41e4010303801072060101340d6200b40c000d0b80d851103250143c1c3c2d8400200400003420300282c0e000300c1d081501c01e85a002171600c4c0d0840690b00f1524600b5001c4045104120425080c207181000d402d540406400c08503986140141640c02c56580000030f4508010b001629440d0a8083c012650042c98110080088000e1030710307801d40f8240568030003485244245101c17410356440702c2d801c0014220003041d4410041c1d031041d24543d2944902007460181c00303094000030b00c00500010460840e613010000d0304036850400081c2d21480d200358002c4071803005030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 725425962 1250 725424712 725424719
    0x303120604180c06110132092b120b060301060c0f1704061409010e090c0c011a04140f010e091c0509040e010b0f04051503030d0902040501050d0b010e10 67
    0x807080e00310010a055111054001c1d483c20a10382900c003600707412480038080c0c5034102207c4003648600000111317103008005140d103039100c1e160706200640040202c071201c1503003840c106540c101c03a2a402d000240e161928803200407021602910070b40840582c0c805010b100411a490040003130492682c4151021000740d10300d0703992000c0109003110403000161000c1000e0000c40d40203160000404803103825a4101410f00000900a140a04809000b564500089145030300000c05031141020b800c0028441400c14000d0100040c501e581014801c0c0e051280c414007201010f802e06010300d02510700003c86a00344085d0083c000c4000d05007210314800c100d08004100b0034485038152180c415a1001e035a90310200800094902d0800404801c0e454100d090000c3d03940c80c03141c0341804500b41c0e0040b42c5681d40030070f0300c20044000059160035000000d49402c444003103a002c0350919100f00e908000d07603620385090040d50300c5c054000412554902c00140082c0d4440032040303038080c10809410641584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 725427212 1250 725425962 725425973
    0x13030302030d1a0d1103240601030606020a08030115091220060c06010521150106081e071404051207030215030912090406030c17011407020c12010902041d0c030312060418 75
    0x8580c280440740040c04c7d42032200961303143c05003800501c0184020b004404071600da1071907600c010b20590303a414030b0007580d01810f64050000007008103102034950010100b1070a1082d00c122900701d444d041d042080e02c409a107880e08409664030304403440d006041c0d0b42e00302020b210815100c0c03140d1420000a82100d0a041001004503010050005184038601d526000025220001c040c001ca119905081150000030071108040c4e940840e00349410443d80c1c4800c800804503204982007980c010300780a01000c000308000a81000b203d00c20b8a40c06c4200340703800f4100270180001d65480f9075682007080800d911b400c06001812411000600004403a582c0381d541d0709280246a200c0345030505408001d540c2d0b00020700c0740d54036020101410280782c1c6814003009440d200081c05040c440d0005010b4419208000d41c40b890308541c1c05802000300700380d0b0f203044402a42c40450000b42c6445080811012402c01005403020b4182c3c5511414454503400108405044010052404803240320a210003045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 725428462 1250 725427212 725427253
    0x18030803072307261606050c03040f0b33090a09020303030f0a150f08010b030d0e130f0608061909020d15090203010501030602031e0105090406020c0313030302030d1a0d1103 76
    0x4048064548217485840c0101c1560780007170076640c030818140104004569564480b618080d4010229216a0f503640348120040041c1c0c042d0740074400c0000e820305407500c07008010b4580103100325408800340c3d407404096002d60b0800040250550000c1c000311341400c540302e181c981c209210120100d4041a8110500180b44081c0d01c0303003808698014082003802d2003841140708840082d4050030007020b01c070f50081c2c540402400301c40c0c025200884607044c055001c0d40b120201510382d1400348585540c0c1d1404039a104001d560152070700088801c0050b1001b11440347c280c02c1640030381200c4038001385407170302e40262010380740020001c1d8a51120100584d020b1182c640607600c9500010384a00300b18481e42c0c03000f907185050704208070383d0340010f226590700d2906166006034885005603444000c14925811805940c140d10102110900301200305500800038021001000b801040000700d0030440c0e952540304011007542042071001e00c5400301e1000d8425000d0034002400321070603002e10b03040284004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 725429712 1250 725428462 725428477
    0xb06070f0506010f170c131805071d070807120e03030f04150b09011205160f09050a05012402010b030a0c050f2704031803080307230726 60
    0xa0300100e0044c0855108103489a01400c00522503d110408580f4025a54000780320300d644546d50f0a4190034003400076411041c220700d86420b0141c9080d085242c00350313071212103026012404103074100868120349405035040c455042a84d40b1540c603160010161030415082142c10394494550300c6c07850070700500b08001e500600b101220001d01e4070345400c1c40d1203d21204200010128100024049250750307142010f81903403240c0042200301862845c0c05840c2007070020340321a141d81220720004129032910a40009c580c0f030f440741804103548074074245007200c1c024000e22400740002100840b81c00c074459180385a80d001d9000001d2003c040750300007440d121030142c6c00c407049a43c1030b50a0010742031803151a0804207094407200c4240c4d121000d10300017805240760168070b1201d69000070f014980f240ca083c03201e281c4000d0311844442d84038180850240d00880383c94010404445004041141001800504d010060546c0e0700b0030640c1d0b5a5038481c0411000c40c034441c200c50444c02d00c081041c410041444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 725430962 1250 725429712 725429723
    0x20306010f0f14120f15060906130807121a01060c08030402010306032001030b0a06020d05071511121003020f01271412010603032a06050c030703060503120d0b06070f 73
    0x85e04c2e20300f04260600000401d02408a41a4107a40e10303603440f4081070752500e02080794502e0316406080046518042154000b8205202e0300400141c21032070380031100740c2c4030f02800c0303483d4603608407105030b206001080c860b0400280302807222a011030b0ba12070107150824030524000c035090b540e030f40300d4440c01c1d51000010520080201c1000130b2942c1c06120b180902a02510f440030040d00d40100603407204442c0003000c0600a000603060b0420100100a01c840c440340c2c60b00300010080c83c03150a180741c0000c4685059102250082030b02140580c81580482e0f0f4020070304102038004c0001190000d070342d0030301e050380000030049030442c21407859241c0d4082c15455140d084540007030402c0010440c440100b07074203141d14002060010176880945503980724880129031000119040c0490a07800c0e041d00041c0002d4606001d20208560410040d8010800b0f07035402d20140f0307220005c0580750711400b404c44440c8601003104048880d20740c2c01010b14008010140c4d07040080c81e840381c06003046030010032200e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 725432212 1250 725430962 725430997
    0x105130b18100e04110d03020f01060b070201200c01110a060504081210150c153e030f09010e0d09060216050d03080405010b061804050a020306010f0f14 67
    0x25104848110002448a0350002c3c51030304042d00c2e400038075103540c0350290090084555090903d8000c0045800710481407008025503944c2e001400b0340c64020210480c0041c14102ea100380c02d0149026800d080c0706408003509070f810070701d0019595104034800e100c00c1801400c1f201400300c3e00d5442018480d500642c1c8135903480110605801040c0c01c0149255002500c030401413190080010380d8a480540b5800c010300d0303001c2c0c98103200200501d8022120245402c0c0308030040c20038140031030040c074001076078081d1801c10703145103c0420082250341000c0d541d07202071000403140b54200c006103401445017000045e804403840c0c402420035580440260110300001c0040000070781c1040740500c05c0e15034124680e50a42043c0010f5141030451001604002c003203004902801030a601203400c6000081ca000c0c0e48409000c1600d000000445190380710710303d020005001c03900180210303481044165203880810f540725106603000702e101d5000b1000c112600312440e80714007940c030041480d01001c181d00c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 725433462 1250 725432212 725432221
    0xd0203040b060904030c0f0503070605071d0a14060f07050307051b09070801060320210f0708010e042d0219050307060f050f0f040e0f0405060105130b18 67
    0x180070240a65000f401580200400300f0381c8014582401c43e444a80d01c11003504c90b0a01c00c0c50350013030300b0010700000c0c81c010900a800d5000703038003040482d00200ba071040c01c0400d54200b140c1c5801c035109810392602c0e05075020510f0328040000f8901c072118101480c1c180045629030f9880c1d078200001c00c0f190703035003e5000c403161402c2450400c081550102c0301c5107010300d440c0e80001c03d0f00c0780610403203050507100d0100b184440c0032441c4d5554943e65080d00e81e030721070301c031211001803503a50038603410b01d03024210020038038910859030154819031407074590005d01e07480c002014804401c0140b0a9800b0307078817038041e001071003044109400000303030803803490341d00060034010403c81c0410203204409080c41a1030030045910045103860840d220780c01c2200703c0c0302104109075120710445203807103242d40d00090300b0190034503800040c009031031705905070320099a91507150049040d41591b02504030703480080100700d249448000b040e03280715401c0c408110140064003040c802185d4512840b81c6550320001c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 725434712 1250 725433462 725433473
    0xa181e110919151b060507050a030c030509030403020d02011e12050106020606030a0b0a11030a06080111180d1a19050c09061209120304050d0f030608061303140d020304 74
    0x40403441d80161405001c41c50090300c8444084003280340f50501c4100c6041105582403060084003950700311505000600c0c06180040c20b0341d001c602c80c1c40c0800c3c50034400e20f00c118443c2c882c0d07510510074000110325080c215001c1200c0c6120a6608a04200c030417089114090369440704200c80e40142d07112015102018424081902c0c0c058001c0c00440d0700c604c0800150b581e0025600c006182c000f4044940c81d00c8030880103014100007481c52440d000c00206129001d800741c0d00002c1101c180344000c104860b44000d070075001703219203010442116810494110307030345030016076801641c2c41203002107aa02548204491000006c95010220750075910400032003007082c0c0226640100c407030f500d0741d140000310070001d0f030b280c0038142c2c0d85002c0780444030000d040d04004110001100d1600c024058032403400741b038180d81c1d9002c42e120040c0000c40700c03264840b60740e02a01039039007501c0ca404050007041e0781d1142040b4034224030000540802100526440b0040c041c000102040041650f002d81e8030f25050401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 725435962 1250 725434712 725434729
    0x6040f09061412060a05060f180f011203210612121202040617090a0605043008040b1315092010050328090506060a181e1109 55
    0x820b406122200008a0043c0c80401d500f40d10124640d400241da031516400302d44802a2500c00c00c1e00032040c030101c0e015080c3c00343c08961155881c14881422a0780358030800c040a00316800050101c1c803021198900c0031f4940d030b00600c01c500b400c00700103245565107100c0c21811045040070b84038482110a94124980d100041d401d00300c82034141075140038640003006111442c2d070882e0803920440d00740444c58400c0c0902040e0540d0707400c440180624103180c2013490f210100e4004000038281000c4031508481403100603450f00b81010b0701c0c3e0040300e80c2c403502d85c00700d80c003401407907090701e2a501010800015010a81c020003a10a01c90000300d1490700c0c90032509840452455011010313002039600c200d0f56514520460b44c405502c0c0540c0c40b5128960401d166248a80394003000c0e004c0c90440f051041c00a5219144442c01201152150b458500922107410003c7c051008a002c2146151070003803800c2e00222016444403036104644a0009910021514200c02d05511004005a02c0400d071800c0b80c81d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 725437212 1250 725435962 725435999
    0xc0c011404150b150a020109020301060e0f010e07020d03180b0403030213050301020f0a032c0a110907120b1206090d03060503030f0a0c0201050d0f060503010f15050f06040f0906 78
    0x40002d8003002c0b0004400929140310f204c0d00305000141a52200e200f0b41100700d00c517074007500034484551510302003402c2c1c4104542c031901854504000040038040c1d0700c049406121150081d24006070000001c40140c02c9081c0407108041c00325100200040003060310511490103542c2c0141c40700c00740b0031105800015944070358030980c0103002d100d040b03100d88402c6604151050400045c907020340d09540c1c9038842d45548038800c01071100210070906001240f003c203030318840c1032081110084030040054002c81a1811400905814134483c0003042c1a804101c00800040c40032050882207005180b406908a4880d00740307800102082581c0c9405005480190100310061070800c00642e140c3c0c502c5000c0d03d5100c500700007001405400350790240d000c581d00c1d903202000500442426014010162115104040c080e41c82c0010358131030341106110f0b00c403440e0800c3d00e0404180d4034080400904500c2c00e16510fa000700c0401c40010301004008000303000f8901103502041047c94400800282c600810 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 725438462 1250 725437212 725437253
    0x180b1f0501021b27071121090f030c10020c1008010305032d0d09110108010515030411042d1a061e0c15100803030402090c0c011404 58
    0x386515481440c80007052503034203003076600002d2003d210745000d400261340024240d608107520284108250320021044c003004800044820303114411800c0480c4296405441c0103811090084038a1f91500b0160b84129803c0201294241c481c40301c0026681e404140358400543e0005408032281e061203003d0841c0f2000c0f82c28031000703561454488a489100310803080c50f09a8041d01800b5031900054003030450003c20411003626000c0030700e860801050076071810342d4840091120009250700c5101094165100649040e2504e88107180707a0b0860b410150088070900403100841145031031f940b1a51102c3c52002454501e10b03100124004d52121030b01c0d0b043d031906030a1850302c0c503a40201d4104070b00c03890400d4441c199503040d11464050380041c07400140740c400c4000641c240013004002144292013822502c100569182c042d2010021025803007009a10740040c80050007510303111442c1039001d003008054a180c002c80140301c6d0b0840b50820086c1040c5640766040c0301c14403207080080001e502d02c45 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 725439712 1250 725438462 725438473
    0xc1419060509010f030e03070c140d0201140903010902090a200901080105010c02131109120f0601032901061d0102300d0612062007020103180b1f050102 67
    0x140052440c81407602c4141442014070202c4034142c0720b5440440d4080c42c1343c042d00e4a61113149840c4200d049181300b55000716603a942418603030701d04201d48503001179050b15140750450f002400c5840e40e801580555905541e900d03082800358030b90a003002e01c140d10b08080000e51180c100e086500005026111a441560a12030740e10071781d800c00f4145040da5000d080c4160b003d48644001044c0004400303203103540504203100e4240000c0323010301030000158100c0d510100b1124818a1564580900d01601341641c004d000410205c2c1030040c0c03508c0e1410308403a081003640d81c9403060101c0b01c40b081c0d03c011b000490803003242c00b4000e80c18003880710300c900034800340100d1503014030103900e00a01550354591605402001130300b40c07c41101151882c40345c1c044203011103940d400180c0c40d42c000c00d08040e9600f0342822984403030103080016006808001c0903200341490705580044004129080c1d10313841039144000c0240210750400842881800059101c0c14002403072041c0010003512540941d041d9400f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 725440962 1250 725439712 725439719
    0x30c0439140a0e0d02131e0509120d020a0509061b06010e04020d021521160201020309030409020702062514030a0203040902090406030f0f030807021f0f090c1419 71
    0x12110070700e038000321011060304c03140380000341061100c051000344143c94880303841c04241710f00000340b1401c4400daa00300400d0707844c0002240c80e400d00b59004440c01030104550381ca900070a40c06040042c202e07252245c144176019000c55416803080c449010701c1051206103035010502040b900703000d0b110340060b96903035080a0b030200750540c09541009110700094141d24640040d41d0702a43c00401c07a0305074140295038114080e143c0b0b0fa506642102062a8210355807117114014001c481c080c00e81a03008500d401d1414080c00c00035000386100704e0f0300240c100148100c0402417182c2003000c41c000c20b0388000754040c615024609030b00b40745034950b080d0028401c0b100e003142c0101c19038049400b00c0b500942da036010390000500500032a04000c1000c100003402c10306101452040118180c403d885568940e201daa1050707a0300c44801e41c29981d41722400070442251341490b0845800c1201032403012a000180c5d42c4c1d240b551f42048d400001142c824404030b42014503003004e000304034000c14600c0900e141e05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 725442212 1250 725440962 725440967
    0xa0e0f011e050f0d080d090b090a0503040e0c04050a3c051009030f2901083307021f020304020603130c120b06011706030c0439140a 58
    0x7103442420710400340e4041c284015140c4851080d103007903102112964a48040c0030840c0281803807002a034400f0700c680005002c01e000042c00e5040c00d90007800a500741807500c0000074141c0b100030422451910103000000b0152140800d00c4090500c11018002c91101c030411940030001c0c2d0030b81c3d003043da14480a80615120100d61540545a0075035038610782d1040c6035819925507003190310041204200c40e031f6100912a40c0304404400c494248105030000360400700c0190131800a0003050869000743d8040007200410b9244440b100e8030610000ba100c0c0c2d0728a03000300c6a403400310b5451015030441c041c0d998220680581c907014814010404500350b04150b000325606000c000e07c24005c800340900c0d0030060007465001e03500107001100d20404600850300c0d008000040541e2060301007541c003625140c20a030004049441400f000d0000d0a15188503003c02003d46441c00490b1400071249100d02c456101d44e05502c100c841504a202d0100111214024040b0307502c101002142481807213034904440e03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 725443462 1250 725442212 725442269
    0x62703030f0a0f20070201031113050f1318020f03030c060a020703020f030c07050a0b0304151a10020f0628020a18120b060306010605070311010603020a0e0f01 70
    0x3070b220a8006144034403200800000c100f6410314500b1510080503900307004050500601c0064800c1c1e80a010640c0d9520844080d80144100403420344a00b1005001c039090107031080c1540d10000b015040d460300c208414070115105034944c0c480003080c0010300015410010b42148074040c05400540c80d00e407400e100c590303e034071380680060075180d00020381c00c050510030084000c503800910252640e507403030202590394581c10b6100300340c062602d112001541e6540007003524404c0f41c0010000c2200011440c1c044002c0c11210394480c512301151a0424268a5030b4440300f0081016400a040c80191500020b10301800100f6045500b050030090619009003a19030001090386000050307294940c2903015200410400c1f1009042550f00500191140c03188081d100803d0190894151946400040c141c0700c42c024007500d400b00d041044400c00180c8511030284124016400002e803081c0c9903400161080304035801400040805014801c0c20840c05170703502d00505041d085619030248c120040489030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 725444712 1250 725443462 725443471
    0xe060c030a110304030203030307050c0106050f1e01170901020a030515220e030a0c1a0f070e1c050a0201080106020c0a050d11030105010816061407081308062703030f 73
    0x2d41c18480450402c10001e07100519801400d894130703880c1c104c20080464101c0e07591031901d036007440400140d904156207074107041c0401500d40e980d0143d0130050443c0d007100e0502c4050400038030421a200310300d4400c81d0140681142400540d540c00341c1440101501d0f4060308500150980000310a601d9030741800d0480c5104001c0d81348182400d0a0484400a20010341d0001d010300002400107007142d4402d0110014034030a60340b0781094006d8035001224648122569078440041901027090b642c010304102a185400a00d2040d8a9004e2059240e50a40da6a401c5a070741e40100d00500856800c1900140509080d100034481c2d840d1070740000300094058850039018030300c4d4410600c1400302e92000c03000350141c080d000b48000e507501c2c0c48079a9598110b100e8030a03508841c042c04100c15118030f92551183c224401c049040c15181e8580c03118642c03181031103242414130740c500060794810500440c1d11945c1c4110f4001003005001620000f00111400340d100035800810070000e0501030294010f400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 725445962 1250 725444712 725444717
    0x30b01180e0402060f03010807031e0308070503130f08340209150315010807090e060c210f0118020708071101030e030403060e0c01230d0b090f06010e060c030a 70
    0x780e01d440c0042404e0b4071498003280c3d0700d41d8001001080b0003138005802c40480f4460594282c0c1c00c1004203241c1b01024072040000c0005602c175002c02e09031440740c4c0166401c04408010118070042d540c1e45d504a00800000455500c003000c1000c44a80f6400700d600030f03141c074944140400314910000020002041c1c014028415015400429000880c6506211030f03142c000c3e00712981f07818a6a440ea910342000d228050f01344c41a480045550085401405d030365250742c0000306a123464103500c0141c190402d080151541603603049031010001c900b48518020009841c10100c0c950500b50520400000c03228034007e49401009690000f0b14810215034056422150044144d882800120090640c10401f0103251002007004004d1120703a9008030302d402c0e490340c225540600c00c00010b41d2100031030380b851010ba800035009420b034401c00c01c00420f82000308020000d14100b1500000e51101c606407130015a4080b807008010180d600182080c8803440200c41040c14103509002c45d0b5a28440d802ca40b404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 725447212 1250 725445962 725445989
    0x90403080a0b060301061707030209010c02063417040b040611070b1918050102060c030702030d0606030f154205090a0b03010803070b091608010b01030b0118 69
    0x89030541d400708002d4040200030540c0d07075035204002011900c501c1c09070314090000c080880e08031070080c400c80e6210b14040c7c55100e0307040c800d602009081c0e00300103400716524618810303620342e0400030942480c000b1500583e0000742c01107030500000901c1e00401d09e5a845000b00403d0244410b84400c0d10200c440914100c11030050b001940c5040108507404204240360109010010743d1000c010303081d403019a82d54444600404408100800103148140e6000d45c01ca580400d2005007090700556000e41c0a0045030720380f5450070041d204885459005100196499140c0c3c04810f0513805a81c0312050031b040850745450411440c40c7e1101e0484c0b000c020010a8003140244a015100d000050b080c0c050101e50030305520108080e09035442400504c2c4260240600403449050b807034156410784804034011401d00010303550312504c45c1c40142107001507100c1c039842240b0201300c50a502d03015100072000030660480c00e20000d803d41c0c2404090741d041c841414440421100624518800c4501000c0440c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 725448462 1250 725447212 725447221
    0x1d0d050405150903103306031d07062303280e1209040e03070809060d09120c030e0303090d060c0302040b0d0903090614161707050f0d03060509040308 66
    0x1160351007603c04144e018001c8000020718810507501540040010748030822184c0601401070f80342d0165030180000c0300b07074018001c0c401117100e0781c4408038034042c02c540340b16100981d0070780d6843c118440e84441d0000c5c4081c070001090100003d503172002e417000780c0032180c194104020254041496000254840b1181000c0410149007a42105400700d06e8407017074541c030f410081400243c90b480403085d180180c1c02c0080c84540d401001007144c0c0b000b504014a00e0170860f400d810444d5540c81489400b59540d01c0b0410390010450b8002040d03840c59042c0c84000d5505654500a0500009411080d2281e0400d2101ea020343c0c640310001d500460740702e100020080050b86090740203014581100034840d10104683c90107103410780c4602070050117515651180d1383d07918011600000b041c5252a4164000d01155085000340035100302500d200e0310501101c00d81c6032400d561f03d900120380036600b5901084242410342001c1c88a8840311026180601245007040007017040b045000d000201080003100004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 725449712 1250 725448462 725448499
    0x301030f0f02011e050c210a0e0d1703040605011703040512011b020d0e0d030504180b10020c09130c1701020405130b040c0905090705091302030a1d0d050405 69
    0x141c03d403000041d03190845580e07000b00109540c01115902e940c504c290940540e20000d001e81180c42400002021854440c0c00b000840e1801c040f0100203411040c07160b0030500052407a02f8100314103d00d09503468480c9011304120080c0c9406074003c0c08144c2783c0e440c1c00007090201108440030b4400541e541070500305a602c0e401e0040c43c0008079419204005602241c1041c0e0108071010309840365a01c182198400324200280f02d07040010040c00720348100000c000034504554000554411400c00142c101c03282c40c04212400400d01c0407600582100d000704400749490020640c02494107600f03c50090300c19a1640a81600d50040800e07000e00d04c41c4940800d00300b501124090100605400100007031160303840082c10502d403002e4444c504014280820300d11403842001110070081900c041741e00d8000041e10240d100e00b10164101d4034003222403c0140c054001036001da09160300c00900700e260101e030409040c1085008854903005a40d0a00e11a5442416141952412200c101c002c00c00032602 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 725450962 1250 725449712 725449727
    0xf010f050c061302090a060b041206140a0e07090b06070b060316061d01030c0f140f040b031006020303131212090311060a0b060418090c030501090302120301030f0f0201 74
    0x42590a1142e081005543c140048850103041d2003070300c0008040c0c541072840406d8403143d0182c59420705007880104600c0078507140364002c06014403000140307403c5c400360003044000100e400a1419440b400d40710200700003001030b000145500401040680d864a0002e110b5206800c0054030810713080c004a082680d0038042c06209551000d00c1000683c0e0301d103400742540300404103810303050031071190501d0780c0c0d4003034000d220307141049aa8410108102ea04140c45041c0700d176203100c201c2081409102e80742500000200003034012150019100e01d08030750810b84141041e0448401c640081c82441008550752013504c03d1940e00482205d1000e0610404440c00c142c5015411441d50802c5801800d141d0005a4000290960000d42d150380d52404203a00948988034511030304403900b000100014a8140b41c0203000300039418010070802c0e07407034a6807804110aa00150783c0d80e55100400e0007050b40403c020207802d07202164003400d40d07165031250b076520070b4080d1016040100010400d021a8410b111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 725452212 1250 725450962 725450977
    0xf19110115180b1f18080c090403120612020a0501090b0f0c03160f0c051c0b0a090c0e07090609030c0b07050a0506070f080a1a0d14191a0103020f010f05 67
    0x203000c81030104081c00c500040c61450304000c60880384c0c4045ca41c5850705a804140e4200c01c0007000c01d80800340a100c40701da40100141c08000080015100584050080000030419240311401000c4c003801085080c00c40b83e0b01660510204400801034003c0c85019280d09121101e02141c589010481c201c8c01d602c54440300c1300c0044071641d020010010441c03242100c25010391900c01d405525102403100d50f10610200800c0c0b00f01c074401c107900292210700c40036841900d207107020802a081d80d4542459000580200d500c0c50042020481007a44c0030440d030004024506d8200b60482c40e507210010503071000d000d58407880000040c00c0d400d1220400c00f145105034407604903800c03440c01103001080f8001103d40035001624190116011021b540070f2100d0720a4031038141c0c02d0104805007003000f15240e0741d1040b00e01403101d0200001c444000d1101241040030b444658201042d0380ca010340c0d8003034401608010042c0614014005610b80030716409401d507007820807040b01d40d18103000380c0306809202c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 725453462 1250 725452212 725452219
    0x105091306090210030212060406260a0b040f14010203070c11040213090c121a010f02211b0d0c0605070905031002040302090f0403080402060702060f19110115180b 72
    0x3501c04d4240f60700d58020101c44d044503200002c1506c42100b080305485d494410b02c0301c0340705240d214000d02c04404442c02407449200707049624121941d61281d442e40e008840070b45003c2c8180c56040244000d220018818040c1c5000031842c61030441c0c030241c0418010724025104008170200048a5255941110200340d405080382c000e2980c0c42c04c0c214050001081d1002c00a41c2d4001e040105000c0c074003e8a4091240072003001500c4c100030b0044444284c031100b03940842c420411891810419044400c85002040c034529a13540c40703107601d12811402c41d6403084940d80c004070400000076405181d981110380c0c03108001c640341d113682c9000c0360140c00c80d41040b070307060140546100304000e143d8014012688240c40340021540c800514461840d012100580819010000039005181c40001810111b200070324507410890080341881d44e5402604020308030685011291b1041e6401c040384402c0510a5002400a8601030b801400390281a22a486800320328040701002c404480c0c00100c0b1055000c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 725454712 1250 725453462 725453479
    0x1514060d0f0b180f0c03070503071a0c03041a070221060f0703022a01050f160f03020f070b06030c06041d0405010b030303040b01031a1302010e040e010c0207051801050913060902 78
    0x240b0784c0d15140d2030001805482442003d000003a203043c0483d5220840c0d40d01d00d030141c812800707405425500d030b1140e04100c9480c00208404604401c400c840c103d0800350310014103451300030900c10f110760491001502c168255191000e000903180005501d6031040000b621198507440d282800d0700039000d02443c0145102083c0d10700404206c140c40d402d24100f44800082c001521654050b40c11303900f0942c0c074403000075070000c83e051585009180c07410450606150040c90000c84c0e044101c40354101c1d8608a450045500601c116894200000840310720210f445600c4c0c2032038070030808503071004043d0f54914003920100090a002080d403100c0c440e0318010302525601c0c0350500d031031b402c40b101c24003007110080441c03040e41d5041c816000c0d08134031440d0650240900e261903600195101242c480300f481d44180c0f1003112016100c0203006070516480907400a0800c28242420410042002c80e08580702c0e41294004011650300c94000c5a00000000e0141d11420b00e10b082001c041c2104090194010304513 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 725455962 1250 725454712 725454733
    0x11806180b0121390f0e090a0209010201050a1e1119021c0203040605040b0d09051b0117090d3203061206070212161514060d0f0b18 58
    0x390415000c1d1900703a200003802c91440018148411803a030050702e00006031300d90b078560650003403200003441489811301d00186030707801d0001901204203c0d14920017507000300d08800036507024010541c00200d121400c0c840c1d40140c2c0b00c076607030591014071901a6592078a04040e14070741382d64112100450940021042040d01c024044d43e5040258680c41110a15481c060401c030b2010040e2426102c0959680340380602e0254406410f4110030100c0d2200c554800603100001c030100325110344c1c8003507103022544850300000054062140841001410f9a0000400041c00c001203a2070280085d10b0400540816514801242d20704541c8e128440b80180b1101c2c151601a18002a40c8182421501d92000c8400c0821043e154102600e002c005a444504591028400d080161442101c02501005000c4c1c0036100d5881d20054410b04090655440e0860404590070b1481241e210005540d81c1c0b01c41f001a03610b09081d0303585030101030013584100000c00d50b1008004044281c80f2540310444002c3c444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 725457212 1250 725455962 725456027
    0x2070b010e0f04210e060c100501050a122d060504172109120a080a1505090a0209130501030302030310080f0c13060308040e011806180b01 61
    0x80030300450720001034520001d025802c2026080740f00b154020805415020082d0719404901c40d420800c10501082c2d1017108440c0d128a0090f00e590580340c4000d01c09074407021040710854106801803402000d54003800d1200c0440c0e0800301c030030550310030b541c0c0e15602c604514034800400f42c0030000c0300001c2c20101074028030003945c11590246010302c407a2001d991201d508952140f003000c00f11107000442d030805180c1c91540021032035204481c8400d42e440c491b4000010384050380301c050b022000c161000b060146ca598548104001e941405003507488150801000030700c42a07004000402e9181c00203945140d640f0b0b02c0300d40c4403000350750080501c01561217150103916034100f191274030f1f12528003020020f0b0031b0800140760b1007020603100c0a003d800b07040c20b050017201a04000c80240660300d0b0301c0008001641d03100104000d04140c0d00001e41541032200701d040e542c15100a03000c01c941040b8043c0300754184d50065002800e040940000c28001e91001a80c0300140202c02c0d61400343c3d080d003c00b4007000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 725458462 1250 725457212 725457233
    0x150c0307052406011808100204180b03120d0605030118030e0306010e0705131d01030309080c0918010b030105010306020901030b0411090108070908010c0302070308010501050901120b040f0207 84
    0x148504180d6040302c0484031041d40740c1c0c0c110481c40354006000300124841d94065290030903030100c0c1d111884545030b1141440c07454071a00b543d40d460942d81c0040c00b040a82000c518201d031540711080144a003d9002000a80d50001e00c03500c0303404250001140e10f1409450342c886c0008100150003445501075006101003441c40b4031100343c0100e520905880d4543c500480c110b030580d001c040f040c40d500d403611801200c0c0c51700705105c06a002000c042c4003082c805400c1500f03240d080c8954220100303541c11454000d00c0104280d00690789030307024004480d802c5c1d8401083c90350007440c00040311243c10003422400d000d4219501c20315095440c200c004001d00c42d00d5002000c260b00282c906100751600b000c00d1000700c0d10303140c17503580100d4014460302c8801d40c410301171990402c80626280000300e0b110700304542140e5500c0070300c40201750b00003682d400701500074458a006040c00d0a112341070102410000cae24020162501c03510320b5039a108500000e07911b6900020314254450021519a01e0703900d0840c0d9000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 725459712 1250 725458462 725458477
    0x1050415090f1101050702060409050618091915020c0c090105060702010918020c070e0a06090b010f0315080706120e0105130f0f0b0a020d15140d02150c03 68
    0x10100d4030003100010381180070300301c035180d0300c40c0c01201055595200c9003090314111100e2070412400300701d480050703a01c0c80043c0014142000340000c0c81c0c08e02c0410424002c2c2080d000300c101a00450030007a400c2404a00040740040e400840b82c0c5c054903d02d440b8640c04920000e650a1070301c00708400364541c400142060700c40806482e01400c59898004010030340c002d0160090001d014050700784040f81e003614400348015076514003d030a0000c01500907051800c0c0d40c0050030903008600810002c20130a004a00003040900c2e000c0141185d110002031041403909105000d140d02c41c4480c0404020440c0c25800802d83c10040d201e0140e1030b054014883e64024811125042c00e09507480405401840303014000c001e4029607095062182d84c45110780d030350040d4181c801c507121100c4000412041280584110314140005a85a1031140e100080314000c0e00f1030301c14426180010b018001c0b4440260080c0c010440380c80c102c8440620010342c2450320010440c0c1003032000308906c004c0302000000360030310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 725460962 1250 725459712 725459723
    0xd090503131e05030313030f11090712140601080114120f011a04051302011409102d09061d100207061202090609100210150f1e0b0a020a05010e010504 66
    0x8983d1030301055541d0045003034071010120003a1003040014200725280c1202032103070810410419403000014081310b0308440c41400325400c4c1c2c3c41d0000d03051071845401c04184102504041c2410b201c00000c00941701402802c02c035082c1c141c108030369a40c0d1b00e031103503030100110022034001060a426441c040c1c1a808501003418518182644061401d4010144150991804070094104580045a080c2c00149034000c00350005c026810b91521052070580c4881d00700c0d02c8041c4c81c80945160200c1000fa0343c220618038200404024510b5a0300c01450000c48c0c40c18601900400001f052000007102400d440b41d621140c0300690071043d54004c02c000c1e00310342d0903441e9035002c4000120780c3e1042c3c1c03140480240e80058100007072903407890003003010619805144101c40400500c8035410f400c0316404011141d0200507118200100c45000b803a1501a01c070780c0e01c0e03140405d12450350f131242e10005130090340c4607018040341c40c03c0304a200300008000e1a1300500244264080c2c2040903000385001c1c0d80030b41c0e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 725462212 1250 725460962 725461019
    0x604121205250528112d0f0606040b0a1205100c080108031e040b130503010e01060501022a030303180721060b01090909080405040b03010905030d09050313 68
    0x7450b50142c010303601c6465640d0b40d8404611004124804070484050a000070701844a1107110300c0c0504001455400607481c00f010f604001364240459020039082c1c1c03228407644640c0300a00c2d103e1000c03448540040041c1d5012a07145420000543c035103030240c01c2003071000400300e6035909005000969101103041c0200800c2410030450040300c0d091000d01645e44158002c010b4070300b002c01901143d1045c002224075041c01c2503100c0014241990086c020030350020040c0600340101d00d428400c6011117000b00000300842890400040c1d1514484910107800c00c094030384103150754007440380d000c809090080590340d0f01d103480c0000f048100451208a0520311480201180c400b0105c00d0450f8100001040865811020382e1440054030212140b14100160340c403000441219900480c01c6e154031036110b40c1d4540342480301b03010403108000b058030700c00d0303041a101c0d0300890b0f40441111000c02c510080843c2482490500610f1803180c2d00c0c0420708142d0000340065502c81c01464983c0465040c01200d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 725463462 1250 725462212 725462281
    0x1602010504020109170a0b091b010504060e0d05030d0207153603030b06040909030809150118060b030f010623031609090908040806180604121205 64
    0x24200c0d40c0488009011403104041807043c1c521190101c84c555145d41c0850300300040d1a41d51107504a4291101020f40d03000c1c560000701c0e0395183c0200c2502e41c00030f18100741031514080c0c4c020015041d012001e13000f0030451301070030140710045c42282c040708101501035507a1100d510f0704181100030704c008402111300d82001d080108506450210b81da85a035080030929143d070003000c05503a00500011024156560030707520310341c2c0b162000392004040b50280062040028100074140301402030804409400030b02d904208980c00b0780015040d1140d044140018011200c1a20001c00c0f15030011b140030303080401001201d40072088114103803940740d42e0f40640e001c0020034040b0508140741402c00302520900000d1030481001001180079626482d003014517558400282088503482902076a42c40b05c001418084000b04001d0301d41c015030501c1100c000702400440c1c0584502d80588010140401002494090b600c114811070300ca680d09841007201f400c004440b01380b4050741c2500b00021030020404d20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 725464712 1250 725463462 725463467
    0xc0507020603040b1e010f3c1e0f0306020a0203120a050414011b030209210307060507081006081512060411010c0213052703121b09010e0a1206020316 66
    0x18101e6051140c0c11280d00c2c100100c068040b14188100c10100078915860f200c040174120000b41202049210076031564204500c5c5003601c4440d070040404852074a10800c188030302da022b21004c403a0868001a141e000000b8201e040d131140380e04000c10002001d0034004140c58a41c051070041d442084c50751052500700750607909903102c4d1101d104940480e6044412504d02036001000790950051040d10580d00d01c2c0c40e80c03880408601d508540d070740d0010034113904002052103000c3e00b1140701e0509801601d0196048070320309900d401082c080000c810b01140c41c90000400c41200c49000803c1c0c0051541142401c0d0380e101000c44050360100352403041140f5550040d004504000c0d000b40042924803a440f0700b14004c1c110140440e20b144100b2514148603001d010580c055044405014564500005040c0c0e100c660f8040c204502e0f40e960307460b6021444204d24202c810880d401e0800d107070b00c0000880090b10070f003225802248850110622041081030b03a0b0300940c815a94412002c040c544403107000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 725465962 1250 725464712 725464771
    0xa0c030501180f02043201020609120c12220915050405041e03050a0305101d0603011d03070501061e030b18030d0b090a1a040c0507020603040b 63
    0x940344010080003145540c14801d802c80202503a469901518069465440c1b0391140f0001c228030500c6003448440034144803440c0d1194410980910041500341020020b143d2103100c1180c041080400c00128861003079030911901890003009a10247c84010300324410a2012090490b041d411a10315004150078910744140060030300d200e5444400a803c0c039040c0300040c14060429148045902000d21041007400340024403280700e5901d44da01c800e80f9400140986401034441303400c4170b2600d0300a0208034540036210ba90300440e01d000c450036031240e101107070041c0314070074a8442503c005000f40803062000002040a01e1081b402000025522111040782405802d11000108000d10307041001c50340c905241d5812a10814132030103d07a800e001d58500d103a0080c80081041c907150454030001d450022031403a40030201403018499030300c10032106062441d01031a518800ca503030341c1008082c14800e006a440003540034040680e2420030342481000904121008256007026600011200300341101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 725467212 1250 725465962 725465969
    0x403050d03110405010e010c0506010909022d2806052a0309221b0f112503170d0b0d0c03120c080d0f0b03010b01022508150a0c030501 59
    0x32800d0605100045032800032001b0460704101d00556800c0100b1320920015000300b04070700300000e03040b070a40706001c26040c44000c1819412103200c0810301142580f103040c01c0040d81105d1101134001d003030040d0002c0c0c0c180418082c800c003043c1d00021400c02c3e0040020603a00540c584c0c1e071500c10841100700107401c00b20140d410010b40003406032041500382010800c0205003d06a140126050040340b0001c94a160500e160301d00e248004515a80303801094600d031040561400d4031100c680d4511041c0d848441e44040c900729407640c08142045120b0320312a5028507400301103d49181c1c020700340c400d4660045080f07101200e1030246000803030b1801411400f0450f41c405803040d0400d01c2c541303642c159842c2500d8003205000000255800003600c11f0001c04040b64241b00018244c030007003025100f00c070880b00745103000741e14000c54419503a0700042c01c005c00e043c19100c092000a1410704607680c0105a0788440303450311400110f42918042c0b04080c81c41168038a508102c03018800d50100d00f81e42e020711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 725468462 1250 725467212 725467241
    0x3180102010e1f0f111303020112230621030903010e1501030b070509040608010c0311180904061821030c050d0b030a15061406040b0301181404080403050d03 69
    0x40f119a100d9005820203019166680000034500840e409131007115400a5410006d015200ca0203108560b0805520801e8105100c01002010300c02140c10100d100f807501c2028220b1041d50005200f90b860010380c10140340f08102c8004008c41c0c0b442019034a4024411031886542812101e100603540050601030300140038030803c58607441c540ba543d03c00d131000381c141c80c2008410050500c1680722401043e004040007070000030140c4103903000070200c1c1d120a0900c410180c00300005101c180d16824040c803609001c9940846c01e44592501c500100f115103401c52001941401c000207226910102088031410706c111264001d4a6003011011649402c1c0381071b01050301448403c10030703508e0b98460a4604001340885034860510f88400308803041c1138400ca81d859450301d000340f10b2821002e814620341801601d001c0d0515060844c05441400140903202e002c1070003541040901d512030701701c00c010a1012003c2e003080e00301410915280c2e881400103848510401461126162103489411110301070f01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 725469712 1250 725468462 725468503
    0x3040203060609041a070f0f02120a030c0323071409091501021e060709050402040b09091b0d06090515030c06090a0332030a140f0c03180102010e 64
    0x8804120500001510940d40300c0000350038950540e0030419014046c0c483c68644070818405c15100600481318150800c0441d0480401075034030040101c140d07540d43e2411b007030200700c2d0761003403c08a00038081c10001c0c030084001b80051344440000c80c00014018a855175980e0010404080c00e950240f03d00e0851070b8202134203c00013110852000c403201c1c07040c0014419910051004441c103198455a0500030b01c00d43c0181d410301c9103968100d083d0000808080d1025410186030142000d030501032515450b0007055910002281d50303801c40c40710703417580b048901d01517104e814240c09072008154502404d20913628200200d0220031030f2860a80d0380b001e00800400c1320710030110611105800a24107560460306c010300100c00078500c2184110005024501c103000c6d001d00c0003504030041c0c03010700c041803203810400ca4030f800c20303500032304500c43d0990a201030395840b1281418442c1c288030308440c10501e40400709019455110321b41c02c001a10400740d00a101014026901c143ca61141704424907401600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 725470962 1250 725469712 725469721
    0x60d030e1c020d060605010206060102070509040b090313090902190509160e0402181302130605090f0604060305060a08010b0f0f030a1e1a070806040207060e010f02070c0b0304020306 80
    0x1070800c10340304062041d0010040321540803c2900041c032008444181c0c403840d003070180c2d5904214551303100c4e0f024030091071104c1c81c000204491038030141001c1d05210304100003c0351520708008603024208072800c000c042070b41d9001800001c00660a040b0311a20040084a402990450003d0300383c45000b021500302d51580e084c4030180c016403240c08014054840c24298003a40d5510180000b0303141e20100042000c0c0d52000c01c5001c3d21045030351342c2814170501103101150b003031250000a40700701d0300b0403e98078841c4400140308602501c910a611000000703000c02c141e42d150300000c0c05600141c0d185440c4a4499003610300740c541880d40a5040b0304010074124030b034a07200c0c4c806814044007900b5145c24002c1c030740740d042400101c4680da40490030aa045c03030302000508106a415040c200049403464100399200820780d500240c0210711860b00400d842041c003580d9804540d840e803241008001e1080694060742c0a03401c00902030b5040404508002542685130044902c1698000c0280c0300b19500d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 725472212 1250 725470962 725470969
    0x603060109180b131e020c0d08150303030a1a030721030504090c0c050d05090d0f081c0501051507080405041113030302011425030c0210051e060d030e 66
    0x1081d0602c0c5032840c0e120800054079803941d441514002c82c458802081507071068111038514558004100f0640340b041020b041d01c54404644606e000c0c0c980d28001e074094440c42c8540000b24141105144e050000005121100080d0b0b802404060410803041d21881c00503c105a10f48040388a49260b85041c0804184101c521082e13030402c0324840d080081c2442d8407440900c007200d4200d0300301c5011030100d03144002444401c0211550f0214240b078050320701440140800c0081032020310080403200b050028400300011030307080d6860403545200f10201c81d848050100050b00c4203100e00c90141e450030659182c20041c14080b1021150014519850a0303e4001440b008000c110740080c0d501c20203000480120356078441d030800550003980046606400c001e080200300001520003403d001d01d0a60b000c000324a034200400c10701307000c0d040024500d081c184003030b81084448402034841a240500700070400f9483d0f44000840c1071008070695050741c03020113200c0a01c0c504d6030003902107550b9038526465846c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 725473462 1250 725472212 725472239
    0x2120307032d060e1603050a020c190b0c180f030a1401150f0302010c030c06060807060918020f0301120201050d020a03020d0e3909011706060603060109 67
    0x800d1460002420480049080154489040024034160b0070601c040c001da40d0500640c00580034080c802c420340e080158002018890b41d19140c0d003410b0301d03140090380d03c2040d681032300d055103420400c0e2400018008080b00c409154811304981c40c12181020400c0400c038141540c03400c490b12200880c8215507541040364014021034581c2d40f40c0310700c000060018580384144017803240003a0011400030145401e4003003101240d0401c0c80b21110110702000540c1c1e0112100381225010305005c0e6600c005403d2103000b802e116000000c01c2d21a03084009881c6038001c2d0034600b152401d40e12810700600d00e100c4a026803040262a103110301050005200d0341c801c41915400080c414103095190175940d46030f220a0343c01ca220004007190380800e102c00c100c400d034095000e034400c0c2c820140c0705d0142081c0320000440340d402142607002101d003c4600c801c0c00c1d00f0801d00c844290080c0742408a40c0e4610310400d40e040e184040041c2c0740a0100410141e040500c02d4030b010b164140c640d04907a40c1000e10040030032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 725474712 1250 725473462 725473471
    0x307020d05240703050a090201050306010c0204060b0a050a020609011406090705272e03021b010e0a210e01121503030f020d0206131202102a02030307021203 69
    0xa000b0203070150004424090994a40075118036486400e00d00444041c1c00c617100105008082d50603d00c143d40142e90140c12281c0c00a07090078281840701181c00461f00902c91908482e00d0560300042d0041d4440e009009003c1c0c0c01090fa085500035a9050412401c1e2241e00511451a0102c2c0700498198a8a02500c80d03004d42585820741c1481a910480d4880e00d1031a4810800004880035000e46401e2200050700000545041d0205824040e208035031000c2075104000d0030194041401884000e02407607000d0310929440090010025114103076465840d4080201c441810907081e0309410f254500c84014800c1c200c1c0c4a6100640042005640c09200c04051000c5160f0f602c0c1308410b080342c0323090204055030203507540c0c881c078a08218000c1e103007420f50815501550f0000e810046031041c10032240b04a203030b01c00f40200342c001040300d00341d15228a10001c00001401d0100c007111500e003a0101425080f007140c040c00f28200d80c082c0a0380c0b2440300751001001604002c8840e1a810755980045811 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 725475962 1250 725474712 725474723
    0x60f0f0e040b060d0803010f1a0a09060f211d0d0c0201030b1318050f03130b0c01020c0d0e03120403120e01020f030c1f051e0901020717030601020d08090307020d 71
    0x19403c640c5c0e540d0480f944260021646c41900910a015001c81859040550200e080a0910f0a00400e01c06003144d90207200f5501049000c41e064046603114145106004080302100c008100c82e400c81b64014005508000ca291110300c640340c01d40780d5000590700e00280303054913078620210050300118040c004284045802107801d85141032403540c0752007842d100c02e2084185010b401c4180c075204e070900f03000702071881041e071040c4041251085102d45520840c3d1007006003658918450410320b004e0701558200c0c2065000d0300a01c0804190042e80240c00d0302800c400340c4c0c203150702d0035003100c5450080f0700014200d501a900e9802c00d150040d9510444500c0500460b1039001c031b10300e1045d10319407000f00510302e150405e00c0c0c43e180d030242807203514024510790030040c083e5107850300e1507403418603030030852024820200d40404c110140a5045400080e00001c03c070341c0710f12001c0604008c5500c00d856150051103107408214102c0d1040300e006004604540107545003000d03e03005c00010300c40411382942c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 725477212 1250 725475962 725475979
    0x30605060f030a150602060402030f071a1c110406030b0301021c1d011b09050906063a06061706011b0204020903010e06010303020f060403120c110a030201060f0f0e040b06 75
    0x881c1415510440014007640d1b006004c24901441890b0a04c00042d03d801c000d83c2c0581c80520050030451a0140c401b840c00e101c40c1e494403121036500d1210a60108024126442e0184414041c03041c00d0090042d110036840920030f01051105060807072041c0003428403c4240740700350f07860408403500001308080080003203114103c0e400c0c04203400c5484101c000c5200041907000c00d20410740040301100280022184541503251441c00700b00607200304a2610721034500080703004600c0c111000d90400c4001c21000d041d6408a05980150081145000c0c0d040412551200c036011500504030541c80f40300306a540700701d210b10740d65043c2c00c080a0404101e074001c0e028030040d091503d091040d2429a001440101030329490f44c20040e06120760310700c044885070041d004010102c0d802c001700075910184014000350b107a040c02c1003100c002c003510040326000d00581e800030701816070540000040e00c007103052855078280e64110001a4003a18403a2902d0b0030340380c100080101d280080c0c0030341e2100002c1d000c680e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 725478462 1250 725477212 725477231
    0x1210501090c0e0703110408061303020a1410291903080706050103020907020a03020319031b0207080f0712140a0f0b01080106050603060105030411010905030d120c030605060f030a 79
    0x20700301e038410342049000103c0007003002015645405284170007030317042e1106880d0504040c0c2c4c032911100c1c0103024810383c0030491288001c05108204071030510303801001d010200401d0044140d100e04a40000c03080103030800e0080100d505480c450b00f907214080c40380f101e4504200106010703661040c1071100e290050700c583c0000100d030039a0020800700b803040c00c000909605502c10403440800180001085600003002000040e400208070707082040f6030000280c030011205000c4026100140c028140c400c4410241e14080d600040c10600392000b0100b41c0300341d40c0148001075500d0f2018400c01c07240f620001034510108484114041e070b80c41082060f10200d00d00c81e101c1420500384801c040f00c0780c008400040101e40002c1c440c0b40301a00080380d50324658140400024941e00014002910203140c050700b07006c030307030b80204004401000c001d42aa0394690120b0310141100241800303084545081c561400b12142c0f0920480054820003000107041c034034503441c102d03102d81000f00321100340c503582da8883e03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 725479712 1250 725478462 725478473
    0x4060f350615040e010b07060209060a0203090a0e1e0901020426060f0402180601030912050403060b15071704050d0606051c020306060402070f020603100302180121050109 75
    0x3100418011401521541051000d0246200c0001080c1003420400d01042c84020314554055044540c02d4405a4860729141404030091194140140d0301040000790100d980b41c01001030714090358119100385040e9690002588000700841c1d0000070103c140c0240304440100d0f1440b44d4200383d01d44001405d0035264000215405500801d4228208024010f1b1008110410485600c001e82d00c00720036181c02c00750302240303403140c0540c08206540008800606241d100368043d48425801103455108402c007400d018009901a01042c0c40543c10a00c1c00146400d2055491485000601101c0c1c81d111040c6ca464070003d8061030002d0882104010019460343c554004950460180a00148041c90309040010100c0321104907a2044820140900566000316080c0d6001d402030b24056a1080189800d002c04400200c0095002101000740400c07101c41480000c10b0720b10980c1c000d104081c03c0134445108020903c40c0081c1e5182d0445120000744e08900140b40aa204500215080000356200c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 725480962 1250 725479712 725479787
    0x3010606020304052e05220e100609081c0c0c03030815040b01090506220b03010503010e03070f0f080d090506100906080307021e06040e0702060c04060f 67
    0x40c500592012070240010300d05820300c80c0c9004034045038131403030210b10403030750312080c941c2c850403410702401140614580b16440d51503032a070310186040b501501d4031008401e0314010251190b00ea490395403c1c021451a004608040c16103054070010b1980c80b0300200c64402c0d00d2402c1c84045c00700103040080c0740009400010301e1018500c692501c1a0300c2ca40103040c42c4106c10803105480c032460800c208903c8590b08103074107005446084e103c541c5d40d0090145103c1d600d011078500c2c10b0720403d00910020705d04c4000e401075410f0703070310450003841502c081d443c002d03903203014801c0040c01204402d05401c0000350400500340265100c0d017491410200d103030007010112189028140c80f203401c4001007000082005c1c900030050305400808212840c01c10003103960300d000f6401c000f8050040341c9070130003840d00002e00d40200c81e08010140b40e034440d19403a10001107401034030480d0151090301c0c0800c0344180c02c203040d107064407850b98441c0e40207003d008081701d11a00b4282443c59000340740c010740d10384150b4031a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 725482212 1250 725480962 725480969
    0x1d042a0308120f01030320070f03030c0506060109180b011b030503040605060111030403080f2a070518070e130203070903020a050a0e01060503180a2009090303011a09030106 76
    0xa007629042c103603291150100000f0b01000724542c00c3d9005000003900180341c0314000203681e20300b550802d030425810303181068580003241254941c0000004143d13201028001c400c1c82542a696103480308001541c030380d241c2c2d001e0f8000c14595030f1200000c40e00741d584440106401450145140400c0503007200e07a804c800c410660008000104000a21005004407034014000386880c2c00298004c1c0c8215803680101d000007814040c1c002940c99080641c0700a0b03410000c801c11500328840a49800c544401d104045881014060b000000a540c0b40149d203d00000706041c11607169aa40c2079007c5410000c840c07103181d400700803003902040d150150310103140304070201cde1111600a03085004203c0c16a081c2d51005200341d61002d42880b9505c5031145060440d04c80b81042c546940742c4072407051703081540400c4000c3c540302d80071101003030220301c07402c01d8408605542320b201c4180d114028008607000440345400305074020401044905120074509841040078000c071420104c15400203825076880d84e1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 725483462 1250 725482212 725482223
    0x90321071b08040e131e02061b01110a02010219080105060d0902030307060f0b0f220903050c030706060501030e0f0c010819050a05060f1c0b0604020415090305071d042a03 75
    0x9460082080004800c9000a03520b4019180700646e0781c0050401c2c0718514031161007220200580400d00002d411111145a4403c0c14139180ca00f501c1c0000d000750429040035030760302440201c24071820700440c1c425042e0303100905410328007154144940301501c128902240c1510040002502184262280d03010398103170301402082040700c03442007080517001071003818441c40d9424403140c103501181c510082c00c00701c082408101110355050558950152240c6031105010024103081040a954011030079514240c9003017008240d40c0c0a89507030351205801d40f80c0641d0101a841c00390358022160360360311101c40503032580074000071031207070058800946484c496252500188046854250b482031007200d010f840c50461182c40b28008600c5410012014008588100204645071181d804981c003070074440c4e40c0c5601c045c1c00b030301e001810359125110956a5010740c40d0040703041c014032030207000388254015241605889680341d4103100740403880000344801500c690140541d400303150702d100950068 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 725484712 1250 725483462 725483491
    0x711030607090f05100512040201090503030c0d080f010e18070504020f0d060501051606020702040906140601090b040602031e0702040912081312030507020106030b090321071b08040e 80
    0x48180752074903405412003171003104403141489180f81d0040699140000403800500745884900050310151200d42000c1c0e0103020002c1c4001000000213420b06441c142a511098a40e40300720f20300c0c0d000d00c002c0c064080321091010100301710301d5500c40e803101400703088410391f82d20760b80c0c3d03000050490f07100d42031016181901080031070b0340c04003601c40d0340f004103002e08100c0d00d41440e9004407140181c41d410b00a2502e0390114010b01503454940c02006041e50040c410004a200c400003114162001c0b02d1a034001801e840000c12200e808000759400c81d41c00750000e50500c0499010140c50307030800307641561103610502c0200c0140e5100d0040051441c0190985480c000030010001c0020358010b1200d0000304410068200080300c900840e891800e83d40b4000036591101d803400c1740980b019901c081d01d02e500c0c181c00e00240c12030100080412000808241e144e22803024545441e048040360500c010504132440f007611240c2c45010150f005100e007007034030b24080d1125000c01c03401034141ea024a442048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 725485962 1250 725484712 725484719
    0xc0e09120711041b09090e0724170a06241224030c051002030c06060108060d05010c02030a1808282a06020c090105120118060c020c0a06090902071103060709 69
    0x1d841f4240300c004150025246007402e080540d1030081c000c08260b454800c03414102c1c0c0360b8610a139503003080058140800083d9041800049000d81094040c90b04214a41d000c1c3c00340580072207800c44013402284d03c0b100c417402c0c0a110b19000a01082429801d100205e080c103001c607820183d0300e2400765202c2c0030500800b5080c403061040440900b5586419544100000e51001d0000680310358010000d01e41452a580d4040c040b6101e2503154400404942c2440e012021854000c805080c07a10b18507902c00c410200c04c0c5401940410440c410340d00716402c20200e00600810301c1d0b00801818010b02c01c4030b01c1410700c0e03580d40000c0b29030000480e501d501c0d0011451002c20304008940c0d00505840c40200740101034080000e248a0046c4200307881a48000980210181c080d00007645420800306c004010a009050401c0607001903801d000c0140156608913034140707084010300c03069411668442e9145401e0041200081d40414000c0d2251321407203031741c42c104d0390703040200368400d508542d9150741d610314 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 725487212 1250 725485962 725485979
    0xa0209041b17070c1203021909030611070830100e0109020711040e011d0106050a08010507050a0f021912031103090d21090c0e09120711041b09 63
    0xb102c41101d40c1c0c101606051000040d030001c0c09101e11508207103903410b4040024002c0e8020701c00e9014510910041c0c032450450250040000f000b1a40103e00612a2030f01042000c1c000e48504c1400502c400c1d81805407910b0710107410f2400d21040001002003a0441403000c8808550500b00c3d100c55004040791030a00248168a59050040010301c0f020f505100c50b0b56a440380c04002a5402401070759074846145103107400350040b180074290020100c0f00351800025050103807115000f01402607040b0031000071109014070855100389250b0340d0b090701b0308504544c104c80030000f0440400452080c10003a1108411104110003041c0c481e201c0c00780071070317007882021b030548007104c0784d05500603800c3c401c00c1003210021801900401d441c1c40c1c020204a10300f80d50307044621101c141c0c81c19030f52600360382c0402c100c2c503401400e05590061111007030a83c0c0c0c1c400030f245d4400c8000b016124044080c4203901c000707100c5045007415500006d00125429020001c01c0c540c0d05801d0110500040e40c0542c1044940c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 725488462 1250 725487212 725487227
    0x90307050f0c0d03030b240405041107020a06270f081c080c0d15080a0309171218030d050901031514010c08040e151c0f08030a0209041b 60
    0x201c2101600310003045600060380010750070005414552106001c9030705079541e04007541786100c9080244000f015201400310250402c1c0200c5010740d01d004284480d0840c514291030100740d0060010101500f08081141d0f8040c0c0b41103028040814880a004c01c0c01c0e552103148080c03c6200d210390720b0540350000c981d244c00001911106484420040c603c5091b50003100d5907800300c0307038031982c0b90344034411440000205a01d00344110f40000d5110081000c036004100b03050558003035034500c03060f0313a1100c0e24070b5072811a80da8117016603402072088024818102e8003500388008444900c0d08141044030200f810700c00c1410510000070800a0081c01540e0140314002e4070308485c2e044520b81c0c03410502e9800d103504200c002d00b410b00428904240030800c1000858001e01300b036080b508002d04014034644400c3c800b0036050b62141540b0401d112030000982d95500209812064060020100d80c440750641c0d40702070700ca15000f503001c210380c1030f05072140d004500042d072040906044101058100800c0c52 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 725489712 1250 725488462 725488483
    0x90c02121606050114211005010e041b081b0409060e010510090b0906090c461b0c12030e041b0c030e0406030b16080601030e030a08100b0309030705 65
    0x1009803960205c201d4440241001200d1001035090380c0202c0b48070030292501a00e07c4102604d40d05020010654240000c0503134010351050041d44444404d06032110507440107800340b015035034081c1400030f03218000c1030902e120949014200140d10780498840b1029910b6004c1c0b41c40c3d03035079160030612001c0901014040014000c2039010458181140005146050701a1260b4440d0700c81c140400c02181c00c0c0e20845819001141d190000320210400e43c03a5103901b4011801d0b0003070b0038030f15210300d141038590301a107404060380e0303a0121070104900502d0300c080791100c007a5880604a08041000c4110709645a009402503c501c955541113070b08200a8a15280c00c818204050220450840b41c000082601c21a40360803d416952100d07400b0078014009940050300d125401b400340062448195500c00c1030100a9840314505e648140c010360558030380c2241055198000c001d0341170858031501000750446650301c0c034030927400e6546900c50400e40080d60070300501c0d00001480c508103c01044692030b01e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 725490962 1250 725489712 725489729
    0x3050318030406140706060b03040507030b0c070b01031e060c120612030804021302190815011107061404050901080c09100b120c12090c032104090c021216060501 71
    0x1401c1c2005402050030100750583c0001410109517039040004d00d41140c406000800940d03916442e06d070401568400309813000381d580d400b112010402002c113050841d2211900034004010603448d5a48883e1840d4480c00810480b8403504244030004079140104809194255134052a4207154903000c021582c00d9407210051140d000448000240c0010f501507006404a03030060311300c1080012040607200e450103d0340c1c2000c031039a1800c0010380200501c0c2c0140b04204a001c0d104018030300559003007051a01ca00a1130b0700c171800c00c00000d4400d5003103a51000c0300719445420143d41d6008982c4949080e04802c80c00d4000d030b2401101030414829a60b804a044c00d00d200b06285030106001440c41030380380081009114000141030069001d044452501c00228100001d1424209454540245106a0f403180c0200d8001142c150f100458144007000000d132007500e050f01c0c2025a03c014030341c4112807025800354449034241c03c1d200f00060510b161041c0d4800074407584d03500d003030002c440c0140c200404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 725492212 1250 725490962 725490967
    0xd090321091709060c030c06010611061b090d050a0b16090e060103020d020c1f0c02120f090103140a0509060115121e020f070203120703170403050d05040305031803 72
    0xc24400800d00c2c08400d280010556209070060100e012440743c10b480c2e88041c0710002d02503001c140e00189140c100c82e0503503184034009442c0540280c441405031080b521503652810800281003003680107240c043c000500300300d004003455031414244011400f05582800e524000c1086148503000d044400711150f113011071103241442643d422044002d4852810142d0204141500104070f504844030007500c43c04844da400f07500351a0302c0c9000c00d803140b541d418600f003500340c40c04680001a41d083d803041500e042030501550051040640e00480841410940c440e81c2c010181d00070900f0342c5d401454910f40110f4946451014286080c2069101d410441101a0030203002c0c0d40c085801403281c950140e0100d0461480c001306a1028049160075010310b20010741d0100c1c4081d003400800072a442038042e140c080081c0c240c2146c0d6401012806800308511090240d03a5440c0301c0f9400780e1151003800d1050400c404090346e03d0840d40e08640480c0400c00c00018000c4146c075210000015401040c011031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 725493462 1250 725492212 725492231
    0xa050a02271513111c110403062a0c030305060901060e0d2105090f030a0b01150504080102070b010314061b160203010e0d1404050f060c01020d090321 66
    0x1889601c0c0100b00c0c01d1096100c4100c1d0501c0c1d81d990203515100011035000384007000d19240c503203c1650107002c640c0c0c3c0e0000b4080714807948210b50b00410f000b43c1e5500041c28102881e686a00007c0d00c5c0320032907155210446c1c07020b4086400c103e410754050180c43d0340c80e00b110980524000c0c04030b0b40b000d007074140705da480680100152a0b0084407140d51802c1586d12242d0301409143c400500b0000c41945034504245801c640341c0558010050301c44c6240490b0034002410b68401410b8941c516a24040c1c866424100140500300340e00c141e9141005040c076185240035624200c00742260004031084660f41031041c0104188200d5a0046401074000005044e01d42020f1414a005050080c0c6800f0030601c04100200050845003100c00074540190003880b0041d107218031540c50709840c903030410200d00c0c1c210340d039241c2440c42d0041e101075031005849181950214400c004507138000c441c10001c0d42d07400b0400b00704508080c3c020504d550b48a070300d610751a1105a40c140d25559000c4110706034941c030344550302c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 725494712 1250 725493462 725493529
    0x106170903041a090a1401030c090e0402040902030a0f060203010e070518130b120721030e240705100f020f041719030f0f05040e0f06120a050a02 64
    0xe03400c8442c4054070f000c00e4000f020001c0e165015035030010760b002c810410005480c07090a00035040841c2c00f60f900704540c1091500a841e24a954054108041c0a030800140103041c0b81d4407100321140003c0480c1c0615203030f595917038010440d292007102c4054011004201903802c041038580c0189080c00d06c40e0420711885c00d02024041c0940500d0302c60440301628680c0c410150340101d08800300070f0455240c200306419030710b81da209a0700c16021190b5044102d510040142c2d061150744a82c19958542064034070000c01c20740d140b50f41441484480c0ca01203c3c104408440010040240700b540136101130341402000000b10b918914144d0b03c458010800c494542558030b00701c4007960320a4580201980c4e4540015180000c101701c0300003901e031a0407020082c141c0061b011440300c51036540b485d407243c43da0380d030072501400340f13126003121411101c0126049018405045600c902c0250902c40b201001100162600000d04019502034200302d0801041d4240450700704801440c0d8076000301455a1031b10341 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 725495962 1250 725494712 725494717
    0x23120606490501290d0204080303060307051002060f070302131706010501030605060405040513020405091522060203091c05040501090b070809130906020a0f110d0e04150e040602030106170903 84
    0x8901368000c16080c07030010724102040d500100c42c50413086494a88030f02000b580c0f42d00984240707110f1300c607500e00014280b41c0108000451385d040e5010b443c1641703400a9092042101030701180903da0203106443c640281c8103800d0b0020840baa040081800c42d9944550500380d06800c0340303040501700704040c41640c8583e0b044a0031640c01340c50020f05903640b040c0309102c000782110000c0d0310034104024030100c1200001c0003001000900c542c0091ba48985034400000a5021120a5080802030141c1c0200c1e035154043c43d40310203040192021149003506400396901030020b554040f5201180902c1103507884000d12014005509641e0310f020344d941c42e01c078554040c9044491045106085480584000b40c114a8490380e2102040d500e8010006010707000c10b0105a102d80001c0116080803242d0740c0002d8503180d85105921051030074600c180910010313064030442c000f00416004400919180090b500c540b00300d020310300058076541000c40043c110f070000550020b2218001040c4a5160b201004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 725497212 1250 725495962 725495999
    0x3060b0f0a11070e10170a0b0402190308040906050607020d0b04020a1d0610050702010c0b09033105060f0a051806070323120606490501 60
    0x4561a8558101c1c11100c41619006112150280190018010200c83d80b21401003d034842c80004040d00c861200d07541c030626800340c0301c030755019004d80c0b404076056515064005001a080c0c01c045c04400304641012200c0303038400c940d001c1c000181004030700b0039881080c1c0508800c81c2c80f64600112600042c0351007001d21805048140c4840c041011940d800142800070100c0f105401c0ea00405c81c2000d10948800b02c48440c018040c0000d2990842d102d2811100d000d58161211000390900c1c1d110841d1107540100004458442041500a45000a102d0110404c41000e200f411014040591442d480540d400107009090601400080c1010301050b1400100589800c035214003c00444c070881c03001e00c1c0714640d08040002a44424168031100d0407a051885058115205583c040207071500c0c03007a18880400b070340f500800f1440501d420320041c5545184c801e1941e000c02c20f84590030301924082c481c002c414003c01c00030b02000da0030004580455141d54141001590f25201601414010808 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 725498462 1250 725497212 725497237
    0x91404061803080a05150a090605010201061208190509030102161109060102030a0f0c0c1815081f090804060804050c030a0809040b04061806090b04021806030702012007060c03060b 79
    0x80004011182c02906c500501400a15085100e03559a610a00500703107030003131394015402c2000c0072501c40d803084803803a441948894681e10b010300a00c0c0e02c26585034002d83d0a010000204100c030b04954090000d4010504000310a40303080c1100e19041480302805480e80740030341800820407046a03000320a503030386803c072810500700c0008064811100c000c0001001170110403107107070214070070003111f55039609034144079800c10404840c28840c10b12400140705040b80c650080b401095038802040d100c0646424440c404281c032142d6950f41840e60300150808000544c8042c100014042c0421038100032400070307005061594000c1c0c44580c12441402e00c114000c030303114212211a44c0f665800354000b0070070881e0341038224440944001c003401d8184190203c1c0e50428030021450b245c00d1007107820188070421484500042c10007408281d1b08000c3c140e60940d503880b80980c0c60118071400700740d1440f82e0100c00b0b0f69500c0d00b5240c100c08803100700140c1c0d030400d4540342050092a00b400304580000c00c502 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 725499712 1250 725498462 725498471
    0x30a0308130302071d0a14060a090e030d050108030a0206070f0f08061c03030b1003060e0402040c1e0e090c030f2a180114070c03020d0c091404061803080a 68
    0x3410140e1030b0134155440400005440780502c8640490071034001e0040440306000e1012002070000001001000d41d45d842e0300400d180c40c01c0040310003542c48442c1414031201903d0800600603600002ca9500340c0c0209016000010841441760b0f051010940c08042c501b003e03d90300054000003048603018000310802c6c03146080110b0b20503541d54400801503444000318114034105803030001c3c040e00302240060b01403800307101c0c071000c2c07180a8040c01c02550928002c00d0069030b51602000007900d20002c8410600040240e90002007800c07180c48403440100740c651104900c42d10381070080001c070080c088420f81c40c080c8240104445c08001c00303900700b040e403104000e24048600c1d0385030a00c0000d03e1403400d0020002090600000350500ca85040007090f211524038140411244849206000c0c0051541e80401c0c82800103107490b089502d2014000e06410b440303a41c44107406401c0300c0d00400c802d4001d6403204208000c1143d24028108012103800324110949955500581806401b400740e803545e0303485 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 725500962 1250 725499712 725499751
    0x172d04050d111501181b020c0301050c0c150a060b04060806011b080703030507021f14010801020a140d0f0507020a0b18070506030c0d1e050f51030c030a0308 69
    0x40e0300300700310040c50305a00302c00f640c6e01d02d04040e40d143c2030110f80c14001d508200001c5c3c1400a014250748802210300080c0400410401c05a80b40d11030051603852800c0d41d0b51008103070320b45440060b0001d0a400c1d2608241400c210001408d0741d034001c2c104070310703025002e0600d40001d01010240c85040750b16040101d6a80c0710a5004d90030b0660020700f80e000d201031098000800d440b5508002605030308180d183c04070380d0304c0c0c1c6880c40c03d0344504215140800e0540d0101711440c1e070316000602742083c0318000054110b4000c1c20345410b5840030345000d00160720034910081440000d2510300d8101c0303080140ca480c40c5910003c05e9480b11007601c10980f103220007000080c000350f40f60003190300003a0040010000e054400300100310307100c0360740380303180c01c5900c0e200004d100c0451100c4030074040c41100c064501c1844040600d0324202135850052401070354101222501d09075040f42d03400707942c43c034050f046160780f0b100014140350000b0300c2c04d1070303100707902c648410700c007003900710401981008840b100d80304101c45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 725502212 1250 725500962 725501009
    0x909060102010603080c01020d0e121e0c340315020a0c0606060f0f0512060603060409061b111506040e0a120302030412172d04050d111501 61
    0x149030b400038002640002d4046c014040c1035004208010001608011845140441a40d0740119482c2081e1226042011380412192000c40c0b1501ca00c002e920245804070350142c3c0d07820000c40ba40d0001c4420001c1074003040144150320304203604560940410760013451a00c0b905140342400115040183d400240c1448583c440c0d4000c0f0b4419400c0801401125520003006040041140e0f04070005511507000c004014880d000300e840d14280011840301c20345071401006200c1e03201424250b0700035aa04a0f06000840901800001952103d07102101c4110040040e0208400340240c290f02d030440d200c0b4a10350040030b00c50541000e01a0307000034175a143c054242c0d2a01c8118003002c0c19070011404040606641500150b01c01c40c440c1103030540148c244d000580700e0b040300c01032103000d550381800012039454200d9118280e9140348004804031006003031040740395030000c1d02d081c0c5442d000f40f10210301043d008915608c6000c07001d0002d00319080e001749d042c1d40030407041c01010504444504402035184 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 725503462 1250 725502212 725502221
    0x170c01020706110a0e010504080d05031e04030c0201020d02012306150c0c0f06040e07080c16030203031608011203030903091d10050405060607030c06090b0403180812090906010201 79
    0x254440410080b011882419000311380000002000068441c000c8030110352144d8103840440b96028001c00c0e0303551000da0241c8003504000d00314841a54507010b07040a240c0c818954502030340c00303502c803500c0381c0c02240002401c2c5071490015100756810030030183d41e4003000413024078801d4a4102094034940f1500c002503400c20b07901615249601012400c0b0680c00d20110f4803041059044481e0800800c2c60014000c03180034522900e081180780c140010f94450040d07210703e40c420395040d640c07841d00889411a48141c1c00040c416801a440407041080c1c001e1400700c03807010f406160510403599850078159270803114100200408168441d11803000f090b004582080141182c0d00e050752454080f0702940c070f0310b0340049907100c00c02001804001560308103845924007030840a41034070300d05101501d040c0c80bc0d14045034102e910f903a13101000710105080e004914052032080e5585003c030342880466141600c1c0079080342400350400015804808402400c44507000026034001410740d94210041c6e0040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 725504712 1250 725503462 725503477
    0xa03030819050f0f090a021c17040b0408060c12010b0c1216050c1f0c0f020402070f0b01060206061809010b03010504050106081212010504020c0f120307030b030a170c0102 75
    0x1a081106104915001c80312482c46a1000e440d1800c0581e543c220281c6c0d9042c2440700a900100300a88100103d40340f00c28000b007a03401040040607107114001001002c2c0c0c03013644982d00705000820248184039041c09003581082140c00c505060080d641c0c20b620b141c00e0103220712400240005031034581d05ea0148080ea9201b598000e03000e0712a00349980c00300c1070740b50b0039400f1a1039025046030301800746400000001005006c0582c0d0000f213001c88405d417944103006c802542c80d9405140e10b20010390342ca000030500350344a1005514500700300c0c03811003155901a0003080039508801d00300107441e100d40000d11400b91008100c0c08003900d91140e003900600407441e1030794265080c2010030082c0a0150401400c0f1010101203510148078485d481289004104684a806080c0d0300100600d1a050300038129244001054039954030040103a075213042820b800e502e5813510040100841190540300301e6400c3e600503000740c00d034030300c0c40ea03644070035000c004c0b2000103401c07008103400c172101301c00f581628441d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 725505962 1250 725504712 725504761
    0x405010f0c0803100513050411010e0406030203070b0a080c040e0a0207030905030604120906030204180249060302011b030306080f03030f06040603030c120e27010608060a030308 78
    0x781c1c200042d078265240d90174001da6011b08079101402e03814004610900f07219903048060320305c40e032241100440e40440c50000c0f00b5032064032641d006c80941d9050180c0b030010024100c180da500c010300c0741d004e84100c4006020b4080c0103014842002a04000300300b85610a407003c0e4011380d280c43c0c03403809540d4800950080c541502c41c804c2040f040000d480301c040030b03411058541c00d004c107584076811000c0e03100714000c10844140701c2d00ba02c81b005040d03802820542c0d01310101c04500e000115000e421000a11400d04650b51a030490f0044444204041d411f400701c0e800000d10100b415900045c0c80b0ba180c000f0b0030311240303419070425400d15110b640050b0181000509640c1e00c45600807265540e50400d40313049022410400c0030610b00d1619100d05800ca0345d050f2140303105808191190416a1101034a590603c00041645070f210358400040030a102200ea41051403940f0600910b084004140c00c4582441880003d00c0306035550003403c10304407641032611600075030304d2819559403000c142c58040c64 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 725507212 1250 725505962 725505967
    0x20409060e0a020f09061e03030c03131706130803040c030222050a090b0403110312270706050d110f031e071418040216030305010f06030905030405010f0c08 69
    0x101c00c408a0201d851900865400c484035111000f0042296802d44410f40d0002c4c543e4641c00e03d100d100b10030001c0c150801415241000103011001d03085900c10140b8641c1005961418040384150611000446070a8001008545090120144110b15180000e030288001000140c200803034a01300c00301450b4044c0204482d1010b120700380d0030458000c42c1402005040200055042501c0d11600c514150807050013117140c1c980e07403400d0315a60210080502d07540400c003c54805642c00f24502c90007514205642c002e0000d007038000c40d125040002008005411002003048600d51140a90b00b10f40020800080c50305026070081c8800d10884e036000e4941180841040f030002400314007d0300000b85004040300c0da95603071000b00c4041d184029044100d5005120000c0803489a13605002c1c0d400000c0e000600c0c10769080000ea0640c416980e085001036140c02c01404107900c0802d000c0003c0240307040502c080c6c5600c0e0b441503202e02643c014a0b04000071046240907003481080c144140a80101c403103070303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 725508462 1250 725507212 725507231
    0x1110d0908070c0e010f0905100512191a010b16060c09090603062307082403190303060602010e15060402121503010b1005180303040807090b10090303080c030402040906 74
    0x1241c0c54003441303940c05410306d520000461644034042c1c030344100007241031a0721103404e01c82000121a040122106a0702c07810401e8200314428003002d06003076008407800082000701e01d25151071144140c00c001c485540070721941581807a500c1c14043d40c1680498040307001c021800044514640c545d02c2808043d051410000500406030310569103020b00f00034680015079038004d11303a03912034141c40c4500014803071305c001640440c7e60800c07000f20410503c06103800340750107400645000c6042d8540840002d10a25150405806109038030003881c2c2c03400244a41c054105140b41c070703840712810001030000c001700007034003c0d6920360448480070111028166241000920300c00103112240215001c1d40c40d00b2201080c41c50514a8011300703464551300c9502d80140500c1018030f0861000310b05406110a01c03022a10300402e02050700502400d040000742c00c446082000000b05d80311500000380b02e41c91400b40007213a8403070500b0780e024200c901819500e458500c0400e00602c503440020785550b10b00300115 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 725509712 1250 725508462 725508479
    0x201030f1e06120f080304170d0f0c030e2e0507052515020a0c060e0a0201090e01030b0f07050910050c2a01030f0908070605061201110d0908070c 64
    0x104074410110008218564550b0120b070b0103074442d2035020f0002000340808000042540300119400303842565410882e0303000403040f035103079040100c1c8040d446880d5942401c0b0b4030918403400056906502d028400003000ca01655200c0410000c0a80350401c45c1502c41205401c587e00c1811043d50f0000c100014503224500500e242c01c1902d02c44030702d11910201c0451a001c001c1c840643c1504010b020201c042c06a41d801c00030740c040c40c2260103011f10100c20741d0108116105d40e100001d0104040d0414001c50b2000412282e91900145040c17242000180042020030300c40d5607110048207900300003601c3d60030003901d8078000d0980341580580d154042d1800e65a01c000a0a604010103088030015004030142e41044e50b000410010f041010980f0012150311903048448198580440010710794000e4840515070b030b01500d02560a01c1c0c440d42071104c036045c031b0314000483c418090000c2004401c01001400b1782e01c01e41d9410b0102c41c0c0c072040c4550901032014100d60440b42c1c01200306541c2d40c0d484414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 725510962 1250 725509712 725509751
    0x3020c0307030b250e0402070515010902130803043507060c0605010801200a0912080403030e060c03030114220510060903050703121b0303060509070c030c030c0201030f 74
    0xf05452500304d02481480090b034290f0240c0c0c1303050350352600d010b006070b42030521000b500000f00559440c411803107001503020040c0c4c041e6020b803000c62030151b542d0354000c0501603a00c0c0d080d401041c499000b04020410f401c0c05130050425421202c500081000c0c84200d091700c40d80c00c1030b420201c0342c000c01c03000103003054002440c00d003d01d100f40b41c107102581c7d0b07070452142280e20540742540385030000f520744450b0541c3c403802420200b0040c00c0c00c400c02522562980c88018a8020803148100009410b00c103054122200204491044401d5403503c0c1015240d41e450740070600c01c0c3c1d112192410b168032115601d411103003051500c814041d43d101d480403500c44000d0300c410703140e050040e02c00034000308540d445841e00001396038001d00100fa200d07195640e45141800d10310782d844104000d0440c50300003000b0000521028a000e6034010450f141000c04201d050f0303001411210511140c004c1c0c040c0000d4100c000c1c41c0e41b55030103050030400401e9038001600600301802407100300c10701e401500c0180c00348201c1c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 725512212 1250 725510962 725510971
    0x120a2001060518070906030b010516080d06090f060819110a0b07051c11070e0a0e0a0f030f03060510050c0f06010906080c030102030903031906050409150f05070504060c03020c0307030b 81
    0x3100c5174540da884070103404480c0415030740c41c002401001060b034024010440d41c0d140603c0384005501d410032110f0341c4070480d141d540100401503218a11180c0151050103080080e02031100079040048007404081e040d610f074004000c105040003c00d2403441d503615800306006011a0011a603540c4181c681240c488083c2d50108a00d402c001b4032401c3e11503c2504c2001c0d01d1700b4510010700b0a541080001c02c0203c1004100c4501c13180c1f41c0c400301c81c213848144001b0117202d04c200d501c0200ea4090340b0b40540000c0242000c5000c0515000081000d0398813054080810022030601540d103103840e400041c1000310400505d045c51080b0000012030034020361100e0219644141956041b20011080509034803080d40c40e503a0550046c0007141c40b210b501c214a0f001441c0844c00007801d44e42c0e0f800400d056030145d1009803882c220300043e54106032140d00a2805480b03400c0801c0002e0315001101a003580900d0052000300725070b1050400c1090b0007081502205e90005084680c082d580380340807017441c0d400f280c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 725513462 1250 725512212 725512217
    0x10050706062408071b0c0b0c0f060109050702070605071e2319021c0c08030d0c030b180a0902030709051611071221080702120a200106051807 62
    0x8a5071242c85042d00130b00034060b681e513010f990551150700101c0b8001c03010040c0c500342c0f4400d01c00110181044d00038011041c550001c0c0c030400f042e600c081c07400e00c80142d100905c61402c00040101450b4040b0b006400d071400d6040c41c90320b40086040042c0b0b480c910348020000c003032407250f4003070900920107c04a81c040c2c0300b99014248040c0010140c3e1500901024280c1d46900b0b003a07004018600201526122006030b188841c8030b0170719484004034007489900c084840e42000414060540b01c500500c420440513090078403000241d10040703850440030030041101c2241000110b42c1c00416070300003441c81c5070014100d910030360703c0b22924070040c001510038000c0d07540c01440340c9070114095012002124103490240216914008140e03c142e80702d44001c03030b01c000c0c03140c40c02e5821019190781d100d03c014103640d440c6510328119101a1800c0c1e0452550003004a040c02035104295111f03172490f006921514020104001c100a0f040c00b4020305d80059600507103161150034050806030071f542c401c0c025503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 725514712 1250 725513462 725513519
    0x40b1b0f0a03150b1602061b160608060a050904030f03021e03010519030c0b030705090d060b0a0b030c0d1508060103050a0b22140a02100c1403090306061005070606 72
    0x1c40c40b0300d084c1e00ca4122030010f0318040020080140c9001d4000e485c520000018048250620061040c05c0c5007842c1400e40004203614800d1243c640e010304c1969120f04160340e4000190300305000100c900c00020802002c2055802c8280089442034041d12010880c040c8140d4640d07a920030405510f410034040c0c04e019070500400170000003d85e42000c07080b2a0044044a002c1d0f0074080e14005d958401030000041c88002c002c0e000480c0c0b0341c0b808000041c2e0140a00150314500c0d04200504c2a07280d0703202426001041c424407c820702c840c01207404c4d4041c00c2c80c0000300c6039000213000815055640c480c4419029140c0000180040070801340d8045103d02c2d100d14950f91040b000c4651410002c00301d010101d01003c9540005940440600030042004225400d18805a0000300c00d00b441c5601d88000030001000c0790104491014040c47d0704a00601031400d090904d00480c0d82c800e0000c3c02944940c0342600c800d1001c500079030881d01d0b40743c0c200106104242d00c514144824205141581e058043d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 725515962 1250 725514712 725514719
    0x3050f0738090d050f0c01090b0f220308150117010825030f0201030c0e030a03050408240606031b04060504030309080d02070608090313080123040b1b0f0a0315 70
    0x704040c143e1482c07545881d400c000048102c80c900b6045000c08064641d40c80c10410045640600820310495900b035400b04980f8140841018031108800800c241e002d04a0000c40001e03049411580d21441c02051100405000350048030503090303815180440740c1d221000441d140d200442c8000c800100040032400364144604a1a500c030060701c0040e141040340070180c40150320a41000c0c2d09440c480c5070610000007000c000034208a5041000c03004941d0000301005240c02c180700f401405a2404038105000c901c1d44130040207c58000c1590344129400000200d801615815841c0455030080d42d0907103907500c1c0c400240169100e40819000706040304000180f800b80000d50318206080c0368090200a464084182c0d42c20f0780180414a1a000a1140380d0300c0b030f071090981c0700051104500200700c1d10003c2066240c1155102c0d401c5400f01c208408110114001c00081074010400d01c02c56945001c0c0740000750340c1d07805a0303807020903108000100000301c1685500007030090801000f20220883c0e5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 725517212 1250 725515962 725515981
    0xb090f0426071a060a0b07060b01260105030c0406030213090303090f0c0f090603051507050d020706022203030504120f0215130b040501022e02030c07140a03050f0738 73
    0x1c640f003440208541000ba0000248c0c3c190441c1428503c10704120841403840403030410990000b030201d001a40c0303443d004200d41c2c41c04208444000707809840810880b811034001c14103a0046801e541c1c582601c0d10402c00805d8480d612040c2035a401005450710081d107807809110f004403510031181800d40c03d9001059070110781c480c000440307601c0801410001503e50041c92440d00003010070040c00418040840721030b407240000d009491156200580d0348220014404449840c10304950300c041c0840d00610020740c22800f224103030f03502060401802d6009140030b079130f5104005402134010003140c050041e00804540606081e240d10305e80b10400c42d455995176034035802148a81c500503404901d0348640514a039811911455020304000b01c400c10746860301c1d0030b0340d10a450f1044d0700140000d045046c41428000080ca003610310004d40000c140c185c90042071400340140c80c01c10f520700003518000300050b6103090303140541461048036415007024501c1040a600765080c6640030f101c40005640580c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 725518462 1250 725517212 725517229
    0x305091203070f020c0901060306052818020903010c050301050405090a02031c03110301060908150106080a021c36172a030a030b090f0426071a06 64
    0x680036020504540d103191048500c03062980e0300409502451106040c036465072000302c0e020301140d842c0401d0803840d2505016413103012000f1240b051140700c1600c00e150941040c0da8003221100f0b03805101d031100550001000f4441e600354280c1c958605480c0300c11007034205001d10304071344c07040300e0402c8503645189e042d0ba11131010b00002549a001030685112000c0c040a0419030000b040c60002804118000d004c00d20754801e80110300402c614480c00c00c021441080701e514540c40126181c3c0417545003103805001d400340540318003504d5402103003450500f104071f4021007505011100610140710301c17412180500350454103440c041110320710080c0e960322400c42d00300d507003680c0400328801440790428848500e40000090904092500d90107804c051180e41c00c610801c0c02c00780240d5904d41c03030030380040d088650a8403c40e018491010411141030b280e44410360340681c1040500c8404e030000260004a466480303080b40403032801013015014098603184807076040c00d0902c910358864990300100000c61 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 725519712 1250 725518462 725518483
    0x20903070927200d03050d0c1103210603030a080a091103120408010f0e03071101020f03070b060f0d02060a030c0e10030c320304080403021f030509 65
    0x6601034001002016032a0340120100341050310107003441c0004182c04080e10350344034425104030004842ca0040341083c2ca402c540c0407442110007032958001e03603501903c240100401c0c4112980e4070b442000050340a4000c0400381e14980c0140c1303558440c4403500d1040c1e2401100c00c80001031540c00094402e00380041110340300c40f1a03449809540d0f0b642c481c080050030140b10110360384504031200c11200d4600f0400d400410b118608055101e60520207200c4c00c4600031982207041d1410700b03a088000020100894440c03603044031b59800d0405401005038a007002e5448200500c0c80f000540c54188820108000c0c00303503078200c2c0d01d0388210b00030208212039800e10b004081d520940401c078540c5c01c03600950105003507941c6810444540f0b00c44100068000c10b0414005000c80d0b1510780d40082d95902c01410a000d088502e00e20010f01038407100414019076242800c02140030000210f420320011009641c01540d0040844a02103140c0c0d084c00034000700c8800700008241404042a41c400c4041b8108170300c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 725520962 1250 725519712 725519719
    0x7120e03040b070c120302060a0c05090d02010503062e110604030f0c11090a090501050a2c01020c01110a0906052511040f0c0f0c02030a0b18012406030209 68
    0x7014100054080c0c154000704045420020f485800280c80d9070210500750f07864083d401405c407903d092004a000e0385c4000e03100038100403040044100d140d8414100c401803a0702860420381740e0f0b840c031000c81c2c1c0160f000348641007a0f1143d042104210328007a45100c170012800d40d02d107020b1070100010987d4030841681c0040100d1072849621540f24404d001d022615401817034003000705098480480e0800c0c100b55007856580361035032410340c1404800d00400c0d4019291440c00c10a01403100c4030b0545100e18404d20707003901d22030072500c10350803030302501540c1501174504020481030010720035807042c9038000d5100d280810b0b0b4201c0700190b0207009030b0a0b50010092060070384004480020ba8082008804c50b0807550a49440142a802c1c0c803a48540028600d00043c000340038007122001402101c6400b8444040001d03880c00c20006850202d00841c1c003030b0b804a448040d40d2030300c6245950124018103206115881c0c540b96180c41c04a8416041640840040366002c01c1e8440b82c04405074841c02d03080540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 725522212 1250 725520962 725520967
    0x312160b15032514010c0804030303060905090d0c0809010c0c0f0305010c050301060f0302071505100e090d02150a0b090c0a030b04020a0e10121a030705061303061517030307120e03 79
    0x113100f04000d0b11038070240d01450282004400c0355120580c50b0881d402c01d1340040d80d148014042010507200d8030703409c510014001c04c402c01104200034808009030100034628400810f0b10041c59001ea034840d0306650344540e9581e4401d440d01c1030614152003910003503c01d9800c00088001e414042c0302124140e80d4550b503080308440200100364060350028104680d000070320351601d0005a4580b00d00d43c0510b4070101100c1c40b130f40c541003c501818101410842807030b0400320b2040d00362600060b6801d07110403280309040c0540d896411900040c40440c0307525070003000810800150554003802022840c100fa1420004a428042404100e0003007084020214072005038226052502c45030b8903400068a281612518001c480d040e000d80300818026407581012440740300032441c0501012010344002c0e07030300d0b44c1886048101d030080910305110203000e040d501c0d051812041d0180c428800035019034a183c1b9803078054a0400c0b039680d44121340c2d081c0007400d00036030b502c14103659000c0d119407010703074500460 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 725523462 1250 725522212 725522219
    0x20405011e180806040c0503060c0904151a0a0921061e0e0c0a0b070b040807050f0d050304030f0207030b1f03140307021c020312160b150325 62
    0x1d031004412480c400078801c1c0070301c40141e03071800158110007814240700500114106480c1190020419400c40380c80380d045401009403116034841552010707601120f0201d90000c1502c00040c01e0318083d0890a491052403150340c0501506030010402e1403010740c0d1786914650f441c5414060070710403403281e8040c901202d81c14008035241e904004003810311100ea8249044845021808894400345a014075400034000c03821246001407041c001000351030b02d01381c40c110282d622895042002000145440e40c045101001e00008201420101154508480022004540c040c000f50030465003200003c44c0e94800f00702d803070302c081740141c00c580e400814076000380c07070303030103008416112030409501c039000c1088002012900c0b10032a0f0368402c038001c000d1680c4070a00e0041c000340440803803001030044800c900c140c006860005034407e41d40c0032801a56110100396905a0b28445050005005141c02d2001d02902900400d03075862004812000c455504103e00d071302e010f0410111100b03910199182c14100b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 725524712 1250 725523462 725523497
    0x2070b0105040b131a10050f030c0705070b0406030609050a0e0a120225030309050306090703020405130812010e150901090c02150406050109060b09060a0f12060e0a0c0302040501 78
    0x950603940014000703000070041368440d000310b030780000c030081103d42d100300c4010ba14140311030f80c010818120f1a1540c64949850707261088d5100140071318154080c002402e43c00e00c1001e2042c60302a226400191343e540e0381e5000010040c0070035000e40322880b89048040348980b450341c80752075081c4441002130f08001140c1d4851484101213055550b040d03015601c8440c00f801c600c0526107100741d4074080024001800e5090040c9200c035150000d90080e4020f0045c0002250001050000caa50441d4041602c5e0313110f01148030760801c6030400410860011032185c4480c0110701c1c1c0c090580702207a8550310f45030303214081031440d00c600826168001400300c00500040300303241c0066401c0882401100e00c00d00078035840a2031081d084400342c540b1aaa200188545140d03030160754010800101c506090062400c005a094410325800d0800d100c4264501034505024020f0700718480c28645007002003590f2004000c8592008450880c956890000c4450340036020f1300c00d440c240c41041c0d4940c81010a078a001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 725525962 1250 725524712 725524721
    0xc0903050d0e0402040b0a020f100608070e040c38130302040b0616030503090106080c0112021b0f0106030506220b04050f0102131d01061b060902180f0a02070b010504 73
    0x10315002031302000042012031400300108056100b5038010035003550946111820160048196504941040300400007038400041d054160307580c4000c001d109480e01e250041907900b4070342c0001565180540ea0710221022100c072000464500c01039035a41821030810301c4414483d060817a0b60031000a642440541005d600250045002609191801a44840c100a81d0b408403034101d0002d00f0000401441150038000c0000600c1d401000308101c06907000080c01c1c02d4020781400070369550114524075011500280031491640c4081580c0c00c83c0c24891045001c1e00d04d602068800703100d20804500b1100003c1c0d118080314203124030325004107580783d990b03070001480078105031042c3c49070a0340701c1409007080c402400d001c0880ca140808452909203900e40204001d5008100030480c8001000025007009100088078004c11000c0c1d42d500803803078201c00801032000040d4010000101450803805d40058440c000c40042065205554070b01d050141039101e5680000c00310818038004100358100380c2c11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 725527212 1250 725525962 725525987
    0xc1b011b060e1b13050106050d090f020907020303100501050f09091f0e040b0a0209100e0102100e0106050a080a1131050115050a0e10030e0609030309010c0903050d 72
    0x4040340000c2c0c140c1016141645242882c4a0f141d2607091118240c50109590882110064401d0102d58580785000c0c00c94062445040700399a100e9003074000300484c2d1001c2d8071300d00c0d500a0000d0190304001034001d50f6a08115035041da2144007040110b600e60051003600c00c8440102c55041c60300046405010646101800c844440c00c0702000640540300c0300341c6031f54090048034100810340e203007504021a4041c00544140455441004011002e8455000041d02c16496041c0340c00f1001300e00380101e10304030640b00300100766403512101004059045d000039048600460b01324000b96111500162651f09030040203000c0c000800d0402d400341000b440d282091034030100e60101c0b40c400000d920858691401c02040c42c50740d40d10051010200840307031300007042110318015041044c02c07400a40b18080e071010300c1f44101074200c01c6100710740c8203412912103a4400d5040d1100390030480d4a040d41ca0f0000c1d15601d00315420035540069542c46004200c04407070308940203004a00007288207179140181e008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 725528462 1250 725527212 725527223
    0x30e0613081b0f0307060903020c090c07060b1c05010f1407020303010e10030c0605030402210c1c08160302071d010612060515070b0a05040210120b0904080c1b011b 72
    0x1003d0800c001c014400b500000e80a244c000c1806034041c07400038201410f5021a501c100041c00511511040c0036003550310345540044001400d213411800039010704c604c0f1000c03681000d10740d060401000b5043d0846c0035214031800e41408002901c00c264510654200c4d072400041c0e00a0004011080894003400d070084020f80380210b0b00d586031388903403215140300e812040200304004180b00031805c0c1a00f03100644000e1290150803082e032036501984480ea500c080c54030500042c110252205141d503080b4200603400704a032985d80084900b10350000020050030340c05400340c00400514440401c0d128401c455100d12f05810507800d003031003030381c1c1c81152507d07480c41c80e59246400f00d200d8403595420b40c2001112808581c0701c80c884d01d4010140c400042c52a449903080c4403c0c00016201c031034071041c084200d410032804c05628580544028000c0a100540c010000300901040c42440d20091051000080540d040320310008210074a25090030300b170742e000810b800c00050852041c98411020f552081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 725529712 1250 725528462 725528473
    0x80a06030203031224060a030b0a2607080c0303030f040f021002061b12040f080c060c0a0318051f110d05150901060f0825030e0613081b 60
    0xa4001c2480c0d500b0109441034846649810701c41900700350000200c0201141c010178211500000200e0b009000b2032690301d06154450071040b070a5039600f10140041e00200c540c0f4017143c01017440030f80c1c0c206070a00c2140350074007506102013120070340820011a0700c0c1c00500158550740f66a141e0383c2003082d0041c2300f998122003055014005030b550045058600d14542c1c010900d9040c03042c1a0b08801c03403d061f001501c00d80801107192058240a042540150010f01119105105003480e0010b841450030310078060164104111052900801809210781c1d85d0341e040124418a11102e51168484c08015149a00034803910642205d010703e10441300311b512801182c7c1042160800c18942c20071072540c08000d407101c007002414020f0049611102c84100c43c04e40030b0354982103000c1c0c40d414041001404101441c00080d640c1d40000c0b039003011a010300e04668a0a45104c0d50050040601d001e0100d841d01402c000b190341d9120709148425002c1e0020030140c54200c0380003070b40507100180c0783d0380001801403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 725530962 1250 725529712 725529719
    0x110d08071505060103150f030b100b16050d08042111030a030b1c0b071d0904080318011b08090f0703080715060f05130b0406091a060309030901080a06 66
    0x1108811000070740e1400119680c14a0300000d0107607261101c420500310b400c52401c01492041d4880e800071241c0003504200e054607103503003000d0703040b0098001a480b4000041d0002082c0e1a110b401804c03d809001501d91800103900100c40128003550050310a0941c48070f501d408694002100102c04101c2c142244040320390f032203040c00d54200b01409404641d5802510b1a1400e00c0c0d02000c542401d4402d10040c2921540c2d91601e1008001d001c00301044a60b4403200a0044044043c0b48400c10052504200d4542464900d803554000c4034410f2181540191181e4410340501440559420144115000355050b007411204200d0050070f408080c801c00d41d01040503842400504084d50103000300350b5840343c1d903007486640003c0c0c08190984070352a04104005c9441000c913000f056460844820349010b02504595015100e24441207074490f140600010700c402c02035110500b200c0100820411070b002c100100f2002c1c1c0000c41d60000d0035001040500c01070340c4104074640d4080b003010f40010303440342c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 725532212 1250 725530962 725530973
    0x50307140f010e12010b281a281112040506092206050907020c03071205030d0c0e010906020c0d1b0312020105060f0d030905010810091a0913110d0807 66
    0x15003116169a503551b564402100d8148082c500c010300180c880c803101e82d0764040710508030044d141c1c42400c800426180e03091700c040d01800119410107004408551490030300c4030403904d4003040711140d40081084a0030200a0300000300703a0306408030310f849206007031500c0d040034407020f54000c0c9012980030f0511f454561405505c03503072040d0700045c00e4a0005105040000b40000b04c2000752001080d54000d07560500361b9903000407035500f81e400740100307807828000c0792600500d98043c0c0c0802c1c0308a142041d0070082581e50010a100d055203003607a8524529503a60416030320781c0c11170320210b80c0041c4640b45010214101500600018400c0c9404104d42c1d6030b00d494a207007210b4004410300060f51504244101d82c50300d103500c001a99412128080384541a58020703010380c07244d10510b41400b0401e00001e203080b048503019001401d0104007840145900040c2a10000c51a80340500c54480207020a0b07240c1c80a074140300f59030354000c1981d440016002c003002039000c81741c01c1c101d80c1c090041041c00300040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 725533462 1250 725532212 725532229
    0x90b0d150e09011103010b0319090210020d0806060705060a0b0a1a0403020a140d0f03030617060f010b0306012010020403110306060909030706200a0c0309050307140f010e 75
    0x829030032100050030802c0c050303402d41c0d40076485102281010b00040c49078424980450f50050401c600004060b203001071580c001e0040914081d6120001e106050002d540200b00707a100c02446030ba41a40d01e690b075008020301401000700180003a44480c00042c85007815901002442d40003d000310589035845214000c0604940303401f601c03102002c1000c00460a10640d00006881c84a41c9030029080240100f11801c102c0c02e4090400b031003000342441030500070f90140c00a400c64200100b0a4080307a560140d583c041505c0c5000103032252800002e0010240703007601c1c007640c416500c001c02031044103240f00346c0140c03030281d02c0b13141d00503010480151314031803000300001c0d48240310f00c1010b4001c020405061440081c00c0310f0044044804014070700401001702c3d007006600146c005194090b150040e034003090300c40c00300c80e1101400030380b50440e20340210310081131904c240da07882c1c2282d44400a15444007243d1240c002030740302150141410749485003005a0514061510a2814014100051154 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 725534712 1250 725533462 725533469
    0xc070215340209060f0405010801240302010e130f06061d0d0503030606160614040c0f03050304061224060201150e0c0306120a0c0e09060403090b0d15 66
    0x1004005501c403501d841e40c0300c0c480014107038941500500c4407075071220a01600034600080c45401c010340040c049076262581c4c540b180c007011b44100025a1500e842d1402003c9502d0140003592440240320540c8803075031030100540f507040c0d4400220082460034400c20149103040190241e895000700e0440213034503c034030320091a282d034a02c130071005a4080350041c1800f04041034015204202e0110100c0c0e00042181e801c030005692176039441d0052410510100600c2400402003410807c45c0000c80700d0076807603035001314001c589000b886039860322901d00500e000c0c400141990402c0c8070420600b40142d00c0d01d604003514190108114680407101d00d40f83c1d1821310300725926070f1150410701c9900da0900c5a0144003c00d0214140d0315401e080d00d6060b081d43c02440b0901c0150000001249034032800c80c84045101c1240880301c0c581513901d040d10b503100301e5020392021444180001080c1c540009601e90190b50541c4400060a0400c119201d09510008a556800e0b0b1941130542c11015901100d0008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 725535962 1250 725534712 725534749
    0x50c0c1f0f110f0a0b09060f0601080703020c030712030e150c0a030204080d080f0a1103150d0b0723040311010c1e0812070f0f030b03120705010b01090e09150c0702 72
    0x4000c00361030000000380e0041c1c44244964000d804100c81d00c042342010641020003420500303210350320b05200324040c0c03040c040c2e10b10540c000030500b4070800160105203a0b1101160300c00707000760107000807010758404d0016031403d140030018001c00c1100013050005c202d40c401a2901524294503031400c0c43c64001c940c4071860009040100700400c9400c03e840d815006140000c05000040010303035a011540405402d21000341041110b682e020b40d500c803100c00d01c242d4403640c3c08509240c0143e01400c003c040b0540e004860040c1e81e40c4003c500c08900c00c950a899000c00d001004541101c0115007104004204840094441580c02601c0940303c0c1240c0c1014400e240d910b94409510044142e00013000c0c090b80140306030b20400c0152a03403c40c0340c0300742c0c6c0e0760a45000192200c0320000280f8058010703040300c201c12000a552401d11006400042c0075802c2a03c0740b1660381c4e42c0c1c102c6200140c0080741d0382003e40d00140b00c0d4502c0c55140300441c030f401c481c44808040c1040c2240c1c0006906400c074020001c0c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 725537212 1250 725535962 725535973
    0x150302250f0f0b040b0f10031112070f060e0306010501080a050603120c0f0c041a090403050f03070509040e0d05041403030f0a081b0715020a02010e010606050c0c1f0f110f 75
    0x2006848010b031641b2103484400180d09090100c00e04046a0f50742c00700400f14520707140081c3c01c40d21550000f07241c1a06080c1203c1d460340c1c4d107134a02960041d040c00380500107410709480072800c0c1800241e1138100d0340c1c107039511107441d03031403000003001400d0251107268140150712158001c030801c03034080d10402c420003002c2c00c0e083c19250355491a02e14102c29560180e4240003041c0c1c03045801e22a84650b00d40c0940700c0c8001c50b650382c034044490b44036260521203000004000e11070b04aa00502400c840d01c4c0c191400c2141685140703410ba41c661902452000180e810030003070041403c910001003040340d000d001c4a05200a03020340d4929a04000710b204000b4030114100401070505811000d5101000303c3c0540c6400c1541e00e881c0768200c0015000702d00d607500000c165030007034801d5105484040e001030003002200d480ba200102940c0c80103100d081248203010301c02c9110f140a0646110707110031700841000034058030b14151004218a94404281b1001000920b44a0b2042c400c90301506e08450180a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 725538462 1250 725537212 725537221
    0x90c03021b0c120c03030706020c1005070c02130e0705061303060f05160903030c020f120307140607021b040b0d0804090603120f0e2e09150302250f0f0b 67
    0x8014000a0000594001c4400200a1710040104c0d4880da8000601503580c0c0d00000c0c0c2e061812107501070b800000c618200410410543c44002d1031116882220151b0300e68000194100683c3c40c0a407040c0815000701c1e1040041e480d041e801025506004410080155602d80f41d010440d40b8000005403040e45940030010094602d8100c007405c2a46030404034a21800d40e20000e1100908180081c05050804e0300f43c0c4d581e560b068002c1c00c00352400d000b201c3d540e08151414105412010980c0082c40c8145804075030780c1b82c00828500200c4100c202020101c6a010f420040502168041a5046040c1420a00201d4091001000a485c40b000040381c2d040c51486e00400007075801500c3e0003003103c8440d6140810342e010203a0091804100c4401040780d00069852440c0308281540300080e0309450840314100b50087d0211003150a200d05001651020344070680603489030403032024816450340212400c1d0a038900c1850b080b9030242420305407902c5035a0311100110f440041c203845881c0d4050401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 725539568 1106 725538462 725538469
    0x40905040609060b1c0303050a0e160e0c0a0903020d050708030d060302030c1002061605090a0f090f09111c02060a030b030d020313090c03021b0c 64
    0x104000e0a10789003890003410301403411200c540c1050000002450902c041c0c607021503405041140c0d184156400300c0c02070000900d0300d0162559031140110001082200c510400030b0700711000c041d60704010f080481154000e0480303c0007441041318131101039004905204903a8103031401c40450050b45403143c1055921342000342d6500c00454040c00c0d00c100c91308100d040328025070a0700c0c048074070001404403060700703801d01c00c015034095404a5003009020000544024079460104d080004079000a010208070390311001140030a29824817100c10710303119015100082d05820882d036440e5695a21a40210402d900d1145080c0086141940344070300265800340c1e030003401c05540b00000100640200031001c0240e00038411550180c4041c0d00000465203082024410301200c00d03c1c010752440600b14500c0c4100416409020b0650000b945171054204c3b0f032101340103800110164401d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 725359712 725539568 := by
  have h0 := BRFrame.cov_init 725359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 725359712 ≤ n) (h2 : n < 725539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
