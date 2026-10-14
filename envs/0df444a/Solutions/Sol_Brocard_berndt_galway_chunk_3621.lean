-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3621
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:45.244637+00:00
-- url     : https://prove2.me/submissions/e1c3aad4-1af2-4737-8f9c-353e2eb81cd1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 651079136 ≤ n < 651258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 651080386 1250 651079136 651079181
    0x80307110d1e020d02100f0b0a06261909151d07080c0609040b061324020f060f180a12080c03010609050d330f020a120525031b030b0913020f1909 64
    0x500078012280ccc19035000c1d044d101c050900600205820f550340c0d002501c3e40401c041c440340128141c0c2c080800c140180c2601445c0c0d00000c06c40008284440c0c0220083c10ba01c3c03404120b036041000402160140075405070b424007081408101c14089070010f01440111884541001c01003d4a0314481144010031580b001c440c40400810125856412401715400540a901d60701d2a04252106a080500c154401c44406800f4421074088103581001162038909080e01c40b40c1400c42144002d000d044085440c90204000318141403e694040342d00031449403522083c4a00400d4003813480508103100c003922040100003140341743c42201010b100740c40302146000b03640c5038080c09800c1314001c4041900d83e104005440d4419010700002d441c21903071810001c42e901a03502070b0041034040e0f010402c0b0380d000b141800f0004d00a12921055040043c090b0089541d641c1810818010580301260007505006100000c0e480708005a0045c00764694036440c0715040003441c01c01c4a60040e1820101c0e41d503c01d0703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 651081636 1250 651080386 651080401
    0x60f0a1e030201171e090c040c080f070c0503120403031401122a17010204051807030e06061f030605040e0102090906040513080307110d1e020d02100f0b0a0626 70
    0x8440b0740348242104024805c0d9910751b42141400c0745080003a41003070030400e003140b07042c2d80800c015105d14200c800790002c91725010400c50b640400000e000b001c82d407041003809041160000355039402440303450040303800150801c0d000c0c0310440031380c8450710040350020180d04201d01107444003034404072040a80c00320440b109848550103c588207150300c51003056003074003000c4400c0d01200c01409001e001550090712000000000c00341c11a4100b0020780b903c407651810980100766140034050080c03050780703552402c0038800e0111516420100c181541c5480000b015115402001951911007000503200c840050a000c4010b8000348428403c40c82c00c0300300711150300d0041e0840380054000c4802622940e5003041aa644204804800c480b84a000c418002c0d00744d001c05e806641510030342480010390f881c000d060380d03101c18844280004da000070b042207000c10140d600c07002d06881c1c452800b060214415000c82c2022a123600b004000410560064078408585580064440200440c10b5414a0041d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 651082886 1250 651081636 651081661
    0x5070503010b0706111204141b01030209040e0d02300a0c0305070b09010203040606090b030d0315030f050f01050c041a03040c0504020c0d0806010c0b060f0a1e03020117 74
    0x82d461007642d012980c0c0050210903403240303c3c6220700442150391008900b5201c8441082160100d5242401070002482d032000413540c0824041c0d034101c000300041200c070040d400382d0040c03e070603900143d0b140e42c0305c4060301e070801c90302051000d2600505084206900d4a03003800303003d105130102d030381c0100c4100ca440d03019040c1180c8003940c01e40361111000d401791604039101d1103056070192118040c130741801981d10b0198000c600482c4078540400c0b60b50b95846c003a01c181c64103100704680c1900141c642004060094000c041e1150300380c83c8003000c803034132540e8038140d008040905844541c0110f200b000828024424941c010b05a024440e00b0686051001e6a66444070b407112801c0c0480070010070200400700c0c001c28098980240295141c4905200342540d0f1002c6007aa4000030b86250042400c550243c210203001d160001c0721603042c0e60f1100281f007620300c00c1191198010240a2000801412b1940c806107940c644103000040030340b030b5000050010800c0401246414410380502c0710449c03002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 651084136 1250 651082886 651082889
    0x60f150b0d02130b03090709060504051306052802040812070206191407030c0203010614180613150812030f01050d030c050709060303030e01060b0406081807060f030e010507050301 79
    0x40c1c0c02682e521501000c10003c45800e5000c40c0c0d00b13a078003005005960b000403070910103641604008010090742c4200304001c1d0f440650f00c92810710b0b002c455400204080b50000c0741e004c41004020030401d201400615404081ca03a0003541456001c64280702d003e8080c0301008003004005007560a05125800158542c842c99a0000c8449070038620400e005010311620200c00c0da0022502d511440c40d420050700035002990304030304c00d518006c004552003400075007040b8241c00180481d4504d81c3c42c005c4e900c074820000341c45c0903440300c1095142004107226028140014290358445c4903c5494903118078905251201c128488240502c1045241c2c15410b6070720341141d0003210020305001e00c0d42019a4010484100682305003e410070205000100d5000601160b00c80e81e0300300101d00c034002c08076007250300c41e002d01181c0c0741c801c00c002c0120710b02c5034070010b420511b00400d44c403280105050403480d146003a84004046210900d080008035014071800f03010711a0480240400e18140600034500d2205 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 651085386 1250 651084136 651084157
    0x703021203151f0f0306030c06110a0605090a031e050315010c1a16021207020d020613080a1505040f02011209060f050a150e060d021c060f150b 63
    0x10000035100440b001401900c070b0000361880d0064440c400d01240304440740140c40022401911089120511a01c075000880c1d801c00002d030002800c0040c100d408001e00c40320400544240c20944002c00c0f405d1040b1402080c80000500700102146009000e40c014401c0b05e0304000c0c0100c0c80026036035003000c11030742d000b0101e0f6401c91003d074410005032350740d84050202a1034925848141d0750b107540010441ea0289228001e203c1002c034040408903075030a295a88880c4500060018900504124006c000c40510082c03445061441c0c02003090900021680041540d1784000e0503002844040c003150f58031070700000c10901c140d04e030640f0b1b585001070070360740000d0400886030354440c1d54100c036502025010790b015006000e00c0c03100c1e02c81c01e4040e040c00e1f2204a107240c81c100c400c80504a00840705804c84540f00d000700c401d5a0303440300700300030300d550110181d070401e20b00103100300410364524014840b00c2c8203140002d0004079145440f0708555002d403501b51184004441800062101029920525003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 651086636 1250 651085386 651085423
    0x3060f062106040506091903021b030106120605060109061409010f110f1b03011e020d020d060b031905061309140f0d080903030105010801051c0510091502070302 71
    0x900003120886001c0140d900410b004074014001009404030f01c6a005026132421115559860808030490302c06002e070040243c1d2103080360583e41122294400b03e805801000092000e90318000c0701c21020801c0d400700d42c12940c1d541000310b2503800c03c0b19880602103516245030f06401303036032100d04207100340b8000074140b02d103c001001649100702c0c506000c0e0342920040d00d00c22a080b400303c640d80c1007603100b800500c1c038401030f92000c582814856000501100d2084507109804520306400039401510000000d40e002c002c590300c210a940240401000791060305552850710304100c070703003003078144200511540c1040e09201459580111110400c069150000359041d01880e1100b0080c0d00f0a03800e003001c0c0200781010781c0b0040081211802d07010f030358495800581d1621000780c0c89100034065a40403400c2400140720905120340083c51070800c4440254031415603855151500707404c5020f0705001030302c1e14202c0d010800030906001150f1000d05081d800d013446580c02a4940d0a03155240c0f06c80c46 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 651087886 1250 651086636 651086659
    0x50103092a05041a01020601150c0515151e041d0a06051b04050d080f2101080d0516030806030a0b0708062d01031d121803060f06 57
    0x30300051400c400400c4400724054241c0075010907550401c80d00c00d051080c4c2c0740802ea80a0600d40b0540f060000c00168040c0c85103a007000c1e001031602c02c02d10703610b0b03040207243c00c02203001500400401c4940c291204141010b0703c0e01030080c0c1185c0a002060303501814040303036044903508421000c0440c01c0c0c006c580100e001d5000310140f4542e024500309159251045680d20810b0205681c480d5000e040c8100321218280110300c0d806ca510f00c254070503547c015000c00410300111f05034101400070000405065898103901505140d005a21440000c0e0300c00b140000400106c401000444807207511410701c1420541c0020801d01c000142b05000b409010100d000903e40369018042d160085902c24202c1c00765041100004140341c00485419000303c00c0501004108020003205001600740220001c0400c05500e00460241c0f0041032140031a00b5000c01001008005005450038101c48840c6280c9803414601518001c05821100c04e009800240074401021034000c10264044801d6648e0308014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 651089136 1250 651087886 651087893
    0x909150f15031c08011211090a090f2102070305060615070b130209010504020301050d0201140d06030f060f0b0916170c0c010b030d050d0f0e060708040c08031305010309 74
    0x14082140403582c140a50120365941100e185000d0b040300501d56200d940580e21042520070000c04c0a0303018005c1c43d004e91000440d4a0f2015030340382c1c4811240d8011070295950380d11880d440c060664100d810b0b500c02200101800701040e550500c00c0d0f400d20003007031990f145031156070b141d00340a44154082e4a01d003007490071141c0d9810454450310b034003a6076000e5030318006c0498049000692400ca114105c802c1c000201ca14250080d64140d4100503ca210b24000c5540192a1141d40c61208580c1007018814540500142e02c00c00d0700071401944a145071a0051821400301c0d503036150050030051400c80d606550b502c401f07140325800460301c00ca51442c0c0c0030f140030030350303d500c01c0980c2360183c00040c00c02c000d50f0914090244c500d58402034000e0105403804401c06031655210b000e0140001d0701071204ca001003c49400c503444d130301042c100008002900008503410f00600b29000030210b4444810b11007080031004000c00244040c4010354108003080801d4240b1500c248240c50405807034a0410b020b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 651090386 1250 651089136 651089161
    0x90c100c0f170301080c03120405010f0e03100e010b041517070e072703080319090501111c140117010e0a03091a0301030b04080307051e03060909150f 66
    0x1010b41004101d4924114052a007030385600c00d000b9408a4050422894000e040c002401c3c40c4040c000344c141c070b0400c0e091000440c0c6d0418040401020401d42d51b10b84411910103121144040340303502c802041c40525100c0260070365001c0c2c00303418002c03441d04038aa80f400342a00344410990707081031505000148122000740c40c0c032646802608001d2102001e10813400e800c400900c60329800c0e09003a280c0100b00030380561160845120107441d4074020800999221032903030200300118440c200000360080359480e06030864401d0160700406a900040490707155500242c5450031203502c030014410080c2c0d8048080a01e841072045100390610908942400c0e98203410907184117000740c00712003950700319040007000c81c02c441c4200b803503c400300420142c0b00120001264103880d0411825140c6440d5940d44650325840113100c81d0422405002003180c00310402c942c441001c0d000e4100d0340d200d041140403c009660045e0070322820740e100451303001540810480c8075510001280740b0613201e0f56003040e40d1a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 651091636 1250 651090386 651090413
    0xb060c010510050a12170901050d110a030b0a0807090b1f0c0c0603140411010c02091009050a0b131d0d0203030f090307030c060507030207021f0305090c100c 69
    0x95420324003085403a02807940d181c021a00c04035183c1840b42d644000584043c0b1200d080507011002146004810041400c0240f4a802041c50482d2401020480d580110358010171609020100011172802840d0b05024041510740c00f194030603115840c0880c10b5548103006d111746806503440c0c1c0210052380d55103c4205a4404950900c4010251110b100a100c0080f000c412151270340146c0c408079686d4400d205500ca00c24480d07403660701c29140e9444c2d40703142c008400d035141c0c10060031901440042e2106000c1d50b00403044cd008182d045818541e01a0513a80000c000ca1880b9182060802d610703a10a2907041c0c0712091400c000681c641402d006041c0702200203d030681a20656070000758199000000354803030400c000302c000190721070700d41c01e03626480391040c003400003800c4d1440d8002040d4954441500103600d07003001860140d0310f50100f84071659548042d5044c81d2009100380a6035010300401b40d000e81045e015016100004000070789810a203001c4208200341d080c1010b0400c04102826031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 651092886 1250 651091636 651091657
    0x60411030106050306040c110d08190e0a0c1514090414071d0907270f120b1003031e020a0b0c0702180112033002030709050a03150b06 59
    0x140d596854400c054079a40c000d450103030089140440c800911849038a40020516002c03000d05600e4001681c21a04110090403d1551003e4800003900d4903090784079510780e804902004d440d200d040c900b0240100e55040e8440400011046010391005900025501a985900c40459203c42c0c0202c0414000c0c03401c5411b180c442c00f000e0080c404169000b0495200c034441c1c0000c2c01141091510a2055085080d50124080780360751003060303040207501316400c141111a41056a285030384000301c20191050341c0c89018154410050700f824040e040b503d080d880300d545618008218550703075000f444980842420118a41c10f0000142c995100b8030000c92000e403c410b03d00d8081c1000c0400c07418542c440759040740b046060310b29551001a0001100e81254941c9900e101071803002e44058840030741400c1c810210360341d001034201403600c0d003440070b215212035594016220b280039400541010175503045a4400c1c1e0050030208006188001440c070301202c05600401d070180000007158007402030b0240e14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 651094136 1250 651092886 651092921
    0x702010b030106080105060a0b04030b01050603040f0611030f01060219061e051014010906052514070608060307050a03141203090102030402010f0305090c090c1b0c03100e150604 78
    0x140c55003054020501454084501c80c003009c0d41e800c11800b440c4110322000b0050800640108801d14000b0040c1d54400e00405c140010008039640b140c0c203c425600c221107030b80c0004070a0000c82800c00100c1c90262820340000d0901e20648a4010103030b1a0440008152544441d4140b81c070f030070700108a51145803000d000340a28200f0741e9002d030242d5458007883c1c0340e4080151004007590702c40c4042908480072500e0346454215220160140404610a0160941d202c54001000030f000003440d407042e00c2080c03003c2c201c2c031824920010164040078200c0b610030b600041c42400f00c1e80e40c8501c0002180c0d4002a00c01c12002c160065608190a1140151031f004000c42000080e1006400552065100766160034074040401c0c001d0703084035002d48116031a9800001c8113982d900b409003082e9041024095a28207100206500881a013500c0d568074040303402c5230040551908003000340c006050200c000503c507804090f0703080750f034694881e644c0d0240c021030b100200e042601c40d5800400300b5903c50401c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 651095386 1250 651094136 651094139
    0x2090f220608010e010b0604050918010209060a050c01050603010501350a1b050a0b0d0c350105030d080c0d061203091d0411060a1404120309060518090702010b030106 73
    0x500074240c07440700d0650ba5003007a50900c41447e00200700d44c152007000304500001e45510901d040603800000000c4920740d820040e8000650f2008060068080d940e40c455660b00a1502006d0a60b41c2c0a040c0758060303030610700144100020789203c1801d8200112910003403222402083e15000c80144508459002c1d5070821020b0240d4240c1801603417005c45001d0308150750319402e02c03081505034865010f03000000c0c40103000e00e11170f580082e40345442c540361031016040e00c0c0400861481c15102007444210282a105d0707000c10414580b5801440c2c100c0c050240c00c02d07401c02c0036180a070024039882800c00c00080500600380c03650b000c1000b822200390540003113145446e000e00490a10b01503040003031a080314003887c201001513000d1140e944400b107203581c00191424030240e50005900e80e01403108403100b40300c410411030080c10003020101e81042e20722102d03050140503507042d50410300401a0801c40040b416011070741c902d01d40e4406403011215581d079401e00f00d004181da0804107070315509104c4c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 651096636 1250 651095386 651095399
    0x1b020303010f1e06051b060a05090d020307050c060c0a05060405010f0516021b0109090f0c090602030c030301122307300f020612090304060f0302090f2206 68
    0x1440c180d4a1540b00780440c50b40320f0030079141d066000d51154940c88102001440803502c520041c00c2181000f0079807031b04101401d5004c0307060038004c03189001a990b40e041000038018040100e10741503191800590318010090b02c50b1521010910082d9005010026603100e603c401040130105240e003003c10b55040e800d1518010b40a0619100740201305810007010801c1c00c84c00140c480300c1011150001c08214150007040000c40500031041814442d503150002684503003405000010f4840a1001030103001c8800040e2090b00180c101004641c8180701e0403c1c2c4001c0001120305442000e01100132001c500e280000c011000f42c0b898108200e842c980090400400140c0c41d416110320194440503100650b6002107218083c128040559107480e003001b0208071003140142e90f1a0010740110700d06024481c0010b544403050300e00350901d40c40041c04001041c1c0c03018130419914102d240035480c0078414000079122148000030184510056180d0100054042203901501c03854940c05100c0d0690b6101c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 651097886 1250 651096636 651096643
    0xc0708250501080f040204050c09030a060e060112081803030702040903020a120f02030a03050903070c06170f010509012c010f051c030503070f0201110310030213270302011b02 77
    0x2800d890100c20031180454958010b08040e807040440300204101079445c0c0c4c003040f002d0035001d4031150103140200301c0700304c0c030303480901c400120325014907000f2031001c160030501d9180040584c4450040c500795505900041d5101048038001c030904108801c4441c48600000c1c194841c01c0300007503110385000208000c260700407030403a08a84c004c650001c0d43c00741804082da0900c00700800040107030001c014a03200d6078000d5016681240f0305908403400d01d40f0310b5881e03045480454000402146201c64030b4003592a00030300407540000d150100105652612003c258404810701a0200a44103400001403d040c076100c17004169030312520741d401743d5a40e4a255404041640501c5000b0075284511030805000744040c0868142d16a4543d0324544d594003003103840c00034141c0040110354942600e4602c00c80ca80c0040c5020380a05050002d00a103107104200501d82d410100c1c80e1580c0c14605520112030903214041d00d948082108685001e0083c40d0490040c00081d03c07444c403c0180710184808a580003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 651099136 1250 651097886 651097933
    0x20a02060f2106120c10110a02060307170903180f0f091510030203090d0c020a0e041203062103050a050c030304060b01021e06073b0319080f0c0708 65
    0x143c401c44000c0b1540c0ca030b810f0316204c4174141103030041c0401c0a400d503403a01c190f1481e44014a020700b591444111a4000380c15030f4015a00f9100280c002c14086920480810f92244c00c400b040000754509010580e10907001d02d4400c2c0c1c01481800508108000d80d1914440800a00c030001c0080c019031406030300d00c40401c041c4e48290380c02401c05040102120707000340b007280d00484030480108403241c0400380c01c40f1035100b115001ca80025910000165840d5030f60101d900540c030a04040b0316014001000604403009584404996047e10202002d00c0502c0050340c84103641524009076505000102990079108580c5460762a00c070000400007484095031045110003800d070309413203801034412610f500b80485030b070b52400e090704981c0101d1441c1d40646c1d0031031004120005583c2e0300a0100c5024040c00340340d14820b000020345282d43c0d00580c50140b1400d501c40c2c0456050865040407a19181403038000c1c1e120103031702c102c00003c96030b000c03040820210000f0719415044031035000700d0f14012500200d16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 651100386 1250 651099136 651099139
    0x30c1e1d15030103120302191e0504050108070e04150b0c24070c050c04140910060b0d0b040207050f07030c0801051902070318082b020a02060f2106 65
    0x110403200c0348038601800c4686a400c1a07603092421a400c50f19200164400f404040c001d050b801c0060002c40015103030b460707000c000c0903101d0303aa000751440a038401d450454003603102002002c12081c0710b981c0c0c000e5021904003104d8900024900c0807480810010071820101061240d220000001e00629800040001d48840c03001d80e880d0b0380b000d40701c44000000606000360a02d2001c40003601151196100a80c031070b0045c022151048803a8012404540c4001001601020b00c40d0400500f503138104002d0000c40a074600c20000c1502d0700305008064055000c4a041e43c80e00d80000000960700c54040d60034098002d01501c541a8a00c9440340e40c410745840304803040150f03e403000a980d58184070300ca1041d100c0d18080500c110000c07929034025806480110184000d84650541c01d010301008240580480c00040100380815040d41000170500f130700080400e5041c40c1311803410390780400d005890319816118241c80d14070550703040d001406482c09009a0020004100c580408450b0015019020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 651101636 1250 651100386 651100427
    0x40f0b0c0c1b010c12030f020f030121020306011a0f0307020705131407120e011d010e07150e011e08010501030b18071101090204060801090c12050706030c1e 69
    0xc1848202c04000c01110750b40d0104031a4242030010403080341c0e1002c9034040d03500d0002010035100320840200d030485100c940c0d1442011006010107000c200720310701c0c0c1c1504034201d550800615800255521014000c034000c00340e40341c1e02400c0980c00c8800307954005540f04c04640e00d0380341171440203541d5882c3c4e22600d40f0070b0100c00c10303064504966110f1055944444070011082d075807004015500e0b0800d00078030501e41569900760311078200003880327241802c1091f0b0b00103072000d8101c00092400e444040480061903080480108518941b88850003802c0300036041c00300300a051100142ea0807080c11540c2e441e1540b1910881c000142e2000049051710b1007624200030300683d00091158104406104003070242050002c94a918003030700b007000002d000c00b80042450380c0f5580c082010303038200b50301444090b910b4480d00c00410120004c130401400c2d800485007103841c4203072141c655074209440b4030800d05035a2503020348014030442034407412031204064584480bd840f440140004450601c8010011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 651102886 1250 651101636 651101653
    0x5090402071a010f0810110405061809060616060f09050601080f060117100f020f0c0102030402120102190f05071202030d0e01050105060d1109090117070b03040b040b040f0b0c0c 78
    0xd40300c4003003400d0340c81c540001c119610804402200030316a207601d0381947d00090000141c03d550f03140c020520201c201c080315842c4524203091001d60040504224402c2078240481d001191000141580e0560002000310380c08400c14010002030071010360243c0f45018010020400c1d0000041d646040030b980303021a061a0303610205039002001042c42400701ea04203205651410b07801381c120303180c0390300c2c14180186410000c0014051a0380b21250004803a50080200419450104001503402845c80029881d2034841da050324400c80081600700c003400494038140030081e106009807069160320000c0805901c01d10078019690f80c2010044c0b042407030070401e50040c0700e40103001d480c0c1260801b0b0074260130940200164005440c0c00c407061000d140007408410030a51b100380109001f00b01035820001c1111003261001d04020080e0008081450104284000140301c010141c1c1d2040d04131500d02c40b19140c518294802c8074468802625140c5d00300180074541a201c40103110003144442200e0a48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 651104136 1250 651102886 651102899
    0x206040807060206010b1602041d1015080d091e230306130506060f040e0105101d07021f1b0e0f03010911091807090617210a05090402071a01 62
    0x1f407082c1c01d4408906c40f010607002c030060900d50000c0645841507034007082030306101400b50b854020740401101840380c5810342480c1107003003495a44040c0a455001d061194030b140c4016007012400e01c01c504c404041e26007129509109800000c02a1181d041c898490910220a641400f074089410034828018079000c00c4841d400340c031410008070352080250825a40e150704225003c0080301d001a04507496034105000b520080c842c043c4038404016628100c030b0304000440c03e81c21500d00d610301c20908c500050285980d0005890f201104601032004102c01d50000114043d100c040314011041800000d64403400b5000300d00b50749010425200303080c2040c01041014280c6030b4144005e40002e00701410f00e0107605140b1559035020440c86032440402581c082c205140040a03032185a02d5569072200b8403c0300221030034840c0141c0100010601024003c071080c1160f102400b4030102004005540d400c181d0168054418180005004545070201410042d050400c04840b40c0c4cc4125000c0010800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 651105386 1250 651104136 651104159
    0x21060409050a0201080a27050c010c050304050d02010905030d09030b13030c11040b1203072915030c130b0f01030507020307030521091005310609020604080706020601 73
    0x206401800801a05445400545d00d40502400790000701c1e13200c4401c40c1021422800b4210348180040440d002110141040c5080114017141e03141000713a001013002c04104004295800e032041114500103100e500d01c01a540070700c0a038800382d0140100c4402c0226160071180b81f0b01100d0040c2103062895407010807004e02da40c054440100440c02c20204c12010654052600d60f1204015000007074001101002502c110042e4000070050b07030000807154200100000d03a403030740d007150300d1140e80710a602c943d0003400485c004002140390b609008080c0203942c1d040042c2d074500c0034040c00d00c265a900751800b03807024241d0b40b001940120212509000994400e21a0b0761240300c41c0e501860604001c2d40d03040300c9982c41526840c0c2d011150082c06052404400106802a0002d600412400e5003002606050b50b000401d41a000c030840f000080c9011000d100785520100a520340c40e0a284503882c1020040c0351601010b5001540482c0200390130703800007040e01c2681c2d02c1d902200c003542e0303880450119 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 651106636 1250 651105386 651105401
    0x7060e03030d050a090606120615051c03120501080a0309080d140f1c09110103060e06010f05041e03021516080903011e02040f0e060a14060708210604 66
    0x800d079204024800c4141c02a03481650000ca4075035001c03950f022940c64002c103030340c81da81000080c0c03110740c04920100485481044000b0103020520310101c0c6c54580003d4809120715480c40c1c200002d0010f240c10140304030b88400340400c880000b00265619200703100e0355a00400b10490100341d51440201c4c4603400007e400c40040015034506040c0030f440500b200641d0800d6000c003072104010b0043c0390100c00c1c0307400b0340c4500040c900380003e8440e0103130501440d40201c854515050505e003000911240344005102544100207080600700c120307024a0886840c072590740181110108990001020303050f41404004aa0003201e008240c140403d0600c1c8552207100c0b840d0034400801a851000240100003410760390f6002400010080508000419140100d0800302d0070706500280605c807051070b0174800304c098589491038034014030307081012801d41d400034042c03020104440d900010443d034802c01291000380d44108890303106d8081035842c108a405e05070900401c07580303a000049244c1058400c490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 651107886 1250 651106636 651106639
    0x2250309062303060105130314010b040b0f030616180308121f180f090b06030105071110270c0602010f0207030512040c051c020406050d0302030415180605030907060e 73
    0x3490f5854100064840d035000c900f80490000006400001040752012818144100301d000800c8a0b1515001c0008035400990031038400c43d803071b011380c501d1610300180c804e610070241c600c640c0c02000c1001084e503401e550040309040303802d08200301000300508600946506015620500c1c403c3e00c0f44e08421700c0c030701c1040d8041000500a45010025041001d2803c3d14003c82140c00240d4800c103080c159068410050050b124410240300340302181c1000d01c90594000c1180c44c28550007124010610380311102109002c8071103840b802e06568800c484540300c4603100d03d10400d140c960a20346082c40c0c61001c50304c1a08055460000303c40307803020150003220b09683c2d0564070a0f15005e0005001c0100c0c1401400c29a041443c7d2030b004600c98844400c0c40b0711000d0030300305112100700144100000d80e03031160012030280c5144a1800d0009800000b6603081d504400c01103540b480c558a0100ca50340e400e80314090403525106400901540c00000a40c000d1403583c1c2a50a442e44980041c0c54001c1200b021a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 651109136 1250 651107886 651107957
    0x3031602120f0d08040804240909230405120712030b010306060f0f0e0301020a1116260c090a14130b07030e0106150816090e01090225030906 62
    0x70f503201e0b8a00c0c60f4024894146241441e4a66409200003503a1401b041e13048010325100c0380b00305801402c8080104a9003409010840d044804c900e030742900384246600c035040c0100401d00b000018000d0b0440754140340308040d10780c03c56003030540d41102e1460340100030901d08660010154402d0180000b45d6002c0d4440b100c1000408008490451500c1030000070040034501040315940d003130000386a00306d900c7d61808480082d80403942e041420300302403032824007800e140812901c9446528540e0b441c1241d000112a244468445420105000d0142c1e03801164070f000c0100b1400c140c1d000c030501400102c80c20641e0b41e01c01c218031080c0c03111030754081d082e000a040010300542c865001440c904648034004a202c0399581114032941c0056290030300400d00c0c08040003049810003140d60301d08440340c580900f200c0d2070003968445040341030060f00001030700080c01601007244903440360013031245c0c03400ca0075400415040c0244401424080ca00000d40f4200c0c54812710443c0c2c00320b51003041d03000b0114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 651110386 1250 651109136 651109153
    0x607140a0c080901110105180709060f060c030c050106031b050d031d0f030a0b310609061e0c020105070e030309040e19081c18060c050903031602120f 66
    0xc918207600500900f43c10400c1d040782c08200d124080c012140101b0402e0745842d030030300301101c1c1c140c240816a00500402d0f46071000811159040040400490380e07141840d510801003802c0840720200040e030090705130342c2000000002c200f00420003040c0c0c1d095030781e41640c0f00c540b60810400d5801007050054009030608142d074800f222500309192000d00002e06500348050820701007400d205924005aa03484070082c01c000d42d8020201c1198000769043c0d0740c00e207000a1181c20203085180720040a05007a5507440303410208655544800340d0083c0801054a6200c08125201c0c050f013800711983d0010750130304d4007044906000300043d4800d1480100590308003002c60007407200038030207032410b03250301d01c5121100d13080c120b141180b50784540e00072112030341c3d2424003404100c04002d01d03601e000c424600e031400303c2c64946000b034023641500c7c0d80844007007400301000e20110741c140500302c0015418003000402031030350310545494203e441d00c29201400d0700b660aa005070f45580810381c1e000c803542c011000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 651111636 1250 651110386 651110393
    0x211403011401030e2d010c0c150e0c150a022a040230040b0f01050a03081602040204140a0b04350604060629040605070309030f050607140a0c 62
    0x208120001c140103c4052401701810f114220003800801d82c48500c100e481c070f4110101c00c0c010181820341c1401c002503500103e44e40c00c9050341140d04140501a6280c920000d0018103016100c15400c004040300407541e0072100907806503000e000d00c44054424400030040310014114250340341d2080322001c10051107544240800307513103d107401b00080b200369440031805200641c9284250b03c1d402c41c0841c035034134140ca0802c19600d00031740510042c110420041003942d40700d1440f14203503030f4450001c6480300c5030741500c3c42000d4010030000358028004100852558a0b032100b40c0303003045080301c02e0f290b01a070b03440b014416031103180103c00d4815100d0015182105040b512081d0f682400024901d594170602032503401c21901751021200d0945580c000c0043c02024036000c01400b00001c0d11494041140345290100d2050780b02e1601404004a440c0091500645424009507001200c0341e446072080c1c502691036020443d42180841d116000009011071110187c1c1c80824454031840300e911450b0700e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 651112886 1250 651111636 651111641
    0xa1a010c020a030b01060302191b290702060a0c03050411010810030c0e0411220e030405030102030405060108121c09080f07240b0114130321140301140103 68
    0xc105a07000300700c4440000001c0d20b922141d83c000c0c5250754005071251004025200d00d20686034031103007004001c00d40f00c044c00095002c0d40144683c08651400440c841103034a030800145001d085400701c20740400c00001c2500454501d2140c5101181088903c0c90814180c003280c00c20b07503018111000c1d564600d42e8a5004000182c0c0141925040c1321509580c2d644006c00d0100c1030704046102041030051000704594250010100c44080781e95000d19a1410300e030060800450201b0b00c1700589440b030003c2251f1060003200d002d814054002cdd5a07900d070909100d6582d000a100d00b01072440b032841e04024251829041c0d401c0203120140110445d0719400510000d0002c48505403a00740d420840401903503101401000860700c21009030b81642d69020450409184140480d4031186c00c0540d10001ca81e803107010b0b503140e10004e10900351074005004040d8240c00312500000c18840c4c03004515101c660050750150800000c65540854986a68000d04000d0200384298020540c0c80911204030f9070098 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 651114136 1250 651112886 651112907
    0x2010908190e1c0302062805060103020405040903050c0c030f121c0c120609051e1b070b15010504030803180c10050409060b0405090118090209070e0103050a1a01 71
    0x52502d00089941d840000d001a0001410484244400c40c0351000705501441402d6018800c40394081544181001c030200342c60f41a84c0d00440c00b540d071400104640e00950582d4017034580500200400c0c0c541e481c01400540c8019034114551040c82c1c0380290900d40015010144058140070304400e0b2200c04810b062900020701080c0220b91b41580210400264825824030080955800030740145140c0300d0070481e00369412105103241400100802d0311780c90030064882c1c1007103800d040f02c1656218500d80556491180c0b41c00f83e040c1c000751060511400028060165804610703510603004a00011341c1e45114900c0700502100040c0002001d514070523030350b6a01c80c5000400d49940161400000780b002c42c6126201020440c080340500602c0b8951007140c0c0039005400b4114981800c010009101c00303014440c00c1c450f05a810035080c2e00c46480d13000f845010340d0242081c3c0180c00d00c680c001e803e00b05600c07032181c0040d14246c0050a48a114064068105800c45102038580c000400440c1e405011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 651115386 1250 651114136 651114187
    0x10501140306060f3a0c0e09010603031b0312091a0c03060a06031a0a080f010e120712090f0605300601051b16030606120c0e060a030203100b040c02010908 68
    0x100c0c0c00705c0e189488907200711356054403a1359a40d04540c1031003219921480080d04000e4960314114090002a82100c82d039a450901c41200000c00d081030b19041b01c481114a0924985609105110003041841c11200c42595154106402c1c199a900c000041074003084810b260712201c41c9100300301e4240603522000307185181088000000c3e00d58008107203814096030203d5039503444140341900c1400f0a1080c0304448840f440a0903015088180b00c401c64005d000010f0031004100c142d8000442c068507440c002028180d005070810317959541e001c0c2041e0015005e400e884030800d40030b00044100350300a01e00c24001500b564826813204801100c06130051401000300029140c19480001d0040009425500010340c24100c3d150031407400c03000b0344006502511281d01048003180008907001c420300140c401e00c030b80c645141e0303840c20002454040540d00203500b501900c0841c050720701150304418200b031300c290741c140854812401c0880c02c85842c000040d150510512102413004035290340341000407031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 651116636 1250 651115386 651115459
    0x120411040b090403080108010507020a15050907080a1101030b040506100f14040e100e0403081503010b040f0f110a02190203011b05030a11160303090201030905010501140306060f 78
    0x2440c0842d0300018180c40035004100d402004022911003409000d82c0039030a44040e010b000380c40d9549880c00c106c074002c6d411596403220001034145e0000c002c19401000414110307400c0308410b04140668801900020b800a400e1034942a142d0801d8000d03203004400141c480c200414a48500310ba040081805080c10001c013103460a01007800b800191020304a114040c580c1c90502100f0001e8901107544410024a02c403801c100201e41c05c000d6141c1e200c1e040d800c1032800c40c00c890700000c2c01400742e03401c00c9034090702e80803002c808a842030b40001d2507614201800c21095104040d060b8513400f4440e00e04006a101500d200c0e401144881602c8041d88068000708040886000018015040340500f90010f0070100422001d00ca450003036403200c0012400191604102007110310015000e0341c8040d041c50340700c100308002c6910950261220301d401030f008004a5851b1100009036810b0b84008921a20481000c64428030b0401211805000c0090040103c40100c0040c481003402c09802141a4503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 651117886 1250 651116636 651116651
    0x10050a0311031614011106072007080d050901030b2e0c0507090506100804030e09130b10060e03010e030304020103050c1b030a080a0b031e07091e1112041104 69
    0x5008201c0140501a26254102d10641d1303980010460070851348042c026034090000e1109490300214160880800c0c078212801c58070919042e1880d100b0107070b0044896208802043c0e01c85079002c400740c44c0b2000242d03424081c500010007006042e00105da43740200c0c5900c821181c8862101c1049812141d41d1400c120141c4c8180d5102c1070b00304480c80d0700480390942c0700c0c01004a24500318441440250003800c00003100d04043c0c40082c070710014000c0207406030b001c001c0440c0244561a00340d00340ac90784580c42d48003d02e000c0c0c85d09000c407801886828003095800c0800301151506018464420144000031401e603034032600110301605020b803464442820420541808a0071110071700a4146128000d55a0310380b6400010b041c5da40003082001c400b0700e0010440c0b0145d4004c243d180410304880c24100c0099883e0030076905001d09a881142214a0f0103400461010104031041444400b000d04014400701e02d180501148103030083c2c255008030307030b01c005030000e04125294904048080c00005850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 651119136 1250 651117886 651117913
    0x50a02010f020d0506180103080313210c02030f2b05090a140f0607050c01212301150801090c0c06020304061b03060503030a0e0d020d080c0610050a031103 68
    0xaa00000f40305411544840c1040224104203824a002035046c0944007155031460302d485003a0700028040340e0740301001c40006130901150040c104504c40c1038070a41c840042140d00f0107800c4641c03081c0100c0c081d00a0641e1204080700100310410240301021303600c6800691a1282d20101500014503418840103102d14035031601c50003051005081d44260008603c0e00f408100004402044219481080300b009040300080d00482c1d540719403d001c5c00d003101c03a00c1a03441d001c1c68040116144181c1207180203a071003040d030f03210400c0c0d100003411000000764076600d13030720003181c0300d9241215040822400d200403c502e0500e0380c0403464400952800c1410014640e403082c040c0c1c3d0043d03505460f03541e00c840d80c1c8640e074002501980c0c07040c0c0083c203042210720b1403e80825280d004503c0d5180030321803204003504094440d031600c200c0c500d030300030324481c0400c01c2c074642105d07907811446c19600f41d4800c14002444103005c403c4180c055440090000c07002510316511040ca580d25400b0440d010701070040401140d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 651120386 1250 651119136 651119141
    0x1b03131112030406200a030f0305070c050607051206030601080c090a0f0c0302220f0605180303030a051e070206040611190e10141602030f1209010905031606050a02010f 74
    0x40c04503540c40034204c0304a0f1132480c8200d0300045c0351415603006841e4401c00281c000d4a02640400d941c240461140d40e0420159215085485e02031302d0380c00f402082142d0194088028018040600b0803050152551010701d40c0c0d4807001d01480049902205820b4030b03600c2d19051055106001c184003241081e4840c0300141543c0741c81d414003010a03004940e1074000309020640b410096142d40d40391403440d01c1d02c9a0f601c9420b103103100300300c240540040e07500351024080f01ea00710700b844094101e81d40c0f41001080d900c000d04017110b008070700ca43c20400c216104845105004e0080d500c90f0b00410380c41d1119140c0000038008081444103241782080541e240c00303001c244248202d2025180c1070400e004901c18020060065180c81042010140452200240301c1054921340c0170030a1400a80500b40c0c80170030b1820005a8040c0e07460700c6000440c808044d052401006080030a81c0c0351101e1301c3d41e85061550b250818083e201662601e81d0b000d0006a10540207030203805010300c001714140002d90303006000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 651121636 1250 651120386 651120389
    0x8060f04140f1c0302190305150a080303060a0b0406080c0315030f0a02011202120c0708090a0b0d150e0604050a0615020709110c15070210060801051b031311120304 72
    0x2034035040100150711038150243c1c0400c0c034281c0ca007000d61500100c0014091541d25480e04402416a10008181d0b1402030150020180788040d01d6107040701d40f2900030720f84d42c2d00110b0754948155010304d0003054501580056500b01c03040c9890b050007686400c0c1c9802600d070801040600840726529854010b03580400103800701240f5200500012440d60000428407050504108861801042151002c8100808266128041c035107a0358072034880346407943c1d40d40724013061941d000080c2200480c041c3c0a820080c0260304250380b0401996003145e54407a0101c80c503101e00c42c0c021902c00e002a00c10305083c4c0040c0e0b4801c40711440010100e48990224041004440c0c603100140d000c2c900901c00ca0030035114102c100c0540041c95803c0644178403c0c00da807070150036040340c03002d510040407481260080200100522400d042482165283c8444a000388400c461010508020131a400c0200d410f000440780035540c000aa41700380d8141d41c941090f65003270f60010399040303105084d03040b0301014140043c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 651122886 1250 651121636 651121663
    0xd0204090c020609030306010e060c0114070807091211040b0a09021903060f0b0301050d14100f0c030b01050f280f0233090f070603061d0108060f0414 66
    0x2a5910704280000c1c5801c0e0001d080c0c92845c0e0080051004c40c1c0c1c2c10003c18414542e08580f01642e4428880346680500700d1025010030720000c036402c4c060301e1030f0003949051090a843d561885e4555070395040d10800c1c954a40054003410202c4400c80450400d0b0f0020042c240c0c020701401d603101e5444022004a90101007240003078601000f00324801680350068600911034001c07288140d03414007440c41e0343c6120601c0340c0c034411035900709500c04100100424104032070301d0748241e40d0080b6101c880c0001178900160344da4400e0f89002416001c7c50301a1040641d8108181d484509195081c10000e0155101000510744400c0031030848520101d940e0003015104090344d9260405040da00e406450003d20390b41501c0b140c0180010406250300b220044c1c2d440c0003418182c40e540da181c400d4070f641012400c600414007030081080220b01d10390907170090800c4400014542c40c001c0a0891540c1c580c440038001d0203100d8200b0000b1418011445c00c08541050140104220710660b046646c0d05d465200c08006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 651124136 1250 651122886 651122891
    0x312050a0e010c290a060506090603220c12030906020102130303120b13020c0114041101030f09050f0a0c0f050d110a120b10090203070c030815030304031110021606030c050d020409 79
    0xc14026114000c0c41b0040c40141c1c2c4082c00c21150100042c45801f00601712100c08441c1c05c2c46450b5400c84400061002d03400082e2420055110701400c0d52424480c071098011030164500000e0007441442260a100301c0040c5103c02c090459800301c40a00c4a01d5500c0d4000b9245c47d201d03c01c9a9030b4814034039114200810040c0d5030150200140d00755003030182d406c642242800d0421000c50852941d60040200c2480c000400707000c030b01c0d650302c02051000d9000d0300901c20300c10180c00703c180004065031024002c40f6017150b1039a954003000445031950042540000c0c1d20103000c0000b403039809110f00000801410181004e441704158180c1540404041e608040c1e01424880004400300180010b030645101c258518a012040030b482000702180007010003041100060f40345035008024889e0301c01c006c007565602c42d5039041c90380400c24040001d601c18000e003010588000d00004000081c20b008c42c0030858107600d411000d44c01041e0b804030480510004010000c60038089100400c05451003d800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 651125386 1250 651124136 651124141
    0x240a09050a0503010c080c130b0d09061a031509030906031608070c08031602010609020d0e010b061204120c02030a06051501090f2603130312050a0e010c29 68
    0x41211481807580220f0003a450050401001c66000100c9548400103486959940d2071055400320049071660103e04418808100360034000003e03009200030354001e000a004030195070321024404c07544040180d6140c0c0c042d06140800e04030140783d07241e102d2480804e490030a01d100010414a0340300f1141e04840703c1d500d0994003c0c00340c00c440403a0700481d152510701135030719480c5c0d9240d0381888050400d034041c81170840c0c00b0700424401d4002c800075181d141c0b41503440748402820003001e000700b003d0700c100d55400d0007004841414070109940030240125a00303031b210340300c0d42c581c5000b84a00c2c42d024030420441484250150710304200c220015442620006000e01d0641c039802c114412482c0144d0400003080c03010007400850f8000503003a5411168803d08001c40310500c581c41e010360f091030382c030a80004501030100e014800c0b090f00c1124007460100e0518160141c0455041c030890309258086018085100c0843d40300d41900103e00c2e100303c03421400c0e04441c0c003a0305030880a40304a880101c507081c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 651126636 1250 651125386 651125389
    0x3090a0f0302091b1602040b0a291c0c02150c0d050901021c0203190915061e0608040f0605090d02100b0102060c0711100f14090f240a0905 61
    0x40c1d03607200700303070502074011300d401608480c084d44103d1020b0030460b9501080351041d035440e42d02c40b412901c00240307403100c4c10f130303507181d40c00c01c0050f866400d03c26241c0b0307104100140003048000c680d0045210001c103d9403118544d201801040903448407421803103050807000f50714420740340305401650154401d030f07240c2c1c0901d00035000781d42d401410714406900600c014800422228140d041280018401580702d82d01c02c44084070598883c0f0f0321351111801c00322200f00f40440942005181e030b0000300107201013920391403961481c041e68621305082001401042280c40c0c81150091341280c0b00e40a00e840d58150f544900d02540c03410b5958501c190070101c0e10220068042240314100d400c4160280102c02c09500040d441e400010000d5004210015034901000340b0700070072921a00000308130a0300301c2c00500300200340100070b04910000c075a048000e11085110203040d960b468130010284680c0b030000a040c480b01c4850348a940041545c00100d41040000c10006860303080c043e0f90320750015914240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 651127886 1250 651126636 651126649
    0x6090609010b011d01111906090c060f08010b0901030221180c03100f0b031c0909050f0604020a0309120f021014010b0a020a020303040311210316020303090a0f0302 72
    0x782c003030600138000503910100b41600142007807003909007442100c42d403800303a0741400d044040f82414480700302c114810f42040020b50201c0f0281e40205100e942907901c91509942c01d80da01a40381e00418021401000241d03102002840809070600d405424014407650741ca0102648100728004c130200b02c42084950301c52880a42240701c10710004040444d2044080381c0c8130711fa00ca2203090000d8545091405080d260303017058141d0300307010b822200c4031080e807040d00c3e0b688003108600c080040c07492180000c500c15280502c60040100b0005a6902d48483c0200300003903022180780f03408d250321030354000c002c145244100c0c181d12006845030000d032101c003080242042d154062500c025440c02002d150705210000000b03064270007040c43c4a6940c0c10300d56003a0700d03001102800940c5444000b0380801086403c002c8031072701c200c0555503c4416690f14038035403c12038119140042903481401010003000c40c46483d8801c0a0014058910302a045400720341e408200385c03c0728903034404d844d008004509015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 651129136 1250 651127886 651127901
    0x905040c030603022101060b040602030c0d08190b0d06050a062d060e030f0d090e0a0c0c03050a0309080705010c020d0503090c10052101140105040608060607140609060901 75
    0x91070104800e60441d800100035a0304001c803003c4003100484501188003096100502600e40129011345a07682d8030002540c0b90b0100380e00302c845001c0c1070354003c4114050313170b80240144d41c404440011540000c1128000b0001011074541c402480c80143c40400da0f0313445018000c03054044041085420f0540003d8050035104c1c0e01c0c41841075150541152040c0c90080d04280d031443c0ca0075180440e00c80e000a40f41000ca000a85554028600c0c0e561070300e500308800300308444d40007060f0101640c4000c0b001084130b000320501d20200c0c84130f1001a0010b0721400040c00640c1c542c0c14001030300c80b082c4e2108403007501302c1c2d03900f00c0d170aa5641542d0740440b901001006100681c602e8400e20314940602000c0c2c40f110f000c00803a00035100b040d0060040790040d42a03601401555843c0920f13030b4008200f0044810085c400c1c0041e083e0801e1840c4290f51280c1708503001d840e59a1528082e64541d5018440164400d6800b6141c1031850b88040e1384c540300a100c42d0b8004d0401000074591404c0c068860360031620072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 651130386 1250 651129136 651129161
    0x60c030306050d050d261503030705060a02040303031b02100c11150402041a0d080c011e14330a0305161814010608090a0b01080706120204062012040303090504 70
    0x261050404030708101c6c080703990321200007002419040d00503000300740385000301c610040c0540a100100030028200f940a0011a0700a54041c0580c0f03912040390341d000c0441c46010f00c0140c2110300145400d09482e0032251a0b00043d00d03101c40181c804d1030345282042131190408100d004000d040c442545441d0280000444100309010250610100081d50391801071000401c034180203d00702038082c1c0203501c107000c2480602d220303c0801420b4008200109440e442c40161640300402044604d0704080e050f8081c1c0c402c030303441100410400a44044000ca0701c3c400301d503000c0701d10400440001c00510070342580703005007a50024100d040492540340b05000b0100e103980a45854120003100c48500385485c112045420301082c030391110b1031403605100c82c0c20405400300b003011000207100d503030005045c401c543c095955451202e00024260060b842140709070400540c90416034494225800c2180ba4004507410840b1450642c010150f08260800e52069020800c908000c0007113042a0282c62100c091 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 651131636 1250 651130386 651130427
    0xc070b1b03070239090910140121020108060d140304080d0906050a0e15090907050c12070c1e18020301090b03060f0103061d030403050a050d0f09060c030306050d050d 73
    0x5188028121309041d084c0305902c01c40440b0007140d2059004c0c80980d002d215064001e000300250f207450620076490a100d0024416546024080c0700e4514880444082c1da05a61382c1d030141c2c07111810800f030350b0f08081054948114029404000c0d000070401880105680c00145c0390904c144a0b024150941551017401440700400400c001c05034003001103e01c0200444050102041e0400f10480e03a0113200400b5401210003401d011090ba04500604010801101112031200c1d103680c4082c640d01030302100601030038100c142407194100e0084400105489462103c6030700b91342e1310603803422a181506130488181d000006010080b0980166000c20005400030f2019007030010303001c02070520500c0050b040e01e903100000340d000016000403450038902001140d03112910b030b0400790b840d110317044400c942760711481449441c00790050140200c0c2d201940c5841d01d5807440d00c401510904204401201015554400428159100e03202030006901500042c403000d1100d000141c9849030541031381780841c0d0f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 651132886 1250 651131636 651131713
    0x50f0105093103030e061b0d0b060d050402090a11180423010510030507121e0903030f230705160215031b0301051c0c080604080c0106050402030c070b1b030702 70
    0x6201da04860047c0c1c1801c0d19103907884140ea41c0440c0104180782000d60721110000300f00340703440e019411080c081c60088412002c1d507200d806541d4219008016100c140c0b503400c1c85903040780c1d0804214000e0f040805400440d01c0b60541e00c40c08940f9001c100c02c0400c1140010041c80f4a0501c1d817401005400d280c1401c002c00e040520004d820185a060120b4146407214401c107102c00180f40e8400d12058400818822040945805400fa0401e21a0280c40d50306d030059201440f0081c1d00b03841610720404406c45602c0e11401000c6078242d0200b2840c0c030081c8004080000143c4406d403d92001603140388080b6100d0400404028101c400101d50b41e07010401840140311503078508035007180c0714280d207140135903400d4149000c14010385c2c164003401080c024a01000140074182000b0043e0030b084000811519841e402000200e01003900c0540c0d40c408140900000034641001203604031a0f84070b44000300c1c2c03044c03501001541e84211031040c01a0000d00c1809248440e408030030500140c00310104501d0b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 651134136 1250 651132886 651132901
    0x3061513090605040b1c2f1528031e0b01020f0606010f11010e06090f1501080c01080c1215010e0a14010315120501061503050f0105093103030e06 64
    0x3298101982048240e2403507032802080303a1032880c40720200c1601d0031510000154000d24240007c9400030502506035201c1440c034021039202110203803102d01442103a0080c5141d6120038a000149012081c907a8811b0b4007268000d10003034030880d140b10004040788000084000901700901400801200d60100c000d10805a81000502c0c1c0003c800b45041c03160002c014210a014005030521070105000d800c0078842560320101e01c3c0408044000300312001410b404c041c40d61105070920031a0010f40005441d021250301c14105140c01404e242241400d02c980d0691804841d58241c07142651102c035903c01c2c10055070860301480c81e02c81c3c2210710980d194602642c0295414440c1b0081c1d04060f0345413000041c100e54004054080c01100304030290f038078000c0c13501b98028078a901030b440c00c00004107036070003242d8131a01500f8420250342101d540141d00c3c002c10b02000d404003412148540401a001142c01032041d101c0704102c2c0148120036941c0e9406080c050119800c141c500384641d00030b0810400b04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 651135386 1250 651134136 651134149
    0x71101030617071a0708040905070e060301083307090e011203020a060b0109080703051516020a0f11060a0518010c24110d0203070809061003030503061513090605040b 73
    0x22030348411310301c0d6109000c48844d80164800c03041d00a04280003c680031072881126071100b407044100d40ca41c180d18440000801040d130009101d2420907a2210740442e052141c0c4105102101e41c4050402c8007408031012034002030740301115090001034003060200411031444039034034010b0800f10004402d040c13654034020344420030790601800b6540c4402000000c0c1e48943c2405000344003030f0040d03a080f207869181c519203400c6c1c0cc0d80c4400040c03c1c41da000c80c03207410030704058802110382c43e0002c040803205585c5054561954513402d803842c24241e40c002005440300001408240c1e0b450b0b403890307690481a40d103007a10150b012402c40c1000401c425103000504c3c40049645038004a0124a080c46c203184803820150800f8458102e540d80c0104240c1d180080d40d130042c40c010103030b58448022594501145607031354131044940101440c00e079501000030038003504c01103400007405416600500c810782400800c0f544418001000320703003e01e070104501c0060344140c41c05001c045a080c00610038280000302c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 651136636 1250 651135386 651135389
    0x20a0c0206160c060903110301062612040f08010e0a0305120c0d020a050712020606010f201b13021303080306220626030301030b071407110103061707 66
    0x30714000241a1859041d1400c041a0241c0c46442000302c00d884820080c2a040648800c0300c12400445014090b80307018080d58003552540d02d02ca149401010406c16035400001020010070700074000b041c12030703141c2d6200420280010081801409103030264403400c6134403000c1c3e03101c8076402950304040026480800c445030f16001800003911615000c060110030700c510384524101d00e100140a50440d5000f00180140c03d00074075000c0d410890400701130780c4848007141c0c4540000d507070806682286000d0242601240381480c42d503680071000a020f5854500050580c002c80c54010a04032890300d0901c0400d40741118404055003481c89a010420889000d40130040c00040084001111502c4002c05c01492580080d520030130f01e42d02c0c40c690001440c0a00032340c0255030603488410107443d40c081c0a01d540c001396400442c5141e296484040545001405a004000c80004026542001103010305041401548100c0a01d032071400003400f244e04c1d80e40050140b110303520f800d80d40d41101103003440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 651137886 1250 651136636 651136639
    0x1d043318020a090807030c05090108031c0e0316050705120f03190e040507090f120503070213140705030702010507080124050f042c0609150102120a0e040609020a0c02 73
    0x42e00d40d00b030400161642c60140d00f1000003441000000014808000c80300822610107581050391641c0b41d80f001c640741c2c86120412120300042c1281d2900014040d80b0115003480040140c030700301403403215041000780400c802070352140d11801c0e01b4031071854080c08030403caa0318800100881d071410f808007503ca0094507460031540d110b04124100680c02804001e0b071100008200700028580404040c003080c143d40142401b555090714040b40c42c84031000c110450a4104000714101070b2550b0811071004600b00511080c42c0c4c40e228a000c04481840e102401440070f5180c40b0748034901030b100207003140c078014000d004000401d03004010380c28010714140c4403680d02c45041402003442036010742e9140f10311101010400d10000e0300283c0c1c910703001043c907200807491111003042d0034214501d1840035020303655143c0c00b4480401048106020078140c0310707528410b0041d6405aa0031004031400d0707030045486007021420012001c105880c1c1482044064031210f08214200b00104800030505491000000e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 651139136 1250 651137886 651137891
    0x8071403010f020f19020313030f0c05060a050309010e15010504090302010b0a08160b07030e100324030605160f050a0309050708010606080c090f011d043318 69
    0x129540c5081d003200100c09000b00055554020844102d1400d40c001c0c5042115602d2899505003042e201008031503842072a00d50600d2010b0441c0c94200e201101440308503001d010183c40041d0948401c0060310781c081054460f9501d030300e01503501130700b900d200a080000b603420603150410704017801d401490541c2c0c42a2000100c585861405a0041c01c00c000041d50181e181b540004480400107090650711682814103500316581c0c81000c2c0950085d0280100400c0c0608c81a421a050118110030442504d150109181c02440c184040044008040b41025461401c080c0188079260041582011204000701004544d884006010082c4042e464040050020742c50072034034800e804c6041c41d03540080035504c0c29a96454000c1c000e04141c03190b8008150a6000554110864403c0d02c00c0310780301078004940c5150700d03801142d078440c240381d004001908a120001e40f580355407140031004401e4040310840542c600c103084841e90300c00019898444087e0105010a82d00032001150151030500003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 651140386 1250 651139136 651139169
    0x180603030507030302030a1d0f120f300103060f2319090c0e01171605040f0f18150c051801050f0705060a0507052812060801020408060f010807 63
    0x24003004d032400700365a0300f511030500c00c10944a0004181c00c440407902c09c044074515801103c070006030340107030004040070020500c5aa414400c82da0300381c40356040341e0b910780c000f1405000c00c01040040c3c01e800a5a80d0356480b200a0184081840707404080141070500000ea41c500d5410b441552000504902d501780c4019001c03424010590002440386d50300807599441140c45024540030344500344511509000f000c264801c48200100d02080c44550304000b115185007000c0a10011f0503510a4500e03440da0368004c0c2c16900e245522071800408102d5240c40d0507240340381001c255007000b000740c03034180e2850803c18441641d0000304641080013103031481c00c101400200141c03403d0061354040024094001420400c026010403031f1849128074540411035922032000848040c0200210301025600444a4410240c41d00044c8619001c052912004e2841c0c0e00c410041580d440780e10098240e900810b040c88a42c0f024400c055220f45148446802fa44c0742a10030350755261070b4841d482c41100d04440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 651141636 1250 651140386 651140401
    0xb04080a031701050913080408100b040b0406080d030e100e0307120201020301050a17010603050307050d0f050702060304080c390f1c1a070801030317040b19090213020418060303050703030203 84
    0x3923800504100050b80c284400e05014280500f1200d40c1e04c1d403091340340800110017440e1603c02c0d00141d80c182001448100c2540700f080d0000e206070440d404180c400d14844c09007589182c02010b283e81250308c00765441d0b1500d4600044401b0a1622907420342e4014001031083c0e07102d4805407412601500c210101042d071841115005114980018101e80000103c0d58280301e130005a01c039003c840740d0b039150b005020344030b002c8030580181500258810b01c1000450081403e4002800001c400141aa44025020741c10352042d40380d81064031072040c0161115803581240070003401d0f2030303503803e980c04072580c0b007900001041101781c00541d803400d5540e020810188900d100c0f08030034050150803055128242003501a08500c800d01c822400a1080f0329800440000300c0700d0300d8000da40c0030014403050b031954084c0d108000054141542300b40e56400c058000b50781c414440620981d0100070060303072070f814002d11980d0010400c4c4504445810b041741080002d0303004045035000c6826140c016225221140e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 651142886 1250 651141636 651141653
    0x20a050403052e0b010c150b03060403200105060a0924260307030929040f0509061509011218050d030e070f120201090b04080a031701050913 62
    0x100050194895007100c01d4141c40b440d040020710f080141003181440c02c4007a102400c1c1c4400c10788690000d40c42110000c001491b51100102804000d0b0010031000401008646042c0c000c80341600050000c82d032584800014001d03910342049104000c0c4100d15140c0c02141201da0107201e07055149a48047d031701c0550007003040f046060085091141400e561398035058406840c0362800c42040024080b440d5885030001086406559242d15a0f02d55207103445440c400d034088034180c940e100d05082d0121140007080714000d1000d04429181400c5040c1003105000c06000010003142c0a416140d600700f424a00e00c000f81c54980d06e09181c0036003410405101d10019102c040100e414542c40440390b80200440403403011010041a6810013124910062031039903035110b841110248840d0a20502a8100e100c009407040e40c01070501c080c0141d9a8903540009510070b40c460180703600401410420150b01655605940701c008004011030350500001915940300900788418156205020404101440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 651144136 1250 651142886 651142889
    0x1050d060b060c030a09050a03150b2422060804110f18060103111306051e0703080114100504140a032f030f060402010f0c02030a0807120819020a0504 66
    0xd4046503c03001c404074040d07680c0e0000c01020003c03a140c6400824a410006d41490032039822600034680c65090650610042c91050400c5401c5440381d1101221001c0724048003c206884003000c0d5a10802076510842c10909400200b00701d0080810400186038400c40700c64000c0d03000401c060b40d0226038000924040c00301030ba901e8000100d011400b02e10600500e4140c801d400070b80f0140f1440c60748541c501043c2c03146030412482075205060a001c040d00c518003030402000d61212a00102401c2a507032811034000c040200d00090822005008000d031010842000c01d9080d180b409801603800b401914a0180380079184d05641046200c0b812540d03510a1080150342220039043e5100c0c3d0310044900d025010503445490000c1d1514040b190304000401d0175040725900050002615180e00465000f0440035070b2030f04000f418280100542d4040c00b103040b020b44946000390b0384054924001c004840d07070f08484424089801d08000458500c0302c40c0748203088022400603034980500c2000d0b1054040ca = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 651145386 1250 651144136 651144139
    0xb03070807112503030f02060c0a0f02070b070b040c120809010305040317010f05040e0708060c090109030c1203110105070207140607083114040f0b0301050f04020108180601050d060b 80
    0x2c50310722801e4900440801030580b800f0f1b44d101194030180c000b0a90785e4a10685d8800d141d42c000300800c101951003100356046200c400e00c16a02d4495403500384000c1e90700010415118000710341c003800100045124804028840120000580c02c8540c50302021401717000420740c14103468000240401d8070940880400d0994449a40c0003540c6407992650702c81c00b18040e0380d010f80c0c58100d40c05901040020190112005600107000035078079246000c0003a080800850306003d0344101c0440058070300070a04026040c1e034941401040c0380e83c20000e050746c0070661032208a91403d418081c0c1541d0100b2040d0903116030700c12880008480d0340110703040b40301d80e1001402542c0003040c1a821003000341403e42003108443c1c01b10440724028038095412012611a815169070912000c10150400760480004556442d80014211034000082401d660040310b000210b6403040080104541c0c1103410180c03c84410241c0240d0035148101e01130b680d2106004062040040d000d50b0b07400c0040d69000745409150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 651146636 1250 651145386 651145423
    0x70503010510140a0c17120a021602030706030e0d050f070b04052415030102040e010e0618070206100f060516050307020a0803070b011520011401120c0b0307080711 72
    0x2e0100405e01d0080c5481200c0341c44007451046000e0ba078480645000c2c04580071110b80685841441400940c40100c20315031803030803515580096a002c1c404400200915200840ca0703802c188600b50410b09040301213030900c1000e0100c00448074410f0140c503800341e031001c103141c1142c42d1414142d162030700703c80c807210301c0c801c120700500000c017aa035448600502c1c0510030500003141d0501054241d0040e401203101c840c2c0301c1d07801080380706084038000d608140c016012143d1402d1120074100c0848046400b0009070b4000014440007003aa641d40d20700030002c00028220380c0d424090010641c2c41002c4440070b103000d1024050090240501c1100d600300d034010081c07207c03959030342503880d12a0400003042d10848240c200010b0401d01e1480260508085907981480c002c0c254a00ca8088440941e040c42541d9070340c00f440c3d4480101e049055028080c000300040b10990350740344c402da41401036040f20700c26032818410302001c41c0e000805a90010b09030b00300341c01140c5944506600d06550418078459004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 651147886 1250 651146636 651146647
    0x9011103192d0b0103390e030d08070810050a06120e01022a03030106140a0c0c0803041518050d05031c09060c0c0c06051b06011d060907050301051014 66
    0x81c10743c40704641036000e80341402180b411122140100041c5140c8110280030240c0520045840e42100c101d03040042c10080c1244182c880800c5c0740c0000701450340045070340e070030078003902540240c0b01c01c1c0e100c41001c62001c2d03440c4c100030116005103401c0c0709500501c41c0c030031800c0040f000250803e104c500600b0008540340c121102040a06034010f070500d01110746482c0d40251a250301008a9050300d0640d01c400060f01c009a6140700076901c101c82d210304104100032800002240c0220000007440003400850304c545c1442e0180000486403030780e03075081c40b0451041c1c8120300341c0303101303101c080b44c00807582100d41d100c03d0304001e402c502c12400090400e00505109144206059001e500841d0180500b0803160a884a05a0703944d0f13010300e40a00320071106c80e01040712a10490040c004c100c3e05200d0718644002507103070f803498070708281c120050009503441119210b1404200b0a80e003d9811a402c610750704004101810511060040320300940c04180c60b040410702400c603002c22182034411590b03403803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 651149136 1250 651147886 651147971
    0x319020a1112091005070f110d05010e0d080601260702010209060703021f020705060f0601050408010908070209070906051c02041d06040e0d020c010e0a0506040e0901110319 76
    0xb640460203d40c8a81003a07000f01c28840d108000b0781d11441d9101a20901c09042510b860b17001c0b1038401e990542c00300c0181c01c0f1400148003070095802007440c20000700141c80c044000901414002886c4034104600003a020000582c408003100c5c4a1120f0720b580416501c0d2581c04a019102e000d01207600818006503c41c01c269000454071b482c001d0202040c0700f089040080c2200384d102d002c82c003601a0f44154045955508600905608070405040c5985025907a01903d420746810800580b4240c2e40801d0030404d43c2000c2c5084c5030f00042038071b4041041400d0842c094001c0c01040d9083c0355040c0d070144c56621a11060f4120740c080d000f0b41102d030003040c1c0c800c096003e0794081219000d0017641840117880080c1c0f030007c0e034039411100c84e801818868031550b0045900b0090030900350fa0104040c400000d090301c80100130000b4000711a140500c626100c0c001a01307542c02a0480c0e030080104004004c0e001e00c04401302568010080350205072195004c403890101d44170041a43c2001c10503c51102a0f0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 651150386 1250 651149136 651149173
    0xc0a02011815200d0507021e0301050a0204051c03080f1e0f06100311030105120106150513080c0d080318070609060e0301020909130f060519110319020a11 68
    0x3035000f9250f00900c0070507440b0155403590007481c032460101c2c0c1c003844100e00503c2d0040c01c21281030749280060040060032030009084d180c064825840c62a4006018000b40c2841118110481d03111404c2051601d80e0390383c01000c040006040240104204001c0b5901840e52035028604403c1600643c0450400c1d4040030b202c41e02c1540e40e603215010282d42c00c84454000c0c02860424030711190f1007401c50307280c2010710000410b0700b64009859581d420b030208411010b10300281141c08030340e5501b6100c44d62403031107410f00040d0b5048060b081d0f009090350216960b0388602641451b6004680c84e4803034807100040061803003a0b106540841c001d010f0045451580518520111805d6070750300701c0c020241d601414202c3c86540284c5070400091000104000810120148040e1140b0780c040011000c94680d2412140280d840c0358070303000c03540c0801550f40094010210f0411041141d5031850a240d064070400c407502070091640c49402090f040180c1c0c1c041c212941c807828200e401e403000d601c0000c0f106840f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 651151636 1250 651150386 651150407
    0x11b0c05131e0e0102042102010306230427030e1e0a030615050d06090507051005161b0902030108010f020304050a080705010209040207050a060e030c0a02011815 71
    0x5010040d4142034600d05809819156241102d8024461080c0d04042c0041c00c0c40700582d0840b590200030005a2000c0541442c083e03440400c0c0840d0003440920005064a8140d0f02890b0360244002103294202d18a00081022104c11500007409800111143d103055140342000e0210100314465441490b82000102c40c800700d08880e1041c4c2c400d98016583c1d100c3e507801e070003e604440c42c07071001d0001a9040d404807058642d28815041c1d200c2c0d50740d0004500402528003210b601d512201002c040181c03c028007406010116840d491042100344020954010010000314619500c500c080c01d11090824855860419424100703240e600d650444029520a00c01d1856a61030489480c0d00b14800344262401543d0010182c008042103403200c2085811800041d200c070355082181c03002603503451009001462148000e044580038501340726003158070108648802e41c1081050000404000c00c4170101103509080940c200c0030311640c0300400c0d965640006005c101114490600103402c440c1203203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 651152886 1250 651151636 651151639
    0x1407080403022802090604060e0c0a11340902040801141305031210081006030302060a1e0f0603050d020102120121060216020d1209091b0e011b0c05 65
    0x691810b104003200c1400103180c3c1d0014031504205000d5401483d22030409600580010b00128074551034010311900c4803001d440340c8910143c0001c0100045800c001801c10703c6241001034102c0281d1101180c03c01c80300b01d103415031700c4a034003544180710b03d21008489018080303182d8119152501c0d510214000d080306007007414082e140800103400b155241c00006a50355002001d94200107181080c445007810280400150741c2001d807001c900709000300702d515840b2510101c027082c11481e40c10003038202071000e0440201c2da130401a5050040b0034140008059030015403001030941c9190401c20018a500e40006102e1300a4030103406840f41d054001e0590307216a0003141150b80d0b41d0319145451005884000c40c54511080000400300c1c100303901404a02280a43c0c07031182c1c1d4490740c002611821240c6044400d004100e02d81c038501a4001c00384005006c0043d01003014010440040c4070703100c0c80700054820050300c0e101ca2450350344682009442072032070300b502d0042040360b8900504548000e0107010b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 651154136 1250 651152886 651152893
    0x60f030a060519150510051c05090d080a0c0903080922200c0a0b10031b06030c02071409040201030b0d1203050c0304020f040903110304060302190203090907080a140708040302 77
    0x81021110f8000303090817100001c100d90044082e036441500d858209012a560120700030713940300c071040d903e400340c144561000005819499a8040d0281c82c00c400501365030307007452410304100140c40d006107044042d42e8002d645170342c60b0f580c1400086d50300310742280f0300b5504000f0803021000c10010342d04070b400c9540700d07d0000c03081c071a14442502c07250f001d01e000642d01e030f51085072100d0100700000327060b60300726440d10700710800d068894441451201485803440074120400d1705c20031031103605100d00681c032245803024180c0240380c400a02d4180000303a003c030384a1200d4001180c11a0300950190f51610006403c0e4100c401c290304200f000024042e00e201c001ca0306200000d40041e4020701100e201d160300404d04081003500000f80700040070440c0c002c5051003841c0a0f001c80c2900c04101520042481d664003507594502c0d00b00013000907c0142802065500034804585940d4540d03802d241d008166180050b466034543c40108054104590880c0205200c00140480142d10410341e84c800c038001c0c1c084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 651155386 1250 651154136 651154151
    0x1b0c0604060b1203040e0901090f0b070207050a1d1005090115080c040302130b0f040f061406030609161206030311010b09090304090902060c0106060305070212040806060f030a060519 80
    0x600018080c0e20a0000f82030304104001d206124400072210f40100c124400091091125502c26100d294100301c1903441c003503000b0820081590400504020340020703950f070b440283c0381c80b01c035801f0143ca40d08030340d0489041000042c00c035003003510028000c02c0001c0090200d560742e031103903074004e40c002044400058510b0380051300d40d0038aa411a803c49501030014441d2228103520100104a860701281d4454003032030405e13100341d899020300c182c092600c0000060312841d0281021004080a5807174fc00f6100900410456559400440da0f0180150000c03ca00c443e103203000b246c0c0801ca90000e031194600e400004400d155202d40e81c092000300f40c40003004910b0554041040e0005c0c1210760750f80780d900801003400b544802e82c208043c003e102803c40d9003405c0f4409030a03801d441d0160001000260383c0c00400402540c100070b00d04900e00f00b0122a460b00f4103250005490700e1009204034003600e000443d41406407010231444c4e0100d90491010082410901d015102140c8081d02050000b41807000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 651156636 1250 651155386 651155389
    0xd1e030f0311090d03020c1e1009080c06090d0f0606170606031b0a030605090f0c1002030702010f09080a06050a0c09050904122a0303050c0306010f081b0c0604060b 72
    0x742c248101c0a03a0410b0b0501c8030346020040020030020048085000c1c1c070200308803035183e207a65206005807040c1082c030003040342428451051340d4085030808029401c0400c002da181e01040c1082c40700010707103030340d65582e400341c02040903a442450000e01b038007109814075080c8a2290b0040056440c81c1078003200481400304c02c1591140d040c0c50060341508001400c0c2c03a01014404428200c507409041403000b0b95403511600e00300e41049800300c0480d007110181704e904d590140100c0704c7c0301804071101c00861030308503c000e42d42d0082c1a402814041191058040140680ba1800040c0820422101041ca50f8544017000c1c040941e90090507600b4601020b401ea4010a40707082502c0c0051720010242d51180c90311000710082099500a00c90707081103600c03200030303140b84010a089540951508400b09490001c0464500821401c141e200610600505a034009411109d459140c1f40407103460b15a0352500c0003d00510f42c904030481c070002000c26138200003180386840749000d46000c10a0522000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 651157886 1250 651156636 651156641
    0x201020607170f04060b0411040305060a02071a0604060315020901020601080705060a23040609030b0601080c030c0a0e06210109020322030201060b030112020f10020303150d1e030f03 80
    0x803504075010100d0310004880c01c0e200700d00b03d540035015060114412078104045021030b02040707800791070640c00082c00e006006041140c0c2d80c00c098040d0045144c0317074050321f6104104041c501c084230b0f519106808207050360380319001070b0040c540040c0414002e00019107000000c1d4402100140035004a500004040c2c1012842104440700541803d00d40ba0074030004844046c440b001c40c20f140c05500b9001c2e108240e444014101070b001c0b0b0b840b584801030442c180403e038840c0c000d044604200c0300000700691501c503603003075a030001c50500000e915032000e01c1040d101d02d045052044d030000d0300403801d07004107000022031550901800c00501a540d80b141c080205911040716005040c0d101c100ca107142601402040b580010700a20000070b8258413001030082941c02039200880d41400b500e4040194a0492146c101d948821101103402c1c05ca00708002c0d440e408002e0000c4003152903424038a159440741040308070b010358030807110b00c0c002506083c04010703504114003d80007e401900300741c00040c06032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 651159136 1250 651157886 651157907
    0xb19030606080c13080303010303180b030601050a03050408091302040611010203040804350706110c0924040207050a0b0f240d141b180a020708090a09090201020607 72
    0x55840b03010740d42e590300340011940e01c03104031180f800c046a000082d0540c0144090341c0030307501c290b0b901035881c0b52030380040403030310440d42003210920420428440c40717a0b00807048500307200301814040748c1c0d55641d0800341300d240907580000d0f13006803541c46100790750a1107034000c10130303100e02e5103400f03501c50804070a441c200d010072500100250010001407101800e08a0551109810040e44243c102c82e1100c82181c541e0000c224144140c1c4604810301500340c210350b684c0c1c0c146080d03000602006103100000360300050080c0000c102951041c1050781e0700003080d40c150008a00151003556280c1c441d1510a86e14900c031002078600c4521038001c9000c613140901c1c124056030740c0a04134080c00b82e0998800d9001101480d5159010340d0003045000004c00c10b504418400c445240908900031000e041803030070010707841100344145040444032003280c00048165030000d04032000140c4500c0e0030300c1c0c01c1c2d000c1e01c11001100c0d48506240400285038000b03400002215200784d0a03a0341e01d0f281d26405a811008a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 651160386 1250 651159136 651159149
    0x606020601081507090b0313170901140915070302010506100e011709030408011d060105010e10110114130c0512030a0309111503010306061a090d03030f051305010e03090a170c04060b190306 83
    0x3076809031541d10101c5408dd01c64640700901c2c07030f105c514001c240d80b0010f0380100b0046025035115010001d1f503140c1051403a8002015040500c04584900c0008140128072030361094000a5003010071041c0e4010000d441c00b400100000b0004160a0228150342d1038068038041c0040c861400086484c1d40f00744580a0480000b600d0150b813a94900400d0b9084075400c21454001e40d0b8500554414008094071075004181841011710302d40d141703091045255481307400a6009582a03140c0d00003440001003100d080b049503180006200009191115a103101c00800991010848403486602c9410200450407a88500010010140c0e03c0401ca80499010514110030050a0045a15a00302a020b0404480c8079141c005940580c0e0f0540390211030081d02e003d2112103984074044200f0000f4861842c258081000450818000d10002145843c5600a001d02c05007030b046110700da2142000704001c444001003050101c3c1e512501e000150fa0818141030641c03004500031501014040e11404094502 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 651161636 1250 651160386 651160397
    0x90c0504061a0313170c0609060f22120201020909070c0c0b0f0c1c11010b0f0609010507080406030b0418020d0b060310020f0c010606020601081507090b0313170901 72
    0xb001c0c0303400c80715801c024100d0b0b02660038402e40c0800508010515080e28500c0c0d411561285840d0710b5a914001c0000c0c0041c01c03650107002071080e0f401c0e0b0180c0b55a84070090903095030107112440104e50100c1c01812000f031104850403001e180040e01900a0801008255200d504c0c680d200340d01118550302c9454007520040e00300354188502000c003c000d0004052421100d4601002d1003043ca103003042c12a016901e040900a90b030604661141440c8c0782c1ca101d0600071301c10034041200141d201d00070340f01010f10401c40044c07050944e900031006d4500d803c0d08400340d26151a92407801402500900c81342c80c0c070481c0380004043c10500c0414283d070107244c0103440c20321501426070b107401301d000380a00511b81c188204801c0c9425504540020301c5502d8a90001300c1c3c480c00002c12040c25a80c00e50005404e54202c0d00040c0308048000a51144031032988011a0168444000603640d402c0c03660440c6900304400000c02601d09803807081c1c074051030300c039030039403006001d003040502403600031802c0c250300290 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 651162886 1250 651161636 651161669
    0x5030f0c03060d02060d09200319051e15160e0123160b0114060a08070e04110a02122505010b100c06060e01060c0201081b0a0201090c050406 62
    0xa0a000e0740c0d022401a184400d08001074000880c1360708001030001c45951124814010031071050b90501400c442d000c03c107400c0d41c90042c0000c0e2140c2060b49101140d0901c03842c00710501c1020401d581090050400f900c05102000b000f1644079007079103181c00d002040c1e0a0125610900290030325504500a03a00d001003c5462001181c00d1841c00b9280c6204101401096a111002100510465100005155071891075140403071241c68164000c44100d4903032507200c1516110700003101c50100840c0750041180d81d03015401c0c2d540700f1581a009400c02d01d0948820307040c4020343d000f0071100405400715981842c80700000016032144280d00075503030a59013801800380e01c0c460345550740304c0e21034000440c90704851808211310141889030080000e213603e044800340241403240f00042c240c04200c1413203d40c10158060b00e4081e00c3d28000741004280c000058107605090305071004003014001099442045070b000078083c1908040a450601d02640001394526052168a00b12040102d2015280707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 651164136 1250 651162886 651162901
    0x5040509060102120f0a081b03190612120e04060501020705060c010603083106020c0f03190506070906023f0406050d05162a020303030c0306010e0105030f 68
    0x1054040c040c5415807013400d44849450351004041c0202e81104600c441e00e0300360740417004180c8a0080c1c200100c800620b080611720048000840341e000903405d9112500d00342c55020030780240f0b203641c04002c80802a42801007000360703203902c01080070340c16500c900c154131840d0104400c481941c45098003607484100e0411640c2042c0f4090101841d0850000880359500d440f1404a0780c02890742c90050300b110529a040440c001ea00b294031000f01c1c2240072007403400c001c0040d640b00c001110051041904018041c81c41da42000040c12040b0055071510315101d545c90040c1e0b598005540e0764001c56041c0c0c0d40410580d20028030010300d450b031858004d02000c01c030020308030800e1004a05d92094503141d40c0404a20703808000400062000c1d0792525602c110750b02071340d8110340b03002d41b00c03040c420b03c3c403544040c8265103ca0714184200400f001c041520144001d031010880034224000d415001c08010041824907100280d0321440082e01c409802d48904001101c403440112540c104100c904004103c0b03c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 651165386 1250 651164136 651164149
    0x19020a0b0f0f060f0f03030d090308280203040f0210020a06290f0d02180a060f0513110409090605060a050301140411010c020d060213090c0c0b060307030803090f120a050405 76
    0x15002502140f4401760420209080d07a0044e003000c0f10703180e01c0c0c54003a0200b65200450550000ca405108801c8002c0c10244100c051048032441034a00d4020000c02c05006110821305903103540113184c1136840c180c012010303480e400380040030365a880c603004051031309400450820308490000300b0300c0c1d1114004601048242a100d803165034010803c80c13002801a01d450301440c24640d006001042c0c03515200004000745d44242c2c00085118101180c10001038950300f03006042c001d0400400702c1ca440701050322074403902940c0c0c0314003800f6080c56551010b00030341b548070740e01a10303082e941c00101c2505c1e1024903081c4c542e4440105014043c0b03100140101e4840e04e64202003003014500000404d04640000d8200e944000301902c8055000034180c4003042455650300041120344004e101c40d08665801425180d160540500007824040c001545964244030200141da48290b4541d142e040012085030384452242030300354140700d260b48100f2103960040075540075003429501e06240c1800d10007840300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 651166636 1250 651165386 651165409
    0x61905041104080105070206090105060612060d020d05061503011d030f031302030703061e0908031311090c120c090f06070816050d09060809070b0c0319020a0b0f0f06 73
    0x800d007824000451418003c0c010345000340c090b68018186401c0000030642190000303084203210f01400c02c1110b41d64010303035007015400700342128511700840c2c4070b0012600c5903030350100003003686c01288100640b145101504080b070700b40a9000304800e00c0c84007141d200c42046000018002e52040c0100c1e4007032040a0003d40e480012500f0381d0072a201942e01180c9041c0e00c60b04111169034480002e0444c41c40c00c81c550444005d20327004d05204590864851142034800581480d8071540716000d58001c0c80140d005002c00c0680c0a84004142d00c2e0010032010b4503003080341c40c1044d43d80e9400c0450340c202805001d4551000000305180c00c0303500da071402c004090f40b00304800c944900e010f00c414844800b2014114941502078030107004c0f02e2000e010020700415484d002142070001b01800c2c0700381c00800040490555241c000d00554540c0e0510126245004a00b151014407901d103044c490340c0359020500c000098480c10301000580c0701e400000b4034000782200c1d410002c1200100141d803c4c1340c00d4144c482e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 651167886 1250 651166636 651166661
    0x201e09010c0b0406050106030f0c08010312030b09090d08070504181d01090b04021302310321090b07051f1e0b0901060206060d060c0e090703050f06190504 68
    0x108444180c0e445546100b8111010b840c0c1da5a1a0010440240c0502924040780c0303c0301d00400c0700c2144080e0261064a0600018007000f41c10420515907074029445a5603c0500500440a81c5090301072295074045441d40c0c2301c0010a0500410882c0d4001d5045d141550364480340c0a03100b0b0300141201005182019a440740c00748042c42e000c1c507260302803150707100c0d99000e19200303c00752a150041c403141d41d40c2c03406401c0c00309204006065035a88412a581281140b021705403507280403240582c014201c140c0c1000c0c015210002403960700074080000412044096107502c402a55915082e0515005880c8060030b1174110110b4903080800d43c0f001049540d20111002403080342c012040d05c045065481d514910300c0e66a02021020300e8641c0142d8010039151006000380c0c5807041c00310b805000c3c81000101015207031355800321200e024008141840201812841c858641500700802511050f10100740c04e84074980418120f013803d081e5001c0c0d0b04161401818458605014031004014018140c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 651169136 1250 651167886 651167897
    0x4031b051f091a0105100c0213020f12060d080702061c060b0d050c160f1113050f1003050706050c12131509031104050a0b090406201e0901 61
    0x6818003250510704486034a40318000042444091405034003032914003290310211010100108500c0c1d88140030304a03610002d00d00700e0340c050300d1480440d440c0300010b04400f50090020a1003e61074107801c020301000142034400420a440c1c04051045054490300050200c100401c981009820100000d2229420a09202c110b40c8060082c0104461064200c6e14003290006411608041c2600901d600400c0d400441450062600341c0d16448441036040140242e10b482408000d20001d40720344403080320007030808064604044188401040c00b20740d80503445020201084901115150050030b803903100c002071006034105141030780c00d031308140820034080c0304039820b51242056100c05044469942d00c0030781d03c0c09041559120503404030101480401ca900c900c104080340448001c2d01115a00740c800042c6600c59007440409010202d0016030090041000e20042007040c0c0e00959043c0380c496a00d0304034400c0b0707507441c031461721031951030440d42c81600045072080c02c454401411049014100b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 651170386 1250 651169136 651169153
    0x209070c2102030a180b0901030b030f01090f060c020a110f040b0a08010f0506090709030305180d051b0d08091908070f090606050a0c060903030e01090503190804031b05 74
    0xc01c444204100c4407005810200713607000c809801042181d8548021080b480a0500f0160340510b180038a0030090b0406072a101e00e10070a0700c00323020b1031501038801e40090050b10380f40e0803c0104001c9500d81155014584a41e24080500c045445008076070b012040c1ca00400d203050400c01c0c0c803200c0040040c0c8c41940c400e0460b550341e803007808400007040c2c008008254406c08001d01422904000c141a0056201e0ba0412030200d50045800c010350303903d402c100381c0710a00011039070382c0321144858107604170b000c0f9802c0105101001410620f1896031a02e402032610114042c00010021100010300507101480052101d282000c054081d08850075540003000d07070799400d85854142c40358807070101240c400c0d005003d10541c2e03000b8040640450300307240c0d280540c9441c00410014a800e80a00300a40d81c2d036000381058880d420100382904054024400e83d84907040c0740791030b40c0c42800e4044885103440c0c034a0450314002d8086912440d016150061802d480d442104d5404249040480315401500305 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 651171636 1250 651170386 651170423
    0x40507150e1c1203020a02031603121a0a051c08070b090d050304030c2004110d14061518030d1115011a0a02010b06030108280209070c 59
    0x308988603560300e40d40c9500c2912154140000307400d051240d00d070105111a00800400c0340003408003010b0030945401039860300c40d02d10881c1180a00015107518800c1104000e090643c00078041207501042a000c1080621440356042c03102c6802c6100c503048000004200441c2c589100400c04540d00c8201d001070500003541d444920794071040e402c50712041e0803000d20040002c1084200d0a15006003800da00e58200ba40300a04101d04c0088000e01d1034680341d00072035407400039103100c0f440440054828418658014100d1845810031560340c0c168600c2d0481e1100621604001c5500403800600608001420003000c880d2581c8400011003070b0122040000c811520100a040c010030800d5483e1013452a01e000e10f02e080c009400742450141d5007070001441042082442030211344070070411540e0b1010314000c142d0240c50a0841c00781d2080010000040340440400d8250824500300e0405001c1c20011003900d02e48170b9800c0020790400303145000141100d005a60142c903040c000d44407500710080e03284 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 651172886 1250 651171636 651171659
    0x903110706090f080615040507020a1202010c11030f0415020307080f03060405240f030c0909010c0e181302061603030c030c0e030a0b1305070909150c1205040507 71
    0x3880320700001c0c00240100a4000a005810083d243c0e80000d00080c0c10080d020031280d665910b1098030a03569140450840c078000c010b00400d0641c022078003820b002c1c0085c00640240508505040850088214045075140101c1210103003048076038260305044c00e124141131100f03034840b00401036210801c510004551144090884020003402075642d0349402c806100075510090300c5c22413000049203140da0003c8428101c5074003ca0144c1350340d0141c03801100003d2800c0034800c0940e0b041210482070060038401034000702001c20b150f4840019506c0c01d10240012200e41d900c141003e4030240b408500402121201c04102c03a00060406042c01c0c1a01520300542c1400401100031a0782c48840414040c0c2500035034032030007500d040401b05a4001c401180d22114000c03002441e030205040003c6400b15610a4610102d1308041128078098a92a10200600d000c1c2d1003602c0d0b400a4003c802a0038032540602000580140d45201080807184c0005025110150048400303000c0d110007c00c0640761070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 651174136 1250 651172886 651172889
    0x3150e15090703061808090d0312140a050603030306060301030b15120c030c06090a05060d0e0316030905060a051c1d1b030d08010303050d0e0a0b330409031107 70
    0x141c0141010925514003401100ca03c241c00d04080b0704880d40720f60100c1c2d0f1800c240c039075021081d501c21387c64503107610b42204d43c0d9580310050511070f0b191200120000741c000541d2845054101420041c2d41c40da081050350341c1c0012500303941d11920400042c03000502580a40f41c2005041c00c0d400c10121600d40005c8100b0251040c4c01c2d01580107107852300d0789150030800003440860990365149800d80c0d4030003041941040d402040c2c0280000521714200c0c1d0a55405081a01052010750313072a010904c507041220000010181e001070103048010542c1e18003403080b1140c2d80500d440c1c562408050000c2d00c1d103500d5250100c11009a5244005442c103015030004610000c0c00c6005841314054225102001c1080e000e2054025400780d9805002150071640460543c1d4143c00c10640340c01c0c2c20f030800009070030b10340020b600c28000c2c050200200315804954a0250602600090418180f00342440107032444201c0d0907030001c0030440c00401c90420758060b47d100c81c000d14100882c248501701052030800c06 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 651175386 1250 651174136 651174151
    0x23030106110c0a0308090d0c0b130e0106030e15060117700f0809010b090114060f040b0c0f0d0504230904030e01030e010603150e15 58
    0x354030740c1d84508080c0081c580c000c104030389040016085848100e100d00a2143c1140a02e00401d00701c010300c200540e1010080041094007039030f4008040200d0210910b5100e17403800308003c0b8001045250190245607080340e00200201095011f07180c044105010241c4841e040c09400700890000c440c00580750303031088a80301400e04c03a0000246180c60390b1201c45154550480304c018401400c2c65041c1c0e011402e048108105540c0806032840000724030001440301c200c0390505401080009070040b080c80d41e02500f5072540106070f664000c1081c2a1340c240c40d10b41d9440210719005128201c5501007039020340720080e000b0f50800b80d4074560760585038065000014244d80c041440d030540e2000700004c074241c0003203101600f0340d10315680000d8464043ca0080114110380b80000f4016045502c0001d51003910003001c0e99001c0c141805c000c4c002050000156001a041403020b070943c600c140581c600f00c0c2c1d4002031102e41441102040c3c80103055403404100e041c005d10701c46440110700d02c12030710301039180d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 651176636 1250 651175386 651175397
    0x70303090506070f0504030b15060d0b030c271503010e01270b01171f1d070612020304110a081c1d0d020d12090f0b09030d23030106 58
    0x1840d0810700d2405500402032410080e40d01c00020150343d001c01a01c0840b5409410170b401d640320701d10040d0403545a00540c980082000c1101d0545082907002104140800c0c0d055401649034601403021100075011240d1a204890303001c440b800f2103008200b9404042100d031a80c058024400090030340d46101100300240e034541041d080b81a01c09441a0707801480402c10203462201a560055181c0c0c05116903c0c43c05462018a007400c4028491407105441c5448218440a4188030f0300c802442216580d0080400a0307030080c1d481a0001060001e4841580790100034250400d0f061000c2c0d80014400c4907914440481d00840c5e8441c00c03881d601814454000d0100300c920302040703d92100744819a60100090702440b80d4103a0507000e103031100da10040c3d64845500c003440c0049107140c003000e000180660400c1e203004507401d500c0402001138404040695590a82d40d00b060500b0b0f000340403600e6070541003012400b40c6a8042c40001c080c507462910400125504000000c04640090f8844c50100381c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 651177886 1250 651176636 651176651
    0x170c060105090433050c03070e010e240c01181205190804050109051501050f0a08030904240824100b1b0319030b01020a170d02070206070303 62
    0x100610010340580026a80290b4038541a22182038410410b8a500c3c8025610030340d81d0202c00c00d2090301000c80d40301010911041c02c02c22046006075004446607400034544400e00302c0b01d03620a242c50040840c2c014900000754500000591481070441c400381c0c0201000c06c1a086e92807000c0c0526503d2403540d400e00c500240181c20907112101904940100300b28041007030600c01c01701c5201000c50305120703181c441900d699a1070f1141c01045805d2000e0004e1081915201c100d0500b000054145c49003502c948101c80140130a11203130911a00822005803c14030990800381065030100a00307903100031180b280300081440410642032150000066600050172541f0504501e180c2e12420f05110307640520340d03142a82c0c55a0a60700580103800f0a184009400311400c3d101c070039000380e00798400e425241e407854400e00507040c0301c5041842c400424145500c1c18000d42c0003080240c07000b40c00900084400001e0851622954000c4000440b00c640c00c2c880d62016854580141030014442d80300001c540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 651179136 1250 651177886 651177907
    0x1020d05010501051303110111010f05060a0f030314030408070b040c0e0f01180f0b0312090306090c1f17010b030405010e01060b072303030907060909020f1605070317 73
    0xc88050304064148903040000301410b00802600004590700403806000c00035580740100c0d00300481608001d255820504c501b405840b8644c0b10b94003e0400b200c4405c03a490340c172042803224110134880600850840c00108418846520003903901c18801c0008500d000003954031901d103248290760940f801d00d00d90704140f00f0494003003000c0d42c0148a001594039a9850300c0d008500b82e0f840c1c7e0a400003201d480e1000d910814800d508001c0c01303804010180c035480c086200101e0a150460b40030184244038940103e0000b010200d24034408440280c02c950105801d000c0c805210509050300d42c0401c483d07001160004034689200901078030280e01c0059403401c00d030030810300b9155000d1010b0010b0345080010003030340c20207108590202e41d0208564108a004804240d0701c101c081a0703041050100004000c1d484001040f00f2068031115101d002007180c07120204e1089001d000140d1040140400c812480244516000700d110b510a40407954201c3d1681e884a03000e00000365203800702c1d00c020034410b814 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 651180386 1250 651179136 651179141
    0x1b021512150f0d1101121d10060303020a0305030702070b03010e041101111e01110703030e070e0112062a0905011b0f08091c080d05070e15030903160501020d 69
    0x1141000c0b28008410180350780051103107a4800c0d0010891411054201c0c0f43d40d000d8a404454043d1102081094900034055444040c0345d0303050344403003802010b102080700f5607148a07800c243ea40580c010b008003000c40c0e409590303590001d4401b00c150b210f0040e00081a1182c10b0095001c0c0642c08100c41c524106480e09070140519600310a060010071140b5041481c0005900054440030344143c0700100a1b88201070300426403102116296100014030764149601a04403c910066010440f1740d036a07560101d103221040280286001c6010703200040d07004c00c2d80c40e0800303100000b2051010b0351800455980c1e40c14400303951019408034910384010403046da0014405140d08518000d00c118202c400e5507004444015050000d059030000303e007502700e0762994000310040b4500c491b040540c030001c6041024107a000034681d9401542000d0018038943c1c802c500d614210303000500320386603400709014041c07240c0e00000c0448009200c10701000341d005403503400200b034540c040c03000181d9a64449814006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 651181636 1250 651180386 651180421
    0xf01032913140a0302061f030203070308180904080a03050403050c1b120c011e050715140c0405060d0504050f120d150503030d0504020607150b011e1b021512 69
    0x1041c1c02c03040030240031903001b040b002c0e0700410311800f00b00c2c0e02d1440d201c0030492007203940010750944600403000c02048403c1c070042040301d010003d048448000c440400045040440f0020007280e424491801c82c5c502035085150424800d0420b039082c002d04850841c83e256010f2030030070604089411001180c10100302d8141905410780140100d4040440083c041021100100c0303005541591a070102503ca002942c517078071741c070855221a030308072008900013030079404841224039101d54011034800050042108c0803508041d000d10b080c10401e21040e0020400248182c906001301c10b403801c801d03d410321034000851401d003501520340806010a00c02c0303803485c840c80e43c0030a49000c014012640e000081d20349409000101041e01d90b190300c0031448900840300c00424440481000750b414400d03940101214240030703680c0148420301852070400e043c21180208010a02411b100141240304600013094540007400c0c04aa41c046440030710500c3e8408103a40606000007420711000844c081c83d81072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 651182886 1250 651181636 651181673
    0x702030406020a030503061315080118030f2601060507110405040f0813051c051c0e04020a0207080a0c06110d051812150912030f01032913 61
    0x14241410100c1c0030b5600c21600781c015051003000f00010b00301d6500c4c20410300e121241d4200a00510024201d8100c00d0702d40e9000341410340d401e040e01609083e080c0e0300300c070000542541d00c0341084000c21000f581d8040340d064000d40380c43c841404040c2110030400500303000f081155901550380030182002100075100c1d041c01032180e0f04090501000c40c11090003500b01c1a00400a940d852076100e2803a01318a007540c0c007454022031201007005801d04044042c83d429800b81c0140d5449503500b400d48640041d4510103840403a02c41c40d2031aa040c101a4003400341014035004a07121a40c0b503110261030801115402c81c1d108040480901000383c0c40168165918910802001540d91406c005006400f40b42d0380b075807040c425100105025aa80070711290110380c02c000f503985074880294282d98a4a003120ad12140c1c0c803403a030044200070801400c0700e1141c09050110103d0ba421561100c200c4800c0a00c5d45a2801684040a420700c1b080b09405001d002034807614600c2d11f030300703141c41c01ca006007402114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 651184136 1250 651182886 651182893
    0x17180a0f060e09010b030f0916121a280b0307030606090b030d1e03061203020d020d050403030c02060a1403090f0709180f0c12050115240819050c0d050702 68
    0x1080170242c640260381d0050890759212803959110040300385008804408050201000b03600060781e15142c500310019203018000c1c24548401540404101c81ca096610300000074841d0038500c1c0c400d03400400f103904c2ea0f8052202080c187c0806000900d81103207138000381c4120303a80b1102000901450311649000c1d82069001d40b040307240451020f4100004070944014020104542e088078900c2a40008080d154005000c00203403100c0c00c001759501d501000150161160b01c0048260601440554044030342c95919801644666405c1c010140c0200603c032040c082c00141d0100f8013104580034602c50304050b0000c1c060307014029a81c524284603075101d082c41625150401c2c00b02031405868440303054200d041c011124a0358500300d28044880e81c4805040854018244e0402c441034004240c100310030b1888000142d11401000210340d030b003c0c0f0740540240992440c03000c1c140541c081a1f40418076503c4200c001e9034081400042da02d08442080e03040d400042d844206510600c120b5408c165a072004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 651185386 1250 651184136 651184139
    0xf0f060f052409040e0a020a050102060615070c0f0611060106090b0f0318060916050306010608071202040506120727230301090c0302100c17180a0f060e0901 69
    0x3258040002070495000265041c51050341c200b4800111460003a02a108000305ca0013821180e0b103a460081040b0301c100007110000940e0740c40002c002e8054480100142d1141a000c10101d09650181c00c0840d10703a00c50a00000c7c44409508508000f00015106d0015081450122a0074540160465000d10242510500c4006038600c190b920034030702c2c060500d40d07984030b400d844203842c099081d2040091051200704040c0c1074010a0303d9400b0034505000d402c0c1d040e2204100b58686d0800d024171400181c260000a2203284150b6081000e40030003040149816200c0000c503072150f0110f03640d0440c0692040030301a00340d9000104002c40030300f510807000100c41c0640881c01140c201e102e0304201380a011011000c4000030b150507100b913a0002c4c000c0010b884c5900d8041d80d00c0301c480c44140d100c5c4c400782481c8a0550302800001031000d81c040000c0380380d90030018409043c0e4002d103041c00043c8500c403118000544a9030018405494018540f0000500d0450010414030300c0802088c0540c0c0403a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 651186636 1250 651185386 651185389
    0x40e0f0118090302030c061014030613020402030615130303110a0f060c0302121503070515030f1306140919020a0504020d02120711060a18020904150f0f060f05 70
    0x70401a015418002140c012090300f4204d15600a0407000075060158009105030110403240c1181180d808288800d1070003007150400d034441c90100c076020703489012500d00e240146460f500441c2d120320004c20341c1010b02d001c4040c001c50b58000c06e00c040000303007804409005042c2c00c440804800e5041a0041c505040c042d83c83c0c100040c012680203020f103880d00348000705980690181c0310803540040002b04185003401d00b0500000c60120382c0c0c0d00a019030321021503d810003000c8004641c400302001461030f0ad42480300c0d000540002c00d02e4107940c0c1040e44040c0003440341d0095914040c0c0c1009501042d04003920805d04100103414207a403d60084640d400058542c5c01512080b220220b800588440000103040064820200c0c98003007690800100316105400120b907a40002510b0111500c595600ea11042181e001c000c982d580c130a0142282070041c40c0c00040e02c0e510a00c0b51701640011f001c0030003c2000c0c2c9440d00920383d0040d4480c261500b4002c454413402c4020103110401088484ca41030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 651187886 1250 651186636 651186659
    0x18080a020907030b10031a01020303010605031503010621020a1710020d02070501020f030403030f11040306020c10020406020f060609100b0a050918070e19060309021201060803040e0f01 81
    0x800003401030380a60001202640030f5840b0b40b0f00c200c0302178490710018240c1c40e401001001202045980d4000403049150036501c008160390513105d0588980d4a1034030740004034a14180598030041d170642d00c5000205200d042101c50006070650481d40030045005441008040c00041c0c200d942e13000c045404030348170f20100040d008a0092601ca0041e5034050100745200030b0f1140e01c1000d000c035800001d4401071b0310b0120700118412800b0799010001134886e5044042520b500d100034404000081c002840800d070a9801003245505c00012501f03144102da080707100b41d07003055110314056048039110b139602440502410b98010011514000c461400803a03911300d29400c0e000c0c00e496070340c0109848280a02585c129000400c00811003c0300d050095030f140b42d840801c803113240004022a0011a080c1401d01180c0811168001c11000150030f00d60700318000e00d5036407416030303000781f10140c0c09440400a01c10032000c0e01e0400043d41c4da40342061021140034001038070090b007844022004204000c1c5c0349 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 651189136 1250 651187886 651187903
    0xc03050606031602241803030415020d140c09032b0c0503040b040b0a0905041a09060406090e03030f09210904110a0903060c03060e010e130515071808 66
    0x25400c0160f480c1d03000c0022407a01a402e0300c4821580e1244d1080e0344d007481404034051080d115038440a400c4c0d408048a00d843c0d00054600500c0702c081d80601022088198001d44102002488000b4099401c103032040c811074000d0b2103540703104600007030b14881401c007404070b043e0300c0b03507150090f50004420360550951050302c1a0840c0c00c1010441d10f4504124060044078000d00b0004045900d0f9912082d0450090f4449020200401c034940e100217030500705401802d2500c1125800600c180316020280840c2810041090b03600032b0766420003040c8200c2910070b00d0701124076000207540320319107070388021240780024204031500c0c0d100120100d944681e118983c04054811075206485240c0000440c001c5d0080c411801860540070801c0c0e450360ba8002881000c8034040d00040c4201000628203400f100d419000f0464817080e03d600600c141c80352680102d412180d8100250054025521442c2c01c01c251101d01d030b614000302c1b80034041202d40c4082586140a074010802c4520781c640320300e155451600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 651190386 1250 651189136 651189151
    0x10c0e060304080f0c010203010e0f01081e0c0a03050105060306060607080f16060e0c100f0504050103180515100905011d04052a0312030108030723100f0c0305060603 73
    0xb01084528419120240c07001003100f80c44001d0080001c1c082d4009018503108024a4000114412104003029040b10b501034050031b00c10440c01403140441d1b550355000c0300140308030030b0705425907154070400c04000e60045c00005801d0402c40205400d103800500000e10a8105006020124040310211841c2d500b00b40354480c2d43d07882d10440c403c007982000c60007408203464490000b151000100c6e80d40743c1d001044074030340101e0100407001e03a0401012120f81000400c00c0c0014007507940207074040f80840410080301e000038501030b5942850301d001080179030300307103009030341032050840c0c1c1c0b41c9600340944040d1b08140f03c40d60400b4025504000b558005c20301003060907000c6814000107019203201d02c5644d013410700c4461400d202091201480701c401900902c103109001d658460340805403410b07104074030301031031402d045a2140f1680040148402099a0580c0100070400d04100000c200f41c1c411110042403c1c07040b00070748000c4402c030315410000d0505200c01c01806a5800b000c0380c4e40300e60b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 651191636 1250 651190386 651190399
    0x213090507061d030105150915091e180304050d03020f06090c010906020708191e030306150509212a012d030509030418050406151202060d0e2409010c0e 67
    0x740d40203103504071090b410929800ac02004103008640800c00d0300e401803070284002143c002d441d00900b070010500d1107160030b04290002d000511080c0b078030310b050500940c001d10456292078494503180c1e09100040e1901044c0c3e5001000444055820a09090080986001401304a49004010307a04c883e03280111b1171490f405203100408008001511035035944520a8084e07101d4558a80035000307000c98010342c0148642110702005140c4603004031020700b40c01400d80340c0311007188401c00d064400190441c44440c05084800010a1208501c2060464880c09030000d840d4114002400300180d103140b0b040c0c20400384651200c20100b4400700740c28440103160000f1966140080789040d8042c54124040d00d01003400148102c1080790045401903000e801c04011483c201007801141004a20900d880000205074140252404201800c1074440761140428018110050325041410240d040000b5192103a16489900e9045810030fa0044899000300604144144068151203070043c040c0d00c00c0b038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 651192886 1250 651191636 651191641
    0x10180209061b06061306300f11190b1207030b03030a03090606120201020d030507050d180302060a02032802040f0f1a0906070213090507061d0301051509 67
    0x112403404039400908003040602e0300c052141d40c2c0c191151800d440030f612443c0b90051000c0c4084052051104032100c1034503400b509001c100500100459040042c988a8440844440030440c030413881150300c5d2203140d480518884d1081008452050011f41d41c40382002040284109a201801c90301445441d18849455a81d0030900320003820840c0601034042c00003055002c0541d4154000401d920300c5904280704103525858800070701e219140340070340141d0007090b00340502d900030740c0300039081542d614100d894004115010016507508a04440003010b41034401014980d0522203280c01c145080025441d50825044241e40d00558a5034200d1005a1180c5a588801c40e581100c00908164219a440c00d5680462807802e0280344a080050040c01f071740c041c0a68026001c940d42044000c100a050003055004d1000c1788100b4543d18149980d1603503158046503040000b070f4010800d80e59115501d699948640d0300e1b480c00760300803900a03814102408240c181c0b056030100c0c45002134a2145041d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 651194136 1250 651192886 651192889
    0x20d06051314070906080a21030b040c080a0506010f0801141f02010608120403080403140a061a01030b030f0a020907200c0a0509040f060c02010e15010e10180209 71
    0xe0390080c0d005040b034650750a82c180c1c141c80801c000c2c0c21a80031000400400e985c0d00030785a04d541c1c0c4182c0041842c2c1c50003142040c13102c00400d00d546a407203035150000704119a81d001c60200e4544400442c041035200c1c04003c0580824002e02d94444005e2919a03450140c1a10240c51800f060003824184920301040d00465211071a00044480103c1d04084900d00400b002a0080289002e5651310b4011000050041d0501c80101d0342100d50181240d0300d03040c030356180d4001704c0594540080460140e5600f41000c1500c80c040d1a200c040882c9142c03000e00194400981121076403400d4902903004000c80c03400c08000462100b60658040e10180c4040d544c1e58411076078651a1022203404042c4a13080b601c1d4107200069001c130400003a40d004e4082da485108004411100701e030000c05010001d002c60000403c241c1128850030750300c0c00007091040607550170705d083c086000f0800304884285c000400c0300c003006d03104540e00040d045d0008012113003040c4021040e442c5030005000340d6034000030b030040c09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 651195386 1250 651194136 651194161
    0x4020103020a0225150206040302070504050c0d090c05010810051c06060f12051006080d0e011b030c0209010b070209131106040b03070201050901020a05120604021e0309060112020d0605 81
    0x60000c4c0700c0300305074400038103000e201e4046240e0195544803020044103208042c0005510790003960582c004144081c5410100000b0f000000c0003081c08140c1840700002000c007a0080c10700d103c3c4202154240b141c1414001044484003d000400c032006080c81000640c03240125640c0c401d20081d00c500841040313041080107015554020032140580c40d100056902c08280c4010105d48140290740701081110090000e6a580d4040c0c12202c0d0004c43c070484d80103000301106000384a060401c4000c101d0100321050fa0b111204000341e010a091001070303421840c044c625030f4050a008005c1030f040100d143c0100d002c0980013003928166910540d020401d0210300285152103010046c191075076651510040350003904140c2d8104095820700c40801d80014040c000c0e01c40b854090303a40c0c0d604010740e00d0803420701c07140082c1c1482d401503030800c007041c0b0045002040c4200703044100d600c65504c0c00c1c801901494028140e00c0300e01e54943c4004c506005940301c0f4003140c05150060b2010600c2c0d103070150340492 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 651196636 1250 651195386 651195403
    0x31c0c0c0f0b0415090e070509031f0f180305071b0308030a090605060102060417070c080d030c0f21110c01090b09010c09260a050a0f0b01091404020103020a02 70
    0x481d0380308901e0015001035901c00410a4418880f0400074204007190300742c96140950040b4082c140d111000106154070440240146541c01411141c1180708172092074810000d400c50340300c1068880145030f41e184036034000c020343e80c50580511710010301d550301d004046000c4c2c043d00a02c404800f40309401c00d41072104014007c3c40e044009265613050100e40d0800800c3c40e00b20448e0600e04020000f070040d030020902c1ca00c62a0082032280f501800c2801c4001c042d230000c08100c41e0110303200008510f141040060f4921080c090300d00051468601501070002003c01e0008000c1040d03040c0b50007003014005180144002b4106008140484020300c804c80c0c0780034070740641c441343d8038040a200a02c64140c504034040d5440000820000c003001004944000c494021070810112950b44007100c90382403141d041000c032000301900c03404032050341c03200d04146107200d00391242c1e03104035282401d1210080d034071401000da0764070801c101100c40d00c02c03109070384000704080d050507400310395009040e00a003c82c60 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 651197886 1250 651196636 651196649
    0x100509030c0706020a0218040b01060f020a05010509030a08011a0702040207111903020f0a0806061002150a020a0f3011070c08070b2a16060f020606031c0c0c 69
    0x140b10030340300c94000b580c90002142c00d9101e0200314000c5075410104c18100c07130040e40c001486044036802d01205990350305046c41400d0461180107255000300b035080c440e29000b0314220001d1562080075000c010640d98040e08806c0f42d8204001c501a0400c2821046a000d25415a030243e00c40d0b200c0c0c1084040303c08032040d015000040c4a001d403540c034001103a0341d000d0380d100310740c1540080d000c00c040c00311a420b070b809002465800603000c240a890068082c42d04100680704542d06603400451090110701c00342c5040e00c001d0f4000c103071094055000910b03941c1d40303c0d242c030b0000c07815071501c0340c000180034516203412034a0105818620b011441c9402141050041c000599581d030030310315200c1000d144600c0b9140035800b903a040420081001412980128011041c904001c644004d40321004400c403410407506116003004444040c1e403d0303900c03000508507500c0d0200d40d0354a184029042c20360041c1154442e40100c0202e411204050355210f07800f48072490140105501480d1007000041342d80c01c0031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 651199136 1250 651197886 651197893
    0x30c01021e100e0d1805150d02070512030a1406092409071d04090f14010f090309060f02120a030b06070f0b1b09030d0507020f04060306050603070b0705100509030c 72
    0x1480071030001354000d0300d5040d40c0c0e2810711041042d01c0700d031400c1320700d03000e810b5000c0c07060400c00c405000c0a501402c00214400d03801031030508159100c4c0d2074103200d2508031049c03003004001c003c0c088045110b00080100c01510110300351a00d90300180044000a0040401d005080c0c82240324181c003804a0382851030190010313602d030400c0c00340504080c1c9504294041c020491000d070700039003002c2c010040500d503ca0f8002c04030fa039403552101d038001c090314030382c0100b90b5907801a11b0300c10a65004100e1b0150283e1076a18a46017403c00c01400b83c0b80f4242c10506552002148032030301e891030411510729950a16001610780c820300000340e62407056240141689a02408010501c110016007501420701c0d692040720000a41c00608803502030701480c541d041c2c109450400390103014600811030144010031540140c0e00000c001800c544190f002524503640d1501040350341d007170401285000d4407490b00c5241c10203030b05503101691002d54201c1114215201e40110359000350070001e4030a02841301098 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 651200386 1250 651199136 651199151
    0xc030711060f1602070f062304030f06111602120c060706020a0807082e0909110a05120601030620121501030b100c0311070602030711030c01021e10 65
    0x1a01c8018000fa10004652041545910001400040c07490111075a6035141480245005000da4501028114000600307041822050001d40d400c0002e00240d4810800c40c1d8101905080030001c54103c0c0300307408800030040016400e044030491180a4a59044035130031145988403e0b01810501d2150321b031500030202241350002c01c14140c01518511019507507042032550f5085085890030000c1c0c0e808400e8040d02d070400310740f00c009075070007404040a80601c1181c1079900c2c5200421103000400c2662450303580490305003186010b490110080000b05e61a013401d400020711107481b110b040c840180a290350795101900d5540017014452108000c1c40c0c51501d034106404c00c0036443c00102c4141c10454042c030704103d11503000e44222151100054218078400c050300c982628003451500c0b040e428081c01012502211074100119000f130200da170b003c0c1d5128011072801c0c02c081c80800605901c25040260f08000396640041c1510003e098000d910100400400c0114101001001c40820180c24240c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 651201636 1250 651200386 651200401
    0x201121e020403210f090315060e1f050102072711070503130b0f190e030d020109060b04051608040f060f05040b0a1103062202030412080a020c060c03071106 69
    0x484001e010004021392105060450458007050128298400f01e09010700a0001ca0051708940d4000a6920800210715441d1b03094180c62080460780041d0840100700c11b0a1a1400c400c90a4020a4203000510100303041002c402c0c0a880310307001164119881c0c4150381c4c07801c111500720a40d082070310250030313a854030141403d6440fa8403201c00208074015110000607034442c840112400c2c41e2004042d282008607500b19180b400039034235030703210401001c038604684030384c2e092144110b40c0e08641c000040c2542e241c6810011b807200c3c010002c6c45103160400700308000004a1103801d4520041c54140300c16a1649060b01c2e102000c1e90000d0040c07881c00602c2034210319154022030040f405405034444a03601d00c0100e1050711840780000c82c1c400024070200c0c1240c01d0940c00120400c510420100d800c0800040d2442260021941030700c0040c00c4083c00380301b042c2c004000c0354101c00041000d51074285020851941c4400c058611040300c8000070002d030307049100b8180b00c0c20003c0c0a4080d02c146003005c44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 651202886 1250 651201636 651201653
    0x1260c1e04032603250e03061f0f0b0901270b03150d03020a020114090d06060f06091d04030e0301020309150a0b2101021b010c02070509040201121e020403 68
    0x182500d000f14a5503c1d07400c4007460540c1c1c400c15008100451003a240900d86410390414007083d0140701d1224040929580c05000c101d128400b0780c00041c20440316200703030340c903044055803143c8130190b52001e05000355041001110703410042802d14001010031144224501028046001100600e035100824481da9010084d03009072340000090115202101c1000441c422a440c02009a8002c0c0c0a040065001c2e43e002190091a018102e05103202800030480e034801010080b03c01c95a600420300000215660030405804c1c2840e02610070ba041c801052005407007801c24002406e4004001000c25115480c140000800940295140e0500e89021a503a100e502443e01829240000190042c14144180c0b1403140004120380c407030b200c0c07640c90358003001c08241c1c0a8606540130405010051005580b01c41c0c2c0420380030000824050300a0000c2c2002c446400c2144580081018440580e9000010100202c80c07a1000100700540c18034000500f1107840000111900119001043c40308031b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 651204136 1250 651202886 651202913
    0xa06030c02010506150921010c110f070b030103031809020a0e04110f090f030a121716051225050a0801050406080a0b0a0f060b030601260c1e0403 64
    0xd400034030013600c07000d08000342c0c8403001c110000311060501c401105803814451881e0384021254440e0703180e0700340c0740c10682943c401c0700300c8601048000d402030000000410070035201c0d906c08406080c0342420400041c0041c80306100240402400500c0b100443e040490050003c0803102001c65131340e0450302c03001c0c1080e00d0340c41c6124840e0f442c0540c00c00e04c0c040c50038200d030b0400c600711b0340751841c022840d010070a929121440d640c0c3c00d441000014000181c4030300c8e00303144809042d20f5040000450710140011920000d00c100040914041d54400d6950010162211168203818024642da03c05103441072800f04841c400310000503030130a40030003903000070040c450452550fa83c5c001d160380390b00a02041d251180300303011040c0d201840c05404554102ca90b50b40120018401203480700b0b40025010945020b40c00c50700035484000223018003507821a045d05204440c0c134101c5103001c01d5420ae004d50041004011b01031820340065440f44d00c450b070214070312003250380d505090b403215104d0a03c05030b030303034402c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 651205386 1250 651204136 651204161
    0x1803110c030a0c05010c0501020d050a1401090213150e090c0421020a030b04021f090501030b0f0d2402220501090b0403030e13050f06091b270a0603 65
    0x444040c10001d0401103503030402580c0101c0001e9070a480c25004403003041d020a4191f405560a04c81c0a0040a6030700420f405030380407000201d032222558600094081c010790107003181910401071200c12030b0928407a8012604030f200102d4042040403c2550b40b5000d050081d50300c941d10100304048001c1000180064480089540c030010b0101d10354141c58040110002c2d500188443c42000021150003000b64040c1c4081c0c040350b80740703034454880884c0b482c1d400c180001090028009000d40c1d42d0505c21840900c00c22544c8940300031540001c03c01c0c18003003242c00350181110030000794801e010700043c0b40c140100f01d0740444d90380c11500d0340101d0312249000b0074810b40303103800d00002e219841903403101c0642e0b98804105151524695003598601d48041800b03400c040e240c58a1141c82810b441418810414000002c0051a202c8200445800e008000d9071070419100031240704200458151120042e074101c0d0000301405011031400286000704581d5402402c460011615a9054010300c110100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 651206636 1250 651205386 651205393
    0x20301142a0d0f060b07080904050703110a0311130915090501030c0b0706110d05040b06061809041e080d0c031a04090c030203060c09030709060510050c01180311 71
    0xc40000201501c0c0e2032080307519100744188165824842c03180d004540c50b08854200140f0b441d40c855840407990040402a9200e01005c00c0720901400d1a01840754002c003289010448055032569034407071802900414010169900c1307080b1103180300e410886928045120181759241c3d40c8031b0710321f800740c40c100309150000032882d0310006420f440ca009480c1a2680803031344030801c1d400e140480700290400039041c3d54040e00d841c46819a025400b000f04084002c40401090600c0c083c1049541c032030014102e14042c0404006090020101c1d4034034a00c04401241ca6500079211810304404072800f084407660311001041c85a4200031645000f40200c648000c0140001d525076002601100e407004e82031040208002d01540092400b03078001001c591084114042c900c2e200d4001c249002070880e100907803840e0000c1c8800700da01c6c0810a00008100000342400b0090521022a1000b80310aa20380180803000c02e0402d42544c0a4015502411400e07040418121003420020210098900c04004600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 651207886 1250 651206636 651206671
    0x90207051207050d18050904030504052103030a1805100903020607030515120a060e03030114040204031716050a03170f040308061e032506051201030f080702030114 72
    0x2030715101070790119508500034120b6140010000e0391800c031011540d203807030303c000c16001c5001c6d0b035200700c80ea009130301a644040d1036508040905c41c40c251180541446100035a00b03400c5105800001c99922440044021a02e52030380399602d01a2800210010218010307184845076180b0a64051540c0500075802c40b4100cad202c20100307404484d419507008030304241c62071140c80c0324240b1082148040065408680802d12651034500864081c009020140c1d08004010440300d082501346070110a4200c804500c1c080c6103039100c0c61204074410000c0d11515021900790480b0300300314041000c254024041d178510054a2400400c89031121301c2050707200868801007a0076940c0504000e01c2030f5810741780d8000300d484007000c101d0300a486040c21010f416001d4002c1006484c00d008960965040304030140000010041520140105810040c1003040512070207003400344150740c0340e045039000b00f01d000c121000c03428043c1043c803948002a402d0740c28514281a000b000310340c01480b410300c8954043e40b10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 651209136 1250 651207886 651207913
    0x3020f19030b15030a0908190c02010e04021c090f080415090f030503070212160b03010306060602030c06041518080912010b0105090f0319050a170a0906050c1609020705 74
    0x74041c01c0400c1540e42041c000605082c685e5409681d205028034000c90501e690000c031440d641100609050000b10950021000c43d6004040d00102400403102035003400346204600c14081c0000903490200340d241c1c0b2650003880b00c0418a002d501c1e41201c00c1d5a81d13a034841403860390500301c2e035141d4000101c02c07200000380c4180086150381540c4d4008065481c1c29000d400f0002342010018102c41540a41d0715154449101c41c46918010010b0b0040c0c69103d6249d07003001701c2164030b642e03c90005c1d5001000048002c450220301c590f030040e401064005c0622024488400070054016040d441c20f000070210b00600800d035000e41407400045071255005c0ca03001ca040c0e4241c40d9403110792400b095081c07110741d040e403808000d2442502e60181c121402407a0502031300e900051820030545030358000140c8103040c003a6a40002c0812405404017510b041e503072940040c131070901e500c2004200100420070403c0c00c0000e02640104445104007100d5581d04c80e40701c10009e6006003022140d512503221034844a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 651210386 1250 651209136 651209149
    0xd1209020a0509150a080f151522020f031f0b1c0902041103040212010b0607031d090106021e0a020d110a0801090c0e0105030303190c03020f19030b 65
    0x485034040d0400704500d01d054180680b2280207404c8601e5144008400c115a48411014900520304d40300140301d954014142d642c1042c0c1441003000030907a00c2003c2000b1100141c6800034030103000c0d640c4c5810000e00c400780d803807004280705014101c2400017410b20000c0c0ca406c1e000d075005025120031420040c0840800341d1900c0401e02c1540b0b03c912050040185200242040b1404034188c404042501e00d000e50000d401c840c4500320f901e140a2000c001c1c002035003400c0c5403828034084600c000300640c0385c80c203002880900820703400030104019400c155586d40d105456810086601a05884040d41c40390f00194461100d040d60480360700b0a03218140020303500081c5800c500e0340140000e0100300b500c2c0c44103040b0302d280e8041d00303411a50f0381000007134070002441505481805801c903501100d0a16103540401881a8005842a84103000b441070500204e5020715001d18000300000700351800d180c080c0d000e4003510b0b00012072000081410040141007442c6a801808a981d04220350708004042162 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 651211636 1250 651210386 651210401
    0x60906090522020315040f09210815130509071e0e06040f020f04060305061806010210051521010605040203010605070f02010909020c0c010311030c270402030103050d12 74
    0x3104400c54504450000650040d6081720300544000ca421844501080946000c00000c074212035540000800340312038120041c140000148500c115a00c0e401c0c801468060040c29024041c400700701605480c2c1d1301d15511482e1240310480520052030400301c0581c9550041c0f003032031001542c1940e1002c1c0301d06558980c805856048114105540f41d0500740300c010444940a0507400e0f40c01c1240600005081d009400180f40700d81d030200c0c3c5407070b104080c44040d299521180c49940411420b200040c6e80216068410f490f14100c00100c641c0c40c10f00d038003006042141603a402c981c10171203a800140c420388e40c05d02082c400100038410140c0c2d44003800201e00c000d10450300000d2060110300300081c20509014042801450405552a1140c203010102d0f40241c1c40001c055006410640ca0395802d40070301c4481c5001c0011041c00c3d8a400c1406825038400c0c409030900000510707a44685000d945103413003000c0f40004d4070864032580c4900d17040380e484804140100c0810847c1d44c13200d040060b540204003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 651212886 1250 651211636 651211669
    0x162102090f0a051c0606080106170f150705130b04140406150212070303020c2406010905010e0f0112090c170313170319081509040c05010e0d0c0609060905 68
    0x161002418504c6580c10780010304210307692a121000051001c20902598000c0c01005007001c03010110004089d290680040a103099078110740400d002441843c01d0b070b2940300f100d03401c0880d681e40e03c951050f460101c854100014904000c04c0100f000e070f5038104290b0b80d03040d05840c20419142c03103542c402c9140b025806100c0043c2e0003c0461074412140c100a41a0f10b4401d060250410b9426081a41801c178058180c64030310021880c1c40c1c8541102c042c04503001a03007030801c00000d500307200c0000c190000640340c5501a1102400b44c6607540d00c01c1ca070a8060340c01144003004492003a02d02441c1c210700c24841e20f5029507120035020030105021080302c0034800c41080c0070f01494a000500d03040070b140001d16080b24001442042c1d08600d40c1c060801000e186580d8100d280d14006483d0701c0c420403c803202034000c0300c48070f00300000a540d01c200c0c5000e030361090034691858041c000010b5a03c0038941e500a0205448080002e40540c001c41c0785c00030344026031115041f20f40c81340f09100003010b1104910 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 651214136 1250 651212886 651212899
    0x80a020a030f0c03060603050a0201080703020c0705061b0618071d160905100908100204030305090609040902150a080c0903060610020c041e0c090608162102090f0a05 73
    0x300002400b0040c0b12410034400c000003a990390740d98507400100d40d050b51003a101ca4000041040c210760780104e19a6000b00c660404600305821104d0850380c0301030500400c2d008840c0002c0b940d042010682141104480300c60484030989001410b6a4021056031102c481311711039aa00450140b0746200c1c0161020400580030380c0e02d40d100c00400510038140301c0b804051012181002c100da481d400245000803040c2e440e420500307842c100320710303107001e1032a02c01c5080c40748144400d0001a80c408101c602c50300702210302c5922800f6103c006001400f034440e0003540107480c0c05046c1e5036040072602902115400d511003a4295030740440d100514481d0810403940741c0c01050004503d8680300c01c1c002c4400300c0c64412100b10100280110b401c641c50b400e0004820000401d904605c40020301030750407022050b00c4c111481d9864440082c0c00c010001d00b80d00421480b450503828130501c40c190fa00b00108012640420800c44000c045000758030041c050b900079400741d00c4140b418103082181604486002d840c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 651215386 1250 651214136 651214139
    0x1c210513110d0807030509010e010306080309060708040906080d080a1e05040f02041104080f0a02010f14070c03030f120506030607050f0d02070302010509060f0907060305040f05070803090a080a020a 87
    0x15121030009028070389034059400303060b0001042c082c1000c2c000da40c1c8280c54040d40d0340fa65400240552080465440c1010b003442014000108048141c55841c04141ea14948940d002e1514044d18001c0350000311543e4901a07001410420000700b00e0035006542e16446510f44400103c034064070360032101d58440c0354101c824081003030626848144e1050042e1220300b5450742c81d81c0007400344c0d290010703481d071580e00c0490188019242840f082d158082c41c1d10086c048440540d0010700087c45014010092009046100d51001039071403ca60f08564442c0020410b69120300e00076100002e007900700310010340c400a1110844c000c91090381d008800040041040341d030780080484881d884866581c1035213500740704d023486018250025010481c4250008103882c0b0340444600d241c21001082003911413060800d03c00c0c2c60701c2c00300e1030401341c40c5a0b26000c5890750b40c0f400c0000c5182c070340c440002c1a510844100151403d004405444000c43c00c80e84031907160703030f218190b03566400344c071340042c3d0712200f1940c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 651216636 1250 651215386 651215393
    0x201050609070c06180312060602030301140904020d0b0106020304030b010b0c07090f0204030b0406050105030d021614010c0f0303050702010b0a030c15032c3702031c210513 76
    0x8100442d0741c441c1c400400c1c00020f48a0000000b484000201e002c82d80c14031b00c041c000340b803070b00408e00944294402981198940403030a0014901c1420660154900f8000b08081d9110340b000780c2142038101c504842c095940381030080d900c3d0b00038441550030380703600700020540300400000c4820100aa500804501d4180103d1100424000c05030700c2d01c0503400c2200100040201e100d461113280034201c006940d625180505060244ca660381e0011500590707894466010040190820307a400f08500940800e1142c006888000c1006406009110850a4101010f0f4141c00140c80340700303141d00a112a088540c00d000e41e5069502004260084601c804d01000c0800300c1403203070089075480d000c500110001c40344101c0070000100c0001d07051203080740804242040000b00518204019005900035529180303000d4848000441c5100d40b106624a0b019035030b08201c40c1c010745a041c5500d5100d084840c030301404400714013000c0310010030386c1800c071400304da001d1142a1250040190386070b207001942d0f6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 651217886 1250 651216636 651216647
    0x10908060a0e0c0406060512010e040c12030311030411120f0307110a030c150f17220c0f1703040608070f051c060504050f0402060906070f02100207030c06020105060907 74
    0xb003004076a0b1040f01000031096445004e40d2006007500e4460b2a62203c8100400020a10582021013461113050a2100088585030039030100c9244440480700401d01380340c00c42c0030304180c0017082c1c1d08600100c00d21051210032503070304071303040340440785180002c01c0d0070301c455250269004000c01642060105501003075000c6141117002000401515101d074995548421848840e0842c10034000c07800d821484a603084281400e21150b981040c0c180c054002e240c644230032000a1040f40b00040310011060340c02c5c00c01141c0180c15900101c1c030503d03d03890b199541d10541a0344981c07041d05056040301d081030080802181c0c15101f03103540b01c480d19546c0e010181c0b22101e0800d446020032504014040320215800580900c010b041e42d00402d00d0b501e450100025500040e0601c4c6252081005001c0140c0c2c0300e4040340c4aa40d4180c1d61035803142c11310304009112003602400a50814410000c5c5074040e58007160400a40b44a4881c0315825078441318100c0c200c890071200301d0707040170402e404140c082d80600d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 651219136 1250 651217886 651217901
    0xf040303111e340905191514010521070f03022106031905010b13020903070311040b060c0105060405090a0512030a0e030a030903091d04080d0e07031a06010908060a 72
    0xf54150001d510380c900800031103041e40401c6445560b80c0900000c5020300210580801041505110140c1c0680c0c1e641e4104105205140b03110b012641540d1250f40110700341c1e0414622110401a402d04092039048001012a2500001a8040340010110303003e0320079920f20405003d4146841c1209207501000d565000d80840c1c0c0c03520500410004512088890b007140500c14400881c0d60031160041c0422960080501100603005100c200401c0e20300061803c210f0340c100340c07500c031200015004200105440d011080d0032080c005590300d1081015040365010381001e9500700300c0e59886420300c40e1240400312000384942c00804103d41c84030040c030051600302900e100002002c1442c060a1480c5500c03201000700469214640300b001c1c1500030800400404061402e40454403404529241a14008100402005000c140c81741a268598001d10b204803108003151030355a100d040003120b0341081d140e030300c00c2c0030450000200c003035208003002011074060030002c0c005501e40d208520040c1580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 651220386 1250 651219136 651219193
    0xc050415050607020111100f06060f050d0c03020c0a03020c031510120201030b040606170f0c1b0111221505033904031a011401050f0f040303111e 64
    0x920001b02440c2c014042240340b20b82c1c0e41800102c0c451078024440a0b10303e1940420248000c820700b180455420404840c440c41c2a42400a0882c0f0509000e60080c090f54055902d180b05040140c0101900007607150701d1024114105d980304054110300e0702c070040044910b0541050001002c0207188400241c14505510504011526110a002040403108660f21050010781c032124003056410302581499000200c12007034a1880c40c0200710a046807050440f580510030384400071004116082d444030000f20038040302d040e42c0c1d41c0884952043c0b0306808502a000c020014400540e0381480e400c071481c03240312509e0b4282190790320b501964525124074444540314039a849030701c08445220054200403600a904a40c0381c50640c01d105040204012004594944a8006100c0440030050400796240d09203050303a6a0420f0310808c551900074420106465040031a01004260300503031000c55113130b130000881d9103107250112400045125182109010b4010f001d40080f030a00e0703603914040b00102e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 651221636 1250 651220386 651220397
    0x101b0c110402030c041809020a050d02150c010e060c0a0f0c0f02090109050a0b010e0f1c050d0302030103060c0305162715031506050d1e05040501090c0504150506070201 74
    0x26040124003640c2c001c951400b84c805001406111000c1240300c0d101070b0041420003040700e05026030109481c1243c0b400fa0611890a084401085544a007005421544c0740749280f9225801450700b2400713000c180400075103070b00848000600e0b000c80300d4140ca640c1c2006546030010404c0d8a1420341d046040301100740c50800000444501507280e442c1c0050081c00e00410002e02d52030032924081c12110590016410404048a01d00c50b647d0741c0303060f0740c1c0c1d4044201d40252407100f041c1c00148016003041801000390140c80344c02d00b12507425601650481c1c1c060101803118400c8668206c0450b4002c03200d0b51000c0640e0603d0490030762041c50030031520b02030361301c40c02141c150241181c5682405584044a08040d2010341e41a6035410300440b0001e110443c0c507400c10764100080030342140580243c583e0320a58801e110f1140103c20031500c3c8120501070410400e030304040c180b0a02800c00035100f03952103441d607040045ca40c1040c1c41011452140c58040b120160705010401070710b640280400c0e4108032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 651222886 1250 651221636 651221663
    0xa0602030a0615080916030c0b210f0603100920040b0a0902030402121c051606050f0403021204050d0201030e1204121202070e0c0c011407050705101b0c 67
    0x1502c40c1e4581c02901561388440c410b501c0c003c0091890401c0340080055072005210042000607240842c040680e20300c0b204494990703400090316103035103d0400405103902104c00911007541d521008060081c0c005405842c3d0b0150b000510405503a4481402004810a40303071840c1a0b0440145940c920a0b00400208203c0c0e102000103d6544260300b1908406a0005c01c2c0001c41c5802141502181500c0026003190042e0014800a02140c40c04040074001d0000e062a1601090540325842d142d101c0c030200154203003a451081120002ca408401620450714035184141600054500b1a8002011031011600c1940110b025000344078040e00d141c4542402c04102507401c03000741029040750a0310b0001141c00c0d0030500c0104440d01c0801c1b0642d0468041805038910201040ba4400100040c4542e2008007640c40350040500801a80c4208145410f001680e68481c004140490041044501202c500603281003140c0403140000084200c0783c8484003c00d02941500c2c581c00d0041d5503c18180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 651224136 1250 651222886 651222899
    0x20f0307030506090c0909010606020d1209080a0906020d020606091801140c070c060801142106180706080907060c140d09061d0904060e0c040207110102060105120a0602030a06 77
    0x7541c01c4c2c88030b0000da00076610307004c56414540c1060ba0b200c1038020090003403c1c0b5203280a034035460007801c00002c10003500845608041103421000d54150f001d211266220404100200500c0386030054500502894044804151001400c2401550000c0059480742c0365014040b48039200200046642d5481d0703145007038490541e8580700d1103000504075a5954010700d1410f58414041600407c007440695401031180310000d10b0501254503041d514400b4061100010918610044801103002d00c1808108111040d06021354074200042d070701240d0045071525000c5c1c4c0c000d48125148125684030203803c00103a4401c1019180d8a4015400e001c00c50804900241c00c020500814602007403032203d041107965881320341e4080d14800040090081804880058008a00030707001400307480d00c601c038080c0d11410500c884103042e84000d03c110358804840c5030840d20300b280e8580050160240400008850504401e204a140d0b0900060441190190f0b908802900090950181190b13500c20102c4d10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 651225386 1250 651224136 651224143
    0x1018090b060d0233190905010801030507090902010e040e0a0b010504020901140d1d0312010e010b1c0e0709050f07170c030411210705031c05550c020f03070305 70
    0x1041403074151903002c0010f02d03001a1071801c183e03015604101502d00104040cc00104102c402e40d5000741c0302060300c030258001280c0340050345002650280c1b401c8220041644005000d111040c4508408401aa6228104002c0340030b03030880d0f107005c24907102c5902070f520410030040c404585c0e60b0b0f42c00100c0c04522540c2e01d03404000844110b42640c000250640480c00c05c40b800390040c60b0346000c1c170070958144440c4000038001d9a00f04107041d45c0591140d480c194482e040108960110000c43d5003443d41e503c0540040c040c1a1411081c4804800200d03c00c80c1c4200400201261b00540408450300c1e04025050203174001081502c0003000304103081e48540c2c0786150486410b460040074050060500801d904020803030703100520039030140c10791501c010808061000301c0b61260602c50384620808014000540c010111441c107010700c0200807582401009074290b2007500c140303042008130f0300d52419034403403880300d039114012842ca040308000510b826840c1102842c4003074103032071400750f50799030702440d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 651226636 1250 651225386 651225397
    0x1401030621030305060a1e030b0c0304030e061c0203240d0224070503070b09011503152021070306030305090f030a05011409010b190306051018090b060d0233 69
    0x1001f00c03c1550420910144205554001400406030340c41e50030107550140c5000341c0c03078000602444011440b02d03000c0c4945550280b04540b5114103640c1ca06d45500d0303000300880004940c0e540010030012410f200d0030300c0c03c1060311a50780680700c0ca84180140e410403201c00100070071560311040030008030303000a1050001d440c2042c8290a40703c5542007051003117007034940501000840905c06d10040001c5002100031006e4881c1107200054003203c6007004503001e0348502c03940366900c140081c2d00a02d04001c8400100e0740e4440600d04009038603000801c42c29106148009000280107014000c3d0300d107000000e107056510028219460501259203442c2512444030001e40401004030400102030b13020300440b0710001048800c1d06032104d0707803c101100041c9600010380318a9841d0300207103500b005100404068840400d1044000b028600c3c0403020f0b241c1104104c403013004600c00b09810341003040c1c0c0c44500550041042010030070040070040c0c034640c1196200c3c000c05001660b080c6600700a0001d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 651227886 1250 651226636 651226679
    0x1614012715080606070201080c0a0912080d0c05030c030118090519150e1504031b20040209030a060e0c04090516080d020d0c0f08041401030621030305060a 68
    0x70304100c1005000b801070720004106034000c410801c11070300181c0c0c2c42084150b000b02c903a502e503500c480345a0011100043d80f5005481130b04940d401c06020b02180d00007402c146000c0880500c020485d0001c1150a4041550800d40c8880240018032045081796505072205080f00030002c0d07403050301d0b1207880c5441c0c040076082d02405201030801c018400903251250201c0b40795413003400001c00c200f5066650f90f140c1c030300001c40c01c200e100200c1c040602c10355041d1056035061900290403d21760905091a4150300000440c1c5680c80710351408506081c000d8a079400310040c040c00e0141c50b1070b00c035040a032003803c040d48030354080c68080982c1540c1d68403695184e18080c1000384a02e04201007500307081030054221030301e15804000042002c40d40044c500a11024500c0c1030a416821454000816652014020445031011030b0100b41d0080da00f00c10f0b11200d409a03410b105507079540c0d400101c110819007444d100744900c0c1140a01082c000e0f0052034000360094141380034188d403800e4401301100c007008080e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 651229136 1250 651227886 651227909
    0x2b0f0507050318010209030d2d020f0d020c0d02060a02010e0607030e01150b0316020120030915270a02040606031b030506061206041e0e16140127 64
    0x100140701e600c50f034a182d007101c24000318030b00307158040003da03902c01c0721b907a02007084054101c44048407250441804500040f440c902d842d0301c2108806521001c13035000741e2a147c030841d01505642031000070f0b1038520440c087c201d1990890140c007840480ea121485c0e807403c1d90340300c441083c000070080003d03900c1800c895074000f03401c242d80c50100c0d003587d055000c2c10300c2c00f1540540600c2011481011a500310340910b02c049504507101d00b007070340507280d50092001d5003480505060800c02030303000190310641080050340c05090014400300032010080d15110400015220000c44c5c03c900f0031210054140c65604651014480c0c0d0b0004090b070360344c0d40004001179190003201e4a14003c03920240d1f850003417414140902c3c0f411001180007400355030709a02d40f84051001003000340e20b40e80d20075000d40174002d0b6210002c442c0000303000082c14180700c00b4600d910038100420804c050700c00e1918140d0b18490300c0c450300d082c0f2100045940f000c113906030341412003040d00c0000343c07031a21054100052403c00c805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 651230386 1250 651229136 651229141
    0x106050702042c0706080c0f070f24060e070e09060a05090903071b060210020a120f0e0c031212060a1503150b0a020c2b0c03050f032b0f05070503 64
    0x2950134203066a101d08140b00a942c144402c0310071590030340d461036039807245060b10745400703003844901888841006001e06482d81140b40c03105105000f902c1030306905510502c28030f50b40e0300d80069a02012101721000a04090092103945020306c4500d8000500600049400d601c440000e541400181c0344882c05920001740c4004014002020310340351801c010644020501c3c091f00652903c585003214081c042e8000350034501c0902942d451203062051a004104440d8911099001011241441d107101d206c0d100907595076150002d0040e003819940d4802d203003040c05011603200d090340f001e010035601514807500441c11120b280c0070768410b1240c1d50307008100c140354007003c0c01f00010b1942241c0c1d8910307000c100c075483c081e400082400751954107484404040c82840040000e40f0b5144115000c2d1102880360b440134026284c07017581c00e0320b010710251003840301c1146200d5901d1094440419924000682001c002d8043d04011107103a9075500004c81c905100c40d02c3d031421150122007900c00301e68007006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 651231636 1250 651230386 651230471
    0x80f0a0203011b211404080a020705040b13090503070b16181211040b041e18020a06080403020f0a061406010824030708010e010c120c08010605070204 66
    0x102850040c50541100407050408001045040c80d03000c07141407254662552030140b14254400c54001016000505c01402c3c41c0c988200d055001155120051042400c0424680741c90b11500d1030481d4001c0504015246401c0194007a10b002e03078095a4501082c402c1c0d4002c59a466989845602d4a82c80840348140f000405016502001411804140c500c003040c40348541e42040d40c43e590b0382290000a1740b5240c2c20000d006040c00034602504a41000310112094005440351351900c00400001d101d00e03403a2040c011250100d1941c080d510065900c8204401c500405001c0d4000b0b0280c41139803c01c4500c1c84029191400d60442100c665070f44d0f10016403280c10a002a541288091070000310328202268020307403541350001d25060f9000c400382e040c0d4440d03030204400c00003421094001c2c03108280a9100d24001d04001c2d803c0c0f00031034038002c0b10340d616008612451000010030380b40d460745a400c1030b104803000c2c2c0000a04a8000341e4a002000303211903140c0e0148c954413050301d0f20083c07030300c110b10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 651232886 1250 651231636 651231641
    0x20f0706210612110d1a090d020f030a030b010504090608030406110d0905150c01050108030c0c101413080114090d110604021c0c0e0a0c08131b080f0a020301 69
    0x2079000100c0785066028031448001c070319240d0302c00fa0090710040b074002d5000c0c0050241598050300030400e0300120803240b010500c082d442c1c1d106507180344c01e440301c03105c030880c081e41c40306501c50310040560010041b03103101c076001c0e600006d06500c061404504258035020755030200d60182d00003414070741c00410100a1103500200351704c00c07000d0300005000d80001c2000c01604400304c500030140300e444a4101c10020a05080903038010b840c04800034403440d42d4642102d070716a4405d21601c5114001c14042c6100341c14405a04001c0c2405944c41c0906018240414115900200c81061403502d11a10010ba900e070309000c0c0081544440691400900f0250300c070030b1030510305002000034480c0c0303280070119a00b00410500d80c000c0c0c05891014420000903e900d041c070010001c001d1000c100c4800100304c07010884a40b51140300e4021003080440b07080c0f842990705100884900c031007203440903080c4001a0718035442e0204402c05404009000d529141d02c01e04040180740100410b500c01c003103a0043d49002d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 651234136 1250 651232886 651232937
    0x90c090a06170a0b12031201030b15010909051005040c0e190b0702120f01090309030c0e01140105161403120c0301030f02090c0c01061202040e0d0915020f0706 70
    0x60a00c4600c101a02c0148080d0040c0100180c0c0c060340d881505241d1910385510f10b844000c910300940b85d07107401c110844081c1180a000642d0080d1000000801c5040c003245021109101611025400d9142a10407400380000402000190121150008168445021b06010702d100f5403507045942c1200001d000b946121100c8183c402d540d5035408001704c0109404585050780c060300e02100f035a04603081c1c2c51802c0d0070741e034000c21650b1805e4964018158440041820340c0d00c52010880126640e60041c440040c0a0041c41059071041000054a600640040803810502c01c01e040a403940c42d200d4049503c640b82198459400000d928030700c000690040c141c1c08804d0b517002e00c2c115415038840d40e0561480e01d1000f4021020200030070081d006800a035035121a51800034840c082d190815079001c40c0c105182280070b54185030308450902004100d4260346041d643d00c1e528094501030100008011032034102e0294002e1030902c2640c10b000b80303c440003524241c1c41300681c40c5001150000c00c1e1180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 651235386 1250 651234136 651234149
    0x803070201140c1e041d060315040b01090e0c0415060f0504080c0f0a0f0306140a0b2b0803010b0318030313030c230d0f0c0503070609060209090c090a 66
    0x140302003010505801007940c503042901c5100034111341200d02d08011a02c6903822003050035508211240d12155075a07401440ba84040c5c054941c0b081410007c4800d051096400420a44194005100c00e08a941c015500f18501f03404407089138440380080b8081301c95540c184180003020f9502400b001e50002e404440c2c07410701d8a012403419150004088d00c80902015040c480e0301b441e5a4a00300b0b94900380844090100b8860a0800c190b9038070702100109801014050749030124000580b090380705108192800700050071f201840000300000d03040059107600b11645600403640030501040304080030794082d01400e204250749060901c400c110383c000c40700210015074410000c0141300c0120f411101250355260601703c008010510388011550302c8100400401c03103001080e01031864000960032400d03d0240c6030f01c400096400c01c00c407042c1000f041c010300154010001c02c0000f48250340b0840c0070b54040c00c0014100502d500c0003c481003020344e401c070026000411114450302c0c04802440040c0390 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 651236636 1250 651235386 651235421
    0x302041b0503041e02100c0b13200415030501060f092030150f0a03030507061503030930030509130c0908100501051804110603040803070201 62
    0x4124000820701c0c40001d000078085039100498002c02c004448581400a0380184045c0b455a0041001885580744a0050303c99103612404075800842588640620a4200704039802e0029103192040444010300d101641103555103000d00d15003425202c008001c1c61041c800458580e161013a42000d40c880c41d086480400e20f0a01080580b2101003214102c0d80800045c9544601c85c42e1480000a5901c0b12101c031000d407503540581c40080c48200142c0b04d80c00c0d0f0240d162025103040180184607031245100f0b5004440d2820a1021a02450152103103520a030341c00304680060000f020035010792030b0f00441c003040d03a0510500c62912407904804104080c1000c0412840d0714130003036000c44091650240c00e00c040051021401d4890300075000514030340300d2060041c44107400d8004c1060001d441182101d00800c80990070107d601d0040038100e400c020444400580300c0c140304202103101400c102c1d8800203040f08003a1903254400079500c6a07005403022502c0749400e07200a42076411400c8403811141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 651237886 1250 651236636 651236681
    0xb06060c03041a0c0d030e060a0605150f0f0a0305010503060903090f01120f11091203040b0a141204050307020a14091602010e03041205070b0708030c07030306031b030204 75
    0x42000060700c0c100e0343c0c0b8454076041a9142c101c01000c40c4a0b00d1182480382c060b24440f59140b0350150040d1f500000c19108a07941179445001c81c0044440c5801541c2d031200c2010155054090350030064840f079284103180c245031a03418280303000503034080a031100110791604010000c515091009640c8109900b000e180f9289040c40007552048000321520706018000703005981040745036003c1794400803207510801200d2810f440c030b00c210360025000144501403038130a9620841c4007000b030f01c00311506100c0306400e02c0300158040d00d9130030812180c00e040302c0041c8980340c3c0900c1030400060081c0d0003880510ba50b00c10600510020014030b4000c8904140007041203045602d80c0388406030b010f4403010b00c9a034996041c510883c09000702c81a41c01c02403001140110b44076001021400035184a40c1c1103e210590300c0d001890700307008182003c0c06c1d0100c1480012082096500200700140c401d02c0c00040301526941c1d582c258183c241e221500b020000c110074800c6082522070b4510040e0396000034009030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 651239136 1250 651237886 651237907
    0x1e06060801140d061e1a030a030219020d0c06050301050411070503120903091e030105010905090a0818090f04060506120d12060e0f0a050a09020a060e03070e130b0606 73
    0x1003681c06080d9004004070b0141d4000c1c004603501c10340c080140044a56940324203500940050301407000c00048043c50300440c2c6da01c6181c0002e2200390554550098842c2581d000c400c1290f00e41007501c01d90b0045170028a00c2c000038082005031014200c036448143d2039505000a2104035412042c42a40c514403c200c0600402c0b00001582d0a41c200e141072a181d42d581d0074421411030051001d491b40201340d44150b2908002c00c00c64080b01c448050300200496a6604d0000707042d60b000b030700c10740038076000001c00b000412002c0000f030424581082000303040700000c2c000704105a42c100c40c2070b20507e02c41c1741070004100e051f004541c1c000c94115110000711252440040c1c44002040d0003d0a00442488040141a0780d40185d0021300c2c0b4462002c0d010f01d0486030214410b00100c552011043c9404000381c9640d2061003201c40b05500684510007150801c01c3c1503403816045400950300d84514030000800b4140040801c4c0b140480f80b80010a40c000f5181025035102c0203408179200784001c2c401300400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 651240386 1250 651239136 651239159
    0x5130b0705120c1303110112020c030c060a1812020a0b010e0108010e0708030d0b0f060f0a0206070c080904230108031306020712020607150c020102121f0303080a0f1e06060801 77
    0x17034035001559554510041c0d00145c40b03e07402c6400c2c10f0803040c004a4888608400840a810502804025078400d9078820740680c084440900c1400b066007a010f004201164401800c0e660301c4078280116000c9441c5501c40400c055000da1010100c04202801072000050a01900310743d410060f00a11800d4280b1501a4581c0600018907072010340c0c90390445020382d0303054194008201d0246c110b50b03540c80c0c1c455040c000b80e80b210507207001500c500300105403580c0c030808000745ea50340c100094a00b03220242e410080500ac03000701d1541d131411144c0142040c10642d00501d030007020f10ba0300440c0d94040079800e601950070107911840940d0010384040002c0a4001c03d00f0f41140c0d81201c04c9669119a450b080d40e40c03131414040084014503062080c5000d80c0c05600a00000d408040a01c90966a050201e250440c00d01015801c41490131000c00000b4001c01000b5000342c00e00c032000c1906d081d0344a00320b0496a0307400c8541030040115030301501015162141201a00703c80c82c28030041d41c10308144056 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 651241636 1250 651240386 651240389
    0xd0e0a03120c12111b0604031b0b07080c0c014511060720130207030c0609051213030c0801110a080705040b120405010c1b0605130b0705120c13 63
    0xe030315210310030700c82138a414900725550901c0d4041079031120200c01c40d0207130355800704480450110700e80407012500318901b6401111140c0d401a40d61820f139546c2e840407202c40c600503003030180c0c8103800c0c82149903481c07080c06941195000b594406180c1d24000608919007140050190002e50b92a45450041095080c580d2000d40c0c00446541100c070402c804a0317000c1c864444040c2458003c40700d0078482c030403201000001c0704000c032002303e01041070840c2002248107128000700403800c6100785000242654114040040c000c1e425240d1401414550003101d5022101700d810303010203114144204840103900c035000e49031800003002403036403103121a0880c1c4254121034052140850020b03400620074004c4038040c5c1004441c2c141c9416402141e50b0720303000e090307a0860789c0d0b5080c08130203501c1c6441034040144040c40d0305801c0c07641c01034070745400000b04409410780b0040440d490313400c0c01080d40e41d075440740511000d40d03585035107800e090385003515500094a0100b00c5070303080041c0c29441000461040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 651242886 1250 651241636 651241667
    0x3030e0916020d110f070608091507080403080402031606020c0108100609230a030609020f0405070918060911090a0803040e0c1b0f030a09090e071a0d0e0a03120c 71
    0xe511184d0000da1441c0128440e41c0204c0c0744645e40e4080303401e030307403002c41c81c3d01a040c0766007168038500e800e50f95060036a1049078404002410900024040380c07003541000d8000f80082c040d502d0507442c80310341d010080c00a401c40e02c0581e00010800000f96400008164000d502039a0610070904200000744080d1441c41107400c05440d100034140c1384211941a9902c0020080646680942d02c0ca01000640b071100303c103034801c0345034502d400b010b800c045c091140b20301c1e883d5948501843c00c10101c0c507643c030400c1b884100c8032542c400c4003041e0f003003d80c460344203108030120748141c03981540400c006901c6402d03000103c454006000801c50352010b48529900402c80b403680c0d030f448140c426052400c00e03081110151a6116105010f0341408020000b0461130100da941c2007103480d10b074544981a514042c280390702550049404115001c2460a4206a04010300e40149840b040011a1080e100303c44580003050300304a24440030103070001d645080b44003e03000284144410542c1c0585808810b00e00103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 651244136 1250 651242886 651242897
    0x1e070801140628111903030e1f0c050403060906060f08070b07110f0d2003010e0705130914072408040308060a0b0c06090f011811010905060403030e0916020d 69
    0x1c106801800c8006400b001070007110700c4c1d51580c40350075a519813200c00540129140039042a0230000103d5500c031100581d503080740c6002000c0d001d100041001c50101000c0160612000c00011980d00680c01507600600000ca1414100740b0a040040e04903400380d83c00754005842001643c82c8801511492038004151006600d909404500c21a9410004991082c1032840e401d0030002c000c041484014811801d616030704201e10241400c840441c00c0c100b031190301103c0d04100034a454208a03c4c1da02c1f5801d00425100c08650342c090308144500e2500c415900110400c0c0250006d03204900e0400c1c02901258205514110700508900380280024041140340e1380002c0040d01e0b500482001403032003c04c1140e4035031202c1036990711500c06490501e503e008600c840034203003505016040050700d2075050b603943c0b9640c56980500700c200c182003440c184840c00d440001c140c2e0f1018081e00c001c0d8080d8542c00280c200401c104501e107100100000c0703910b0701e0004c0280e0701a034001307508055040b40c4d042c00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 651245386 1250 651244136 651244207
    0x15060302130512030a120c02030403060e0309030316031205010b030402061e030c070c081c121104120204230a020c010b060706060302031912081e0708011406 69
    0x8011100340d40d81c200c40d0700100300b05441c0c6a4000008000d00440c5c0c441d5907a4071400610480c0c01e400e50b40200740301c10042e03105100034404644c07030380d20140c00b4200030303821070303182400c0c400c0070a040d500300301498100210801d50b2607040c150440d01c1c0c0c490110341e101c003c02240d810442404180e01001d0b0010f40a0140030130010745180309101114101481102051b44074170303000c40d41d17110f00c1d406010102c0da88030341d426000842e82c10004004c00440d8600c0400704c0d1492440c08201c036000c0781101d60b0381203251206072145005220b0710040001e00341e182c24103032116209004ec04107840140610b03104406c00306000c5c00d01441c1501d4000d4100d2a041d50140c0e0b00c28a07a24018013600e00780c4002da030300050024986d810003034554024000c8910036070545518183c0104000f0710200110800341c41c0c6a8525042000c2903c2502c005602140c242e00b42c186001038902c580c03482d050101d80520200e80080011b000d0401001501e06481e203048030024503060b050300c0d403608c6480340c2099100c420000700340c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 651246636 1250 651245386 651245407
    0xd03110307050106091a040203090d0e031501060201020d0507021b010e01090302090c07050105131e030903050115050a080c0303040506070303061d0406053601020c030f09100315060302 81
    0x21650960b4106009100082c0c131200e48000501c00790198007600c42d01c0b032540703c020341132030b00a6901c9141064040c00030304c40c1103201030301c8104821040369410301540005d00801c0d240480c00501810040c2d00058580f403840e140d80c0304a503005000700041d98030001000c0e6001400c1c54110204c0b2900f0b207030085404454100503602c140700307508025840684d100401c01e102086401401d0054040c0009021949540224035082c0c80402c2e405064100704c0060382490503d07000510b071241d0f20074601244026601c1e2669030031525841507051406036000c0c81004286030426a00c0c02600b0401c0141c54a200c1c2400000d40d20301c198825140900004140401414001e60015009141200e003a0103102c02807a620412080100c508071425441c2002245400900781d0941d4009101802d10101c400d0702e8001c101d034060303020000c110706036408011940120b0b0090000e08114580c1060184e11614483d003002112421114408105458440181500d0304003525280c1100d12500300103a03038580c04c49 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 651247886 1250 651246636 651246643
    0x112020405030a050a0605060f01140304170705030702030c0a05011d0a05030a150c081003020402090d140c010e040c0e120304270f200d02130e040c140d0311 69
    0x140300d150326000f01c81d618800d1200200e244122036110f100104050380c2ea80e410000c00b802c00300000e500040f140f040510300903143e40021074100340180d10015188214079a20400b5078000e1302c00720380c15000071400c401103040411204d040142c040751020682400c041c0000c100c0400a20030099154500740380d92640c0e00c40c0048080644409401d0b00c98a6916003080d42c011206001d00740000c0d442d1910707280101e44900388890143c180080c08071035044c90342e020032019402901c06103070b001c070f1048101000100a00310401c3c2c02844000501b8180c0140e000140424001400c1da81c0146c0c02c220006d6180d40d8040640e104d00841141c0c15040d62030310024062960256810001060f110460000010000d03c45204e00f09030038414180142c2109001d0401650b40c1c454400080c01d40f101c0300c0a02819420020346105205a400141400914194404205101c2d4880c8401da0040340902040c0540455404042c00449507204021150500840c141c1081140007a00f04494108204420303001030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 651249136 1250 651247886 651247889
    0x2b050f06010e19030507032001020c1e1201050a0e0105040221150f0105120a050a111c0807020f0108010e04032f0606040b100509091e01060c2f01120204 67
    0x10615403d180b61285891030360390038240000d5841c0c05c022016041d0720307020030242000c3c5200603406404168000303428080410f8030007007110448400c035982084030343c40700d82c40c0c034105c0c0a040d0004111401c0101c005803c4a4043c2e001248507410b050410000d40c44443c0040c1e01280e088018682408180a1a13800e0162a1111240050100090040d002c04808a05040e40c100300c0b001ca9004490440e49962021030034401045904452000700c0428403231000150030307040141c4540040c01e00c10b094203800b940041d10031110644003040480c250b08000c0c0061400e07210a023020101941010440418580018002400c1140d1024400c0b40e4162458007945041d112602481c640c1600c2e40126071140b501300d4060340620724001400c889490320550403204c080698913030701d113031004050a0051030304c001868048503100d0201e0140600808007041c600070203540d942c0c0301351001d0380c0c03400e82014002101e2807201c803200c04000c1c41d4080883c80c80014905c80908040d4441c0d8031041012000c0d0166 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 651250386 1250 651249136 651249169
    0xa1d030102042c06011b03140c07030503070b0f09032b02040806070f0201020a140304060605030d18080102030609060d030903050d0c020111010621172b050f06010e 72
    0xd80c0c50400d84100000c144804400420320443e0003036a603030b401101c410342200b0b8601c0c5061028104100070030300580740b04442142062405140860104265140820540c0111443d52000402d041030201c05c42065801c501d10040480c1070341400f076400b9540780280d49452001c04060f20407155180d81200030301c81d065050308015503e036591010f2840c1c0b00d000840d98032011804142d0850480c40c030610881d05c40560035242e9136618400b0790000392139500000e00c1141c015581d04070201e51694200030111180209a65091082001c0d03619070072b40030130b43e81c0003009980c0140184801c656a1070602c551002040c2c6a500c65012541021100d854440e400079220340921100e1406007640200d124002c41d000b030703c031000000c241300000d5003250703014880e00344101012301d181d514517045030f8401c0d050b241c010000e01064440a40a404031603110100100910030210940d0010b0880d08401c0d020705042c0f89400c12940c5002c45a1004221000704414100601c2d20f1580c1c030b9994480c1c4c0da0503201d02a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 651251636 1250 651250386 651250409
    0x130605161a0106120b060412022701150e0a0312180b03060f030a021e0d06020a02030a11031201090e071a0a030506150d09080f0a03060501090b0a1d03010204 69
    0xc0c24481c03104000350a000d400001030603102c0800e1064842d00526902c0034001d80303460320746450800c0c00790b01c4085c174403005c80e4031400001503400c074030310112420407008102c5500541e4551614100c1002c1941c6c50310100f06200a03c071711044166100c4e401c0305c04503600000c0d4160400003200045904075501d40c50300804403880c00303010403401034007000303588507a42c103450303840c00b10205008150351900c12074030003036000700004000c084e8401e000444103a540c0c80035000040d1002c99036606030980c1c10440e84400141d00224040c8400d42d480304a10070504940c401940c07a11001c00030341e492045050080c11107480c0c442903111001d030410402d00d00180b81c1404280c0f410809082c0d28200d5600c038850f00000603027804085003140c0b4100c0b8009802c49598a1020700e0021012501c80282448031002e0314800b07170500015140016030300041603080344d580e50001e00130b0f003088000740000259800c982102e079410300000203031035009015005410b01110f4940050303140d20001034064842ca8018410090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 651252886 1250 651251636 651251663
    0x112a06070c03030818060606160203060109151215090503130810050901060602060103151404110307060201061415092d10140703170108070603050105030313060516 72
    0x121a06202050b24401e80d560100c948a0501d45105030b000c0c00c49140c9942c10130004100031b45005401031400d900c40c2c0860300500c1c9190b8001034109502680f2400c1e055403618180c1401c0a8040c2c01c50b005004042c546030300010782c40d00e0f45000411410800301003903903190304c0d440610504200355a80074607000604051561586002e5440303001c1c07140d0301c0017034071304040100d02840410b00030703e0141c40300303580200703007a030310795200c100241c0c80c440d0183c60495030b922121080702e84180c61803845940208440d0010005c0c4005140c90101594044021a407400b8014000c00d103045404422111084401d14801e00c41560007001c903220b20f400159004050464245170351400000c0d0792a0382111400b10600c42012000740108100407840350760004800b00001c00440200d0400b0701031260107407801080b129003c0ca83c248400c40c0a0300320a62541c0301c81d1013080700c25814052680944002d40155050a01000744d0483d20402402103409010010402d150221142130080c0d1400b50042c00d50026103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 651254136 1250 651252886 651252893
    0x1061d06041706010909170a030603150218241308070806060a0902040b0f030a020c0a03180f030209012c131716060c0c02040e1606112a0607 62
    0x1050504030b409060080c5000041c0c0c402c81445113025503134200e902d03054103a03d80203400042e80c3c0040303046001e0507a07a0381c0210105020000101c1c281d800d4000c01a034800141b144080385142c0d50020600c241a000300c1001211060004010120004a9082e8a41000e41c860106510702c40d0040750043c030032a2800904d01100181c580c5c01500c0580f9100002500c843e5003105911441c000c1100e4014200115289081003900460b0310030400c60005041507483c4202c1800c01020017819000100c052148803030003049034039140014420100048403071455a40420001c5c06c0505c91007502c0300216100e0762107000641c0c6032814811401c0403007600c510b485000c260125850721000d6030403021078140712030070780116400c40384c602c0d41e40322540d03045039281c0e07031035001070000e40d42039108214205c281d2000503140c5025003940120a10090021050b0031181119076481e030b58458020000005000511000d02140c0c0c00360018040c0e82040c0e818584110240210b62010680c07601701d0400141c80050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 651255386 1250 651254136 651254159
    0x40501050403170405031606020f0a08040209090102090d060209040e0d0f031103060906041a1903110a031205030603070b1605070509010b0417210304030e06030403050301061d0604 79
    0x8510a4603030300301c42d819101d069151018119402421644208031f1a0721001816010101d00c0348074074009440c002c0b03440203051694000004003c04203409600748021480c04110055002213588021418007552400150341088000000b421240d80040e031850310b0380b2203402000d08020954100c4140032600203005005841c4001c1110020349403080c140500c40076001100e00074640205101c0d01500d881080200030410b4941c258000c041d42340e885071064503030300300d02c0c034400942540581038240b85041c40c00b01140c000c11150300c0b07030840f482c090000074680e0768110380c500c0d807521b45640c0305ea170307520003083c64501541c124001c0440301081515001035a940b120a94501c11400c0d110800e0740c40090001280c428080c542024900340000c2c0310b1207081800480141c000074040720141c0c5510303900700c0c045c040100a2a2210580001040145508884405810017090740d01a29510b801e0703c0041c25801f060280c14104141002d40a5425603a245440d405940041c1401d80e51982c0340031610740b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 651256636 1250 651255386 651255391
    0xb033c0303070e01020a032001090b1006180303050f0309070503060a0f0b01020a020a17030f040801061e0b0d050403050d0507050c070b0304021f0903050f0c01090905130305090d0b04050105 83
    0x120825003800c0c0f0b6501c0880d500740700300d6050710341002c11843c03050441d0112500c1b920025980d0740ea40b1201c000b0885400d1403600035120315500d41001c0f400c2c00c4c00100140b14800c0c006252400c00402040060751110031130b070080012907101e60700d0345c5820794000e0400381c05070300030f542c9481600c052045580407540208926050750004000c100d0107072005a031a0054500041e50241070f8040411003006445150b807840000708054a213000348401c801016604650011100c9a6440900b0700c4106107440103003c04a4800e180071174500e2511070460003900c1001d020303c65180e02c4801140816000307409603803070102d025105010b5441d000c040144140c1041084010034481c499000580d455510b003240c0c000c64015041b01703580c200e08007140841c01c0b004441030b420000fa4101c00000718000b800f0300c00207684400040c2040400070070005145000317941000c02c01c2881c080074000d242d100ca0300522003542e410f080c910703100d40300c0400080203116a0700020b00450174190030803040000642c030151 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 651257886 1250 651256636 651256651
    0x31003050604060f0506100807032c0c040c050415120207060207140c040b011202030411030d03020403060c08090d0309020411040e1614041e1703090301050603010b033c0303 76
    0x540d11b0b402009001c0c0c501070308080101e4a06400b0078202c1d40b01c0e410640102110744500780610507004460b80101c0c482d849401d40c10740061090400030318240c02484801102441d00d24241810304a17403007400d07c0ba081a51013070010081003409448403a8069404250300542c0031503c0b02060300742104600d4014a0b880d0060180102c1d2001916181c03144420b059810fa5030b180400387c0c0318000500075807000c0c00641d00c0c2c0c41101c120350360640d0104503e8075004080d50300503031540d1031482c2a809aa001c034200400f8401c0c6981000700c808000a82c1a01e00096441d0110780c1c02600d00101e0001c1104525030a845180000c02080b60781c24050014050300501201d070b0703540314a01100301d8040700c48901c2000406070402c410071481c517a02c000c0c807100d04c0041d8048282c103541d440000d18100440181005030741c0010030f50010f28a804e102d8140d110001f5002440201551000a0380750642c040b40035244440c01e140d910070780102c00368040c040a801000c440392000c00404003d9913a00112110f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 651258992 1106 651257886 651257891
    0x90204061b1b03051c03090b040605100e0a0b0102060609010303090312020708032a0c011418040603060227400b03250b031003050604060f 61
    0x240001e501c1840200600420100181c10003160302c5c05410900d403a0070f1104022501132000a980079034460400110f566904c40d0045480c000c64114205401210f01005140c04203075200d00aa12400d0b02103c4075135641201304240c4c3c917403d00004000903015401040025004082410076403140d00580d0003032034440c0c05031b610310303000764050070600c0d6801c030117048440c1c08900050755441c0d48000035140303021035200040d00d084140384004100d541e00144118041c09101c0306030124034402801481516600c0c240100690001102e17920800b2030002260360b8060780541841c000c070406800341080c0c030303907000441c100b11900c0b81d00d000320900503020074006d0b144480001c03400c0b03c44440002580030f400c03509040c9401000d00c40b86803110205006024000601e20241040f510308100965903030b0303504148200f1410702503000806500c0340500707000c01c0010a070004140c8070402d41e1308 = true := by decide +kernel

theorem cover : BRFrame.Cov 651079136 651258992 := by
  have h0 := BRFrame.cov_init 651079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 651079136 ≤ n) (h2 : n < 651258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
