-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1563
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:35:38.496799+00:00
-- url     : https://prove2.me/submissions/7d585d3d-65bf-4472-bf42-f32df24165bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 280935251 ≤ n < 281115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 280936501 1250 280935251 280935293
    0x150f140a0b04030b150f030708071a040b0d0b0121090201030f1a04020903010905010e030c12030f040602070302010e06070909060515030c0a0e0d080301080105070305070207060e0a0e0f04 82
    0x4140003088013144880d500070460303100242d41c0340084c3c0c0064200400703103100700c1d130500c44c02e08080380e82c42010402030304889200e0201c2c5802d1851400e04c007a140114003401105602c10701c402c04602c20150400140709006040c40c03280c60340f2241051000240b80300075440e5a64440c1e29010465a040c8103808440081c14810410350201c40351074040007414502c030b00d20498000c20380c4901543d0a5100061155001c8000c000d041c02c044041502d90300003078a0400ca500980c40da1040349185401120322801840200c0d0140d0380d86e80c0d0700c0000039081060306078215903035401056000d8030100304060081e9941e03100c5503105807402103580d007559000d420a43c024000201c21400660741e1031306490300007855081c0d081d181e04c00300c2021102c0080a9145941c8081041c0c001c005201038440154180c5149100038401940c600e04203400762081030310303c100164031481c000c002c043d03c15007415207031800c010301a145042d522444904070035001e458500311104540305010401c0032070848040403030700f000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 280937751 1250 280936501 280936507
    0x30203090f0c06030a0908040b0a0309150c09170312071e18360b01031a01140a030608070305031831020f120103051e030d150f140a0b 59
    0xb00494041d010182c9454442d03515440403104012a91007628003078a07519400f1a00d0780c480c03010060141510741015507142e110450079a4403200d080c001c041d54501f090f113605034554a4822403072850507a40000300000c0c0400d0219141040c43c0039041c40c05030080b40e07111260b880483d45000d005031100e4203184240b02c2c0c0f07003507010421403225400b201120843c0814414180c61103800d0b000f0403003184002030400343c0000c03e966400c030465102c0c07000000f0a0382c080018141e0101c1c0070041864091301980816851a0661200041c5134020604d814151401040f0b240e0744001981c90010603070000c49268001080408102e04159a030b10400001200d10780741c096299680311614911052100804611032403040c1c14421250701102c402c50ac2d0b200b40c142d690665211001a65142800300316014060500c5a001c4481c00600b074144888404015515100345050098010190440303a0036035074183c01e1000844000943c100c0740140782c4400642c0845845034204818171001e50046a0611024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 280939001 1250 280937751 280937773
    0x10309082a0a21030209090403081f0501021b120f030301090e0d090b0708090d0f02030d02011a0913120207031208010b040504020c0c040f060504110f0a08070c0b07030203090f 77
    0x45182d0249154800c0c40391080051034104502034806c940e081600400c4c40701c240010107900c031422600c103014410110b0220202d011114030813591034410580141d200b2510f0541442da28030740c00108420042040f60342141c903000b52030030248026414121030300040010032641600d80154108525904050482c1110380c1b100540750401a002c1c0d2007164101048120800c8031182c121081410018159881c001c810300d000d0000d10360401007203010340618244044000e005000748417154850ba00c114404540900a0040c074000c0205800c0c140590340c41900003042c11400020b20410059024101d0207065084c40c60b0302e000c141e1846010016a07500401100d103040040c0c07000d40e42c3c2142d0140c0e071280c294100510301560601c503164003504c2c01d00101008807040d0f100500301e84050b20244000d03101c944440d2080c0c06504044020407104000d2034054500c41c100f11036201000c0d04001c44840c0a94640b4015050704464020200b640081403004100b001c001d84001080540002c005400304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 280940251 1250 280939001 280939013
    0x905190510080a0603060f05060f090106140702040b0907020105180706050a0819051f05041104171908090108010509240406081f0b1806060306010309082a0a 69
    0x1c400302401c0059a00104855072100e82110f4011600700c00248103a0407203008000003084181d51092013151401490a02400e00e00c00c282c1c100d80c1c0b90385664121082c0307145d000032203511071102281d019035034203107107034566840006141c000e11482e80001042d290000e0101c1002c0d240d8180c5294540c0705503010050558010112211038641c3d1070260426103030320480360302543c41102400161400c20003000044c0f18141da11482c5007258420344149250742d14140030413119542603006a1100c01c11080c0070495001c00c01c100d800b03d00301e04803804c071182c0b042081d400c440da0800899205900146184080d0b038041030041c0034110490749040765080c501c15003c5201107001c9460520071560030440b91960350780c1d2149000700b5420090301e80c3d940704550340b07800701000e00c0025403200d490030340d0200e1242412918821048156044401c55407185402c102a9400c0107080604160b00c50f04110002070b899006018251450b500c0a5041c1010100c1000a0401b1150031006a4407403c129004104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 280941501 1250 280940251 280940269
    0x905150301060e0d061b0207060e0d14030906030a14010f0806060d060e030f0319050412111f020702010207060f050915090a06090602010b041122050a0609051905 71
    0x88030b041070f04903071100c0b0011038800d4060304400b4082e140340045a18220310380500d0507050646640c02d4070070160701c6000030754000c002803880540024400800000241401101c450800c100c0c01c101c9040c601d110300001d15513072086441801c0e40d91038a280d6540c80740842c0340c1d2405004000c0c0c900c0700b003d0601141543e43c5400a00d502e106650274181d4030248085076002c20380317450074a07046d00d80d1102200580d1410764410707a00080c0c01d030311480715101c3da0b410503c03e460041e54401c4000b0392030700440b82c0031948031034100980d0440f4002c611a00c8a9580b0201419040c8070305480702503250708060001a052250302e40c480350501c905001801c1044e5440821545688012210b003060141407495107841e0b8007400312060340145040001050064100b84860115246035000340b21000e4000103000c2a01d4001481c848808018020020083c0f0040c08045c01a8200e9541e051151b54440002d4034421065015102051403500c1c1484181001d00e00300621460394028840300c00c2c548804541000c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 280942751 1250 280941501 280941509
    0xf01050d150302090705091c020123041806060206071706061602030303040c030c35030d15060e0103090b0708251706090403080c0c07180603030905150301 68
    0x681d594048280d0700c54010640000b440e0058043d90091402c0c400c040c01c0d55101c82107141c4911840703001035108034010034140062960607034810f540c5014400e0702400350840101034030300412003803001280401c41e01d000301c40440d0038120081025841c1101c040e0138150b000d005803041006e54500e11501905503900550400c0c3e083c3c80c0035540b00c60034207003400e0030b800104000f545804000140418480104e4289065902503c0c910042990b9000c014110481d480e005440303001e080c2c103010f8204030100d240c0d513038111020015070b4079000029620b50211f42503038080005ca0b054040043c0401588208003204224007801e040080c0c1c1506d03250303064402d4000708080100143c0d075002405900c06019500e501020402001d012510465806480d201c500541415840d0444000900c98030781307064201d01458040c0c41c0c114a58450040410b241e504c0f00358156814428030400103000a04c004038400030b00e40d240c0300007d00c0c1b403e40c8ac0042100000c4d41c00207103d200040090808541c0030022a411a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 280944001 1250 280942751 280942777
    0xc0b2a2b0902090f0907210209070c02030a050703030f0203250201020705190e060d020f1207080f060105030c04061a0706110f12070306381b010b0f0105 67
    0x14400014100040c1070705101c000c0d0041048414860518a20090340d40240b510400b03941019460f0f5042010b0981c2405041e03507040c2d203040305070025060031007034180c001c036091412002c202c915402080c03600c1c01104046030558407840c820401d041d44400c1000c1d050380c03248041c6203800700c41102203080e80f848000500c4202171107640401168001c01c00500100070152940703d034800d00901e100e042900600c104503050040d403000507401e140030071614034101e40c01015001038002c54024804041c800c500581c07494464004042100001009414414140070703008051a6041a0a2506191030038042c01d02170381c00c143c014483c2c1090b805810b104c0e1b61011501a8840b1030a040000182c01c00d08050b4041000c001801449050080c2c0100240d00d44080d0b030340391a0302c401724124101c0d0058030071100000103801424501038015203881c1584d07001608104403000303c08104100710340c01801302d420722107071049051310000c00a02a00f01070580445105421120440c000381c46886044400140e0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 280945251 1250 280944001 280944067
    0xf060b0a1202120903070b0105220f061a180306010b0a11011b0c1a0415020c01110c0d0906020f0303181c020618010501030812070c0b2a 60
    0x801c640b5419076a2002d050003c0c603550342044000961294054a400c0d0360b0604214004141030070550050108031041700d8011101c0d601300b00c2610018a040c0030304281c200e85030480002d6942d000e4a5030701d01030215807038050b5907d080d041c41c0801032034500c48050081e0018401041950021420ba0744104000d04102903c820000c0f01c0760b006201c019200d00c00165030401044070306a0180424500c41e226120721826011070180458042100310390013000c130540c1d01304100403190310f5005040c6e4120882c0021170f0002e024200011140c0212490032615030000c0105113503d0340c404120402004a070016214000c44d039162980c8a200080000d460301e00e40400ea003008072000c2000d001100d401d4100d004e0351055408000307469040564100245a0417010080c1d04408184034190481c0d5006412525280000d80e54000400000f880c510a11501c1103080c8003040e94406074901c1452901040317801e107030716841081c0c2080e01d0618030029910381408103c0d0104c0c07141c5050114030302d5101c2e403858 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 280946501 1250 280945251 280945277
    0x40303021e0a0201050103031205060307090b0a090501031a01060804151a04240501110c10030e10050f0c0702090714130605040302030706030c08040303050903042303010f060b0a 78
    0x400540001e00c00d03400c410001509080c49941940200d040e00c1c8a5070355010500000d8040f0360507604265181c50b899081514208800d42040e0710109c1e1000000d4078100f840e5940741e90000884000f64000e980000244280d000c2c00028580e00c01e02400c850b040130b10b0a07091540300c8941c412840c0c1c8221940e00d41c0d80c444000840c10b5240b035004080c10082c0244a00299100b09200e403403074000311a0000707040c1d410041441d6025440780140c140100006040060354030080080480310500c0300000e0598894401d844000c05000610010000d8a07001c249400c046a00e07640000f401041c00c0e9903000280662001607035013580c070700d40001041c50818401200007900c00b41c9803089044200c0301e0721a003800084c0107a0010003500c01c9078000c4068a00b8070750340d40010380a03601c40c0502c00c80010380450002d00081d000b0b134001c640007108201100e04040d1501c054043d121007444104186a00034000301d00245800d0041c11024080324105202c01454404c00d10b880f1b0040480f90400d00c44224500300f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 280947751 1250 280946501 280946527
    0x20a1a040c09020f070f03030c0306050307060f120e0a0807170405130504020102100203090a03090906060522030548040c03020909041101021513030f231c110304030302 74
    0x9103172581000c00d021400d8428500a001003580c0c51000d400720342002d10000b014130700411000e00f105d070561641c69140c01890021204850007070400c100d02c0f40d0f03454000707440341c8040001030a0b00d84282ca4040e030b1002135050500c403042c4090308440d03119200f00320a0240e603c412184080130038105402140b02e031105d20041c0d040c901104001104c1c03030300c04030401c0072210000641c0f41105000b03031500142e41b61a035100e072003660b03014040c13840404d8040002a18849110303547c041d000403080b124110050300ca54803141482c0c400310098032240082c200418a4290032080c4500d42410141403a12162140c40c0b04a402c00310b4010640c41241d4505a14103000d00a404807950410000c0500c6118035040c40c0074501c1c0c0d10444042c60042c85150028420541e40c02c1e186800303590802c800704280c200301e5804a54128410003240304010002e030800310300d40500e2881f0484a10030000413910384035800c13030b0340c0e0185082031104c1041904081451080000c40c1d81100d070065054600580d881c0364101441d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 280949001 1250 280947751 280947757
    0x504150c051920100e06090d0e0d17040f12020108060411160804080f06090c060706020708030a090203010b100c140c12010b040f060302010f0c0507080706020a1a040c09020f 76
    0x2e600c010750f020440c81c0c240e20049100080751100030801c00040713400c0c10b80e83d80d41d00342c1101d80c10360b10b0b84001400c1c05618000c0240c0d0340c505500401090480760f003556803290905045005111459000c5020701010b040c210051002c0c0030499000c1319070b000c00c0d0300020140380001e0545401950344180320310310380c0c120320b00b240c010841c41c040a014403045443d06400503030080c81010900c0c00303134100d5042d50b172402040346400b41c00c0100080c1a0343c00f5600410101e580002421110154200902d900041e00c400103944508030381d190014180302d082c0181800c0d036403a060158891901900401180303604951070b64260303500306a17000c13208050395130480e242208014600f81c0c807910018400c004544150810f0a148070155006d000c545011032841083d90b105000007404280c840e2204d00000d840303440400c0460740200100e0781042c0d510691203003001e286810890050b0800d00403401400000480031411443d42405001d00d07250030384a80c0244000e034014040c02d203800055206a00008500ba = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 280950251 1250 280949001 280949027
    0x50a0f0903050909180d0305150a03061e150b030a02090a0b0319020403030905010f02070f1d0916210501020a0306030b100605091201090f05010504150c0519 69
    0x200300c0d05910741406005a0040c0e411030348624108000150000c0040d94070440c65400d8000900301e4520160094014110081000340d858944003d040c217541d640021003c000d50203108001500d2541419070800012294423048146040c44c80c06205d4540c00c200e250100c5001605483d22b030381383e481c102c13001707403140c413003295484400d000000c5118806030008500803800155005801c80c2503201d0380d0141e026904c009408500080740c02c22040d400b92810703410f0301c81d0034410b07200036548621800724042541d8004400c41c011004200c45199690340105807c03104000080a449086544801c000c4102e4018034191642c0c04c2c507243d504c0e40d88104400c40b01c0c1c1d0701100035911098043d40041c010217030340c40107655600c0007a01191041084e41e000d202640e02e140d43c1c03146407003111000c7c0509071410b1200c29846658581560340459101c0ca014842188a107001040d01c3c14a8100042c03060540001c1d010101d01d0034a001c1c0c14a41c0100c01c844009001a031b02800d13144122105650342602648 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 280951501 1250 280950251 280950281
    0xe01141014130507020d02071409060405070c0f150b0406081c020a08040602030d0b040c2c041802043e0c030c010c140403020d020d081909060806180703050a 69
    0x209001d82c03150082481c1c04029826822590342320340c0c4032030b406a24942d59500c0ca0b040b409180100354135051641003d5032103480750030b2140440c50703141d888030307403512225a0a8620130941035030001030002c14000c00c044c20034101c03801e10165040c4045241c85008160303240c05c80c0d031400c0075100d8166009100d4003848075082510b0039112941c54002a417a584800719000d601d51410490f42036a1506206050704980e880d500d448001d94a040e00504481032002c8100710050b5000580142d0360b01c038029030b54000800d00610740c1d07010842c81400103480d1448104102d0401c0d620607054840d0003052410040e40c62081242c2d2043e010481810007882803001c13241c42400700099094903c1c0054221981c4003149035103103454802c611100e421180603501000754044551004100507190070b40d040b4404500500b440c600d03002c108580745000c0c0c0ac0b41072048004c2000e000c01000843d400404299000d5401e5a82c0215000202c000400b83d03200206808103040d03540c1d012130003800503a8444421542d10403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 280952751 1250 280951501 280951511
    0x11030a02010507020606090c0a0c080405040f0b091305150402130c0e1011070612180f05060604090305030703091703090a0606050a0302010e120a080d0e0114101413 72
    0x800240038000c2110300d40b0140c0301340ca0104900c2d0030219407003840740203075a0507182031505a140490b880014180161009a014800420240d41e1846800c403100c20103240000c00c03001e00e8041c08103070000142585a40303104a810318011900118100000702345242e0030504903a1944000780e14650708003080c402042c60905086940350f00842d00025550003160402d626964035502101c2d004a18031a9002c80e8000e80d104009050103941b050842d0b0528000c003003110303803040d0f90400380c0a64401042d01c00c4040034042d003040c000148103098001006481c00c1c031066009442c050300da440003030000c504040e03940c2010b030706001020040800c14103880030865a0b9091040a095503103001100548074580782840000385031030244100300031682d043e15551300c1d84070140f0403c0340d84851341c05445414081c8003000300000b4601c80c001c000346500300380c0c00030759050740c03d1041d800c442405400a440d20203281c10702c0259035131006c3c50340441d504134241d0204148140d02041c0c81000d80314002c9080c078100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 280954001 1250 280952751 280952767
    0x1606170705121602300a031b03090c0f060507080306031603060510080109020918030d050c0406110604020f091b031014100f05180d0b01030b1f050906011103 69
    0x8624448010707106079007241d0600610054031042414048250021380400c484c1401780b12040c24058540ba14540c20005240b40c0b007070760001c0419449070204000607545040c4481001410070f4884d002d4840741d50602052410050041c01c64803803880b010302001c2000c03000070b216030380801100c2002c090b00311030303007403442e80e2031070000c02400060310045403000c1034440120700d00a0501c03440151940052920805e51100340c6100780390418009520110700040148000c09440c1e03000780e034001e028900c8107a583c1c618046004040f6010040c0c17000c5650049004d00025994010078500a001c0896060310961245201014110540c9038000500c440100400c0800640d41c04844111a4005a01982d018120007001502c5602101c1c1c80f02003500c00140c520041e10410180840845610100d0284920a00007130000301400d075007242d4044140c8010300c1084603000c00c10380c220b546c6404c10b0070903503e042105500b0000c5405981c1c00b03265410300080c0395038464000296002d4000d01580c1d41c074450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 280955251 1250 280954001 280954021
    0x10b030c070f3e0a030807020a050a140a06110c040b041530030215040c05060c031e0a02250506031f080a0b0a2c01020a02160617070512 60
    0x90040021000340384103030f1220150080400c5441d000200603120300c41c15a03460030801e8000900980e00806c8034600850b0303946580612102403e203150502000703052a10400c42901025040a000c20124140145840d000010f072980480303012078010070b18030449004200140484410300c84032440300940000c80c03003a103034140c02c04c141d00c800254100d14103522008407001c10b8141d009006038030103801c2000150009580c190020700c6001d0709400143e5903000260f258000b4031440c007150300001070001c80303c803101e2110110710f400048210300b060090040a510350703a03001c540002d8903000c070703d0fa22030784050480c010001c0d1500a200b80c0e103d00700039903004543c40070f07060748900d06000d002001c2481c8034005000312446600c0312100d0710741d58441ca054005816110f500d50580510000d0a401041500e084c1011800c1850700040c0c030756460a2000340303001000102007104003001d8038280f200f2a80890f41c032418000c0c001d140502510b485200311102c6c4a64004154403000b0700d0248980040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 280956501 1250 280955251 280955303
    0x2041e0c020106080610050d0609050a140d02010c0207060f1806030c120204050d0602070203010b040c11012004030303020c0304081006231807020109050102070606030b010608010b030c070f 83
    0x41254020400740e0344540c91380d9500c0e00c05541e1002040c10f003540400c10352070500300d045800c42c0310310340c00f00b90808166516403034000c1d0b440e000c48408001100180564500b0440342403400b00c944000c1c802100d100d00302039110140c030b0180e03404100c000d607441080d2500991070075a001860382e143d80e0381c00b0b940e0720008004001b20381c182400651103100300e40e1030001c28000d99040c0c450040800320482076036a9094000e5009040403038146d501d076517102200e66514850381d11b425080b900d8401242107030b21000f900b1600c070300032505140111540e01038643c0b00d441003070b9000d4940c5070400507900c8445005d910f285005540c80140648074240e00103a2084082e0024007c031901b032030001d1104030720f280e003c03809415141c14098200c0111250b14800c110913201c2c00350020301c10300000030301002c5a03e505003a070b441901300756826910340b2010010001c811251a00504030f44c0780040c031039410103551100c42c0c030000d8004403038100c0204482003401140c56441c081e22f036019034032042d041d00d44150648010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 280957751 1250 280956501 280956521
    0x7080307060c021b0f040b04140f060301020c06041b080a030c0302061b073e090604090c0314150406050603100e0307030c08190206010e071b020d02041e 67
    0x1d410100d0445016000094822543c40414100d40c1400303000820b00140c4503058034000d5019844460203e110f880d80d20484140401034003d4060718a040204441c0c00240030b04002d000340e10421281d2442c1030301183c0b1680095000b18400300311a07840004413007000003034100d072041c0d000b01071520b170805070403a41c4402e90b05e200b6000d0714040d0b80d801c2001111441e081c000c40108010810500c400034041504600301c1c155845401c040a070b85001000e4044040c11250170740844814405e111203141036212158407107811038027030040091580d1040e01c50034903484000c048144041c0886140ba2060180040610a60b003604110349440c0c01d05070064241511518040e0091140c801c06a8030640070f98068488160021460050550f908441080c034011040d41c080000f400f40d20048100000f000e215a6500c0d801003000394100902714004490240c00c41082c40403d20101c20841c03050b104a402ca641c0450b0083c00019885c000304d0050241441a80345112050380c0001c01f16550ba40300e54101d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 280959001 1250 280957751 280957763
    0x303090105150907080721140a05060a150e0301020a05091206060916111002070203120c0c01050f0c01060e1023061c050c0306010e04291207080307 65
    0x1c0e844040e8403111a00d03061080d03580040f10030000580542c001c504842c1c1005852402c4a441411304d004a41001c8603851200c40c03c0e03403140b2081626081d96844603411800c0d4040c100454105400000d0a0800602c1640c04031002901030020f120701503000405090b502030000d55941c0307845440103201d940081e20306841510107000003246000300155580c07048034041c1c0014200c1c0c5403010300760141c0411810220811901e50082510500e0503c000d40403402c00450140e15501c00744101401c02c02081d00f00c102e002da05006080301c8107000240c22680200038203000f03640b2080070740d40c00c520b4807c80c03002041540c00d20b000065980f100074446445840c0d070410f505021501c0342c08003c3d522805540d110407401c45101d0820091624800a01c1c00c3e0342241d0a8111462600c44c103038007503c2003281c4203405030801004201c00c40d60080d0a4a0f20190111400c201c620075044509180307400c8400441c00d1504540314550031501c42c40039022551510200300e81d000d131b90301d02e0131517230f81e42c00402e04540f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 280960251 1250 280959001 280959011
    0xe010f060206090a0201030203060d050708070303030b0d080403060b28030b07170105190305070305060106021c080a2f030417120118060b0406020f0d1409150706060803030901 77
    0x2080d440841e450340280d000760054104042c1030707001100650406030900d44c1c001d0f50005044001202001110001d01045004d098090701d035041c003504070380c130482c0840d00428100c148000006c4c0c4c2d07641104d0a507a40914005030401c0040085400340b04840090007408224500c40c1c00041d0817030b400c00084074441d0480011a5503a884211130380d202d000040312185a901006210a10341442b4041d11406e0644030680d00c1d568944815140001c02d07842a60b998106100501150380c0c14044580c0e405840c03690492a14240f49004003414002861004000d40d507a00301d11980b010b07444074034040c4900998540081c8001e1100c1c01040c2e1068400700c0b416039041c1803203030790603181800351080c10001c900c0f000007507072078007000e011691004070400c0c034000d50b500000300f1885403013009840503000560003441e4015251207601d18110864000300700340280085091510310030007040f108100c2056650340c28060342c896801140b030080ba0001482e01703040c03c502241003a4000003135841519414001d200d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 280961501 1250 280960251 280960259
    0x30c0d051519060c0807060207210f02120403060f0f020d020d230103030f0e03060a061404060b040603090809061801090e060603130f0b0103080d0c05030c090d080c070e010f 76
    0xd030b07824041c4954004100400c00600c0841d1041c8050300826006060143c07500320f003039580c66007010000c00c144840d02d407010191541260300c0650701160b25a01d000501084910f0380340d04555001c6c9c0d00c0021700680c2c5890305d0440700c0616070807061190304280d40641d241c29030111200c02035088614441c410629200517074008000c15102d00025200c0c2000c0d52100e40d0940e1000c55005280101600c05c1c04052001e04406440400c44688503505218000603018107140003800b0309180100c00b01d00c2103041500900900c40d10101703c50459074903003000540c125a502d0244514054009402e900490100310010700d500815111000014240d807521105034550840c040828400d81e41300d43c0041052001800800c40183e10f25000c5001d10340c07501c10000aa5140d00105009800490f4114004a22150100140d00940400d80d809003003590940c585800028104e00a1707070906403040d00445a600180840c0c841243c18001100702518003113a1174054860803d2170a1040010001c2c0003c0001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 280962751 1250 280961501 280961539
    0xf0106110109020d32030301090f0510090c1b05030406020106060c030c08030709030b0703090506090a02010e10050705030c0313060e0306180c0a18180308040602030c0d0515 76
    0x1080302c0e5004010f06441c150710f0b00ca180820210110981030405002009200340a91a8104040c081040001c0d40e40c0e40c10f0081c03190940cad0031100b144250905081c18045038544096440040d0345030090009400717030a07010201c030509405202c5a1aa0320003010480c00e1160120092042d10f24540007440350981c0ca450880d20001102c0000d00000c2c03501da40c110016401c00019904000303a4038284c02c103075441e6141c1215005040d520000400d41d5503000404009080c045698007400c143c010742500b03020764001a0101c4500844130f071180000d0403035500030342d0060055680040c0c0082c1229200c1c0f40b034014a50303480c0c1c00680c2c141d11210740b02c0d0300050420711403072810320a518054040c060b5500c075291a0051070361882601e09882c0100d464241c0c035919822500c078003c00c01c4001d0032452011034103400d0300301c0b105161003039025010b0880e01004650403d120981090f0700240041e680d0b40d5070100c107100c0b4003d0350142291141040305221440480100003041400100e81110600765146024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 280964001 1250 280962751 280962761
    0x40210020307260d110c06070e0a0b07081603021b040213090203060d140a03080105060403052e090b06040e0606010912020a120803090d05070209040803090f060f01061101 75
    0x5098848207000d0322001c40f08051204a00c03032061a10504060f0241c11400070b48600240c0c2641559010036425241201000740b03070741002c0c40d41009a80e4000180104035017140c01d0040301c899107030025640e810040241c0449101c01a030b8010705174048260b1600039110010b00740c81d01c802d99401d9916a1007881c00f44200c900035180c405003102d03024070f0a04108040c1d013008001c40d0744800c030221440e0103d2800418508001b0070080685006107041c5005003c01c4811381210b402200103002c00e00000c0c40c005172800400000301d910300c0c00708a0300d045000e024812191140106030410900d6000c129072460fa20f802a030b42242c003800410707045d841711a80c0b14800c4030b05c0e0707001600d082010404808541c0c1c28402c40c9001170310700c0d01982d07102d0700b00e04c41f642e20100044804040c00401c00034aa10103025000c844009403a15510781281500014800140504040e0a44e440000410708005080007034051000703541055400c0c5281135039410440017024031940000c11041510080b102c501841a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 280965251 1250 280964001 280964003
    0x30708011a0103050402030a0c1e060201020f0405012d0305071d030d0e010324050f03070308120a1b020f06010f0b0304200d060b0a0b180405090c1305040210020307 72
    0x140400c285080044014020145c81a80c1500981c10a100802c16801c4036802500c03410900020070000e00a0031840303009180d00c803408591044c00b544070b0201001003140c040300c8003483c1088488550058806280d400300c100c16502d013801e85824030b201e98240c1c018a204040c59201e601c42a81501d8072241c0741050b5848040e415000f0600c00c2990600900c40460001010b2400080c50b0700140c01d0015504803c1c2e40034698000c07214001c0125241400703c42444050980260110602d181c0d60380066000d130b004e038505550f02e00b40026054103e5a030000020070640c0011180507031034680082d4443c050b62080352194000c80d00086403090030703c0848011541c40c082c2c11450341e569919a50300c0d03400641d40d0a141034691809a11060351111440c070501d6024000018460b0350510802103403104076030003072420010a00160710304100100c000203c402080c0c60104481c0d03500140182000211121035030700030000034801e904680326a10592085100742d1b41c942c0c0c1c1d00754058060380c2c2c074060321074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 280966501 1250 280965251 280965281
    0x6130e030307210f0501051002010c0f05031b1c27030c05070e0405030307021b0a060e030114071205010e130206280309030e090601020c120c09090a0203070801 70
    0x804140c42030711031804640f0180f101e000840c220b00d02c038030400d0f041d5040c042041c1035890301c940050200d0b10b082d44000346d51128070b000800c2202034082002d82071002d4080c41e5411b010005c400164800d0080400603074440403122071960398007a542201d0300244100e914840c220b4608003202c2c40d000c06c00100c040003c14030506802d1583d070155812914920f0310002241c0e44e025581d070008a0241603107016000c2c901c5080516160f15103050020f06c0d01001c090301c840d103840c3d101021880381d1184c1da00c10b82034400500d0000004c00700c0c1404079003d021184030581c2041815070801030880d6002d40c440d01055a07000040c42580d0fa214a182c0c032403041644c0c04506c0b6680484800d005260020003412450000f074001a4805003103c2904600030031448120042520747c0250b504055006411410b105e00840d450401420319a0000b5a148c10710306c140b85c080d4050319802c5100690401884c0d4882038010000c002c03901c0c1c9100c01ca505c4a0300c0038000c90113481151000f02d0301480600981d440038000c56 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 280967751 1250 280966501 280966507
    0xc0305070e1311070c150f02160e0423070801240b09031011030f011508010506030705040b0c01020a0e060403150b1c06201c0b030316030806130e03 65
    0x1809040108020180045a40410801340e800203141c1402100280602a00290350040c000e07005085a0b807052420421504400003c1e45e540c401c286102c01941c0805404008a41e41c1c0d00d04541220320110340c1248440d1100f801c80d156040005a240945038114004e0140740203001145151407084120950b140700303400018850742c030468020342800d0030003c04580540e810300010f40225503404c404c03010800400410001c1d14030845105500420700032018000e10920560003c00c0c1c0d013018020540f040000001007041203118405580c00340011100b00c50b9650308100c4103034003c0d0320222141010910100d1741c0107442ca089015201160342001c0c070980e2403e1220707040001003040b0100c07540e0000400130b1000304010903d40e050059440340fa400141c00348803006103540030200d40c0642403c0b100800c0182da01c14200200c1042c8014003030300c0803d2841c0150000390450060120004030103020003628014154000380b8903014001c20380c0c00a181e01800145001a54050319171411158010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 280969001 1250 280967751 280967779
    0x2040e0f0705040f080703031b0b0402150d14040b010801050f0a09030507060c05070b060405160c02180705270a030809030a02120a0501270f0507030f060c0305070e 72
    0xe640019484480d0b86800e910b001c2c0c44060030b580c0c1560f00e4001da1101d50011000307008141d080341c1c0002004c00301f148800090340e107070b0703075031305883e18004100a0107408001031041d00210000c1c03ea0301007200d0a84180300c1d641090580d007459010407241598000c09603000007411a2041c490b9034003592000c041010039907203401c100c1b40a404004022001c004c010081440451486d11696480309520341e0b032544e94441c00c4c2042cad403001c4405041d041c4238925000601141d00341252030040b01e21818109084404403500018280d0f1038501c070080ca1012003030f0100180c995200004000000100d0207031500054111034001c0d40c40d081552842d08030210040038800300e28004040c2c02c0d5010f004044407241d000d2070b804100d031100541034408160344041e1040c4100300003801000c0ca80c05600c9031402c4410131300002008499904e05028181c241d0403e2036009000c428010140616040031804140c0b07a40751030507100400c10b4008580c00030f840d02c2d011601c69881044404c524030802014510300f0700341c4c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 280970251 1250 280969001 280969021
    0x70c050904150c050406030e011401140d060e010902120a02010e0909011805010b030c0d020f0420030c120f1b03090a060e0d0912081e12131502040e 65
    0x40c0082d10342903900001200d548007540a402500d00c156030740d140e201c910b00349003d000e41c0c2d5141b0000b1156410401d82070202e4150007100d504451400c000c170303041c0c1e400703000104214454a24000e0070143c10103440c0390500c13005402090715903100380e072040d041c2c0e1001c0661503160701040d4802030000d40c601403e00d03214504030800c1501b22501030000070392001d00703050220031600f510000b00c070140d450711803202080c03405000c0301c0c800301e074242c0f0904161045503000601010440901c544107943d00c0c4075402410110300f2003000492403810003a0f983c0e04000c0c030b50840d560040c3e00001720350fa100714001840c001555020318050310068080c203c0314010403101001e150002000d0b140203102c0e1100100c00f00c0d0701401400140003601c000750040740341ca40b0004000c5000c135000000f031070407141040303c001424807046800c944c0c100780c4500c0700224110001130451040304100d07045c4900d000d090000e00e00060142c40c20032841501c45460380303502c440075801039020b9441000f42c0e01203548001018110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 280971501 1250 280970251 280970269
    0x702030304060f0e0d3915020403050304180c090b070605040201032309010c050c0d030b012105060109080c13051306021c060503072417071112070c05 66
    0x69003550200c0e140c000c0380304c0d43d0703d0301c0d540c240c1c01c1000078451501003c4041440c80d1148418810301440020703400c045003100d803001500c0303600130070040603505180710308802681a00c001c0c540c4142520b47d6956a0025004444806c0351613079001898520075482d48d50046056008459020340140e0401c1407a803258001410300070310603814145c41c0d0383c0402460103420503441c2250b45504c105181414910350050071203000c65498000c1c000200000e8404190000c0d03404840702583c0b034086a0820b01000488007201c1a4860707205201405941c1826004039401c030f41d218007070a903240090b40d50780d651240c1d683e00c10014290b400aa0f0820440e18100e65604101da110103008041501c4202341c3c1d69050483e8842001e4400d00059a00340925401050049400500c03085004084281c106031140c0040c00f540420444525900514100c03001e0040c5aa40f0f580744143e158541d0602d8140701c06049260f040c107074590a40100c001000b1410105021348040e5074022441501c03442c20703d410b02c40000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 280972751 1250 280971501 280971521
    0x10e01090b0f03060c07031b1e05030d1a130504032012030c0301030b1f090b0301090204060e1501140a140f0d20070b0c030a0204170a031403070203030406 68
    0x4801c5241446603101081004e00840c030850700d8546c0c030204c9080003020040b480100340c80880354283c000c030110389003d03003074022030403001101d0192014501d02a851031003200300d0380000c035042003d1051900c810075036000c4054400c0ea03800b06500080554181151011640140482c061903958450f488044502c078013016000070403100b00f0a264400e4001075002150201d181c1000040180200700c240801c0c3c44d00320000100050024550100c072401c5240c0324050700d002c0540e6210400c4407641c0c250080d15410f40c010f00200b0400c0c3c4c0312000382210074009c445005100009803040c000c25440f0306030501c12075110b69046c03130902c011030074200c81040c0390001e401400042400000e1440b040100205000c0031521380c0000d50104840c003595605014584204602c501440301c47c02041c55940100c1d441940400d0030b030f13501e50360303607071280000c0c05690441c0c4514103100321600210b90001038251300d41406521070540040320741701e190321a0b11017200c94800580040c40840c0000c0c5080e0041a125 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 280974001 1250 280972751 280972759
    0x90a030e030709060f0812040b030a02090d150c0e0a121502040b1314101b02060d020a030f1a031011190522050f060c0106030c06020a050c0306010e01090b 68
    0x5541d0f8180356415107109400c0312101c084281e01c02c00a02c0b40420420064580c20b5580300c0c03d0902c4c0501703a00c1d141c01b00030800e802d025000280c1c214140d5600e9408696241d00c003c1d40441146440303d25030080c8840e4181001003515008060b24618080b0209000c0f1024125042c007100080e5545010110465100d500f40d00c2e024030011540d02e19401c084c103070038056070110061300c5190003c201750030080020b14074003604126010710803082d40079011701090a04440c240c01c40070814400b155861043c106000c00e2248003180c0c580d03d813030b49a000000a26640841484640d440782183c0b2035504202c60b8040c0d165000c0e4180980001d00342d080100d20192480341d42c0e00b0884031500054180003060304241c0000c80000e5081c0d0f4903130945c1c5491000404952803040030030b007000046464100304944580c0310f8040841d404000d114250080350145500c5515140a1a640c20002c1d40c0c03001c68120071980c50246661004503402c0000d10b15048803e104510ba00c50b0340380007248c00003014514501600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 280975251 1250 280974001 280974013
    0x604050103111204030c12080105060f0a0c05030a03060e0c090901180f020f071b0302031905031603110609061506070201030b09010303181410030506280e0a0203090a030e03 76
    0x242d190102d90b01e500c524025115000310042c5480c000840d4411f0381211014400c1e4140107000c40c6c0c4842041d00e0000018a052a940d4102070405503000440f003070b401044c034400000c1802c00ba5501d43c00c028100c605000900b40c00d91030b8101c200300340d40140340c5c81d02e40046080340100541000d030060103030100702c03805002504000702449207040e80d126030750442c1841000598074082181e05819440a030515020026102e810340d40040d031901d85100040c80b910307803c4010b040520030305008451182c0306142c20b82049915619001c1c18001c014032840e6042e0103032500103103000101183d540c0c0f0640050605580c0040501d04115094004140c1a070402d41e0b1200c480000361240a4083c7c0a14000c2d1101200035990403520314044156400c06010302c40c042c80c0d01d80a580701c600d203103030002e90715003004101d40d5140808100942d07034002110071560700010112400081801c0b081381650743c0008120002d549113400941070307200642e503203007080d401041000d021a200c0c0c0001d0140000007029201 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 280976501 1250 280975251 280975267
    0x80601080325120c0c050306130b07120608071502061918050a03020c0301180b0f04030c020a1d0f0702060712200c010b040506010210091e030816030b060405010311 72
    0x10061031115500010034580c070b81913400d0040440e40740e0b0051500320000c082616285250081c00420f070180204150301c90004658440e004034900c00300b4036507030f000400c030171030b650a261940c44043e0f108900c5c4111402c0181411244013155591050481903240300000500100400c01485a0240c1e045005d20800c100000164180420380708140654010005143e40604040c02c5445504403034800c8150008060001201c00303402c1ea0b400104451040c0d002c3d83c4900301a81d2403032210100a40c00070b01c2200104144001c0e82800000a8100700000c0c1240e4504000c7c0300c15880c1030308c4040143e48004002240c9601c11680c13040c421741c1d100f101107901d265401e48251400d48064440c41f82e030601003901105094244102005440100e5090080e4180940007030344400200d03c0f550300d42500c81200c002032120f00f114a20700e030405030001d40da01c0c0e0003600b40140811429207580040d00daa003000310001c140f0030302518446800081c9402d14107880c010045d0024440407000700018003050003009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 280977751 1250 280976501 280976513
    0x15041d0a020d0f090209010509310231050606070b090a200112020a0905150f04060c020913031e0c02180619080712050c04050a15080601080325 63
    0x1070320740c00101e004a44c0020510410905030b9058002d80d01520012003086030740c3d40003200e520110407070403420a002c0300d4680d958070042e084600c000703508032000034103420f00d0300c044d6162065038015a030b0a10b485484900103d5094a00c16211a07501510078054000400c0400700c120f90000d80d44030440e840c04040f030391182c0402003075420000c07081b40280020314003540c0162803100030070303401c5004625000900310082c00007440b60196500980481100304101101e5604403103400c0030398a40c1c10740b980d40d100e41c001d00016011008074011a04880865249403283c0c511101259160310381c070085411401d01d6560401e440c084010030803000e00c442401503103ea81d02c1c41000e0b0b07840ca0040742189441400e008044403420806952003009240800c003200d008201601603441211103d407032124039080036480c100032064102c2d0302507e80003d0054485044e400600c01c0d11107105408ac80356681c0b40000c0c0c0711442449a44a140c0041007032510404110880e102910030120f400c05000c501602d0320 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 280979001 1250 280977751 280977761
    0x70f060f02091e01030c0c051507090b03010f05040f0e0a08130513061a0a1b060608151005011b0b2701021315120c0e1e15041d0a020d 59
    0x1d03203d40140d100300a0401e5a050140c0c071401210390400c404a07032495552070b40d030340d20720403d1301c2440003404010454441c0b240310f90000a200582c0e120ba01c2c1d507121080c1ca55440c1e850701c51184128540301c444139622409008404c8040b4118000d0301807428280c90704410350b44511014500e4182d003110209207039480c5c0030480c83c00340001d000001c40c0d500b020340200c03181041295269801006010044900e03600403507640800c400039003010080c0c0410b19006015044a80040e1458060801c130b5060346c0c104100b906100c0c24a100320f116140c1e5031400152000030b070840254218210030740703590006c1210650030b950440b0303c8108545240440720209200400d40d51203408283e5000136480c40448003111000000d046003180d9210031503400030014011002c0e11400c85039242d05c4056030192a40100d4510300b003258043d0510404e140712146503d041c0084c41c415911a1807065180082c400c40002030310305507040344009034050310b001d007480600754100400321200a40c08101008605000d4014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 280980251 1250 280979001 280979029
    0x60a051c110f06040902121003051c12020307030b1f020312041703010b03010f050f0a18061a091908190c051806090a090b07030b011103161403070f060f0209 69
    0x5891f404035030b030903680c0100b015299031206000f04401307001048020591058500e00c5a007404241001c80d00141c842e08000f00c01c00a9282c40802040f40d0f054054005410001c0e04644000082941180c860006645103c000c80103a02c144800108000c8103940b05401c14051103100c0c120007848207901165520903080010582c00220041140e2040ca9102601402040b15034404081d40b41c00410301c030b000a44a440102d6035600d509440306912503010901401c50050010070908015011282d250300180c0c507140184290050750522409499610301519448800341c000052282850791040f81d40040540d030300c071400100042c86d0b5907016090001000c3d8541c090380d6602d03042e820090341070001013078200d240d800c02081c003000500024545501c5040c0c3e042c0001d04030b45000040710020403500c0f800c140e920002801520041020500146540c80342c4071900a401c85860000c0e124082e030100202030300010610003000170b600f0b401020074107101720710040c205203074000061a082c100e605 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 280981501 1250 280980251 280980269
    0xb120d02070f14060f0304080702040f1d0601031e080c010507020601031a090d11030913050901180c0b0a03020c030a03090b130b04060209060f07050105060a051c110f0604 75
    0x1c020040b22140080c88001841c0700c528241510701420007154241c42002c05441254500200082c1003118140542d803003203801410030452883c44000440040c01205103e44c0241c010010030215a1000188141a0b80c0d000e0a00c40d021020340700c6800041c4540e140c201d4040c2c00070700c0700801456091081c0c52055070300350700605095244d0b0800c5a00307070030000c69150104980b001040001080003420210901c02e03407400704104000b8914041c01c601038400301c164441d62030b00094100e00d1440d0020b6000d42c20302070081240e4400b12006070448021100000c1001581c01d0082142e5920300b40900129000b60034050702e88100d8104c0d26045901c2085000040b079520840c5100317000000505540c007541c50503442c40c0984e12a140c040b80010b00900040002d600010a00d050b500c0d950191403a001c1c2c044942610ba54a5107483c40c0a40701c00c60303065002d01c200b580b00054a291036181011042120510b000ba0300406031188620380180900b45030708901c2034403154183d519050014001010152 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 280982751 1250 280981501 280981513
    0xa090b391e010b03031908161b02060405060a0224040c060302070615080a03020622080708090907110d0c020906060a1701180609020406090b0a0e040609050f16080a0b120d02 76
    0x6c0003d0101c090190051448098450554070344035049040c1c2c0444545012508008401600c005940c030b10441e0080768100703601198040750281c0009a030050758060a69140c150315514036112103500c001c880c0a0516144960200081170095000700507440c0188030100b195012041140340d180c007658401c00700740d404100048141681401840d8204140310070844c071909980d022042c1d000308180018000510014083e81040300b500c00321208a18042e008251918000700050610400c04030000954041c806840c42054440d142002d400c3d40d008100980507210b02c8280005074001045003020b001c0c40450014140000c0d140d428000c00c1e8410081885041c18030b1000305690b200c0e4000010070b030041c0024446180c00c00050b03000c2d5072100d40410744480c4882c40c22940180c40201317060f04140b43c4030012860800ca604094440e50980c4d48120040c1c449501e4641c180307503c0390120300011484400314070041e82c150000c804001000746038800001d88210403a00f0001d03100c000c0c0300564000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 280984001 1250 280982751 280982797
    0x10c08060f010908061504060e07081b0403231504050303060f0a050607060507120f200703090b0a020708060c040603140118020a090b391e010b0303 65
    0x1a0640c81d550400038641160392500d8010350035035554014003c950a030fa1902c1c402c54083e11542e010300001d204070301d040c43d031a04005501a00100040c6c95480000d81400c031980c000d44905d00c12034003102e504c80b20704004201c101d861012456800003c0d20120300a1101d82c3c2921282c0500046c02580904050341d43c038107004e401c1210f16800c607200c46014884105080140d95590742c140c1d00815008600030030940d4500788202c03880d540d4481c1c002a030915204074001107401e56400800e0148541c04005490440c06403648038078003d14000500043c200b0b4030a000f1000040c1c090000786199004444040d038031041102d051080445642082c60000301c2c0801c6400e500d8040e0650000075111101e1023941464040d121403140c1e42411071800d43c00281c0304869030b220340300c0f54000700200360040392120410700c0c154110f401c0c2460040d200d203c00e94a11725065045000010710060140001e1043c105080a81c10039404030481c43c02040d5a107003800340464400740020140c8090303044031142c0c5d039002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 280985251 1250 280984001 280984009
    0xa1409120106061116030f0203160b070201030f020306060306010f02120708030a05010605161e14030703080f070c030804061808030702070b1602010819020417060108010e030910050c010c0806 84
    0x4082c0004003617842150404038003502c00000c4403c3d40e811000c2c840ca00c210500101c1d283c01d102d1014078032580c55400300001da0050100c00b03001114400d0f601032010909983c0040b003607000c15038500b80d0041082001c86c507198040c44d0f01e84010f0003030f4016214400074140401c68a600408815284035900008000c81d000e0140f107070501601c501d040560500004144402c59000c446c0001091456007540c22400f0840d070394003200700f0551010310031302050101500261039801c2900124081801d000110303a40e03011410701c06100c0c080350b640303010320002c0c10b0300c0032200024003070015520f0640d200000a005944104e00b0b48404e40114846581e0b8209100f0003442c02c852070f400061007074800d100c0240c001da049040c852465409103415003072500c651801058541160500c20610352000a00250440e20003411403d004014010f45a440e079860201c0c50903240c070b0b206c91411980003002408040d140c801400d4400c40083d2518038140a0403004a0b0b0849070f64408010124000c00304109079450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 280986501 1250 280985251 280985267
    0x9031609090c08010219180b0d0c030507020c24040506031302090108010501030209041121010e0d140409020307020f0f0c100c020a090c02010902030307060b010e030d050a140912010606 81
    0x4101c00218508031001b0010300c40710508002c2101005218061101c0d191410b802213005003501c007071301940c0e82d102119108020703c2c0e540349a034046410540055002400850300385140310001e8591010860348011040c01403400c0251240d000c101800301003a01c1d01c0d07020141d48280780c41803541c000d0701c240d170040055000c0141e0200015a0501c8014001030320b4034a803003500540e1040388121351444c02d500103a1304200300ca00b40902513220524101c3d2004054104442e0840310005680070110b00c410100c5110030810f8421003460001c02c0200300a400c1340c0d0065a21581a2064030301d56801891381030300b80780313406a01302c0f100d51103050b8403452490700700d452200800032401c1003d12440c140e40400c148034414402e01444564529048031454001c0d04040001e9a004090300d54500303036850709600411002e508980011500340e0b07a4121030a002944200b18000c64880c2e608203070601508554217441c81841c40e140100a2110364240e48819811050800600001007001810300074003c241039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 280987751 1250 280986501 280986509
    0x408070b010e16030b040603020306040309051905030a11040b061207180303020d0f180e0f0606030f041101051315020c0f0a05011d1504030605090a0b0c09031609090c 73
    0x1160710b0003445100c01900d8001e0790501c2c040c2c00d010a12a80800015004091560003c0d42602500b0100000c0562140c12030040e0380044600d008204d100220750b0b01d10002c40c1c02038a4055020004000200c0c811500c0d00003100c100a101148080020004c0b407641d40158001a481c285140c0038803e13850b400c0814043c2d40ca000e0350400e1442451920000d6840d903101d0119030502c2001c1c4c0c1c04209180c45644c50324003040d0382594003074a04c1e40d100c0c0007202aa4040790f004000350a500e020840c145411400c80e07000b06460501120240c6440d100d412044075940720700e44c14840c0401c9180000c1c80d20040c44002450807580032050b040c05054081c0c140b80f042c4d0581803050b4080703c00041d4643d03e0035103860645400b80707402910560200d650081020440303042c1075110400750b0f40e261110711180000d206991140009001b2515030803521580e940c14075034000e181d5480c0000048000e540a4054400715000404a03180740f4094a900c004e90039180d0070030100251910341000500c0400c00c0028018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 280989001 1250 280987751 280987769
    0xf0f1b0604110d0302070b0c0c01030b0612010506030c12070503060306060a06320c010504171206010c1e11030c06041a090607061407030e03070b06040519050408070b01 74
    0x281c0340c1640d400c8201c5814440e02e40c40703980c01c2c0861509261081042e07001804c4204034060751001c41e044079968030541038043d10f00003800c143d00020a41480e1303041c1c0305089460f004001e440d9080c0401c1020725040141680c40e400343c1440005480812014018003694581e00c8107a40c134142442814140707007004109901440240504110aa52180082d0701c0071000341290a103d25402488034111011082d420800740301c0842e81c50a03500c019800303240554402d50342040c030100b2041d00b0004c3c074003034052100b000101500004006500990346e032a0b0440c880c003600e85690321601c4400c0d1505a8410055454078200d88400c0401c0c1000c015200c034110b82116141d09140c1f400307450700782c07002254142607c141c50202e03030002e054a500040d03c00300c990140741441100c050058001180e03e00300c5c0c1da0b10000307040442a481c204404002c882201e03810800c240180e075102030600014250140c100703844107244401500e01140d50388a0540a644100401e07a40c1c0c003114103002c552800103801c01c3d000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 280990251 1250 280989001 280989013
    0x70f1a07020328080d020d05090a050d030c050f030a0e070b070809100c050d030c260403210e0c09070302030907060e19090b01030f020a0c03140f0f1b 66
    0xd40da002803c600410082e0006615028034621140c082c4404104000c004290128001301c416030584c0181c0006800e96408021550f0f0b100e01c2a0365035001e0740381c0035205820800900c2441c03482034001500340289424118603041c140b003010700304d680c4111340d41041d480c4d03107000c040d4003e40706008810003040342c3c0c070850381480c4d41504d80204601c6072240c80391103104028401c40c42d990155582910f502d400105035420040c41907070140142c07600c040c210340010100744001034400c202d25807081910002c082041d1550355540e5040d1000302c1c603d0f9802c03030941d481d0502d00d070006040313020341c500095035200036004204418050014921000e4228002e050041c000c00501036000100e00c021201c05152440400c0c0315040440c84071110b003040495002c0009001017510609600f1406403050280d0342084140e84400d6210102d006420221001038030b06403411010912603549c140c5100704420340da51920384030051850103030f401101451252007000c00c604881c50600c8072100d4640c401a806804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 280991501 1250 280990251 280990253
    0xb040b010f050f090a08060c030f060d0c030602031f080307020306060d05120f070533040c05010e040e01090605041707050a0b180d0e0301060b091f11070f1a07 70
    0x8154043d0400d603010714440441d1812441e503ca500030001011014141c1303140341080021440951b10440c0c03200c81000c030480204e01281403c10f0741d40e03030240c1c00c90b510f000d19a083d9528880603500242c0b0310b060700307000411030302d0b0480003882e0103000800c4194000d55440308103105050500c28020b00c60b0744100c030140d07074241c0850800300f4042c04a079141c041580da1900149200c42c5d50380108132010705507200e104818401d002d00034609510710f08010000e001e40500030246178510b0780c4100c0d0700504180a542c02007045500501220010f040010008108803850002c2d00e421520102c0c010340706542c46000740024001d48110700051041228050b51a01d20680c60755603842d018000300420101c07040c40000c0128007907000c0040303070143d000c05581c100ca042c528004c18101044000901c65464039800142031b601c2c07402100e600e000041c0403011038026000081400141200f800b10521a844a0700d4000300810301c0440058143c012401c0881c40c149040c4001e0a8648520362054100800104c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 280992751 1250 280991501 280991507
    0x30306060f0c0a080f07060f0e0a02012a0605010510020a0b040f150f0504050115140f0105040312020123010608060f06091c050c0108010b041206020415030b040b010f 73
    0x218a0201001829a00c41036061141d14203c031240001d80f404001185090442a00000a091143c02108184032034001c8003007000490319540502c820640c0800c3c0b0031801035004e048020303000300385202e20014680d02d0b4020600150301c2510308880e09982c0e80010302840c601b031540c00700f0300d040910080499a2071640d4090701514081e00160100b0102c01105040100d16903000504c030040c00f1302409401d005502900141809840440b003d50030941d69400a503441200482100e882049000e14079051300180030b1800780001241d070402808000200c04182c011010000c01c1c4800d40c000a910301102c107082020001080020792040d071058010401c49034805405600214110f0701a14a1040303100018014403d1556103a00403003d01081c1003c50f01145071180c0203405034080d43e00301c6809030011280c0040c01d0154a94a0b4000d21080c0070158198810381c40c224420b2030010718050316806040c0d4006c0703600e084480045d8603a000c5000505050180d603440c02402c0c200328076a06070190001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 280994001 1250 280992751 280992757
    0x6100e010f080a09020a0b12010b1c0b040b090f1005090103170a090e0a0917090a06180503012a0801140f030a06090305090a0f0819050c030607020708010b010203030606 74
    0x9500300802c1101041c1418803a070b0206400c180c3c002c00104070f040e0b80b00d01e0000340f5040401d91101e120000b4000089949404003114510203130524080c00810382c04c0e070014001e00b014404260021b83c0c584ca20740e41038a401c80b01d2400350700c8003400c14219142000d8001015031403031300b105001c0c08007040104001034400218178110041801d8081d01c8540f0034204440766003441d485101d0b41e0003940e00b41b09070300d0b4003a03100030f800a010b100306180650388440d02a00d07a21682c3c5030103400102051080080a2003000349204104114800c000e6030743d924000070b82543c80d00c3c442d51040c9d00d10003464480c1c981905000c2841c03558981000103556140030350307405c6170301000501140221f007910034030070440d0fa052003e0295036074080420819500d003406c0c01006504191100c9015003005003000c07030491008035045048440101c010030810703c44200c000c0c11001c0d0f908040f181840762003070000e4039680c00e0207981c2c030540d03107a0700a0541920f811911820b440300500301c20b040d90001c200b841001e880e01411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 280995251 1250 280994001 280994027
    0x50409180f03050315011106010308250309140102160e0c0c0304140a0b03010305030d0b060408010c030c02061308040510021c0c0b06011407060c12090303020306100e01 74
    0x640c49041805544440350009801040300281e009428200354100c40a14002c294510a03d002808000c0040d44d04261840301600c16a00a000400004521000070400c44003a0807282d142c41918403043d030b0b4070361407401045000c03840b400d4050045008150701146100401d2006083c0c115007880e0860844200c0c0c052000c0011140002408100320141101c41059040701100c0d81c655560203960003403400300403094460782d812440041e031010920b00340c90599411101a51500884140040c01444078001c0b40350002024400010050401c1c881d0703180c00000d03520b011551092800d002400d2000050010004400d1040180003040851003500d003a21000c2e40c44246000c030800d41a454250451031511008143d5061030301d02c1c542c4620196070061080001450300d8613401d006485d18504000c4000301c1d4981400f50201207040c58114075906007407418258030b0f00c841c2231420001d40702552815808260000305224071400c1c65540b101280020740381c50f2444140900000708913681d5001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 280996501 1250 280995251 280995269
    0x10e180604180f0c06030905030301150c08120a05090102030108030a05130e090d020f070e06041d01021303110906060307050a02070b04090c030e16060c0c180203011a0a0504 76
    0x80010800e4645902c44419075080042d40d065081075480c0844001030801000c81c0c24110b980c4001a080c2c3c0a40100f07003400b54004042c5045a082880c80c001e29078a0322841d00030072000002020114444178010216499081941945851b09a98000941d14050040d081c40d07071041004100c00300d40402a9101c080203840c1687d42c920490200c6803800000360803044071001b40d1400d00c0103001001495860300c1101d9001e5410003040140d000d0f4071549284207250703031b044102c0002049807800394040b84441e103d050011094500e003220140c00c80c0c01c010000b0300100204103052007030010301c8003052080b507070884180ca0380340703403100200d45d00e0301016203904180440490b5403594a4020711810003d0b020380c0b6019070f01c652340c0341c207a0350262480448082c04a07140c2143d224100c0f00204d041802c4680c0915641002841d01ea412241090b8103001907900307040042001c138040510401c26030140000070b80150322541000494400d911003c80700e8140309200700181902c00b81c1090666003103859482c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 280997751 1250 280996501 280996549
    0x10207050d030e040c02010912030507080601200f0c18090307080306060409051f0e040201021f020906030c07060e150a0f110c0d02012d050601051e0a020606010e 71
    0xb1506550420000a11a50142c101310040d0716150b81580031040040c050860b6100b070b00780718001501100e100380e41c00301c00101d8800005840b9400b4a940542c1c21702d143d01041004210071b40924145209c0440004103600030110b02245072900c00803603002e540030036565510340d040c114210769483c41440f500820f014001b10010b0000e503070704001c0d2801402c48480c18041447e04078001102d0350051b4180044003c450740b00030404800b03004a491160f98187c0040ca034901210360300e00e8036186912064084180c00f0840d02c0c1e0207446401c0514015101035030a03640798001c07842c0c4202561480313407091102e5401001040380c1310019000d01c64100c045c0740c40000700714040307541d01c0d0040c0490b0026880d50030000520900803860009244c10300d40410f6000b0081d6909100c64034480d0700c00c0c81c5900e0329400640e0000056410303d94001d03a001641414000d10b4100c12030182c0c00e40d402d09110315100c0030030203c4e04a008a0b01840440c0d4444000d01c1c041c1b14003509803000a40c0c801802c40b0500c6401550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 280999001 1250 280997751 280997753
    0x3010e1c05070c290702010c02040e010609060b07050706050c0303010306021c14040203150106020d180e01030c08150705070f060908031009111305090712141501020c010207050d 78
    0x24030460b2001a0802c84107a0ba140c3c80b2085507603283c0070481c122184003040f01058680c0492801030b1400710394140e503691880d041903001c00001d00110303d0400c544c2e55030b42000040310a101d2060364010455583c046881c2c1c2014148542804241d5110390140802084901c0d8030b924040304a0381503d6101c0c40040c1c42d09030300c2300c00c0011401056039407a80c642c40c1c41005900040e091145c24072a500c224200c0710030442d09507414014500a104000150344401c407030100c090300825001c02d00700070380401400e0f625502e03d201c0000355001c0e4400e41d500343e43d081c4107212405040c000d80e01c002000d03903220345150400d100e00406d940f007030700b030068419107401c150682001096000210a035420094040d102d041000301081a01054442c00d0300c0c0e60f01c0c01c408011040a04025a580e8040f030307440c00e0b003034145018184400c0040080024042040071060b41e04c04403544d1140e11080010503803600c1c100d14041c22456002c1e068500b5060565101c482900e01513a400100c65080e80c105a03200100b413050707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 281000251 1250 280999001 280999007
    0x24020403050106060324051e04020c07030f0b09010b01050409050405030d050a020d0b01021204050405040503040b070803060f01020f1002090f0310050601020114010b0708070213181103010e1c 84
    0x620340004100354200280041c070282d02d40c0100fa03100d1081c3c0d503001001c00011800602554061145030f400c100780900300f040400701d91722030101802025001624144c0101441803d02210f60004c40f0032001010100061011808200c1d0f0b2240e00d0000070001501c0400010b0640e0080d40310328445030f5180c038006002c000d02442500c005281034035003849942040403403d400794104e0400d0594803454225010203d620000350b0a001c0c2404811079450f19080c482400084c0c04014404c2d650f521040000040d480100001482ca5074091814039071281803c40030003032810b64118001c0e046600182c081c0500040101e00106c445241e402d0050341e0700d041d1804190341881025240381e05d4040e107243c600142c601d0b5045944214806d80c02003100343e07240c68012000782401e01504403011028070840b0001100c8400501a00e130000303110002d1280461042001d41c1c0c210041d6403d06c1c0d40784a28801045108071039181072001c220300034840940c44500d840e64584034641020b142010030001103040c240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 281001501 1250 281000251 281000257
    0x1030f05070f02100b0901030f060204030f0c050a0f15030c110307051b090112080310050925080c070f080705011401140a0b030420060307030c02010e06042402 70
    0x94003030046140102000d00112040e05411002d03004102c61801940342070b01c1072080408008041c10820b07401c0d03454100f021800034404555055081102002150f05a11026900307440f0b012040112801e10341441042d50496110850344291072200f0b222045500d927801c2c03c64520741c5800203682d100308038211843c00028854804a000c0094440306010000c41d4110000441c11b103031000c581160024004122000d100300d41004004d4501e820000b460640116044074840c1d0070154260748034400111781c0c0340255004140046c1c0c050f042c694403a25006804a902c88178103005180745003042d8000000d22941800410603030150028900b0403034400161440319811038020400ca814017001402a90030a000e580d01c136048105138040181307070401480007a644a10f03250342c01c54560395100000d20440850002d000da00305900301c400c40d16040c004d07500c80c42c92550041408000703904081d003100d2a282c2c04901e5900800304100c003158040000802c000c80740f100d1510040981b05201d80280 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 281002751 1250 281001501 281001521
    0x151e0e04020d17041401030b12030307140c0d09030b090601050f040225140f0d0c03050a0c120915090807052101020310030b060103020711090c0c120a091217090103 72
    0x206000c02c4c0401e20a035014501140d0b40c13000c2e00c0401c0384000c0402005038941c01c008124045900800000b501207200d804100c07850440c0d801d0007814201c403083c00c42d042c21080c28a480c00140320240400c103002c1c00d40c0703250360045001c3c40648050b50402010500d40300c44110100c1c0205d400207041d9100c000101300c0380d0386012215103010008552841c1000c4122444901240a80719818201614441c08969003c0c6500c490b100c46210f03012035a070aa40b19044400f14130f0a00440c1014800850400b400c807102003010b80c1e0720590f4045c1803040700428100b8945d80300c0c0801820344800d11014000044920665a048801500c040020380400908205582074105030394000300600400e03444001904003a04c0c40f400740103000b6907903c00114228002c042000c0c203c210300c2c218160250a1040009400003800600d5614006050084519083c0d001c3c3e980901480001410030b007481e40040354401808041d050710780d0301205030325054010b00c1280c042e244102d100240014040e8001d500269040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 281004001 1250 281002751 281002793
    0x3071d01090b130503010c0801081c1124150a030f0606050a030506060109150e0103150b070b190b010203040b09041b120c08131113151e0e04020d 64
    0xd0400c02c000b5050b082c00d103202d813900a60921000342c1c00f442c002c0d04058107a41d502c2c0004d000b6811040b090109109504c0c0c000001d018020101c81403075030b802d00034401890110900054040c03082801032800c9200149200000e00841090070003a540d14004901220f8105c0c8501c4200c030360750b00380040104450340c4101d83c44444500004108400412070b548602026222040c00c00c0c3e90300022034544e9002c445100c001030031594029610340c02a4001c40824004a008858058071100c00c5002d41c0e1001105459004030002084000901c1d258649400c8030b0602c03044c01000c050382c0010b580c0f809180074100c26a14085142c45558885030f100742c001544840d21003101c01c900d20f0b80900714404502c4407180d0705041c446d01c0c0381a0341c05a210300707000c0c805001418040c15820782324500c9070091945103d90040220900c980d59103044e008145a0701040808014401d2503c4031242c0600709042c4a9003170100d50045c100a901c200802c8158000d8050302c010581190911342100301d01020030006481c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 281005251 1250 281004001 281004007
    0x110a051305040c120e010203060619110609010b0406120c03080f0f040306050402010e0a080d05071a07080108150f1501050d0908040501030b0604030c0b0705160b070b0a0203071d01090b 81
    0x2416a01c142910a0402613030f20400c059441c0c468500d00344d1100b1154150060300401004045042d000c0510403881810f18102c0501081c802c000390501c501643e0500039691180d90580780703480c09100b40d90003081103030001000d0f402d00340d5030511000c80318800035100b1000483d200c602d21076440215404900c020030443d60303a41c0c2724907007070307000b03240640e0182d001826100f0700c2600c0c2d0034160101410348600100400840807640c204481a9000900c01c603444403500c00840c4041c0040080540150100d440315652903040c2403c1d07034504010405c80304400c140c00b1050102c0740580c103040c143c000b004980c46502e8072902c0300c0140c0e0984070307010510701000d1a084919062050340380241c802d4810903a810f1200800880c2084624000c5d80809002d042460004000e9049444002d241c1c0b2803040d8159484000c522100c40c100184c51b510103090888009050410040414105039014956000c11801c60034003200040441c8050020001c1803000b9986800683e03008903424402880904c203420b035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 281006501 1250 281005251 281005271
    0x30b040b18070f0e0a020a09031403041a0306040c08070801050114071a010512010b060d1a0607120206060402210601030f0c050c07080a1502090406030605010905090c04110a05130504 80
    0xc030000c0d080c4203203510340c140d03140805c0c0d641c44c40e8000c0b61040341260351081c4483e800c40c2c5945c3d0368080c80c4400107105200030400010000000b00d01c80e401c40104080840d00e0346042c200740020b54680c2401d58080101000070064220341010b001c1d4151102841c02c085001042084001d6034843c212000d403445149941c1000c4041052450038141d0300300317071092440c0b0221010014243c411040150341c0c4030005010141c204080c3d680855845040e0382907040d6180c03033101c04555241c3c0260b80030b03240786581d081d51050031501002070b5900410190b0b002c40c5000d0550b11000c10310f0000d19000403040e04181c01003a610303032080c1c20001040ca08944104400b4840440c003401c036034003c3c1c400c0c1e030a038040d484001038014800304840c10b6168010035403038000607810008400a500c00030b101a0300956440c4040040340d01840b910b07020380b01d0800c0015680c2042c00517180b42c48000070802d0711540c2014654403561101d10241c403070001042c10120344680c64958428211421600301c95005880d12a06072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 281007751 1250 281006501 281006519
    0x2c0a050406060e06010207090f111b010b0f060f0c2503110a06020d0c06090b0f0f060906030c0d14010908120f090a03050702040f060e0a060b0301030b040b1807 70
    0x40c0650300c110020015190380e81c492610488080360b400303001da040031034204886c0c05180c000008441025900051232103000c41c5070b8403543c103c1d4403074000c80b45034076482c60080e40d400d118516020f5401c0b00c18503090681c210000385070703101d0307a0702da40c610300d001040d00020310f2401c100d070780d03100840701c40702c01c105c424524486201c044c0d00d4030050300c02d010810b690140d2410804084401d035211030b0f0141c05840340e1800241c0e881040307403204a404680d912000400300340005801d6000c2c1041881c0c1450038103041541c6003400401800403407003840c01c541400322542d80040c010500708410b0321048621082c60500e501a0f04c3c00f802480483e50030100c003542000303081c400405002c0c0301001c410f501070320303001030701240031a04441c0c0d0a22a03011511900201e40a01d000d000d20310300c02040410324520f021005400e4441035031003082c00114460030f100d0090300c0e501960307029181808003c1d09540c915181c0410400c0b024001402c914a0400422890310b220403400b8041c80752003044410301a520403480c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 281009001 1250 281007751 281007761
    0x6190302090436020a0e090703140c040c1e0f0311030108010509060f04170f0d020c0601030302070614030c030c07080a020a0b10120b0a020919030b060a0f2c0a 70
    0x40100c56182c4541d0b0031801a140f0010300c142e80d0080c10307031142c0d64245000008000740160070782c4041d11031104000000761010740c0d004415200344001d04081c41d403007810310040c1d07094203a00340103001844441c901c2a09415035a452040860b1410079440fa283c481d05800a18401d030060328034090000001c00c0d01c52054003c1c0c0c0c060782d0f180c0d0440d0256074130495404503440080e100107010072450a555015041018058159080e034103407000d140401214154080f40c0c00103220b0340aa4001c0e80042041c940c05104000040060b400d020750100c040303000180f101c0c4401012002658801b03c0400c0c40541c041e400d0b00d00040d4844440750341c0b001620f1010350f032866202012150303070702414000341452907405800c03401c6619001c40082c1c50089ca903a00305504c83d004020950a6509020400103540c2e10a042d451b4002e0341821410f800707041d0304041a000500501c200e01400c0d00c43c070304101c80040100b040048914001040710b42107440ca80004241c01629000721422902200740003c02150381d000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 281010251 1250 281009001 281009051
    0x60f0b03060f0f030d03050411040903020a021801290702041e05010915050d021206011202120615011d0a0e1609060203033121020c061903020904 64
    0x420b0124072410401c11400c00c080004140e0907030040c0c0c0303d90000314040e810980d0891303c10201805401c1d050310108085658500f001e07070041e80030209050039030a12800908041c5403c1d221440c480d03050201c440812943c2c0451543c00030491030142441810500682d00202c0c0e004006000080c090102c42c507103540d2800c00603070cd20f4900400052608100d00c03440c1a03441e0030030180084c1c0341c60801003007040d0740349400c1a604030f003094110380740d2480e0034481c41e4044c00182001040d40e0103d0b006102e440e035800d010142c1c142e400042070285c098441c80c1ea0a082c40703000d04c0c0083c54151070810380b8140806290070140c10228800011500741c1111070000e10490116021001c1c3c50300300c1d00200c44401052040d0f2000d82c00c2040810b1440d10b60005860420a0b00b488120341c2400d031030100c0b41c203000b9040703040c1c482c0c2c0da400c03d5010342c000e01072040c50400202e45c8000c1c0210262040013030912300c1108501d030140d50341c1c00000030b4124042d0b01922040c0704001d2040000040b007002c040211a07007621 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 281011501 1250 281010251 281010259
    0x5010f050601120204060f0c02130f0e0c0406080a0212030712021b0906090103140a080d0209010908070f0b030714031e0901090305040b0703090b030703060303020c0913060f060f0b0306 81
    0x50040303030f805038400d03075044504654403a4002401007805a4046090302e1042c0d0700031309001079056000074035000d45025402007a4002038082043d524003400c040182110520950400800300484503000071280316098044800d90303400c0e011103000034038610510400801d105861000070b0740258001c5145d880317a15407048080031985d9110200002d48904440c0c1c3c03a07100401c880144003081500d032042915007908021070380d143d2540d441395002c6410041e1081c01c00d40d00010030b0381c1d940d40d1080c162030051a20000801c030b00f40c10300314003100300c00480c040c01003860004800940c4d0ba40c414505941c48029070004141d59041501256180c40380e41c10011403440c0aa00c00320f510340c00144115011940c05946843c10329041008908403617100c02d0301034040041011010500d01e10a50040d0b019130b060f0707140014040d1661802905000c00e541809100389280c60822441100c9078101080240d403242000540034840c0c2c8012000f09090303000f104000d851103102042e040c403810001c43c0101c0c0c00312 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 281012751 1250 281011501 281011517
    0x12021608010b0112110d0c020f010608010b0406120203030f030603010209040903080a050c0a0212090f06040b0d0f0605181e010906061e020d1805190303030e0a2001050705010f050601 80
    0x1000c00c400d0b00c1090341784c01c400030340c01c212645030301446500890000101e4415075400c1c0f048044a42c0c00d403542a0410400780c0d640c0d51607486140b41600c071741e4005003400892558101c102d900003d0326405030140c4100c40d040c001000895995080d0704403050020300900801c180b40b10381c00c0080020804940c105120b604d004c0c00b0030100c803414002e4035280e6405600401150f81c5481407400d294000e050350302c1c0c2291103403001c18640da9800000e8000780021050f07aa031601088540d400581c1c0448084030601c5252075014003043d100c0510b490b60217665241c2210003078440129010381a4075012011144a40303070400460100354503000241200d44035550b20041c09260707544040c40d00140c842c207001590201086880040c0151034110307145540c0b1f81880507480daa240811308803441e108000301c0342481481e09100b09a0513100d51202503071044000c000514240d5a00301040d100040301210103864aa92890568030403021034521030381c03020003441240000351061025140580750b2a010032804 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 281014001 1250 281012751 281012777
    0x6030203070833010224041712011703091021060b0904050718031208010617040615090e0307050f061608130f050a060501091812021608010b01 63
    0xc1c00108181e01901d0143c0082c40010b1070310360340602d40c4058854154000c1800b540e0045506030314420b55002c0310190340c102ca240c14600803044083c01c1d1843c904000c4144034100106000c100d40f9810345524002c9503100042103940c0c03528601440c40316903803100410703400d07000b620392221008038000030b01e80242078841681c2100e54207443c0140141c100340c4105019451031403500350441500140d0a00f010111058080101045003003590410748007103051146124480364880c030414014100b0b0315240c050715000c0e44030498020b034060009000d0301d0311034000411440041080f5002894010403c00122118504051b00c035040940255002d0143c0815025400408203040f0300c6241d12490380200f05107010415075030b00c00003621b80001d00b98142080c40005042c0020100c220b4081d1008103050300251a214003a1a0140c00c1424442d0605607403941c0109200d0043c1400340e8020214454032200351b00803403818a06020106010f00e0030361300003a443c034041d841103410344000c0e41c1d9000d003c404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 281015251 1250 281014001 281014021
    0x50709320427031704050601180204140d030306091d011107020306040f030318060f060602012016082710050d0b030c09090106080106080109030207180207050106060302030708 77
    0xc0264600505000c800c0c07000c00c1c80c9980c10a05072001d100e0b040483c4454100e04e4070903800ea000311002c655580c05600180201c031541300c4151240c1408083c10351400d0b0828030124406040d420005004041d554610307410180070380c01800191503044030400141078010980c07891032001400780005035280461060060800808070340d10b2640140042c00785454a0350303004880b4040da01c0980c10181e8840d0712961a19070b15100480d035038042c0030003040805e282950201226441e81c04042036a1509149000c44114070f440440500d40503100da030b4440c44005110492407842000003050a800040c9101c0d444101290380542041e2044010203040d03216418003401071025045040404d100f44000d08448001b60406003d5180140030b46221b00c841502045030510b080c1c80105007651203140c1031100c0c40302403141200070090740700244030521003900e01a403104c1940c00f07207000900342e0501c1d01980490540490702c505502500070801281e81e00c030b0090003504151607610001d01c140300480e100d541 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 281016501 1250 281015251 281015261
    0x1810030b130c08121e0708030a050f060108100b1c0c020a12050414040f1805010f0c0c020619020a0c09020703030c050903061909050601081e030309030405040507093204 74
    0x10b02ca83c3c502d280c0101c01841d054400705d0007900c0c0103060004c01c01500003c40c45400b840c02800c01001c085941e041c4810010498000201958100008d004c200100c106208240208032a110491286c0e60012903e8544c2e4100001c0410a18a410110041446039000402424841c0625800f00c01030328000c40403145845980b0a01440b0700a5000f101c0c2d0301c0c5030a0f0f01c01c0c42c010380460350006094031004207000015800e044141c2c5c041e550b0340754981416005004144e00804030740740020345403e266000071001d010f0082c2c0e403014031654003a440c035194002c2140c20b01c0c282d004244501c240380e07100d05100c042c0d40502e8046001909085500310b4450180e400d4800c061b400030094031443c0e540c0800b0810080398899036903021510b400810010500c10700a00740a8041d800c003800240c40d903c250903010741d0452207090b119078020020440c07119070110945040c6d410884000c18036803a9581e04940002090700145038000c102d5100380e00203c00742d00c86031129a1203000301c01100840744204002c8a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 281017751 1250 281016501 281016523
    0x3030e0d0801050f0d0f0b06090a0c051801020705061306410f180906030a0308040f0f02041415060c15040f0b01030803011806051810030b130c08 64
    0x107a501d03030042c030251521910707902100d9030280280d2441c061503115422410382c51281514040c21003803e001041c141070b0303161580000d10407014004241c0310761000701035200e41c112401008800d030381141c0a5a20030300009006240c0284029101c5518038030040f040c01051181c040415804200b400030445401c1d003a1000044050b80740400c140c0030f2010f10200c1c50001c41c1550400e004011020102c401c201c0a001032410301c400b1100f0070000d5006002034608058007203807007903002d0018900040e40c0041c80a40c41030703010303c648011081c4c5182c9a202c244200c200250300604000c01000c0126005e1120352080220505002c0c80303140c460700f848140d01ca0308c854095141c00c2401c10880e5903100d0420300da00948503802c40c0c2d0148041d034a424490003000c1e0011901ca400000040202c40f840302c101c44241050303c82c041080d00d01c1e000000d401851540340e81d24141800c1000111001c94a0904000a54106205038003c1c54111150542210074100849a50214070004140000e002550000321 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 281019001 1250 281017751 281017757
    0x100b01030c0509040c0e120f0f01051302060703020c0607060b0906100f051c0c1814063906010819050d200a05030a09090b01021e070e1303030e0d 64
    0x450f0f9480180400b40103152004801c1c402c162401844030344078032001410800c2d00e540581010301c00c005103541000c01280d050b00320390307042c2010b05c80d0401c130750f46c8000d030043d504940c11942c4640ca484e06030b0411058a200c02d500c07450201e5903070b0912900e80c001e00c0c40040c045904071820b958402c100001c201c1ca0740840c800041c10130610065070b50240000304000e6813243e88440d03444d40b036402c0000580c1d5101c90f18000041d040210f106024a01c0390440015008501c02c030705034641343c4030101b40c40780200b401c410f00f4444103000e12000760a02c451414220440c42c1b01d60140420f42010b91540d6034000e1060540c0d034401c030440752020700f101d054402103080d07002001d000308001c140c40803034030442c60401d48114a4403d001001440000700003000046100360051a1214880c007400360001c1c44030341c440384841d42030246169080e80d0100307002801e00707a80c1c4a00200001c1031101c492501550342c100348800c00c2403c00303000b002c0b010040c0b203440c036038400e642c20702820822811441d12144e084c0710303003004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 281020251 1250 281019001 281019007
    0x10050a0c0b1e0408071707030f120908070506160e0901090b0a0503100615090302010c0b041b090605030d02150705071518060b10050405060d06030c08100b01030c05 72
    0x711408000c42d084405210824540a0501034440314250140e60454080d20000703281d07010808919010381ca14040c2c80245400d100c01d40c0c8000c0c100d9034506245a0801402d996082d102001c03d5208044a580001c4925110503103407812503078410050f94401040101e448a020b1514491070750790784034100c090034401080c2d1034038000e10050540880001d47c00461010f0114450310100007007102851058408654a4600700261003694074030f8014200300f10f0034210900240c0d0b0013100c0380c0c0c00e40d6440140c0f10003031f54560401c8030010241031604503280c40c01d460002080d1100b500040142c620880035181401720422040e40c0e2101c092000c00c501030350401c00900803500400141c5842030245200948804c0c016840e50100d52000034041c1002c0d4000280006000c5d8078440c4000c1c6000981d1000145d080c00c031000360050060340720301803082000084030b1540a0341c44c0c21110080d94408a1b089079076840341021512191404030040c607041c601001c9001562180c00b400c1e05054117602c61521f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 281021501 1250 281020251 281020253
    0x5040902130b160b01050d0221010b100512010b090a0510050906040f030b070c03020601050d1a0c07150605060a0503071107060207060f08090622060504080910050a0c 73
    0x1020303401c00016004103184840703000811280c41c00c010b011840c44a18000303002e0805282022507210180c0140307005a91028030200140c445a40c1d01001100c0c40c984040041701e4135065902500700c01e007015401c00c0e094642e400e04142c0041c0a407401d080600c5a10b840d41ea00c400054481d4040d400030039174822000c1c542000301d400c221807000d0180e0b421f858131900d040740e03100205803180e004c1d610051702305400078800c0040c460009405500000140781848034801d064070001d69a04040c002c6910542d101c0c03d030102001800e00340102c2003a002d031040c8040b8603003142007460a41280c8401c1e41c0c4906140c1d000c51640348540300d1401174442c01071401c2e00f40354120070120742c3c40c1c000a061400340608040c10560300301c010010030008000941c0282491410034030010f203000a083c45503805d00c11003009100351187c0220b06140c5c0000700042070300032a0901ca1b10015102c00b03298010b00314519002c00d000520504100500780310106441c1c00c00c8040c42080111071501c240d596141c001200e540c5850 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 281022751 1250 281021501 281021519
    0x90b030703021005120103240e0616020307060510050301050c0418021b0109050706030e0c0a0b090414250e0d0f050f0312180a080307030f181b0509070504 68
    0x2030716842c0b01d103001d03030820390b071694040c51004083c5c00946400c8100200c00f48a144040301c401c42010300c2c23100510119096001841d62480082c200034a541c055011025007d0b1003002030324840790308500d00b400780341004101c1a418001070b02599002c0d50030040019403c41c0b040c02240e0854030b88010452a03481d4003900c0500079000a2900541074070240d542102c204824060441c01c94024009001c90707520308034024044501483d0034006603001031843c0343e0142e6500c040c1c0c5003160220703c2c61a0b902c86608001400604031840704004d540383c0502441520081b248080350101c0029101e200700345980d40c0c0583e0701c8101800c0c00d07940a08041c071b0b01e000050b6003007444032080348104100c820314138100b0b00843c11908096030b14a40c401001d03080200200b41070100c3c3c54648200c0025080083e030030703180c0c06800d10004050800303058842000a50140d06644031490b481c8607031181c6401c106152034800c5e2038040840c0601d01126018002240c43d01e004100d15000f20320b03035141c2d00c1c5403601c1c0c84e44030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 281024001 1250 281022751 281022769
    0x6030705180f040905100b04060f0303080603120403050a05060108030f0f0a030f0203010605130f080604120c05120c060a0608030d090602070507060e090903090d15181506090b03070302 81
    0x1504074122090718021a00c0d00c4c0110481640305102500498100d00c1d9080c0071100340030121845030781441c000704050b0003051041d5066a030140307801c0c88150384110110303240442c040455901d100300024000144030011940d00c1103184141c0c00d0b510300740da880c24096030704e0051158000341c01704c0421041306007100d000c0040043d0300340c6003004580d541009490700104e070400d900c920041140040c141c00d00100020090f03010f81541c444001015080c400260380d035440c0200024402a81d81e0a14409540079030392200c0e510340c0c4042214034907901c002441043d07420109000c006442206c01103072528032302d0b000d000705403a10500210f00704651420010b0107064108403d4070141d40c01c001c54004030308140701032f101501d803d45412408401020034415544001441c80306103030418058501a0780d200e900188190740c020038068071044071000500000c1411501d000350017501c00c40810100001d00440c00d0ac0c42010340800c01605a640030304105880c1034444150b0306810908040c00149412520 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 281025251 1250 281024001 281024047
    0x10f020303100905060d0606090209030106240305040f1509020906010503091c0c0c0902040311030f030906091225080f0a0602030c120a020c060640090b060a0506030705 74
    0x142c003594100340d00c959042314078903003103460599000146040ea0742001d000d43e1000f0020800001c18000b2004a2400c0200c9030003103803401c05440740042800d100d00101c169601d103400081512121501e803000400a000514040740114540d40024100c1e40c081c00646c3d1041000802419421040001e031074000c0c586004900188800c503603580000c80c101a4250024010303403240140d450741103040a08c0e4141f0f00c0b10038644031358842c2c2074141080b800401503c901003c1a180c964440604000040781e008110364010b1252050a20301281c6599083c0c3c0c0300d544120903a00000065180c0b03084684401e0b03a40005511a4040e10800000440c03aa0046a01000007200745041005032001006159429540700d000c80b40c000c030706031884142c280542508113400311155168805201d00190301040300d51f480d002e401c17408400940e1544c600001c01d0070342c201800d0040082c6001881d00148804094903581c0c000c0035400800b00d05c9040c15400c5900404544d00c0340d80c00e004c1213075800d4031a00c042e454 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 281026501 1250 281025251 281025259
    0x50109150e07080612011a0f0303040f121104020c06060f190b070c0f180509010203011202010302130503011104030c12110630091006030312180f11010f02030310090506 74
    0x10001c10209001e2142e803583e408850301c103004241c071f03001c100a84c08500d032006034400d80040004001d40c5020088035011695008104421103046040070400c05540045003a0001c0c000030304405148070119280d40709400071240e20010525200910800c400410620801c0d44c07401481400002c903050041c0200620178020003da041d2940c0c04007643d10700a61060070303501c00d440c0740050040d605004046e0300c5007404c8000c508540c50301c4809460514110300c0a41416400600031000c449914010700c0503000243c024450200d02c071903600c249520a01c0103590000b6241000b080d43c0407010018031405421030b11020310702002d00c082040b15407040518030f8808070601c080200e010550402c034602017101002220035454184130755820100b02c17182040e649440c240040c00066080089981c80801d50340c40028100b070861710900f080351114501030108180d8400d0f9008000300744240c040048402e9903a140c41048030728040c1da8030700068500800d4a684650107000900341c59010544c0680020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 281027751 1250 281026501 281026519
    0xb07120e03131505030f07050c100606020d12020910052b0b0a060c02090106030e0304080105040503191d0d0602070807060e060c04060207150509030709050109150e070806 75
    0x82010780341d50302250200b828540d0041c02002090700010711020b020031581081d5180d494406002111084003e0452040c442c0110f01340da14550100003080038450340b41d0b0104802502c40b0303406176468803029244000640c01d40c11091006d0841c4c0241c07200c0d008003411010905000d1801034605411040c40020040741d003609080c3e40d00d05005c420315034030340c0018000a00700d00304030501c58147d01e6500540c00f03200d100b4011600584440e10f000d070444415180c0054801c4083d00401e00b984501d5100c2c80780c542c20213040c003050010100c0204004c0810302410080c428030302a0981c0d424074041824540003219240e0040141084002c82d6003992080704014a0b110240c0c0c1e50709550303041540d0075655940e6a400c1648541c07810040c40340c0040481c1e14890501e883c1c040001e40d500c0c0c140c0a06246440048401002540204203643e917000006041c0e85c9042d07100c480960003001e00744144520281010560300500c280c0802010960b65504403414041e83c1d000740940d24400c014003c550040103903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 281029001 1250 281027751 281027771
    0xa050a11070b01060311070209180316030905040e0c03060a0c020a1a040c080105150f0f1c060507050a0518030c15040807150e091f1815030b0712 64
    0x400600319103100e520030042d40d50604400030201c800c84600203c0c120800c00c01c00c3c0143c1d61760140c1d558050f0b038580303c50504c8615503220500710301442c0d402400d00000030615004040d00b0603807120540b9019034080003a90b0055111070b87d54060020041e806401800120b040c243d21600098201031850044400c68110340d41c8102c0015400b038ad902c0b8128510b00c081c0410494641034103001031880e40e00038005410140d403894072803004031803840d110785004049044c05480b059441240e400c8020000704400c51031289054040c1d6030340400f181c02602d03180000380000d003d81c3c16644035032016640c040c01c10425209079140b48a0b98a4016030500c88c220f4541c00e5039aa0751046007208103040c80e0070751600c1c07415030481d190000d50b410520074403101d0132078040110340c001d41a404452007154a494a03449407005038070f42c0020f00c1c1450820802c60b40001c50284007000c0c0388200c4980042080001001203403a440e101221400020301d0f51041c00c002c5821240f15021040c0b1800761050002002013039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 281030251 1250 281029001 281029031
    0x1407030203040e070917060603060c0d0e030d0903020f010c0203040312360801020f03060d03050403061113080a0f061109040204091401050d05032706030a0e07061103030a050a 77
    0x4200c03442c07000170f000740c20140944205288110000401440180940d040640000380c0701d40f4020308e000903c0402040360b82c8042a1750b00003e031044502e10650359100d590034035103006400115819130240c4a06045100007200521440c01903003100c0d409107091a0559031003c03480000f400f248000c1054101c1c0148031006403078202e03800350104095a02c800402070310002d0035814190300080284c0d01c180a14640c8036210b00840e40e000f041122264402c07101d40c1741c151054003450300f014020b0f41c1b41c4604991644100780c010304180421990b08464244e4070602c40c0d669451084005001700e17290450103000807182d410140c038817089454110308103649580803074104c0c0c22030792014600e0b5485025005030407090940c06400b6050a481d550b50802c0c0f140c030341641d40e103c0ea009652000f1100a16480180ea10f00c4000c0e00c5800000c04d0b29650341040d0210302d01600c402c03132003651640910100001c0041c001c05812108a60040103541940d89402d5038070028400148041c081a858200c1180c02c084 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 281031501 1250 281030251 281030279
    0x1912140708060307140d02040213030503160b0f0702100903022e0e07050109171006140405010803210c07050a0b010e13170310030503030910050a020307140703020304 73
    0xc9a45038005450030104144c0381150980c09003c0503007500c00e030307407100340c89a0104082c0b5540544015070fa07903514500c44042c01c9050ba101500318003000c40d40060007a00014081c030a0340c020360f11100162070300e011148100c001943c9480250340440040d000a21280d0400b8a07040d011f0b00590304500c0d1005c00c1c50b1805882d501015100c4004a80b07640a040c5452081441d4449440c0003400d5060620b80040d1100c85280030b1418401291060104141d4040010007070000c03003000d043c4a40f554440c0e96985c05d100c07000c142407103541004000320b21b9040000a031151500b0440e203102072171400601940b40c10402030981030080508102c00c001081e400c1280c50750303003449090142002d607d403102c55281c10b48094481524401985081400705e40820003030590100080b0000e0340d6a142d034004400884a154001051800f01000300401c0300d00204680c0a01071000000340807503614403418001324032003241d030813001c03520401c0004190642c400c058030010b03210340122480c240d124031056204403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 281032751 1250 281031501 281031511
    0x10b0a1e0e0f070c11060f04031a04150e0304090c02070330050306010e03071e060309021f1103030103120e1f0e0102070f030f1106191214 61
    0x250040414030100c00351030019100408030781e0701081450624840807000d80d903000d4510b00c2004000c0c1400c0b001e0113603102d070820415000a010a58540e0600c6495541da04a84002d0b42c1e03914640403040511400d01040c288a82d03408011400d00c40b8074410200020710b54012242c0c050f12040c840400c050300326204039460b4070b00503001828454518501021542c0d003500d5081144070300c2c5900302c4444420a080f466841c0c0e15414080c0d100c1d516440100c0c0c01d1040341d45050340c180310b08800054400380c00050000e244c00d06010f260740701f584851090302a85c0c40075400a4006c80044000642c4401d507590500118000d450034804072107180c00303010320b542c000303800580344122012225654140c00142078000c9020a45250b41e441382030840d00c04c00411013071005810b0143e00740d000b0146a1080c464540600400383c100000181c503800d15103850783c0c04503070844401460341a4041c2c0303480c1c22819602100d10301e9003400c800340e0865508840070300088440700e401c0b40d10744502a00c41d01494035014030407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 281034001 1250 281032751 281032769
    0x103060207020916020606010c060908210709030809060703030b0d0501050703181e02010e040f0203180a0b010618030b15032a010c051608060a0b0901050d0212010b0a 73
    0x90219401000f11010015080903c0000c0c00034900200075004100c00c1d034425000d003801c0380b05242e05e04042001e45001900204191b0380040d00c050174105840ba558084c20720300c18081c4640d51514015500341049000150000c941441940c0042c60114001d0010a00c42d15000c9821a08040480d01c60300f80d04804840b1a5140d008104001d41d042c801e5500b440c0088940020413003041d111003000e4554207508500c41c4415003070000c2035901545a100b0342420140c0f04124900c000740c0000020340040c3d4050108510212440002c00b500061014030075030041244c0da0319034a04a0140d0311051148407000d40c1103a82800000440e800ba16002d11402043d91f04001c10f2151a04040c1480b00e0101d81082d800b266071014004403150814410700d1140a003011440c8006a042842c6005607a0401c800310f400c2e42a0003040c4d91001140b0140900c81e001c000707000c8201c800040088600c4240202c5400007654a0302d14050b25081000c04a2440110000135158040f130000c03034000d01d0103801030510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 281035251 1250 281034001 281034007
    0x403020d031104050f06070201020a12020d030e03040501050301260a06020306040c0c171606090c0e0702063d080d120b0307050402090a120318060806030607030c030603050601030602 80
    0x22881d014001c0d080401c00c40310086207014180030014600d030818106850040030080341b0f250443e4020805500099000b074a108030040115800a640d0400300d004140002e007840c900804006001040c1ca080d00c2d0140c44003415030303080031161003601001c42c240d06664160f94150f041848414402c90301910b0180c074000d41e6131704d0306605100580e50484c01d10010407408041c2c00c00400c00440800b500e44c44610030740303907444a914043c241c03440308100000d04820700d4171401108014020721070108071104002004102d985000059881ea501142d500200c02500100700c0354611010720000021500b04000c00200a29071103254103511168000d0031266106000071241e054110221076a90742c0d896000f17008140f04800480e071103950034802c0c0e6008580101305030910781e4807054444080e01e64801c82c0300c0b040038a400e005000d5013607480c1903547c10b04141008100750780300d139104074801d060180c02440141c1b6100401c07070040c02400010700800d0359940d8040000364003030000c18000c502803d005030b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 281036501 1250 281035251 281035273
    0x302030402150408060403080609060102120a030207060e01020d0506010c050304030308060a03050f2109030705040b0616110108060103020405010c030c1704080a0c0518010314010902040204411215040302 89
    0x448c0281940d031150350314074200001a03a0000311303c1c581b6500095501c0d01c030484010150040d00031414010103a5007400d407030307400030441580944082c800c900b10a0000380c9641006540180a07044080c250f60401c04c81440481d00681543d60441006480c10250700c0d13070703510f41500703100c003496074500140c001c5841c0701c50390700001285800c1c1c2590841411f00c0d1441d0f56001036612001441030030702940c1c0702d0280c0b91140d611442501da23081a00c0540b40522046441c0c40105131a10803080c80c089200c41001c515554460310955054850685071304000c01550340f02a60411407001c4101c81d070b03c80659814004080100140004060000007080c4d003c0c0180fa01a003100859000b01e8003440e0984110030a1031507481d01d02c4c1c1180d40003c4140c642c0f0450303c0049000d001c5414011b50018000030300051604c040107403440300c0f124941d11400340e41c4070f00304010300c0c004a206d00000039900b06500854240c58180511299150100e00302c504007000380b1a480c1281008840075805038210701410a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 281037751 1250 281036501 281036507
    0x10c0f05010e0d1e030b0a03140a0b01060804020a0905190629120105010c0f02030601060f030b040507022d060421050301050604180902030624031b010302030402150408060403 77
    0x3e420025034105103501880d041181da09900c0d943c0c24140400d91a10702a402d9a1914901d002c05143c01001c94a58001d1210b81c542d0345580d850001c031004d4501c000005070681c819405c070b074000d41c4d004200b40c503064541260480600409072480382c40f5031480125100c90030183c4a01002001000c14820b400d0141d65548000501904201c5140110810641e6010608011558103488003404c100c8404000343c01d20300001405404004d402d8801d41c0004284c01781c0082c041703001c8042540d014002070200e0014001a198159103078000341e80907801d14012020b0103c20400c484503144480c1201031440041340d80f606005880545886040098095928031500d290060728000d03800c060703285514150201d4110312540c0301d0300c50725451a038060355103014503800081d20150000c0c229038140c181052800681610001d100790041014180b014803400c001c5003c11041215030346812203d01e080005501039803008100301c0e4001e001c00ca101d100c0790244030190001e071414000078000ea1802d45406 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 281039001 1250 281037751 281037763
    0x90115030b01150203160b18030403031205090c03100c110319110303041e1416060905030d0912020a0f0801050403120513030c080f070f0213020f040b09010c0f05010e 73
    0xd2070841d00104442108400744007044651031f07038000c80c0c1c22401c1da5007503075000100102690268541c0030018000041c1540310780074400600003110100419118003040c0c60343d030040702c40c2c0d50343c160300308407050071340410594840d40c401c05023030510f0200785102442007130a5074070402c0d03400350b40102d55000810041d8002e0845210060718001186141442e480317619401080000d1511030302d040c0711110341004154000c2d4603940064000320381c5280502c010100c0c600695001c0ca03000500c20707100002c0e080c9000607107000c6e0a46c06403210088039007400010010100048803d0382c004444000010392400300c4549440104078510002403541031503e001808148492140720a440c104001e103c0c0604420b940c1510240c1e141c141400e040c1c0322494028001d0003900d03141c1075a04000f04061040c003000392a4040c001d8801c6400c00440036071102840100d000b080b05150101009000910a141c030450081c03201c20814103000051150700d56919540500300b1500320364503511a16441807000d020010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 281040251 1250 281039001 281039039
    0xf070603061d060114121602060c09150f131d01050f1e030d02030a030e120306060a020f030a120c021f0209010c0206030f09071203120203090115030b01 67
    0x601c221498407800c4411182034015107042e901d460400700340d6070303030290480c1e1500913540304030b06850340c070400b100340c964060450702c03880720802d0016120105880806c04a02c1100503140c16424101c010052281020203000a021001d10410040710b070140e91901074404171414a0701021380c075007026981401218031440d03a40c4026000c500600c055525070b0480041c51000f42d0b172606200b400354600442441c2e114050a42500948006030314003607000c40103007202c00c0366481c2806138000c2d5801c01569441803840d0740300d80300c0301070000c1912442d00c0d0000b0000c2d00304501c1140d11003100c40b10120f05680c003880c03101011546141c040100074640d401092150225400600041e00400d2103011500b8004460403039a280d001501c60380680c02466200e02c195000340000361640f41c43c5018000c01d81d000e03100c11a80b441200400908038500c240c000f203220f176155854001460308040800045c2d0005084401e16540342c04198400708014010800111300401040c0c04951407d240351000400d0b11403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 281041501 1250 281040251 281040257
    0x607020d09030b011a16060c0e0a05030601030b0c07151506050903060403031107051005070305010f08071e080303190606021501030b07030617010209010f2d030b0d050f0706 76
    0x102000402d20b83e445450458035005441d998444009503644603a200340107850b41c0e80d014960740380050101e0799002c0c541012854640041c200b4a40041001420039480340d81d80c99807140005000281041c481c6980121001c0c54090420038281d458032179030541c03540b1024000c1d40e1400300640b01080d0440700002400542030203032800079013001181d00d6520017000541495201c070542030480c41024202c078090707508101541c801e500c00c0300080e00130345002d82d0003100003410800081030841d0320b035808104456144000f040061302d8001c1d0218642c15054948856800000c000140820184025440f890701d82d0294503903c104050042c040718400e0308424210342c80301044107180aa880070843c192038101506518540d140c100460145c2100d0308404000744141d1991004204150044c0482d401c2c00d88541510000303c0104444081140350088400f00c18000d24108c00a0703616801c3c00d0050301c6143c00701e120400c1c500408c04c500c0081100b120745078410382e1050380110041c0040e4000d00074501d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 281042751 1250 281041501 281041517
    0xc0307090905191401090b01030204050a0507050403030f0e22060e060a121e0b09010b030c06030a050604092901080d020c15090a09090b07020a12110a0c080607020d 72
    0x14a40070f685115020f02c512001c01c4540101e010700c00111416000f10300e0010090165410304c0c03602006499082c40101d016504110201d42c804459010b418482c03c15a076402c0c1c1444d02d180c400304d4415800610080620204080d1080c40c1c1d1510894000c20102000d0380c00550000d0071610012150326500010012944206004c25540c0303982d0b03c001203c1c91108020741026490034030131030060300700d1a08000300f080541030004200da0800924443c07030541000f04008a070302010b02d521001aa911030768045010000502c03048002e80c03040d5000130b00508001400c205554580c441036405070b01c8249815446ca400050345421411214003426400c0041c006014800c00082e50310f4010449943c86600d11188600142c07210209441c61040011b082000c0d0039910340d807000c01840d02e403c00b03951154030440000c0903280005142c1d5030040c2e018090164600c0c5103a0308480e64500301491031140d00511000c80d01048031120700310003401500c4054400360900d05406441d1540d640030800c244840340e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 281044001 1250 281042751 281042753
    0x9150d0c2a02010905011809020a020c01021203040302060c0d0b0a0905160903020a05012303070309140105071710031506140d0c031524090f0b061803011d0c03070909 73
    0x26401c4d000c4038420309208000c1810540120f40c10580b61b0800c4201741e10100c0c8400d882076001aa0003c0341c2020b80994a582e51006407101441c0b0040724064003603070111002c1082035204000528051108140c000f0740d4090003000601010340c6070f44510001070f201d50030f1146c0000f02e040043d031000c4107030612140103131031503001c82e20035501b9214050502085480200746213661180e000d9014003c00e05640ea40c0c03904000240c0100001c0b801079403903110b05d080c2d440102c0b505105ea40d014110b80e8503035821808401409400c150402802d407041c040400c074002000070982c1c403500050310403540780800c40350f01741020913034a44010600b15214030001003816003c20880c00d00c2e407064035004040c0c40d00c05040014808003408401404c0031410001950b0001d03003600d408420f5003a950400c5040c400f04451204c01405e0b40d080c82005a4846401c22a058402c1d440f41c0c82c0c480008000360000c40c1600c8640703c032801c04000d000c9007507216001145100400c2c502071043e4009003030180010445000300e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 281045251 1250 281044001 281044007
    0x19060206040807020303070b0408040f0f06051902010f02070605011404200a090b071a0c0910080a060504061d090a11010c11060309010c030510030809150d0c2a0201 72
    0x1001e0406800000300246520a546046c81129032075500480102135508281ca03098040f0b80c000c1c0701e900603a86e10140041a0000108000c0085440c140d89050402d02c01082011100381d011282d40700355941d03001040016011400501140c600403107000403c0c0d850900041018104002c1c418811440d2035074440390304025041c036503151041072413280e848641d04601520b2a44450700110360550303010a0b0442007182380c20000030021803642481742c86803101e00001155000706d0070403541c00f091085c00340c003040c0d10034000564010f8580001040c01d07541c407000f141c104c41c0c55801584440311103140c001c0c9401e290002031500700e150b110040900700f5445c2c0b5a4440f0048444207241084440d2080400748181000c20302c07000e8200801c420303130ba82400c00ea0a0300070a5051202c00110b801c140c0041d440750303030704400350080303d070450b96080c0f40c80a4241003102403141500004c4000030203205c05002c04a00303104008410700b0030386503c003034014081d503982c5400046018a81d0200c0c3d280c140c190060364 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 281046501 1250 281045251 281045263
    0x3051002030903071e0b0f0628060c030215070e010908190605041110030f14160f020a08040b070c1421030714010c0810140f0a03061802190602 63
    0x9000b03480f0610b40c0e146040e070b651105d50f038040058402251417080c0200c5102142441e405100201c490020021030a074540d0300c1c06159280441140c00c58104c00c00c05c250040100d030b10324500c00e1040d03070fa041d6100c0c01d2032884000190f45900026280f080551040d5030000b80807805080d40b00010f06072004014201c1450419040004100c241c60381c001c45c0400104240d811400c6100a01858406035113105c014005c200d100c04240410b41410508460480480c2d0754a00404000c66070b205802e581c00320076240311119103040c0045125100c90300b80401d0014000c1e0000c0c120130784506070b032a02103042c0b00560610503000700c00044c103200c0c9020910790340c22202646d042c00740c0d441c241c0c0c50850380384010706500400340040d2210704088400c41001078190b00800001c0c01c9a181c500b850744a5110f004a540c0050003201500301c0103c41600340d900d004000224540e400500107000e0356100e40e52a01507034004d034516a1045601c050020840c603001c9407546000c004400c100b25580d20340718000307513102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 281047751 1250 281046501 281046503
    0x1008030306151219060f06050f0a11060103080c0c06090d0201030c091a091813031b080a05030a0501091a0d0215070503220e1503250305100203090307 66
    0x24410420011801c9110041d6041d801c031804002080d131401d40200064150088200b80c040c9252680204915107201681e509540c21a1f03126420541c030281c22030860f41c45072055000b44120508505080c00d002c020060181d84100b41c031a0300c0c1c120070506245032600b0400c2540c0b282030207002c02c03502500c54900340d405980c0c091a0114401c0000c0406580c07408098002d488241d0400121a20300d1080d0f03401000d004406880c0324444088034500440c9060058a61054082400c128040031034490070718401109034000b05c880f10480951385107005980300c0c05103d40401c0c00401000301c0087d05100e5071340101204c100c1407020624000c154074058a2031540d69205035034981303c034001d5444000320191289a02c02c085c42e03480c03e1a04102d40c5d2074212000c01c50048900c40c4010303000001c000700401c12921244016200380e207030356025130f010090311070b43c0355014403841981e8a0980411604c00111130304500e25804803a065007801420040074207182840c10323004205100f0300d000008102d803011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 281049001 1250 281047751 281047759
    0x3010c0c02210f010c080603060402010507080328050103021908030a140d02040b03011e03150b1804060501050a0906030b0601080c0d0501060207050a0e0402012007170d0201051008030306 82
    0x1c40a03620240d5002031107070300807082901c1030a07516485800f05600202006480c0c1e1034885695842d4000c1650340c040c1110024005102030001200252500000e1608010384245a064192400500384450100000802c00b00c0303403600010015824403814031055008200920392400c0e0801000320740d079205100655080040148060184103c4207003581e20029100406554440c2e5031518500035400038000e091400f6070300d0b01c1c120820b0368000000011a030303008003484c0e81200c2c8031120742d0041200126040e0440e000030100c40380302c1c0885125910641c402c00c40081c80c0e504000600241150f91342000a03a40d00c2d040040c070220792400d021541c440d209203400400c95845184e14862130040e50700103203005081c0000881c910782c0200703401c0c0c00e1307e400303a41903000d80340d5890101c13403541000c0e90f0280c003046460001050a00d800550065a4034480c021103081d95500e4800c034844c410350701c0a50420ba00902c41607145190f081c01290b07001048140c440200e01d0614001c55140d1001070016403007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 281050251 1250 281049001 281049019
    0x1140403110f160f06050c120307050403020d0b07021002181216090204080c221a030a050a02181611150a0207021203130302010305130804080d03050603010c0c02 71
    0x490392042003400654040001a50f0605140100711203c81010303003e010039050041e0404038200d8490000d60b03001000400040510010311a030400b45580094040020450104408030158848503400b10001d031003180b1541042c908103200030304048004044440c0e0078010000310820b65083c410340c520581080711071041c1d6045801c48a80381082800c1c80d1501400515400101c503040e070b9001d00115a00201917a143d205400f00704030b800d04807100c80c0050302000c20b42c00024aa09a0710802180040e5400e0444072403014000034030384000050105c1d20396000c00d08200841c144507002d1003404000c09071030041828415520400040303810070f44800c10540f6821076101c007030200112141da84c05100c1ca0f2200707007041c1100c0c0780a9031213070200380d0085000c8101c468241c3d100000f01d5a00c100d50380440c00d4618210f0b801140030b400b01410000c5419100151140440d0b01c0d0360003007008007500e0303006012a110100000e0161a4024000381c4039925040e00d480c603894009a10040f01a4101c88001c1e17 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 281051501 1250 281050251 281050277
    0x1401060e12010615050307020115051318050f07030519051f020d0203040c030b090f060c070201030b0307090b0108010801060608040f0201023409060b220801090602030f010801140403 80
    0x2c0108010b81c082d4810000400d421416250004005d60007485c40741e009000e800079251401c882c2282c140314098100c4082c5522401810559000034080503240c0b854900302046501d03142d2606c1c0848001409940000104004210381002210000301c030b2000001c11000441d1034454907400c0b0901850300c0503000c003010324681050341e411100c0b596440d803411504c1c0e06040c24007001ca602c86000441d003000d00b010104690490010f0050155903582d4000d002e40c0e0b440c0c0c1581e4085810142e000c03414103444007510f150039034051101201502201c0320009507810b290000404460ac1070707100c52860b914090f01441010740c440200c942c40f541000d45000c49a0052004034a00361b0000c03060b1036428001d4414107000300074810304281d590302540c41c0e0744a81d5103603142e880072036000b4070a43d0300860003000340c0d0f9000b0700300d40600c9220300051420a03d8881d9200c1040c0d007510945481110b940380d00004002caa940710364495405020098000c01c076065403203d1494020f0400381c0094240000105010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 281052751 1250 281051501 281051503
    0x8070510080c160f02040c0219021009080105090c030c180406090c030212010f0c090e01031403070b0f19050c090909030412050609011a03030f0d15080d02011401060e12 74
    0x2030b00007403424143e06820111401c028002e0108000124443d0b030801d01005100c0e0b10010740008100f40d043ca160111020396402c1102032100a0800c0d01401818000021211030038440d0038800c0c805a40a030840484003001c050801022009007803040b03600a0340303155a02e8505101a501907800100083c00d00302c24140030000b0100303940000c0d40640c168243e90400b0702c06401c11100380b01030040034440815580c2050f6080079503402080e12023002c0c0070040002c41c040b10310710200300400d0010350385400c48903150380b506040100c4409075100400001d0040c03004d01401c44c0d8003600c0c0c051200f040141030038100c4c15040c0c881e10026501c81ca5841010a44028060040382c005002154602400400781c0c03415545529085540010039481e12503040b0b00661496415201d400005000d03500d04841602c40030800d0300aa102d0001e10780c2d482030940301c00030341544014040d00d040402001e030740c0c0300ca290003801d5074804540c1c2482541b00300c00411a064005640e1031210504450414a0031a030100103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 281054001 1250 281052751 281052757
    0x606030c12100909150606110c090417040320190b07030207080730020a030308070908070303050910020705010e0409050f0d17090a020906040f180303060f08070510080c 74
    0x1000300c582c134201a410801400401400300e011392640300780f10060760340f401520702e420004003034409500b11010200d601d140900b1074070b42c05403040049408080180140c0111604039400440b44051010809002089115401c3c5400d070b404540b0029403c5c408800701001100311704c0b40780500240860071204050007440604064907011040782c80c0e2035910b00c180c80188003c0c00504010079824001c0764044140c040d03169003e00c2d0081c11000b8000d146640c112102440100f1140401c040414007140b0300d0414869807000b10700070760341c15884d40e015500300101d0590300300001055511901c010001130741c1101300200c1c5130070101c80c0040c3c441807078142079040c20081e040b902074900503480704c5038500340c00a0f10443c1010824401c011181c3e0351541880e03665840c290003a501001e20000201b0518150300005a202410340c07010640f1069812040f16080001e242103004c03030344a4405000400000550300010b2403180003d000182c80d080104403180c26030b407080020801c0c1a00011040f4a01c5011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 281055251 1250 281054001 281054009
    0x1406191a1e0409030306050a06030603020f0105031e0c0306040c050901090b0d020c030d0c090e01030c260105070e040506150d05180a050307020118140f04110c150606030c1210 77
    0x10512820f443c0c0d280080082001c1d009452082079582c03804181d0911178429502644e0b4040c01c040b0407074410381d0064949810080414034020f11500c020050740500b550101c1c0036a418144860f240d0a1440400064890450b5607400300001841030b201b0503a400100301c0c04641c0c04210142d41c0359860409840a8810030788460711900c000220350b0000015a0302c54040c0c141c550b90ba8400190b1111032442c5d400c1420710000d800141c4801051260818a2021544503080380c50035081200f91160038a003540c208036038020109020120440d05070405006290384000d00701c90090000c0d080c1245035032107000f200320310207256903507400094440e11541380c100c043c2d422040480342c6412051801580d268820202240095052101410b50f48048102c0070240c88450300c0c0c0f8124030388804d0500c08000001a0119801500ca2203401100a0313030800900c054501c0402401c8818a5881d51240340000940310a001c3c407010000c106042e903c40050b80d81180c030080d401030803a100e03104139030b440d021107400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 281056501 1250 281055251 281055259
    0x1908130b09101d100c0f030b01021603050c0108010e09070b13080106081e070b091903080307090317310b0a080414070b190c1406191a1e 60
    0x24030f4000003440150120580107007482200c904108080c28401540d07568494003002c1408a01a41e4500e0300076000100715076011300c1251094920020040016003040e4401d40319078210740b094552550b07210400b54094041c1904584490030064039003595020b480c840c95908082c0811441c003403800202d0700d0001803a8090080c40000d456207143c80d00c2e00800315000c010b042c01035444400c600780200340c00084900c03250807642401070704414049240140d0413034010b00200d80750003100141d0044042d5004a00c0c5035141c10800b42140ba000e8610302601c108030802139018898003600c911503079101008410fa07480b104902c100281001c0289103402d8103c40850100441e081d12510707030184017140b1460044840640c000b0020103210786508107070007078140075802040000e00100c0003410341c2da511003a80c60542d0560388203481c1c94200070b01a51154105800400c28040b41c019090407080924101400030005150026502d2440359215060300707010307100040d003007250781e0046a0000c10b204001743c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 281057751 1250 281056501 281056511
    0x16080f0c010e161409060301140c1305040204030807081c0e0a0c090c0f031112090109020108060114070f061803090302040501080a08120a0608030703051908130b0910 73
    0x11105000c0c0101e807550141510643d003090340300100c000b01280403110800c40403100b104000d4248400c44800902e400d0301592203400d46a00781c80c04600342e5100f441054007007901d50010350300c0300d1030602140d407150b4030990052000744040340702d8908561506030302c5a20f6035074402c0349559883d2a03640510060180d2498415002d0003e4008145d07881c00c4c5201e000e09200d5240c0340e00485003100c010300598000200c20b05500b0350142d000e80c0c0620001402e4098050800b4070407820030011507001c84181c0b015946401c095011943c008613595007102c02401c11046c1904242e103d003c1034060200301a00d008501c002c807206009a561003901140108184582c1c0070326503081c09460902e4500c004c90040d4a08800080c200e400405c8082106174085c1c10a440c01e41c00f50000a202400078202010041e80c0310f80028450404000400032548203454064440c1e210a0070768144004040c1c81b002408036000c10440d65441c1020f540d11041ea000c80640314580780c0040e4903103070000708804901d2092400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 281059001 1250 281057751 281057767
    0xa0f0803031b03090307020f060c071706070228030e0406030f0507061412040c050603240307050109052403090a110402070b071d09010306020d0e1216080f 68
    0x100c001c0d03100b4004010744055000c040344a41100b48401c40e0340070000d80041c02140d00601d4454540388000c17100804403400d01d8800381da550300b050002e40c04126007444071140003038581024484a41d00c802c090000e000c0500351071040f5500c01207807407540e4003a4003160f000041058001c2d000707070145a8018000b0480192249407405003445c4815081d0f500388111100001c88500c511011510321716004801030501041c0d5540c0244518003038000c641000c0c0b0740c107010506031618005103218030795000c1100b140b072400c90300d003034410b0080068450003070b01300000a00141c0d82043e400c1007142c40c00d607903882003640c86c510f80004da00101c0e101d1008000b000010301c04901c1000039803103102d90141c810380072842d549100304000c9101c1c400004010031400b000184c00c5900845213502e0a1100c07a001140c014180c10000b911078009030070407076510340c0c00701d40342c05400c0c0c41c4e1041c00010001c003002003003101c10041c41d0607501c0c040c01030b0064900415000d9141040380c21001d031001458000812511103c034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 281060251 1250 281059001 281059003
    0xd020f0310080c0d1113090b0901091407050d020909031911240609100e0a020a03051302030a0803060d060212012d0303050a1707030c0f0c11040504020a0f08 69
    0x7038450030041e88100c0004a04514000380a11103455014040124008403a400e000210f0704264161321415038038059500400c03245130301c3c80d11500008000044005062520110b00c0008542d8400c9540c071004040c005a01c46010300e0640710340441d4840d17000d80e40d202010b03183d4801d5038003d40e20508070b6041d11483c04e4100d1545016003120400355862107489940744103150b0700303a190f5091a00899004074400341442d40c0400d80141183c07402444d81500c480da000d0440304181d65006901d90b00284200413207525100300b54010700700c03060b04070820410740c00003940c900d003c4001800c9600c00101140150342d031821030b01c103413a500c00700c290340710b030301c03078680c4020300740302482824442c0c5054869011040d252042100e11211289020302d08981151000c690540000c144141408003031020080c0401c005a005807141c059031364081003241d80f00c1801080259650600e07811702c060608240000751512980032100030060f14005201c0d07580380000703090650755501856610800c0d02c40400c0c5c03c03034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 281061501 1250 281060251 281060281
    0x1a04020901060216031115030c070b060f09041b081015050f030a110105070618030e04020c03040608040c1203020f070501020a0b0106030519020f04050102010e210d020f03 75
    0x8000ca03003030156a80d072400240d0b00d4041072410f03000703000540c22084c000aa001107803031011040261403031109010320790481580d5030041d51070549800e408152042045909000d00e64041420f03a61190a490700c10b02060091401605c001c0500041011484040366002da0440007403081030200d4105102e5149000001d1002c90981e504201d1101c102080c11300f0b02c0c1031b2001080c04041c0083c40900e403035071100310702e194202c1d8a150400c403041004d0070101e18580601d60086d42000003a06a254680c5805003003851540200c038001d0380107020b01c902c840c42c04401e982c2200c0d140e0510400c1603840e803401b00809001900007085000c0201c4a03c4245035000030000c44150021045030704480c1c64000684e80c540d00310000a020f00412401071240901c2030b041260032403030700000c0904144500e004042683c0000b502d0a09802c0086810031456a09015070420344c5000e02c041c21990b41070030302c01071440701c00800d000318910000490452000c1c060b411981d2a4584800c0399440e818840c0c5034020500d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 281062751 1250 281061501 281061503
    0x1909021201091406120f061008061b04090902030304080f070e0c0301030b070509040e0a0308060301060509090a120c051527070e0a09060203040f17040b0d0b040204031a04 75
    0x4038129001240034002d0b84501414203407000000f0000b60754140400152980c1d105a1003018000d882d54080610300400680d4040d1040b010460401802c0c6a140c0e480c00200500c44c1071408046d102903450180751808a40969840c1d10021412481c24000f01c1d00d94892030b80901441d1003022548500d450303002c15284240d078180c00704e0560030b40b251640201107000c2804003a100d25290701c04a0060360064001300202100540007040c0507100210031401d02040c2c1009502044800082014a180078410700c009020304441e002103904021048175500c1c0034090008108112800d00000303503d0044850210407070b070210840d45c4100d0b01c0c07901152003600948110122680303070310f1111010070722070301207415403d440070040c0040d5203441041029400050585224240c2c0c408610000c950075000841c441d074000d00c08444800894a808407580310564284000c6e03002c14401800f50000503c1207450007208540c0c003244e00511034001034001e20850348001d0103800e1100301e10195080c2070603000d100d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 281064001 1250 281062751 281062777
    0x316110f01080c0a12230a0b0303072006070f050d140708030a0b010e030a060e0d09060c082109010c080a0e0d08100f060206040c050307050109090b190902 68
    0x20091040c019900d0281c01d03203102800960a01144014030701c10a000044e1020b90400401c1d940780c0d010144d04044662880c0c000604e204e60704221000d8070600842a1180d400d03001585492419120f90309002c07582040c603074148800041c145851741e60002079981080d000240e0025820072490611365a200d91032110010400394a040310364008a8000e035910590060000e910395510b85803c0c5000304080412241405101c042c04107068404000550555100302000500c907035002074000d02c1e00c038075071490004200108006110155002159000450b4480065500e402040724403c22902000e460003031400c07008001c001c0c000c0b0054004480d600b1f242d8441442d20303140c06a02c101a40c9651020340015030080750b4980c0554411210b82d64803c0c09280802460f40d119101e564102e043e9501580050303114038140001d001001da0207500070082100200380e01403034580040c2883c480c5102d02340c3c0300c0d55640015005501c4840407006081002c0e21080c003015202c40c0341400a41181c01d0341804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 281065251 1250 281064001 281064019
    0x4060207091806050901110f04050909030a0c032d05071101030e0706110f15010f090615030e0c0306010915140625120804020112051512031611 63
    0xc15042d21450400720546048407030400c2054a0f03403009080003030269940c41d940d0300c0c01c032100001070304050160301c8020414a9581c0e842c040420021a0014103200401e8004100b60780c40d140d0001180c0088544c14144003901010490700d520300070351550049440d02e01c451065a04a0350b0100c0100f822902c9803141d10300c400b051304011004c0381c4807a607845202d548044c80034040305000340c440c0c9941c00000d40440b0206520852103d00b030141114441401750308038001444802e217020001009400300d10300401a052400000300210084800458240b60741c0354000365002409001845071644042c04443c040c1d40e440400c03000415011507200010900740a02140c041d0103a1000076400c80300900040c101042d0a844110a0f42c10171086040005114111800140f078180c2004101d101500c440c4c5403031405000140032503a001c1201305041d4034110400c4206000020b406480510958000001c421442d034180d10b14070901180084000e0240301d0350040002c0b1078030900900340b00792440d10b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 281066501 1250 281065251 281065259
    0x306060b0703090905091002070b010f08060903090d1703101404020c03070b0703230108060c0721090f0e091e1203040c09050403050703030b0f0105090405090c060f04060207 76
    0x440d4014007000500045070710508025102d00c0f80c01050700304149038261065821202032000403030344000d408440c02c40d0100010030484110103000381c024800400a0062850001c120355164130134041024868100309072100f00344241440d0312074110340d44256090f52418200d003183c01e4882188500b0050100c0550301c844c003800c0c94001c0d07811002c40b00c0c00440c10a000340e03407072645855004212808140d910222004013119100c00b51208454081700d41c6a1541000d10482c2404001091404c3d11001000345000040100408014900c00c1d040000d01c5081001c008940e07801050f400059035000801011465002203203c0030700a101d03010450f02028490700e00c2c2c0501c805c07640304010658000340303039203501c60302c4020045a00c1071040e1899085035460b1410300d000c444040e00c093f80040c0022038a0400c0580511514210510031101404032149160009101d40310720500a4002c1e41c841c0080f6010f86002c21107132000850041c40303651202a0840d03107010a40040c0b107148018031460304001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 281067751 1250 281066501 281066519
    0x24050702031e0c0a02040c080a1a100807030b1009080c09011406030411100e010305060406030c05060d020d09050c03070b1303110d0f111215040b1b070c030606 70
    0x203420b0300070200307034601550982e9500384095001102141035038004c95030b40c00010fa44a00c2102c107800c26984803074005045c4410350034110340100c5081300d466420701258204030350b40d000d200b150550762403030420219a610714044015154022590380c020600c1c208800740310380c1200b0888280c50303c00e401c42e510188002c042164520302803191104c04a109642ca0702c21381040401107601500030590f455032603503060003113003451032160410800150710710000c521540e80350007402e421030800c0b942403140c2400c60311401480c030781c40d110300380c8070301c10001e40c2105100c25a01510300101c1c0072041007280d004c00d420525102e030701d29040703d0702c00c0c019908080b81229180d82075134008040d010518540307a0840c0d13600301180c0d224482080d40000506111000202c00c0c02401d030846118003251200e0710580d9051109104c4450070f541c1c5940c106020304181900050189507000ea00300480c0415512a204444004103085000240d00356001840b4424001d83e15502002c40744a00e1003000041d40d120859 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 281069001 1250 281067751 281067757
    0xd0e0109020f0904030c080307051b150703050a0608060c070b0702060411010c03090b0309070801180213090204290102070501260a0b04020c0c090f060d06050903072405070203 77
    0x951244400361451a603040543d40c50b640700e44070307040200f507090060b11000c1544c0c000f251076100045001a40c442500c000c0c020010035001540010521803800d0b440d007031441e01008100728205a0b841c400035109410581200f402408034109682d254204809401540e9121040c1907440c5081600411079203840010036501c0b564003c01c0855000c040702e4011a001c4600c2002902040110440441c038a000031008500940110009140152400ea800d909440201c81e48103145848001074a01503251104407540207281203d00147c01941440000e00510440c0c4195440303d5003000010381800c0000e05000b040c460036003c0f980350a50303400c011a07020b102825071141d900d00300a43d001030300d200780d01c00c1900100942c2002c141c11400a001c101240c00c407a001c41d08070380c007482003030045043c10341019412581d1640b1150541c03070960301280841c602024001c0440e581c50002410b140002c0c01981c02182c0d01c2044210b444c1d4200380c049201d90358140c141c2d241640b4107004211420700000403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 281070251 1250 281069001 281069003
    0xb01030204051312050c15090d0206060312040b0913060e010608090a121b020411071713050d05031207200706080606090a0b07080c0f010c050d09080912030d0e0109 72
    0x1150542030a552811680354014560058207403052094000d04004031007c83c1d0300c50703031148008080b00490071b28001e00c0c0c00000341001d80240c00961402201041790403c950a40310a0780d100303035840c1005004503844c481c1172078283da101450b02c9004649416500301c06070480e07480d69a0500c40f6182e9030f502d03d40303415900303400074403081421040301c0e20240501d060b000303207440013980308603110110b0b0041004c2c1c1d40d0038901c030f1106400014008040240c1d848501c91610030300300b0f050303003400d40c410201850b11461b0300900b440760085642020400004108844020149580302607642c02c103410003804544032644011903800002c0e403a24001603001890301c007100c0b02544d0b9a1643d80b6030f4024050950300000070642c000c11040c0f00070400c0e00c603640051011034810300380303166180c42282000e400c10150b000b49564503410026191301c1683d0040684e00342c41c0b0f81440005942000345000c030200d2245648458000d000314015001000c004000303040c1c61035540c2800d000c0258506030030307403c84000f910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 281071501 1250 281070251 281070263
    0x305012a0f030b0f03060403090501120b0a050910091802101b0b090f1509010e061b0a030f091104050604060501120c0c0f0b060f0105040e0f220b010302040513 70
    0x15641c07802403180e049030444010141c21444940e4048011074240b40c0121010360114040c080c0c200920350340006054074910302004100300220350b0b0300002e0440d00280c41011300c00c40d102c002281248010092003401840714990401084542c010155541c4141e158284d11410260400f14404c601441c0088061200182c9516045600d82d403070028143e40074001c07680a100d80011410400030410042201c1c00b80a110b0640c54540000000e080d9504802910b401c2e82102082c0300b0030105e40c80000404040d0b02800c10748403045808110014074500300d4045540741002201c80501072881090321a081c0140c406110550312802804242c80e02481200d001031039200c04002071602c182d004400c10b40c0149031080c00c40005880d1142000c1131840103581c1100c0c50b00901c13185140040900600f00028200241028901003208540388001428802c2041c410000075009100250514040e410070456200030b1000c1c0d803c00b4402d4141c00d00027280102e02d4040807506444648240480e0b20754009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 281072751 1250 281071501 281071517
    0x806010302030903031b1603081f0515030405010b10181a07020f0303070c0e010e1b0a051b06090a0b100b0a0f0302090414070807030905071e030204060305012a 70
    0x100040c80452180c2481d41213286c01070180c0c4428008107111040c2c1e00d400b0b60356542c0b19040942107401d8401c002c1c0030000400c10702c0783e002c22203131301d552080080094a05100b9501c9035201c0c2402405402894205a800300e0803400c1c074a4000d41001b001001ca582036195404119121219150018480031310fa01c09070310284105801841c0c0251401815000a015030b4104208cd580f07401ca03c040c41d422201e0000d08801c01402048003419450b81d120007249406108081c03001061034080c440c00a115040150000d0001c01c0700c0c4030082c1c2001d14903440c9007122023916194200c207485d80c020010031150390385000049217403a054040c2c90000d48109c100100c4c5482050b041c196840c90540703440b0002d0507000d0151010a545612520200781540b02000100d03203402a0010400103000307100509040c686401003000c200d002a600e42911b403224046074003030400911311644100558802076125080000c04810410706420204850113588802007c0d51050f09024600070944003031100011100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 281074001 1250 281072751 281072761
    0x6060305060d1106090111120405180f0a2f03060f04150501051c090f0c090c081605040302030a050102040311060301081f1b030c020709110426030307020d080601030203090303 77
    0x3074401005100c0050518407200312081c03600a023012481d0048240312180880d042003203060240d02052b003c0284404079a00e441c04104010340500090400b0b040c0c187d60f214080520290740340c48800e0200100341404c0000e003544051501a070003116428000d2503000c2100005052034041c44615075011140d062110b8202001100d56400c5440d9030940a0100034484000080d2442098a0395020700045a04ac40003805c00c4a03014013203500c00300045290034900681d55a1000010f50000c8858140c020f2140300700350100c419014903040690305000d200242000c00405500600480c0e108040e80186801030300c042150780d000c00d10032102d0030303044500301e02000780c4143d402c2401900414000030f051a0f001d55001c92510f0740030740250210f503035840c81c15105030701041490014031a00030706010008a2000b03501c000c1c0124401d0080c124031405601d0701072240800b00c04c0c80e5900740412a0380300e1429000003959030a400101902140041340031031440e501c240200d07031044404500540c91500c2d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 281075251 1250 281074001 281074009
    0x605150307050319230705190b1b03041d090706050a0507060905122d0406120b1503041a0106020303040b01030b1503010608030d150303081f090f06060305060d11 71
    0x204d51040f80c0503801550700401c4c0114005144480038030103001000c0407420001441140725198060242201d1031381c1040001301c03012001c0b10346000781c0b080705178400781c00141e40300d10314041c2e9040350342c082c0d613400a039841d01444a130300316100d10360031412284a40ea640000307031010b1054060340c6000030410000701011038280d80141804510880484045095440816629170030801c166030b8190038600d40300803411002110807214070450146246851b00e000e00c042d01075000d19030414503641c3c940402c00440e81d41e04036407444264481c00c009a603440c043c070b400244461880b6401001d03804440021038070030720000680788074a031b00c00300c0f0a24503401c54a905004100042c050001e8510910050000e600e00f80a6440100080c07001191210225240c0a05940280c40202c0945a001d5020000700e07600c80c41082c0c2080403003006d22900424040d00e1010740c60180c000742d80290411007500020107165201c402142c6065034100401d0329540104988400f04c000b020f0310760f800710035900c01c0a00e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 281076501 1250 281075251 281075293
    0xc0315080316050c090c0901030c020d1b170301080f071a090d050309030a150b0102030903150712090507030303050f10140d0204050901060e06030607091406040305060406051503070503 81
    0xf000300701300e601c60364210001980600c01103a18034a501d03004070380c0001550305401004040c0905002515482c18031440041240c41510000506001d03c1d45110040c0550f02d032150008004880129660390303181c0509035504d051080011590384503081300041c81f903030507010701080d10b501c3c2c4102d01d2900d070001041014044d103100c0103039260b0000704200072130340c0d8003085101802482440030507000b03c01d6103107843c100d0702030440070740c1075410800113100d06640c0425132211903000d108200100d5264410121101d8942d0300c50000c04614160910040c800000341e403d040b2440307545c00b40005c0d5950030098400c1d186c181d489201c01440554140002503503841021003d410151a040100c7d0301030300080c0c2a0b56056648600e940d558034410300400c024058840e6110070280c005210508200d0300007850b04101d8402c0c02d0b10010b9064000186a030345000f103c00545d0440c1c111015400c1c18140240100016180c0000a00e0001080741c03c41c10080385200890301c000300a0f020f0108a420030080c20070b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 281077751 1250 281076501 281076503
    0x5030703090204020405041410050103060303052703060a020315060412060e01020d020f30070806060f0c0f0615010f030506040b0a0e0a05130b010303051b0d02010c0315080316 77
    0x84d02440003082e55100c0f845070050503502072502c00c2213030130007041c10880e902254003c681014107142051002c60b81210032512130041645100708580540380700e154803507040551640c3d15004aa081c004115950780103103018201603481d0102600c1d445003001160b1003240f10b160071301e19810342c1901c003103060307030b80603880709900300d4000f6140000c99450102240d01aa800d09401113001c50b02ca2405298010f03180c0c1060303907a4143d0642214502d4115441c194010b0505c001c210403040011f14a440300b00a40b440b02b15103c5e002900c4081d583e00c120b44801290000d80790903c19000010aa072030610140030b01d950040e100c1ea440c60541110841c081c0c24000c02c41e46d005526000941d44030388903c24000d00800d03841850300020704046002409459000d0030510074403002e2a03401d40401d007503800282c1180c2c0c3c10b0409541d9905000240d042514084984003001c0c011013210034066a010b4128041400c801d40c1c080013504046040d25034a8071813030152103001e90090003614010f80d0b103120b400b2031345 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 281079001 1250 281077751 281077759
    0xd06050a0e030a050c070b040f0312020a060f020405101814040b1305100608091c020a022d04090819050d0509030706050c07020f040218030a0b060916050307030902 72
    0x2200c02080051850f8030070103d0384000b0b0400a40b41030281410b20000780a013040f06a511700d031a140502d40c4c00c40811500018100c032440402051546000f004501d1415604c601c062046804202000c0d0094209118203401150700841d9815901c3c41176105140300400c4d41c1180040c41c0c00d00000b030020400b040c1070643c0003680c401d10559140d076810f408610802100c07034042041e01d00590300030744522581e4040700134080c1080c2805100600130400900c426180d080c04101c8000d00e0074100d21b8002180e0000c0c0d0440c001c1c1ca41d407031518134409079010708030303600142c014020103400c2d084c0801c03030741c802d10007814104c0c0500039030011078220310001c50500c40a181490900e42103c21002c06c0700c005440000f490760002401008206c07040c050668080385440b6540d06000745038001c0350591420b1545035205503400a400114400c4c142883da159480c00f5003203508548080c900348440039016683c240c032407003d540004038070320301008084d000003609a4400342145c442d250107074058495064100e80c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 281080251 1250 281079001 281079011
    0x40b09040b100b0d05011d0c04030305070c0b210c070327030c08010e010c03020415140c0307030504030b06060412080304030c060e01090c0905060f012d050c0712020d06050a 76
    0x480901d039409440501301d01c44000909500d0076042e24007650851902040c080045020011014034400640301160b40600708bc84da101601c2c130b4151045110b5030040314401c80c010030301c546052510b011446006051580d0548a030f1241c2d0100011402001802000504081010b0348102d107402c00e00c401200c0300007030040c4216100e0740c43c0c510a0071950469030580c0c0d0342c0c412100001c8424091019401900e040440c5424140307140150800340c2440502d0900900880f0b42e0407481560080b2440340c4007003015207440790708034640206158030500c4240c0c4c144501c4400304900f407504a04480803070b40c0d03c84621030008041d54415160b50030080066050040d40d03c80c62000c02d0140c0a0000e00b5000c20780005001c0e405c0e85403078405288240c01088540380380c0410850151280c02030810b840310700742003000307040340054403072110400740782d007140c80d000c1e802c001c00007100750040041c2c20001a0042a50045502d40c500e9840029103484c01a501c038031a021003c0116400e40c0c040c035004100c201000c91 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 281081501 1250 281080251 281080259
    0xf03010903050c01060e0115050c0c2110050c250c060c05060702010c120b190b030105090a0b1f111516090b0703050c100606050d0b040b09040b10 64
    0x42100c1035090180c000c2200043e041050703031820310400010708044100c030500d55040c0844c030b8400c804160228018030600251540100ba03041010180c04003004200f0400c0c0c100c0c060802918940910301c18955204400100704e40e8006805298070400052104070304100250100e04a400990316804112100e040d5041012992511111016203002d880e082e008095074078110f4603140e0000d203c45c0841e454007031404461984442034515820403001d02003503640200000400d11200103110240060050100042288000014604030380c0100d40ca0340456840e4111001a07032124020158080e102112010319414140d9481d0900b541620703010f500c060101e401c40303290001c01c0400480d080321490400015061091342c0c40030f0207142e468114031040c0b410f00c1141036405540c0c0000e09201010030030300506070041010011032243c0707000c107018043d910300300602180d0004908184181c1000d08013405824140654050b000b005800c12599588a0315079018454005d01040b45d10707421144001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 281082751 1250 281081501 281081503
    0x1d0706030c0c0f110a03170301060f0804020109060e0a120c050102010c020f0607031104080303100521121b070612060e1524040b0909070c02010504061d0607080d050601021f0b0f03 79
    0xc00c4a0f01f0480b03002d9881d41001d1001c0c20f40039803049640c04028151040000603680f0000b910111340c142e06120350250380120000d0000c2440f0f400002c41000c402802e40c0502c8001c503075103011514203800801000703940d0031080341c4403944400c6428041c0d0050001c5080705d031080d40501d400c3c0f02e182403454101a281c0c00100d0940d80269400e41c40342c0070609043c4464944514144d5080c3d40f41680d40784091100a00652111595000d0000395400070038192000060507400a031140410030640700c203d600c070100684459480d40030107050614000e40031902c1c0c540c41460301d000c0e91003070401c82d0340d07005100108046061581040d0600c441c034001a141c050040401a0004d0710003606d003681c4a0546205200024000400c810200310000c0798000140c0d800c9000c070303004d82d0305502d031420b50388040020a0302240721000410342c111000096800500501a01a00070790717500e81c0040c06a5200e0744012a614501ea005000b260301d10b6481662046410798880f00d20b0000c054440c5a044044c0c600003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 281084001 1250 281082751 281082773
    0x4030204090f0b0606041a0d14180f0d14070318091a031203060603100305070e0106021006050303040b16050318090c04060e0409061d0706030c0c0f110a03 68
    0x1107034041024414001004a04070b003099001800781c1700302d4240351400c1c01d0b4070300a00302442c1601c1d04080005a4142400698000c4403c000310000c1c110010b051071002038280204141403417540d8025031142d04445039000c44d107500348800305e0340d44044a080748400403005600100c42202400040701800f006400500c001c0c00c010b00500000042014210601040c10080e000c03c1c14401d8014610900207090258285c0c0e0700300a05994580e100d41c2d410300459503654964001403c41d1103071101c0003500e40030b00c0c52010b0503200f586e82035680c0c0b1a03002946000355605400b0792a4150018070003840b41b9200e00001c2c20b52310080c200440780b15455070311442c0c11984424141004000f00c1c900210803401c7c09112941c1103800d41c4035241c40d0030f2604000901c0c9002d071000c1a440365480d1000034040c09190b4003c8100031081480c1c0c1000e50b1114038020380e0354100c5200c0c28010034209942850340301d000c2e0036401c070360540208400c207803040c903944d0f0600224440f003200c0368800511727040800850511084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 281085251 1250 281084001 281084003
    0x1020f0610060806011e2007030b071407062c03070b06010807050f0c010b04060501020604080f03040807050d0c0623060d08040f06020c04050a09081b031e070c171c050403020409 78
    0x4080c001070001f050150032032212184941c107640180350400c0001c0b8030982c1c40348c1c040c1c0d147c90710b80e91a1525861000040c810481e01800b01030502507806040340145061300b417900c40410840444009950080b42c507801002d02c094410004038000500c154000c541c2c0b681c1c00039003031a001c0d00d443d100c034408090780c0e00480103411040c1c1d5515080d110904103440340601500d82400100b80794030341543c0b201a10300c00c1c047c1c3d074146000080040303010440840e066514481d403080543e4a84c80031034038010254038900341c00303651150804041c584030240c80076000c10a010f05541240da1a40c5080c180322320b4248224040b50f51310001c20000902c42600016031300035002a80c00f920410300d2180401c420b582700034003000c1d1464600480c0a000840000481d500d41215007e01c0001d00b400b8501641075008043c041c07540200758030707580034680107000002c0c65001e110790803030803a00781c50390b00c001c40b00203041c010701001d94440020500140d149000c40a480c0c070310ba1420900c0c158813580444c050f1046410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 281086501 1250 281085251 281085257
    0x60501050901080120090f1807031d07090b03030409090302030c010e12090d020f03030a030603021809120309161206050a09020303180303040e0f0601020f0610060806011e 75
    0x40148601e1030001c1c0414018400c401c0203101500715900160030080111030703000350114000450b0b41294486400401d0007900040c25410100e44140c2903e0000b64125014000a0f1414600600490511580d090158550f0000b400794504004110b002403a40e0410241d1500c010300000071b80702010302407140c2a0380b1990143d5207686c0400c0686084d01c802c25268050790b040494200d144000b4a42034900303441c0f085a0105226a01c0d00104500c159107100d51b58043c040000d1400040b40c01d07801c01c208030b074030a640382c3e0071080011081c0001d01000ba41c4117040c0750014240303071007002403200165400503151016100c10341107011b80e8500c0d018440e03100001006504140200340511885001e42c060701c5035000348003c4190341d00181e00c9101d5000702c540681315000100c002c5072002c2040c2e502030025800380c0030742030400c400c10000442044821354014498003006200d13010010845500645007104ea08100a050400942d000c01000b40032074108420b01070300007140054441c042c0f00b4861151 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 281087751 1250 281086501 281086511
    0x207050303090f10050708040803060112050a0e07060801050607060902120303010303020d1218200627060a0509060a050d02070b01061b021807020102040b0403050312070c0b1303050d0906 82
    0x440b05908006405031200340c4a45003008106d241604241d906a000d540980e82d03135070300d59425006859024040203107404031172415081080c4c402c0247d20070403c01c1140412548410b40da800c0c01c5030a11000d0290300d030051000d110810004205070024074a00340b0040036511880e0040008514541090780240c0c01684240074031050340e80c00c00d075503143c510030405041c480c014901c506603170342c0007050400605801e03113980060400c0d00300010340504c2d00c800803d000c1c0d036a5072001d605041203503091040441c0003400b0405044c186000c10848100950a40f9810300f842401402c2103150703040209658180031040100036420241d9100809106102d0074400700c1c25414040c0c02045051102c914101c1040700c0c0d04a5809640e841c4510712140c6e40da0040d84c002990b070002d0807806400785900800040c000460040100b040100c003034021031810031011129951042000c451f100030500000e4207030390581011a100340744141c29210114068180b40f850400515601022940480c0e026201c2591325 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 281089001 1250 281087751 281087773
    0xf1305030a0c05180c071202010e0a03020705100e010f0c05150c0d05060406180222060914010c030c020409261c0c02060105122a1f02120d020705030309 67
    0x3902c60204900b0381c0e959504c6078507040700602114440d00b2009460004c001c0d1828010038400d4200812080c028815120b215a035498060740c4e6480c24010f041c42a803440702c0460000b440346951059182c416500d03428000d18002e010344021f003600c40203541c10301402c0c520300950f0b080c040081e4040c04010b8002a03560400521007070032100082c1045100d0b506280007000034010420f840c451070b4000003030041e5211440c4407500040000c10036001c41012000100240558114118030f0450380b10600c00145400c03008011107030041c1c2043c000b004140d00c41c9040c0050304240d4020003e186c0304000145280d03880d594982c818001d8103412004410b00022100c2084503c10400c22000074010424881107036260b0000c2c0d2144414050b00d0700544501040c4000b4134010450300209107140001d01c524404508031504c200540b400174a4041c1c0d0000c7d1000d0355802003242480d000030700c2e56001e41203504603400e500e54180d00c18001c45c0c0010707400b480760a000c1003003800114092485040148190840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 281090251 1250 281089001 281089009
    0x705030403030b040e1b0a0513090201091205120a21021308010614150d051303030506060702130c020f0f03070314160807060207080c060118020f0f1305030a0c05 71
    0x1018030544d00550910910480c07200001900001310003082c500e0301691a484000b05902180c50340c0100ea006c40341c41048d0403c1c0300c02c1e0707002881850007a6a40d0764003a80b640c200c840d0340c58004034001d115510041c9006080b806506c040e001c248200d01d080c80c0d440f0b0107a40303980000c403445d80348000394680c0044c04841442102c9030040c001e0810000a01c076051510100c5100c80201ca20400c1c00b840f41c8103205c80903001d00f0400c80e01c80000e0090100014203214000c48100752424504030003082c64000490704a107044000d0303902940e0f004050207202c159034000758000d007001c0c000000951040300d01c4d41c010f4450901c030a400d01c862480040d512035201c3e0400412090325030002c0c1003117550801c1120502003101c002011003030703000030030982c0d21051803805200a2041c59409460303e2000310712800440702c0407600d02e048503407900981c0d6400f120b0311900b5040748180c05941822507820424a202940d8406c0036082044003a03140300030841d51040481d003000e030709200803100b10800307210074005468 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 281091501 1250 281090251 281090261
    0x90308070306060e030c0402090a1509030507050a08061f170102180f01091e03201201050601021504020d06020c0607020d02071208030a0603061a01030b09091203040305040905070503040303 83
    0xf514204c03070002c42520200c1e84030411425842d006540006404401f40c407452100b400600000d5015421200c007410700520440860004450301d004051000443c5d1412043d0300042e100b046000e001c0c0d030b450f80810120b0801862001c1140b83c8404a0000f85002c010f02d0541c0e813441e4090005a544c099000e40d1000d034594074401c0f1842104280c030140c4460b6809140b6105031160702c00e09200c0b40705d500900c540740201c10341c0014050205840c0514421074590380c0040507020545292103190b448846542c2600c0c012910b060042c1d200d01d20495008c00c0021000c1d40040c006005500d1804554035036000f60703449405150190340c84072090000301513040010803080c41c0f4920151101c1401c00c10700481c2200c0702c4401408141012001c2845460076a01a600542c4e004000301b01d81e010b0b40c03034001041c213003140d14503012038503101d4a0760140c202003240c94800c4c0812409401c09050303074035483c1640d80000d0320a0f0708020301400301190007130703042c452940200e60701d0300d4098907031500e0f19005003a90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 281092751 1250 281091501 281091509
    0x103050109150302090403030209030706031407021b0d0c0801020307030203091903170604020d0906231e04080712030603021c050709180b01090605010e0603010803070303110706090308070306 84
    0x500e018998004061001c20342c4080d41d90480d0340100503181e40c2400c50113401085444c9a1500880c80001012901540b000d010070081c082044a296281401aa200e00d04202c10340007150300126614032a180110f41302403e0b40c801c1090b2000c40d41c840b00c40c0c03400ca803c1200c607032012035400030030720141000400c85030740c807254404108040325485039402000400c40d010300199035121100070600c136543e1034040d203c1100d94954104004940c604000018242101601d0441e11800041c04201c624540721280700381140030740a203aa803006020034269a034000d01c01e8941d0709080c8903c13000140768400010320390700c4d00e56011a20714190b004015044003512050080b82401c03402010000780d0106500d0200e40e05001c0010322485514411007e028000e13000503c0e0038408000828400d00c554032620035900e0a82c0c03829100d14021060041d030703102c00c1c010311090380e005014104c0041c0c03282c0c1101d804603c0f40c40c0c0f12403c00c509603072104151001404100c001c2501c890030881e83c141d161040c0743c010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 281094001 1250 281092751 281092769
    0x106030b061c03140721080a0e030901140c01140a0903030b040b030c0409020f10020f060615070b060f0402030c09034317070312090605030f250e01030501 68
    0x5686503009049040c44010b01c1300e0b0b6080100f841c50901c241c40680da00302c902d8a118103003000040c40750017850200c08030b60b803036407982c80c2000703070622010000203071242c010040c1c44204110001c0c1172042120f030032000700d0440c01e40d2502e2500308071008112059010b42041d950200d601c407540d10300642500c44603034149000341e14040e04403540b9900021134000ca0300043e100001c680c80c2c0750020a80d01400505603a800c00208200c00d01d41541c001a62034150b0003c0342a00c3c001e45804041144240842285004020050049001049000b83c81d44d0b00110020414200040f440c00410103a0700f04590544201d0004a105d4480342000e0001c55814200e0a400e0072880c02c140c001c00c608805409261300344145080ca03000b80b803464410194014107040540540c0c80b5070280039240e80c601180c0801c580d81040c04c07621309207a038000c1449000b50740650f1a04da045d546d030a50031009005008203d08990051041c0c00350035052403c12407013400300103640703141c002050080050103686040c2c1c040014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 281095251 1250 281094001 281094049
    0x715030f0b0f091b03090d08010f0b0a0528090e06040b03101107021e1c0507050405060d0209070305060a08061003080a0215011401030501080c010225080106030b06 72
    0xc41c1e40c2d400d20400c01d0400c201c49488540e2201e41c031904141e90584218a603440c400014400400000100c11100203810b40d100b60701d613a240d950714103c0311070318499259208001d005100506000b803001d4000c1280000c1620008040807034405124184c6200c00310102c1c404140c103004031800740480581c4480140e03814003404401e02d02007561901d00c0e0741000c10080c0d0b9451410190369101085404890b0020f0006420350350184201c03510002443c03000d072040d0f0780c804a108041c940c006500c4509074101002d00103c614001c00d01025180c01020190700c00322403c3e441e001603441015060107404580c0d000255450082c0031312a003580e054000d02d509a01443c1084607844018000710150b1368009031003600c4110000c1c0c160724040c42d03810b022856501201c0045000c04c1080c0b00d0300310703104007640c06010690703a499416460703c2c10882001d00503040f0580c032800d40401215041c0690b8103000491507056500c102d59421540d0b203130070031140c440d1100c09002c01440c0c182e1010460345085040b0f018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 281096501 1250 281095251 281095271
    0xf0b07051603180b04090b040c0206040b130f08120601082428030302030d0c2c130c030906140c070f0c09020a05030a060812070f050304080715030f 65
    0x20010004610040410114540c0403d04407203502e00c010040450700d43d035540382c644800110001e4820810801d0003a45490500c4501508c00a242400313290030880d510003075110301c260542c07100d130ba5007004d684064661440c403001841c034100605c0401140381000c0e020741002800104200710150038103070624208901c02d82d5095890101c08284c190817618080491610803074000071001500303803021820b129050000c04d01d80c000c8000c1202000b030481c100011346440d402641c604034100c4203280070007880440900b9041020044d2404090002c1c0345502480c4540035a0080c0c403404050240080d071540ea11104000003800b6500355803503011500c03000e07803802c40340041d2607000f80f11001d0800503450f51004107000c2d40020100140c05100c45c02d569800504401405030303272064801c815240d01d0320b0f00018120304c01081d80404007500b140b0003440e12111340c440d14182c00d4046420f0b60345000402c0700141501042141c68000c201c509585010908004030140c11140c0712980641190704200c8041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 281097751 1250 281096501 281096527
    0x9170306210d090806010614090d0203011404030210060f150e120c0a090c0f080a0603020312044103030c0d0906020d020303071e020a1a100906150c1a01030f0b0705 72
    0x100c5109056003401d6141e46a510004098aca00100080d405519202441500c50b64500754644a40c2c041e13004c17109012404526030b01291514030402e901c0d5100d0070800c0c00886c21308400d510a00e806450b01c00e104412000001c3c5410030380c3d010320a1294440ca001c01300600b804401500149200c080401a1150b88003000d8a242c2014025800700007803107000035200c42895010101642c3c019086a64540c070600280031190f01c11b0041c0360101641c610307291601c2c01c00c61000032241c0200c1104400401c070b0061800c0d4a108203080c082da0500040c41f40e5880d00c0010081071418103a81d0384c6050402d8600200641422031004440d01150070400c10407403500d8000352025000001c8000ca0b160210003c88101e040007407081c0000c24180b20f490301175a0200350506054060a0350300a90840c0310343d60320000c821945103124089503215140c0a00e1240c1d030140405404a50250392450200d2500011a2206003802d8004450144a0850000601c500710f0040740d402455400d0040c03420702c14000c44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 281099001 1250 281097751 281097767
    0x6150907590907120c080f06040902010e1306030f05070603051f180e0d030605011b03021506061309050f06300c060a020c120109170306210d0908060106 67
    0x601401c070b14404105400d1084201034000c00c60410308210601034034400512070b007016a25100703000f146001140591800c0d1142142c050707030503101e03404109034540c00d026410807082080d8480039620b19001001c229001003410364544940e024040413410413a0280442c1c1000c1c1c01d00c03544e0140410103d0001112045010595000c07013040c0710100300e004090f20240020107440d0110b0701948102050360307a010b0b00214140c901c00d8850310555512008030034000c40e294203001c0e0040c0c0c05080840c400030380000d505608504050001c07454081c004400d0501c400342a484030011560b40c20030044047d170942c11541d002101150b402c0b25506070182c16440010900c400c1c2072848014031500340d4440010807000c01c5824000d000c141e1a94039021000c3d44a00e0145440c0d4010f06030081a0340e0300700f5040c451410707074a500400310411441016a07c0c003454000130016600216141c1d0411000aa80842000c441c40c04800400ca2a90140001041c1038415400407101da840395005002c03041e041001c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 281100251 1250 281099001 281099177
    0x406120f06091104020c0f0606101704080408150a0e06060a03031b020405070e040f0216030f050c0a20030d020606040e010902090708010602070806150907 68
    0x45101121820311030700038000c019403e035002e440090040092800440e8032441181d00c202541c00c01e43e03591051222490706104a1000030b403480d0381c1c450500784040001e80e0441e00400b400343c28103071508181450400c211440c003030f4601d0340c401081048295805100c038130070780c1e40d0003410300750508a0200e1aa001c03d400000c0900c900d6100c15948400100044103180341c0080c028001414118009802d0a00d20741c8203074051818503e0000b55040da9000711010030155070004203080301c158030101c5035003103500c0224041110030050000003039020442401d00600a082c140311012190200c4600d444103080014043c0d0407040c41048416000f04815520503815140401e401080d03114032801080c030094020740c0b100210044c007044a51041c9010b0680d810307502205c10741074035500b065a55030812501c01820160008260026041030041550025198104a104036060078442c030030b81000300201c044115031302500d07810050507030070700c0705a0200d01003101407080403104c032220400e0200000e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 281101501 1250 281100251 281100263
    0xe0a060f080c0603012d03080d0f0207020f1504080f0d120e0d14120415153203010e010902010806010e090c0a05040302100c03020d080f2a0a0804020406120f 69
    0x541c2403040340c0885110020b03188503240d51480c00347c807498403800c907070800d07008403205030314280e4000740700074040c42190360054005000f004582d03801170404c800300341c54041909003040c0500000800b117008010150814007180702038001d0140030311000b00300c0c91280c40e4079030b41982004100385000c40c0108070030040c2c40d01450304142e11003403c108a00280700b11120045a60220401c1105010041c05103007a4000e6a81d17003800315814070180c2002801c814001c0168148806c20000d002140f016a040d80e6040700d8172030000a0691900002c4c216a00c0e16070340f180c16516440b140c02103603800302025501c01000d09100d013203094031401050401c00c004110f1039924400280d13640090780103030140c60056a000300404040d61040400800c50580c0002c00c038094882e6900400310b140c01150100c1c4506041c85210f0aa50b03035150000003103503081102541603213403840b1210800c800c0e02c001404451916114441541410b10600041b100c5031703400410000401c800da03030000b4512005500c80c1c280c0182c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 281102751 1250 281101501 281101529
    0xa061d010e060a05031008060f0c280e030f0d02070311030c0a0605070506010909030c111f0c0b0115020304050108100f0909060518060a0c05040e0a060f080c060301 72
    0x1200503960051030003000d640c485408503c410b002c96200c8000c5200703910300007600109a80d146201c507035921098a90156403501c0c1c1c4001803040e42900050010042000e03802488000454805e20f40b01a907903003140c0000b0b8442c21054600d0504001560114903104002c2180004c0803038000d407181807a0000501d400003662803620035079810014020304102c018042180c255540c1c070060243c0e48080c1c0120f41034010030000003281c1342c55104140d12203406032201c0102c9981580d450000103c28141c2c0b40e4060003c4401c0e882a0320940304144410700551204514228141411048100b05074483d840102d00322404840f004c0c1d010045d1411141d00307082088254681d102d8440644030590801038000643d01c0d070000312201103411034108280034180420003a01c03000c03a006907100100b003141e261580507101103200c080e020342c06a0480f40c114907155080c561104440441d40d0700035a011900261115030510500819000c160018103160005010040c1c20001140003800140b059102c280029 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 281104001 1250 281102751 281102807
    0x91401030c12031101110403120903050a020105030a1407020c0102010e06091207080f0a020d0305060609150903030705060c0405040608030a0903060f0b0409060507020c010e0a180e0a050706020c0a06 87
    0x20207072a584c0c056814028440700d004420300035007a401c1440161220810005000b01050107480074809894104001c3c004008054005480300e071b10140c9130122095803440130f4141c44d004c024007103015170301a60207022828001030009081d5410303600c02840541280060281c0b0000002f4004c00c40114024140d803940020700f030400c0240210001302c440d0002c0012901044da034042881503d0181c2900d007004540c8480060002502a000701d00350040d0440800d03202648007031010301482d103002000c8920b01041030303981b00e003401d07001e65445100740000720303040c0014034082c018007000d04564801103081404541c0002d06e000c946210103032a01d50740744000c0b0369445494102082d0303090040c1c4140040402494028000c140c11a01c800c0180140c469222003588035816960404100800b072074805414640040c0d5104d00e01400c0340c0003650340b500441d106100502c804800d541c0500083c0150714038014019040084d9021800d2103131080540602005401801c4000078021200d400c0e11a2051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 281105251 1250 281104001 281104007
    0x1b0f05181509010b0406080117030313020316060309050d05070302060f04033c0207050f010324080a03030b0105030c0307030c020c030331030302030a0c110402030c04091401030c1203 80
    0x1800004540241c2e05400100d504a0410000c004031151650340f0b201580e44c0302c802c2c0c420f240030501840002d8100700080f824031081d90f61000b440d140024152801b4000c2184001c6114001d6031040b804252207004000512600380040d08480b401800d01e40d01e0711860355802512407a00a011314203c1051802040a240c071034011a8240c161040d42d000e11a016150041e418280721a2910030171004c400000920307600c04a001c504940014241c0044c07100007400560250601031088180b442c40500d010300300d03001000c4640000d280c518003524030040a814010151690004414188002042032214020b220742c2229403150092030000340c03c00c24160308a00740b10b03083d0340d0755601d4400400c607a0320300400206481c100120305502890740c00314a840080800142e4440a40582c01c01d12619001c00e000d00740301d502c1d280c820f003002c0032403800e1000003400b05d070426200c5259804c00460b042c808524035100b081760aa6810400f01c0742c075031455039070078020700250158100088040c03082c0f504140c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 281106501 1250 281105251 281105281
    0xf03050d0f060e220210050a050906070809090f04030827060a0204060e0111060c0906190207030b070302071502090310050405060601020606011d040c17041b0f0518 72
    0x5101e03803090022555032204a41c1d0703514195020016100c4050112a111081032a25201540e02501021100702c40341c0003038405820046045041c0003003040000c100703580700c034000d1201510420a80d5103d06d888014000010f80040c1280c001000441c03d00c80400d41291000c1d07481260b80c3c0303440c01000ca4100c0c030070740c2042d51458141c01c1c41c4212002c0c050420b0458001d0016543c1a680712551401458011210510040718084030360308540d011400f1100c800000748000303040070b41032614280d2b5144040c3d41240c44e1402d40e0340180c01850050040010306400e680d0081403624080d42004510344903080494110b9411482e240d5001a401d817241e20300740000395030720b0400e0307204001a01d0a801c041d030300c5d0307182100e01ea03005004035800144650b02904000d030940320001407040c0c102520700d00b444001c2a2146820043c030020b0041024500d06500303c81d032149100d070000b00d00924100610b0040120f06411100e5070b0602e407a070031301c41d03501c3d1014180310b00111052001d50701d49a0003403014a4074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 281107751 1250 281106501 281106521
    0xe25050910050f031014030c1c0c030f050f010c0c11010e040b04020c07260312070c0807031e050f180d0602070f0b0c04050a0b03071e0908190f03050d 66
    0x34001c8100700400c0103005d109030032502c1c01da420482c0c000105d820151204104400300d6808000801100043c00c44020b150704c0003442440d103680025240c4c2c03070b1110b00481e0410115203940c0140700203a01e5001c00e000f02d448510607400c1529022442c2d80e11241c842240c0000c2d141000f01c401c1c846880e641e22a00305440601c000b5004540d141034610300d80307031502400e01071080708000d8001a808800480040010111414800365044c440c94800020b120f40020f40303000104900b8010079004100441d0041504602c80d844c2e01c1c07851800c0b8401c100e10741002e00300c60070502030280042d020500c100750450710307000c801c50b461603440803c850004100044444001d0120f61000c035080c000c0148490840f031a40b030060204461540e504901c003085807260340600c80d04500030306810419000d000c4003564001440d801c2103400300e02843c989446952070605120001401c0302410030200d2024842c8160205808007442c00741c107042e80758180403400e0b066000301008800503805202488a900c11701002d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 281109001 1250 281107751 281107777
    0xf030905070e15090c120112171810141c150603090302060f01050a03080901030f0e1c0212030c03070903060509030706050903070b040305090a0306060e2505091005 72
    0x1a040050151101c5081214954001c20090010a5100820f0015200c801e602c0e003040d404141c3c00d017000423100c4851440122002c0703a40c2070001c0c1141100b43c01414443c0849030b650f00070040864108034010f07074010b26040901c0140100701c2c1d00c116500085940d000541c41b441e05400302d01507001c00040c4480c000c00181410944004980d096264229489683c000d600300c40d00780c3c07a0803101c115130ba0002c0c0b090541c440754001040001412180140011001c141800551070103050400c40a0360f4030b481c20054550032038100031650b400b0f12007110b10081400e1008204c0c00460040000c003601c0007a00440c448100031002449161180c45044083c2d58082018400d070705144401c00c2d0b481d044a0707400c4811030b04140c00249502070010540d5141a04042848150f80b12034070300791002e9000700c0f50181c100000320008008207065002d040010078521a203180300740342c803c0042440407590044200780051651200248980c000e0a9401c0d01000302c842e080c2c242d00b0300b83c064036181b2444c0303042c0d83c00b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 281110251 1250 281109001 281109029
    0x2703020a141609360f02130203160306080d12051305070e0106081b0706052706041b05030d08060a0323070b090604091107061d0c01020601060f03090507 67
    0x404030241c005001569880109040c02040f661070300145108440540080f0094132652801086030360381c480903280c0c009088640e0000c0580c040c4800d903881101c207a2901100d20420302c03160755140c03003602c008240d20b10240c1140c110507080103103900f001040100c0000c0d100c0010400f014100010f6041d00b0b603016045980865031030341040740d0000c09101c1e0300042030341800015803420301c2d016044d0500010042c110b11b884225502c5400070203001d00740c0094000c200c00b0001480d128901c00c0180b40840a004000d01d1600b4a0103180165150300000c0070214039110030817071074800041d0780a0292140c10f01c0300d06582d03000301040c071140b2103a201808184a40413042c1d211184600000c804151101c299120585c4444190030240701c3c520015400200801081090003410791041c002450f1501086182c00d016440d4641a109601241050518560032503405540b0230804032492030340c2800a0700c2e00398940b0101801c04a40c00c0c4403030b130605840b100c110007001070500c42113010300f100c0410302c0384c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 281111501 1250 281110251 281110259
    0x1009140106080c0702090117101503050106090204152a1a0a090c12170a0f0801140105160f320303060906061309020301092703020a1416 60
    0x801002886400041944480410008082107007101c1c401c64019050095a07440c000605011000310b012490003406095441080d00519024907041c0303480c01d0342400400350075820042c0c05c540003548a0035071103104000401c1240c02010400c03882201c0340c10700c0280c0c141d07106900345040c40440304480b556000d10075000e08215142d00c8026040744243c0e2200d0790380c0d5030881c00d4000c8443d2000c0191400cae1255400300400c400d03d006040e0142e11504421940010401c03200403180c210172110800319000c95011411a94480202801040f010907618900d040b2040047d01c1840b90f0356105819100d90758110f01401045502d900302268403840c0100c06841d0f0b001c44c1c0c600f1004040500c86d000d440c0c049101c0d0036035000002e9078041c041c0206020603039211001081095844131000b1000888000000070350004144045d41c004e141c40c49000c01c55181c1c0494940070ba41f601d41d1543e1215505402c07000120b90300041c00c01c1403a40c4403541202d0442601440391401c000302ca00983d0348400313a10082 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 281112751 1250 281111501 281111531
    0x1f090501060905040902010e15160b1f140609010306030209090d08071d1009030803090f16080307110a0906090b0406050406062102040504020316080c04120b1009 71
    0x290403210941d882221840d101c104000030b4400d04031000c2d0004000d604525200c0c40c0c07054140c9501000d41c0c6001f0300d400170f550b000c880b44241920050b902000c3c034004110394000003260301880f1030014080303400c81c03604095101d0480050200c440e03000d01008291010240d000743e002c400616001440348000c1e142c4418019a1803929020400c0001c50002c0821080c5004d295142d02e0345810034595014401200309010b14603169080980c1001500880000454281c20046000d0007555000d003030600251200d81d840c0012401030141c1c0365509107420022944040161980203070302c4914513403402199400038503550816082142014903000000070042450340c480c6035040402e880074041242e4030b000304000c686c224031400000c10410003480440c8903d084440201030361140c80141041c0d101c9021070100d810480c0e5415600d11b200100f200c4240d04903d42903400a1101022803500f802c2c686280212402c1d001c00071301300e0811001003091442c0080101024158034201001b400303000701b98030303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 281114001 1250 281112751 281112761
    0x5090d0b090c120a0b0a022206020724050a0e0301060902120a0903141b010c0e04050a05012103050c06131203020405031509160303030e0f071d1f09 65
    0x1241c07042c840c1004448182c20441150260031008001800281202c1d8444070168070000741a090301640c02c202185c0071000704400c40d03a0748021481051074160410340041c1c50910644c2299071402120661200c801c8500c00354004115410310f0501d444070075200e4103880040c41c1c0e111050b419401d041c40030402d004254080c000c09070080b92210701a89402030f80c8811101103840140001d49880410074020034144010901d07000303007032100000504403000c82c500712401003c1d20000039140e041803200a292500602c2d80040c203c1d07000300410f51400000c000c44c4030060850440700e241c14042e4805140c0075a06a90742c02c42004180c03002480c1080d41c2c400003000c0b8010031546401400100351f0994868400d0340d055902c007500400c020440014214003010000b008030905101d07032195052000640e809070340c000d40c440c0e20049000d80c4540405424800c130b040c041805940591001c201c1d803038051003031080b021102031b4200030940742c2283c0d00c41d0002441101d241e60a80d20080040c64031125448 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 281115107 1106 281114001 281114011
    0x813091109010813050303040c06080c09210a0c0b0703031808040504051005030f2a090103060e150c13090606120b06193203011505090d0b 61
    0x41d0700c1c41c42d1f00c02c6030200c03a0195100d404108041e049090260010302d5011403a0030491800b020941c0d40110755802103481c1031300c58544080302c80074016004420703003100b0800a915100e081c41036060b444001e080b0002441c110403020340310101e0140003080b41d44402d0944c0f43c140f40c002000050714000d0000000e1001d038032030004c5c0c2903404110704201710044202038a8420f904007907903821058103a080d200208041d8140c2c184503650702203180d0541e07a00c590001542c0301c0b50050940b82607aa403503050a00c0040201b48aa607a041c2d40284c2498a07000d0030750004980c032226039200341d5004d807281001291850210302a9030b106a081b401c2988009070242c0d080681918003142d03641040808135001c00d05400d00881c100c1500100c3c044071180c0c100344081c6601c041d01000045100501c00c440c112440c1000d00b0f04028071a00880d54404002880c00c02a441d0b24241003813851010b941e = true := by decide +kernel

theorem cover : BRFrame.Cov 280935251 281115107 := by
  have h0 := BRFrame.cov_init 280935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 280935251 ≤ n) (h2 : n < 281115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
