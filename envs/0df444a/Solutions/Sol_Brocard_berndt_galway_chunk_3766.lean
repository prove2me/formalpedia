-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3766
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:36:36.921725+00:00
-- url     : https://prove2.me/submissions/92751b9b-ff0c-432f-9f8d-a84cfa3e6c70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 677158273 ≤ n < 677338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 677159523 1250 677158273 677158283
    0x307060911091612181e0209130b060d2003070803040e150102011b0c0c0b120f0c0310050f0d141f060506040b0705070b0f0a08060a06020a080c0f0a 65
    0x84a03544043c007038012040140d00d6025070307040c0565281c80c010f01c02225100c280e00a03840c9400201090895284007002642c0203502070310010a1008058021100100c030f04e04c514071143e11074640c44104154038414020061496940d4195503c0c0b00222954202d54a0006412900030380e4640b0742d520b04541054002d181c40240c844104420000005040361100c0c20a000802c0080c00f800401020703800d21440002c10b124107002500100b0000c4a900c500520301101140c3c3c40c1c1c0e40403115250824003c0d101d9240618040002c100310310303008002c0b00c0c001c0044084101c5200d00c2d00703042c0546494500c3e0b0311030f40410504c480002140b420150b15031501c03076050140c00c010340280c2000c0d0f480c4030311600c0c14001a01d014401d0020f40c860b401101e00b647c05280c4800d8845d00c651030001d203031281c0c9401c4100c0a1101007081d4041408210150480a41544070b5003110341d41c1c00d0034801c1c03401042c425400180e00c0b0641c0c40d808122854020629144244260303132446d0b44e0001c0e0249000000708003298 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 677160773 1250 677159523 677159551
    0xe121e0f0f0a02091f1a0702030c0a030201082404110c0c0a0b0a110c0306072006091533010908010902090406020705070807061806030515120c04050c0408011d030706091109 76
    0x46149c10701480020880c21503c6044913400c41e000244800e034001c000301e480310144540038102c0075200c40004190b0f01e0041c010b202c0b40c0210901d10007103800420080106214090724600c15182c07043d1100d0584060320f0782242440310b00c14040341c0011110100c200280203128500340c1c542c5003031042603c45e102903203031a40265054040d0800240b0740603e096183d40010082c040001e102164220580f44405180b07589074075070040c10b0259000101180ca40d030800d101c000400c0c0b072110101031031901030903216146201e64130003810f800c0e42d048840003584010b00f580018000ba60310f41c0582a903600031811200855250700000e0f20388411900549c01040210b440d207400d0200810160380135204500e0203100c0c1c1d0504098a44c2c2c903013032046600f07105d00e89074508540340c900100000c0d100454020420710030740c02c203140101034030b5000e805049207a500f800f124418180034080c000840c07000120046141042e01e071148070042012000c119036950481e05101003076582c0c5411035002d881101c0e4050f13 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 677162023 1250 677160773 677160787
    0x10b0d2a08010b100203031608040206041e06030506030a0b010308160c0b0408010b0d03021e120d020301140103110a0c1b181a010e121e0f0f0a02091f1a 67
    0x729144c0c9110302d600865204004005640503451020180c21400382000343d525140c2d40700040c0d8600903604405412107100a00c402540002e0801004480c400e80701040542ca401060644072028410045d101c2d4165000420008036038400510003105030b190242d986e40e015a4a50302450020f6204160850020506100c03100e408c5c482c0d05070500044403038200740031041c1d4019446020701c002d4400c03440074085540481e0481880a14030969030051440d68510041c10104020740003070042c1605807070fa01400304c2095010740300741084a07901000c02400c011400b83c003121651440d810445054000201e052580a0f071000e40030054007400000c0761980c0803090b50502100e0700c0102da0b00ea160344441340d0450590f00030b04001b0341c85406482080054050042c0d045c0382c6440156900303041040c0c080070302e00040b00491400c2000b011842510026083c6140c11070307803861008800307035019000704041401804a0b0181d00c54042000c45c0d0060702540d10794220205490026220a03520f00c009446 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 677163273 1250 677162023 677162029
    0x30a080f100f05010318050303130b060301060f1a040f06080106031802060d0b010201021204080901020d02010203060102030405040b0102011e200313020603040f0c0807030b0108010b0d2a08010b 85
    0x181e41c02210080700c0940c0303601c0c20300e185016403032610460b07041c0355442c00c0c540d90600c0468103001285800c00122952800c0c55079105c00c0100d18940181c5841842d440030417010b20f010b008400c21105080c84402a960038102d0410a4900c000f84c2000c80203000c00000400445031203590000f407a0316140e2603190f615100c405401e445103807280782c07843c030740c641404c2d00107030ba480084d52003c00460030300080c3c01c8088401070b40244074210b400756444c000c2008200030804000001d100c40b8001380c0c04c0c1c0e03403641340b44a426030a03070106a42d480d0150700280828480c2e403c00d0707484020b40341014800820140380c0850304910050308000c0c1d04c5241b80d00c42e14448000b400000c804000424034890091079840c01031600d0100c44e61450009105003c000086002c0c002c3c40d10b5200181600440003a0b0f200d80d56000041e0780b281648800c4074800701e00e5000144900061007030b4901c2c02e0f0045c0210703228201d00c1d994264584203024441c0c81002c0c0041c000000e0301080203038140600504000044e05c40681e0b820 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 677164523 1250 677163273 677163301
    0x10050714030318190b1005130c0e0108070206061507080c01051501050702090c0708070206041d100506090409030210021c0b0907051605010b090a05250f120608030a08 73
    0x210210f581c499420b00e04440c02100116103410b400004907002ca0b2610f01c4420318a060b0390340240d5200c0402a107020042072550b0245071541c0c03081e00d640d122000c8941c01528140402c8801d1000b68001100060050a0601d48003501e101000c10320341c40c09900f60b0b02c032609500112103400c91699100200154000d0303803091051274800900b810350a1111660002d02c3c505801081582c2410380451000b00b040303000320607240d034680d004080d40e441c1c9071241001c501e003024900032071555028106c08554480041d03401182074840c080c0910b860b10800c10140406850700d040118214031a07605401a860410320103000c40f41d00d5003024004000455400106844c0c8221405210300d038180240180300e03411008841c0c4244240314404a01049070909500400030000da1270340020034070b003c00071950380a03400755101d10704508038551f01b06103208602d000c105444600340301080f14400340c6201e5500a004c100d04044e104100410380b141c0320740d032007815904088200c801043c8000107101e85808508a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 677165773 1250 677164523 677164561
    0x6010809070b160f120503040c090501060f050c2b02060901110a0c0602190905031009030206061c080d021314012109060608102306100507140303 64
    0x2006140c018240042c044a5203d070040081820f1440c000780c0003008581c14510582d20b400c280c22850061807000d000d4030700da20881d0115000610000049807080b000c2c85894140c41c2c4a540d220316040911400340d903541d0148401c606c5510682d484030342918213054501c00700354103020280048007003844029180030b0005d40031105903410002088100c1c120a41500c503900014038025849007124101036000b446014911000000c0d40c4450104a50b00f00d5160400c4400581c11684200c04030002b10b01140c440090040041c0c00a2022900a00d23104200201069401000b94900e4800d83e0724061142e009000d21a400c540114000d0000b00000e44803400801128601060801e6808002000300d0160300f10100e02103241c4071101104c0c0c20980c001c1d0041d6074008410801d043d161020a079a440e513404100fa44941400d004209000120320020010716005d0808110f03a00d440041011203441804600b0412006200580101d000940d4408865805901956403420700f0304401d804c00190031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 677167023 1250 677165773 677165791
    0x11d100b030c01081e070f0f0203090901060e180a0b030708151f08250902070308010302060d200301030302010b090c0d1d03130f0f0f03030503150d0b060108 69
    0x1294400c0707850100e200c1003a10024038111546648000c2000c5642c2140000c13030243e04211400c00080e19040741981000c10356544a10401c0c68866004903668854000f007582c04c0700240c40100b05450050012004845000303004031001541d40800200c401c00840e076070983d40e030300c03000c0d08107060505010b400c0203071614401a020090146600072102000902655409400800180c40b04600814000b000d001414281c40c4200c0e01058028418440080c03811b82050319500e001419411910850305000c1d419200c05449078696020004560040c403032203242913072070740c00e02ea140c511b000210080c0e80800c040e6164982d411400c0090840d404094a2030250400a0502041c0c03a1004203441d821850003034041940007a4a8081c9001d400b00304802c50248400314041c2c01a0224945801c256441103d01e180020783e200e02c20003081010384200c965031a507a01c81440840e00c00c1c6c0003540d12100240c0001090901500410061850584c040e01c0b8250a00107100043d070707105128a400907840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 677168273 1250 677167023 677167031
    0x110301030f1103010b100e040507110c0d0618080c0f0a0b0402040504060617030c010e0604120f03090f1124031311090c0418021c020901030e011d10 65
    0x558031400e84280388500a442d40161001504a507582500401c080340006408240002441d081c0070b00140e50802c00184070711304100001c0c84c00da12584240300320740c026200410f2508200800e2081e40a011103042c1c0300c0d1a100c03036440440e103c514102543d120f00c10a582c5540700000708840e4240301c00c640b030b0b00722940c00281e8620b000c50b0050600303d030400d8040740e0001e46500c0320728000004000c82d9201500054224800303910f61140480a4401980d41d00700a00981e1904680e498a5040464000740040500141c46006521401489050803030b41d04001600c0080e82d2201c5824421201c000c48400903419669101030030a50f0390b18910801e5400486000880d83c0507a40c5107010081c0700c001035000f1403801000f48040c1101010380d00002a20030101030401d082480300c1c50b40240034a91900131460150860705510707100719118550001242c17240031011000702d401a5026081c601d040544480c0f1741101ca1000f0300c15a00402c1c40134804c80c0e516407000c1e01c02801e00e178000300421011858 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 677169523 1250 677168273 677168279
    0x5010803040f0e13140f0604050313050405040f061e0e0a031202030709150c06140711120d0b0402190305061512180312011e050405011503050c09030a05030d110301 72
    0xc80720b4180740440d8000410710082925035205c034606481340c050082c42e48076060511003844030102c001c005800034100c200d101d0305e403120207210036588280c6000b071403e803407000341002141315030f0b01003480c107003005400441c41440e071150102500c802100c40081c40d001070101e0070401d03401c0340309074028004d409410344c01d6241c1541c020f0003d80b40c610854282c55102440034041d144108a013980c50b0794806820408401a1074007036130160801c440d0325020960785203005141510015950701d4403000705400900e013075031704400c201c003034456502110380081d02800b02d80251503070160490510b00c2282da00040b28a411010405031003854154580d41c44002c0090030300c2907903444100c0d5400b41c035000200710103c031a95a4a8914810103111190303401500b0008981102c50300300f0707000c00c2c0c1c0a585525580d503446d001048100d031801c0c41000000c10b0110031000c0030a01942015900c1004443d20700c0c00e0151000109040c0003049104480c1c039040040c000c42088030364801c1035454041c0040007411581 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 677170773 1250 677169523 677169541
    0x7090c0f05070f020a0b0d022101150e0406051302070c050f03070b0c160b04150201020307050304060504050a08040f230102120d090804180507020c03210d05010803040f0e 75
    0x10a4010180c400075040d0100030540d2210343d445401000e2a0121039074590084142c1c00083d0427002521441d086194000c40d03000016000a5050321505a00300800b6040400241c0e0307059000c115080d0000e4607088002110380e00c10b0b030851880f2400090250f600ea200e03107048450402250841031150b5070f00300d003425480e28001545815950344004803965202401d0006140803001707036040d00040802000400c0345402c0e80c01038004c43d03c1d0003004000003040381009130300b40e000c00c507401000034505000050200e0030581102e5000f034024410380b0b80070342c91509d0720029030b400394100100c80000700a08001054542084940d1000704412003071502d441103000179100c045540d61800e400700d001c20300044203581540206902907029034100e643d00d50b1041d50312031108000343c071a00310b40e144c0700c00540c0850011518170110310000b0f01410b0b032501c505503890a05034030302d08203421760103050160442c80d400c0d904c03c3d82d0103005000000c0d52102d24021055031840038036044003840d40072510a10007040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 677172023 1250 677170773 677170777
    0x11b08090d06021204050109020a1406030609070c0611090111060103051c140d05070806060705070b1e03041103120a0210020a11060f07031a030606040b0102031b07090c0f05 76
    0x4412680d94900c01c945090060107030040b00d1010250034003043c10302081003015407100084500c00e4615586480d551615201202c91038103106410140400000b002032804c403106a612090078100342081100783c1c1c40d0034044880d58040800c0800d0002110169980c000c01c010040d50702004c01441258116601c00340c6076413084103120180f054031040303020580c0c0659412052106034240302034480c00f541d07901c14044e10041d26500c010441030008602c0302c2c1001400c4032110398102c1e0041003841c0c6000c0b060701c0f0340d40c00f0005142c00701c2d90000c05003143d0f020f400d0045001e540503204001800c139000080509080103100e450400e00c10411600c5a41c03038004c21181500c208025005072102c0020340d082d100031070b0030b003841c2099010350f0042207000c601c141c90460041803d507400b00b101a020400141210030f0303101c40380ea4036031b0001001454030300c1d246d08070034540101072041d203081803c440807811079240c0c45440e0304050b41082c8030a004222051158103100a0349180062414604620140c0b2078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 677173273 1250 677172023 677172037
    0x16060f0e061e061c11010e030d05040303081005180702160803091e011e0c060c081801151a040305060f150103090c03020904050715110c0a030206040e0a090b15011b08 73
    0xd400f0100d6403501d83d038007d42c003140240e50090281e640c50341062000600d16409400210042203e40010801c050b02c880007540544038080d04801c0e20502104288103180300080c803010440c4501c0c5010300c5003000205c0480000c1404a00139600c402440c0c00300020300310f800d015240c0209000c1c81540e420b0303034044030306880380c0c40c200300140c11305007415411504549403400103001c00e8180000c6012259110070000d10481307400703007100900321541da0b21074241ea590384210807003c54220402d0201c4e007580000341041024040056140c140d903036403802c1c2001002c548440d825984032042281541c0d20ba6034850fa11301003440d04205c10816507403042e26a0103d804040d000d0414800000c0820004003d80c01c0580400900310315845076500c4010892030355845ea40031180901d40b401c80031410100c22101c2900c7e40100814141810005042600d140042002c4e000940700d0707a4403004504c2d4840c034180582014480c1480c0c4000b003c2c009800804c1c40d5200c280c40b11001c40090303007c524200142c620f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 677174523 1250 677173273 677173283
    0x6020708011406060c0f011b0324090b0a0f0807030c0618140d060e010c120204140609031002031e0612070e09030405180a1116060f0e061e061c 63
    0x82c2e82104030034030301e001c007402c0c0001d44035883d08407852600c00040c0b0708d40e03c0e002900c1e43d043c4032240f0110800c1d010101c800d600103c2c108d0b6000024004a4a9034100c94040040909403444e200d03600da41007050444e1aa02001c110780144c5014410301440c0100b040141c0164185801001004684001c90305030364410410104140b05402c0503d51b2091680842560804801d102c10480641154004c0400082000c0400e84012041801c4011402a5011904120201428030120400384689903200c02c006035071500811b81c1018450b0760074405103014681c00c0306891002d48000c1c1c007a0200b0786025001c148540050916100c3d40000020000d0a075000b1821502c0d0740d440701c400385899400f440e0442617000c540c1c00a01d401e403d203400d14451003009160814451070a50301e51241c994414000c4901ca540c01405e801004554541c100080c07158035108000755034240e0340401c0d410304106031207400351008401d1a0281200980c0e41ca00d401003401c070f40512007039a44603040e010025617400c009113 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 677175773 1250 677174523 677174527
    0x1c030b04091406060102071203080a050c04030b07050c01110f090d0632070509010906050c24160e0f0906040204030f05031b16060c0c0f0f0602070801140606 69
    0x590300c4a402584810b40d009681c4814180c00d51011600e60908071103990040c410800000756000142c0036204140d601911000b0407a2140d0001501030007000700000c800590800c000000291a802c4191103000b80d81d640e25101c0c114000b0311402e45070350070f046000c501010b004c072002942000701141c0d2405021a41c038109030301c1d41d20308200940b0740032000d40070255601d86c455a032460b4400080324049a1980450450350310300c00b06031001d00414038a64005155248140022400f8070000e05d00506003508070344403401d0b04541d104071107030b841191a0880d4155024423010200c5c1c51006040001c80c1d0801e100c243c3c2c480004284088544003100d88104c154034046211511282c2c100c03009550003503100010b483c2035081850341e03580403d00b007041d15020407942c1049500003007299404221100a420070b080e140440803546441d41c120160b075810b4080c54001000d600d0200550020401203202c0001989480c00103800c0074800e41c8201107a034100f0f642c02d020804070654041d0f2186040740e0180d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 677177023 1250 677175773 677175791
    0x3060e060105040e0718090c200d0507060f060303030b030631030c0c0b0301051309030806040504050115061e09360603030c0b0c07020f121203040c030b07021c03 71
    0x1184132691503182041002502804150780d4188d03041aa0945656124140e00351818161040c03108034104d070745812500000942440c0d24428030003041200c5c0a10f13000724554420606000031180a0740c402c5001c81c1d5640720826142c2814400264026114000712282010201b8200c80301c0c81d0240807801d45142c0d014144040501a0980651076a000008030707040741c0c1c0b24100c1c00c00c00ea000380030740d030320841803c956000c541819000301d03540c180d8156a06080e0303480708418000680f40c06881141c9030b54179808441c0c880307a1080ca0b0100101400e13901c040d00c4291028140e040100e490a122040160301d5109010b00340d03400b44a005281e9507820140c005001c1c004054404020f801074910074542030480010034181e0201030300d02164080c204500c469113540c06a0f5030709115400e0000c3d017128580c00d05000514180d400c80c007140c01d0403802d44900b40c0541001210b96030046904468100a0003418414800100c4026510041e031740010031180c0300c408180044a40f00b61802ea08041e101c000c18 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 677178273 1250 677177023 677177027
    0x20901081612060e07021c0e090703020708070c0e070306032a0e07050715050105030a060b1309060f060f0308030a15090903050a020607050a12020315030a0c0603060e060105040e07 79
    0x22801d002e1040d00030045a51258281244824140e4441c4014445c00d14600d9000c11041c00c2d9842c03521554484810003203240d024440b2205c0024001c2080c198240702002c08220000001e0201c00c2c80b034a414210142003403104010710002510301001c0518010303060000171180c8400c050074002c0d802131107503400b500e541e58441d005440e40001d0300c003d061000740b01c0c015030010080d045a502c03c00b0f00c000c01e5841c2e4240481214024846c282d4503520034051071002ca0780551081c0844400a0078141b240281c1905040603607040c081c044890039a52880742903000a90700c2503901410780005204142803031611030300028000902800011941c54098000c40c0c001501803000070104000c0a002c18003050401400300d8000003800000350084500081c18240b00342c046981c04a1252500002d0102c030090100003500024085403041e595407104c6900f13a0382c20004100c01a1050385404015814044010103640c0c10748c0c4050001e07040070341030040c26a008029102550f42a40c08000342e80d864141c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 677179523 1250 677178273 677178287
    0x309040509010f140906061008012105010c020703020f040902030706050a02010f061d0f071215080703230601080a0f02041805100e0c0f190914060406090209010816 72
    0x100c115040ca032960030034000c09104c2419200d4035980082d03401a81c0c0b0301040c40350176207903101c600d000100c0c06001030018007a001280d10030318000105100000c02c0030b03550b40d421220000c0c04dd00150b40801e504004610b000c03900d04049a07400d840030702410207141c6c00b2a0761412540251400d10001113950841706100754000b070710b00311001c1803d100243c1d440c03010325001d20151114080e9180c1355000076000140854160b0b002d0403055481c602212210440e02005040302e0300390719013a02d00300e000001e00c808c040000c2006103020303080c40404200f030700401c1c020001c4000c11001342500075400400c00c0030404601405d4954000c4444950100c0f10720024004210650f800e54864200303880c410305011000a24002d080c01070302007007004544c0000030704d03a108080d56000c0d512410300310340700d04035003002508940d8910103210703810801e6031502002800d451310b210100c0078510340503080001519007401020020a01d41d18114504a00d840001b031010740d005049039160100074880044a92180074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 677180773 1250 677179523 677179541
    0x140d0b04060b010f0206040c060806030307080d0b01021c022d190b1302090109110c0a05030a0305010509040b1303140f09040509160e06130606030506130e030904050901 74
    0x452005903141a161440c0104410486140025902c40c9003840540c0001815801550006111110640381000499401c40011b00664041c007090155a00041c1d0314405060312040e54000400d1124a00c00024505901c00c1c0d0100045803000030422031454000c1120382c0048400c0c1e450700c8180103004420091503007124201c074002c7c440d01000440300452036007611540d500c142c80c100361a4446c05002d140d040791030f0320040d601180b600c00400501c8038551211200003050b0030400d0a101380140d155051184240c0240e07200d8000048407520a80e00d0b00c2a10b02401041b1f60314589400d0a0301c80d0031242038001c01e82550406442501c0f01072500501481500c1081106046c0d0360301e14010b00d44200b508192240e038012410100441c400041c04120b14030004070001d11060040e00c0c0400c86c4410a0002d0030480d04113030070303215104000195008200c040c00b8240c4001c1250304109050000701104012961210740c6031645440c241342010048854007581120b01098680351000703040c0c010001a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 677182023 1250 677180773 677180783
    0x14010e0604080105060406140307050613030c1e0902120a0b03070801151a0a050702332511040f060b0d0c0f05030405190305090904050705100216140d 66
    0x100740003400100540000388a5441034034180b00341c507a14000e058202a40b41e4010b9410340084c0c07800d0101d814013402a20071003031000c0302c003c980c0360b49848240c6079806d282c0080c84001601040145041d5401007688001d002c80c890451803c0c1c80003007280d2048501030445105c194403504501c096940800c44400540303041b40c0204010119240c1e440b25094152040b8440c042c4072070780c01a000b21600055542010701070300d80754900140e0383d08101814541482500c50b9190017400030210620b4a6003c00581068191042e07844080c815000c0045010340001c15003804294038840c002002500104800602540d010401d01d401810f000c01030300c01504203c94000c4080390020010490f9000014003c102c1e0311080d400400e60b84040300c0324070040300d010f8585d50018140a460b80d9440d8510249207000389080c4c0c0c10481150700144004100392019621035005160922481c0b038841651004a0600d00003007100c00301e01403005905442c248140030303602c4034202d4200ca803919a00261030001340c1c06 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 677183273 1250 677182023 677182027
    0x608190c03020d0e120409110d0203040b041416092003040807110d0f020616060e25081b01110a0305040609120206160203012318060403080114010e06 66
    0x990020025045038861000c2c03142410030b040d04004c0080f854079040721003686400d2409060070820006403c1d15450428100410841080818840e10145004034031460347c25010f801e150501140c94000040040040d400c4410070442e0206020081c008035600043c01280d18041c040030103c40b00c08880d04581c8000c0000100f00422140303d0003044250f00c10740706d00d180c900301c0d94148041180d079250f00a002082c981d4840c0c4c0989851000345c4140c4034103207101158140c1030317510381c010f54134030809000e078550000c112a840074090400d0042c4d900111070203200410303c0d040d43d9641e40c0b5400b000c140030040c40040b145d400c50340304052042d002c9003040c0403520b20050390702d00144550f2251207600300040303141d000440c0c201010822064038640080101e401c208841c03100b24072400084038220303450b40d601c50340c2100e079000d10860a0105a81c00c8230105a43c81c003201b00a10000180c24040c026802810401001941003610217040d6040504080c980074890001030b00c648800c031203030341d501400c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 677184523 1250 677183273 677183291
    0x2010c090b12070e0a1203210c020d0c0f0c120b01090209030c0d1a100303030b030a210e09090a05060c031006200105010b091c170d02040909030804031103040807060819 74
    0x44420000d04810328248c0c04260905440c103c21540e132030402d840160001b280c0d00100e140300e86000c03022540104445855281d16555580c0100403a5101080094120000200744080801c0c824014242c201c0150b00e00440040000e840b8803218455510030031415414a0500c4a07900750400031410001c00107a950408480141924050340f00440001e41090b41034222420b02194440c4000c2d8000e480059415085000802070b00c0034414840802c042e80304005c4080c0e60b43d2104070b0041c1a0b5074050580709040c0d041c00b504148006004e00c0c0c1c6440f0400c280444500742110310000c072225031801e07600340c0c8038a070b81c07124040d0801d02c0001c3ca158200000410200703410b000500000c1021600b0300d001c2d01c01c04484401d102a031803006400d04040440d02c001070030340500241041d1016110040c68581c6a00a240480d24900000d80009003080d00b007104154004003041c03800103001000310706040c644142c041d44c4040d81d0007168100690240818403458411104000c0b01c1c401034800e002c001e02d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 677185773 1250 677184523 677184527
    0x12019260702031c0503010e25030c110a080306120319020304060e0d020102060c03060d060603050c1c0809040f02071e0c17031b07120302010c090b12070e0a1203 71
    0x104000070b078400d010300c41000c01e89030690032489050b503a1179214a41160b103003410503014001c1c01400160461a8001c02e01c158402e0032900b1300142145441c0000c02007181100109000701e030030006540c56200030400f10100c0d6050060329809441142c0f0005c070b403018031108500b140103a402e483c0107540b08100301020300b50040040c1041ea20346565890640814804106026111070b0020380560001404544d0300441040115881b06016141c0c0b215412103554400850310030307600c2610103400120000005161076070204d141c2c00b640c0c492640410645448030101440341c2c42d126880b5664406d0009108103003038040e41c0c8240e8100d52422201c810010100f0941140c20710115880343e00c3ca0700104a0042d02000541e00d1200a0021070400000320307408a00304c1c81402050645115a850015150b5a005007590000f4825800030a8141401101502d684600d8028410a8205004c006803030800d418456030b00c0122450310148000c0307a4000328103190313500c0c1c01100c241c0c1c041c1a0303800141070b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 677187023 1250 677185773 677185777
    0x4030b0613060b09010804020109081222051005030402030c06160c170c010305090f010c090807060f0c03080601110d17060906010e280603050601201926 67
    0x104041d01c0c1402074448141c03108040715524020600300c0e190038880c910080d40305d000c80030f030f00c28410f0601c0c1620b6600ca40c8074034502008449005480304000074020700c1d8011402c584100e2200d00044c045445082c60002001c9041201d42d0100b0044040002405c0d90303001c100c4055140405050981e841c0c142039081c440c0205241402d03541ea00354550001004101c00b04222007104112000d0940c0c82da862004402815019000c1e44403882003e0200d04d41c000203129202c5058004d4442d03c86003480e081d80c072818a0348a90281e01404140b04000e403495801c001d108941c0d80c0c0c185080d048a688880c01a02c00c0120b2a18485040c0304001908031002d801581402c5010300c89800300440da039402c0c0400950341d41c00c49505000070351b58091800c590078641000700501d0342c8070004c602c9040b1440c0c1c40100c004013550041d8000394844084c8107940d40c00640300e41030403510401d42a91007034810000c6a454030003207000c0c6010b070035407600c00082c03240c02402118244045401c081000303000d29640c0b0241e03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 677188273 1250 677187023 677187031
    0x302040302010e090c0306040b1302031e0c09060703030f02190806040f05150103381c050d08090709020403050303040c1e0e0a1b20031e09010201090804030b 69
    0x8514403c8002c103191a10101481c403407005014200e00d035036070718070520014054047e14280c004c56261850030035030031240091841a4689400e40e41400c03000c00031200440009044148400c81c1000b05080035180d5030202ca0074581c041c1400b003618a0821400c100900c03030102039460082041400c0203806034400e46490280c402100c0038000828000782c0101280c905661000d90b480740c3c05146822540240c01800381041c0c0044002c0b8500030143c441120041c02c84442e242058111218592501e070028a110b00b0301001c52094050341c66955403540c0d0707440000312000c20f001045000aa408400b08510b0b001f815803003a0554407599a864000d95903001614226506aa0048003044846245490010891900803104045440d0a14140805901a120840302a1244441c000203100380c50021514030341643c030141030f012004001503004c5101507000d0403681040080000b90072044070100341c2e40c4186590f070390780c9044500041c1d0043c4805035000304021004a800010300001b804030f1403103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 677189523 1250 677188273 677188277
    0x30507021203030a141f15140403080c120c150402131401090f020f04150903140303061504150e060c01053904090e0f071511070b0304260a030204030201 67
    0x110ba2a070f92025150b0358002c0500d050206180c07441008a0f9a0f08071141e20720007d2814621b181508400120350f184d84160000d9501d5000000c0d960113031001000000390b071680e50000d0508042d80030074a0350b100c078800981d000168003000d02040a56840c0f940748200351034841810480503899041c00b4100c04000d2083c8140c0c640b6049078904680e0144c022510021200344402d031405040c1045010710050711201c1c074003082522540480000c0740e510034400c0d400d00381030095807280392120030002c4420342d90500110217842407204004d0b054003c500d41060030070b541000c80100341070a0106150f030084240e840c0603503003042c0c24030002c02d1061204010444604018482010030548618282140140141c140301010032042000c0074559001010307451240d07086d200180e81840c2500d2400119800060364034291400d135201c12030300160354043d040c044001911020f4039150001869020040000d082c5520321001c084070482450416110501403000250316040c03101001002500b02e804100c0c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 677190773 1250 677189523 677189561
    0x2010e01050f04170c010209030a241109010e1f1718030a0c051c0801090b040e06010b0c030d090c0f08060603060a0e0a02030304030f1716030507021203030a 69
    0x40694030b018050380314580180501c542d098642c40c041c86250b00503c1c003601e15541c01d07c20007074035a42c2401541c58143c09100c410341c14980c0f02c00201c901c403e0103004c0301190707403400a400c52a8683c0d0790a4681504090030f20404658100d00800d2490769041e40e50507078501040155200b072904184415004100048440d17500c0d0340d079603070340040c00c1a07607502001154000d0081240c40c0c1d100d607480108482c85002600c00e40ba081500e00b405021150142e0008900d1000040c0951000c40c410f0000390001201c05000800c80324021a4a071a810300a0182d81340c0002001ca03450302d000c000b142c501e100e1112003000303002c1650400d0502c15000e0700481d041101c0807100007862441c0000e40500516000b00039100945810600c2c100401e108409107200380a0f801d0f60a015990500c041c0000314003d0811a100c002103140c4000c02500609d0a9102c1402c10301108107a943c0c4444075014040e4981000da0350740f1510300006151440d22221170011707200010070841498a95044aa042508005000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 677192023 1250 677190773 677190781
    0x140901090b130809091005061c0b041e050408040b040b090f101e18080c0f0909070b09180403050c0f0705010e061804150806060a06091203021c02010e0105 68
    0x311800070b100040c0c900501801014201d00d0148011078020700b49a544690190783c900101d11150058507400526072000040708802111342e0160b4003005204030303070070400001550b801d07041418113804440b26407030780c500c0000e04000c000c20450f40584408030030243c485070b0315148045030741d200d01d82c40707805404501c0c40c40e40c0e13505100c03032040e1151140b52140900107800305440c200790410f44000008015599030101a40d0000c24040b40140c86024080c1c2940c003016410f02c20b12464004a00d8007900034039013046141c1e5000300704201550b0482c0082551581c030980001c0c00c0211942a40e807103110030030181b1040603088001800d03403559510555103c20302c110003060b110101889081d010a5a4460780c907070b541f5000c130080130001c403411081c40c0410b51040118007255415500d020f000c01d00641c0500242c2000c004140c1c1c001c00c100c0d02c154100c2c0c10600024039000c41c9224101c0e40700da04440b0001014000d01c4090511a01540310000e110140d440003400307040c140c0e1205113654607000220b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 677193273 1250 677192023 677192041
    0xb120a061409070302031e09070f1a04050d15020d0b010e10050d0f090501050c030603120901090b0a03020909040b060a1410050714100218041b12140901090b 69
    0x6491240c001415002d041d0b86002d0160040e500040040e9990003500300d154264107003c6036410300034080e0000030010760703080150f00211010150405184190f04112903006182010115400e60310300744c0e41a0004030352844c2020070307403a054503040c503854004a0024000501503000c448803806c2640c85030032a2507010140304903200300d00c0d06000041c800f0070840c5c218440c61340060250200d030700070004030120640c96039800c40e42d0035922044170302e03c0041402464030b42002041d8211600541803860403800c100044d0088086220741c1411510100c0d030050303000c0c080d60540360056005020101e5a00c0d0070b03d04480c40074007c5506521a44206501141d28503154241004044028250441051314176000b0354031074018001c21540808905003c1a40001c28413203841104000513016884031000c4486001000b40c40c1d14003030040d1f28081c000329407031904141164054110741800d92000c2400300c8064041c0200c00784840031550a4000c4c01100c00055018526203070084002c03284a440d81c0c000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 677194523 1250 677193273 677193299
    0x905060a051c060b220e010b090708072d180603020c06060d0507080715030506040509060f1f1811120a150312021e2d0102040b120a06 59
    0x4501101e125080942000a100307a0003011602e10041c1401004508404011222079407444045d0201d074403060110b900c62002d0065a104820454545041c0d01d072082d0700500004000b0982e00400c0410840c020715580f904d0f00d0400c103413000115851007940e1401c0050541400c02c81070400d483c401c12000580680300c3d109860454606401811164540e2401c105560250fa18281d8013401008c400042c15002004030b50014950b1071881d410050480001800b150700080540c5d0003a4104020840c00301c0000c269503a0001c5074a00b6900180c94505030450b41d10250502016004c803034403004545140d0110424040e2484198144030303507101030b04104c03460b025500710900d04ea41c040001c28007180168006094007000030344054101a606e0311402141c92244020303001581000c08400b40318040b4002030100300341260b0040c2840d08444551629021030a0000c18403010501035600810100b9011900288031400405840701512a00f60745c004c401a227003002c4c1285408800210b00307902c041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 677195773 1250 677194523 677194549
    0x7061d07080d0518090f010905100e060d03121d2505100c0507031a07020c01020d031a06030108060106020609010504050a060203040303200324030a06091403040905060a05 75
    0x1018059100b031001040d186500480c0381c0241403c601a084551910b07076002003407003070409402c00c0c40c4651500c00000101c9001030070320f03002810120b0040c07203c0c02d00c10f850a5040801658a0300307811005e41411500c00c80c2d482a042041c40c2000c0c074090301c118544840d454072248030001c1d40c82000e050b610690402da29a0185c1c802c405011008001502c0c01d401c3d410b000f4441c03030a166031880d41c07079601c0c0ca06100c810b070021a000503581140811860144031442c0d400403040c001803040000000000c2d50321038010150000b01034680c0103580e4055030014102040d00c074090300031901d95071075440780d0741c488109000300320041c8100c4002455100050044502807600240541328101940d140c210180d070008205409040d150b011200220b44400603100c9040250203045869017005000030420343e83c0300c2c8810072001603983c800d41c0c10340c1c2c01150509aa03507010200003182c0c0e01ca4a0204000d0b000c038102d05445000101e0002540d103a650070480c4034807811540c4d0740140e40c0b40c20170022901c203411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 677197023 1250 677195773 677195789
    0x60203180c1509120313180915050a020c0111190c0f03051e030a1401050103091e0c03082205010c1221020c0c09070c15020f070807061d07 61
    0x940120401d06040051403042e4001c0c0c400520750303042da1032003483c40d803181c51001520207070071074204640040c0850000c9401e070080c909108d4010a52074030441b051301d0850401c1500c1d59030001c524900076640c11507010414000c024400c400d4400c100b00e0041d00b010420100042e000b1114610062148007141c0c401c13a072240c403c2c025071045884c111b03680d4006042c0d14502550701c650135002182e8010142d44181c40b4214045143c07404080c102000e08410792005040c141081036171400940c20140524074103100c0c8080c2e00840c543c1d42000ba01c120080d41c40a000a1000035962000118100e903c8188400c404911000550b40c0c0c40116510511200b014001c0c840c400f0a110b000c1d0700c107229640410718448049910100d4604003e42242e0240750004860b520128101c41c01d800c0c0307400d94030341c460070606240082d5191911124503e03040d0000c0540f10a900103200400000d0340c4c0c05440b49943c00c0040641c0300c2c81540b034600d0043c09503d003407e40804210f5074181c501140003483d441520540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 677198273 1250 677197023 677197039
    0x105130504020d110a090e030a030617100b04020910170c04150c110a090c140c0d080403120f0b011706030d0e03190c0f060c0c1401050d09060203180c 66
    0x141c0c84444500344d0402006601405104000405030040e0082e0a42c11144802555a8402c1240082c04440c02644150400076140070098040320000c910048240315611001c030b000071f203580c0010000e21031040426031103112101040001c41c0d01c403e46086d0295a000e0341130007900e800f002200789000c5c500c03451f4100384250031100030181c451001c3c2c100c118400d62980c01512242070000350003549640089858580c0c6000c075289040d804080c003030f8050315440305c580c44c00300c0c0b82458030703181e007190145402803086103008603040620940f649045984014020404c101001c80700c0c0024060010310503000880018100311508000580103014202c010300405101055031416034919400e902034983c1405500700d80031020f1100d0f620354100d284600c00fa00d0141d030070b04040020040c4d40713410a20410205603c0040080d05030760301c003425200c41c0c0d02540400b010a00c0105e0f400d1241d845400c2c030450074092840d080007202d030061070044010108443c2102107050050b0f94a00324220000e0340440a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 677199523 1250 677198273 677198299
    0x30c010e070f32191410110d0c03050c070906030b07021f15120f0b07090b070318080115030512130b0c03090603160207050108160305061f08010513050402 68
    0x1111492103040c0000380000103003660a02c800d050307111007903000c1d2442c10017090440c10140352903495151482c4007405c3c14051a10421a00d617503a500442010042c030848041c51400d0600800c00e0b1408900202c0440c0c011548403010403002e491244001c440c89400035000c42c40719400070890007080c1562410514050340125083c00103880d0668070640301c046040c4010940ca13040d0702c0c008014078040c0301e40d041c0d150110b2900c8414500000c0c03111081202c2c49000b8408400c14604a0703611380d0300751510402c4031482442000155036540e001040e95032038280400d4544000f4001002124090000d070b0b0200c6690f00740400c4140308030750091100f60203648c003d01032100c03007c0241041070109000c990500c41101c000c01c055070700656114044404c01c0141408060381080600c2c007524081c68100d0342801c10211845071562020600d1043c1074482c00010a07589500304101d07541c04170191700f019aa044600302030011902170160a0040380014a002007074009801003600495001c2c01a00c1e604031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 677200773 1250 677199523 677199599
    0x51605060316090f0605210103083009010911061c0203090102040b0705030c06010602010c1e020c03010c030c03180308040b100b0415180f060c0302030c010e070f 71
    0x8407200d0381c2c0080c00a0880040f40000034000040043c01036900c071503985842c0c580540c1e41d01c4000f1100004150700400060000822040545d03410001c0b440c03442c0040c0888000b4450b2582d029140380303400c50882020084031600540144080a0050000d1250142d0940900045110354841c1c00c0010603021404120064903070300035507001280100040c01d25448070009400340d401454162500c0c0d00c0411050b445807814405a801458140003c10003241e0000e000382441c50700101685415141801e0300c2c514500034010701c00305e0344e0001c0c020401400c100c0720107002021000380510009151030001c590b5032011060f64620940c00d034440d440156aa6596401c00890003094051200c0c010100041da1a208202500241c030010308001c43d40c00c26050000c101260040340a42201c00000c420407010b184981c0980a90f1007524000c0b0440d10b060070280c0c60b504c2018144a020341c038011911002d8038000c100402038800180c0762002c01503a40200018940440c80900d03085500400541c441c16 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 677202023 1250 677200773 677200801
    0xe0306060906100e04020a030c0909020715020307170a06140303040302031506011b0305040303030f05190b060f0c0601031a07080c0a0905030a0312150605180d0219030516050603 78
    0x1e4801c0c50821404c1061001080c180d80000000c807022a49030344585400c2604141c042d07000d0080c01d4400c60800303d4603190f032080d990403511843da00302d900001145216204003801d01d100701d0349140d01e4503a03050501095000f44101d12801805041f00b081c0c290340c1e407501104542c100da80040003800444018480c0c2140c2c8100074041d5414000c1c2070320b420b00402040001c81410034000e40b603068603145036080240071380d1110407000500310700d8101042002500700f03a00717511460306248000f4061000303034040f90980c403a01031200c1c041713003000c03840d4101104001030f882d045ea40300b0a0054004080072481d440c086400b6074284010400d40f02c001001010150064030003210f084c42c052280e1591000442d052404c40c4800350001001c0008403400d2880a000b240c94040801d10f00f1315071036282a500401c54003400b0708408203030003002c0700c224040e03450200b140c0c241340e0002c0030101c80443c45680b407011115144812141800b4034009149410480c0f03a04000300d500c06800c01e4034655888019120b18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 677203273 1250 677202023 677202049
    0x30703080909150907120b10051905040f2402030703200307060e030c0c10020304031b150207090e070f180f0c0c060605060c03070b1012030c030e0306060906 69
    0x440c1c03d1030180302d07914a40154041c1c080ca44611000503010340045050301c45840c11140a07854034a01440d8082e0700c40c04880404c4c00251541c000001300420444540c0302c0c0f0380c404004400007141c04290f07003c000140b00c4140324149140e036640d01080c1c005984034042c0003005000300e8120350343c01c40120400c0070720581282001040d00d1070140c650356444119002003406401d25130000c00c26103540d00041010146803001100c118110901c4504029628416800001d0200140c50b081c403200000c40f01e1020080d00c8400b500c60012035036660b00a40c4d4070320342e1260704009400c1c2100c020030480d01103a1102503e180e40d50090003941486008643d000205a401d9806551850b401c0c001e41e00c544a80000e036203084d5203c0c14042094107214085d2502c5811017449060208002040540000216a03100760302c0a034100302c595420000c041000402d80c45004400d0074100210100342e0f0102c6038a0099210303858898000c1c0004042c5540c51008841c040d0708544d0f5480820f0b000c1c50800705c0a400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 677204523 1250 677203273 677203291
    0xb04060609090804030b07022a03160312021b0609010c03020c09040309140919050924220c031e060e0312070f08041b051008060f030703080909 63
    0x20150744912000444100c00c0040d6207032000410140100040c040d03090b078004c8054801800700c1c034400b00200910344800c041698040803102d50b0743e41c1c41e4606101541c0080c040c0d512101c4460341c5c0381842c403c0385d10103035480c2c001070040d50a482030b908103a024000700d85101a00c1d450405056a006503002c5c00300000a034250702c00d2a041841d6070303880034141c9100742d100e5580e84510034940500b0003c0c0c0582c821000d48500c1095040009a081c4100340c5080812003190205164481808807820034040310060807005e00d103040c0b007203415908036a09600584440600e400801900c1c0480ea038140c20f87c01000700414a80881013011421001e0610a5040d040702903081450003541ca9000b1181740c0943d100d47e030380011602e000e480c0b480308400d91740659a81803407622084112402407620b00d0040c0000c00301307171801304000010301d004010007015090140283c40c3d010300c040310140800000319540c41c40f4100b080c000300310a0901098110417a9805981c0380c0c200440401040504d01000b07010307281d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 677205773 1250 677204523 677204531
    0x408060c030121112707020a030c23100203091b1f0e0307060c021c02010c0f03031b08092b050304020f0406180e0a0b01091d060a0e010b040c08040b0406 67
    0x1006503a81c024510020320417262001111000340f4024400c10f100600080a5420110205000ca50000015114903600c0303203500030f5441040342941400303414101c420909100d80800c64501010355402940600d4130340d400c88410680d01e0780004000f40b005202980c00c00d9622200c6001d04020721165000c0c444e1508065a0208a010210780740041d90b900c0900050001481582581400e50314054907074001d230b044400561490700064071184400b9001400c0d0710b00d03110640f0070b0500c40d0740710584001d144800e4600c00302c42d0540c02840c1c40c20a44107015203008210b0703104100da10310801e819074204044003c0c0494402200d0a85d92500000c00aa812244035482e25103155200c0c460394000c0d1030152081101500c502c00d620046035042c101d10540c9600c0484550041050322002e18116503038040b010400f90100e541018408100c1242c0181d540b0402c02400380c43c0c0b050790440c400d00340f5420000c0022565500400042e038080d0a1380c21301290b00c4c000810080b07208a9212030f409030240da0041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 677207023 1250 677205773 677205803
    0x1806130803270106140d0506010e0a02070b040b25080c0c160e07090f18020c0109050105090f011a0604060c02240403060b03030c15060111030f0408060c030121 70
    0x3101d42c840c81e200240480c0d40d07401c4284a4808250408285010103403402a044c058036a24686e986206000b882c0f000c8124000103507114446404450003107501541f02485400c05203400d03c5610f0060b00c610f00e40c010a00384900b0403c29010700944000d02c5991140b900340c8800c802c0050075840a148180319015840a00c0c0d025110200128020144c214840089180002c1c6c02082401c01d9044031689921524080021104a01e0100b07036508502c1c0740180c0d01c100320100c0a005100d070080041c215404e24041001d1104003050090805403054020300440d402540d1076030000c45070460969001105001c10310010380303d012810101440603041224103041c903d0428182c880500c02c1130f60000c0001000d10821900d8024800001070a034021030070015000c0d2800d48440009801035200f0030980e0000380c0c268440c500c1c0007013041e280e5044e20f54489000005020300d62043c000c800240c801c080100d152408008201ea0480e101078080c0583e04004560014500311041401d541c0b60400c51012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 677208273 1250 677207023 677207071
    0xb091b0120010e0706140c0318060d0c02010903081006090b03070201021308030304021003060302060d09150609050609060f062d040b09030d03060b180a080a03081806130803 76
    0x104001c20908000b0008103141c508002c11b90f210040d5642000322003407040f2044a5030000644081c00d016006914404500d100807c41b0350107114001e8201500382001c2941a94041d800f9055060203a03546135115a146406241565802c0c416a000980c00c40c1003007203124041c0b0040e6421200d14030000d072500c1060ba00705110081c144c1c2241d0221b4000005100c00c6203030054003d190300d1418203081c4106882c0d9000988103006000c10000d405880341c403a0410032404c064120610140316004018494540441000803d02180d001d03014000950120b1241c1c0391a500345226050010f014070319066000400110010600904150049064604034041040c01c03028001070030075001100d0301c0d54003510815160400b480624002d1514141042c0035000d400c00485506090801180005038210700200701e008209911100307641c02211081d408041d03100114500850301d44081d0b0342048002130f0410788031401038078060444907210846400040c40040910f42c042002119699006520300017 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 677209523 1250 677208273 677208281
    0x612040f12090608010503070e0703022a012702031915060303050309011d030405010c05100212101d0f1509280504020a03020d0f08040f030b091b012001 67
    0x10001c00d0140c10140300f0240d00c0301c401030050404600030156946840406504500040c160b81c041680005e8411101d01c100c000c000162003880406981000b041800c0d203000b41603810000f800f41000c10442c1c80424400926130b005150010003504200029141780800e203030f00058111940f0b80008080c00002c52036114010086019803282c6681c0d14044c0b10303071800c6410450408030344940226004055031000000d903815580d082c2449140004203043ca0740ca00010301451400c0c2c10700000d074161010b003054280c0c0380200c80380c0c0380b040071031900c0d455080114944c03945041d00215801c4001a203010007080d61581080d69005002c00c40700480000c100b0034a000c807850000f005040482c03401400c80c0711501022415440020040b6081660010f00031204506c1301034420300c4981120720a12840980481c41c40741d01c0002560b81d561348a8005220302e4051105880c6d010700103001904070031010a509600f40314031120035517000000c03401035805505205d41052244107290200c403052400b445 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 677210773 1250 677209523 677209553
    0xa1808031204110d0b0402151312050c010203120a18061a011806050d0c1b0c0504060504093302130f080f070303080606071211010c08060612040f 64
    0x190354031052810703091543c4050b01c0a00302a0040032008030307440104212440040c0c020354112031413a18203000e050341d80028085c148102c4c200094090700050844007600c468107200c0c0c860b5060b03a00b099640380043e81c49004c0d201903032480c15841c0380010350360841d560100b01708901d40103440d4003448140c0c0b00c0c036048031495540e80811b040103040041156822a41c041802e60300b0a000c250280c0c107080f030081044c0685127040c4441d0342c4420070080c1050003108070a04001074500700c41d02c09410303800c164074110784a02c5014095071801c00d004c0b6142c1880d001c0e490700e498103c19082c98100c1d0b850904140c0e2580c0350750441e074411a07500c40d100304005500043c01c6102e0b0f800c032041c4003079040c0001011400c009502c806201da00800b0960518180850210100c030f425003881c003503582c0c400021440c02d2040c0302c001490b140d00d0542034103015400035086002229014009c00402d008041d007960f02c2c0f4410750315140d20400a100c80c042304101072800d598018450b0b00200001c410b55541c00b25114103c107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 677212023 1250 677210773 677210797
    0xd0c020309010305011e030602070f120c150203010e1909020405150f04090b16090b030a0603030807030c0905150702090c0918070f030e0a021207090c140a180803 71
    0x8511101c1d42c0c0c10302070b84e8003418046000c0482c0306400240400c1058903484014500e98004c90030005104050110030702c0c5035000442e0031060345020340c00500d900b030f034035000b1503040e07000c100400c009058a1090301e0503074010311889050b9803581c0c074810400e1001c2c07400c01c0c01d101c0e45844013803005890300e0140394002d5140d52041150241d0090800c8980640b4021581c000c03403918400700c0206e58011002904403a450010440d4060280710444224116402c00c0542441c000144401d91145a00c0601228080d59a02c01651502c03d01102030301c181c045404000752040e4000c0c08203161500c40b5400a80503420258500079442d07010580440c42110001c1001802103500030312410300c00c07001c904448140968010520b8200e80140028203045e500200b0075546000d2810300001c1080120f0655030010203840084507181400d90b42c914041c001c403010581408107007401e40307000f142c24a0003051500806418100301c2076041341d45503013115680e4581c0e200c00c800095204010320081102602c2d403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 677213273 1250 677212023 677212027
    0x21020607020c01030911091905010612050114010c1b05030a05100b0621180a060c0905010903081c020412081801081302011d030708210703091503020d0c0203 69
    0x4140107414001e41c800054145805d000c0c108001540e49001042e00b20003c45441c0c0349031b1941d00e00c400d460b03045441c80e80c0c074075481c00300003181d0300360070400f02603624100e5101888103a80300c1c0ca10b010400000700e140b601003004500684000307a00504904809010748004100103035480000034a03002941c0400d58081d0020941e10407242c10034015803090110642d001032030914111079020040b28000d00030001c041e13920000c6000704165591f0103441c894528215070888060b03080800c02400202c84c00408a482d40e0b20004055000e502903030100d941143e03100c0e051440c0041c65102038640f00d02510441e0350f0800001c241700812150803100b442c050b4103070a45900c2403203600310a01d60350f03402581c184100070040081a0050f0400c44044035030a2030101d9030b21402402550710392600b0303808030350b2501a04002203003a060000350f041a114030005003400000e4080c400303200620807454090f000a00b4140284015551003881e8110364a645c0340041c030341240003600100b1100c0d203403010b200507080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 677214523 1250 677213273 677213281
    0x81909030504050a09050f16020a06050a1e0c0507020d021503070f020c030307021f0c080f180d1e08130b0d05060a050625050304090c02060c0405010c020d210206 71
    0x10280304d02000e0403441008100e217082c03800c02401d281000504d00d405580000740e400031018800d1000b2940144c1c888401d03c01800d000c00c0c2c0c5009416940030302041d000b144600e0000d46200c0c1d00400901940e50389803d4a45506074007401031504403c0f40981e080218442805a05c5e000140118400c55482d52012000c944040c0001d00340301040d000c1c41e11a078000d003c02009a41c40c4402c520a8202c0c540d6a030091820449058420400c1d469000e00b11a00100d0101210700c0380100400c01105c880382c40080001c0c2c0c10040040044544a0160213401910103606241c4010104188880d010300d0324281401110454007400d500300ea0064128203c001c502c20700250158010260440011224806038034100000b041c96400350b0007540c19a01081526010000008402d8030102500141901d58464441100c0d001a24044600d00018400d01c80001c0c0d0503034025083c6c41c15210142d441212040043c4c0800090034011041034600b0031001e80d800c00c05011440003521340c003825070090026490 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 677215773 1250 677214523 677214529
    0x6030a090c0801050f010603021b010606091806210305041a09120d32070b01050f2707051c0e161404020c0c0d0c0905010f030f0308190903050405 64
    0x22036644400315a84c14034090101884040d0311a5043d190b0500e001a01d46106c907032038456919242942800329403901c2070220702e007a400200c0720240d0b43c59250a1102411001e10320b01103550b40d2140041c205c0034848111440348558803c441c40501074a440c90401d40c4070304a2011100401c4110710641c00001340740041403c3c0a0320700781460700c01c400900401a6058006010107a071001c1410411341c881900e500280144d550030286424010701d1107484502c0ca291012500c002070245038490a02e0f4440c24920385041d26001c140d20b0503043d0311011000c2c042403103052034040608800c040c02014001100716540e108100510344120700000300303144440b0502e490810380e020540001c040c0341e101c01403010342000104200c042a080d100181e0310030100250724181050101032a03400b03618440220f090001681d010000d8966004080056980e0349002d40804402407100521290f81e25100360081780c0145201396000c90b03440300351052182d0034000340d011125407160850100c1ca010805010600b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 677217023 1250 677215773 677215793
    0x8030a020310090203010806150301061206020c0712050d0c0201050912030a0305010503061006181707170a2f0402030c1c0239010f02030618151302070206030a09 71
    0x18a100c4218a19410f000a007501c402340180b01c41c01c0d085d804107000e4403d4400b54410001402a20030a1510100d40d203001c0001c0c1d8096a00c40307186109118021804d0b400c4144084003503548017004250388118144203031880034620f501641403010a00c0007140c035448002000581455480c0036555070018001e000d0125041a00024020b51150041010b2a050f40c0b184005940c0345090002e0324050651240c0d1420186810060762100243d05d6000601e030001500b5080c0c41d0b5050f03d1403405004900c05550301c5278840f502408002000300d44014610a8010242c074401442c4400c04c0fa0307a800d100401c0c2070303030b2041d10540e041813000100e180c01014110f0781c030080e1020b26807095103054060b9503058080c2c122940800341c43d5a407500d004689401089034500c40c21b02c030000038070141c0c81e0714800720002d4000b2150341d40901250460356103509410001325115001a81125802600da90140070201c00340e607000c0fa441c0e65080007680007680e18400610311a00d2582c038042101c0703095142c16074440e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 677218273 1250 677217023 677217029
    0x1b0f2101110a09080d0e1c05011d15010b0703080c300a0b09011409060105070c0311010e0105030702060a020c0708060405031e030108031606020405120a02011425030c08030a020310 79
    0x1c50012614103d5503620301d190400c7c0421140d000c428004642011401003d069050040c42c101481303510510345004941b0880751101120729031002ea07079944407140140f0980360001c000465000001d4032070040600500010600362004052000e1103031410707400d01848050502c0000245010004606004d00070048202015580c000c2a545003641c40300700c0026110800303116407881c0002034000e07440740d0156901290010241042c0f1070703603810881c0201f8a0103403141d0014600c05468860743d405602203074050b070950750040c10315640701200c020094000c040d05d000c0301d00450a0018080a00b0041c0d030b4004c0c0d0190003d19a51210484d03094018140250740c00107049090004014900e408401e6031050000111810010305017440c00c0c0000b80303d80c1e04002c0c6e004840307401c81d03840110b00054451410b80b007a210b003006108010441c1409005100280080d0940082e044040324903070407440803090300c03078100a550b42c3c0c0196102003080e081100d12612190780801006a9100d1040c140001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 677219523 1250 677218273 677218277
    0x120204020d4208150a240602011415010c02011110060905060d08190c0c06030b010e010206060a050111160602031305150d020309070905091b0f2101110a09080d 70
    0x190b42c07408420548400704401800b001010700d6000a44010b060381040c0ca030101d220803850000010910310f42c10f40c8030180105801586003503a0b0341d40c5882d04044403402104092680d00b098841400111a5003640c1e03401281080400d9000e400600400c2000701c01c0c1400d181c0c03001c18580e04280410044400050869208003d5908080081803c09041304d002c03c00000c1013500c0b0b020074041c160785000c04007030002e02000500000249150f810b5001d1030079000309907180f8446000f19001241d441605803840c179444540b61030200804e6000340b00d003030000341c00c000540307144c1c10655a05068024807540700c0400b5800009680307108412040c01d481c0603002c12650003002c05c0c8503401d202c040e400744000e040296680000400c8001404100c0d1400412014130140b2041c03610300c00d0f6a840b280c642c441e5034680c0f00710152580c01854882d00300e0312101009070900c1d402f0040782103111b40f035014010b0800c010307541c0c0700003176250318040c103004040301031480d142d03130b08454901342c0305620340303103441c0c5081e41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 677220773 1250 677219523 677219651
    0x9060d03050a050a09050a180f0902060301091805030c0105010509100e0c0304060e0601091d070b0a1b0f0c0513020a08010b0a0e0307030606031b120204020d 69
    0x10000e40c0100640e0701c040e1043c40c209890300101207040c0c03841070841d00000c0d408500c3c6007000403103d50760510b41700b4881c4c80d21030500000c10a85c000000340c030210b03540250b00103000c0c0014003c9042581c00310700a00901c035040040c6440076200c0608651000b00342200e1651100c00506c245d080c940425904200700710303100d640e12807a1050702451050040c244898121001000c5410b000c60b0f1382096016200e10310903150385507500c512810040c02e181171400104601040b00c0f0014400104811046a0924080e40d250801c200c0084410485079242c5171442034900300e10b030f004540707015070603141039209403800740380141004100300720b603840d520030212080d004003c072045207a4451046411500c100c10f10503101c1c5040c15041d107200c03070012003154040c440c15000100b44913082c6c005108990040945a1480558582d40c003601c542034042c1e640d0b51080400c11400505269000f080c004002d408000703540d40000744054140d00e45030300703043d035402013031450380340989250016100082103401180d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 677222023 1250 677220773 677220799
    0x11060c1006140906121924060801050601090302090606070204150e0105011707021914030a0e120106030807111305010801020a020f0105090c04201c0c03050712050604091e020906 78
    0x5076882100740615800060106d18050030000c2e140e5003007041d82000d0600c1c0d20702c10b20641d00320004021500c62040503600f446d012480c69409420004140c03038002d4070301d40c02640e074a021f100c00c2da44460000c0f0b030840e42d5920084440d05d0002010382c0680390019002d84603516010006103200085504412646100e00511403119000281e00000c0342c00c1d48443c1d80d1180d46030401035154410046a02c80901000441d182c0582d07210345845000002210314400700090100308a08a40203400000c1c441c070030401c541c0d80494003689032104802e800a01c845001ea0b1402101c2040ea0070a9100d07103d00d0b9000b2031011103803901400111139100005008022a280800b000740c2d40e4130654880a018030703921700e0203541002440745401c0f0ba1240c0e0007002c60365150600901681c37a03500d81011000c40c0d29089602c00d910788203016050040b10503a50b14601d100d10b28000c64000c0202070a0349e984682e80c3c3c0700100000d00c9803001801c02007031a040000002c195801071024040c1c00500191043c00303a01204c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 677223273 1250 677222023 677222059
    0x10305061f1401030e0115050a0807030c1a09060a09030212010524190305030705060c0a02060606090111011104051009080607030203090a0f060603170711060c1006140906 75
    0x1070125441641100a40e1003404010390080080d40031100b500e508120510080d91414480d21084440545841694907503070390100b03448030a01d0000074a51a100581000503000ca5419580a800311065040c6080601d600140c0998091001280420403803c000c005501c1c00401c13420856244000078070051419880160141e690020380c00c1001c284a10600341035114800700f2401c4070940c411b08141d56440e81060303540c0760000c500484442c810900042d604020070740a940c992072281d001040300b5110b100402c041c64001a030041d0422800710300340b4170181000d0280800e8100019569503440b82040709110303164a0010b110418880300710400c00003400002080d5501c174503140380058494480000c1c8070300f022140c1c3c0d0b02902031501d200114081c010740754401411244600b48507425440d0100c2c1c0114940502d52020344a034040c01140e641074200740004050401e811400e0740c02c4e0440c1c19011804440498114800d50b1010160307061541c101a1080fa41012084800506a01c85154a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 677224523 1250 677223273 677223331
    0x6071103070f1209050405130228031511030712060b0a0503061c02030609010f050a050618070e10031508120d180b09010e06010509190b031c050301030506 68
    0x30007840c43c0010385008001a20418462015040061041c030690600b4510213500f05c89402e0181d1242d03030b040307042800e6400705800f00000c1090501c0391031202c5203135031148081d800382281d441e80c0f9544c43e80220791a121800300118411400c603224004141100142c0c030003120b0703542c0c01c20403505c2003c0060a101c1030f000030a4a50101044400d040004185640340340c0f05022088002c0d0184100403d00c0131105040d040000d1a00700054100003960790014502c058500507501903810203102d50483c0451151036814980c0301d00541003454801050b400454903003940c4103c01000203645102c202181c0940e030300ba51005103a604000d1010704600441c500a510074140281800c0399150019007602c0e08a54001401c581c0100f08401540340c2001c2060103003130702004604150140d0f0002007040c2c640075010034060203090b07445105c4c00742c00d40d003010010414112403907898030448540850400c0c0c801107680c005480c41d41d51648a524500d4101d1401c20301804400c08448082142000e4825240e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 677225773 1250 677224523 677224553
    0x62303030406200a0503030408070b0604110d050403091e1d010803041205010b04091a0a0c020d0f0c050d020307031101050402030c130b0405100f05010302120f0405030c07080607110307 81
    0xd070742000f080710344003004d150102c6480002c2150002104100600204501402245004114014032a99141c0c2040101c1d040010400c0e1401000c3c031602e001c4041e00e501c5203520034464204102c1140c2c41d07044000310301c0d0081c001c031800709200050070300144510310048003100040124841c190b5041070102903d0340606c0c02046d5480495004c040e041c84401d40042e1000741c0d01800810075882e450501c5802c031885184550090401000821007403c4c6510800c0c000e0b8002d036001c0c0c106521800d208840103200c0c8480841006140344400c0045502400390035950788594004541d1a889850301406180d4907a01c0c0941d0380c4d15040800015840109058160040440303e440c0691640700e40c41004105414000750080c0c500300401080c41d00d03600f01c817025903100e40040c081315079841004500f640700e00d44000c00b90449403008143e880128000300740e001031060b01501d040c0314054103070398a030061070b9010241d6176100c0b02c14440380070381003c1c6400108600c60041c6152440503110510301d0350543e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 677227023 1250 677225773 677225807
    0x1e0e010f2a0228060e06090a0b09010213080d09060206280f09110f0301060b090f0d020d050d08010510020a030f02161206151206020903030d062303030406 68
    0x441d910a518400e029030110320407001e1164561114500070941502d080341c03c1161000d00d44412180703480400500b80e032068040000a1040c82c440396103044048101920440c455034003404001c0159843e08080ea000d0500c140c0100540000c01c2401020440e0075401716065400103802e11a0303504c46d10445841c0f000e2a024000b28007070000040d14000e10700030000c181003d140007040c0e020010003000c030781d4880070308640649084081800301400c070f40003482100e14103d03040100c0055401c2c0114a881c0c950b5000b00710021010403500451401c8032514011261a0815001102010741141c02c640c0948010303940e814401e05070304006591a542c1290242c248038404046000d45482041607038080482c2c0c50985590a076980041f08204c152424116a40c038146550311090505001d43c000440c1c0c02c0b081082480340c1c440c1c5400c0c0080d40840481d94041c08108101030840c800750190308020034072218068422100c0ca0b6130201c0e03903803903142151b02c03039001000304215a0350b01900c2d10360108440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 677228273 1250 677227023 677227091
    0x1e020a0f0c1109010602030703030c031109010e041107150e0a08090628110105090c1026130204140603100c050403440315041e0e010f 59
    0x1400c00301c1c011100c2c500e0881e4441001000421140d502001a11686109032828080860034440a13800d440e102400e0f540d00706e2081c0440800c80d0b110700240091807002800010b030007090171030505459071040c1400d548801c450024040c05404600c180c10004280d10045e2400102554441c4040e100d003000d0f051162001044860038408c0c1c41240301004803121071242222461080c020b0307d1024040c00301041d03940703843d0018480355070118850b148a00b0051941d100b0607402d6030180c074406406a00c40601c006001e220b011501d0051010034080c0342d640344000c611030043e204000c02c0d940f40c2c0745808903040d40d41c1d090161580300041c0c0a0208010288040350203500132381e080b200740c003545d440074045003201c0d0101c105a406030404030803d1010b284410641c8050350f40145040b940714209500070140801c00124440f152072006008102c0042020500c0440d4406402d050f581c00f02d12400d0047d9201021002070500b4469018480e01c1c12201348001003550480100806407240030009500c15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 677229523 1250 677228273 677228297
    0x818030c0405010e191407110712051501120c14040b030a060608010c081303051803011d060714030c0d15060309030905181b0d020a02011e020a0f 64
    0x2480841030001016004001541c0d550b0440b107801801035420050340642540000008200e0340110f0b2401100c0140135000c54440c04401c0324141c0350308080420134041d409010a045080350100c940300350007040100f04100d0714541d05201c0d048103a000203803c554514180c000a040012004111140301c4404403c00303803500701050203401c0c021850340c1d05000c0e81210354100b08840c0d1018094a039850b008024401e90b4401c00d407401c4034150307007410700400005010000240700b43c00500c0e2801540300015102040724001c01d00356005220f0795600034101880b0946800d000704240e0360720a00c0385c50041000e03d404010116a0b01c0058504036903036600190100c90700940790012100780301c403002c100d801c15640b404002d00601e000d400c210000342c1c0d1a500080d80307160800801b204c0008210b006100e038ac48a410804209444158000c001c0d10144143e030213520140c806045541d00e580c00128000f80c0c0569945106012244402030161040c400300c0c4116510141c481c500110a041401d80d1040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 677230773 1250 677229523 677229529
    0xf071b050c100c060b03060c27100c03031407090303030207020f0612091c0807112506020c03192406061d0904032703170a18030818 58
    0x1c030805460381c21009001c06100b100e03078080d0212910070301070041000041d01070804c05842e5003043e680074103842410b001001c0320310f440306400c5482c42010b10303612460200316808074401100c00c2000101003482040520306142d01402002c0d540c10303c84c0303c581901d15081c00c0140c9041568000541010340c0070828404540302c00d44003103000c41300140341d10703100c440c00501d4400e1030008882000190040c0b108915072a040d90340400300501080d200d00801c0d643d0804222220703100d41482c2d1610388a400b026000000c090407a403c0070010309131040310041c0c02c290002c1c1c03414220b841190f001ea4000704002d1001c45504280b0b0845507488a070310041071501c41044040c1c580301142c40b26031030745044c00000c0d441c0d0700300f505905c13030341a42c42c082d4810f61205010000e41107000c480150201d01c0b4201d6050302903070710340c11080d030104180031131a106584a48400321400098041407406203000200055000d0300411000c3c1d040301c0b03c4034110840f80c103607500c041060180260710714941c016000c0c1c4c0c109980d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 677232023 1250 677230773 677230783
    0x103050303012904141203040b0f07050a0b0c04080106061b06051308040b0901201b21060708010e040503040e07030605060c16081207110607120905090f071b05 70
    0x1401c0850f266450b01e0311261101407420303022228610419a410001007580004019102200c2040303401909003201c0511041881c0d01819040311140210585c0b81c001800c0590003a019181410140e500d8506208902d421100c1541003a0248611080c940c07160324144901c2c011840d40c003e0010640380c4508949845651014200400030003002c0b5012a170384081c2405861100c000340d98202112030858004014242e02468500c02504030506880a110482420500d0341d81c025200703800031291140142011980c5ea0442041908403009202c3c3c1e0a60001e080d5024003200042001e643c24a9030701d2981e030344110300c038014811010000080c40c15002e40c0c000d000515019007019510807807201d505496109070569800c00707440c0807001042e40360000403406400304128082508e4040c080c0c561280100d00c060019501100c1040000f00144040a0154000e0304d5030b280d00300000d05003010041c1c9403600501e00880004810300b0480010341c0b04280c2d103004010f5106210241d6950b007001c60400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 677233273 1250 677232023 677232089
    0xe010c02060a11011d0318031c11120307050703080408040906030506040605090c03150903040b0f03160207180203040f0618110d021e0d0b15031009030504062106030609110306010305030301 83
    0xe44107040c814010b81041074400038101c40c8041d2040082f1044801805020030344900000135401e20551000a00a0105980290084c0c1c1d01a007000c2d0741c2c032001c0c8150751003900100c0d0345411034414442041142d00581c0d8010040344054000390349807401280c0d40e004040d82540c078064140020900d0f07040305100300d03000303488101c2280c0d42c4c0f00c0602c6c4049600c0d6209440885503111150242c1d654548089404801d442c2009180c20709407045201c000d0283d000a00141e40ca40341c10b0301e00c0800500584680450800c040c00108584010360503c00840c020b0754440a0117500c2d04400b9000503a128450001034500c048480603141940302c0110325144500000205502d59003014008880042600141c44050850232240c03d0221100d214040d502d1401c07000f0003040c07062006010f10742c00b440a01c035032a0710314050540a56038003a4440b040e242d16500a552050741c811124090088400010807201001c3c0e00811081d459030351015501d100504c05c2d100f42c00d10b4011000c11455003c9100651 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 677234523 1250 677233273 677233303
    0x207020d0c03020f030d020d03020a0e030f0f1506100807020a12090f090911060901050d1a01080618060f06160c050102011407050403030e010c02060a11011d031803 72
    0x10180d6680380140d1a0415404164440d4910a042d03e145180001d0301044548090380940a4010501d0055010b904003840c5c81007400002481041a506e040101c9160b501c641c10050030300301e2030303241014108600d070280303241034000354010006c0780d403070f00d481e4811080d4039490900c800d079480c403d08034101032320b40700000c04141a01c40804d02c52a4440f81050590f0715410000412907500c0b54808202d583e42d800080140b000105100c035a4074029001d0304040c04181411751500500481003012181c209034080e5a04001d400c1e00740e410750340143c103640d0004003500c0325060801c01117114060202c2c000c0409201d8021451100c2c081e40b141c2040e2265660964211030f0b020410745030000d0810514014a4010f40c640010005403403000d850f410b0152045481d1039140c40d003951002c43c0c180003c920b000c1c0c18021900603900058452400400c04a00e4558036408640c8061070707520309407900649003800100ca0800c80540700e1802000700d81101c8090301c11081028031110209081c010340e20040d040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 677235773 1250 677234523 677234539
    0x12130f050f010506010c0f0b0402010c02060a111c0e0d17070f021816180b040b09100206010b0405120a0501020c0a050606100e040903111606110303010b070b0703020702 74
    0x4100040000d85608444080c4000e00c43e6a60303400c0115044640c038040984521250000d04020034003107591242c20a006241c05c3d41c504032140c02041e03045d4000850308002400c0440c500032402001d000105405220f0764030080300c00c2c286240140000304c0c03964083d2281c5070305c03040a81000194030400084808030a09541c1714002420075202960901c18140d01400740042d80034141c15203401010310035181501c0321080d1842c880e404070b9070314049246030788000c0e00014002c22040c1da500042d0004045103c40c26544168000601190340320f50001d4400b0340d4840b2006000031880d50054a0603120142d4031085000485007410b071400c0d0700104050880c0d440014282c4208d00007142c7c145c10180604125844c0b9110102400480c0c050110144000f95880d0b000995925042e000200054020320702030791401244ca55081c02d0900c5000440c04a5002c658104941c41e00311455a44503603008010b90704642c500891302444c0d200d00740c0000c044484c80c8000a84490181d41074408540e00541b41c50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 677237023 1250 677235773 677235803
    0x319053406050a02040806070f020c031903110d080c0705030403060c1808070510110f070b04080706081b071e0321090213050711030c071a0406051213 66
    0xc05003050084181d40d19400d0074000307000040180202c4045a079030f00000c01d041d50b94078000703c0b9008035003541c2d002107001e131900780860b554080201902e503001c11428614076000901c1c010302400b16104900341e4070780001040945158100300c100760710001155010b5654100343c0f429a045108680008126928041c140c3c1f800a030301c40c0c54425001c2c0d000007400500340d00c1e0b0360241d968060912a26030312480010001c995284640b101000c50600b0078205d9410078860600d0300e0501e84c1641003e5003a12001c1020400c485003000307041c4c018111401e00850b6400e14040004d21074603180844038881c5000102c1c1130070003088800a00d000801300042e08a28249460018603030304005082110b054110100c5240400c400d00c218485541d004112300e0010324003410503005001c00400300c40074024580b010a1458205000601c50560800040c010382402c01016030500c0d26000002c1041120501080c0a500e800508a40d28107004500d11441980c8030440d1425504c0c50b20001000d4003500c10440c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 677238273 1250 677237023 677237107
    0x810020903071e030611121e060103060602070b0a021614031c0f03090c090f090b0f0c0708030c042301030615140c03090904080714031905 61
    0x2400940e94114103035100c65a507404a01008004200c4000710840540c5003080095681d5000c0320350340c000004100c3c20044a440c0c15050801c0803941488048400a84a090303000d90440b070300e074040e4003400c0421020b414800001d69030141d034028040c40c41e00002d24040c0b0a4002c001d191f01d010940c1100503100b9850301600142045101c054038044c5c45102903060100c01d1814008038001d1160740d56003c89420402c00710040d0100050030f481d94082d100300031600c0c004a000300801c001e0190000300d1203840e1880c059040c014003c05c0c40903104a40814440cc41100d03808841c810394000407110b45a8881284849c4544542d61000607201c0002c4403082c800b46161030320381c41c440402d0303e080007801e40c2c60010f01c02c48a807494180c8001645206000f00200601014000d00600070040764100404d040104c0c0c440c100903142030722041c0020900c0c00400c56860b000320358409686000d1800c1071209005039030010440311390035003800b00114840729003184a000010b20143c0d5051202c40c2d03d03500e16a5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 677239523 1250 677238273 677238277
    0x100905030c0f0708060a0903050a0e0409080d2016020907110106030f02042a0f090b030f010806070302090f040903030e060a150503070f050d1704150e1f0e0a081002 72
    0x40541302d01800b400160140180d205083e0019015100d007851301d00003406c01c443d45800e13400c2d0b1a611980c1e800c004000300b00039034040c0504860712400020007a20b651000c225400e00c0381110190080104000c01c904550700a03941d20442e81910a01038a440f41117003a501b621402c800500d503903191001c004180483c8110300103400e8000d039000c010f050421120740403001b80707030b5040b0614034040e0003a00003410702c15000b0a0320720070740d4039084011685444007200f13264401e6a160785a0b01ca480018000990240304058000d10030741421880c061044012400944825002a115607620f039400000d0501070340090011803c0700041d0345132460280741e06001490302914100241c005120041043c0c107001138544144c07000910180307551032078a0100683d40c00c4070481140c1c00c50a0b6040c0d451510700d404050700160a1101000c1c0e000110340030f006080010310700c0038502c00c481290b6030301040088141a260480650324066504000380c502290340300c800b5910603503081c454007000414068050b40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 677240773 1250 677239523 677239529
    0x80f0a1e0b0a060e090a0308060f0d0c091d2113030b0f070e0f03031c1401090b032e0506030f0f2505060307030c180605120105040e100905030c0f07 65
    0x6803013000364aa111100341e40d200040d000901280c20761703010800070701c0d10503241ea88940005141400b03040d00c44c0d42d51368617005507a0042d42180c0d2110f4000341d800e034128640c0007603006003800034980c00140200c0101c2403100c50034201c4030b48000007200400b49404503d110059500b090640d0f01a05007140c070580031403411120382c0001400c400c410011031425814400035544028001d60a00d071840d450684169401c429040c0f240350703a06000300250344e0741d00205000f40040200059101114420b05090034440d030705071040503c218403c018000d50b04c03402801311010303400703000599a0b80c41d40030a18243d00710ba201d542910502c00d2103008e4840000b59040b00300001144010b01c843c00500d449407090407805400d03030044040c00003a07078840c801e600c1300c200f0288603c0c15017455890407500f04c4e00c0e01c2032a08900c0026800051003403076019062002401048150380800c0006890001e00340c0301c00c42841140748a0752540024010b1020030400d4801030030700c40003502c0c00500d00307420907681c3d401944 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 677242023 1250 677240773 677240789
    0x50c0a141f060b120901020403060e0f06090c1c02131a15090603130c0b040e0f0f24060409050f0103150504030207030f080d0603031206080f0a1e0b0a06 67
    0x990245181040c0e80502c800701c400015010342400d0001c04211600c03c802024100c0c1d0b59802c1c400000031804c1401480d5003000310a0192015040d240c40e41401d1510051a9446551089541d9511912410041d0011031b41004c2070b16100c003020302c001400310f02c00a1205500504040384a14048942c0c1d4014071190000c4a4100310940c090b1400d100728000d03114407560040c070130b10005100745400740348900c00380e00c14864a4070b201e0b01c81c4008103164103e504002d036035003008000c1100fa642d120300001d800140c1c1042090103850701e84d8045009c0c000c201081c028100c1080c1c001d5420340c6883c007e031005801c41000c10300070b9262410128003502003d11081c1c1d0760740199890815861300f24840c0030701a0b50103901410ba85c2d0b0540d115020915842c0c82c1c00c07107118804104e1441400e5180c8a50310165110780c3d03465500f180701d40740c00c2c000d540454105100c10380216040101e810070026242a005500181c13059218203a10032406503140c901c03d002c0d2800d0209410051034040d154400810b540c2c1c88 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 677243273 1250 677242023 677242063
    0x1021c080a180c0e04020312040b1b06040c05060a020c21010522020d140a1401110a021c0201020903030708130b120402090a0b0d2d030807050c0a14 65
    0x15561a4400702c0646502406603200f01c401445480c12081404c1d6005001500300e80c0d090450080c200e10a901a50183d50042d40c04101c6032045034038040421800e10403200100241d0407e034030750807251007540c4a020b200b0000003425540c498000c1c85520140f200003002e81c14064600541035024440d8801da0030419440c080016004206165030051101c100b0b020340201420b03682e0900404036003008099a15000301130102c4450201002400c0c5811320680415804c0c0c0d00b008455429904907804c20b00f1507280030702010f0701155002440e080301807030f8001d40003099414184180d009110301c0c8007240c0c150200049020600c1402c000500c0d0003d16040d004840ba81e840c140109180250540d051003000e41c1c2005c10094036010485940050903014001a6030484c0000910003070800001105c0c08620341921a4164200b4280d0b06000340c8540800018170301c0c1641c0c000c110040080000007071220100b0091020f2104004542880741e11070421a0b090140d0300d1065a546100442a1010400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 677244523 1250 677243273 677243291
    0xa03050621062d0a0209060706061d010506031b071b170709090c0527091f0b0d14030702090103080319091214120112020316060e01080601021c080a 65
    0x901e40f1840d241d182803903200d1016280c3e0802c0310065400b5514040c0c0c041802d004850105181e8031031b4400425544012440303045003160703a0003032035005034040340c415001441049240d8461980030008020b170950142e50f1542c1516009240190038043c1c054185086c11002c211041d007145c0702c0f8421002034040720800c50703a82c00344c00f09503001b01c14000c3c05003103084400c1203282020b1607103a0301941402c044510b00b80d14a0764141d08548100c0d903160031648080307110307218481209034070444004a050b003804201c01c62004100c2600c0030750f00c010181180d840e400711700c0007014800d0301c0d9465030007424031020356174a041110b10b030b402c25180c8150f41e142c000c84000e070f40701041c4521040e00b40c1c00100030820400e4004c06131241000c000001d6220401005460400c1c1c44480343d50707010f04184088810000c64a00506251841c509048a04821a80400d01038075810040c1e21012200918080089a6540300104e0521500040050140c0140c440c0f02942c0c03030b0004942486200c14110030880415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 677245773 1250 677244523 677244571
    0x705011e0501060f2607091509210305040e0903041d04120e04020913060f0501050c120d140703090308090a150c03060f0306090201090f030203030a0305062106 70
    0x7030a201c0c03040814640f840c8801c00c94042d0b00002001c10f0020014003850303c038200c100419910884d5410001031f2a08802c2c800c51103044000d00300e10081d032414a41c6681441b04c2655004907594003411389116048842d420513100780100d130701a141200c0c0708002400c008034007039500e801c5030003000d10100c0c080d4011240d18544800c124482c9030032180080311014000c80940301180300006090b0416020800100c403a251030040d6810b08141c40710001c1c00c50301e0922900b080784c40740e811050400000300000500e68400046d2003c6004145241643c0d5004400d000002081050000c000703401569003017044064059001709455400398031142c2441d564415003a450f0174480d007008105008840000303072404155071240c00003101504001408c142c49032490400750900d5841280c0c42501c2d055a1411944d0004609004105240000c0c041c1810b56001984900641c8031100c205551a0009095035461141005000d1616105034022203001e450454031044221860070b0000d1000d004e44061007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 677247023 1250 677245773 677245781
    0x1f1b030b0f0f03160806150109050d12020102070f300207061d040e031e0f03010311010e060a02101104030b0601080a0608070b0d15180f020f0705011e 66
    0x34000a005101c22190002004001e5000700c0d1503640520072509012146041e0300c6540020704481e00052480b480c01d20500709482940a00c0d0b00e040001e051410000c545400ca041c0c451540c2c001c074000b60b040a0038500b207009000e540c0021384060021a5070000b40030952185c03d1840145407641d00c2c001428244402100d80d18408420041e030100000b00b0a0078800d046002c085c0200103c140d200100d03a400103010f444801400b189030b50000280789481c3e0034585c540c2054001040d0080d4103041c244c240041ca54001488040c0000142e9103144000d0303841085842e2580f400140040e44841d00110000e540d5124010769100180c5070645145054508401360b07003c60ba402800c1040d1641c0d0a0f00450b0312503000742444200549454010074802d1060007203030081c0a140150300d449030307807522048003a25045600e03031303105070080c503001e120008070504241d4403110000300109803100100c000000910940290401e40d11021480d4400c104041d00600c1c0c80f030750000c009012455621407480211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 677248273 1250 677247023 677247041
    0x60806010e0f0f030f120421050a11010c0f05010501050a0b1903180804060f08010608040b0a150905010f06031409150c09090702060405060109060b1b1f1b03 69
    0x700840c00280c2c9403409240c10444400007400352800342d5a28a98145080000d01e18151900004141032100c1f885041c91481549800100907085100c42d448590301c03103290b040c010f4115810016408800d900600c4585805613000c00c482d4101d4800d410124003c10f402c0c080c8502c00d0409e008006010341014003030b500d4424800e884100f007003800e81070940061900629415032520070709411008107081030080c04c010411078598890040c04c600e0001d05024050b0045d00500451400340008220350350b1211341e12102c20308001900500d49000541c00e508203600c030070200750804002080406011203580c0440c7c54035101401030101051003010510011240c030b801c0780d40002c0809221103003241d4210f0f04400442c0c1cac80c0c1d00c0d15507007401003003114008a581c080564041000d02c41048810030080d80102001d02c81000305030704003104c01180744507a20208600941c440442515030740705001c0c5503010b54a030340a481103c2030014841d809812a0039a1240300124603072503251850180c064212a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 677249523 1250 677248273 677248279
    0x2190806061215040201020a0206030907090b04180204110405040e0102271807032009181303050c030409180c050423040501090203060106020c1311120c09030106060504060806010e 79
    0x3c0c610024580b0303800f00001481681107128036030700e620160b100d042c0107600034903000028111160078030700303880d0a50b00c48480c0c1d01d0150b840c011501d8402010a4113603916690b04803004100d071803c3c1c25040001d401a500001e0b40f20b40340c80b0070b07071104c004154000d1041d082511030703440e5002c80c284a415605001c3d104056040984160740c129401080015264031a04604000074006200d810840011042e07a08030800201c000846051907e0b203000c601201d6403149071519104e01d081c1c024406c2c02d85100b1401014040e0100b0110030340e040500c1074a011305034201040204599032101c3c4070008083c80004e031354901c0d84440c0400d481c101381c05080c0c918100c905200502181ca80780460003120020301c191119562130b46898016602440440c0c000d201c40e03401440c60001e107008101d1840c001641e0051918505003070b100c0803c0d240e2046c2d40c0b03140010340502115030f030f032001c109201e4410010420783c15440c0a4003c6174050304100a0300a8030503580d6002c445580d004015908000a003007583d42c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 677250773 1250 677249523 677249533
    0xe041803050403080c03040312030e0c0d080412031e2708060106050715090b0106030f06050d0f0c09050f0a11030f0121051005011d04030f0c0f021908060612 69
    0x2001c04c6264004101464140b0112407500da42c0c0d07200d02c41c01c603c01782410780005c0d480307204030303030000404020179030180d4002c0783d60300314124907542e6200c07d6108900c1a591203140241c9030005140c044e541d00131400f01d04001c1c14544c103844120051480d0002c0c00110180780c00441d035145072080c00c1e20800c040e96030002c02040c0316401d01c40180d070660030080c01240c580700c100100c0c035410005800b4801000d8802c0038078603402e50402c1000b42c25160b2003d11032140b24074000701003102d030341c40c000865260360700180c1c12001071046050a43c2418015000040c2590411052200e0100c02500c094451030310108100300d41009a03c3c0745142d4801900c0c1080040401001405842144145200d0f01040e9103000201500190b130b686003402c2003510b00d488002d64450041101a45440244406801d00c680c168000d20b440d90303000e000e203a0181d0784203040005007081d070400c004d514481600304070f40040c0b458001c000b41d48010010150140541d8115025040100c2c01c241032000c0b4034200d6204200142c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 677252023 1250 677250773 677250779
    0x31506050a06051207210207030e150a0212070303140106091d040f11030322090608071a07060213030b0703061502030f031e0c0c01050c04182a0e0418030504 69
    0x12407804408a011800700c00401840e1b0b140c031050301c01803503268469120020320740d0350401000382d083d00389420455000000c0042504280c0d0118440e008a8000c0c21903544500c03450a08500070102c440d820241c140d8074400101d466900101c60004031342441c0e40d000036002c48400c3d2900344071016070380180034640c41c2c40030500050580c082006100c030040d040f03a0600e00082c500000c3d002c4514603101075080203c1090001e128640625000340070258020f04030549090401051403a02210180310110f01280c03039401c000030382d01182d6500c0c8840781c08815454881c1005801c81d20151008800700781b0702007001a0444484030210440c180703903005507081050765068075010794002001a9000300100c04682d800e0048900c400b030091a03181030b00394640d007030381c1403150860300702a1046142c80400d100c02c00a22104809607211183c03030f150040360a4428500d08903190400c2103641c20144403c102c548021980041c04620f8100215400d0140800d4280a103101ca6034560000d400a1402c200078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 677253273 1250 677252023 677252027
    0x2070b01050112150609050307120b0c0d06030507091d0a02030d05070302030c4219020d1109030d09120303020c0a080f1c020c0d18031506050a06051207 67
    0x10300c43c0d0f140e4a400c0410b01c41d01015400c03012400035044400071810400b01840a400c00700492000b810050340801d1a094035521b81e5a45150018081a8680b00000e8510000c44140e00700ca001503622204803000b00391100701e110060003c400300f9210b414803440c4008107030400025031945107070300030b00545902200727042e0840702c17030740305030700c16801d610042080303920f1301d04204612240407404100049030815070390401c18941c00144542107290b00103141080c0321108007403105070810200700340d180c211071006c405040a0f0060800f0140c5c91858008441707105403c44004040052003101900c0000350100b50503200e02d11580200c820b003d400080c3e950002e4000c0c0c1c010240c854a42d4100d84200c504c540c1d40d0402c03a845090350420064021640c01c0803082d01c841e203061a402024025070420004000d0a566195001d000b4400c0121140d00e4840c0d45005d4070103030340515000036006140d01924084900502040d103d9140218603d02001507028032440688032002c070b00c1c00404c02603886220301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 677254523 1250 677253273 677253287
    0x1b0d1203150b0304050f0c120c0906040609021801020705120c04050a090c0b0c0d08071b1707060219020601050a533d0903080a0b0402070b010501 64
    0x10740401e151080e14085003100c0030302e01451186101750b000f006044612441a41000c0403d110391b8040c0340020224600b070503002c68411520b98056481c9656035079480c1c005009400160310885426100203140c221102e460720321407142040a13022210000e68603c1403000081d40140303e04495001011100325034030701900043c0c0c1008945002142e540100d0703ca6035888610380e0701c440e400301e50000d040040343c01c00784500f400c000c10382c0c02c11103014a00300e40081d0428591003110300140600000b00810444070b6100d000743c5500100c541d503118282417030804025484140d884015100c0c180c850001d1510009400c1d060b1074000d01400b203518035003400b0324002e54142003a400028a0700031030301c40e01e034034160034407001504900c40d8510f03c03c0308020120407d805210440415003203a80b00d00c09400000760f45d0520911a041a1000925101030801b40c0020352813032040c80504050b500c60501d03a020b12080d0188009800c10010000c40204201c124804c4000080c80c00340142e0040080791b000f42c0c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 677255773 1250 677254523 677254541
    0x3210608010c110601060530090717160605091206012c01080a0212030412060b0925230706060807090902010e10050d1b030c05160f081b1b0d1203 64
    0x4035601c460703000c103034030201d448d02190440166444034070f040006240c00f0580c1c5080504002c0908502050340d5041c040f0460b090140e02c050203c0081c2220352902c401552904040c20042911070b256164a5650290300c211401d007040c07903c2c6a01e80840c221210704446048844c054000e0410042582c284103801d40309000c1c00c411800309010002d10102e0300300a80c100305110700030026044203180304000300180050950350b100003c00603102207818050603500d41420782803c0403e039a040e09503d0b2280920b102c240318841c500b02050030000c110741900080300f641c05c400103541500740c50340c404100300c64000780c01134001006d0310300306051810018030101c0044002d00e44079207080c040e1140b940c16211642e03500d42e4503194000f01c041c506913052281c96060b5510b8034120303140c5880075811100e03000312000098540107190307000c0d8040080110440305001000c0207001c41e0b81d080c482103a52a4292241c164440040003001e141440c5031040100b54415800a8480060030034181e0450040c95119 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 677257023 1250 677255773 677255827
    0x2090705041706012102090a02030c0d0603050c030d1706042309100614010c021207031a070905090705120a0216080910030204080a03210608010c1106010605 69
    0x100100b4050512110300da0b07444070040c000c18041d4580b802540044200712410021021001c03041c43c010307911948643d40001d1710789005a20380d01e83c0c129103030f128443e4000080480d498404000100306e008642041200c400301c0079201450b13044241a20341e4521440c603000c0c072940f94400540c0b1443e080e0b200c00c0607000080400c454002c0382c070344200c000c003805460301070f43d40d4408031300c03031581100900030340c0e0160000a8003041800b120000181c070480300500006e200d07078038455007010103540401c0801d0041da001603040d005003d2090581070300150584d86400013610b5000d001c12642014114070303000d0380465072101d182c00c40c1c4c86400264808080e1040340015020040768031161881a054141d8600820405603603880314001c0001c401c9030030004a05060040c031040000031070210343c10a01d1609400c2c250808038000c1d07103201006041095600300c9520f003441c041404081540141f04501c00768688207030b8250000a02c07551a02c00b40314010010364200b04080d5104280503840d15010091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 677258273 1250 677257023 677257027
    0x609170a06091505180c010e0402161a1005300f0d09050901050102070b0c0106030609111c05060a0c0c05070e060102060c0705190320030a0e040b0d02090705 69
    0x159a441056a020440560b0f0310040520180003c484921803d60000c82c01c1d140510380c0003840032419200e17002d02c0c02c8181880102c0050008607102ca4049030041c824600500308805024684906003100584200e041c1550060020740e0b5150000d03010402e0702c800400811000d000d0745000700241c031440800f118112141000060400e6003007010541002ca0344020b864192400a00100300500c2c1e58082d82c45604070f81c00402540c0d80105103a0282c800d41520981e4402c0c0503841d4602401441e800101918582040d4005014038840801040c103002c03240c40c085040d8140091b090040b42003005802900000c01140c411116648040d00001c030b1802d1640f5a1205074440900381002548082c1a04441c0c5041015943e414016568020721898407903041c2000c035100d06035250414803c4558018107811403009042c003d80100d08400c03410668444101e500034011600d035000280c250020442501030585180f91601424032454400360403101c6824080c0c0030480304680c06486071060040c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 677259523 1250 677258273 677258293
    0xf06020c07090c021506060f0717071b050102030717031b030408030a0501170d0806060c0d090e0c21070e03030a0207030309050d03080a05040303110a12060f060917 72
    0x5000c1107000700510040000c483c1d0003594080e0600d00d6a08900d2070030342a5104001c503a5890300207a801070218580c50381d0b110740040c42d04592004550b05101c0c0c1d4000082a01c8041141e5001382642240710b82c8185820035544400590756030154400082c130740743c1d100c15014420322456010f1640601c42030511966000e502c80c00218a50007550161942d0b00300000700408508140500350041134010509940984000f000c15102c06614540508100901021510590310030b400e5809a01c079050130307503404803280c41c0081c3c100001c1344224800c0e01c0c0c18400107540038a4450968000c010158103540d0915440340180405010090294051040c900c550300040d45080018012511139600141001401d505002c0c00c01c0002c0d0303021610601c08405030718002540f00c0e03c0baa40000e019180407580761144c0c5000e50140120b12102c502c800380110b82d400c0110f5001d0800303040000440c1c01000344c0c0751503031540400e40c41c4034045c00c0003141a01c102007048a2800060a1210040d4400e0360f1060f00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 677260773 1250 677259523 677259547
    0x18080c2a0f15041d07050a02100b190605030403020c01081005090c0d0204030503070515060d060e070801150905010b0a02030924040b12060109240c050f010c02071d040f0602 76
    0x1058010001c80c5115804c001c80c1c40b00c1c82d03030719281c10200c9402d0003824001328000095482440d10a41c071421034640382051036580b01c1840d01c4203482a10f48501e9000d03611520002c10b107810840c0c0943c014415020306080550044d412503000717007600104885880e0401040c0031040301c0180481e411000d0400413030014001c4c81c0b0140020b144600e00ad0340da9541c0d20b04000340b428000d528942050101902800010794906416004c107d03404003011030510000c60402d130510b40260301800f100d50070320410200b0381002c0c404010659441c03081c20170050362100101c8844c0d015030b40200c8056030040040d4030300341c5480594516400c1410584907240e8100c01c4820000b500300394801d0408600201d0b00d40b1130030300c5004580341c0c00142840e00c5a20545402d504c441400c41c22040e4800030020030042202580c41031900100482d00401281e0681012104840c02025041d401e43d0060090160101e0a901007041c619110341e4070803101c40c3e0940391070316000f414444d480001c0350640d80c01c102da0fa44050b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 677262023 1250 677260773 677260777
    0x150b062208010e030c1015092705030406170f04081e0703031a0d0c0e0603122a120a2a1a0c09010804110418080c2a0f15 53
    0x22400400755480e090a885d8241c5440b144c1601051618100645c1c8003d030701c100003c00b011940f80c20700106040704042805a4040d079041ea03a054100c40003081541230100c000b0060041300d45583da03000107008000210070110100341c50454440c040c942c0441c02046039400a4003076280a42c030446030300603001c81c549000794811002100817948072492050702e40031040e1494105d0009442000340c00311580d8031201030031841e009241a044160002c9255518204000c140c040c1c10f001d2190b0342c031720190450522046040c144001002d070281220700411501046c1810304402c6505840d01b481d01c1c0792010b4441c0c0611880c011503010311004001c0700701f201400c070f10013014000e02c0c04150340c00d42c1c0407440311b8a000007405140410000c0020000d82e03640640040d80c0f0a07080410b8052040018000401401e10300c0d90480039000b2040400742400406401403003142804c0381100c500198000100035049803440010b86c05440305002000c03182007444840da15400c3c002e000718a4140700156941581e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 677263273 1250 677262023 677262041
    0x201140412020705011b02150906040f05040e0c061b03161a0c0f07020607061b050307080601081b070c0803030709091508070b070609050d030207150b06220801 70
    0x80c8071490540070a5014000d880c0500000e1815200300d1004040e02c0380c07103060801000740150340c04a04283d103421800151403000000921a1383d07169624101c4406040960103481c0c8158607010ba02902e0210010b849021902c002c3c00710350401604105490081000307210510356800200080b02d45840c4894900d0382c1548220480300d0300c400c0001d060181d11030001c1840b07181e000c0410180070354501500681e21420313030494403241d440a140c544030000d0300300c034103454035000e40410a4540d0b00f60010f01840c401c2d142c0399107404040c0c0d01c0100444109805803110400021119003242e0350940243c000c1c112a4080c00d0030b8440f1031f55640281b460341d40704407080000035031070450510140c007490251410070070b0800340c0342504500704020b094a17180a4803415060354800a404c000b000032030f4011041640c0c014080d201c90b6039160700064040d60005000b1241c845000442c080002c4651140c1c1c1a4804082e20042c10850a10b00d158410711304280454110300c3d0030500000c1b01c0000740100740913 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 677264523 1250 677263273 677263283
    0xf09010216060c18030804170c03010624080c090d0206090904061508070806131703090312180a080307030b0d2102120304060902010c051603120e0105180102011404 72
    0x482140f1030320083c081c01d0b84155150300d14070381c080c0400100e41c1d15025941a9240c001c80186200600f00e4860b14210413a410180c2550130500c001446c0c00d540303900075071821240c0e110400700c07801c400c5046501010443d140710094600344021202814011070445940d4806807905240034102c000051000d01c040f101124041d440c3c0c21f812000000c2c20720200300501100004203011805c0c60046502d03044e00900c030341a406101082041889109561003075481c85900c071055880c145a0740b0340343c40c2e03848420702c5442c100f08000450115000398000380c006070038071009008400e2080da18000d8950000e0501001c154031194002c41507541c0f130030746840407031040d01000c0000e4805000e107007001d0003066550f010354016141c0c4000c0c50700024101c0c0c0e03000d54060000154010544010b982003820f40c4805801c074800d080d0312601e407071814200e0bc0c0684c3d0080c46030205040600c1c0c0102c03144038580030340324009a070911812408031640c1c0c4040140040c1400007081e0088614241000c001c011102980c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 677265773 1250 677264523 677264531
    0x7020d12030e010c090302150f040e0f010b040605161110020303090f06040b0c07022d0a050f030a080310120308040b1b091002071e0f09140f0901021606 67
    0xe541501c6800d0050306002c00a209a046900000d42005494800640a0b10310b884002c818407040382e003203031076024040125989640e1200140c4000c10380443d1400d4544040b003001064441d200b20580c1c0450300c0a030356540c075040000d01c0765900311f548000220380810703c62112212a64a11034144841c0e80154011078907454000b410318500021118181c042d03070400020b12010441021500f68820983c044041d9a01402d1000c201010400ca03036443c0c06051410b002050381e0a0200e00a40e940e07002c03070f880c030301f6a51940c00b00301085099118042e8580c0c08410084000b803070445c06143c0c051088a02ea44900380c1c0c0d0705040090102075a401c86c0005c40800c104820000c0e440100c0b6007010316034600f81d408800c4455810440d1080c841814441c0700e0320b05100001c0c83c0700300314440c0900034892140e011103100c104140c3c0b0110b00340c0540b64200c612a54045603e401d0f501c00e0702c81f03182400c02d40347c0301500e40710346028500a0280c40c60035035540800100c41c101003509000003845114081c001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 677267023 1250 677265773 677265803
    0x414100e011401050d260c0a030801051018090c020307140109031103030702100509030c070303020d030f1404060e25090f0e1005070207081603030809070f120807020d 73
    0x500c2e000050300003a02caa411010040041a02e01009440003102c90f0b140c24070390031113041c0c0d005003405007109040c102e11811080d0410123a022070358078101d4000b62151707041f044a00c4010384042408000d0082c800050b141d080060a0a1760001400060381c1d0040d070346403105907105d00d454059494501a04ca039160f21080c000c050f403281c4049140c01944000d142982002c02c002912004030b042c1c0321a40d81d8403840071646014003402120f94024a14080f6001c140e500d180c082e46511214502c04086480c0811180c03d03607680d40248072a050400c6a020700741c0d6078581e101002003026070081405445810005546140c6003c0000d056030082c1c019035054a141003208416282283c0c104040d00b41050680c50414400040740c5500c1c49000070085595500e1070310480c0b078480c071540030116600c0385080908403505041c060380d068030301a43d02c0d54825521284441c2d40d4805078400d02104103903008007080301900401000e407500384190b50312403030001503800082e43c110b8640c0054942080601001d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 677268273 1250 677267023 677267051
    0x90501090506150c060f10080a0321090f12021f15060c020d2310051509100e041b06120b01030c052502090903120f0f0414100e01 57
    0x3c1c60410f081034814a014028051035449942c0541001940210280440c0e545110011145c000d04023103811140000c50302e0400500040d40d825600141da19070035000707021392110b402840071076600141c14261204203540c0300407a4210301010740341140200c100c8a00303047e140780d0700100e508007000e80100c0e914050950346641c0504680c054028020101e03180c0c401030b15841541000c0320f4102c2c004042d08149500280c49240c001c100390017150068050703004c980d20880d0702050060507020070300d60008000c1c8080c40304001040d0381c1e0150030200854100441e04462800c0b80c2d0281c41113a0038a00c0007803801c030090b460080c0d40c1003c40480d5a500140e071440c0502d10a039000a00300b46024401c010020401130050320841d141e44240901035501a4210103a0100d1841d00a60280500000303141081c1d01c01e440c2c3d0003068080005030300342c10200349150300150f4494001c1d40d120300100b615450395900c40c0c154604c42c0c0c40500b0729008040941e454100c0510443c040040400008a0040240006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 677269523 1250 677268273 677268289
    0x30b0625050f160e10240c140a060b040209061909050409030e1f0e0f0d1a040b0a060501020c0111210310060309170a020312011517070c110604090501090506 69
    0x10142044141e21020040c00003104903103403800d807540006c55480000d1b090100e82003001d8107400751040340d201c0103581032810002800420301d800b41e00d0400801000804020907072140a00e81ea90241d4103100340114100302030000c41101032141099004180e4510120303054a8401c0d0003507000c91380201600f1f40c1c0c0c2c200008000c10707204641500120166021101074829100c01c1d05032401004104141a000d49540106611064000309506000d1030715000300c11501c00200d804031075206502010403c3c1f03207143d004e0841a500140c0141451500400044031a079054041c0c3d11464071803215034460000400c4c0b2003040c0ca00c44003605030359a25210010400d843ca09034840c0040518040c0c501000c50740000b604410600d060080307070b27074444e07410a04903d5801980b0501040248071400020b2100c0c10724082408140103031900174088040100c94006204120380040107e4001650480007034080590001c940c0e50080585040c20f881d103403043c080724003d03005091855030303803020300c1103074a04240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 677270773 1250 677269523 677269531
    0xe041203050402010c03210513050f030a120b060d0c1808120409050417030a0608120901051207090b1309051315050601030605060f030601030b0625050f160e 69
    0x50500280c02d065000030614040600050308004558040b80c51945404221b103c1030100d1080030300c8241003400407041354502e5184100c80a10501810712042074000c42035441d03503021030700c510a10f1a8041c4000010309070302c45180758014010000880007021b1449101003600c07550780e801c00c004401c074510100c1e182130354000c1e2440d43d2208001e120441900c40454050303440000c0c010440e522145800c11030a503100410021002000c010040c2c2d022150703101e541110b44003000c40b0407000e80000c041c0040d1184411190010f1000c1040004078101c2000803a001600b610306404110703a01d12003d040b0b81c000503a4582503000d660001c000c0e11000703020f4140c00c580380c1c1e2100341c003214081d41c801c02c81c980041d20368456140c031031000440303982c0240c8c081e60013010054406560798200207290311042d0b2040701ca06001c28075200704c0c41068140303034040e40c40b0384560450800e070314000f00c01081e0303d88040500440e51440ba5980d2003804280510180c1c245c0813100d0117000c2528103081100000c1d4070001c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 677272023 1250 677270773 677270777
    0xa3302040324180609050c0312030f010b0910111203072f06040f03030608030d0c020d020705060d021e1303050706110705090c092206050d080702100c05070e0412 71
    0x20300f01400a410502c1808240b951140d00003510359414648a42440d03100304010307074180601e8440e80c8440c100e42000310321840c0d060541e8030250b0b89446022156005482c05181c20119429004103ea0301408070340441444070000c071010718011912080080c0d00031181000003c24010351450310344500b0700790ba01d03460494950141600d042008443c0e82d004c0003040540340d212290850343c1890301070340c8500007a2031100c00762a61390301c0b00b00000d0042e011000180c0014401c032401c155002c1d10100e00101622001420725181100c1401d110019400c41c0800c0325411449440315064002013000074810444042825990103103103040060400702168401d60030f200000c000d910082c5070200387c140980f002124a03100e40d0300c1d6a06448150302524000a8000e8001d15240724109004015074403a802071a006000540d00c4405100100290007001081d412090050b10018900301321a40c54540315444d00c014110310700c2c1c40725468102c090f80003488a887c1c400500040c000394500444200300c080c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 677273273 1250 677272023 677272031
    0x40e01021c0b180405010b010f0e09010b1b0604110a0e070516030504050d0b0108060612030f03070216030605150f06033106050906090a3302040324 65
    0x2106040000741c155101010107642e074500c814065940e40250101d028881d05448400d250516242e4000c0991b06500741c0881e800c0c0c409000894444e210b40103110f40050130041c5240d2a0200680c0c1a80040c80040d003031088900042c0e01c81501084500e2049019116103514000208103210400e00f440c1c200d000c2d82160b81082003070858120b811250588901c04131100c5800803400d08441d04d02541c2c110b19400344400d4040340c1802001414075060f209031109448060304e82ca0200541c0d13408042d0054030070b400034080c5451001e1000b003d10791000395030050b00c5180b00306520b29030740c075174075500300b01c800695500030f0041012202ca079800e0b0201054070170109003810b078000251076020081112241c4220f0b001a5245030a808175410030032070001c4070882d021030503464100042c1c00d08403004030007446103a0001c2c0c10607800040140001e034202404040400043e80740c0405102c2e10b103031042e035201265030851aa1000c6100800045000701210640f010030a045000c0c00303a008500f080401d410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 677274523 1250 677273273 677273287
    0x9260301080a0f02040f060909020a0e070e040b0406150207090506300a1709030c030a0b0609040c050d0c0e07090609061d030a0623040c060f020a0b1005040e0102 71
    0x80082c81c0042d294000d9001c0203070408520018024120203d48013404a09150001544400a81085042c184200e410040c807989883c098046141d040300d135400090311121015105091607031000c42c480e0805440810266200d0300c944a001a036030540c4e1005a00c08501000b00d00b00078800d0300e420080c1114910703071055001085000c203190020b812a82802d082580e180d6020b010411800c00584c044d5001c641450700b1452145250030049074503000b80aa03e80d00200d03481e000c124134001c5a40200c07a00515100c1344180320003c0e0000340119a0450b00600c0441c180e91002030012006100318051000d040c2072802c9118408009082c03107003030090108003401201d0300a80c0b07400c00d4411a00d020034042030001203039100d031000d0200c6950103000b40d07054401841015080300c010484039031402d02034680c20441d0040d800c841154041d116140c4403805010903031044c100c0829080d0036104864100581c2c0e211002031000136500405900c040400801a07401c081c09407041740a082c1e002107040c080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 677275773 1250 677274523 677274539
    0xa03090f050d080a0302190207140a0b0304080901121113172104050414011d0108070303081e071112130b030c040807032010050909090c0409260301 65
    0x2007101005085100104e50107030300500ca075042e265519001080784424202c80d40c800781d215411401201070380c066a0715103407501d061410400c0c0171100003848503881c542d110b4445440030303088500124100100d80c4100220080b180c0540d152072003038415a9940d41c0c440c0c00f00140d4020f6150b00946d120f00d41101e0010181030042a0502c120303039a00d50b41c12a4440420701403141d4412600911342c42843c00001841c41401031507018107844204281c4401080a003d8050940409225403401584a04da042c000644030b903003800d070071000b00c4407081e0841031410b00404035070f8400c488040005074078115002010b40c08008500403001c0b81440c15107000400c1801d800109058000c0000a8030700102040d82003040b04c048030014217071101911141601c900c0c003d030031581c60b09042034941e455507445d1501442d2840320040c0340011522420f207070030080800c0c05500000100f800ca4540251445e64440d6100d070300403005c0842c403071801840700000c00c01d0f400900c0109141c07510f0001a0510051003055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 677277023 1250 677275773 677275789
    0x10b011103030613060503101e0203040c0303050703140c0307020f010509131812050a09080106140415030203030a0201020c120301080a0b040c03061505030f010c0f120f020c0a03090f05 81
    0x404150f452428002541c4c543d1009010303240c1c000d030b0b014458170354010541207840d407010180c468080360f03103800c10030018090304c00d0f4001982c0c098004016080d0800000e8080c02c020a030140c0300342410050702c620311a070815243c210602ca050543c000141c01011441e110b060030110340f40908000c4e003404440300108021800c0c1e1029031a1044d41d07030f0702100110398660703281d00e0200c0e0b11002151608600d20381c010125040420b03084045000174002003010a410300800d019144480107008892100c0402c12001c0c143d00040f11003041074005000c40540c40c14001032000600075000035a640000071001460038000c82d0829404071020300051041c4540400c1080c40b482e081070100d0140e803502c1c18103070742100c81540300500075450810313240c4003008075102c4001102d03011015610354540c51b4a1081c00c3c1d0b0700c3c0c41524800a1440202e600e1f040d400b0382c105404a80203150005040300d807140301c2e0422640100341d21051540481303034030f01c10035900a4448003d03003008100000924a0f01c00860000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 677278273 1250 677277023 677277031
    0x50c040c0806120a0609121409100e0415080c0112050f010b070318060207060908010915050702010605060f03040b060307120f300201060f050102120f04081e010b01110303 75
    0x107180c0038008400c5203c0410100e0600703900014100180c1c5210302d0420803c40c0750204800206910020045041c555030042c1c40c120040076248003000c1c074100804440c619220805c10303900c00c0d521a2900001030280884901903c00c410040002602140c009040c0d060710307410803120181403104000e103407074000c1c69603070468071140900b40d2103502a10f81503400c8900030007050803106401200040b107960005000003282c40780e4840e101100e441c0c3d64480d003038507880e24024242260f4070b09030340d000001c00c2d07001507400340384c2d48000515180c480700007c40c036038011455801000008014070090017181d2200b01c0c0c01400440042c0300f118640403032036820005224002d8210300204111406100080c000b849610b80c0720001003240300103580d005400a510339110704015880c2600200711925082c040c44203541050700101580385442a64201c590710211000d0016032040c000010003001c20880c000c06102e2111320301011008003020582100d941190b001c0c100701d548480c5079200c183c084102e13504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 677279523 1250 677278273 677278279
    0xf05090c060d0902030309091603180b041416061e0908071e0b0c150708010f0506090303041e09150308041809050601080d095607050c040c0806 63
    0x3ca5821400041d04600a007086103410010b2a410404a284001000442c6910503201002500c500300d81900d20918031041c0101040381c0c28000c036010400719800c129000b25402c080f5908842d840c000c1e1080354a003503200b03001003200c4001e00c00031902101e01d00d001362003c0c3d00d020b040c0d191a0038100c0e90745074541c1c400d043d403004000c94280b000c03040d03600300e020251030200001c941c0c407001180d0850380c1300704010001e071001d07060001003040341d481001114101d4096807850740105040a0400049500543c0100e903d844108400620850750000d00c2440030349410801603030030311740301c200c2e010b8860320001d101c400c4207002c10602c00940c80206071404d07034122003000607118000350101c81c000d001141e0040c0c01d0380310b6080002011580080e040c1c03160f00c20396503444d41031070f694012603407800140018403801c510030310118801c4c007510100d1038100e0035a580d40d01c0d1400700c1d8815100d200c0c001c3c1181c441d01c0180b0008900c03041c80410000101d9001e41076074200b02101001d08000c06680020303001501c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 677280773 1250 677279523 677279531
    0xd0f08070504050307120201081311060a030906090f0210050a050d020a05090333011202040b13060f030309150c030f02160f050a0803041401032703030f05090c060d 72
    0x6007403045041d02c0180c40701038200c80459490f005450700d81881403804900003004400010041c68441c800c04903d1640444612060321511080100c11b0700700021030400c15584020a00100c0c105019058a441c000c00140004118500611404010f140c0100d824084200610004560312004031095850728020040c0c48043e40c00040302c2500c00d1450160381813052146040c040c040440d0032000c060500e120f26141a11842c060750f99442d024411440542d8100d028140542481d40100303440c07410003410038002041d5480c0c84030407207001da003107000e4005c810901441019000040e0070081c0c04003c542100f002c0380500010715603440c0000080400940d4028442d0040c0200b010b1035031140001540c561490700c841c0e0741e403e031006521500340700d0742c000381001035017904c040112000c0c2c40c1e52401c01c141c0c04013182c00641c05800075017901d0b1101c0b14001d0159588484d142d6081d250780f8426900890b01459414150040d0345c80601301038020f41203500b1408035135682da000c43c2e030402d041d404042 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 677282023 1250 677280773 677280781
    0x10f11101e050f090d020a031b060207050d080f070c0f020d062706060e09120c100501090f050105040b010e1306050301090f030f050f03190f0f1d0d0f08 67
    0x4120405008840401c060500042c0709118a41c040907900c01e4520360102e0b454400f4100b0b040f80d89024011005d404520107228030b89818062010009141d40a0704001d49040c00c01d41e82c40740b50110b202d0340f0300001040102030003283c03003a030314000307801582c135113000104820542c440e0711000040c4a40203200d80d00c4800712808014142e0001c042c0400404030341e000c0f00e84102c0d400d4858960500302147c0c0249006408210101c00c149005e00030710043c402820081e0225440700c0e0030b5401041c940d2118454402e00c4d8900c100719010f058003034541101d01003091804003510105488040e00040c2c8241d09101035a526a40d011800e4540c5040c201e41096507000c041c020040144400c0d00625015400c1c483c080040c0260003101c9071195109556801c466441c1000483c0c49000e400001900b0180410120b0032045559a90b19009105550b0000308030184941150440310010f0022a0160305c48030f09a00ca14000c0001c60301150024015185d00805010010f140f190000101010310083c2e2000c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 677283273 1250 677282023 677282051
    0x30c0901020c190810060e010509041a0720010908090609040212090d020d0908060703090311010603210504080a0f0c1701020409060b13030b1302090a0b010f1110 71
    0x800e40a010303002c100f480f071031290408018541d9000b420214440c00c91040c03039522042c49a0011a05a49280800c59081c002081264500540169481c0c460403200e409140001d2044034024130803038841402c41d05100092103244c800814604034940d142001131070105030304c1e20031148209001c942c003da4807412540000c0c0240103148464403000c5000c8200000d00701c1c001140c080c480c2e810340071035105800108003107450580c0c0b405466286c1d0080c50109090500a4114040641c46818441190140d11510b0340c02c46400790b10a4410701c8201036500402c0181e2a0361a844144a2603d50302c3c10b8246503003540d962141000c020084e030889400314052141c8204003802414609122510034070ba9200c1070340c042d4010340680240b00b80703081000075900e120182101c000801d041608641940340d521180241c035002030014900320020391081005035964149076100b0018200300080b040c00001c001000c04030b040c80e03d2020f2142c41e591154070020000b490a08070150041c0c042500d645002e15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 677284523 1250 677283273 677283283
    0x607051b0a1217010f0e0403091502060712180b040c030804031a070f1e050c07031a060f13051b070302010b0102120f0a120912020d090614030c090102 66
    0x30380115802028014010446410602e86418040ba0784541c511060203c1006240b402031186400f02d1044030010000d00a08010056006000e424400c2840350b683c40201d803680b000380a0b003801a00010f0070005641d800c40a5020700502c0c40b0010440703045440c1e0a10102e1018050150120364210300150802c0300035444107000d982d00180c41c90311184e9174a000701d290300d800100e074007081c041240051410780c810201d4941802640d41d54030941100c0500c015140c20700071225804100382000780c0c1003014420441c000007540b20310308824902c44242d500d00350444020b00664403480c610442280d203a981c040c10640c0246000c90002680d0300c40760103110300b171a090021208440d40c0030a0780303010b154043d40b003000e030100280c0030354600611740d801142d07043c42520f03288841d0201c00e00c843c01c030862051421600307924415400040c0840c07103807903905220190700071000c0181c4c481c00e0381c03185071644402d030030000307001506160380100704540300e1501e030340801403500804400c049082e00f030380e03842048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 677285773 1250 677284523 677284567
    0x41e030501060608070e040203040b0a020318070b1b0309010915020c03060c04080f0c011b05010b03073c03020112021308010c0906051315140f0315040b03060705 71
    0x1c1041d10b0f0b95407006001d40300111120741c007240d1004248507480c146402182d20a5500c0f440003080c5641c0c03c1d014900035080a0b01440c01079001c500502409038040003801d000d8400d443c0c6440d200e00b00742c804104602c040190f401038580050148510317698200042c00151400001c181c05000c914130b8040f441e2100c1054001d6242c4104070600c410007035072400400c103490b2000f0a83c1c403841d6288130200d9494810010050010300d0302a501010400c0711300c1d422181030311800001c140e400c020740000c3d14218841d000400e046000c3c0e041356002c40510030b40c00c1c054822001d080c01031001c4428042c510312601c3e20000e03040c49000d84003a4100f20380790781111200321080e109a20403a4480221030300920440401c0c41c0071800010010640c980104240c40b0712a0564410f414994240003400c1420b10840c44c040040c024111600810322822802401c035011030310a8080c0c991400b045005584110244054002c51920b003012070b50392400309205502500c142881030352000c0819540084040e845 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 677287023 1250 677285773 677285783
    0x1302011e050403020f0306070c06050c040824071b0b0a0f0c020a05060709050f130219020c010e1c0b0912130305070e1909080f1923041e03 61
    0x3401205103980090142054900a603092001003030310f5014580c1e03490081c1c07003103400703d41842401c900050503600840d601035403202e02507040c680d03146000351404078622a0036203070411303004900d03025141c540001d5034880010718100c00b00585a1044042c20b0300c041030058051203511000070700080301a085481184006081003110388000e40b0f00a49440005400302c0700c5016610110b0549480f40d0b41070300586c0c0d0001c20500d26484607070200106c3d4000c0c50700a50010f5000c0c88900000c1003410208041000d141e0090101300042c80001005000104030b42c51103521a02c60f64662507881c1c10b41d1001c403e900c03402444150b00d503002010300e0004000614480707040d000402d50405031100c01e808007141d12880464100741d80b40d04d403040100e101140e92001007990610220922102a0004840180240300c4a850108515401e1034a80d0042c01360042240000b643c440b03036550301c40d01581c014181a0002d1030307c407030303151085c01c124812440348924a41461000407070040003404000002d5900c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 677288273 1250 677287023 677287067
    0x6070801032d050309090c0309070b09040b100c0507150807110c0306070903030305011203020309132315010e1c1106030a141e0c031f0e0a0e15130201 66
    0x540f4010303a407940000601801881d008001c1030394114203100340c900034405540135047d003e00b00280900a80c00840040e036019840301201d04840d1076000000c5080750a96645c2c224400b1281496032802d0555032041418602244040c04c22503070264400d43c02ca645c600c1c0000340c904210958524285541d41e840d0f80c140600307400d11418a4016014904407407007601d060005a0382d440d440390395601122006809030300f00b0018426140b81c40d250612030682e5003840051440754000501601c0ca02901090403441003c0381442144041000341a03e444000d18002c04100c1c680c00110301011100e09880501c010200085030410440c0d4011242129028221035144d103814145c00000e4865150303201d440540c4000858042c1202039000c0906410a60555000340c80b2196034140382d5200a0044111115420f01103114003550340900000340001d0350424000c0c20000000000c0740d44000e030015541e44220001070b279403101e03001a00d9101c1210409682070075040d00068903c009001d82070740441b191 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 677289523 1250 677288273 677288363
    0x60804230618160f030b19050c1b0604150c0e0909010c032a1d120c040612051f0902191511061f050406080a11030607080103 55
    0x702120010340a241c00003100c0f68905456844803c0c0200e900910701c070321000c02c80510120307501406480e045a0703e814090418800c811803541110300940340028503003c0010500c40c00c2c5403005c07109106041c220050041030500da40c031a140c1c080c05a5014452640380d0700d5401040340504410403080c1c0e00600a000203141c0a0700c814001d16030707040440c012914000700d8910022035100340002d1040c0d0702d0001c3d072a800c08040700350b4031145004c00c40601c60925a40c444865200e01c2e00001e02d540180c0006c1035903031141800c11040c2c1d103c0c0c0c0c1100410321000c040d0800030501c005821900500780c0c0d0040d02c1e400c41e05e0010b200c0034011404000c3c1d007050084910082d01a0780401410441c0d6411203071502803031412804842c1140c0c2400348103929807010700403e0f0458440118200c00601761841e03451070039614004102660001c3d0302c02c0415030440d180d5041446070320700c0817415407031045010f8500c0c4c3c074014201034400302d01800301802074a18115036014811841c0311020f10940441c10745404192 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 677290773 1250 677289523 677289541
    0x30918010911070803040b0402042705070b03090709180219080c06120f090c12010b0a120804060f1101021206030d17150103110a0302031f0608042306 66
    0x70301c0384182003454000d0341e01c2d08519800540c1d41980c0e0000f0079074559103031034907010000c000182099900941c4c54900000759808129480c8840318542c85000c030461660074280e040c9061a8040c1d18044010810003080200200d0f0800980d240000002040383d2001041d0b10301e03160b1202e00079013000d000100c01c03070f1022512521104441c1c0d00c001300c50300003c0c003900b8080c030790083d9440c04044040100200320340f00c070001d00308ca501000c9042201c02c0f001034207001802d8101ca464145007541d5441161400360304201d103900001d81803801c5044c0c1038081300d50f07549640b40700310b10480d0204101610070010746441500c1d013020203056500299211041d207005a912540e007560054030074420307000c00d240254081d230507d22100f07242460b421b9150751200d0f5550503101609084904256a44450800100b00c2c1005480c0e40301c01307a0b600607202c6c605000c109910701805041c0e0b060040c4841010031101d90702040855001e0b42c094a204940103402c1200e84410802444a9071507000360420450b00704 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 677292023 1250 677290773 677290819
    0x5040b1b12120c070201051608190504140102030c10180507030804050a06030e0616030b030624180c07080f070b0406110a0504030206071e151104080c01110309 70
    0x30344400100740d2503d8180f01c1c500d2510803400028007041d802d22400f06103100407010b10807268003550700c2e00c0c070701036586031000102c000c0c2e11045e201203940440d0030300440c0344850710980c1d080c0083c00214604000910705595540880000055094446a5801c009080241c451102940c0441225241602d904e050004c9400c80c0c09041e0048400b500e0000f001d40c801d004e07416109400350007804c1c5688035144400c820680c0980150f0a140d142c41000c80c660301c04100d4180300d011103410310340843e000c4441c105080718503220803604c14044e0081d100340709070103c801d070f680005810125990f1404c0c01c1c40c0c001003a008817441461402c001003070080a005241d440740748518407400003000f40d0340e1903e40a440d240502480d010000d07509020900050902d01c0061104502030062012010a000652811100000021162800c61003201250070a41d40a45480c040c1d154402505090600251a503034440a000050400c10083c41e50050900b050040311524078000d018400f41c01e0036219001003907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 677293273 1250 677292023 677292037
    0x7080604060506040207030e1018080601170a05031204030c0605070e0108090d051e0714100c03060501210e07120219140603040503040e0a091e0305040b1b12 69
    0x500b030800282980c50a44212024281e241d100d13880800c8000040c441c1c50300d080380556080c40080159a0701c0b0842c80a02ca4000304145d5004203030781d60411345030000c0803041c0c0d5401002980700135060030024002106481e0885500105815607a07102d00b0704441340345035201d000d480da074645814422200e600103080c48420f142a02c8490381c80e200c0c13481c1c0d01d030386030340780c03d0b1900c00144140046c140305086203080d0b0140b82d0a140e1880e04044464440b40d0f900200c00d120280b55600c2280c048161864900800e949400c0070b0500f008400e1800d00068012144d202c01401d40d0986081001c149041e0b991100983c20404802c07141c02079140c0700f10044c0000384010aa10440403869000260b8a0f0501c0300f0040d244080d503540001070a40041c0459904050000c65050000340700210300180009600c1384a0400742c8004140d8424605110007900303000d080020103191074198030310101e50000d0456086481c141035282e5218291615603c80d03039448035560700b040c0903d040000d244810034025040c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 677294523 1250 677293273 677293283
    0x510050304030201181203020d1112060a0918030503090f0109060b1809150702030c0105090c0f0409030c14030d0e070906080f0d23070303060f0906080a0b1807080604 73
    0xc0391171100c00d00814020800401448050000e03440340d80300b88a0f801070100e020003804041450580194a00d0341500b140c881c440d500c81c4510200941c0d4580b0a10440041100040401106040511194407407201c0140601844400408074080342d0703042040800c401806002003000d5116441d001c0040e12458a0692082c10301c145103008140490001074080c9074402c0080078011346040c10501740030401001102540820701541000b0386081c01000e2250240c4005031114200711740801603141080c0d0101805a071802c002031000a4004c04080707101504080c024101e41c08000c0442e10b14400c584130400c0341401c101c01a440c0200024002058864004090010545503103d913543c1d1401010003102d5a4050106210098090403801c2020120444107000d807a000c441030075000d52040000700c0020395038000821544c02c4040c01c0e000501001030050141514010003142c0e280e9540314041c1803000c2480204400d425030070f158081e11030b4150181c90b40140d45e25901500e074003040310107403070f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 677295773 1250 677294523 677294531
    0x90a030309030509130606030e0c13090c05060a030f050705040509070c020406080d020f2404030804052b021005010f0b03180d0c11010309020d1b24120504030e0603040305040510050304030201 84
    0x2841c00020a030000410b00203414100c500604bc1d1200020b400d14113800d0710044151040800c00e515198010304003d20140c41c0817550700c0c00c0d400c07040e00300e0300000c00d20340402000340000c1c00180ea40c2c08020303030451702c60324220f422118180002001002d8642c44500c8038400c016061482c00d07004503054021841d480c05031613a0002d003a98400c4c0c1400020020a600340200001400080c00f5011480d0054015400c544240c542c1035140c1407144004094182c0384000502000800c5a0404c124405205891018000c03945401c1444002005c2801000c401c04004800200314100304100116440035032b00403503141c0200080080c0441d40f1141003944c0841d07c110040626502900401c48050b601030322107104014640c8403009180c000ba0100b250403a009440040d42e807000d51300c100810f582c1925100005080494090204140c6c1140e0b141e005040c001040042900511444100b40c02581d210b5031744c4d031351868219101d102d01c0e0040c95110082d8000d10038551351003000303540320324820f4000300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 677297023 1250 677295773 677295791
    0xe0114221a07030f05090901030b091c1e05070803040b06090a02090901060c0f020a080309011d060f07030912110a0602010b1011120403050a1109090a03030903050913060603 76
    0x101c04850509000c00c201010040c04000a2160301c03142e4010205140003800c041b59103000501040080e80240e0713151012000303000f038180007031056603d100c0e400c01840c5051119004054001400703400340300c0c050305501c08100e40c0c0500030401c4030000c81d4080c8500343d036440c01d86003c00c3c030000295000c80c040c01d00d02001441c0284103108841c0010030090601130941c0c61b0840803240d01808810480b0003040440002d00142c964505840240060704040c5403a248d52500041542011814502e00c00d600c142a07c00c0d9915081c003103c0c544ca25a00115541c0d4182c1d09059500b52010b600081010b003005081c10244495200c1c0030f00d05440c110b4010288a82d981812401d0364110781096030b01c1284287c0c02c0c04014001ca4901c0201e20740002904d10b03001840e2503081f000c2d0096031060356290806d000d0481046091040d800040e08201d0b22104070b8180502c2c0165a00004640181130540d50242a41810b000364150364411500402c6a080c4400c004182d8003d07085602c651000300741455000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 677298273 1250 677297023 677297039
    0x1217040b070933030b0306040c03062403020609041b3f0506040b1e0f10090603020f0904111207020d12230403090e100b0a0e011422 58
    0xa0f00b511101c14051003000301041c1414914141410f112034140365403600382c0f00301c1303442c18440765108500800070719906e80e280d403c00c4015110346e5107261802004c0000241e000b20800315401065a805645054a40c051007002c680181010f05940700d0100418000442499100980901c0000200024102c11860402d14003528051203407400c000040748940d880714007015449035500c61401000805c04100e0303d400326801c0412503150365001c503a4604051101d04020944081000c001d072036003040828042001080041d00f4000c00c0205034000808001100f1140156441910018002c000301034440c119181d00e5030000a51207605050140041c00035800403078602e0b800340f1503440e5038200e014030360744c4c4100504000b04500c00c04000148086000f050030461a40f060f44242c0f00d83c2c22290030304001d050302100041c10404612101c8105200c0e00d00c8038029036001c3c0b01c040c00e01d04510009280182d440b080e10b0a8072845216010802c444241000b001000c0041456142040015260500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 677299523 1250 677298273 677298299
    0x50621130f050733030903121107021e150a03091b0e0f010e060f0607051005010e0f0603120a02150405010f0b0627011803050715050702010207031217040b0709 70
    0x140c42030403102c00441c07001130103a00620506e07446407501e0942640580440c10486d100d1100c5640022404a1403404600740281c1498842a142055040c00760b400c07000504d6420012000c02c07207018001c0790303020516000f80c1200040303503485011000c54400c0da040c26036003a00035200c0e12203508609070116403017804240400d8143c0e5403041d5180043d0b03a03034105100b1042844154550000f40401010010460502035034003601042000030a10754900500b06400903409030503140c100031820300303102150ba000190311048180091074141c9460085030103a05103a42551103c540001038002c00c0200081944001c22410300d03d05c040205800800500910f8002c81c01c03000e90014040d0380d000840c120010103130340a9070301490032030450000668010040f408690084070a688600c2c4144403c4420414501309158a40744c2103040005540000355200c80c94800030381018040138144114a05c11a04684142441d05e40e03a030060030f00f45400315080701c0072194000000c65039040031820101c5101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 677300773 1250 677299523 677299589
    0xb01120e06150d081204050c0307080601060c0c03021017150109030204200a02010605100305040206070f0c08031b0106150206190b0a0308070c050621130f0507 70
    0x1000388015690b003111601030388000e0300c0701e96000503500592400900002c00800258981d060070907078030b00f07061a10510f050454852640b103504202000e001040740081c50074110b0b441c5182c0070131103520302c0c149084020300361f0300702a410840354402090700d83d420103200345003003015404d114015943d0a00101c1d007410082040c5000485001c0100003603e040d8021965035988220b9000d41080005240340c3d07268040c04551000d40d444880c03c000341e00c0e00e01059200d0881d90b0406000f50700c0e007603000400d98403070704a000b42200f50301050034040c4007000b00158003504400c4100e82da651074240c101000c10200820103061903080c0000401c0b11001d0103114140084503800a241944032031240802d9001411801c8a00307607520f840b2581c09035520340c6030324002e60082180725610081030601203044552a0800342c021340003040003140012800428880e1040300c0b10341d40c03009842c3c514141070700c0240400c0142140c0b8080701203c082c010041900310495918140c003508101c01e15280e40c4100402c0c038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 677302023 1250 677300773 677300801
    0xf150f01020c0909070f0612051f150207051005180d03080c0d110304080c0c09010f1a040b0d02090909010c020a200306040606080c0d0b0105010e0a0312030b0112 71
    0x402c41c0c921820100e80700c503003200700c410584002d00d840b26018031101c01345600c500005002c1c140a4280f90180e4803d0941001601c0c81d446000b0f0140c817014107d841e998071600807000301e03129050411500c00d22000b405060010860100700301a200c006000b50803800b0410401c044079100c00f4042d20340402c40000c00342d032540b90440d0769581c21400c40750b140c1010901903181c0742c0710540e124800c4c121000a600c81d1307116104080c1c842d48a45802031500240100c81c501a42e440c01c01400a0740d000c0304a042119202420340f0b90500b010030300141e00340255440302c0070100010031140c0e0001d4031a006056404001d42d4070b6101e55032001e08030350903204460010f0300540c0006103403101155110381c60b803007408295021028032803100d4010a00e410b00c22a800c0d21116601d11090000310350510895803540c070116550241c40c645a1140100120706214141c140000a44003d0654071000d210100440c0c00c061103208840851101802800211130080e001610107114080022107074410003100c50101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 677303273 1250 677302023 677302033
    0x1606021506150f1b06070f230a02030c060a0209040b0d350307020a060b010c0b0f15062809030f02040b0609030f0c181b031e0f150f0102 60
    0x82d1603a60201e41c0001ca40c100d8043d030800820100c849182070700404001c2181c010001881e04240c010003a4010000034010040600d8200503d0301242c0c61402d41070004500070b55079021640000c0e4510312a15041c0c036005c1c0580b60401070410300c036a0117003c1c0310784251400d0001191310000c01003481031810000f0100074038a020700d881e185584810000001810303000f0580044200d0807815030f60070884650780140d102c00c031668100300c068022011040000c3c20b14142c030101603035400c004000d0080c8420702180b007040000b085803050300c025481c07982d000380c08a90764042140380e00010b2502c1e601d10301d0104400c01d1500c41c1051091000c08116908100d240b0044041075003008080d0241010282c1d100300140455055560184180e172a92a5640000c0c940200b03003005011003001c250301c1d12002a504a020400d03840d104110b200c101d0402108103035900d5862400c0000b1b040104010901e84100410811901420300600d160240720300300910726845120703804024030b03901e61080e12801030f040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 677304523 1250 677303273 677303299
    0xd02011104090f02070c0306050a0f0b010c06231f210303090507030803151503040804051005160c261f0623090f010302090c0a0c051606021506 63
    0x156500c001c0600b0003c0d8001352600c0c40d9911404442600781c0c00c02d4881c03a13965014000d07000138510480070650302c1000f041c4290780b040000604004034500c000b81442e80c0713405000c0e188030040c0100e2403007844503841c015002d060840340c240b1074070640fa0482e11041140d54000c10a000711247c1d12a003c04901c5581d1131004940d5000c40103011309040403580d0340305040011001400c2800039601c210640c880325001c4c4a2030004000c0b0190f40d9081114040d8010800e100c00b0035244000c0b64252030058945601801a041c070489440c400c48402003000708001c0201410011040e030034000700d88231002904118204840800f1300c450422090407002c1e846134650310500c9006190503040750340b445000082c940e6581000c00d04080f40c0d010006a84012a10380305a1880c01b4039009070000e80c0e104460031198115030204038003690250110100e80d0012402206c5075204000b400c00c2c4540c40010740e49140445460403010b62124090807015004540b44080c0310844040c2c560701c58032006020319072041d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 677305773 1250 677304523 677304539
    0xf031c0e011112271f170f01030602250b06040b120a11010207080a05010b010314040506241003050105010e030114060d030c140705090a0204060f110c1507050d02011104 74
    0x10b2a140055101450a08900c1256890724491408074102e001c00140c41405e10720300401280901445448020b410320900100f50448146141503d60085c001a941d05c6a1303d00310740408543c203450320100c40001850010170042c15002d90088200303a03028010b8070510010004080c43d40c080c040700c1c40d03018407401da0206683e50441c0c0601041030041e52841516501d206080c0b501c000000d0707a181e034458648008950303052049410340340036400e50110341d04055458580710900601210318005024a07100e550407080c0f00105070400000b0300050f00d0007101d140103406803400344501808107007810012806400c040c02601403058003842141403075035400b01001142c140f80c001c01d0b410480d0746003034080011325400e011207040040c4001041040d160408005100300d00506c59030056006000c01c1041c1030304241e0036415a140d80c248150b03001400c1045c0e42c9411105011258021000b801041959402000800300140194156560b0194408040c0e01f030f00d08203600c0480d10002000100b1083c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 677307023 1250 677305773 677305807
    0x60606270118030303020403141204060f0921051221041e0b0a11120a0b040e010c09060e04060e041e06020d0c020c0109080c0f031c0e011112 62
    0x141050400d02044545040c1d9050202c00da81c0084012a6000405000707000d11818a07075001c83c04000240803c2c0304e40001c000c0c84c1c1c0030350320800d02801802205162a14000d01c030003c050030a01045091503880214503100c500017004043d11140921810604001c90146c11240d2030a100500008102c002c25a000840400200241c45401c5506241044141c501e204601240e000e0354a002c0c150401718500000c6a07800641d031a100d01007081b04601c00310040c200943d026404190000c2c038118480e0218001d803d04101941c2c1ca54640407140152641003950201640c115650307982d9601310300000d104c101c84050062113200704000002500142169a400c642c0c219040ca00c41442100755803154180c0e003003d92411440b54681025420301c80e410490800d101d202440c00e6445a803030a00055216440350b1440c078003c04069004a6043e107041048148075001d4240e0082d140341c0058000f0220000441594009112100380c000c50000016030864101c4078000154035141130070101074050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 677308273 1250 677307023 677307097
    0x60311060901051b030307020607020a020102070303030f090204090507210807060c0c0803040f0210080f01091a090406091115090603060f21013801020a080409020903060606 76
    0x50100100590b04100e0500306413000b1164000f19100d05107180040c0c1840ca0007000c510455008000850160f82c0c00101001102d400d810001000c00b81b281010018040c07505010790800c0c1464200400c01400045035001c90b40201d0894448080a402c20590380c5030380440989919001e21014010503031039401079201e6601803d14204040c03a13661601d025410840b0107442e16000b8035020815030916803840c843c95000382c6004140391500b140041ca03001018001c4403110b90b40c41d80c910b420070a02e508001800040103180164618192a100010741a0648129001c3c0040c0421680b5400e003080740607004042802500c2c02c2c05020410b2000c250402010300d50f10403203103101c00c082619124105405412807804800e202c0c242484514251819000c00c06092600100035036000d2001d40066a40c0030200751415a0b0003640030300403450151010805041801c000600181c3e034400c03035000b000104d00a44c190b070048c1ea00c66007044440e02480c42d030b001d2010200707804c2c0320f00180058080502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 677309523 1250 677308273 677308277
    0x307021e01091a0703090911030f07140408010614040b01090b090a0e0112050622030503180105090f0106060503040b151203031608060f0a0b0a02010e0a150f060311060901 75
    0x1076403a01e40f031a07244100303982c0c842d5044000404000f8161300c6801c6d0400303021500380521400340e00d040034911034070004201d180c4030503894020400f07161084403401100a00380840588881c0c07035031102802041c051141032800c0c10b507800002c6050410b4080c0b003523041416104c480003945021205e0215074031a120740c50b4024140718003c0b42060708500c407180a018100d401408405c100d1400c1450100040c152030000540145020703d00b0a000c0d84d2000c06950600d8007648a80b00e541d8102d0009a82c0c0004540550a00b820082880c10001e0001d14407110b80e030090103c1580c52905651612055030082d00440b1201c0015405219800810141e20320140443d03045001400c00d550450304240c0315803078100f00e065420846681d2086d00c007038005504943e00f042004810307000590490b010f10030050303d88408038800491500070351010010202920a0742c00d00420703490507240c40c806010b8894045841c00c10340380c2c031400030f6214803015a07038488054103990b080c00e030801c07030341d80c110562281c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 677310773 1250 677309523 677309537
    0x821030a0608030d0b01030b04060302060f090d050f240108030a0305130b0c04140f3111090108010e0601080a0f092a0e191d151005030307021e01 64
    0x35a90b282040140400007030300070000f50034080305000505403001702103a01c0c892400c02d801480980d48083c00c40c1d00d0b0311044090b25940d05410740c08512250082500900a80680440300c40e9010000c43e0b81c80d1f00d5050700413060041c610316a103242d040d803828060882d096005000140c401402a40003540045c1900d4400c0e0142507541d460300130002084a51101409011030104a50040d50400200d0030404481140070340d0301d030401103000c8034086402c02c49189000241301d202452603c0b0700b2030031400c0242d000d0286144107584c00d48250720020b409400220000000201c1c011032440c9180030b080165a00c3e600380d110600c041c1c0240003503000c0d0380001d950700c440141c0045d0154030080e1022001010900c00104c06020b50030543c4510340c00040e068100030108650200d00b42a0b40003044050030307001808000c10f0703528052001810051034002d100340c0500d50742071760358138215510850100131030722004d81d00c03002403503100e00442074002d401c10398985035152841d0524411203174045040c58850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 677312023 1250 677310773 677310779
    0x930080f0402130c02010605040c020a052112130b07110d08270c030c010c050601092c0309210a020d0510111305060301030b01120c0b0a090801060821030a06 69
    0x12135003001c0032040540e540c1d00c81040070303041902400c081c08102d4005820305420540300d250700c0c0d0040c4136242014268410f8010054100c00e4151313400d40006c0c030b05070b2410b40307400d80390f2401802c4806e10540380c100b61840091100b40c410300302c414211070741d01c0c00b80a0748140110141c6d80c052000c1c0c48050020005141000491142640900d982074001c00070110b51400d5800e043c01c28050b00700c041c0c104101c20080d00007181002503410704492003410000344403a5103041c0c00c00d0f204951003540b0040c001d0329107040071050000014003051a07044844a20b0340d041c0311071b0190010054003132251070313401001e64034001d403800703406805600d4091816561184001e00c0350704100c0b00010701e0804000008216141e90070321010000015003c00d41d00c031444d550464603a60f10b81071052203501d40c4521007121040806c05004005c0d8002c02c42810f0302d90b160346603a040a81140c09038011448551b2a10400080101c0d0009040b06000d9421480303000404078810040b46a5200400401e092601e4507000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 677313273 1250 677312023 677312059
    0xc04030b0615191404080606010c030329040516020706120e0a05060906011d0112020103021e04090c030b060d091a0f1005030c0f041e0930080f0402 65
    0x285421509008009980341c5148006401c5000501e2141c180302e03005d000a0000c040c001034101d0300480242810562a0340d5440c04902508183d0a80c00d0701a02c1c09101003c00d2941d07400d0740c00b480e902103409019580e112480d4018180a170513000c40140c1c0030b90420801c0b18050040524841c00b107010100e1250580c0014902c0c040c1401000c44181c1e001e103082012106c0c0038003171a805084141c041000c103c00c44400c0c150244011f0041c03104141c0220070000443e802035049820b80301407000c04d41003482591241c800c542d08a80b04480b452400c1801841c0b4031b80c864450001a81c0e4014000c1741031415088904006102920701241e104075003418075101c80782c0b800c0724035102d03040c9060b44414900d0725001000c449441684000d02136840400c0c2020a076903510340c000045942580c0000303c80103034030500111203c240e0b6680c1c491919159031a020b20250318100d11200244140300d119800d40d5000e0000d190070300404600000d110000425030b00c6201d510300d00c0d0401d00080c4203034140343c00003c0e6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 677314523 1250 677313273 677313277
    0xe0406120b07080903040303271508040c0501090b0f0d0e0a11040c0305011d041707030203040305060c07020d110406050429060c0d030f09080a050705070504050c04030b0615 76
    0x1d8500c0c006003410000c64503404030f00c1c1c030f500000b4500039504040c40d669003d484d402010b1403200201298240703407005021141c29000042c150781d400c0d000c8400034980d0140c1f022509441c00c1c1d03910300ea0542d01003015402007610790119800c044006180c6032110184107101d03003103ca64440890b0304c81031582055042003200c040c60340d004000c00101100403104010450f80d2210290051506000041090800c25043c50041d038594022b0344c0040c0d0340b10310700103402505d5409800907800001c103404060590002c080c1003628803440440360300c1e88800c0c960380418060004001d500060708c0081e0000615001d00c0040c1c5240c0240022550710f8854001405842c6030300a0901c101100d483d0007a52503001c40e0007540d5030039040d204d2510300489950265260500000194141741c0c41b1041410142099485a042a03400000300e50311006440001050f5522070707a41502d00d07204003c07010415140c01c0c468140034111400490f0310701403440d641d0300c0c00400c0081090740e104c45001c0250b0254010440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 677315773 1250 677314523 677314559
    0x21206071b020f0d0c0f080c010f0809070f0b09091f120c1511010b0405010e06010513030209010e041202030c0d0e060d111c1b110a0602070614070c0c060e0406 70
    0x4400d0401c0f5040c84d0321b03d50b180e4601e0303100202d00ea00619841e425642c0014400c0c03100680e81c03418a0b41641c41400281c070b410032a50050304010071b410400111042070300007a0005540440380c41e0b00588441100d41f0b01442c09010041d900c1890ba48200010240c2d0301c0e82c11400b600c64418101600d9503a400000c00c44c44c100d10020114a6080403083c040d202071186080c1c031401140c4c10001941855840101400c006124a05001000820700d4100311b404500400541d4000c080016643e1201861419014140c0d01199102c11101944042900120070345240c40d010600510816401c4403040740c0a006d1681040c0c0c102508200c01c00e5000168020030ba0041c0a02e0201a41d130700000281e00244005650000311061400c111511400b0b44844110f8100210b0714044d481400c200c1c1c015400c01c481350000a02c403910024a010030000950000b10300400c41461541d500e950310384096481020070180109540a401c84c1407240e00d024a2003a852050003401c000340c415240c50030039502640701d0b1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 677317023 1250 677315773 677315783
    0x60c160b030a1407021f020705060406090302011808071205040e1503071d1f05090f04020a06050306010503040311010209030732031005060427021206071b020f0d 71
    0x820040c02c00d41e6030040420504240300483c3d0b103072400c50350003134542d007003a4404074103280d219260041440312501a111807507041400e599450a091501c00020030380141c5c21005542404006401600300c0a00d05400a8220b034480c2d00e007a51341d50350342000c0d20700c0d007200d0f000b808070038040458011815018244030f805841d034909014204081018901001a40440c41c0190001100700401020240058100b0140003004005858003c0101c0d82442a6000260041819401c0004400694400c54022802a69000c1460f0384407441140c552008551150200e030007040860300281c8540c603140014002c0fa0300040c1002000c000081c14040940c4c400d45490b107440f2011074222048010110800d2090b02404000b003042d480400d4130360504441c10600c2e295140001411501d503070300a030040031b06a100441e2010004c0f150f5042c0300d41e0007070003a40640710442102005800009403640900029266032581d42c0b5046105480000707080c1d0206c2c0c0081c50a41a0b0941e40c0f20090007840b070318424 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 677318273 1250 677317023 677317027
    0x30d091b0906060c0201050c0106050d03082d04080c1617010e0606010c0b1315020c0f010c020c04110f04060509010f0c120807050903060a021b0a020f060c160b 70
    0xc10380608180d0066046445032510344007080020a0304260400780e13075079081c20182c0e10b440d02d103200b050050080b9405140c100c0d100c0b07000c95041644c08a102440780e094001c1006210706800e44414111480313070b4061701d080402001080c0400d070b030741029249104001044503941450031262211b295115800520001c02e0040c640000c184280030784541524204020000740c60480c000034004041e0340c101900500c2d15402003003c0440c1941c4880c84950400750720000300c484251610002e40c0049004a005d01583c0f5000c1c0c401481801042c0641c42c4a6008140320380c5080100001030103074440603100702100300407400b21865881d01410003440982ca426440340c0c185000035050f00d00f140080c1c810403864402d020000b80140c2d100d01d1500ca003610f0910300d00d5030355210581c0c0c80d200c2d489000f84d0501c82c1404201585071643c0041002d4003080e000804250b0010204581e41d90b16a040250f0004008001110b64140392000c3d0084212140482e00701e12130009103600a04029000300c1c10740c0e040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 677319523 1250 677318273 677318303
    0xf021b010b0f01020f0706030207031202031501030506091e06030c15090a050d0807110622140402130902090d120e032a090c0409020a08010f051009031202030d09 71
    0x2002d00100c40000081c0090106643e5404105440b080e0600514090590200d1800e060503c110b010503142c100c0003904558900b0040413031004520590001c50010b03051070300207140c2e03013040341e1428020700b81841d0701400700784425008821220020400c94052140003a2200c560f0f031070308000d440c201058201f03103a07100c00544c01c1c01008100f940103207000d03603c55560440007400322011146816005280c260307038616806c000803003c0c42406040c400201c071800c0850307a490185000c4801f19092101803004a40b00c42c001d1006a0003250780140382111490420810160140c00a003c444070040c042c1c8004a504d03540c0556101d010050000000d00e080391242603401c04000b140d0100344001c12801554614011070300c408040380c00c0080c096100000425400c810400559010300720310034040d034840020b6040144031440c24030460481c40c0854400144a05108507004980301c229580c01d038040f425501c50740d00704050403020108501c820040b0080d81c0640e4807800d160a0710030701e2446402c0ba4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 677320773 1250 677319523 677319529
    0x1b040f0207060506180708150312190206010602070605090909070509040f0302060a050c07030c030908071e0b0901020a030c1403030a091a060a060c031205100f06050301060c060f021b010b 82
    0x1700c1461190b00c0020514248280a0740000950b980224858010a0400ca040c80803e060810f859011b01c0c06c00408998101c043d11081014101441c4560880e08107a9880c030f8226510880da21440c00456000c002d0103e42d403d00172500703a80104440300b10340d00c165881e000310321292000c880944040c0c03c120213500030140c6c10700c007558010409420500090508040c000810310401600030107102642240404144c0141a80e2004240d54001d48242e55651141d00d0005100f1a44041e5502c58420340451428943e60540703005820690003460b11a106684c282c0304078502c08400d641200808412415540c810802148038088007440030400c17800c1442d0030740d5000007020b0044050b42009081021a48034007001c0f8044410030702d440e8401481d40d04041d1780000c000e03d00580d2007420b040030851050700f00c41e5104101c0f414002070301360003a07813008100d800c1cbc08280242c5c03000900f12002100421441d40102c00703410070301c400041ca442d108100d0800088036042c03903010180d44803d02801360346 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 677322023 1250 677320773 677320789
    0x6092b0809030d080c04140409050d0801050301060b03010e0c131e05100e30250b070c0902090a0b0c0d1404030b0a090c08060103081306030e1b040f0207060506 70
    0x210084c1000b14480c2841c244d400100c0c0140e01900086445407902282c0c1980c80740c0100520940100544411000000b0014415002406214002e600f0000b001400c0031100088134100d83c2201a400380d16110314840305803d0b8041614500702850380300b000b144002d4a40391a4036141c2d80724050380c0c155450002400308003030f4520040004d111003800ca000c11500e50040281d2640180c7c041840c024200240d80a014441c0301404082441032640d50601c410700c0302c58070030725040f0703025442c0c903555601c811070245407203198002099141c00c0001000210030640281000c114018240c2c507490361900c41e20225034001c40c0710080f01e540107100084066801a00c50a41040e1141044e840c00b82141c844c00c515034070160902451580e242c104c40b06122100090700c02600101058450a5940b400c03e40151740004502d85000c58010200140050107840340644040c145c00190561840c04d09081f0034001b12078070040d03006626a00c000151000da4401000058070402c0700041c10b0604200b803021003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 677323273 1250 677322023 677322043
    0x303020705090123130906020d05010e130308060102100e031e27060403021008070807030c08070503060111070b0d0b06130e040507050d0605091b06092b080903 70
    0xd003016200602c00d80604c88030102d40d00341d50403030b1410314950000204e500802c0c00c1558580040c5410480c0081007000d80060101d4591018144010390700c8554500b13004900f511521f1900d00d0001c10350000902071003032a84c0c030200c1401641c0f49040703400d01c04002e4400404ca03071021a0030010707211300b168244540d450303070403010104003170309000d9185a0b104000440001c1100e02c815040321440d802d83d80c1c441110051507000c2c145c10b603407908041c00988022030a84040011592000004482d140b00b88a45c81c02220155920403090300d8000040d1a21792001e011207040215080b5600c0304803d0030004180103004004aaa548450340504e190454164164851103883c0400c0380c42000c01c031040540d0195224034001170a03586951070318514203046603001da500092141101014003109a03c6103220308141e0040d10683c81d0404980c25101c504030007040c0d4080d5040c08154114100314545207410201c03503200b414280444a80d1f258001c0c0950000c0b1000c0302c0000f00c520ba00c1c1014000c0800c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 677324523 1250 677323273 677323279
    0x60503150405010c110d140c0f01050f0109090c0302120a02042c0304032315040f0c08030c07060e04090501060b0703090f062109150e0606060702030c0609010207030803010f0303020705 81
    0x145100c20400d184c41ba03101c44420307000c1155901e640381a51013118101c2d01242183c02c00c0301c1901c0900301046020b02012a007024464030f1440000450b01c250380900411154042034088015095600b001041d840401810f0010f00c502081c07407006803558440c074a40c03082003105013810070201c020294075035040b001417121340d60418042003000510148140424414000c40380c19514107820582d0b107020507450700c1500510100050000b440030100740d40711202e01950354617030341d103840354011a501c2c415102000c070b8030b43c0031000170030070f0900c100500c91806100900104061030701ea203400703084d01c0050704840788458000881004268100e00240300400440e210010801e140003030241000c4a00c1c40803400c0d1701c01040300401d440c0200e9003c1c448995200030a2940a01c400d2500300c02004005650a114030900d40071507200e160080c25100301550040003014929101010301800b90000482e81c0e055102d03003040400002d03d9a40a1406040d446019a002c1d52030f60030002d02d002c0b042d030711a44c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 677325773 1250 677324523 677324537
    0x1a030f030c030d05250e0310060302010c030e1c0c0509070804031e170a052e120c0504090818102c03030408100e010b22060503150405010c 61
    0x1c40d641011003500d4100c25031000018041d030320012805800030543c0207040035a41003501c07502030b4035044a008200688203034115000c400d01e41d5907a604580390b500000e80850b100c0c20115000910a170041405a00080c003801c0d550200c444d64034ce07424070f070000215005942c05500b407259081c03094049a1007460b62501001c0e505081d100036000c1d0720b180c08481c4500001c0c450042c140c40c001c4042d0341000384d4007007aa14076481c101c0c40d8900103220a50380c0e0703820403c005d8162030b04500c0e4045043c070b80c0140003004410f00d52920440241c0104040b80c100d40c030440c02e2100140c1030b9194821080440e0141c1841ca548402c02e10207081503060f0001c01c54882c44a554a180c1800d038400510000c464510925a440f91400942401e45241690845505110014001c19030050120340324081c0d40083c80c1c280041e110300042c06003a1001f101d5015000840585003200e07901100c00c940310080b00000c40002e15640302c80200e424100d403000c02d00d80da06c0c034090600c01003160074400e1007404000b914042c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 677327023 1250 677325773 677325787
    0x4150201180c0302150c1603050c100f121401030506041704031a0702030d06080d111b060703230715020315060c1e060a0b0109030f15020d1a030f03 65
    0x40540040c04060301a00c10741621586a80c0c000d011690004060411500c00e08510241030307800c021f882c0012280750041d038504003213a0030483c405081c1900d994641089105080038126004820078800c208000c0d142d0400c06286200303810414080d60223803024080b149441d09042c0c18440240300940c581d034600304030400100e92100e004045000c00c0c40704084141c0c0360b403c2c040b840c5004608242c800c040c41d01400207090980014400c0c2464010780328503000c6a4272a03c0c854035208070403110f1920030566400d0352511300d0640300501c031092113801c1001d00301c0c0b500c40095820154003548100c1c00d10001680702c040c400c003101c907100103d80c04802985549461080200400c074101b045600490001c1401001030b5010b0200e8000d10402c04006c0381c41100c8240055514041a00e0f4000c0071460300d41550a1395101e503003900300780c9400561002100d0070980c0c80c540b0380d00c001040303214030950078801030808a440c0d00a99190b1400c1c40103510035042881d0402d818008446204580c0d81e100304040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 677328273 1250 677327023 677327033
    0x70602030403121206030204021308060a0e060606070203030403080c0318060315120102091519080402090103120e0909150a1e0e010204080f030a08070807170604110415020118 77
    0x9200003d0702441c060000c0451107501a001d0003690300000c0d8054004520b030f04a5103e00d6500b1004c071403002049800b99250520060100d032500c030700750700041e041440002c0c00d50814000405a2910140031a0314140c1c0d02d44405019400001e46c0c1142508005900c0081d084141d0202171070204c222090b82c0f85040840e001c0e1a21400710280303a00a4030402c0908512240039810741c1c82c04803018000080c0c140701c8080340385095200502c0084a000001d101e9480d0394031070360320584100da0103010601d1036421502c0e107520303001e654001e020800030040d8408055803603100700c1c60700450303041004082d5203e24a12814551030020082494140381c81d840a0612401c40c02d4402c10700714805000034404103400c1e02c176019104a81080c06684602502010041d400000601202d8803550358000c0b1074580d20000c60f400300003a101c800001e250b482004d03c0034044502400d801c840020b0000403408075108602c0c40c039400036804228004912070080c104c0c5902130260b40800c4010074904001007205a4134 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 677329523 1250 677328273 677328293
    0x10608060102060f01060c11040516034512050703120e060714040806250809030f0d0b0307080609010f272402030402041b2a0b09010203060102070602030403 69
    0x1200e003005442800030090210810326235101c3c050103030040c8401c0c50648890768007040190f680500003842e041c1c0917a0100a0702c0700e01122250801c020302c0c00302015140031070450700c89004650149174801803850005480307041c07950030300380340b038072920380359102401e000d4201d245c410146500f00e0704044102d05642c00120350985e121009041903240001040c0c50900c1f50700854016a51a10036070040c40b00c140406003505c3d100c002e03180c02e02c121a002180c030031a0b51aa007078680301d42a901c18081105191907580181c10300c1503c0d0308000400709030050001c0e207485001da011075041d07080320b424800011801c0c010f1103d41c00640b034003403101c404030703566200e003201d02408070f02c0d451850603003500200013203207685801c481c840e12107049003c40c82d156a41c00941c02500e080344200d00c2e0205841824181903404180800d2a032640324620b2500c0004107500208a80d4003d540f8a203501400000381d00c50032070380d000d024a14001030f1645810340002e0300d49200350700610305641c410b010400c009401241 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 677330773 1250 677329523 677329529
    0x102160611120d0b0f03030a05040501080c09100305070305130201020c240c01020919050906040f110a08010914040215132606100803160807020301060e010608060102060f01 76
    0x1070005480d2800040c0c007030818580d012803509a5400040c0041c0b95400ca4110310650303101250381c003e5520940c3c0c10540c0e248074203800700d07000c201c06200c200555070040154540c0136218000451424041c000001c407803c4110f400000803d0381c072814080030f2581841982e6106610001d244004082500040c0da904641100350b0301c180890071151840c0d20410303001c10010034032100c4607626229500c02c0603000c3c4d003007980118050750200d4104e0070805042070b00141202d1001d05a0a01031316400c00740409001045004401305496209040050030074000404204046580d502c030194101005603042d1070811a0b20700b40d0011013800d000c0036039901400440d41c20100c0c044540e40320707811241c080e00c00155034400044810230020310615601103183c1d0301c0b40d0f03500d2003040d100103544021121030440d0090080d12840ea0040c0712801da08801c07085d01141d42401041d0060806007254002802e42c0d00942200d4401d4020030b00400469400405107a00701000f4009820f4614080d001c0d031034240300500c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 677332023 1250 677330773 677330777
    0x90106020a20090702070305010f060e0a0c0c021005070c09050903030609041b032301090c060c0602040e1e070e10030b1f020105011802070b040f0311070303031a01021606 75
    0x20380c0300d8948489088500038414805041d031000c038513100a0203519500680700559055003001c034400c402a420344101420384801c01c540c90903a8540c004170800914600c003441040c0030820300001c003d81c0e254401800b142000395034481d542e040c10303d80b861072104540e014200ea10f06290511606000c0801030b40c0d03104038107135003000e040d0307446080c140200382c107052040c4080305408001000340b0040d4520722400c40401501d2a15820398000d440c0e00b21401c05501421121035024103110240c440c0460007180c41c080e204c050b060545a01188042c0c0e0000d842001d60106e40d407a102104028282145520076590f007001d0100705103840c007244176130392140c10100c10503035205580c401d259140d5207450002800000680107501000c48080d009080c28042c1f84403500008501c84501034243c02181c4200d580301c02010031603160707665140ea00c07414604088052118804021010310030801000c1d000394040d85e404580120150102800e43c064145a40e0454111799805c5000f48200c0700880d00300c0e8064 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 677333273 1250 677332023 677332043
    0x140702010c08013b0c030a1407080612010f020c0a050d050f07021012050f0106270311011b0605010e0c180d030509030d26010617060103060e040503030411090106020a 73
    0x130000c501c4080180e0080300f081e4041107000e0108a19400028500c5a060010104007810003290202c005a104680a800084d200c500041650900070140506011075500101c2c0c486115030040c0180d03082425240900d070300240300502805420401c040c8001c0b240d06000346480c0c590301c5025982d22602201074001c0b840b9001480405105290301c0c1c507401c0102e1420482803c0c10502190683c50a100d0100001c40c0002500038441081c54108452618016960750309840c40d650002031403c0c0200990600a0302001030400c2c0440b1004038004a00c00d00d0f000a1542c103110580c8407203080a0300c0e83c3c1da00c0200703001c0001c1984045c214175244480444001e49100d08524085405105039504035400d030007103ca40c04d0382d2903000400c01c0244e0b5440c801c8a581c402854510b210050703424440d0744001107200c0c0301d0202e045030400c07010b80c1150781072501040494892860070150b0105442c101e501e503000200b0441071102c80800c10940080841d40c824072540343c200000e541e03220306000a400040e207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 677334523 1250 677333273 677333339
    0x2003010308220b0c120a0210050a060b04030b01150e010516020d080d090b060f0a060f09080607080105041d060a0b130c11100c09030b090a06140702010c0801 69
    0x100c59502c0308003841d07440a800a9602c4a9880000d5000416aa8801c0c89400c0c1d107000e10003030440a4619042041e0700030701260503801e038404003502c8060315040ca416030301c601c0407a46070340703400082c009140215101c208551410030101c42214450300c040c001c00c0050005642260b9101080358244101000c140c40341d40707224000100035411804004055240020312203021150031707041000c08600414050314a5619582444001220604026030040c0340040600110740581c1042e10312030341c1c0d482c00300c0306285c0701c9032450b140075000e807540404684d52034010091842d2600403240401d11030424880e0401d65500300543d40d50024118640c402d40711000401ea9444030140507800003911202400980050403014000010718940a160341c011f00450003250300950047d00e078030050a1303590225031031440e11741d940c0c0514080c0030824240104003203a004106603014181501c0a60404802d4904000001a00710380700c000c41c0100b8018960300402540416640031400b990908c1c0c0d1481e2103043c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 677335773 1250 677334523 677334547
    0xa020d020d240c11070b040506070c081002030114030a0b0115020a0503270a1503050705120a0c0f0309030203040b090307051845010209120c042003010308 68
    0x200929180408a02c401d60b101051001d40e04203100c281c809403210303150000008415511922580500c04e4041c904000401c494100340000701900e501540c02c082040b501d4400240c1818005060003c0786c0d50040010300100958403011800041c08030b0080882c03070160f58a02040560502c84e010b06000155502040c841c02401100d9089a020b0f09072075807500c1400c01024030344154280d45e0400c01d03004e8001802c6040c00014041a43e80d80403102c006070707a030450101d010303010050200c41002000e00070b00c0200100380c01c18a0203102a9000402c0029110500800b00106140924100340c20585c005e4040303030b004405c0742d05980c4038010b4a903940b480c40c5d004c80d01d824115441241c00070034107800251818000a4918065071000a0840c1350030380107503039078032020301e160215001390034075008041c0412800b80f0341038a15013480c0005400c1c035034800c0028120b007602c100c40d0080c1741c0003003041e0348081c0740a02c1001015548140c01c00303070412510404c0510390005000041c210240000c0010041c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 677337023 1250 677335773 677335793
    0xe07110c03070605030a06050102030c1b06070f0506061302180409230609010b0102010605011403060a094104080703020a12031a010804030f05090402040909030f08090a020d020d 78
    0x2203001d0300311003486603603010042866000f210382c07040140c50130001003132035807010048070b42d69442400203007449602d549110038001c030500480d55011408200e45800a021001c840b07240e140503001424841c50038906101046d80c0100e071210300c0910400c8840300d10486540d140070304035016640055a0403036881c0620481184010f24264229400c034940902680014190310444c2000300038071140f842d0708016800d8a10502400d80400c00d206561140381e40c40002540e0300400040080908640d035504140c2160080c20203a08008a5150011242401011441c2d105c50320368045440c007664051a480491030050001000c1c1d03540061810240b44c4204550700400d070300a030628400140b4200c016000309004408013482241100c01d80507150b004503803079448ad42d05034a88191700054142c0844269101c12025680710f0b5003130201113640d0416101d00841d0501c652112862000420005045044000c2c0007800c1c983c84400c03600016256856400c0165605940c3c00c41030a10b01e1400d68088 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 677338129 1106 677337023 677337043
    0x60614031905070c021003240e0a0e0f0303160801060c030207051203070804150e0d0314090105090301051e01060509151b060f0f0606040e0711 63
    0x1040703402c8254080f0192500741c0e022045a40000d0303210400d803224800190f91103c00740b041160310740b03813242e00070312480d06114001e25100d0548250f04006140d14030b10b90f2240c000b030f00040c0c0c00300300d00c0090901101c242d0b500d07854000440b461840c1034900c1c0500089824000044441c0980445900981c056001c0c0c11741e9401c1006002d04869440ca003644148001c1110002090104010384043e040382140e80c62140301440c8001d28a400d000d10b020310542600900c80c001a0b0011038090080c00d40700c40c0b164444158a0042e00c0c11300601940f95015400c00040006000d0300c000c3e4048144d030562184181c0d66241c0d202140d05005c0c20200302c3d0803188910700500741e1513111014215044112801d00038120000414505206081c0c1c0c511041840341401c0c00441a0409000f030f40c06441960140c0c2001d01e042c50308a80d044010341000103100100000050001d13040c4250414 = true := by decide +kernel

theorem cover : BRFrame.Cov 677158273 677338129 := by
  have h0 := BRFrame.cov_init 677158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 677158273 ≤ n) (h2 : n < 677338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
