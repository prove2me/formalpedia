-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1791
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:41:22.157977+00:00
-- url     : https://prove2.me/submissions/298b7844-6b0f-4b0e-aa6d-0d658b4f278a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 321942446 ≤ n < 322122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 321943696 1250 321942446 321942451
    0x5011d010311031e061e2203030b030d02071a03010f0603091e0b0f0a06060207050415031703090f1f05060301140115120b0a230d0f111005040510020f010203 69
    0x40c000d41810b00c0e1000c002d84034903120f503c04041c00041c1c2810300c00c81d088610f00407400c2820f40c4a40c20487e068130b040550280c01c0200707034150184944402d140c035942d80032611409943c41c0c94180361240c040b2340741040d0140020301940742d5103c20f014041010502135485904003074801d25982c008207000d1031264820001007641564444000030410030b46808c0e0300c0c1e1450307000c01184010840f8a00780500250f60740c0b81801000c1c000e0741e0b100300c0d100d0f003005110422402540d00440c481928141c5c01c06d0311b8100c1c3c1040c0c504040b14840e5950719942202c01060324601e00d900c090144610310341c80602c0102500c03003d80080e425560340c425814401c5010700d140c034060440c00c014482503150f42c5800070411000b800d01d40d05194940010f400b45643d451000c10119111b10170a40c0403141401e9003503030201543e4200541c001c004c282103a081000501004e0724250082c8070040422046506102400102e03691020005108000c00d01c0a03240024480c885c038903143c07048800810021322241d0072030748203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 321944946 1250 321943696 321943753
    0x16030f020a0c03020d020d0e010c05011410050a06031a010507021201050403112e0c050412030207051203030f040b1506070c1401050c030406050f0903031c05011d01031103 75
    0x9032035015080c9134041044451042c4244020203218402c5000204002100c0b900035040000c0020b4003070900c00300f50000c0009040001600607507050125583c8022000e0b0b00c0303403a002c1c80719010001401401380c071070845500d007519a2408810600001100c07103901508041303034080b01ca04003002120000b4070455100764440d0701c170202c40600d803607082031904400c001c02c43c0100d000d80b803148047d4124009400c0c2c82c0e035034a80c07000c6041820710708113035224040d80c0c0103446c0c00d00040c0c40174402c0c0355000440f9811a802551175100d00c8019250454032848115201140f40408802050002d141c104c4440d50044501d0f00d48008087d0175400241c1c0c5034030020081d1160031024006101140d8000130040800c0300900f4190310384622900d00d99204d0043e442040c05000c0007091441c0091000000c40780d00620080903641c2e11816220700c100000d80c0c135640c5654840c0b80000200380d451071030500f4082e4001d81414403040740e1071a5240e088816500c4d52a0f90140500c030010040c0140d14041000312622 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 321946196 1250 321944946 321944957
    0x7020607180806190b0613090213170d0f09050306040f0c09090b0f0c0c1c0c150f0f0b01051c0605060304150c0e1e0d05060903180a06020616030f020a 66
    0x1440c1c04c000c1c4c00d0f40c01c1280c0080c401c00d03041208a40041c0250307004403c840c841200540c4a07030f44043c59a041003100e501000e0f04480d0316490420901e004201c179560380c80c0d20745402000c03032103032001140c40d1030b003d0241e150150f00510206003c42c411445054003188117070004111381d6182c0d041e00b0261013002404859888015050040c1c0800c001c00f03290784403d01030760aa0134641da6241103a40c40c0703041c840e012200e000a204d0414814403503075208460940100c199100a40d00982c104000c0c0300e0044040c2c010391605d00014440368690042601d9224140c0d1103905049001e150001c0c9103513080b00c1017000302d030f580300d00092580307030076001d544620b0264a0507402c02d032081803003505680030742c1c040104000e0307140340c0202d2594900e00c0c0c1c00b158985094210b0040c40c0708002181448071800c4d80901944101401c00c019036134000001c2c01842000455806929881402d01070b800549009990158001100140f2091904004140070840c00c2c580440d00c3c052401c000b02c00c0760700004a2100040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 321947446 1250 321946196 321946231
    0xd050408010e210310081204031e0f0f1707080901030b0a0b0a1206081b1305041505041e140c010c0b0103060e1603080711010e0a0302130f0e060402100807020607180806 74
    0x1a021000a40c1302060f44482d2101cac0d2480da603060701c2c242c00340c0f0010b0032541400111010b2095005224401040d2004c60690312100c40c10200e6158000a402e035001a0512079030b04600d04103c01624200c4040e18034040c00c041043c2002d55400d081c16030050000b542c0c840c800900c00000f00708110343c000c0c070441003100d40d80c03000e020b016501104000c14951a0304000900c40014015500004020240b40b000600340d100c514050180160700210300003041101c180000500c0050b90001000101e0b10741101d05080c920401502c2c416001c64020b0488455640100702060850f003296034595054000c1d1900d440c06482d00d0103016141e50001d03615414007041007010010308802c0e804452009080880c1d0781c00d030f14000280501401d0100034060310141c0d500c03200d1209150092401c40c645420b0038000b0b080089a01c9964400888007644100000040b1480144c011000f039409842c1d01d03806000c0b20754a820381611512403041c0c032a0301508a0800008410505204c0380703009041c0c4002c441c00c0341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 321948696 1250 321947446 321947453
    0x901110a0803073b0d0b071701090c080f0603010b21010c03020306030a030c060618090204050109020a0206160903020a06030b040b030d0c11120d050408010e21031008120403 76
    0x114220445070028245900d401e08002090220701c0d0700d441c1100080c031a20401c3d0080740f003126400700020181c407090401c1c1f142060b00400d0b101c4944002c42c2c5800a0f582c1e0700c0f101c0300240c48072a510720000c035843c0f0020030001070500c501d03103a005d60080c0011900702408404516501d14208403040e60510500e04080c22100a00815a9480b6686010f50841c00c1240000b51900030000009062191000c07199040103070b107070440002800010300d49100c1d44a03402d2010050480c42904a11031442c04001151a41c1a0310941e52007100f941d0040804e43c1d600421802c10810322600f01c4244140302000000607a9045482d101074060380d030b004070f551b094020a1000340d44504c440248207801804404e0480d039404202d0311140b64100d101d04440d92122404134078200901d80440c10320380100e0b8243e41981c1e4100005001b2600424000c0140703202038981d0645515014843c00d04202403600e9072008140744401854200c1c9415000045559513403000914120302c030803951400150225041050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 321949946 1250 321948696 321948707
    0x60803031e16080604020706270218010b030f1b0304081b0d2f010603060516110709050c0c010501030303060807080601030b072003040e01140f0f04020901110a080307 73
    0x30001c2156a04559612100058a112401844c10340200d03800319041d01480b00d20303004801030205150011514401c400c141c0640e901c080c2000b81e00502e00243e140042c41820710b103903812a10010b42246c1951034403441422a40c9020b00101d00d01030001d46c0352040c004aa40085001e41d1003028500ea9031a20810310b0b0160001c2e002c00c100d0b141e00000340040080b070300300c0b000340c1e10480401c20b030044600c144070010494a15000380c01c0c0c40ca42ca01500801000b409a0009012322a001d070041072986a0250465210440b105074102d0b58001000c200020300450308101d80118520078141c0c2402586c10b40c190846100b64403c1e0002500c45100708034400041c44148080c14007200946190340c1035072644050b20307038050701c1a002c01180000705080240c024104030502c0882c84292542e483c1d41c3c3c1501900d01d079087c001c066045403400d403281ca0a1030034a4040c041440c3c00f410b40b00703503060203200304002500002e00c0541409006200307400c035410300b40280704103244540d0f851034407414012002040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 321951196 1250 321949946 321949951
    0x31502030a0501120210030f0e0708010507080105100e100309150b131a09061903031d04020a02060601030b0622031401020412080d150e0601030b0f06040506030a060803031e 76
    0x10710350038030080d00050b80380d035205181c507001c087c203002c100b020080c030100e4000c10320300034581854007030603101103030750f12040d006280107010540d9a05420707601d1348204003070384860040c0381002c2820b039000c5800f14100100c0d02c26040140e070400050b03640050300c0340c4034034070b86c102d07100d01d00b155617000c01c1d290303901d002c0c80340d0311700b00349540e904010200c2c81c1858211800c03484001c1601c610f004100040c03580d40c2d80c2c9904020415407500340346003a55685405000c0482005800c0b1441031090703140085070401d8400c0e240c282c64a640245980c0e20b84200540007082e604000581000c01048848441c0080c40700e00c82c50001b4a808118980380345080045100c10066040040d076401003004100c3c00484100740b1281581181c0d001c0d83e40c1004406510050940040c0406122a00c140000d42c40c2d18242c0c07407600c10b02080c0c82c1031017001c0d040c5042002c40a0b054416542c091030900003489503060500195a00440c01c000018043d616401100d01e550400c58040d01074403a410121400002001541034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 321952446 1250 321951196 321951209
    0x504121a0106020309100503150d05010f090812091501060e0f06040b04080c06090a061b02030607080103020306060a210c0b0d1514010c120c0b16091403030d0e07031502030a0501 78
    0x4c0c29414075109c01c50341e08044444007403140011218000c1484001e40c00007400e80000c02c0c0030004210b0b64904144242c00020007000100b1504000840180011a081c8044403541044c19116030a11105440100001c103403650004851b203080d40003600c426008002400f152100c040d01c403850000058a0f202400d101203014080c00c0c480000b294407101c00750030650700359003403010f1040b09178a519040f00209a002039418400d603814021155048840603059030300030b03020ba072001c0d514141803000b007103024070488958160482e244410051001d118404062240101001c11075403800e4080d541e41140c0000582a9a10f5404032108850503c01c01d0091000000c003140d1400b81030006482440194070182055020340303000007515125143d00707540701d680800800304a003002d0f07a80c1d188000c006d01510000c40c560380700128091100c80c541d032443c00d4000300254034102190700c5500261480c9a008802c51244480200c00905c00020002000d00030000045c0c491406034403050a942c010b13800702 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 321953696 1250 321952446 321952457
    0xe0c120f0c060c0d320421050705040e0703080c2b050409020d0902041401080d0507050714270402040b040513060b1c05030d0b010306060504121a010602030910 70
    0x1503035240c01308103070192500a09102da540111654041c0c014807440c0d001c00403041443d030158240c400b00c24064002c2c0c0e650f1810020001246030791b51a028507a03044013a2155000c514200b10526158000e55202d42c41401510001c40d500d940d50301c5282c200c003072004000e400401d541c0322026804a0390705441f05030f030101a104041c0000005d031003482607001c1c86018540000c3ca003440c8191903080000c1030380d40600200a0b00c0c440b8944504603a00078040d0301214010444d0100702a8070800c02d0b80c1000750400c01508020307140c00d64030300d4100100612142c01540c51030b41e086100225000d1205d40403401d0360321600d94078040c4100000c0320031100e4141d02c507a107040c003070108002030543d41141d41644624006440c40940c1c0000300c0c0e81069071031401c540c0c0c07140000d42080040200107401b180c1c504080030700100c210800150280e8100c4c3c01141c0010b0024841040155a41250f00786028000c040d40008900c80b00768402d66806e0036003200025a20000d59146582405424608100d2691414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 321954946 1250 321953696 321953707
    0x161110080709090c02011107030503090c090603030f030a0e01021308062d09010b10020313090209300a0804050111061b0903100f0509100e100e0c120f0c06 68
    0x14107401950301030030540c140e4500c840f190460003540407c01035031240c24560784943d5149001860b592046030b202100d070141d040301c4491400c04a00031805003200402960070901c4617064034086420007800c9040d0140c540d41c2000701e0283c00c0c030080080301140480034900a0800407042e24024001d00407066291220402143d8945c42c01000002c0100b04185200345446445107140074011441c003c540c07250403441d10045481d0004010041c0f81d0109504145980d50303940d10300228028000903680115039041d2580380100c007100070091540404a01d60000b500d030328081440d00c1c41034041103c40220014081c4150341c0c000122000e149444001441d682c6010030326140c84140407008140f41c2203000c18031503d41e40e01800003100481d4906000c0102c070b0140180d02e005007900340c4840701c1da4040c51210100c42e1b100c6005044800e84918010300800801030b04040c020050481040d03107500520500500760b03903a1000415030031000c18004c080c9144015901400d00742000312591040c40c0c100117 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 321956196 1250 321954946 321954961
    0x30304020a06030513170d18050d050901050403080c0a060e010c020a0305090102030c190309080604080301060806040b0306070f0306060c05060105090408090604120b162316111008 79
    0x4035009440b0785103004a805d84619401078002100402c0c010040e202d50083e000844140f04060440c3e1005c0d030005000f410a4100e580c1c501e00140e40d0040e03d40d8000048150f034150050307005010035801858014606030307aa031520310b0160403100c512003894110300c01413001e1000703038081c20011040350b0000300b15000390580003a569403035000000301802008540c000c0568020300c01c0d60079442e0f001c1c041d104654070761161140d00c94102c1d2000c802040e60040041401ca4000415900c10341d84412840d117036034207000d400c0c0e840c0e5000801e45036015403203d540b0704148d101031008a0103241141c07501c0104031340e66030b00903040c0d80054121800704145407500d400407860010f8454110b62003910360300b41035250303411711004501c1103151154001c003001500040d400d451031808031038a8020107040d002e07610f442d101c010b0306c07249501022000680f00007071304880c85550b41d80210300b105203c101d1480d12008510741860703001c0441043d560141c003c02c480403141018030b0180b018042c0c2c0c1c980259075240c03a19 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 321957446 1250 321956196 321956209
    0x5090a050123040f020705010915060b031b19030207031715040e032b060b03060f130608011a03010f0b03060c0d1104030b0a0b030105040c052202040807080d0203030402 74
    0x60040d80340208900d0011010348860340503000c21000c0704019586c440035400d00d036010304844c401c00c07540c00d411710707400d46d13100b280911a12003981c000c0c845091440d01c4611000b008801441000070080d070701040002081300501c07009003c8031070b9940300561140000d050144c4410b080c1c00703c501e012035401e410018201444200c190607203004031000103da0080b925018034500a0820b0034800c01216201d00c0c11002180900f0b040d0340d100300703906001c456102e401140d29400700740c4031240c10011288240c001854420340410f081c2c80011000202e56545501c900c2c2543d0010072000201d0f007082014003071604080c01281c244419035002480003a00050110340d5407207004000180158011030407094040d0541c020842500022a499448130b40764140319002000c00d4030b101104910340250511141418040d03980b0483c0c029400007941860803003445820f8000300c90b0b00030491b0b0040f100344581c452a102901c003501005000b800101e0401c12120702e02407150032003600b55030040c4104001640d450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 321958696 1250 321957446 321957479
    0x3030f08420a08150a020705150a1509060501030f0b03070b251109060937110a03180f0618020402071208010f0602070308160c0602060105090a0501 65
    0xc0503200d80014001598110360911080c09a40b08044203400510b45000040000d00c200c116103080303610383ca612000c041248221030b802032268000c0c22405c401c1e40d11503800c043c0d21541c000000700342d0004564080c1d0003683d068006911503940c480c0c0c140142d590500c035803181d6941d904010032284140b400041d6035481c50340320384258403500045100309004401410000d60100303e41c1c0074000800c41c03070440e0002820341c04483c010740380c1c2d10010302c42d490205030280c0200b0164000c42600300c0d44e00c003981c40071003201c07409200c070247c0554060b0750f480e2140710f44880042e0320030007992210241e03d002015503140c3e1400051600418200301e0125170480c0a0076525984124005401100c0c01c01ca1844407401e03600c081d5011b071011803284d0038070500a0b558241c08a50b95074032000f603a203035810701000013800e002da600103904c848802d00018401d60000c18070390b668400c0102800700a0395813902228210740000006802c0000100042c0c1040c5d04034a40113500304600b4401c0d9810003a20311000e6009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 321959946 1250 321958696 321958771
    0x90715020601150e0907020d1e05270d030806030106060e0112150e0a1508031603050702030708030301180f0c050a120b1c050c04050606190e0a03030f08 67
    0x120182c11401c6000b050f070b1811380d2102902c0440e091604400c0692200f202c3c84602c2c0100e442d404200c0803246104042400114890b01e4403420f15210141c1c10300840b1014240381003440c41d002000581d540e0b00301a5002942c80391b95012628500403090601f5654642c0c0b103001400110090b0380030300da1300846802c6011035a0707000000c1d0501e400c051072624079034650281020010003001e00110341143d404c500350307840070001c0003080b40340d0704d00a1658900c81c5c011441c0c0450004180350000a1055008150060006040b51051070b02da012860440c4e10a030300001c040c5000340c2c1001010000340c0500c9408403441e0f6003c112003059004080e11038450428403908100412026140d564050350000e4040301020f0000b8850f441d0540c1d1200ca0325400345004d0f541ca100f55444c810691506010300307031043e2806420542030500d10f80e442c5010200811280050014000303c980d02900c9010152000f14005e50b07a0300d640c100c601001500c0100003410180c80e0100c03c00c0c95002a80e50122140303a00d40c1e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 321961196 1250 321959946 321959969
    0x601030807050a0b2e03031b0203070302040f0b0102100b09070f1b0c05031005060f0904020319052a0d170706060801050108070f0f030b040312020a08090715020601 72
    0x814030b0141d042034400700e0001c10a480f150140081c0021100c0842240c0c18403201c01c50020016089003110403441e484002c0005a052565070b4425400319840e005861001d42243d03512030700c90b40004d060b0b400110f00d500015a1300d82c2c03000300660341084030400c49482c0c50400c000325105940804c2070514020100d20500845801529840f8820179440108251650300c020b882559450100d6584110713100f003512920414412898581d0300f4890140549030041c100c02410300f046040c8680c0f5000108184da1501a02d6070170301d040750450401e400c22610860141c003c58113680884010394041241984204164012058075520fa0490302d050107500505545003510380401880c0c110321616000a02460030030000054001c41500541d041e90842c10a868100d40ca50a40307516256a07840b5100c6140c110301d50410100d920039401c036070130500900d080981010486452070603a13003c0c10032040061088002c10000704c2003404101e0281c003600700d0b00800402400002950342ca0107000e0b01a5184 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 321962446 1250 321961196 321961207
    0x40b310e0402040b130e2d03030118060f0f080d080411010c020307080304120605180d050c0111030412090b030709170c04060b04080c0a0b0703081503011b02100e06010308 75
    0x241d4a00308003214089405c8244884100582c155444074160480462055060079800421000003009000142d41c118029403e680c64003840c29001e28110790075100040d55003401049010803e001032000c0c25101c0303800300c90740c0d140c11252803400700342c000141c1c01c00c1641d40a1000040190000350700c45142417074180c0c03450001e800085d0901000fa44603000714440001c1c002110a60a4803800a01e8061001049550b03500460507003600100e4410701c1d150f80100001d091424042c50140441d60108400080e000010000070381066000751030a0b115511114030196900c1d50003807540014061113882c00d070841c101140007805410441c0124400c0d00340080b000382580034100080f82d801e44005200340203490b81c0300791420741c540c424000c50000340503c410782c0d4040d0400089000840368107130001481c0c001d9076281102c82a030043c0030358801541d13440702c01d8096902400713801310506070301104d845964000703034020f46442540d807804142a07081960342042a4804101241125004400e041d0780300e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 321963696 1250 321962446 321962449
    0x2041413110a0c110405130807030306050901090605040c0e01081b070203030f09190302011205070315080309100c0b0412050c062401021b01030b06040b310e0402040b 73
    0x7054401c81c8007000c01070201d00b001141c2c3c1d00c0a09540311600420710708a120941074184001c1d164120340d2007040d060b4120903000029010001000f516010f0719000410a448400144221200707a01881c0e03038a850700301c203011602d858455054081201d040a0301109900e00001e445884003d24816550190720192081002c86e402140e400a42c006d0a9a96039032400361040b200790042527000b8000c40360300c460418800c4607a40f2b0036041c0c03074058503209540c20340c045800c800b91100400103c00c16495001d0484217582c3c1212490203424030f840074640f2043d4034014030020944100104041041054411003c9407220b88a20341043e0800c0d000e80100c8082d00081c0c405114410400300c1a01c40c0e00104a062001e25134035000072011070119007414a408801261354502a0040540e048035010700302a07107600a50003503181100240080e4101a500c4003c15a15001444100070b001c2c820368201721000080712030328000302403401000385030070b050002c02c07595018018030081c0242d039500f8540300f59 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 321964946 1250 321963696 321963701
    0x16230d15090f08030411010206090303040602070c030f0c08010c09030c0e220c0306050114010e041d100b09060301060303021515060301030f050c09070c08030c0c0601080304080f0102041413 83
    0x10315040721451501c2c010525022116078030071941521040c2409418992962001c00c01358003c001a000840c110340b0f940e199030703000354402d41d421100004607560010006105022915050340030b0b01620130172504c0c00380300a081d5507910721041d080015003442030000a19007090002a20b03070b0101603101c240d50b0001d10820302140e4842422200e40a100c0400411407524203240c282d030701c58a010b00091340c0e58010400206c03210a03540c2d0200e08080c9159000d8100382d80849002e10721608800300c01501d4003005420030781446d642d020219254080031041d42411400302e9007082c400d40080042038503549009403100d4401002d054408000d00104180502c081e4191003e5500240903560f04c3d60342e441c040a012009540440f51802544007003540c52818a204910900c90360302c52010810b06917940b030300390f50302c0200305442d07030b1500f803041c0040094100142800780c03044100855442e42000f01c3c561030a80c41c42c40e81901c0740e00411007481109070001422200e25415600c8044c80c01126030000c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 321966196 1250 321964946 321964961
    0xa03030e0c0603040f030f090b03010506090301060306020a03060f050a0602060705030702070513050103020414041e050109050a0b0105130e0304151709010507030e030405031b030f16230d15 83
    0xb0b01040100c00e0009001903542155030386403290b01d03a589030406e91f4030700f82e81324041481a2040c104040c40100681e05046005182c0c40c903000780000340860300c03540d80c1d400700d80002345404002940c4039428402c40a100711240090b000883e0b40d100854070309900290f40b084001e00380000c100000c00412940c80c001c00400d0701620004040e011150000211032008040922059114600b84000b0b080501e801a00640c0a81d03007108544406115800804400103900c01c011540f640d17a41e502600814030078001c00030303003030720803200803034194504001c22070311200c410000c0011340d00d000c161065549000048800302e5100d049145611030300300c0c201b5030307015409840030f0321f81c6004513040110b181030650100d440746c3d9854a08018028005000d40c0c2d0724004c5004054042d0310001004080b40c5000203000c40c0440004e0403904a81c0042a00504040d800c07030449840c0d250603803091207041e19000c01003080191505143c2001010b14000407407031228000f000c0c2881d05502c070403000458a603002500c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 321967446 1250 321966196 321966199
    0x7121103040303080f150a03080a0c08070510061a031506041d070f050702010e150403052b1115060312131403010207150f140108030a0e03060106020a03030e0c 70
    0x985469a07414040c083d558100c0c0e010500c02e00401c00251501c400102040d0150700c0505003201f550305580d5200c1036540124904c00034082c04041c041c0c0001c1c2d4110080c50620b210b4006000c0340d0269020410581340c4a400000c0b540c01d005e8800301c80d91740c2e080c0960b544200300b070058089221201010032a0380c4103a40045003440d48200054400c0410807190328007a0240e50f0764a1811100e00d00308540d41d00400030000d000814081c4080460b00e060550511000180c000311032400f540e0366034981c64200342c3c14107010198040e0b581900b0a02c08145810b80601c070070309001e0b148a0f00d541c6155111070f01b05070110011407422001c5105a1010880102d0040c5044048e035500c0b0403c030010f614805040c071410011103040c0c0f0703000070746007030600940d9000c581c0a00e01c003a00908103016040503000566407842480d69031400c500d10036450600150003003d503800599076070721181030010017141c03560303102c0c1e806940220010041107600107909405650140740000f440300980c02442d09003c2150b0065 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 321968696 1250 321967446 321967453
    0x1120515060d020705060105191e0803070f0507050105160204020a120609270b010b030a02070b1608130507062601030516090b01021c0e0901060315120206071211 71
    0x4030b5040c0c00c80d034010710f8410700400c101c98050307a80e10700300000d62050080940010314144070401604420344040700c02c8240d480c6111103129143e003c8145142c00c401da0565000129440c101e080c080c2c24448580600401e00c1c01d01d02d002c0603203c4407510200028402800344d580050786e072850302d2043c1c9504003d501c001da400d0121903507844101c00542404880001101d407068500038021b01c2d41d0504550045d4410130550290f0310708610399400e80c04c01081140d8664003000180c0014546801d25441030740036074008101034000000080c20404e009208a0b04501002855404a070340007a040003242c40300c1c270303051900320703054224003040c0081c06050040702101078001000300140441c04442c106000100b1101281c0d40d00603110540d0700301484070340076030031032044400300042004081c07080401c2410020b0039030500d44003007246203030f090303203c04002562422606a80b4070303c003c509005101c0c81310601c01103829030f00002d40610480600511070032200298070301c0d15014110349030030710440c6000ea = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 321969946 1250 321968696 321968707
    0x31906030f081804050a0c0f17040201081b12180a110f010903050304290a27031e021203270a050303030a02030405060f070f08100915230112051506 65
    0x1203009000156007c0001c01c031280c0d0091a141d100d00b1455801890362201050a82c6590300190740940000c0d11030b01d2050088152250b00c0030701c01c4001c1c04011040c0d0651902071510940240d541826030040c18082e400600502c0c02007400482000721000f01101c1d18038030105000016900c0601a910003081800081000100e5940c05910540c1070389640700352100d02007264441d403265121b0001138001003034055000b80e45640e0b0050041125a40b00b09101e0503040d00d0361186c0044840041910920003651015001142032094040c1e000f5103604000314200003050498010440848040003140860304003501d003a17079581c18903480108009416283c3c2e90400112441c081c1d8402c6509031064850301340411000a9890b503551b104110641d00e04800c7d10070683e0880780d0782d20103011030000800f10600402c100c0c00612420310103a40ea6504c0d040b80c0c40c0351810038042c440e00f405000f00d1580748110708031240d0741c0054080c018407007060702c0041c081d0703a02110510040d020480c0c0e03d802c510f02240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 321971196 1250 321969946 321969961
    0x10305031e040801090507051c0b131a150a0803030c090d06180503070318050f0f0d0209010b0702130212061002010e01021305090f0105010e120a1403031906030f08180405 75
    0x8003901903420a03101103032400c41c89240fa009c001c400d41801087c0e2400e007c005180300244210740e0100610404070350394005501c1210010005042c2e48002010844503003c944510705a569400103000f40d1024500310b18080100d04654012200d01c81d000707446032150181004150340c800e0b59103202c038040c0001041582d0901c00c0c1c1d00d0300201c8085001c103580d43c07294002c900c107203290721007102c00c0141200c2c82d81c01c2280a10442070448205160800624400140141d0391407c182d8064030382400302c1a01d9688034010030804888190410310640c0c030401c280711220005080081d8840e105550100001d085440200c0c0140305007646500a1f51000c42d0514a0b01d04882000f801c0300e43c00c030760540c05900c400b81d804101c00028480e090224100c05241101810008010081c3c00b444c6000e6904d290401d81310401340e4116240b046469070000001c0200c01512281314400400071542d04002e44d90469407900201413170b02501901c038401c04030783c04400d00c150802c0c031340c04010058828000c0f41400d1a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 321972446 1250 321971196 321971203
    0x40f272306070f0c0b04021e03010e0309030c181503030d0c050901030f330504090803041b060806040f1b030b01020f010209150d021204110102060f010305031e0408010905 75
    0xe52140004804510300f855040c81003410741c012941040707138005545c56560070801200b006540b50707450400c022000f1307c0d00b59020302c6900342c600d0800003e90741d46e442e480b0415083c40b00700800144607048000313088a0781c00810f4082584140d580740712260108540300002d18600a0f10b004801081c140075038040c4142e03215020b010031040030303201404050b580030158000d0741d851102c000c0751003648000002020700160340713500c80c41c001a621070701a151128003107016143c01c100d0603900d1060010602c000c02070083c0c0d10301f072980d031084118041d003030078900002c06031240a40810b04c01c9403a500e036003182d00101d40c03104010692a00c0da114240c41040006000381030840051800350080440802d04044103000f207c81030080140800d002d80c074500b85210b5607170842c0c01c802e4034541d400d100b1410039107410700320913018a0040c01054908026407000a02e08640101508242242c10b00100001840002a100302c10032518401c0c2c0c0d0329180b20031358050790003503500421081d0b0070084000c0c00c1c0400070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 321973696 1250 321972446 321972451
    0x7060e160306060e06040608030a0c03050d06230a080a0b151002060f0906090706050d2c1219050c0a0803010603060f150c020d260405040f272306 64
    0x115a01504d56a4102000b0032600c80c0d00c81d960080d0000c01a003180d1901c43c0b00f1000c0161b12a0600e07505040d10388900e281111100d030400d1084100002c20480d400030000018075510034111070b580301050400e001e05880380b010799002080c0001030804501549102207045440c003c000e0310f0030440200e2480000c1d43d50605440a1150341960808541c20001c0031941720b1240c05c50000610545181440807600c69202d00481c0e6880360303880e00c2c2d81c02e20240c403a56541010b40003042e0070300f0b00074103400d24a050480b895013420308501e04000b1401109404441281c40c403a903810f215864042068600b410507001210042001c031000001145207030b090761001003034900d440201200103884008400f1a441c500e04c000001c10440f00042c0c0051400c2c925440e6018400e6004604204481c414440d6000404200101d0b0000c08103003030081c0c1c241803060300351010200388203201e1031702035000355602c1e03000c42468980c1c5140100164810310081c1c1100e41000c110540754981c0e21a140b00c203640d10b07000103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 321974946 1250 321973696 321973709
    0x50307051204030c2913020a080111070507060806030c010327060c090602060606030112170301061e02010917030a090503030a0504050c010503010e01290a090303020c1507060e16030606 81
    0x144860400460010410440156420356011764540b60510b003222403000c0803e080b6400b000c0b0410104103101c0a0240200e08443c007103145481e00c40da807030b00300d040c041c454101c0010070100b00d0400c102540d0024803a40c84078802c4c03e0014480002c04c0e909000f00941d40000020700580181450030030485074420000f001c001c0c0d80f0943ca00d512503c0482c0c44003c15a00c0c182d210b0070070b10050203c40030800f11200118030030f41c244400d6002050b205690750308242c0c05900400c2e6007450070000c400742d0101c500c1c8071400b584000c010b0000503a0310304113612142540c84804200100000f80b8445041d4410380079160004126922898080c007884060701d0101e0b000c851501652551308800d5000d101a02d06039003031450030704040d0382060052200000426601c0003004d44000401c00b1100c1110002c2403150001c3d565200c0c6039045040c040d240a03070b81c034152030092601815041545010b00c050701d020755840f08020079140580d07800e03545003001c00c0d07500a1010b108008000100403c0e6448401215107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 321976196 1250 321974946 321974963
    0x4030f03080f06060711040f0b2101060605121b0904110306120106030b07050702010201110706050a0e030a020a030c080d140f070e0a211b060201110405060406050307051204030c 78
    0x441e0000e1003a98040c9017030041c0706450201c01c22245191030f411480c181c051703c44e000540112014002001031400c6010340181807030548400c80740076002e00a540203082142085841e28042c5107080e140d40000828010002e440004040c82d100000c40407130b54441c50050081c0080d0b1102200f0610590007550402d1103950091014080148107000743c00c00c40780c0010102c042a03a03180e00541d19680b007100c040f8119561543c06e59403640459010341202401400000344a03c2d002c19404210b624a00c156101c81c0e0044c040703080090340c00180541c00d036526103003d200710180c0740f812840741d000d517240f01c40341c290602101d514201000c01d4028070440e1b18104601a40d00c40b508242c3d19030001c0081c80381c010100440601c0240b03000412440d920341d09110b0340350482d2554481240c80480e0741004540b0500451042003504d82c2405504c08401c212240d17245060710b01800185c4900c1303035214007001d004010001404071401001611400c8c42c912515610b14500b13454000c00a82001e04100c0f00c068 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 321977446 1250 321976196 321976201
    0x10b0c0f06010503150a06051807080603060603030a050a050c190b150a0509091e0f070f08030301090b0a030f08090103050a0213090e12040f081917070201030204030f03080f 76
    0x40010800d040f00c0c00903000d0915848109480300306018000c00c51443c15850700c00c00600c54558900300711240354103007655251800c6c291001000010301500180c030a42c000002d025640e50088100c0d40094031030b043c100d03035500e0703a894242c4850084804099082c0079181c01c5088003059026440e611501c143c500358010b07500c0c41c0c1c00e0140c004070f01c1211a0400b2040c03600780841e00304480d070240c01c1039054044804003100c0c00f400280003001080c10b410300390005400164100070030411240645001d5505c42c500d5410f15480c40d94a0005105408515031161601015615410358043c01303560012640d04940300d080c1459041c5a002b41c0640e0b00103490200060581c0c038a62080d10510100d04000010b41d40c074000031980580f20410320340715140034044400d400403a0150051005240001c1c2044805103070110340381c10a20901c49409001c109000c911002030343c0c094103036a071040f000b05d01a0b2110080e000480007809250070090403050002200010705401103076051040910200101595 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 321978696 1250 321977446 321977473
    0xf060b0406180b030403051c051807090b010c110f030a0305130b18040c050f1c05010e0c0417070306060e0a0b01020c060d09080d050106050301090e030a0e13060e010b0c 74
    0x20414802d10843c49424408180081c0c400c0e03000344407524030004c0541c44401d4000090045039000c0c0c030100d54400d4641a80500a0f20038486100141085d4404005290001e400a0030104203400000e04006a2041440660780c884403444103e43c2d000d02101c54144980c80c0150540d440076850b08100f0200000001e030820544046454402c8810f803040c2c840c000c19800d001c0038201e0b03500c2400c203000b400c0c1f004038900a43e0178040c00103456824044544d030b680480100c2c0450300117070003100e62001c000c410400455022421201243c1c00340ca809000d1a0104548508199860700b000785468181080002d0408403850441c2c01000301d81e904100d14890440160781d01e1020f800031a070400018405112a800c0c103502950180340a01d0003e0318000100303201100b02c40c0c00340c2041c000310f8804401486509614402c034648494080000d5181c4503c4082c00b40c50401004142441182060500c1d620071005030448402440103848944071544c5465141c50190403400203030138540301d8241c0140d400f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 321979946 1250 321978696 321978737
    0x20f0318071208070602030717190b090709050613050405070c11030a03122406020601060216050d0b04050129240a030209030a0b0702010c030b030c220f060b0406 71
    0xb25a07009007941e00d083c00301d50701d04000c0d41004000f1400e01c0b41e120454840c134114038030901e00c81d4502030103580c6c0da003030036165040440324041c800c240030708061002c00c6003040c1c0000c1a14142d52003195810345510541030505c0950341550440307500b2600b08810f00031100e8100351520361080c401c0175143d83c05203a0200341665640301c070320050005400d1900c50b00c8205a1680f081c070501c2d6900b04401c111030482d40c061445001507600110050b4468001080200d6051210140008603050301c2c03141c051400001034a0340801e944080d00f04038110001c103017040801d52000041c4000c03401da20441024184692818012000c000790052913980d0f0000c1040c1c002c000d0722051510b240380030908045829070120002d401060700c464042c4141414400030409002a01e031003640a54000700e501c482000c4000e05a0b412032020700c1c0282e2000940c03002543c3c850081030600a91400d2401490303003040c1d00407000e8100030102000e00352401b4004a10908544010410b45206440d0702c40034803081c03103c00c1039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 321981196 1250 321979946 321979979
    0x6090b120a030f0f2007090c020304080307171612090503010209130c02070305031c1a242205040b030307170309100e0d0906030c090b0d020f031807 65
    0x19070980c030b0801003a40500f60280c04e01c00c2038a4142900740d5130800c5482d08000f14907807201c0503401503008100d0150310b40035034003011800d807018504052130029080e0381d07402480c5005214041d0928602c0480000d601590300c5281d0b4090002d65450aa08145440c0c408040d5041e0000d03406120110341d608050003110008240540310b00743d1120483c0d0030000400510004900314020003070b002005c1002080a801400003c0c2c2210441040340c20a01c7d040701c0c0c90441410082c03006440800c1e031a601d451803240701c40791440c118100c20341c02140783c10551051810545000111454049040c0d480c90100400e44e03200796020400d00d0381801c1055528004d405e4020907003101241c607500c66101c0c04d00a103404c10b800004961101100c2288101600c800e46c022580c107900101441c11034981c0041c8603c010480c9040820180c568006e000340614407d004040007040000340442264201e541111068015001d0036a1a03081110601280607548003001245200b8000e011414440d8400c1e03009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 321982446 1250 321981196 321981203
    0x109240b0d053601110f030115180b030a150915050f0d021e0a06030b101110020702010e0a0b0307080a06060906080402043e0301290d06090b120a 64
    0x1003803c501d46141d1905504003464403611552038207441c0c091001a50050000d05030030603c00c0d612513040c034120b1070a14542409940c04c008004040039020b4101140780001c0d14500343c100c942d01d5840101520207841d03c2a074500360a081084000f442c0d41c4554401c48000301c0381000e0440759580c0e542007100c45000e514140d54400c4c9583c0c2c6220043c60305c2103c28080c0414042c0c0345054042c594001501d45103d03a01120109440b240d485100b440d02581c00c81468400303060910ba2074000d00070940e07030307401480180d00c0007550005000055a0140d216100403031070040c54680c9071503c980a9003c01e400648021000c2101000030886208460242c10140c481907558210340754500041215a541c001d8400d07604165030b05201d1880d46440201d00d032071005041c100d100011820a503040c680c0103060801184d4001c01c0c001030052201000300b800161038100d5681c3c00452140d032088400f1f100340300344071001030728102d000511241c154025032040030088800c8490404091003080e2610744102005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 321983696 1250 321982446 321982501
    0xc100e030a0509031e0706080f0405070509150405150a060f12150810050402010807050702010e0d02030f060a0b010e0406061704060b030d0305091e060109240b0d05 72
    0x10940070344104080c225280004044a4012107009030000c0051110705015055400080e0306018058020800c41d8002184500002840c60300341c40302d40d00c80a540c0151442100110040307101501c4000f020340c09110010401c01513030800d0b00010340300000c2020030034020080008001503050142c83c40e4241221540c54281501100d054500018000b840c0648642100c0000101d20702c00d0400001c082c0c5c4110030000941c034180303400054003040d0000d04040c2048002c02040c00180d0b4890541e00480d00b085e520761101c4900d0748002810309001d000300184a209000400c02409201c1d0040942c2da0400c2c0c07522040b00f001d150a000541c3d185014003808900c0c01500795020071455082c0b075034428003032900050301c000b101001900303252043c1004c0c2c0c00251540c080c00b110030070078000c695040d14130b144a0744c9a8005008415203400052040300e98640ea50a28a0840700b400c0c60003507964000483e40d9046c2680b51504180c4a40020700e0001c0100d1800c0e0000c6d0100c40c01181e08100c004e00074450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 321984946 1250 321983696 321983707
    0x606040308090604150507020a091104050607050a05010e070303081e070e030708010204150801080102040302030c100306150503190b010207051905040c05071a011212110703080c100e03 81
    0x1244081d9000042242d0004010040000c17820f184a40141c0385501c02ea0300d13650f07101454010000100c2a582084a50038a040280d609408010701120226141502d559448250900340b4909040340400c2c0900a942090038001a0050101c1d401e000d80f44a03443c2c20b40300d13032a2850908407244140f1441031003030440c03102050303620380100082140b46500400701e401d40e0b600c80710180e00b603030815030024554107055804808400d030410242805040079074021070030a440c0d0b40001c0d560300100141c450240801035154090381c0d20a030880c00140107185454000155402c00080c415803017195800c07140904450740e800080c0b558011480c03421016401403615a00303240401c41c0300032415910244001400720000340c6625075004038100c0b8042910b0340d0b03840c0ca0b1103060140f20050300240e058041c05080006019003500500794880d0301da0400ca0030100b06c0b80740311058a006944051010f540d1250500000800480c0030040282c03942820641d2050810b1104d200d007601d003030001c80d5401c1d401c107014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 321986196 1250 321984946 321984953
    0xb0702060f0f0c0712020f0f0c06030f0408070b01121202010e0a0b1905010b0307090f030302071a16060515040c0203190302043305120f0402040b030327060306060403 73
    0xa0842c0c000c0f01c03e9007050710304107140c1d480c00000c0d0021900c81c0d0168200c160707000c040da0424400c03492000c40302c10181c0541d240c0c41d4000740c020b100003004d14501a01d05c401190501629005480e003841e8001c1900300d0745d50710791026100803445a002141c50381540302965030b001d841030040003004d80100d0014030301c00740b56660700000c03444000c1035401942c1480d0102d24501c0081d004090080c100c1d5a01d690352418844d030014441d10f601e4000004a40200808000190780062140c040b24031112207002003c13104a8070701c2952040c842c11800455424803544180400c5905c500d0040c0c507940f4030320071100e41010038001502d04442e0b021000da0030610407107281c940040803140354071001d13280040c541620380d030f4100d154800d0101c001d03d403040d2203084a031541d641e800e80c035407055016040550410a0351404820a04002040e8401c0c03070b00c04a02040071900d541c0c01c07000001500809594649489046c601c0711003000c0748a0204440e404004000300d400c140081324081d2001814186c0340508644 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 321987446 1250 321986196 321986221
    0x5040209060a0c023d02070609060c081201080624010f03090602070c060c03030c020c0a060e0307080303010b07021c0b180f03030a021b060106320f0301030b0702060f 73
    0x1d1041c5c0e0454000b02118200302c1c68800c444060a040840660160101840c03a071420035055105a0a40d8071110b02808240d800014907421a0041d02c1c24405501c2140f420400a0003110741d400540c0701030400100e101d100c042070440c812320f102a19444484c600d001c20f03190507110b01c1e0754180401c003060302020030603200390418881180203000251a00f2a960347e2044400055031101c000142c4400c0d40c0410150f0501804c2d030148034510050003445485000100c4124507403099400f409019460a0752a0714240250401042d16000356502c4e9a9038a060800700d44c0040001ca200c2c8520614501c501070020f40540c151b0707038221004604550f1500044800b0750303442d41c00740705c1c0c074412002d2121220800700001c52241003c950f0240e01c50041082000c291207402c00d184950740c000c14014403200e0790143c08102104000201c803103485900e0100711782d040c4461410b01c8050030000821003030700c84082e4001e5040300c2c031a07602d91140f5030712144200d03120a020395250080704200d0700821000e60609 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 321988696 1250 321987446 321987467
    0x100c0806061308030a0f080a0b0a051314190b01091404020708130602030a0e01020105041713050d0c03030f0212030c091305070305070815030618070510020102090a05040209060a 78
    0x4400b803000c29030710f4094107860350300401100790000702e0408502c6842c60f8090000c50b0000400342c1c091000800035400510f203a902801260b005280c0d00007417070b0070000150402c0304109070741c1e80c00b00074a0419821461b42d861120003500940e0341014200801f41d489510b041044500c2040586a5003a4050810010b507100c240180c410318030500100f84d40f4030343c40001070010100d5800031170b81c9194240f0302802401241b42c444d415a45400300b0080401c00c01d02684003028a000b42c81907840648030001700c1d4107086a0095504030035503942840c10040070400358020707203000ea03c900701d11a4000f401203035144d1400f020007030280400c0c408900c488104401a01c20018010300c00d845900214038400215101280c0d40b500294540703040c4032038039400107009508000700b040e03000c2d1030406072800720350354103409000440d6503003080c0c0030030000c100144948000303810b0041944160204400009010350410750065114180180c4000ba00346007604c2103451000010304203070b040060000c0d0a41c0ca01084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 321989946 1250 321988696 321988717
    0x90d060603030923092d011d0c07020d1b0f031406100b0903120711090604060614030a060f060c0b060f010c030804171b120702012a05060a0608100c080606 68
    0x101c0000c9513140c41042650100c072002c03800c1102c00c1d600d40348d41102d0303000006a00c090203d149005003c42e60b102c00e0100c940c65501500c001c40b04003000e02d010500c01e540410300e207120700321003400410703400d0301085998101d82c001c0505503c1c000d07501011b00e0721100d040e101d45005042c844010482301500a001d06084980101030f05d071010070300f41c002c1059510494040307411140148000d645440c001059a810100039502000001d08010025080c0003600300b042e44034510120000c5c118480b43d42060002d0950010882000e560b03a000c0613108922a8004039003900300100001c642e41002021a200c2c0034059442d0a014001038509907070100d4044c005640c05410307040385008011400c070082a104910400010303092070601d00c610f0800a03c01e01e00482240100003010160317a024810401400a103000c000c098406680e0b10702c02d88101d440007c2103401502c00b041385085060340143d01306c03111036060711811002d0755458030403100000700402c08503082c02d010600c58281003001d03203101142c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 321991196 1250 321989946 321989971
    0xf06021c060302042901050708090a080c030f0105100303050d0e0a0309050f03160509190c180b16110f0a0b030403140712030c05090d06060303092309 66
    0x250110300c40580202511003400c925100d000c1002181800e104110a40601c1c403140282100150310000c00040c0c1d4442d014100000400d5107c2131240920803036070a00c034002c00036070801c1d80d47d4118980f51510341030440c1c843d005d4400800480390040c003540307104000403242282c009045940c1583d5036007051550205107940c50194a2560170108026000f060094851101c0e003440c0c103007001586160074510b1400f81d0400260003800692020101c400c3e82c6044070454280c0c2c0c0d81c08903101521034081c0e05c00d6212030805440f5038503140c01050280c40740b00d428280c5034619807070320b0440c0c80c10b01c50700a030300440108481e01030000c1140c6601440e0004230040110000280c4840000e0341080c0503004401d841400005100030035401c04d0380d00c448100100710003801c1200c0d03903e0b04060307c0403000c84c0344107050316880e103500352a21402c2180d40c0e54100908030034a4050504040c030091903a0700003100441c9400c400410340011540c5515a000d4181d01d9110080f019034050220510020340303070100300d1a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 321992446 1250 321991196 321991207
    0x103050c071202061602010c090b0d0902100302121e37021308060603071203050421020102060105150d09020a090504080d0c3b060d0c1101020c0a0f0602 67
    0x490b59401ca03803490b503050340100140d04141d03000ca4440b8050282e014250780c90301c1d49100019401c050114215034411014a0300c1d02030074000c10003d420270b101c000350b01500510720b803945141c15501408511042c281400144da9450b10000001400e09401c001c074499840c0001d20440c030040916400f00d440c0b80d2803011043c0707510521702200003000d12254009500441c0200c003509440b20104020181d0030001c00c03490405c100030940b00d51490249401d0500e00b07001000503d40260219001003a0011072001462401c6500d4000400d00c804128014090400002881e142c59068044046d580ea1100b901c1c00c015000c2100c018880d0580403030304000401c000003010780103881080d214501510500e43e8550300c443c080c00031030316a02350740e0f000e001d0b40e801815032401d103240c0001080c06100c0341407000d04c0c0c02c0c116100d009188031900030341d000d6070004103002c1340e1076181c001050542603515503440140c0e00b8a956800d0380070716081192380d035010240c8600810218242c500e007240c041c0340b0051402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 321993696 1250 321992446 321992453
    0x6040308040f240b0306160f0c0302070f12020405091b10021905010501032d08030a0f0e01020c120f0702010e0d0f0c05010905220b040e0307060609051e0103020103050c07 75
    0x800c943d100c0381a00d980e5000003143e410180441588006110003141e82249032402c0135205030031180c08101000103540d000f41c10140200920f4000e468202500303403203a0b80c0d4041d0004054102e150480c001c0c0c1c180b50118910302400100d00420201d40340750a5040645030041c04041804222500e08621a56900c4800510107020042d5a07034007940000c1101d42c10350426034041644040501c5041510310361884d0300d0424050000c1305564052140f50350703a22241d08600c09070510b595080b883c1c0c0c0c0392000d86020500150f0003007408a2100e030035201095254000c107e4180248044243c00240402002e4010342c842c6460282c3d0410040504540034001d440f020201210300804403150f200008041c07100750380000c4004000c081c1142c501036840e1440d0802e0400441c081c2c10b921101c6d44401c5440b0301e82e0b0701c40d0846031210080804032500e5101d40e00b80b01c4041c0101303109640c20a40740002040c6035002502c0e00b80e01038078000100c20f116911316801140100801444400c0032201403025a000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 321994946 1250 321993696 321993743
    0x110d080a0b010c0c1d01150e10030b03030c0601140d0521070b040c09050124030902010509060a090e0105030a0201050415051306080402010f1b0b04140102040b07050c0306040308040f 80
    0x1400c0c0400400c0d5414513102c005d181462010380141d4614035811002138003031b6a000803104001e242c1501c0920140002001c01d0300903007405405682d040c080426850000f0800080710b50480d00c00c94410012000460284000d002c5085805003040d000b116080c83c1301502c84018202100900075910310b020126151072640003015182218003c1a41c0b808000c000000d0241c03a003d000e0b10f1120280c40785107500d0750b81540c0040c80c00501231645420300300d03003560301400c140c403140c28025085540d6180b0a490042090750b20307006080103800b21000208550800055003202e16034180c64107460213050002c1750320070440d0000c01c07004100c010403078800000108000c0c94014a000e0721000c0f52820907100141c840150b0115210401040d03a00d94100c1d8055410302d50011600310701c1311000c9458908180d606104204444410396000050024140b800b14004006040c0a41e094480c5841c601081603101c03141075502400041044002c42c000c558800c1d80020002d219081c103680407012400041315 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 321996196 1250 321994946 321994949
    0xf0601020349050a0b090f07020a080a0906030614032e020403240b0604090914030309070609060809060109051807080c1206010b03040803040206070b01080a0201110d080a0b010c0c 79
    0x20700204540c2d64480ca03400600801c0c1d040342d0060818040c16880c0008a022060005d166041141d6424042104d480c001e11042c842d00b03030420126582c410300c3c05406850b47d441440345d000001e141c000c00154210800c1c1e0101c0c010f50f4010094501081c6c0c5046104414402c60501a08607201e141268070b080c4e128402400118803403c841400c064a0307070380443c0f54040050f500003000381081050121656188104c1b800d5400b140c40010700a195401c00c0340c468a1000d580102c148400070034804688400210001242c83e613503207442c04240c1740c40382211201020344c0c41760320704d03481240144204001900850352146520b0540d9544601905400d803601403260301c0703068140c02c01c2c0c15059041c01e10b92442c500604149000f0881545407103840c034203610004201130023040c4080045030440d03a41000300e805043d0000d02e40d4595507144d6000710784913050484200c0c0866041001801c030801c01203001c00c1f40c0d240b2030b2920455540c858080300c1c09055198a8103041003034488001c000078100c115401d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 321997446 1250 321996196 321996307
    0x903070e090615060903070302011101020f04090e010b0634440d0c050403050a111f0c020d020312160203160503030f0d021608030603060f06010203 65
    0xc5503090141440340681c620303502580c0135480800c01e04c0290303200041c054046990a10309801d40e0a140c0209a009002d0803840c0b1103083d000040c0081e040c60700380c11130340302e91012400030031031102003038200a481c0c81914501044550402d48114201a13070403c3c02a40c1080701104460450442d0b4540440b001d1031400d00090030001da102c0307100008130a0841801c032544000400402c80c102d1b41090640c02002408580152600300142205115800b603500466200003140c01b5040b140c500641c00d80340008189004288a0b030f42000044082c5852181c040019200c0c00d000701c00640334441104000c200598141c0300369280074000d0035801e0001d1408500c142288602d140c00c0e807041508013440c00c0316040b04403140c0300050200396404002c80c0c80100c07440e0002c4e946c802c070000480700a401030140f00c600303440120400300240b1480000441c0f061704124142e03100340d0764032a04c0031401c00c4181c4a040c0103a0007400b41c038400c204900d01820441d440310000c901005078040340b5500240c1c0402550 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 321998696 1250 321997446 321997453
    0x406060b0d050f0601090f0b1810090303030c0804150c0e030f1f1103010501050c01090b15010e09101517090705011d030a1e02100306170a0f0201050903070e09 70
    0x9441d58a25203d03401010918000360040d00d022465580348440b030191083c00030340041c81d0310401001110581c00d4072405882c00b43c00410105010304040400c0c803094004c070b42400e01383e60b0300e244a40e0459110340e5220f80703180b80d055040e891400040c0701c41241178003400a40100020783d139504010304450805600018241c602c003d00000e40351220f040400f82506091040003840c51901e8015241500c0342840c04545130b00c101c00905000d014490300180c0202c10000c140300403240140f007482c0c0c111328281c8070841d840a106040c45600c50084170303200000111150280003140c1544507040c8550407900d869103924003c00c1c41501c2884059440d447c95900c00b20017000349581000300600b02c0c0806038401c07240c0404c00c6001c2520303129080300c018808003090540742c04070408420040003403a0040c008811a1448000c060010903150042c521900c80420200c1c044800018104084950045840c174601049a0055805400118907180d1502418a01160843c02c4001c694480c0d940340009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 321999946 1250 321998696 321998701
    0x16080405030c031614010903080c070f15080619080105092811220c0804021906090b1812060a1b0e01121503050c1002071d0406060b0d05 60
    0x200741c036005103154024000e804c0711140e06400c0020043e003608490b110155041000b54000040300c0552071a00000d210280c082007554440c01d00107090820380380c0c00c1800002d0b03680c42d5903100307143c908005642400298051300040b01e6080130b54060901980c210204071100c1d84801c0b105007503a600b00c070142c880b584a2080d00c10100c2d00c4059108140102112803030031000c1c1619a010840741e100f03200740c00b036003090203883e0100a0603250b40c10002581e01007040b01c1c0030541c80c020040f8000f51800c2c0c2c45009006046071440c08403020a90403121240c850f600c541d45041c000381c000f50003491100c031411203110313089801610f4451078030615440010241245107030010075401124401010952000101010051450b0f00284020f200c00803d0918000411210881b003010388104403c030000c40c0078005000080040c005800c8041003412204c0401005a420f003c03659034689228141124940700d400c2440d034451001c0035500b0600525010039810b48900b503441103540036400d40808155920704 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 322001196 1250 321999946 321999949
    0x1602030c01031116030e0901060f110327030109080a0f090b090f0904020429042f0708070618060e0106320a0609060f030902010c030807030216080405 66
    0x2100c40c0d00030908003080001d18041c86201c083c007944140207400400111088240360080c1100d00310224001c003403c0709580c44403402804105c26040341c4012440c41c1c0011a039000340402590743e51022100c401d009908070a0340c034045015030281d03850701550b0391410705003c00c0c40e110060504048a4a48128039604400010300d814107652000031003940510540c0c9455948030b03184400210100c41d00d9419858500008000301443c40511a10a0700400000760003401c51440601200301110100200c641c60301400341000c1d2102800c0044522440031400e4400d4218041e248050184c0301141c1001003d6603032034201d42540c1c000c04440951118002e0410105001e11501003035030100038441e051500580c080420b1080f0f440700c514904440901041d007103850003c0903254001849910303425521003000d40016618040c0d800000d461101028005009000b181000b580c1a520104d94200740d450440744d100b0040d15040400d5000c00c40e40c0c82140c2e8801c2c043c409503015141d0250344a140c41d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 322002446 1250 322001196 322001203
    0x1a041b03110405040626010605030a060b220b1216030f03091e091d0d080a020c1203040501050601020601120f0303060b0d0e07050103061d0601020309090405060a2a0e15160203 77
    0x101e542c0420b0381400348c1071200c2d86010070380c0010660300c007034041140d000c808001084114104c03400b405c0001401c281903c0f001c0703150031152040307409561340390000d2140000c280d21481e0441060210a060310b1040000864011500052501034905900096100c03041009180740c0d040703a600f0308516044091110340d070300303200c2c41001107112070888d500202d416810030780b01d0940c00b00c2034051042c60301c0003e0550781c1c1501111840c1d20780c401076581c06c04002651001e190020b0328251180d600e13000016505500003c0c089059510b25a1404150b00c82596020300381c4810031811000c050b1101000031b060f0704080050450590290300104051790381c1c03580c480c50906644e010504041c1041010011044004407070000c0d94000c4004002568403a00140d20314464030b00040e0304440c3c10401c2009214011400e14050515004d0500400f904014500c912011120300d80700c8012040c0010b0841c180260f114800c041400342031400d449a01b1207054400c0d4020081e445c00302c4241745414801c40c43c062 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 322003696 1250 322002446 322002509
    0x1b070b07020724120b120f03070c0806070c060b040207060501060e04051f0b09030c06030414060c12060108150a06020a05010e01050106050403080a0c151a041b031104050406 76
    0x400fa22410198030300041c2581081d04c550350b1390315034032414699940c0b10803000e640c0f2540e50500301c1c1d0245001540b1142d50360b12440c0e041d14003444120380403508600203d0303801c0c000c8645588000902001e9210780d002042c1e004c004592159081001600280160050500a0645403102c450031104001400203465000740f0203d04078080e00d030896030304103c5244002c1590904a032003500c492100d00400c0c60074200c0705d900741e40410044100020845500c08064600c41b8150a5034455102c80351000000c3c0950b207405103550b101c2400240c5213511541302594000c040040011880c1c0740e4002040b02107160750801001a0490303020030342400742c24040d019501c00c021000304410361600e03400410714001d03070000504501001480c25000e80c0b007540c10b9001940c2200302645844040c919401c0149036064844428500c03035140340a861400d4072407650b445409640c94440d0346010b0030110005c2c440260710400028091202054981f25441000090450a8200c0d0103040a00e0402032500010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 322004946 1250 322003696 322003739
    0x50115020d020d0c061e05091005070e090a0b12010f0c0e0306040f05030d02041d09010203070804020603091e070501020111070302070303031d0d030b01030f020906031b070b070207 79
    0x3070080116038560001da2111422810b28001580040d05d242280240125003210807000e2000d02d4040da140700d240c0e10480c050700345582203603516004498150142c400880315900800c1e03880c2e40003401810080400c1b9402a11407100007203200308240025620f411140720b4503404d139501c2201400c2516035203d204003442003428403000c0d112a0303400007503480000500040c00c11626019a10030880208140e5005c400840e4095480c2e5444826000c1500809a00144410b03100b90101c2c107824010310889000c0c00c402d0307441a000383e880c3e4080c08503d500285c000d50f842e01c2440711040003050405840c0c40f4410094000e0700300c082c44c0800090945040c0c00d441c1d0308044081048c000004d80000c0c0d540100c950509010a40080340181c07640825182e4601c0d810324000d0f69604038070b01783d0550041000d190700f41c800300444004452404202d011b0300c03240030340024040010541078244424640181064189541d02d001040c1c0d031490980d0401342d40110150707112880a101201d0004007044840c0d49 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 322006196 1250 322004946 322004953
    0x15070302012405060306120309030607020c0a0902040b0d0b010e0406140a0608010506030a090c05060f031b0a020309010c021c14060606030408041509151d030d020303221505011502 79
    0x43c036000507610311010305058403034440b4040c0b1880a4030203105440a0007802030030303a08140b82888029440314000403000e40b040c83e228101180b684068070075502541c2d140d20007a801d051200b0810700007004440c2c0500d05115101381d001c01c0f03d039142d014040c00f50140b0715a50034014924001e100e61680590007480c1401400c0b030050000d0b480d13038401d032540003801690110709401c40d81003212100310a5000207402000008030a41042c3c1c8400c01180901003402d074000024114001181050040034850380040c1c01c2040039150315841402c00343c240702d00081020840c0700000410440041c0c000404850118000781010340b2208180080f030350181059032007910f58502a500c4403007a10640c000c100d1042501340502c03401034803480c030a4020b400c0551442e1441106208041c12000c1001182c20341e0460803d4400c6842c140841c10407241c81c0c0e240c00650440d1910103045002c1149104481d14035119444800003280f51041c0342c403000342200500182950403c44a4901c0c0d22010400c2c1080d9070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 322007446 1250 322006196 322006199
    0x60303030408031003020402030406090210090f05220504050106030302070909031b05010e010504050c10090e01030b062706011b0c03080c12071a01080d0e0f150703020124 75
    0x1100402200d60081c0d1007160150b40350742c2d0001ca031910101d1504040d4002e4800300c04c2000b0803030382d98804c04000c0c0c02211180d5060341c00702d8085030048810300a0102d001100301c000c200906103080803c01d100000c90649003480c03003c43c960021241c0844054034140c0d182c80f810410725405000070320280085140c01e000c6401551005403d0008180b226135007030844d0030414060001c02c3d4090703292200320348000c2c009400c05040c00e95a40c2540d9405921540010007801c280b140580e803030104681d640811036415a10303544910072152001003180b07130002c0700841c0e807401004903215001c441805956040c8400d0919000041c5243c4c00005210b848824591812011860900842c0304132a4051180c981e0f90b40d0840e00340d401e040034140d00190b60100403450b90100115010101d20b4001c5076280704049a9a8005142d51b65000c8403062000c100713100700100b41814003210300d2150807405003500a42c6010240d0a9000d40d00c004402d40060f550703030712003500341802d4481c0f4800401c0000152060517 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 322008696 1250 322007446 322007449
    0x100207061e031b030b04061d040204150b030c0c060a020f0702040c231801020c09010911070206030106050a3005041b0305030a0e030d09050105130e07020304090b0906 73
    0x7840e100028500030a5200078004000e201c1d4101000001d60b915500c0b0102c4428080500503280124005114a041003400304542d0306550aa204410b80605907109a403184d4003440000c0103056500410030101c810046011441c5400840c01610480a00c5596100c11500c0e02e0411380040c1240c3d04050041244014801c141000d680500c1d404840000b241043e5110650b0000301d44603c08c1c02944150310300e03c0360181200042c0a444000c201c0740c007403c4bc00b00700120380710b90310170210700d034007089120051100341059072289690006c041c81d034501e00b0900c1e030000360054000b43d21600c0003031000240300741581e0384280b66100003ca581541a041d855048200303001c001c83c90324030040d20ba550f800050502c031001d50710448240c60300411107003050301ca0420580300ea10000500000c9248280c1c0800d0a003000105d403102d001482d0f031001c0c80981040300440341c41d4030101d00c0d03150b180b51462012412304141c2d00c0c102d0080006400440e030740da1504c40e035031b010f848800f1816482520548100b1025 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 322009946 1250 322008696 322008707
    0x50d0b0411071209080607030f0608072601200a020d080435120402190302030c060a0215090714010c050d1115040b01090605030c0d02060a0306080a1110020706 70
    0x76603404040c086000d030b4040011541c3d404c00d40e014100a12a400c10322225941550015107000451b48081c400b03241c980c000aa0341e58441c0c132032402d000444803030100100c145a5501c5814208e07000009c03422a004e0700903207850741c4610200c4581c140c4005070114a0035010440a50200c04505020110b480c0c507032250840e4510b11101211001260040074038034103660344440480c1c0d200380d08481d44590305541603541c02e00c3e0440d401c9004041d06a560b422852200701a541169401002008810270403007d104060308820006802d6100300710070450000a40c082c110b10420ba0000200341141c9040725200335021040881d5042c460744070840e5000c5000402c806140001a04103010f0080b01044428a080c24050f03000c90000061000d0000b000900c04485040f5003000e07006000440d103a80030140c46070070030444260b00102c480070260040c01c1140c06040e000101d82400990f140c4c0e1100740b03074208418078108036813070504450094010b150448400988908510050425605204000e0300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 322011196 1250 322009946 322009957
    0x602121e07081005150304050105060a27021c0f0b0d032304030524010501170f04021201020a02010e06130f110d15050a1b05070b1b0406050d0b0411 65
    0x801250760300142c00c90042c608a90f00800000d0429400c2c1e60000c4e030481500c0d082550112501d500b041c000c01c0c034500e420703181079013600d04505140c00e14298a48003104e80080c802043c002040d0203101250380034810f0912029140360500d00429400c1401510a08542480701f005100e50180c0c040c81c40802c0d07109103001889040c03003860710080920b061003200c5d58001d6501c002c109220307000c00700340c0d4120050914444118040d035420600e07600c41e401903500012510540c3c0c40606143c0c0015800c00c5d001d14881d402c14000f800c002e0030f4650400d40b480c266071044041c00b0160303450b40c2d940015a04104800e65012100c3c08048090340700c165220f1b00220f1050001a00c041103010000000790f5a070100e856001d58450480c507540c00c421940c11018000441e58240143d01d4440c9907981c03401c01c1800607000805659801f49000215a03039810714110151005d8064542180c02c52100d000c1e4100410150069444098940050840f120251504d01c14464042d03424035a411469440c440107a95 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 322012446 1250 322011196 322011211
    0x50d0f1e150b041d0a09080a020a0b0601051204060f0b060a0f1d0d0b0703020d2306030106062c0307090501030c080f100b010e1801180216020d0305160602121e 70
    0x1d62a00c0d802800c90103407240b84e03409000c000c0c00041840c52903800082582cae1041c030840d041d465950f11040195114064002c080d588202500d00040001e042c0e54802c804140e4140000545001c1c9000491240e40155241c10041208c070100260865000710020340c004840d1055110303c85640f0307021840c00c1d039900c0300c000c1047c00c51001140013107000780c0540e05186658502005200e840704100d4090040c98000c4101b0000801e011464605041c05803500751b42e05600c510b07000f2441500550410781404110b8140d1628079044070440e0780d0203000310001001d05e8007010585504500b000d41404400380d002010070f500064120070110310106a42e03c031100701e490009001040da000603100301c440c10701550b500c0301c40d0744009484000c050901906a0313000b040541c9961011144400c101e10491103181389010803401b0200040c605800281021482450243e0504105c40070104c541800148116406600850800701d040241c4a1b0154001c4100d1551594850f80e03401411240d00040c0510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 322013696 1250 322012446 322012499
    0x70f050f19030f050114010501050c152205030d15031a100503010c0f0206090c031207060204170304061d0906040b0303040b16050d0f050d0f1e150b04 66
    0x700560108090034002c6411180711885403c6034681340d4001c5c55000744030103d00b241c9070000b14203548900b003501d1104125000808000c1c00041d034503000301c2c1c002410014141101070f1034481c06010602c0e401c04071807080005584a0100829810070f46905c0710001c2d914241c03003132080000c103204003001d068490507a070810069444011504d464180309801564056003044003414140e60f001c9100c0f980320f0300f5607080d0b50294490800042e1118407031401e0661551040703440d1007803c44044024039140344219801480c0580d26007400144d80c0c048800480d040d0400715003084007941100d69034840703524540140d88111000b900086540401811751800782c2d0b500ca0005809440802c00c440c0900004078680e0b482c3c03c2d11103100354a4006201c411260b0740980f407403500c421405092a212600b40035140c0500b00341d01da400510080540455042425803501c0e1105540301c801000f008880c80103140108894409900641c0000070a50010349640410401044580410345201d40d10340c44071100d9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 322014946 1250 322013696 322013719
    0x40501120206192a021005040b070206031e09060403020c010309030801091806111803030723101104062d110c060a1707091805090f1509070f050f 64
    0x1203441d0404c16503018546982500d180320f180c10381c4034200905500c22100d10b5400010040e044130240031343e00c2980048030303003401031100610300b070f80285034040e1010040401645000320120080413065440b040e950b000740b0180418180d046c41030040c8400c0a080038480c14074585c0c1c0040a03524148108400c141d9607242c40010702364000218a022500000c00344030801c18001800456404490000c0a50224004020140c200803040e103111030741100340342000d0b10f00101441694201a16821000d0140301c1d0042021211403103960200500b440713401e0380399411b06001400440c041c01c4201c040c041101001000b50003c1d01018490001d685001d46117001003884540c90034402020280d0700c00c101041e0000030a90040c0c8003c0004214030007242c80361940c802c1550210003501920300c190ba41c0c91141a80c01c222a00604c1c0c100408604070f41004c4944401c1c582404000c0700405030001c04081803050700d1a04001c0303000078001c50004202e120b0b00e42000a40d080002801c0b40e8010900c0c00d41 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 322016196 1250 322014946 322014997
    0x60c0c0509221103010f0905070b09011101020304030905040f181101091d040c15020303011e0503060a09020109152313060f0f0516140f030d0605040501120206 70
    0x840d10142d031222100c88500461510700103550b0551501c0c0d940c002e40ca0100c000d43e0f004094064842110b0b0050b01901c8075500b403545407452030703020040d02810700440442d0301034003500034030007075200e10f000e586c07a400f403d41030070704010a80b004100d0840b100c5007041ca007141003440248014603125480f5204296408104006032140d9941b40d0141124140540702c0d40e09103140c4002c094450341c03144e04030f81c80c6075449003a40200000790343c198500592050006214050b40c022707890b02d0100840c240c00000954840c00249011021203107160f60548400c2c00004558000384000c2c041c0503c110540b003202c140b0302c4010403090600300100f100140c00d103645c800703400c1908100c0314800c0c400050880007a07100e410150150900304031880000d094410705015584c4543c0c02d4a05010b0035281440c8070300950b4035011054130001a46083c140681d1900d58541c2c00100001c14181000c0100400d01d035240604020454405900121103141d1198480c0016640c0c44222017201000c9102c40b1060410100b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 322017446 1250 322016196 322016221
    0x50703090506151f0905091803040605030a090210030b0108060303030705070b15090c041a0f0d021309060f0306110301060c02010507030c050a0c140a0501020304090903020312011509060c0c0509 85
    0x35000f94080451413020864130380c03020140d07003a22000c0e6200040ba8032501005040c0c854585012070268200780020720020340725070300441d08200001d50200c0c81c007c1b25000900f5450001c0100d0700070a60b03a804101075035802c1603855500400880c09542036103402d07803000d070143c400c082004048031040e000041100d00750303082c8411084c901409a0007140341180107481140d00901a0751546015400b014060b25248130494a003411141c800c40d0502c88404011800703074028803000d0542001000022840307026501c0781e800240101c3c5031003503e440c80d50524100711844c05103d481090401c01c0140221f036000f818003801c1d10307820b07e400e40c0d50781900d007002c40350260159002003080c0a91485102400030151a0070141c40c14801c0208044a00800b0054051024450107002d41c00a01042105054a42c0800701141c0a401601c0c0f8280400c1f00c4065021001d07001101e0049002004078100c0b07074403103290400341040d800c0041011545483c1c0f60700b008842d00c1441d20860000001070607404042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 322018696 1250 322017446 322017469
    0x1180207060e0106180209010c1e1403040f06020114040b041a010305010212131101031505060309030a0e0d0f08030a111810260a2d05070309050615 65
    0xd2001c200205005280302d018040510030424002c0c2610005d40881e001403080b03401040050719000f00c840f02c10b9a0398240354130200c0e658030210040028030070214100c004042500e4a011010316034542c14001c1004441100d900000c04580c90290904800880c00600c0c5c0c3d00660001c026442c46d07a00d52a00000348038804845140641d81c0c84000000c1040540207826480c514070307045c8000d039903141e0b0700104102d040c41e40038100c03600b402c1000b00e00d075000740e100780c00c080c210000914620380c990000c12600d9100744c400301b0380340d800042d81507040e0380e224444410849003210301070022281600d6503c0c01c0300c44001d010342241c1001011400030105e0b82d110340c2c40c2c050031780d494589030301d00b03402500000b00540c0c00e07881c0a4202d000403418002d100e5100c3da101c1d03443c904060580708042d68619000340710001e14059100d070b40c1c0c6640419108100300303514100102e00c0d564012a00894a000b81592000740c014801d050500d40c15000040c00412001e511410740c519170401c80c014580080d10f100c0f0107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 322019946 1250 322018696 322018703
    0x60e130605060412030806090603030313030e1507150506030d1d090a09110303030c0a1d06041502010c18050d0302150109020703110a050c0d080c0d110c0a050901180207 74
    0xd00282901306950400d07902402522120000d40d12031091007003090342161103a81c150130410006280407000d030441c99410f40246402c8400c4040d4501140c00c84050054491205070007042d0707042005000890741c0c00c030607801842403000f8284040420b07559991030442d00306005068816007282ca4032020341c5240007000405240c803c1c20240003610003030000c0041994040706200c5158130070700f0300000700ea00070406101d80601c1c1007201d41084410814443d910400d80001c2403003014580d82e24000f5201a0000300041210540400d8001e0308503641071141c04180302c1c1c5100d0000f803903100401b1031801c4038000d5800c0410b03808586801c80c14910104510211a03d21100102d607040003940500082442920f0f0040e5401203014582d51b1190701c03030b100604661240c0341d8680d00741000c0002403052446015014140036503100510301380000d14905400142e004180c2e01c1810404000c00000f28a00343c81d001100b0382840f0101c1e40c034070014018100020301c0781d00c800e003c85d40f295044640703d0744c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 322021196 1250 322019946 322019959
    0x60f151701090501080c040b010e12100507050c06091501170f0109081b1b10090b07031d0108060a09021c14061503090307060504031209060501170106060e130605 71
    0xc40b11100c0004100c02e0250050f58440c9882007955420980324407c03180380c1c140c40c0e01203400180410031500c240491100c0c1e0881c0500915507106c0043c900030a805034a0301c5d101e25481d02d8020081c58545070340101350176440d030300040d0170403064043c071409181995013a4080c90381840000d02c41d54a0440c0e6494400b101d50300e001082c0040c44880005042e14065014900381401707030041c140c0d6560314403140e424060003140f5440026602d070403030a020000045044c80d1007010382d20b446000c10b0b90007024040d0089022020700050780088a80c241070000400d08100c0001d04040002c80c1080c0020701130b1240341503000801140c80307041c0245500310240740700f0b000d002c805542c0f0a0241c0d0f400301901c0c114001da11038428030f001c2e80c00325010f80f071150714500015070504000da01ea21000c2e101c0030b00309070244445c4100c0a440042280200c4400740d000c0d038008100d03545000c5621691401d6255801d1059140a40c10b001c078513400740c0b02c0d002e1410219442c5021f941c40c140c040f001400e4580c4440d92154 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 322022446 1250 322021196 322021199
    0x5090a150c0b0702030a080112060e0303040f0209010509130b0403090f080f0f120d020307200307030e01020d0c02040e07050d050d030507031104031203090c1413060f151701 76
    0xa90014a03201d059102e448a4401600c0302c40082e6501d0040303030321039404140700d02e006002e0080d40090301440a402580c02040c0c104504d02c01c4da0465109840c2031381c00c00030030444c00301582494141240145001e031481819071a00e15003400e094081258001c0058485002040c14540b190a4503070140200802e91558140d490318a50795680102d180480300c1d0088800b04940070710041008003607210020a49854262161221002580002c0c6244103201c0c1146110b0346003020280021442103203900103640d604298180908400945480a81158410341c1205030b10340e4418110f103031036a4151400308c2e82c801c0480480d030602805410081e00701c90186040c000744440012019000c440c2610304100980f9804012010380d600804800140241004100002081c1102884080711240382c0000e42341c111756150f82790342d10581c1c44012810000c00032000c0301d140030000c011102d40c00100410840780703070402c240445042ca1040d0690076042d13882c2c0309070540c080e544087d000342a083c40c030310407503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 322023696 1250 322022446 322022489
    0x30c18032409061b1c06090204031a071b020406092a020a081801030906090c08010b1219050a0507081c03021c0507020f0105010f050118030c0605090a 66
    0x3040710031411400c800c01008a11107200114805001e4000301000300d540f00d00360502910a940022064416003400b80c071050720140d00c3e441101702804400b000981c2d138500e541407010003c0c12400303261482031210014400403039000041d224100e182c6455070207008010780002001000c140c2c2c0101c1c1000c0c148078203404c80c202158900c1c040004000002081000d121000b2650f5800124008003005001c1240c510598541d44006502c210145004507585146540d044160b0f24401b104880c5440c94800910214600380142ca43c1950262241d514000c4000c1443d984c9481114803081c40101c100841014400c0c18021800b190303030880300312040740369120b500f0380d03807400030784003503440d0f403040c0400300402a00c01e000300c52610107000b104142c800034100c40c940040902510382029482000300340301c00000b003801480c0c0201062504c0c988039901c0c140001d000000f00b540d18510300c1074402c0043c00000c2080102c0300c261903c600c3c1064480300320314045003502a15401c01c15907814407403040c0010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 322024946 1250 322023696 322023733
    0x90317071e05160b03040609020a120303150b090a150c08030f010503010507030c0c1407080d0216091806050a060f0e0603150105100809030708120403090803030408030c1803 76
    0x1500c282c00711400c148010403480c1c2a24018010007035100300c1040418046812a00821161740c001444000071607034071055850115000743c82103000ca81c9440c4a802901103c901c08030040c803210b0384940c94004c6003c002007640e401ca001d02c552030306000c90f410303182a11644400404560241c0c51039500c3c145680d188901e11400d1044612a40c20300d0300040c0384a200b0f00030248940c442c0d8440741448003d541d2a404e4183d818221050320703104207540050540c0c8100308424010070242c0191104038042c0c0301407800611241c00c2007680500700f011403d443c840005c0004002d0b42c00120004140d203c48170503201622041d4021254244003500100b0141284400f0600803007040303003107a400c1340113105201c07901c503800d1107001d61012941102601d00c41c080d16400380d005200310141d0b8070b0009260345800c0386400990030b0520441c400b10800c010907401c4090711010b00700e1003004504602e0070f0340c0c0f006140d00c40109610320a40002c07403902c0044200729186411414024156207041c0384849442c2103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 322026196 1250 322024946 322025003
    0x1a0c040e07090b070b041403030c07020118051f0c15020306180c03070509061b0a02030d02121602030307022d0402030603070314030d0606020c0114090109031707 71
    0x320145254040358016029000d000c0c01c45402084060802145450302c0c0744091005000750340c00f181c3d0700034159649905100851041c1c00c01d84c503a64884046000040001100701c02002e500c40c51110244050b41c1e611609004610a00c0c482074120007900d8070481e50301020f01f00042461680d060200d00d400c0c0302c0d07005035103d04002e4484000c080c0d2000300c004050a01033380c0b40050303100300b0004610700500c56002040d0090000d480c5c2d600d405a104144e010407501c603a0348000310b80218540000f10700e014403100301c02141d14030050042c0007410428036054812040d0103003802403045031002c11501c0c240150b8921a400410408628030712405418030744404040038070050280c442d001103d89001d02c2541c0c02001c1c00b4006000d41d0307007941d036040c1c2c915140d0007512134603200520405144070001e024210180580da4007a0049104400001d008825100d03004401c1000900005950782d9000034003400b100c1d0480c0440c01d00303051024031411240b0030b0b40000360000c0000303151074500c040100320303038103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 322027446 1250 322026196 322026209
    0x50f0d1a0c032413050a02041205030a0311070506070323091006060c0c120201111209010201050c16020d02011218020a0905070206010306050603030f0a0c020f0405060102191a0c04 79
    0x580c3c01d891188501540780a150180c1d0b4001c8080090104146090384540e0384085050b20041c40c0c15150300500c0c3c09001003c10481d4607610008a920a5a80c140903801ca000b00043c1c1c040c1c1807d000740d032070589510008141e00c0c205560b03122003690303482c1c3c045604903040e000ca84d100b00031b90a01c040c11903250b80503460620840e508191000502d24415414502e0068004110011040c01c14541e1401d14491080584c1003204940f005c00030781784244902d04404c0d40d29030070b10741d44543e1071002900390b600041007035070904001e10440e0701d9284003218030740c0354a07030445a1591988a5100607295018105941c46000b40742450400381c5808a1007000030030ae0084600140042d1b8612500003920030807074203000141c10200040001803400e80295400603001000d403420710342a04071500c107640050b10130f02e0014440104da5819800c120f00b02c804903290580d42408149001c00010f1f40d1040c1525490701e80d00818000c0006024a0340001940d0801c0c5443c01d2240d801d00c4102102540c10074090300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 322028696 1250 322027446 322027471
    0x130509030a0f020c0d06022a151b040b0a0c060c1d0603042301021603090603050a05040203120d090b0f18030306090a0207021c03180b04050f0d1a0c03 66
    0x1224414000900c0d403001c0744c40101800b41c0c2846903038031200603401217001645500c0d10325030a0154402d00c2d082d840d6502d503180d00103000f1a07807662024040540050310a504048c000c007090700320400c06208032010344900034406591048042005c4904c040102c40c0030303203890315016007030400e2503121481c00c51030b0340b0441c14051044008000c208144c8400d48005144107080e01d540b00e000052001020303864486500014148020b85403590f03044041a40210002070f40c641c0300303000103905481141c0d04183c2a8904010a1400f035000c00e5440c00c0d0b010704450740b85000700b0f01c0c0400f0f55154100050065003d0800d440608186200da800100140c031514400a140d004945103e14004103583c800c00340241952940d45956490f0002544050700030b0703810080007280c0745060a24020035000d80740c420b599501c0c007141d409017851a604990382042c40324440801040005a960007000005140211341c900c0c00340c9228548130f42c90050603c0441907100b41c000070484a040d410b0007a52185524903401d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 322029946 1250 322028696 322028717
    0x6050301140f011202121209040e0d0c080d0213030503070209070c0c060e1305070e03120f090f0409020d060905010b0a06020a0605071107080a050d050301030b15130509030a 76
    0x14407a080e4800c9805035201202c00004100002d60b00e4401c804040c00540850315407200c03e40b0b00f41c00c06417184251107500300000303203040d682d0a00340300301c000741900c1201400e680d140814009184118141028203c0c8402040f2094254030f141e040ba450070072150889154075a0364982942c498100c01c0060384110301017000600030b640194425030b0666400000b80740f1880c2800710548074200801c80441e0003407041e90100c840846030703100b41d0740544003c3d00c84a15a900d60801c040c41e083c900404540c2c540c3c000c4c049030102c0760f00d2030140c07200003d0031038444d800c144103003000c034005007800000654410880711240c800d00007150711901c8002d0242000f80207501c0f500c014041405850f2044100503844241da217408100c1e1781d8050354012104e89810111044800850b40c0f800c002500302c22003e03044800350404100d01000703400c00303031009410b000741151b145803100000c550005082200079001420441070954584190064840780400100540c0c2001d010b025a40d400c201d00010108003d41c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 322031196 1250 322029946 322029971
    0xf0d022808010c180e0f0a0c030906090b100611210c0111070b090604030f120f0c05220803220305030d060510110c0d0f020d1a0a18030305130209040606050301 70
    0x181030703202d034031b000c0c1c10100c02c0c1d110040d81c40d0080034002182000c05540d1210f4200246450046040e490302a4943c40035a081c9280c0308401e80303289910000c14000060452400034074003140383d508900a02c0c030200244c00d401e240e601150f2045244203c581e5103000904040d46081001070180503010b071120128507591030000c40c6e0b90321000c2d10080d010488400c2010544c5100301510f154100c0004000700d001c0b10305403800344c2030342c1d003d10146000c600c0100b111182d070426a05ca42012034400700d868014285000078141d205e115000d01c41403908920180c0011802008ac124001964041c04580c0ea4181028803c0e00030100c40c06840d01c40d202c0c440170740b20344600ca203841d419940d51a10190044500f01e80800000d090003410441d48281d1003600c040241c0d407031080304002d2078082c1031900039041751000e41c900305070001001c0000c01032820624100c52a1020144481140e040c200013400c2d44071140f61000300624824001e500000c100100000c06c9400d402c1081201c2041d002884038100101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 322032446 1250 322031196 322031219
    0x50a061b0e011b080d090c06020d0201061419080709020a0e03010902030c0609030f070315060515030703110c06151c02010e191203020c0f0d022808010c18 68
    0x7030019201c00300400360041e110f500e59605511a040d120714003400181c01c02d00703640b0740d61420b0311080c2082004000068060080c5080150184000c0041c42d04007420110a2120720b460309000384801040c00c5c00c40502008004049c07d2540e0840d400c40b551780702c1a0700030b540140340600009121400d41d0001d4281402200d01e07442c0c0c010060100d0304824000d10425070860841c81d03501d03101b5a224418802014864200650b008840d0b05041114082e5502c0a56026900c028000c00d01c030b030f0a0b54068000c070403c1d281c02c10307201d18001ca4102c080126107200c0f0b01500291600318016078060001e840004080d2907040c240a40f003940940c0160210742600c61440304020340800d9003001542c20380c1ca0001e001100b035a031042c00019200d43c950080c07080303081c1001801c4000d60300030222507105192002090014100c21104030f01380c0c0307c160340411103006141443c4034400d0400340f105e550310001c1e40012006080c01000030481045071030780060910500802594400d180312401190030748030300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 322033696 1250 322032446 322032467
    0x3071e0512030a0807051908040c0b120103080d06030605010605070c080f030418020409050106110f210a0314090a031d0f060708070213090201030f0e07150903050a061b 74
    0x74010b103082c5850840261680b030380090840c4100501005210741042d160390307000202c1c0140e0359408032a0310b803614100d0758840e4560080105d100c0c00340483e0070f140280080c0300d0f05483d406481c254480c0150b0010901411858100400503802c010011403c0345d03102c0c000e04040c5001c2c0e0300001030903603034660058841c0008400402540c004000507c00440800c0c0d044441008a03c0b006180698545110301112800e804c104006040d08251a02084040001740b40b48440c0d00090000c582c452420650900c1c1c1170b85000c042100d000c545605510b00940c03000004884040ba5010545040b801c1c658032030314502c00441c0400c0311000029942c0d0702000c0c4120081c28040c040b1540c0800390002c00603a0303080310360300b01c41107582003150b4001a1076102440600b100c000ca00802c61803458400034050b00c0440314002c01d018a0000c0c0c040d84e1030800517004003116070208070010a406034030030440b49a04590400790491040c0c0d801c5200304011a0700100d00a518880401c40804e12010211080f44c1607 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 322034946 1250 322033696 322033729
    0x150e010c030212072609011403060a12061401031202150402060702060f13030f02090a0b0d060b04090b0c131203021515030a0311010f0b090a09050c03071e05 69
    0x9080020349010200500655014410b06000f0000e030315501c0c001110b081707420442c15a030108034500c40d0358001d4005000c5409810042c1d003149880f402141c1000701b94800c031030480d810b491111061015603480148241c15824020107550703182e09002d055019092007200051007440043c0303000e4074166001900881e4020030f0b8500e04000b0340c00b0000683c005070911424103408001070700003054207409990095102d021a240015098010000b150764000d2a2080d101d08140342d452135950f800107603c0d180c40d0301420000b414800f020202d402007640c1100101052003001c1031020150b100d0f005440c010003219825809580caa00d03002c800a2410030008000d41d0080d4400020908040c10a07644092080d245403c546410300000e45000da056209901207100204ca12850742000e024200540342130003000e0040110400201d4040c4000900300e004460f0b442024404005d07052080d00a02e050080c00c039a80c09482e406254241d2008140450305085c03100700002d0107051440759099031068 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 322036196 1250 322034946 322034953
    0x1a01050a0807030c15050405120d020625030f02160602121305030f1e0706051801150308130f080601151d040506010c02030607120f060e01180603020406150e010c0302 73
    0x2401c0103175002c007581d441e80c00c41484000d03c0080740980b54548450003000300c040080c040c4220640d0060309080001d41103825018054081034001c003602021050030f44481e10300020242d0503504148001e0041e20004110042e51801d00d209002e1507402800c09059220b0b4100c88944404240c0c044800382218010600e1300140b1510500403d954081d200302210004840580b512036480b45040e6800761030201c607040e5460303007400041807100c03034010028259403008211046200082d010786444c14070000381050300020714100b00c070541c1c003000f0008040104010010030348591820391140c50034040c4d45441d810681981d01060f20800f9048181d08004020801c94213008060001600000748003505000308403480a00503182081110711512240c0d036150500c040603042c10090b02e080c40c6400010310b0070010306014481e40541d41504403544481000c044a42c82d0741198040c08090303002a501070310f0241e0001c0c1c408141ca401038030201055a03201c2420f4440c1005450159001c000600140d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 322037446 1250 322036196 322036199
    0x1060503161205122a0f1e010615110d0302030c0412023705060304050d030507091e03110913060f0e01020c071409012306071a01050a0807030c 63
    0x140c6202004182c80c001da0a44000840040f00e500169120007055961007508158005c001100f582e240c3c0407021440016050200340724070229990010304140c605c40040320002c003486030740e09512800042024a00c0b100c8880d10701840580503441a0b51134541c04c0c09030214901401c2d10078401c42c0d01c02d40110940c581040d080c041c680300c0420700054200e81260380c0e283d0560210040103a42c444088501d80302d0880c481c81404403003241a4142d10481c0247c3c014814000012008600242c1d1f1703091501e0009101e540e41c12003201c0240c1540d0060306041042661400c0851034401c0340d1058034001c1c01c910702d501b00a070301801000381c030840e462415501040560303000101c0c16003011824440710440450303880740b5406010300f282d000a10404c41507000b40d00400c001a42403000c012060740c200c0740d01d00c0d0b941c5000300c2030541d00c40b02092250342424001c060456942e9240590b0300454001c66840f641080d4005c030400803550a00880303100d462007101c0001c503900005081010f80c0e61044c03007209140e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 322038696 1250 322037446 322037459
    0x6010b04152a0c1406030c07020d02120706180b0d09050115080604021e1810032901171b0a0306020a120507021b240a0e030106050316 59
    0x31055441d10404005010050b4503000300140d80340709490110a0240c42d24a01d41e01d0220104550341e0302140e9110383c090186100c42c0d81d12815603a22444d046855a030301c0840e44006003543c8403030a40290b01403000e40a440c80c0080000381201520581e440b0b00c1603e0803031544100e4080e00a1017900c0364a6000c204000454000d900303d60042ca01c550004070701a02ea810142ca07020089400000320366004d40304000962504900000c8500c580d540c001e05840c40c3c000114000c100c14082c1509108080d40c0480e4060814941030001150840c0b92000c0003ca01800b5200d00c0d44910520403000c01036034004036900140c80d05910380b0401c014000e05d401100003054400c4254140d450640c402c1c2104400030100d94540000c0541d0b90b480e95841d641c417051201004115403010b0002d07030442d40445640e4a4464074031b060341801000403105840d2603200007280102406000f02000c4000d003021800e512074a410451160002508030001d102107901c480074150758000c0c00364801c05c00508282c2c1084007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 322039946 1250 322038696 322038719
    0x1d0a2601180b10091406010f0909061409010b072d02040c050c0f060613110d09060e0d031406010e0d05070915120503031302030f0f03030f150a1e1a0c060906010b04 72
    0x2407239a0341408440e007940d40381054101c6d1125030080e50300f084031001c591000e160440025015207600141c1e1400c02900b03884800081c21503043e42e82c4055410030540307441d000e20110010500360700a00070301403030031310440082240c1c101c1e441072807491081c400450f00100d404641c0174410780c0058040e11100341c459082c0c801a03d03590080d50382101c4d081000710324801140c059440e550f80111400f003200c001560785107160a142d10702c0032040524200c081d40c201e040c5414130f02d8221a0034a0038010000401c00011074109038007400401c1445864400079a00409801035074070041511003007850507664200d0030b091081101c000925030340040000441010803030003004c600f41e00140481c0c40e00b41e00003181c1d601d407049051603000c1d160f1001c010000065045000650f100c0b89400c560070050040300042520b40c6c040303004621100e5504400001044010f40910004010800544084401d82540610303d5401301240c9c84003405000c0c00140710041c0015020704035180e010149160a190080c82245c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 322041196 1250 322039946 322039967
    0x142d06040b03030d061e030503040303030c030b1207030303050702030c0a0f0c03020306010806090d030c02060622090303020304020301051602070315110a1d0a2601180b1009140601 79
    0x51055881620401d65141000904a0911005000110035080902c54101c4071046a441c405820428100340001500482030307504983c5d0600380801c01c01a016026409400042c4101d1f4009070341710701a4004060001d0744504a82c041d44040205854925040380c4a118074120181d19070f004175040701c0080c0421801e4004107005441d80309070740c0c1d05e907800241484030a90001050354040703820b0024000d81484803000211141c14104014205680c01075200c2c00c0040c00700e03104402c0f070146080c00610505400c0300003800d080c000c2062922528028000f9001034601381d000350710748000540c85c3c0c0c006941c0ea5610340866001442403504e56610301c01b41d00240304441001c641c541c051041c0c00322001c0c024005031040f130380b0f901c2c56004050501c0e900062103a140315218800300c3d0000c00c00f01d040180f04000160002e0b2059070755100c00d5008601400c110440300803103501d0300c05503806100f981c41ca03140c040c0d0b101511000301c06035502e61140c1990442d1480700c0400340103201281956010b811000c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 322042446 1250 322041196 322041199
    0x301060e0d080f030907060908030301060f0f0e0604090915060e0c0d0b09040609140a0c090c020703120e0108010e0606030a02090f0904050601060f050f0403030f050c0709142d06 78
    0x140f4009002c10912000e400503070b82d0040c03551188138103010403a0001802005020038100a41c155890818018845105103030302d5010302205080000750984240c00d00c3d104050090401a900d40d56801c401c0018180c00400395100a24080600008030103409410202c0761107041940058070b40740275086141e484020300000140c0d540711a403d064448505840c405c6004020004880c0b0303044c201510381d40c454860385442e54002e8400340b40040c1d0440440c20550b210414000345d10b0b032032685e00f030380b414080760005040090aa00303000f101b02d41c081e114640c44c01080c4e070780311a983d0381c0b143c403088002c80c10381e5040e603c44000e000040034031941d940685186000105010f00415031080824815101031b50140c0d0180c010340010700a043d0404070204000303c6524015262210325848038015020b2804024200501a03220841c0203101d03d00ba125132390300030b1042c0c404a5945000300ca000b03144011101249001010001d0658589184c00c12042e1140d00702044010000c101c0f002c00098008240d0f0303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 322043696 1250 322042446 322042463
    0x140c070e13061107021309030c0327030803060411070b060415050405251706090622050a0b0402042304061805180d0c12030204210c0603020301060e0d 66
    0x1a004640c6500510801c45403445080f44d448082e0300503c0a00403801c00c10015036420f011184001030b5010a1858500c0d400d85004801d0b04000b903403007500301031001c1001c0162480394802100b4400510011070040d03004440c01c0102465035000b00180780142c4a01418032141c4800080b031034100b98006104142e4070000c4142c46070340380c2c0f00180480f4801c1d40e05006920180150290701000d081075031003100d0351828614100182c80310802b41a8600030001805100301002154032a26005101580d04801c0ea00884040d001610071000524084131100b020b1806c101c203041960402d8821203054600200207801c10700c00c0e101c0100807000d14041215000340c1c0d80c4500240b01c4902000412001c3c1d00e28101050360308000e07080c1d01075030001580000050700681248000e8980204050011590000013580a0484038134140c009000325403140b0001c2c808407012000c442078050200e1000c51140200564190312400100c1c200d0000340102c2d404240440b64404081c40e0040701d01c84041d100c1c00c2c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 322044946 1250 322043696 322043731
    0x901020703081903050612031803030f0c0d090f0b04150207051005070209060a05060715090506180d020d1d0d050a03080f070c03020c06030603150c0307140c070e 71
    0x1102d4140c2e101c000400b454121861040d001d240d0326000b003640048040740c8248198801c819540c2d00ca1003000f0440c501241e0700d00d0a9011502c050058400d00c0e031401d10540c2e100e0303202c2c541c0d45854064000e0720000048000102080025000500c4070903282c910243d00d007043d0402d1500b03401032504604060644c80745140004180d9105148030850411568030a92204514414004c0142004d02000d2007404029001d020b41c1e2100c505807a0255000104c0b10700e1403115260703c50081c0750540003e05030380151400c01824640724200c07861100e812034121001011840d01c101d0b101c8020100060001e005504424460105142154a01940108010006a1b180e0b4806103000e000c860101c0100300c001c2c041121804070703001c0003039000c6400c0c10728400140c01a0340094036011624966840b5405c04408101035841c01c01400490f290001c000c8040303401c2c01d8440f210755400488020001490309800d46125005aa0543d1036050700e10000302140345c01c094400102c2c0070002c05047c40288461078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 322046196 1250 322044946 322044953
    0x152c0d031209050102090a0f0e0f0403090b0d0c080c16021201060905090c180910020d022109010c170609090c0603070509030d0c081b010e03131d06030607050901020703 74
    0x42c8586940316400041e03a414104040c08000c15a0f980710700c01502000004101c008011001c0540c402c1d281c2028540559031844c0690b414545a00a00c100400c040f0381100c8000007940401b03800c1120f81c5900f00e56503200f100051452003542016403a0103d21000c17940141016084944140c00810001c02c0c8243c40340e0340c8008a170707003c9810007c0c3e40d0040306012280c1c184280364440301000c48948a400e0315008014603900c000380740f903031465294001445c028816095041e258808041840d500b000322881a1100000780c00f41d40e8441e555203011205055a0301665104800501d5600000f085136290070800c100d00c20018415240c9006140080549a64000085100d01050f032034464403014030009040c0780420480c01001404600101f060108075100103803401404031043c400581d5480d200031902500c14144200c40038400485d03092021003010740750a00361241e02c6d6269200104150032a542c4602c162200781e0103410440104841078800d100803c169003060040f42e50300da03680c1d907 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 322047446 1250 322046196 322046201
    0xa03021c140114010f060206090718020f0a080601080109020901090909060b030703050a034d06131103060105060a0815090a06080c0a1a0d060e01152c0d0312 69
    0x30312000041000d0f80144030060111600101800552008020b00c0c50040c0055985103a603026a141d403401c0030300c540c800d005498040f524601c6c2a09056515000341c3c0c9000780610b0310a40301103022480407030000c80c01c0c8982e8402d8803000c10b0140c2d201a4094034000c040402005020f0301954a10b480311030303884158808112607001144904002e1202640d00c2c10000e144c0048120180d006480002c00c03035070154060b42e801a42d29a00f100e00760300c01d043c5d01d04001d41503200e054242d80e00b40901c1c020499110240c40484401d94028400c01c20707031b54049010142c48100900400ba0300200500000c489148508103040d8007111008542c2480c1d41c0e000000345142c0811111018040d8843d5414002820280980000c1040954100c00c610703040c54440b103d8000d6560107490240c0c00411ba010320020640c004000501e401006c55940d5612580031350311510419a030300f40850880c00c600c1c180203007500741150015414150080340c09280804003c0040134000c0d0640c108074881d0001d81c0700e05001e2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 322048696 1250 322047446 322047461
    0x20c0f0f0d0f0b01121205030f0402011b0b091c0503010e28090f02011101050f010b03090304090f0b180f04110a080312010302040c0507030203030f0612100606020601050a03021c1401 80
    0x50604900c440b41713500c0c114122000c480d1107001045024420b020411025a40c0150400d509007803150341c248080d110310351f1113007d1250182c00214400180810100e02041c05820300e104442412601c085038042990039100c2886950380c0110444005030500380110001014036540000000c070300c02001d5211002d84492078410750341000384131004000c560300030981c5130040201c40004e1200e4589541d5881200310144580004200000002045004140104c40151100035010401018114500001480c10b200c00c1c0340203020540154110791110744141d032144c034080c00c80314180c1c4e45580e03940006001d01d90396070307820640810010403011001d001420652501c00d0b0400280d41c5180100000d5600069051050100800612000c80c0c0d0101c11130f039008610844454003a02c803140402c1c00804a904204217030301031902404210450703504841b085510360f90880301d07940d072124100101d0000d9448001c0d44403041a8158010700021040e401c4114005d661498406078100c00300c50945021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 322049946 1250 322048696 322048709
    0x109080d0212010e010503030307030b0102010e12040503072103030c05070b04063806030619120506061012050709031e140a032a020409030f020c0f0f0d0f0b01 70
    0x2207103842c68030761005052401054100b079200d0180d4908004030361a0300c03019154604040e115414080964001d41000000713500c6003040f1a04400310a61411040c0c01174010f1601c42c0c09040d500007858808090740c0c84001204404110440c07a0b240d4095000740035540301e11050050a1041c580412103500d60700f882039000c2c0901050b80e2035141e40c1401c2d00b261000700680c00c05400a454030003070780390b15104034000c0e0050303a0341e03541c0740ca45500003400c05202c0390601c1411081c00c140459a50341400e8138140e0184100f044404030b40300c1804101000c80807800d02000030b55000e000c0d408050407504820341102541c20304000c00c0d500d0ba2650040c10710729441c034074120410708280904106602c40d089004210180180000b0019070307400800103614400c2c24104c3d100e2503500d820041e0103000a086030142d004004000b600300c1443c02030005041180010013500884054034054142080600001440100420300c040380e04020803451007108801980c00207118425030000821101e14503019050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 322051196 1250 322049946 322049951
    0xc022b050a1202160203010e06101a040906031119080c101e05090f04020f0306041e0903020a031403090a03050f0c0106030606092306090c120a05060114070305040e090109080d 77
    0x100c0c1d00506088d038291403031240d03466120600f00701d520310b002d82d000c40035034200030303070200f000c118008400169000d0358000c40c40652030b1103070010401001c6003a5025001c420355940302d01056200305c07010402180d1090715803e0300012985021407506e4800d00900c5417090a008042c43c50300c18601075040d0180000c1c4010401c00200c400c2c1924140d41e4041e0742c1c10003210254a4001840c0001d406800081c10306800b403a01e40511800380c9514101c2d03000040b04440d4208250324450800035615442c000c029030200b03004071018035892110b0002c0320b120340d401000502d043d18503654102c034907030310000442c00800400e01c4008460042030044800843c040c06c0d000c61498142000c0008540c61054250b4035a01070700d110041010031035500c554008811129000c0a960b504281441c42c895220310000b401026410407030030f46081ea0100e80a80700a82e40d100c9034540c080720a165501c00c01d0310240100702c040c4020440405c1c6040386da584181f1100011509c0340c0150745000245c0c114144002e505d94 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 322052446 1250 322051196 322051237
    0x30912050d020714061c060e0c040302040b09070206150a08100608010507030b1f09030f0b0906011a0403060509120403080a031b08040602070303110a030c022b050a1202 74
    0x2541042120080c14500102134070414a01000070250310a00f5104820342a0203581c0c0043c00050f58001c0c4010950790700030040c00d20300400f102c03031306034003500040f440b6500c1c01844000300d080c00e0b030280b44101d0803038000741801c1d00c5000c401141c0514103d400d40d8000c0e5440000300c0c040750709000308440c0c2c04103801c000c10407a040071562800d441006080380d041515041c065011503440c441015854040803c0700c03800483d40e0802110206150f400181c00e044026140c0410090b44040b4188128010000e4804690300c4000e042d00b26800f048001c1030b07031401404180040740d0154820307a0000324400842d80c00c0010001c9051803a049644242e900038004105030003459054011400c080341e02c540d00682c11554614007a08801011f04060200e5501150000415000780d110030340c110544840c46442d0118000d0003000341072103d110f40014099081190840100345581e425540100545880310b400364510840c0c0f240c0207408254100001c42030107506920261001b131501002d4500160040c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 322053696 1250 322052446 322052473
    0xa08031b0a0b0609100b040f15030606081501030209040c0302030f010b03010303090e182b0c05070e06010c0b0406090b06100e09060105071b05010306170304090903091205 75
    0x39a1440c40486a8000c0000078001415000c0183c0c3d00c450211420403c03074480c0c40c110001d40049400208105500003800314254558801c00300440340709242840c40303403e80705011000d85000d4426100032541507004503902030000e50818003043c0c0103248c018140040d5000040645080c403080c5008039500006100c1c412400690f0309003d03080f902e00061442d4507598000342962510f101c1c3d00c0e1141c9256020481c0c1148100d07030034468074045070444101000009081ca8555164910007000b10340e1280012181400713401c0b030708910f0303400c24082d00722a1f00d0450900c504000080500303040214602d05540010002d60200d40101e0160000250b010100d1038442c1e120070001e0b1003144a41c003640840480c160780300307034140c0140c0300030b81c2c005406480321030050714680a001c800901c1c03401c41c001c1c900d041107000101030040318001d0343c0520803241d40c1e01003400050751030701c0c1150094004000a014095458000007a0540700b45007052080e9520409500c100c8200f850441d025000a0601d0001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 322054946 1250 322053696 322053727
    0x1403100510021513030903020907030f05011208160309050607121407020d06090206090d05010b1504061209170a0f0e01030204060c0f3216030809040e0c0a0803 70
    0x1100001e000400c40150003040202c10303000002c01c16448400c4c48078100b81010311400c2c00000441d03014140c8040ca00f03114a01030080c15a29980300c01c942d161100005000100f450b000d0440c0e038002c1d03016031401c09900d03020000240da0400a034148107100c54005566100c0100400300c160143c8071640700c244130030030001c0400c46c154020fa00508818842e500159680310a20482954800b000189a081798804030302a80a030035621503104003201d1815051100641061100044c100c50f00e640488a000e038070050f6001e02e0060000103082c800d001001c1e2810f640c070408040d4011180100021a035000c500340f154004002e41001502c0010701d83c1d0f00315042814100c03003150900701581070906014004103c600b41c904044c0481031072040c014240000b4907807a0b8050304002001c5a5a60607449004500d807080c00382c1d244281c850403c1c5500d03201030301c0803840207a0ba805045945007003001400c003c06440303081c0304e0294600a51030944042d176070b001c0910004120f03d40140da20f03140740780d1102c4070303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 322056196 1250 322054946 322054969
    0x60504030614060105030a090f21021c08160504030503071a071103030a090f0c08060702060c070c180209030f0c040b04020c0d0f05160f0b0c1204060b0114031005 71
    0xc844072608180f0143e030ba0400c0a5070351041741120000380300707182c0307007011f03501810111005002d006400c0c2c01450b941041070401c8007000c9480e02165228609118080e8644a60000c14000100b002c8003003288121052040c004205161038500d0410b600d1f6181c141c10350b4400d00048030a90441c40c030350702200808450326980011942090030440302040600d0340c4901c8010301c0548000c0c1d4030402c1d08108490110300880031a00700400c0001580c44c0d920441d528032080c0c0303104026111300d40000e400440800d0440d4001075001000001207880c040c2801c0c45041c1d01d9285040a94090220201940b42040b5003038a05c54040700070400c250b10101400120360700001214000c60041020551006001660000b0180c0c03501c0c0a000c0100c060f282101c80f0300800140740c8002c910208098140101500d000c0903c0340220055555529002a071041a100c2e080c040e91a00c030651000170042109a401101e0110301030404040882150a82c1003a0350310489141350300c218050400e000380d040c00b03060f894 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 322057446 1250 322056196 322056221
    0x1207020109030c240908092805010e0105121e070221030406020f040806040506060111210c01020406091a0f041413020c03030613050c0405090406060f0605040306 71
    0x7004168546000b000040460806003076513288005501040c0746100030000040541d007820450300e14540340140481c3e110202030b9100342c0300b85c03440300326140e0102c40103c17010b09409440701143e0f107007500540748200100841030500205000d40d01c0354551080c9120321506085034101a4a01e11500c205000800603040508551112004076040d0388001b0030458060404000302e5200d13652407500002900c14001c14100540c0046000500d02d400018600d0055201c0da0030b41f1510340e201001101c111030044900407466011415483d01c50003e000d8080144241c0640700d07140c0f01140c01136500b60f90055101000040842400300b00142ca45035804a111141078880c074a02000d0a0011110f806103000c0c5412000c0310500d2a49585d441100440c0150704c0064155120449400c0440d200d4204903422401010340100c1080541c16901c01d5901c20f408491042c0d04181c20107041c0404814000c00442d100c947d1340001160784130301034000030010303c0d0580e1510760f11421803802e4026140c4000114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 322058696 1250 322057446 322057451
    0x120408120a09141204140301060305030403122703060207020f0603150a33051c0507110601030b31050303100e160c030309021009080c1e04020313150212070201 70
    0x413030314100380021541100d114141240641d0401000680144031b503500017001407000140000401500400d5041c0e440410385070500129243d02106011842c0541c0c0350007201046082070000034031550207004150b001a0000ca0003c400c031300421a194010740316070071821156101d840081c900006064040c1c07680011a065065070071038000781c001072083c070106800802105281c200340c400e17010f4806003440d901d0030351100000691000b0040101383c414500054803074010034074038400060140d040701d5003c1d810340c285503a003000d81541c01d41b264406000300d08042404108050720a8580c1000b9405203018603524140148003200c045542d900803840820088100110100d0f624100c400e650780d1420580100890f61030210010030f510b5000960140040c54001c469542c000c44000607141c0c4507049a100b02100c608000740240401040451344001c01501c5070340e42800c0e0041c541110b0100d22000344d15515a40e0134544021b1198200d10641e404901c92190300410740301c1d04c2c0c10401d02e0008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 322059946 1250 322058696 322058713
    0x10207020a050906010c08030c09042406050a0c0b040507260a080a0302212409130f170a03150303021c05040504180b06060f120408120a0914 62
    0x411681040c40c0302e10303482042040001842039000d038018042c2d180e403050034507543e131030214510151038206020300390240d441e08003406254440466104400207010040ca01c216203080f1017200c0035446403001000700300d1110f020000094541c0c15944c022441603014042260038505408403200c0000d0455140350041c403140800041d0214500d003159030040714065496549030800da019210740841a5003942a00d1030840080080e9108a8095020340382d558020f11000c151701c00007088410b11540c1e011030503401150100004040c01000305205424801202c4420780b0740d140c900c107104050b00241440010a0084250302d0311030009000c4090001d40d44e043d0440d10300960340c581c0e190803040540305034400d60010741e001d42c09490042030001c1050012800d4258003400d00600040100d610900c0b61000c40c20350300c0d0800a54541c1010824180d040c00d58140110f006e0040250055907080c0341001752125102400c40500d2151218240100340003500b80f41029600f0b070000010071690304180d04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 322061196 1250 322059946 322059949
    0x80301210c090b031f0504150608120702030c040c05070b060a0f090b01020a05060c0405030f010c0503040f0614040c0519080c1003110309061801090c030b3d0801020702 74
    0x9640e002e407200c50200103102c01003140420700d8882c2101882100c4019803110303650f0128550031192082d480b0300788403007800310221416829070342c40e40500320300f980040005a1061100c140030700b00040c0014110b6035400c0a140c0820100c6108030804000500001084400e100b820000560844010307190516a1450240042c0015103140128050346840d4465506141e1013007240018060b000b1041d1925400c08a15a0030691310a20555000e40140d00314851000d03010f100700c00302058240c0f40c0d01e185035243d80e1000039074040940e088920554400180361500342e81c11100388070354810795142601c5421f08013000aa44d010072803480102c00c0b052b00500064002040090001c501501e03125903102202e4070a6002d0a023480300d11200c00000b01c100709148800003800ba001e52403c5140211358422134010134245d85c1142000f514000c841a400c2000034040083d655110242d0140080fa40e0500c440d0241100f00001c00424100381e541d40411908802015807002041818001c602d480c0d415030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 322062446 1250 322061196 322061213
    0x206070c0f080d09050609100f050105101413060917010e0717030c06130c0509040507270f0605101706090703180c030b130f0b060f0303040308030121 66
    0x180400d5002c01c0040440f0610713040080d105a0200540e101032410b07405050341c0e6024500808211414910040712a0340c2520902c1d06841015205030080c1d52000320988041008098189684c0400c10100240c050f072038130020b0141045a46d43d600c5a80344c41c00c0c0c641c551030440140d01040e45080308050b5243d0002031040c0840700d4502c400c02040c10105015411406600b250041a0041c0002c010140c5403e40742654041d1040801c00740c1140c40f0414001c1480d0f040301c0080050f409000e09003c01c08048111000301500c0112031101c01d01e820308058140c50301190a071307003220b49480050085140032862031004d4a240c0c80e0460a03040344100314a12071030b010307201034014141c50011807480e900c240c2055400d4000c500e50064101c0c198a01480190014030054582d00030060205007468414030f0001001c641000f4403410100d516143c482141c0300c060810703a40b200304094003025946061020308002c500603032450340c27030b5854500c82c28094120550803aa0346100300c0030480025103104c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 322063696 1250 322062446 322062473
    0x1060f021c0e030a030c0209010803040302090a09020415031b080d020706051b01060308120f0c1210080f0307030e06190f0203040306050112060b0d020f120705090c0a0206070c 77
    0xd02881c0281066a000707407203020000706140e4050082c1c462000515420040421b802071083c1c1da07030100c60f070ba181d02483d26070190b40002035000e00003002050f040d00380f58104000d840d0004000050343c48003a100b4903111b00751a801141c0c40783d0416605039103003444103141030044c00303400060100201c98241c004d4036413406010f603600b40400400e0020301d81c440029006165507030340000700030603512828101902d42200d4000404174040f240011145030298140c0d50080d0722820907241004030700244019013603002051421400d07951800011807120030007040e03401e0149000650307a038080c2400c0c028038980482140e01e02038942080021012400717096005090003242c50290f40c60051020b0407402e40c42550700c06040181454000300f001d005d20342c1500901446000201f1010000b481403025240700d00c08040e50043c445080d89100b801d10f0545044805400410386000c00d480303000144031240d0584005544a03030104416001e542c040040c140c01075460f0810514005d0103980b030048a4015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 322064946 1250 322063696 322063723
    0x30c0306011401140706060803041e03080d0203040206070b0411010f081e040c0b030a0624120c12140405060603060c0304080a0c060c171806040f030e0a0905090601060f02 75
    0x40801e80c4c1c07801039250742039488081c2d01450502c03c55580303025581e80c0c1e030090b0081c0c0022821084403a040403440408c0f40003141c1e0b01401031810144010300020080d000100280c0e0402000c00007000002d040d520540e10561158021401541d00300000600308840d038078420f070510a9810511000d078404068191079481c21148101607030342c4503e0131030b01d00f1015503c0841803410110a00c0700d400e9540c0c0015043d1480c83c00c0c00c0240f42e903000011441c80380300d00008004609509600d40d4100081d030000301e4600c0c0c4900b03001e03007901c240e00e00844c2150848425000e103803072100d050001304071081c05041d40002c0101c0c01881e00e8103000311140094800940018094200094143e0085003e00e4190b11070603041801000040b201074409070510400b268070b0b20070304400c07100083d80d004030304110f00d2800444600506581c0c0d00c0782d554410341030700042e0903424012400754002c4c2c03c0c2d8440340d041026008032040441c1a04007003140034076001042c0c000809110002e0340991507903a00084010640c01d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 322066196 1250 322064946 322064957
    0x301292205131b18110307110106080a06021e0f030a0902010207051215090d1209050a020402040b070b06030129010e040e011505030f0a080a0e0901090506030c0306011401 75
    0x3a2030200e02510710640c0d1008110301c1000c0801640c412040030700e801282c0d0314072541101c0021100442c4c04441c1c03a0301050315070020500125070264402d0b42c4082c048104400000303411626220b00030300d421066002114402c0d00040c1e848985a413144601241c0501030400d241042465a000d00b84ca01004000c031000b1943c07160707030350250780c820400b24005000c05806040c0040f07525294503124904103011020000b68200800c0b107400c000a04443d5010040d9500b4104103041000c580140044010036070b9144211480100580d071588002c10042c824500130380c2d5030341ca16140614040030020002442a45003101d0114044154840d5010340003440b0401005040100300681300540c0002d96076400170320b03089210860150562040e100788441080c4401c03c25941c0c0101941c031100c0d4100e000082c2c01c00c6100d200001e80000241c1000207845c1443e400e501c03986408140f049400b603220425040d2254248011407c040c010100101410b4010740307000c4d81004600e050404225401c54100075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 322067446 1250 322066196 322066201
    0xd0c17101107031d0d120f0206090607120f060821070b0f07120f0606020c0d020a0608250c0b010605070b1b0c07030507030b0106170a02180301292205 66
    0x81d040c003080d03c068103005204904240503400d020121403004151b10021486c00440020034038000500389119030b8136600100040d9540e1001102c6441400d00740346002920351080c09440030580c05140054501c0c40d000b81400010391200d1a21600e80070b0610008030020040d01d80814106600e15606c28100c548102d915255031004a030850441c10021104914118661b090042c15070041d004440b040d608580164980c2d100704202c82c031203490020f611048a4100b0010035014003134a07540510400d55000c1d0024000c0070001c20503d40c0100400016500d800301020096002e56442c054019440d000b070414096a90f8040c0c0d160000c9e01d80130b107107070302032000d210300f4800c80c400c890444c14038400b0362315220341d40e2030f0484d41c900d0b885c0000c80307100b181100007049052007580111107200703240d0303011400ca03180c58040c0c0d002035008034010811048480d60a4529403003d001c0c3c5901c030245041d2000000c00803170081c0310300700e0080302498030402c40003051482031001c03081d0411180c05400e900044c01d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 322068696 1250 322067446 322067477
    0xa14070905060703050903010c0804021e0609040504020307030f030c1b080309040504021c0c03060b03031c1a040204030b061e0d0206130906030b01030311060103030804030503060d0c1710110703 85
    0xe000da1b0140d41c0e451b41c00d00d070108a505030700c00d815038025842a50580c4600b484d8142d040746c000e10032640c80c2d80200091015001e00c2c909600820380160002e426651007640b01c1d21411075650003603400b41e001c10b0252503041c08200d40302c0009200003c0081526070709900386502c10340c4078030444048030301c510786580114042d903a1b01051001c51202c0d00742809818500e0740340c070510801d01e42c1300a5131905c1c50042d8076041400d0100072140f102d0b071081d89405d10b07500385400c81300c0200414540013402408096081805464a100500185004040c1c04d005480c0060401c075038101601520100b104411040c002c041d1038036480d80c01d0107a4102e40e62a181c2040f94400c0c0c2041d29140d12180d209400d001c400021302030120540e5041e40e02a0391385080f20310014440c1c2e41d03680d01c02c0c400100001c00580015000c68400c0c0095034014600508020003038080e078072a6240f0b1803c94106849484c0a928039001a01d000c010301c5400c01038061080c40381c03407641c60140b8207074000c003030b4041d09210040c02c440d180c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 322069946 1250 322068696 322068707
    0x3060f0105130e0303091501080601210501020c0d0e0306061f0f0c150b0102070911031302010c200a0503120405120304081009020906040e0d030f0e0708060a14070905060703 76
    0x844a0b102c0c212505d070300d0040c4240342c0ea00c0301d0150b80c03684102e40c00004142248041000c0741650521800b031960200b8540c80f242c001080b02d141610719550038400e500f4240070501c540b5404102c00da44040c070030030010003050305220010f06420303c01c0c0030540d0307440415a40107007e400c0203541801e08401900023000d058860240301030004045950951040359111003950000410310001c4e0308941c1c3c40c0b510741141f8811070321500ca503408241c406000141150031150003c0034994418940304030396005030390301c003e80154122720060400030000e02c00000ca051103c01840201012801810001074a10070354125200744c0c040c95004d0081c110080c900500d00704104c4000381004800c50707000c8000c2d00711401c010000343d80101c0c403403006400821010f19141c011207440ca0980809040170740010300c41903005002400500c0096a140c9003900009081401000000c1c0111302c09861503140c41c0d190001122484603201e00c03c528868144070203280d0011401d025100244d6155179a005e84c1d003030070780c7c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 322071196 1250 322069946 322069961
    0x2100c03090c0e0103050d050705100b220c1215150c02031f1802010503150406090c08040210030c08010e090106030c060e010306050406050d0f06090602160b0603060f010513 76
    0x42c140d0984000412140e96200c0d98101c038040e10a480340403070000400c503682d01c114034001c0c046a000d14004000c4141e0381d4800019102d00401c0c00144c0221000c0d01a20001c200340103540c8140d817809040030700e030b0b0020359005400d804800204030340c003814040c3c84500d10712401081c0404125441e0280000e00445900840c030303400030202c2e2500c1803140c821034440c640145406002904064041c056261440310004407541c3c140c40e07140c216aaa1480344609642c031700c0760359a10588030f00c40001c000318640301d0a6140c50582e650041c884c901401480107201d01310042c4c01c100342c83d040980e004903500c0803615064500d0030b911007442c2c3d15031a104074054032094001500294030038000150b0349410040400e2154421380342441099500c008000484400341308860f08540310401590000340b890004400e61489124002108003854a9031f034104e0700440511840c000303600844a09000894100980c441400c4000303160924003c0f10303030305681d401031050900486458402071000c0809030403e10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 322072446 1250 322071196 322071203
    0x10020426010b1c0302010b09010f2d1805150f090405390109030b16110d0504030b0a020a050d020304080d0c05130b0f03070f02031309021902010c02100c0309 69
    0x14101c0301c0101c1c501d002c3d095080c0c1100907620b81018440d80e418240340d401d04a600844107201407518141e403100682d0030200b40e412414210010b0f41c0c164540303803000c450141030000200354410144031100421244040c00c42a620602e4050003851542c500d050800180d60649141d0025101c0346407451814201f0020001840c107035960a070084818800c00c12094062000c251034102106001590008480c1c000a480f0030400000181640340c4400340200e034044a141405541c0d04400c4881d051602e00c074078820004400003402c2050060018015030001e82c0213008600c0c20100403c00380062103440200c210003034000c40002c042c07143c600e0036107140d44400803092101c01070404000300b55a000310042812840b8900c170208004442c10306840c48100e0103251645103465519060340c0c01e4080841003c21403004001c04086106400c4081d0000c1c0503404c405615200900b88001e0640b044201d41d0045a141070b201440d800e90005510a00c511081d0000903240e01094040340030309074442c0f015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 322073696 1250 322072446 322072459
    0x20a0f1e0b0c0310090507120e0a1505180d050403030e04090f0308010510030b031203060a080d030608120c030a0809120403030206160c031e050d06030807030210020426010b 76
    0x16207415280c000e40c031075a030b400904c08000341c0300d4171350400b00c1e1001d807582400a0344644850315255141d030b0190b42034002d110201d070003105040c2d44000d446840e076404480340d292544203024040015002d5403115070300f00301c042e001c600b0315400010030a004502c0b0160401500114034105034a03140c1c412031010760082c52901e2311000c0340c140540414000c0c1f00d01c0d4015846400400350700c9209114411503540010068a1000084505a1307041d8202400e02540101e129000180300d410030001c07182e19000d5900e01040291a0103049030030007411490544551038100030000868001008980c0c0c05040c40c20550070648035120b0007480d10103402c0030354482e0034001a021080c0b41d000141d1130700ca00351650a80301081181c03e021038000b448210001c01013a00c00542810281c40c14090310581001880c006040c603509411410980e04141e000341c815000008040d400c0c541e051002e403891888402d410751a1902e0010b90354a00c0010b5941c100da584002285443c144000307410001d16084000c001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 322074946 1250 322073696 322073701
    0x7030f0c0f14060a1b080a020c070320090403200c030601080304050a0801020a02070b030a0f06060f030e0706020601090c050702030607090f0e06010e10021606050301060f020a0f1e0b 80
    0x6244166042d21100c80c00e200d020b0001c1e09034881c5000f41c14400303807000b0700b410380c1c1004003505480b0f0500251071090021f400388280401e0420800ca010025801100303c2072075110f0f01c0007000c284032040180b280c081c40040d4104000f00e0f8100d114914000001c2214081d0b55611003407640c100115a040b0a80c1806100000104000000b001d00b040d100100d4400c0030103951040ca040c01c0b44940d60700030001d0f80044030308000030128080a150700011004011070000c1c00546580b040750000e8001c01c0224420082c4007d00300e0741442103040403544400108181c0e42840000fa584540502c2031100842e2194200e4109500c90026a41340c0c0d07034003504071816810034500c042d02a800c0e902800c8801c03085480700041c0c44a10b6807001d8007030394068440035608402101032100100d00c400040055100b07a6001c44100344074246140c0080c00e0507626075031203506001c80101300420003080407086604c030400f9007000c60060801440c400360700c11044010485509000020340c3d42031400035014031200d008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 322076196 1250 322074946 322074953
    0x30f0e0d1b051009050f060f0f0a0f0339020f060112031b08031b07120201090b0109090822080d05120601050708092e1710080307030f0c0f 61
    0x201031041d110203d408004085102100700c80682d41071007084da1040c50f48200741501c0c1440c20041041000703031508145050100c40ba0658140d000201e00301c0010920032901c04050360501ca040c1c1d004e8450b0100d107114040d82d0008000c41c2500e098506140006841d83c064084c2c002c02c0b407880307101e141c1802c8e101e003507035109654400180b079401e05a003c500201c4001d55980042c0c03154512043d40704612a04540354003260349005003551021082003401013080740045650410400c01c02c55607a400420110200c0c07429442d564410b9002e016581e081008680c00250003005039002c101000c0d0140d000c4094070a0460400c80742644810b2860003284481000181c0c800020600c0001c6481c081e0003e0b112000111120b10030444080c0155409010281c0d4034a8028083c0d81c0140d041e810081c89200032800540306000464a0500403071043c111034404105581c00b400d0b400341c0c85401c0c01e45940d20340807009440e03114420000f010400d8101100d05618024000e100c032254000350000201019442d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 322077446 1250 322076196 322076243
    0x306010f120905210f0f030a06051201200a090506090604090e0601032a061209020312040e01080f0309012303040303020a030e0c0120012403150207030f0e0d 69
    0x100d00480107200042201484d0350134040340c4621000b400014500b42d00d03025500c00343c3d0030180644454545400c400070b43d5a60b1341ca0a240e40b4900c41000080e041c01c2249a01d00c1c0300002c2c070000580302020320002c618980c010401c602200e200380c450302e0f91403501d10001074061107142c10010310302d40703044030700b205100c8000342c007a040e607108904144031010900801c1e491030031007824111040e4410b140a10004d031040039401315404204001044240d0241d0020342045003100d5401d0348804045420020250000f20103801407864030082c000c400c59950390b45403244642d140590607c1170324044074220008ac014045100040d000c0e4ad942c403400c0904c4c0090195016a0411000900304001180710503400308481c030542c03005031580c201c650701100204403190f181c050301808a5694200703a40c2c0c0c3c42000c00c2045000034417001c2883d80e49080d481c1042e83e0080c03c002c0e8894051042c0500342c0002d820400c1d00f80e981c0d45a051403940c0700030312400180d294a2052004000f604a0040c2038150801407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 322078696 1250 322077446 322077463
    0x60f050c0a02060916061116060206090d11030d090c030501020d0b0906100f08090c031002091206010f031e0503070501050405010501050d0f08030c0910090303091205030306010f120905 81
    0x90b8291800340c0c4494074038a607104090049402444200038040203998003804d02084a54142025200800310042c2c0d0401d00001c181d0102000d43c100400b0404000c80500004010901ca8200345486400084846c0c3d0b60307000314001056150b6540c4004001e02590500300d03c01182c0c05402555500b0150340040090008484201c0c020301c80309000c074000349401760025075020600e07a10f40720718480410084407502009840c04040d40074000b07003c00c0b252000e0040f008800d82044000d80e4903d0705009121a6503480149801c894114800500960b10700d6196041140d40010590300d12038503003445480d084c000c540005266220000b031103400c002064018600c904c0c05203000700403580c0d8039000d0240350b8200c540014001c11905401c540084d041d58090b6802110b4002118202100140825050480d0100b01c00204080801c20403c1541c058041f074040c142e82c8040d410b181d5070503500c6503600d000c0904550f06201d102402440c04038071550801400c0c00718142c0900450f401c030706240c1e8840024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 322079946 1250 322078696 322078717
    0x80c010b1503040201021b0105130f0806070305190905070506030f1b19030f0e120d181709150f0c060a1b0f1206090b09090703110d060f050c 62
    0x1104640764900101e00036079100d590182c005d012900301c2481542c104000340e192242c1809010f1080349103003060041c0a002a12031304c801c410b9030600f4030310800e160030001444070b81014184001c10040300103156010b0914a02050301007500310483c6400c1d405d1217155004160000d80100030007601011807450131f4011000c1250001c071003a101031245949200d00940f184404456a403015440d80c8681c0c030061041d0706141d0009440490091aa810f112900168029448001c00c220241c119140700310a51404607030003601017407080c6c1d82d4240d20305400b85044080c00fa400308682c0526140c4516120f10340a050250130340c3d440d0501129080e580110141c40050b101741000038010b0b900791312662010307900c103040d02d021101e07000408441c10000c3c84d98100c01c1240320001e4605541507405050040c11400c00c000c2001c0140c83d042c801031007401482e4201c9580005000c0010901045881d07011080030f030755451081c03440c3c3c10008042c00c1c500c0e007402001458001000b6003c0380b0382000d0f014950b032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 322081196 1250 322079946 322079959
    0x16080a0905040f050928140c030d02011e0507180906090b0109120609020105210a0e0c01080a0522060e0105060a0f05040902011101020a0207080705061216020703080c010b 75
    0x203d00c9004001c65004550507941e0b54041e55030403500503525030b0080d4110075044101c84050030555503c0514020380000c3e0315844e40700718044192031405000c03400305100144000c12003282c42008080d81c04080350302051102d543c401c01308490501c125540212485884039030388030b581d5640c2e0408005e00c2c05204080050745005804a410340c882e0100300b04490b640c04c2c0c107042c196040e45800008105200f0100d051010030017140e12104100402c00d80031203049424a0742ea417070540002d0051b03a0609201d654141c004219032000c3da80c100022035001880709500141566540d0310f0b500c0d01d424100408403d80e5194541c40c002c02510f40c103c5444101254000d0045031102030030300403404154014a4050205c406040c8100e08060340480c920341c1c0140340c040340a0700c028101d98220b0b44480000380c010380000740d0900c080c040c1007012074000c0c1010741c3c00030301e80400c8000600c8005006880c0c500c920b0b224602c02402188200001405950458007103950340750344e000614024500100c0881c003591 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 322082446 1250 322081196 322081211
    0x5040c09081b011d030c09010303030902100c02101211070c032003030a11190f02030105071407031b080a081f050108060d020d0c1403100501030c030816080a090504 72
    0x40c0395503101c928000040e1600c0004c00c00004000c2c1481c0041880d0076058032400a42c4943c5544501c000d5000398040d03280015001d40d0350040c000d18001c569030030018003890210500c016200e900502c864043c181c40c1850310805201e1200000d40002c1c401c4003900000866018203200c680c0034414100c034407030044103d064840c054140c80741d009542026030301d600188442c0c1c3e0001c1c000e820801c3c8250480091350075502d00460012034400c110a000d03034016090785c0e4000c0441c1024481d603500414681044d000007080001005050302c40c15400404200300c40021811524052041c40d50a551025640da00d412921100403c0749000300d40240304183c00e041402780220314100e040381551010303580c4c06115501c2d101800904d20041200700d0700710346a0749856000c540404908000b810380c3d0995408059100702c201850044002c0f58072100900d8034004000003825100c1c0c0300d0480340d20880903900d070248080880c00c03403804800054000c1000080d0041103650100039003050300e10458040110302e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 322083696 1250 322082446 322082473
    0xa02010f0b01080c0a05120109090209060f060405040c02010b090403030905210414011b05060a150e0403030c050d09120809010c08150310181a04080301060c0201050405040c0908 78
    0x280c0d41c0300c009a001c00c0071030003c280d0f5600701c0002010b021420b82020791074903030440002d00b0904406d0340040402e594600d4108114135080980c10b41002e01124441c041000100005500c0d105612696200c0d03940c5100c2883c0d810300030b400030201c4031001441d02d00a17103070130f0030040e002c1c1003041411590750142a40c03416164042000c02c100c40307035000348102e0510341810403009145624602d000e05012905141c22588044140302240d268890340141c141e5003412800c0c003080c1c0e1211141d0b8450440c152000b8400724142a0005500c41e8061402040c0c03500301840079152845075040c41100f076420f25030440c050080c500c4103180c0c0000603640d6600607a9428284500b201d4501d03c03500300245604c00469045d014808911034210310090a49000401882144044402c50354802802c204071203054014400400c22844000e80780f4940a00d06103800d0380c610506100500a030414031043e0010700c0156482241500e01070302010f0001c018030a426000070700351111a03c00d034900c601c0352105442c2d25 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 322084946 1250 322083696 322083701
    0x281109010b07060f111b0f072123030405101b110a08010f06050a0611060103062003090a17091e03012019080f0601051b0d050a02010f 59
    0x484026800c100c2c20318442c1d96541e0084c04003a13000c20207030b42d02c0c0c450302101c04030900014001500c03840d40505551099500c1a0b0038440c040d10070b40f01a40000004000e805003110740301d1b07100c403100295a80400c01e14a40400c10500e5103d40200c5101c0d5128040d0300d6010000051059074402c4686514034141030b40d080f908407080c4480c08c04c4022030180000000380d480d0b0340031109204020900031030203445014250844036507d6000a20580b1507404000c1410515010300140c44549018486401c00c8030010380d441d101840020700740380d071b20764030400c40a420340480321010002a07038080c1d42c1e050202580d542e6092610041d1401d699213416045d2500c0c040c01154050b030005042801800010540498103041d02601e0a1701035488038041140d01c400c10041c95020041070f02e03903d45500c081082c0d120b2219241c000d050900c6490750a0000c1080041200c0794001403d03e002d9688940d00408041110820902d103841489004401d0060f55005805000310b560140c1c000c01092040103c1c0005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 322086196 1250 322084946 322084949
    0x12061a070b06030a030e1c05060c04050f030f0703031b08040f140a1a0d02070c090e0d08011a03090a060f0b18040b06010f0c0b01060503190203060a140328110901 71
    0x4151229151b05480c1090860315140d00000d406030014140d079519500c4c1010001c9411410042000806021310b2038402070024602c00305400608840c03001800c800c0e6503429600000c3c1c280042205094000c10070003504004e1707180d1100c800ca495681e02c0b8000d41561025000e030a09200f00001802e45a0624084040c03c80c0e03a8051016800c0040107142a0b959200550a59007180c0801c401404110045030b6180100000c1400144140c440c440e0270b41403200c0c2e140d6a0040040302e4004001c0c1c5441018031031200901152001d6583d241e024000340b414915a5008100b541009503014090300243e001c4038110740140d90b003040030101043c0607540c0d1441150010b080303c80005c0801d071103520802a511071441e103804c0ca928941020707150041141000d0340001c002130340c004100328042c220b509014140c1d0300441411360940c208900000c0a511440c040c0c0d80d840302d455450120103a0b400c1107403c4007160220b168543c0000f180c0b0300012a006120429500c0442c0701c14031007003908007200c0190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 322087446 1250 322086196 322086203
    0x8040314090a0b0a050d0908090a060f050403032006040323090a09090204095a05070f09021b03071205030a1515080a1a0112061a070b06030a 62
    0x5114108007410340e40341c1210300088100041401b54080901e002d2285008490041d1003468807506d0041c00c011100c50150400e0081216140310954050303003042c03da07400c3d20313070500b0540c5482540000350800050041da40d03440c244a0841808141030300402500b0300d0034521500c40104d100645811882c034420351490a411240d80703601040701d481254070944e0120705c01007000c0342d445200d881f00d03440c0141c0c081480b41094504036030545050036001d074000021a00b050000b4000e9147c0710b020140400040301ea00c4150401c82020742040340a020b050040e081c551054080703681c5651902000b9000074060500941000c40000720165000040d10003070b65101c43c4404110301c1418040b21550005020183c42c0c075225950345070f205114440d00d9024000640100d800381c4e0b0fa5450050245002a09404c0d9007850013001860040d4404015000e415081c20014620000c070b02501c0001c0c166603021124520041c1440307000c007824007000740445806007140c00c43c2a05d03050100358940300c0c1c3d032400a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 322088696 1250 322087446 322087459
    0x1b03030403030806030a05031b010b04140f04020d06050a15050612070f0309050316020103051003020f040b01090503240106110703030c03030209090f010f1a030a15150804031409 78
    0x100700007407040301c990f58890000360a40d56480d07000c1c1c1e145880d60708086003561809004905900302030a0900c42c00e1003d000483c3c040c440e4100240c40d038180c0000c081d1003a010184104002000e5440344c0c0c000c1403002d58401410480c9162200c07035a002805102e5030388580064444001070700b40341c4072040da4051058880c0e010b200341c640703000c1521a4024004d0306000e1585a40f8a44040391050014281c00140f41001d070b007400e40c0610004080b50802029489594032500d42031001d038513007040c14804210142d900181451800f80145e440048070792255500d8460a44041201c0c00e00841c032a45009525420b6038199880d000d0584030f181d40c01d4034800c0306510468040000c6445803228142c02c07802820014a40344211010420058003101c07404210744c661001000380d09084000a40248a5060100903404000b036404090344005403402e10000e4980340d00c540c144005800110052201e8420000c4d610340142e8041c00c00c441c03c07281500481c0e030440440b40c54101c040111080c6240007000e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 322089946 1250 322088696 322088699
    0xa0b070c060f020a122f060417070209090109050c180705070204230103020a06030c0804150608031b0c0d050a12140a020f060c07020105031603110304030f021b030304 73
    0x201c1c0c03525464103108085100d1130202402040c07280c0100c06129240d40da0340b40300c800804964030a10300c4c0c1a448000000c202040b9010702000218100390007542c0b00d0200000b1004401003410319020344e40001c0d52040d032140c02e01100440560000117124483c0040e522000100360400524440d41821002c140b00410005521284580c0081600030b100400c001407465468135401c2e054030b14841c031407081c810541c0c014015031419600c80340040c4054a414040c02c0c204040040079400d01410061004041d40141c1d0069510323904047c2c050f02c403150072280c440410341c03003071805881050000055401b80d59240390807418152505625290444003c0c03800d07940b075640362820400c01101600c02c103e80c042e821070905820360000c00c4036034540d9004200d2140c000c0099400c04102038000c13a0002000c000100043c2d0300002640d51120240e4902c0c00a02d807a9030058002e40200d180c03031900400c0020402c000c0503000b041d200d02c030601035402c4030b140210590001001d82401c0400c00e615a205200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 322091196 1250 322089946 322089959
    0x9060b0706061707030b0406091a04030801091b05090a0306020304080417012d060f1e080c0120070518041401050c0f0c070b04091d03070f0201080601030b0a140a0b070c 74
    0x6c581d03400500c01c07500003490220584075000d9907400440000076140e40380701030005141d804a181809044120810802111501c10300104a40303051451405d019010a00110983d19040300000451b0040000e568900c4c1c0f91910441951090058201c8000540f01207030100c0014031510740c0c0340c1c0e18410b03030034180e010800543c4040400b80c0004016961103c00208986050b240d0030401880314107044c85d045034122065548686058000c4990340c7e0003141000980e82c0d218006401d0f00d5841a1442d03d00f80300248250700f42500c50f000107401c881c0340240c41c5044c26082d0106c9219038020801c5180c20f03a020f902c5103098940079108007150240c18415410441d641900408040104100300c0f940c041c0d81e65070002c02600554030421081d50f0f240c50440c80e07030410130343c100394403854003000e5460b040b001d80e1203050041ca022006810852840c0005401ba4082e40c003545c0c6042c0d006000c0d9100c02e0703655200404404d03801002034007079a010b14002a403400d5a80554900a0340420742c1d0014508015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 322092446 1250 322091196 322091213
    0xd051c030c0806041a100302030105011202030f060d150606020a0c05010509030a020603060f030a200108091005100509101701060302010c14031b03090f0907050a0f0909060b070606170703 82
    0x1011005914026018800d180e83d443d181c201d52038681e611f005d03890b5850980003402c00c1d01c1003490603140703900400412250103890700c407195014030101c4003520010503e050401210000c2c2d19001c0c4541d241032400704056070000381c0f2802062040365160a0036458800444150240414258056210643c103000502e0b00001469000f800508040c80201040002074a020150b032015215820001400d0444a030104800e4028100a0070644040e0a02c14040e55031080d500406018140d581c00219040160000415006220041000e070795420a006c006580d542148070700c440802c10710010140c0444180101811660140c658131001003003502c807081307241400e4240c1c440600040200e60440ca00c2280c00040012240c4000c5854014440520003500c0c42c0c0d0403014850038480c01041002a4408112540c4030454a0314040f4500d5a0304181c6101010b900014005820f03c08040f801c621500040c1061b54000c620a1100c00d41d160086600031840083d4889140c010b05024000b003079020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 322093696 1250 322092446 322092461
    0x12060904080f0d06050909010908070b0405030409140a1413080708090a030b0115020715050d060506040801140a0903020a03050a051204080307080f10061404050d051c030c080604 78
    0x80810038904220382e0389500c80e942c0a501807080b40c590302d0310180301904054005551244c0e480700208010300700c98a91103c90301480100070300507148580050100202032080d5001416242d0007800380350f08003010641b000300c00b00c07543d00045251814841090f40d10700703150360040004c2020b9401a107071540f00c1c00100d0744149415900020100004c211a0725413210324001076005103020309965061000710201c01201002c1c51003194020b070001d2010350000341c056941c004650510903651000003072804081c0030281d001c10f0740240c01040c0001c4c07101c019000b001903028214900e0b40d00d0f0703641500500482d01c50110142c0180d0051400000203800382004061300079450803c0e038103146060b006c440003810704071001c80d1350320340110601499581140c0f1182d0440354103900742d080751420782200941d103001d0b4420201000314008190002403204012140607001c081c01080c000c24040c20100d40d20398000c40b028591402d41c5015518451080c49010844410343d9600c280f182c41c0c2e00c080001809a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 322094946 1250 322093696 322093703
    0x909070807140f0c03030c0726030112060f1a030f24091c09300611090d05070521100b040e34120204020708130e060a0b12060904 57
    0x4102d004e0031508200041d5200358010f1a08540d110268641448140e05503069540028402034092a41c15160020390341903401c0d82c410004070710304034100b003405042011001d241d007a2800b008000462101d208200020b42e0a408a5105c7c0701e02000d00313a910b03529a041407500d1001d00301403d88480d42c2d82006500845050b00700d407107545580c0030080306400714002c4035000c10341c2d292040207510500101103001203a01800d40c4010900349080c6e01c40c10201c804000d040c00d076144501e00300b480744401990724151014040d042c2c440013600e006a42c45000b40039061007114048641200542e014814503140f441c00d0014042041c2d040100d40082e044400d07070302e584652a8a0401c102090030400f03001e0082c401c103000c0d9680443d9441111a40804405d09004009092014004016401405105541d06440050f900c4d12a0b090408841c05442c00d8414024008000041c10f02101c0644074000d06085a480d070710ba541e03818140850f44a0300f050b440403041080c1c000341080c034044940a900501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 322096196 1250 322094946 322094977
    0xb1302061b0304030c090203010e060f1f03020c0105090106031211011806020a1409010c080913240902030402010e04090311070b1b010902010203030c03070c0503040b090907080714 79
    0x100c0d034040300188840c444088a090b407010408006101c0704103060802480740340c03801c48c503550502c0e85000070144001c040500030001c8840c0e6400a407034901081d000c290301030b802610306004a0302d006001c3d511944840d0119030070600800e407454010b202c1e501c200d03544802d80309111154642d0554030704c40c4507162401c003035603034904010560000841d601e40d518440d500c011380d1205c010101901002c0914030f06110900140500c8400341d0300503440444142d0855031041d1510b01d5000003414110020341440c000a082c191400d60700000c220500c002849802e200100481d120351031003089000c210360190002e1790b1000d4507406170400798082c00b4124000c3c034040800c0d81503600900d2424900b50b1160070380001c0001ea005401c662032100843d03084d2010020300091519800013540c81c0009800303000e100b90008003107001c0d01c3c024524044241c0d4000c003500d803119510440d060b2240c00c40c040b0140944500d00018403014410103034184034002c0d40e219070040c080d0342403070f034090703a080420500313060b21 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 322097446 1250 322096196 322096207
    0x8071203022a1905040207080a0305071e12020903010207050c1203030712020c010b1206180f120f0c010c0801091409070e0910020d0c0221030105010f12020d14010f030b130206 77
    0x460b0f86c001800d0381809000b0203980d516507a04028200d80005040b03008101d8030002c045215141742d2142c0e00c0f4400d852034881142100448050000e2142d165003d1f0f05610025651040150203e24845a41e00c00c40c0c90403003200092030350315241d00c011900f0300e000a020b08044003040e00164054440e52100000008602c903041e8003240402045d102c4000460b4441007c100003c1e152101d80f00b1010150f0303010b0003c1141e640d030b41c3d55661305411800d9050042c0851580c02d074910081c203950004a82c40b00900c4034007054000607215103001c0c041e2044180c1400074000c1004005d61040d4016920140103059440c5400c0002480d040d0140c078174081c9004a4114030014a100d001425000030300603400103604401e00c138042d15200c006110000301c2103d42c4080c2400c818024140c81c1124006c0c03d2002d000c10f00d480d0704641c65889444021b40d0a44041034451269010b50b024841d03101040500d02c40591301c4110300180449540710003010711200340002042600010400c450080c4003419060038030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 322098696 1250 322097446 322097449
    0x32306061606091b050103020403020f0409030c0206040902040311060a021b06042303010506030f060a050403120c02150c04050a090f0204241205040b070806030708071203022a1905 79
    0x580070f048003520204000c00c2c080300312002012400000b0700382400e0440c80c146c40c41e80403888407603007034903100c1c0329a0b694181202498020803440302d215a00800c5169901c1d120300c200402174000c1d000030794150043d000101c1860030310104072000c054203600149144c440ca00d500d8042950008003858101005000011f8080950814600341190780c00004ad083da403030805250031114002d107041e11a40c0804000325101c040840d14680140c40c00e140450580d030345041c1520100040940031644518020210000c030754003048800703030303982030007038008a503114111b020340301340a1030043c1c59000048034130070494a5001d60001e9042c10400c3c00240c2080d40c5c0303441590007091056440307480003544480700751009520103d5113003854040030b000c02460402d038a0300b0107000001011070041c49108000705d41c0d566002c01c51907005007407600403a1b200e1030716500d2811070100c0c0014214003512804120010074a103252511400080034207055010782160801c011608a2701140c01e506820b80f900c003c01d49 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 322099946 1250 322098696 322098701
    0x170610022a0108060306101e1208030603010516080c0a11070806010e0a020c030306010c051e0f0c030f0c060f0c0102040306051009150501140c06010305070303032306061606 76
    0x800740c1809030009200314000015184030001441c5a200e500948208000300d1820840941680c030814424030521800402c01c03c8580400e801000072402000251002c02141d100203610640090b402801240c172a82e40c20802c3c2e4107000303800c6000c541c1d11400220f644801c4009841c3d80c0300b0b43d140c403695215596044504000094003c2d040640104006004c8810404030054000d910122708601e80444e027201984c40380406403045040141c000c8540007800000c01c202c81d950304d80615143c0d00700d003090b1242d56035010701030304494039400f581c0c80940c4580350200e01614100260b40180400210304020084030790f00c00014111a40340074082c10540203030034800b4101441c8941c0002401e07041140c40c07030b06110b1555000b1039649092100130507408501440c0c000803031f0030070700f413003507105a5404070712038980550034070480284a103030000001d001d00020224200c90090310100514005290305441040101e81076803034030001080414030307900b0900001c240781e105045000b10b0408940d41c82200f07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 322101196 1250 322099946 322099993
    0x901031112090601080307050d03050601032c2e0e0a0b04050105090105060a05061c0b04020d0915050f04080a0c0b0c28090308030901090605040308070f17061002 71
    0x180700d0612041100a0741d04016490250856500440c1030980f00c0c2d849907078403600460000101034640011581c164000d4000202c0600c0d10001c1028418001ca50112681000041111941304115030407001c02030368111001d460008105c60051480c0039402100504000811140340e48540341d03e046c04281f200c03402d00d0045109100120722800c192412600755080540b81911500212008010315a19041101c40865014980c02c00000000c109040140702c1420580d4000d8000601c0075404d40b2590b01c0b88103a40c2c030440786850828084c54591045800c1143c1800c0d280b01e48202003008204c000d809484ca00903946020b040c2c02490b0307076598440c0e0805913141c4101c40740105110188103001010200203540c682d42880c01c020040400514bc240c05d4440500515000408a0a4190203400454805070460380510040c20b0a2038003d041ca0070481302c48001400303003900080003d100d40c20a00400c0e000300c40d5048140c880750104038601d000c141898066108449090101920114010b42c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 322102446 1250 322101196 322101217
    0x3040302030c060640020c0a020405101202010c2d0308070809060a09140303132003070603020903030c06192f130b03151201091709010311 61
    0x151140020202c03685030000280c00f803442103140e03102a0400c40b03c107403c2e042c182c0b00b42445042c100c5929810319a0031440040c85101018000a00c0e007038000e0300007035400a49442690100400e603154910b41d00344580d6070090415441c40315543c03a000d2f601c141030b96002d0902503d84002001035a554041c0c40404141000c000111012600d606158010b6860b9a03c551682802445803a14514464503404001d20850040b5070310300300c00301802140d20715000d03425100c9046917030303e04000c0350317489040c0e500003800c40e022145810f00c0e100781004000c8072400028041e0080146604050341500690007401d43d07940c0522003448040300000c1d0402c00c042c020f01d10b40e2115805005079001c00e409030345801c107045030030b00c03d2004944811348800da44440301c02d643c071000680310304e080b2804850308075407507104075a0500302009200185a40c084201e000c190115030008005c0e800000d418203a0b691000c0261034079092112010b0000030700e03001081e01040500d000204541c408144400503000800841b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 322103696 1250 322102446 322102453
    0x171c030209180a06150e0d060e0a0f060e1c0f031e1505090a02070c030224040f1509080d080411040207050a060c090b0f0a0504050d0302010207020a14010e0603041703040302 76
    0x1044070062003174003100080c0040c945490420083e07804510071100e10b0700700801055035505891100303d014404280040e40c0654800c804620f40d05101d40078040900c040700f264058506002002c6c40b2842041c01060311944511183c0d04403010240d00034107580ca01d004021010700f26140442c80c0c6807260b200750034010400444028145003c4c040342400060804454a10402500001c21400594403040300d504851007080403c514419001c11114840c005001202c0441c0c040340007035081401c0016079a501000707042450300080c0499055007a4424000950480c0e071000200074410400c06034014041c5414000194100d030110341207900509058403190840030f440c4040181c2c0d8001c64800d80140e290800c035050034081245041c0c401c840c90f1403840000025400303101030261054030000d290085c511400010b540c2000f030b02079408848100d2158140c0320700421041d814500110014006170f40f001d40f0910001d09018041e880980140c44d401070002c4803a03140840403008612a82c0f103a40039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 322104946 1250 322103696 322103699
    0x307030b0907150c1a1504020d020d051003030e030a0809090603011e090303060e070801060c0609021801050325060f090305033f22050a0804171c030209180a06 70
    0xc104050422a010032480d000f6070900c0710111800b1b40c2ca891290041f20010b030742e5440170094000134400c1001008005080604000c01d141e800c86008007124040d4803200b0078040003204258840c044a01d0003400001c06200c08501c60608031545580203001a00000325040d00480054141e5074030f5420601c0244c90b004d0f19400c00da4113001746802441c2400da15005800e0220000d000c41c041401218100b00b40d5600b6042440a81d420070b404158001c0c106140c028174184018021150900a01e8041d2003014000000000103501e0b00192420b0030652401850415400b00c5600341d03120001c2c07003084100702c0040f0115105200a01130700c01910056502071916200004642c83d0001c04140400c112030141c4a03240c5640760000d0344401644408040443d0026540a8003c80d40c5d070041c00c6c52085116030000c000e0b81e14000d0040d282c00340642881341d0950260559a041088411901c8060b4949200051400707074002d80141c0000500c001c082490300f2000583c8040d08940e03148026445100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 322106196 1250 322104946 322104953
    0x40f0e070503010e07210f051c0f020607050a11100c18181d030316030e0c03100c05160c030b06010311090d0809060a0504030507080601050307030b0907150c 69
    0x200c4001020190000e001c1d628403c00059100e0f0f02911901e800c6500c2e8001c2d880e00921001311540c0020307400083d5500d440300750304142d0b5482601c02001804800b140320b1491440340108080c3d0391210490b40203003540c0c5d80e00301d0115100d4203d12805001e0010044008540660900941d250450003600003d10108c100e2401050314400554068011007074800602102030001c021314051590400c0104040c2180c56070b0340781c034400b01d001203045070001105001201c0c0000381d20004050050380c09000c10701c183c81d0800c0d15145103001c3e00707515a01c203690016090701c80c0e4000c07460042d190f040c600e05180031745800b8120b039440000c003210154040941403041103140b180319174000f5001c0c603080180148010b0703048103a114525145120301d060220705020003542c01c1c211610310001600941c1c40e04101000940a5009400100c81c1402030302008501c01500080090480f04001c004104175450358468811651010b08100558007800d1b801055406000444421a034159030320403601045905 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 322107446 1250 322106196 322106203
    0xc021c0506040b0a020a0f030902060f040b09040506061804050a020408010509030703230403060b03070503031c1b0e01080a061d07081003020f060c0709060e0f310809040f0e 76
    0x3c00784c00111744103000b180c540503404682441200d1141c1400500409140009401d60084080c1e02c030b600380000801061020000c2c024000a4409580c00d01c0140ca80604014581c01490440240c0b000078005080c01841c094004030382080a14000625003501d554903a425220704072101d11441e4400a1070404251b4401c0907400d101c040482c1c000071524103c0c90b010380e01d105170300c80600901d450325034034081d030340c0d062102d6002000010110703651007401080310049101051100d03a0118030304a18850002103580b03100e4180d4120350740b030110340e1001400642ea04c40025003018000b6943d1701c0042083c2034111a200c4041c550580740c0320306803402c80030090101000030640c00c5807084071001000142c603000034000342c000b02155442e481e1382c1458642da10300002c80c1d111580c3d05050040c00280b610911a58a000f00040c11100d2081c1c3c3c0c4114408080400042e41004040c401d1503145404603006180e100145100700541480c4c824240c0018060350404201035100a949065144140c2403c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 322108696 1250 322107446 322107451
    0x140d17160618231c02150a0e0c060306060901050705070e07030f06090c0905060c0f03040f03050d17010e040f080c07050a05030718020f04050307060503040203011401030b070c021c0506040b 83
    0x800400d0302d0802041030440d203c01e03075041d1344030380544c0800b080110345000340060700656103d1500044240317404c4001401824018030700c1c0c0380300e00802d0381c81d4503d82444c404482c4a03010281a0b607251001080044805901040c1d05440c0d80c00744480200d00701f20b0542c6164040e03001c40d074000c502601c12800c03070000c0f1005540403410751450982c1c0c0d0100d140d0072284a50031034004a43c1681c41e41440c000c0703e400c180c950042c250141c003002401041c01c14194080b003050b00d0040c030494001c015866029180c2d000d010b1711030b618100721240100040d181110190307500510441101d1808491036039410420f8129040f00c00031500079003c00c2c84a814a044900000d20b400c40c0100b480d40d2a2980d0b00341d807103508000020304180c00007500c100c8440b11030119401480054200d81d0900e0f42d5010003441a08240c4040b44607501307040e0200c8120256500490503a5000721540c03520751a0401c0035070f00000200e00c00ca8000d41350603e00002070105030200f1190a0080e000b4054a00c4c1ca86004e82100000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 322109946 1250 322108696 322108733
    0xf0f030f0e0f031c1107060809070e0108060c0a030b09010b0304020f010228060b0a030c060e060304032a02090a02040e010902030c07020909031c06140d17160618 71
    0x2208610304241d40001da042c1d40380c5080c0b5828003138108034203c03c0703510805142800c3c000740710b400c4001401b01e032301425551152207504180d488040c2c81e02e0301407004420030701c646607003a071100003c03071100901000280008103ca007400983c2404071004100355006c240e010324010b01002c001c100541c20942032005d440340091016100d003480952a241110b0f510014800212040603100410410386900c8030310409402029030250079603904d8986401d101a001d03600018040d000c8440d0141002419a80100d1307064941c22010103140310091036190610341d16814045c40d000c0d076540580c0700c5031400d40c040c2110300300240e611810040f100b6644001079124524446c4100f0810140c01000b1742503c14040d8110343d03411042d103c45104619501a80e586c407500042c108070200e80010040e40040d048417210266003500312402000c22003210f4010b030000d01007007000240c0911b0480c5207001003080b4504640e51032289070041d1078003012110038030503c060b1000788002000c00d1245500300341965044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 322111196 1250 322109946 322109959
    0x6051e13060f050d2a1103040b13052e0314010608042415060c0c0b0c030408010c020c0f18041101050409060806060a0e011a070f0204051005100311160f0f030f0e 71
    0x4000c600c06e40d80788034500c01d00c1c1d491032000c522681100c00784000b6100510b001490110303600e28601c0d601c8080e910071004100000c00d0300c4039402d20315000780168405004c03141c0803091715a107001d00c1a110454001e02c00c03900e4007110120094030b503480b00641c0700080708440d030000312038445020303001169040fa00100140300c525805040018004610341056070b0140004e5901c41e50b00490441c03860080e0380051a0035403e000c40351100300c3d40083c070700155100850f00800000f94510a1010811235210641060380e440400200840c540f40c0200f00504d8040c035005d45040d03035400206086544940103418960000b10500c680c901d446080180071741002c40b00480d49500d42002c90620340394080d203000c040d0313a0120703483d010301401d49840d49400340c02800611007460249134620300240d080c054180b16407502140003610074483d00c11600c034402542c0c011032800790384807218007504500e81000c90304854820600000103000100307012982e88a501c440e42d5800001c03801500008195820340c1c0101d6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 322112446 1250 322111196 322111217
    0x30c03140a0903031b030213090b030d080615070309080f0c130b060904090b060a154d010b0f0d06020307110706051e13060f050d2a 58
    0x30302440c040341d003014400307000041d680ca107464160050800c9181c0c006602c41c00000f884c1d09950160010000c5c064076500c0e03d41070365211102c00085680001c80e00e60541d01c900844815039008500440c0c001c00c00a001504446441a400142d41d0080d003048000880680081210030030421044000d80344407000380c86140b0b64271700869051801940003e01c025150002103007107413144401c403510210042d10500581c0203d00f480d0110003001d44405000e2001064001070343c503884a808240000e595136521520003407116906601c0c44111072061540c5508400b101500181030505c1c203580c66070417100c4074130590b1750201d00d084403c0742d070303516000d429820342604e0309544640311211020381c48000143c481e01d81341003c440b8080c04050046003442446800315117036402c10003804090810b0009544001000b81e4022140d0165180289255000000034000c482c000c1100c020004580d140450800242400310000e0340c2045240180c403400d803041c01104800140c20a0501841a090070018907 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 322113696 1250 322112446 322112471
    0x22151d0306040305031f06050c06090c0105031303030f0c0e010f0504030b0f0901020903011409070906050d0b0705070c1d0a0c0e010e0102030409060902030703050f040f0b040c050306100501030c03 86
    0x141d10082009042050000005140304050301d000040240e040311040034894644d0000307031031980300001230003084c0318541c000340040d000001c80c0700c008031040e501c1c0c5007903889180c00d008222507600400c07414551901100319400e1120710541900400541d524034865144000240003140f200042c8010440108024000300d048240c00d1504980f42c2e403e25125a503400c02e80500900903003c2e81a819400c100f44600440d03003403c1d516005230200802c0c1c1d480c4640d207407044022a0194407846030000002c2038103c01007002001f00c0c59029820f410a503203410100e584248184040390402c81d005112031850351824105003445a0340480141400c110255101c3d201500c0204070080c8e150400180740c412001c130764800d100341c42c01030080707040034080c498480c0b00d00c00207500111040f500191619000410b4120f07400092405150000c2580e040080b2030b0702c07a10031103040144103813a460a49800064a510200a510711840b43d03541c82c0480b050500e000107003a5410486040304243c00d060320030404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 322114946 1250 322113696 322113703
    0xa0e062d030a0b010e01211b120501090b0a151203020a0c03050109110915090912040602030c060604060e0a0f1119021501053105090321010b040b22151d03 68
    0x4a68000c00403148c1414441c044926410f40354100d036600544824000040200c15000300d02c06c2445103d550815584080c5031030b0407a0b0001c01d003010390102c2144200f2020100081d20b6074446e001e441a40c0f11051036071904081802c0c664012038441e990b0390303000010312000791b40d03400700d40d2402c031040d0b04281000b81c00840d810600c102d0181c0b04444e14804206411001c11030000300140b80700c9180d80703666940002030340305d400280240b8824020080082c10710710705403091506a4440d050100d0341c0d9102d00c05d0960042c002c1250b501490341d80c0c3c044500e1b0f021301b500003405510702400a1030f031205081c0900203051501c0d04001000022a00740148616a100444028a41c3e0721000300b12403110703800b860300324000300c1c02560345a1a1624041c803144000100c020f0040c0104002c070054022044121100109030921402220410a000178000c2c4001c14009002e150791050307440f074410740c0161a09044030802e500902c44d204031711501c9855990084213a000c2c102103000c5101842c3d8011010a44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 322116196 1250 322114946 322115009
    0xf0207030c1401060314071e080601450c1719090803040b0601080f0403022a0907050301140a12110a120f020a0e062d030a0b010e01 58
    0x410109010501c41e42c2548141e000b075401c100802c8446108405040e03ca000b00d004408902e60074080141c5104030080240c01141c400c071004040680c80c0c500080415501101c0c4022841c101d20801c02440519003660100d4400540140028026105031281102d600d051030f8814020380100300e9041130100204998052a003811101202840c03850010041040311002825440040b0030300003400800c01d54540b16680c282c0320101103440380b0540202c039138400c460050050b0f21610203400c03c141a04110000354202501c20310050449900240205004035030440018001000402607003041e14078404120a064500108103070600582d030500380382100c0b020b00070f810600f02100700c1d030320b400b000c6400601c1a60320510080c4214500f40d160a24280303402da2003143c0d011008207129042c440c1705ca0080100034164080c1e0b10309075400c40420304800700245075295803e11100701d161000d015800c0811700c0749908003250349c105400c0c2189007a060b00545d02880400c415107002001080021a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 322117446 1250 322116196 322116203
    0xa050a050411040c0e120d0207080a120e010e0324070c1a0c070804080a020414091c12060609030501180302060a0902040b04020c1c02010c09091505060f04090f0207030c 74
    0x14154041c8006407a00d4917116003840e009048025138000030750010811030b0304226a5800d40700069561569a50ba840b2074078006410f000d45001c00c90703480c1d406012907402c0548181440c0304040b00c418000380c1030401c41c81c1c1c076034444912580c2c0410b0610308103c030b0301d42c006c04604008190717502d2500c640f4900e00c0717055076101d0720b060350034041064200742c034055600c0c25a004000e60b0740c0d1070325060070719111400c14804078011401d01c0245410010000f5207a41302d0007001d4000c0c0310380010b0340c501d01e021252a85200d0184502e01c1018200030215014400c054130300c0b5158204400d14515060342114486c1420f01c4101c42241d440c1e1000940c00705400d034000140880125800d00203000050040105c5020240c0c086d01c002403540302c5400210f62840c01c803500700540e22a600220b942a401c5c3d90108441000143e0907441c01c1c0546182d6034402a8101100c12450f90036070380310800719000f544880740d00e20307448078003041c104850f051a0207240304a00703003c074040d801d100707ca5a000d041031106c41d0008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 322118696 1250 322117446 322117451
    0x3040516080718021315080c040b0313030c060612110a0605030f04140106150305090105010b0d180204060f05191406160507060504181a0103020309070e010801050a050a05041104 78
    0xc0143c60659015103444100c06a4003403000b640d1410b81001a0b8100344c0600007081030000001c0040c5440f105940455201c1050b49241d540e42e5100116802c2c0907071011824010352201200210b411307441050050104000b002d459041d10b800d14041409102410b540300d070090031414001c041d40070043d281c200e072000f4030a5019854034500541c410300ca51100940c0c96103458000500300c4007040030144c0c0d298894504200903201c1717200301030a98000b40078018114104004000c0400d00a6003c410000c1c44074240303005070348080d130020b4140c5185a10940000615090501903450300f520f02c0d010500314000c108500510b0401440382c02009a0401c511404020500600e00c0c00e0b8210302049003135024054504040e15400f01601c07540041c000d84400110f05030107000c1080c203d1040b07841e4006006407000c1404c611200441c06540020201030042c010f500740010a9003400b0406170180180a001160b6490410081c50803100010161581300c4d080c04144070215411940100c0038140981d0301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 322119946 1250 322118696 322118729
    0x304030f151b080114030705010f110102070b041403071205070f060f0e1606050714011b030525050a080c0903031b0f0a0218040507050d08030405160807 67
    0x1800080c195a07400070111810440031042140c032000108003405036507241c0c2042e81c2d03203a80e0700c021144804022940c055101041c20b01c0a580a5100d07011501000e00e0842d442e40601d207405404d9800400003110f00341d00360300038041041030140503a400f505500005508004550300c41e1102003410806000c1406000204a418000c442c03451803852900000c0900c9000100c4442d44000c101500710100719008020074030008403049c00c0c41f401205c0085c2c2d185030500055807101420ba550304400d0403001c2d0360b1002c99040d240b0f03203142080008102a280012185019200070400c600d211101144c41d69480880c80101c0c0e07040401e40b0a8469640f400da0300503075403050b07440003a100d0b05590701d40c50b12001c500b550916850a0011103441544020b95014100c4140c03a84d6030b0340d50300a0025400304036491480c817511076000e4110b5200e40500100c0320500d40e039001080c0b1425006005071303400c100000803c4144032041000e502201301041c4038040c4c0320314242a264071240c0c81c0c000d0100e0003000810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 322121196 1250 322119946 322119953
    0x10093f0f050f030403021c0306060e04110d0c17090102090619090807170f06010e130303090c0f05120609031c0e0d020a1b060c0809190b04050a0905090304030f 70
    0x3035850720880b0001d41079481c201400c001c1d50390f81c011000800000b0712910040c041d14030074050b00c1c04036142e40c0c9501082d102084104006050354403a4108450824052840840313141d002e800b00040d000d40700c0f021040c8844540c1c8014680041042c14203070b004001550076038072200304880b00c8d10f0700d1301844c07422200d400fa421102d4075507540c00004184141007000c211807174141c0c8100f414030f4641c002c440c4403000c095080343e01c0d40000d02c54442d0039100140022080801c41241e0384e24280300303240004003001d141d0340d001d042e4560768114944181000c18240550b0600d00030529500c01d5540091101e0f00c1c012442550b1303880752141030051105100105c46502c600e9801c040d031003070006015030b00b6001c0c0310300009540701180c500c250303280d12001080c0d072000d5055095541c180d03a0307955941c240c800320b9a1038654040e0310101c1807a0f00911b6034003007080d103100031403521000361018603040c80c1c0c0c0314580307000c10000b1000c94200528031840c280500c0780c480c100000702c1d41180d034401c41d072035510b840506 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 322122302 1106 322121196 322121207
    0xd1101020d181a0d0f021b0313030201031a030703150506010908060402010302070809030a11010807090b04050904060b090f0105100918050910093f0f 66
    0xc814420070f10300d00b4440900401c0407050600d806407070440b00c401c55110101914900e603000c60500b407454036080d412a040e20000d4029070924a240c9a40d50107522240700007414503a40f0440d0b0303111750391141c00d041180385004064400190362400c00001e1025241c1040611514080006080f903001d098458240d8041a00800007a502e0768019402035114400558200e00180300300c40865404015002007a881440301070741d20200d4100160940201421078800d00a20400a01c0841440c10a5401301c59080b152030506880e54142507005000c0000b209401107244000c111031403035a0206075041310303c1901c280b10482c4152000f2039041d00503006031030110b000f240c0c4414016006400030f6401508000583e94454403811a4000303c40500804681031031313401410b251503148444504100c0c8862408090401980c0c0100e0098107211802c18030078007690300007c0708254402d0303 = true := by decide +kernel

theorem cover : BRFrame.Cov 321942446 322122302 := by
  have h0 := BRFrame.cov_init 321942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 321942446 ≤ n) (h2 : n < 322122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
