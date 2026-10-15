-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4678
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:23:18.190513+00:00
-- url     : https://prove2.me/submissions/ab56f9e4-9e88-448f-8d27-9260c5c79ba6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 841187050 ≤ n < 841366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 841188300 1250 841187050 841187063
    0x91505090c0705030d050105150a09140d050327100c02190b0a0f021504110409030302040b040803190305010515070c0506030406091b061d0301020c0d0f03110313 71
    0x3a001e51000e80860b00300641c00000d50761307a001425980002414280521801490b401a92000e103800a1f800c840c0e240100e0344070008118074012000418419800080350080c4d80344000318000ba6042000c1d015051484802a54023204c080085088003400109203101d402c2d60300416190035048905104101c3d0184c6500c841403c55414419802001d54824480e441001034803000310b5031b000000042c0404035500350b850f54000b5003c0fa80c2d2a01040d640035007080c01003840040c81e860142e00112400d40700c2d080250820f80c1c2c80e42600101d070841d44c441d040380e03000003034406030305580c040c3c6000307691003e0b0600704001d5040c03502007080ca10450070140c90240f4002529403d1102500700c030001044014082c2c1d0b6645850326015025295600d812142034840d030801d05082c00101c08840203440701e0b5524900780d00d2404500c400020b010700c02c3c076601075500b04a03102040b24280b0501e0382848072603c4844080d601028000c04a8000b0404541d0041d0180244103d400302880e100003040c0d041070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 841189550 1250 841188300 841188319
    0x108160311070503072004021806030a061502100e153909040c080105010503190b0a03030f0f0201060312050a050d150512010e060f07050d110301050901091505 70
    0x103141c1081c41807100c041d096100200d0f051003049845011009140041d510b2103412241d8501840107034011034501d46a40481c0618802150402e40e015507401186804003140890b500d0980c06e00c0369001040100c0140c0100c02001c0340d8901502842e4081d03a4610020030002a40d20480c2d200e144025158110319100081070b10b0005200365072074002e102e0516051070410b0090010817015034003c0700014003a6040070380c501540ea0040c0030141c1202c1d4180c64051456481400c0c01d6030906151031500701440c0d0312003c2070341a84442e032010028511985139003295640d007002c0a4802010708050004582c14204140005a0b0943d030000c0c2a40e164242103845044641c1c05407000c0c0958007214488a28120100140b000031f055414215442524144101b41500145030301b690907510010142d41c0c401d001240c50104a008150b40c030609501d03200d420300e8060411a0f0594920b00c0501c202410301000500161a0100b03680d0b0051039001010452200100d034204913820081c1701d070b5841505140d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 841190800 1250 841189550 841189571
    0x220b0402012003030a05010f06030e0d14040308070503030414120d15121101080901021303300804031b0b37060819051504060b040911030c01081603 65
    0x11400ba0480201c0d000551380c507413410500703ca0081100b486180505003014000050b8640a032156034078031286134002d03140e056000b8400703468403516521075503814070741000000041454100540292881200078550360b04107401c080d45040c0e8481d000c0403490700416015443c0c0c0d03c0c024202c0e031817a07840b1032001c101000340088460301078007294400d80e45401c40b12000307400c00c400ca0032140c9120304240c86044c15070b124030310303a1404c0303006210007200c020000040610200c0d09211289062012a5080301601e41d08070004610415801c90010b0100c0c11410030f00003007541003030003c00000c0d0300c1c210510100c20182c90712205040082c1c49860081c1c58001d81e8508a4481e005804920211189030b1200e00800401d8400802c002d20410041e40113207148a01e011a003803422901940d00b0200a01d9040c42c5410744098034200a04101c2e401a0b481d03118101030344440c0140e40d1841e001c0c421625450351840e051506013a10602c485040280d1042046400c4220f007200340e1081569240000f400001b2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 841192050 1250 841190800 841190837
    0x4090b0a0905011413020310060c08040504020a180614070f020d05060c0a02011d150a060504050c03040203100e030a11120f0301080712030203071101180b03220b040201 74
    0x340d41104260905290000c00c1ea09601c600c81d16141c03805680090f00400403254010807030101740d0b40c142c245014000200442c2d441000d00300000c030b00a556603468190f03a0400101240c2c09001400045030f20b0264842d601c1002d50341c000e000b0055810f03c0f8030b12101c2d1401c1e6502603ca8000010042410f07072500c0015034403610302c480c141d181d0040443c0c11600307044003602d10603000341c443d941c0190708111950115000c804600102003100b00018145000c00301d20b000710801d001044c801c01182d84110008090340c40d80a90b03401540440b40071907885c01e086c01031500b48440d4081000350395040031070480385a00c2c00012140c50340382d14604031002c200c02c1c14045007410310307c80b180a800b070008030b507850303940d03900400441c12143d00c10304031600c0b00d6848120a600c456500c002030003507002070003d030021038140380d0b810000010524113140101200341900d450580190428400c03a90702004201942d423010172041c502c60001c0d00d60300c8051075941d46105034a0340051009040203a103240c18080c4009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 841193300 1250 841192050 841192069
    0x90503090904080c0604110415080706200102070f0b0a0213180207051203010e071806050a111b030d0e0d020625030806010206060d1a06060c0d05091f0504090b 70
    0x1400143c1705182001c1c02d180c03070b128040d11201841203245c0680301100c059404c0b0400d0842c0c0030100901140c0b440c080c0150f8104038054407103a0483d0b8041e2081d45040300070310040945a1103200400c0c1801840d043c1543d503110000d11100300c40b44104407622130480c215001d0070480b0f080c64403184c03048085083e03c0c006030280b400000c0040c822000d00d40d440c0340e00e04000d10f0607500b40c03030402c86266075081c40807503100050080d036054040407508184140707032061000b00071800c0241801804602e03444126850507000f074004e0000541101d09000c000e14007070040d0b0440709214a40000e94800c4040000d1a000a03810002c1c0326940004041c101d059004101180d40c80c20f020189003030045070300f00500030000484800d4014001c40b80041e0b05480c25a0007140030541225050640c9030360a00c41400349840a130010754444024490320152030402c20080c036595400d42d840c1503c50140307100f84010415000101000071510602d08000141e00c8404d8404a030740c10700b40403403000c0704500812110030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 841194550 1250 841193300 841193317
    0xf2107060906090e09030d0e100f3207050c1c0807020c0f01210902040e0d030608012703091a04050a0512191e06141f140103140a050402030f0109050309090408 70
    0x2810400c060004585582c0020090048059000c00480303465501c0404bc9000300b2006180340d411001007900b40d44240040e024005000044501c2c5203000c41c0d1642c150140f14408c080060031220400403080e0303040c0030b03080f007222080d102c000c0341070750340c00010780346402460307002544960b100c009820824070b40d08440c0310150054400c000003500700400d00d4441c1406800c00010900b001d000054800f0305104138844110200c854144c3c44400109040c00c555140c9130640401c200e046022031607803280310416584488103803549907194a040140691002981e01c194450f4250445540c000754002c501c03e041e02e688070b010014030000f07614103001580300390205141c9513000813501d102009035a52080001810b0344011196130350b5003420704024044d200b412a90000f0702a5410003010005200301d0366152014100824002c0250507600d500308812150f20041e99111000c2c4000e50500348000150300400d10028000112252101c0da5a80300d49828507004840310400901030085410945c0c480d072 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 841195800 1250 841194550 841194583
    0xd0c0f09060207061206120615061805040506040b04050f010f0e010b0703081812030615180108060102011d0d0e01090e06090c041d010906140f2107060906090e09030d0e 74
    0x41641052001072003182025a00d14100e09000701d441401004402e42d01d0b540d2f04140d001203401c140a1002400018015640154640d02c003103905680d180503640c402d03440c510001300d1030340c540710140d510150303240d0000800c1305412006200e40801e44d42202c40160701410305000b151644215141d001d880d600e0114038600911120311171840c0080d00840c00394008603100007255820243d50b400d144030b60300c806d04d2001c10700c0c01024480e500500300142e210304140000900c1d20b1107007100d0310034a00d14030001240d580298000a0341d0a40002ca1007148260a00c2d108008070308141680c9045807010f4001c51007100302e2030014a0440089007186d002e02140c10080201446000c8008605d02003809000c0c0001c2c1401c40109902101d0031090b10031903002080c8600e0003401000344001c0008004814281c030482d60310030198444100140b00003015155940a001881d14174003c00015168000b410416400c00900400c03400c000291410001030010000303040e0002c8a604d841c1100814040381e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 841197050 1250 841195800 841195829
    0x1017100603051021031404170f03120117240708160e01051c1104080f0303011406090307170c03010b1002150901110d0c0f09060207061206 61
    0x4501016004208660094030240314503154034100c0428406140180c40100c0341680e4400300b0300c030f150350000c0307000da020381070003413440c03c61000d000da0326800b981241c0e409645490012a0004081110303080145201018600341960718034808040c00062280030664681c10500840c110401c2c001000c4692040100000d0f05286403c050429034007146c412000c2102078001030300e05040386c031400c20000500d0340e410420000c580010b60780b80c0c0211006080881c0c0500e01c11102d1641c0748900c540b100d500e894000d450b00e02d0290b01510305088505094020703041480104600c544104010413010411540180c070349000344046072524100341c1c8142c016804420f14286011804100d55003240805d038024411228240103021034003130109211001a0b000d82c40706c20b84a420450056000310511001203800e80500720b03501d100d50006000c03480d1455903070418103103203070b00074584004444c1d90341070601d803a92922030065103035400c0340307d0700060200800610001b2202640900050110600003821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 841198300 1250 841197050 841197061
    0x60301120c12110909060708070302160203030d06032003120f0c010f0e0f030c0303060f010c0515060108012403020d02041a070323030118110304062007030503061017 73
    0x1810f401d0003a50500503882c0402003207000001003400c510a80c82510f40600980b100e0030100c0003507104200104024100c0b03030080c00140c1d410f00080030600c0e400703200031420381c1c21402c2040d0b280c98100302c40340d8034900350510148035450204a401c0244140c0b20199100c20f400c400400d03503803142d0700b82c0c0d01d00d0f03500e4980e04007200b100751752000300821500c000b00c5102d0745c500000540d4078407440c83d01c640d407980240001640703440d019011102000c010725050000008a0303942a1a001402c04420044205081049104d50b84100282e0040004100c0c1c5140502d0b003e40d528140d5044032590010141c000a0404d500c030040d030120b40c000c0c04610700e01c081c100c0da82030ba902a240c00004c0e08034000380000a4030090f4400c40701c00c2000d000782d41010750b840d41e40f130001182400c05802c2234450240340c9a1080800340c82031040510300ca24011100414940602405114807803000300e1140c0c10310000303200030b81c04654450b017640e500103c240d455034072114401c242a90404d10410140d074031511510100f10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 841199550 1250 841198300 841198313
    0x30607020d050d111c0e0f100e0a0f12021b060d09022b050105070f022806020a0e1302040609030206180616051005010b2205060c01090507090b060301120c12 69
    0x3910403005c01803c0082e1810500129143c041ea414038a6040c0d0040451206244456004c1d0740b00c50440411502c0b242c04561714019510041c4806540030000d0440d4584450b8061003109014402188800030071107000c0005071030350003544188441183e450b41d0541c00c545444031752084138020048100c4920340620a001c100c013840c440102c0c5c0075400c18002ca5a81809141c501c0101415900603161021424560707007070b0344401ca0100d01c0d10506411048d0301084c21031000745900c2d00141c4d100301c08080a401400200f4410981225140e44100010401e00d81d01882040582e0781c11203e0301d40e03a041d08a4207034000d4880c1140c003540305000080c1031204030300c1000e84107405407160b42684e28441d15042c0031000c4441c01d00c20444000b2081043c80300605800c2d00250074030020351b0710100c0040c0c0700c0d03011507295040700180942e142c2d5240042024410200880e00c018641c021040c0405c58080300071810502041c8505480160410400b80030048005003480c060040b8103a0280003140c1d80c104007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 841200800 1250 841199550 841199587
    0xf150804080d0b032e051003031101020708310303120903022109150a0807050c030c0a0506060a1e030206090d080a0309020f03030c0606120a170705010b030607020d050d11 75
    0x2000c02050482d00044115070a01615100e1000d10030941111f6141d038409694441d020210320f140f07958200035820001e25848050648062694406161300c1e52a8125130029600035880c0d209281c00328404000007688030820051001d801d0ba40451070381c44501e802e914040d5160030385602d0301c14804d411850b462246025144010084481036031560314103040c0da4240c4140f1054400003820240095480340c0250001d00d03d0415044c2200c2c6049a0702e050300d41021071600c02103449400603400d00c06540f914071555005040196480920702d8481910a56049601e00c0003e00401010480c40352607514600000700c481d0300088503642d10398407580018002c00000d1001c0f48943c550010f40750745400c002040e601c500b48480700030030181d00ca1174200010604010201e540520940c81101c0000c0c814450f03a038034131095402c0107500c9550600d030103401d44a1789000e40c0e01942c00f120400c00c8890703002400c008406c942c1e090180d80c44541c003079003030080c22030521103501401d00046c4010499890782c041d0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 841202050 1250 841200800 841200853
    0x50d050c0a06140327030304050f0f03090f102a06060f1203030f0f18050f060408030f0c1e1201090218130e010c090f150804080d0b03 59
    0x203041d07210751201000e032000580601440e036400e0051000a010101c001182c0e80c400145428180402520444141c516131003120b0460382c50b000480307030000d4010100401034028210901460900000c5008500102850a186885a0b8800c1c4003040f5840c000c0c2c070312243c41003003000c2113204882121410702090041c6030089420500e080d00c0001c0b541c04292030003081e120403c3d8400c41d0b071000b54034104c02400c80009030100b410f030740d0326251401082030722076180c040c00d10320a000740d07008050a08a060091000f9484aa42c00c40e10030080054182d0303048030b0b401403000120803e6130702c2c0d05a0b80b0302d49001d0500c0d076024400b030036035803240702a040344058a003001c5030a40c180d030240e0b00c6503200b1040c1d0280c05a410740d64110840c05480f245005405074401121500002600e0720620711a41e003582d4000d00f0110224600741d800740080c0d45e030400d000000d805007216804188607683c1700100b54030070090024203002408241c0d0500d202c1140c21001c02074000030111011031500d00c0d8640400c5030030002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 841203300 1250 841202050 841202059
    0x112803050d08040c050622121511120903040909030503190b0a050409031403130c060c0b070c030e0d050304060215060a03242901020115140109050d050c 67
    0x103414074214495844180729561040114140d00d01e014180041c5411480095034400900c80c011580403070703180e08002c0101041034284c4484900390400344101c0d039030a0800143c03135051007105140510050101e50701401d00d00110340782650f4a0310f00c40d080d8059600200080743c00c0585040516070700c1005035001d96900000c0725036450f5481d81c40030443d4098856150072030303060841003006282542c00b0400041c040c0c1800004650501e41955082e4011a002500340f9040707501c800c203000904c05108050581410b00c0403a841d0350ba192172001300d00082144042046000320413081500c10001032509200203040c0c58408500c1d0b14096840350803a006a030300500c141110900042070f02088039009420180c0b203084a1405d54440a01c1508164040d902d0111210410f0864007414462030701c082519802031326000c0803c51501210a007a0780209046a041c4280b484c02280c011224004459480c0c04111616811200580b8000410f03400305034005464101c1c0c0042c8040843c40280b640c1c41103d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 841204550 1250 841203300 841203313
    0x106020d0e0f09040b091501260f0303061c120c02030118020f040e010204050d12021212060d02040b0d050601031b180f11180411041211280305 63
    0x1401c2c03000d4041c010764000c1e4040d9105001c00e001c15650344c101ca0308002c80c102541ea91210041c880c2c42d21311020b1b4802c132a0038882241c1900001ca914420030000d80a1401801e002152145a00d03980c0c00040c000f14801c1282c0c0107645102216004e004440540c8008425040b49240701c01400c03440071480164065400c10203240824840411000ca820760700800c010842d507400000d210080c088602007915942d8204404109907840c41400d42001e40b00d0b09800360b4000355002c00905000741486292403001d0180000d807000b51a0070f41c4a6440481540c82c00743d086014000034000c0c0400821a6030440384d608158020301ca00861140d0589008082010003025407040310850070f0003034415400f8010000c038001011501030b070803552000030b44060208004801400e0460716078001c0d9400399122030443da45120b5401c0502038110451041c4403110b041c2884c2c4605601c4560b0b000c80010800d2001d9501d0218990381c1e07641503c1c80040c08c01c180b80d0103080c400000007005085002c180c51074850310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 841205800 1250 841204550 841204577
    0x210050f0f010503030a02071202040e01090506100803040609060309060b1c05060906070c140a02090c12060907050d09171306082d130212030301090c020703080403030c02180106020d 80
    0x5c101c92446000f54000d04c595464000c00152003541020101e074802c0d01e5a4140070665424000c8c10070f5980100040e042d80d060079050a1415216170380210610380050008020050b00716a56004031509400c02049420b601c0c5001c0005000b8200510352080c1111080c5a00443c0d200030410f0300703071141003112100e1710b44030340b03171941e50500729515000107815408030400200d0300c84c96052031110078011902c2c80b03030441e800610107200480b648201c156006c940c0b498290701c401c4181e034110380b0079925803681c0e0a054000910314421901109803e54564100c1c0f400c1101d10003503201e907200c50500142d1103105154445500b0b1015105c2c1c00002954480810a8480b901e03c0c0c0151521602800c01c0400d000c2c100b18101103c0c00030400403040e0840c04062015841d100c03008044502400c02440d900c0d81440e541004131072016103103000f1036002a40c00c0c030004500c2d104030f40c20740303826003020b01d508003030380c40000e246045540b01864440801000042d0f5140c00040b20040c680003502c0300c25054a41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 841207050 1250 841205800 841205803
    0x90e0102030f0a0929150f03060c030c09150a09050109061d0621371a030f0105161403150402220e0f0408190210050f0f010503 56
    0x50702c280c0d094a280c10040f4003015a640e2100980c2c600c240158406200d034080384580301c0601c0001c12405071510420003010722508400d003a18900308440c0340c00f80700c030f414000c20b42d286c400a00c0200d01d0440040818200d1b40c0404c1500d04c007400042c600b84000d000c01940c00090781000c0140c40118040210121b540e40c040c6101c00141c40c1c0d01da42c2c0c04500d001d95405090110302201c900d40e080001042805600c6209503040e2504903256411003481d07003403081a050185c0040111050f0032200e405912200c200c54800010a0954402d0702044602c08d801c0d01603d2030803c07a00340d580c135100301828200d4050040d04554031500b465010076448240c031020a0b9001064040700356070f844800c20000d01146203d000000d25000d02800050a120110100724445089244403407400c0e500900100710440f01607900c0340d48150101d07036201d0a41481d81c2e0380c3d0014040d541e0b00c1f81c500e241c03040d038081d80c4a10800030318006445040c4184810708180d154081c81c82d8003a68086500d05a1000105d25402c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 841208300 1250 841207050 841207057
    0x203040911070b0c0408031e0f0d02090306090606060a03150807080601030b070203071a040c0b0313110312040509070203192c030c04090224041d06090c07020d051501090e0102 77
    0x2601d03c0039600d442ca5074a1410011064023034260350910301401000070144003140a06096a2086001a901c2d86000f08051602d0801080a4119481a8104842ca1320b07800e094030245e0b09d00c0d043c04503031030301114605109007040c0c0e08003e20780d101e00c0740b0024540c840003404904881c0038011000294560000481c0c591041710340c06040c601803040038018824070742c511a54003d014014113040315480da044440d030b039031090700c90642e40b41c41850b40a0034441494001c041c1008100c4c01401c001c01c0e0b100d00782c1e032180614400c4c503100c2d0b5800c0000815650007030088480c1c040072201c0400303a000c11460041c0c08189a4000c00100100308119080032607a5080c50b10b00000c00140109200038200c0100b10140007117010803a042100b41610108503501d1a900d0000d0745110f40030395803100d050519410400402c071080c110315241e420b0902a040c0c80d080342a41d046107400800e103507144030301d001041c0d000808507402020742c45000907500c41401d007803909a0680d64108001e21074162181066424ad00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 841209550 1250 841208300 841208309
    0x60f1b0901051b0a08190302030f0103170c0610140609131a0612062706090a0e0f06060a0503010204031106070314040806040c12030f0f0203040911070b0c04 69
    0x2001004504160341c09503010741014204540c41c0c40c00d1140e950103050400b00100e40440d082040070800d510030081122205000c5155881d08500b11b2400180354902524103120181c121055001c100c0401ca080d030b01110f820110103011248182005403100810000500c942040011500d074a50a41d203030007800c4807000c11009100c0c3c0305a015500c203d030010801010051850140008003107034039101c840252451542c0d00c94400600d00d0920103004003034072060b10758107083d494088602c040c140c81c103070519008542540c50b50f180d541e40c00345500080a120351507580f070f0302c1107000e45210200006401403044000303985d68180107550b8024113090303000d5400020300b1451310695031200d900b411005424914003c0c40c00c040c040a0b00c00c0e1041469002d9000b9101c03d17006402007006204445009074010032085030449101c900e00d880003014a50403040302010880713503400d81143d0714402c100340c4024020754501006124050040c07a00c85a002c10411540c0d80980030001c0e00380e038552420b54003101e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 841210800 1250 841209550 841209601
    0x1513030308241018050d03030504050c0a061d0d021f14190e150705030316140d0b01090315020901082a07080c3a140f0904090302060f 59
    0x8140280c0555004410803200d43c031541300c820002420350b0300c4205e040d5207035001e601d0000349400c1030300340303141000a48080b49006440682080090661250f042600d00c4022910324801c0c004000014950401e0034030080d50100d05205041c1a5550214000001040756107038070100111541fa420264010f4030000001c2c0b0780400c1041450a0140d89207086500005000c0958028003504000d010381040d04190b03016400401000310500610719586a078036024107003164a080d10040c02c1040d4411403510441c1d45803110426040d903405011000c01959000da10000c80d00030119984001750060200c031800100940c001c10001c94410051502c001205510f00f4841e83c0340b120407211076440860122000d44041000007080142480442074100d0044205001d48000c4d40c1c081ba511644041d081850040d8200c01c240455040b04d980700214580c80d445c140c0780d503041e0260310300c14010f21040070b4101d410118282c04055000c142280304010092400c40d082c2c0345c0c0c2860a010154080d00300b40b80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 841212050 1250 841210800 841210819
    0xf1d06040b060d0c030207021e01110c060403060c0509030708010c03150509040b07110a0c150f08010e1324050f010815180d02060403020723151303030824 68
    0x460303e150841e511030000c60501600c2c200f280e078081032a2019600f06403881d401290090400341d0390040010f07401e03160381c40c01040c80100071000240e0511407440300400540d40c401c00a0b1006010700e06444050000800341d0304616a11118140a44000701c2603a0009241440f42c051b10450a5060000da8001a00d03000349076403542d544011210000d00309205100c9000020a0b800104101c0e0521151044010441d292f10740300030749070b080c0c035189002410f1100c003c0c0701500b0f0340c2d400b4207a24112066810311a040344c8800000d501d500207103a00207002001c07281c00110000480c14200460360500c0c0e0380400c41aa00c0304082e0101080a010700095500805045c80b0084604c910341500820000c0007500051540345505140200140303002016800440410080c160140701d40b03001462015000a041da814640c90600300c0b0b040540f542c0b04030961140c5540b040e4185003503e265920045084909030740300e08010380900300c100d4041c05c00000422001c06142115000070b401d914000e000d442c003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 841213300 1250 841212050 841212067
    0x601030c0c11030106030f0c061407020915010e060703080f0907030206160303020405061b0f010b0f060f040b0c0a12031422020a090c0e09010821040f1d06040b06 71
    0x20081e002d040041da042d03484d40301c0070011566a41034226601d00c01c200041a246c5000c2e8068020080e44a010200943c14484100561203407074885501210000108440000280040c0e51702410346501a40040b00403480c54100354200c600d045c05601d0081d17403800d40e95170f03010000e40d072041caa02009401072010311000003031055402c0703143c0341d981c424100941407a460b040070070382c2900305407030640701070520148482c040300742805101011301c0b242c2c001344548019040401e1004c0c8800d81d646024802c00940514040b45403000d40c1c000c3d205400407141c0c2c51a41e40074165603401220303c10744a040080342300005913030003845200c001c020241002e07801075803116108001c0007184956601140c0e040c000000043c0e96140030710b40035001c0f4030300c00034210b0540b8400404840110304440c2c0140f0109005020942d00010f0880901380c07096080d280440301d00103081d07000e008a5000c4035018610300d03404a02401a5001c241005007071040724801942d0340c9041200781c4550107103040d0040c108111086 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 841214550 1250 841213300 841213313
    0x10030203010510260c10030209040f05040b010506090f10090e070507050d0507020f0d151109030309060304151a0907021606260a0e0601050108040b06061803030d0e060601030c0c 78
    0xc0756181d402e800c1e180c000f008900425003006180b502c01b40002d600041141e19032415114065600301c40c400e0401c0b180c41c03e541c51940081060103040c2c400c0c200400c0030746042e6501030341c005d280d08000d0522420001a0315000e0207010b441e005940000b031142d00051401c911810688544c9074109006211400f2211001c0e14603910100d0144d81045038948019619114502e1038100188544001e50310345184220b8076040380c40035a0640c18030042000b0f030020a41d40042640e0030f5207400c84d48945c1da600c03146042c002680541091844d00ca0a12840044075201008040e1065200340d07110191507941100c03c0b0786170030402003582d4060342c00040c2446220f1050040e101c001e81415400e10149100983c00c0c3d0710070b0000c0b60b20301200c1d1744070050400c110f04148441801408282440030311400d065880b03040c00c00c00141440e004900c0426240c2e41c00e80301c00d4403840c402c80c000d4280d0f5a182d0000a0b0f0a028007212050030003988900070220701c055200744540122507405076503008504000d42d9444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 841215800 1250 841214550 841214609
    0x90b060703020705012f1b0609090a0b01030e0a030519092d091505030d051204030302030a02070c0320151606240806091f02030703110310030203010510 67
    0x139860200442001c1e488001c07103060541501d80301b401000b8079103245803400000003001c1e000c1c500841d0b06014410b025281c801400d50407681101c0c02181003510080128010000350314150f00d1841110750302800d16070008014414000f5106e00c58a0301c5040a0703095507011254071600c1d007160420000381c984105e400e143c5840004020348003903807003a654451340342522200b5480c44004580088104540d1800b0072000c1803c1c0d0303260a081c2d040562745015005540401080035042c150000005031554485c0c0d0304441499612143c20880301e0303160b00380964000701d2400d4a0520144082e404800d92a183d2500b8044013898605640780900d072070070320001c21101c00310450b000354407000d04021906e1600d50100c0000042c040021240b031420310f9035441d0038800380c044812600600750b10511100d203800940026442c11102603603a88550100b11b008000c0d058402c4412400441404a03c24000401000301c80c001c074000e11007a1113540000912684906c606c400340001e41c20f449038243c6c1c010054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 841217050 1250 841215800 841215827
    0xc040b13050402040b0406081b040501030804150309020306010603022a06130302070812090a06210b0f090a05091e0607110a1407090609091731090b06070302070501 72
    0x300c5da5a1784c079400b040548449402070f41c6c254203c032030680100840d946045001c500d0845090001e9451520f40c40540e1049004440740760b4030000e1401d07240c50090b00007140c1103501808540d61503958000046c000d4200759507520034813542107c5016906941c83c92103108280c902c1c060045034480c103c8544e8201180300044095005040000601520078006100a4110000c20320342c1c0314015403c10003425001d4000806200d12007002102d005059600e0744039144440800003064545d0741b001518540020030026804600d43d0104114240b158001c10300403944041250031401298421042c034020001d0380d100320794000d078001000b061145da5503c3c078100c405010f642e000050342d1181d1036854a41521003409a1000300204141c0b07070341d40719403801408140f0301084410216a1003207004610f030755602c2c44001c0041240040b40b410b8000903501c41a400851600603651400503460903882e600ca03402199140c000380200c50308145007120441035141e07020740301c1c0320b041c0001901c1c3d80340a500c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 841218300 1250 841217050 841217059
    0x20102120924040614030f04030f030f0f0b011206050607080f040f090506010e12060601030507050d1802030c0102010513080c0a0f1a1f030611190f020c040b13050402 73
    0x101820702002035250b4031031854480c045640d101d081c01030180c5452601c0c2e00e20100c40e1400c004000b1824500f0720001e40166140c80c2580c070001000314120050b24140c1c1c1850b42140c80c01d00c411480d000a5400403170204020303210b040d2a101c055071030f0012207602e8031405400283c10001a00018901402041c004048150003802c094075444120945555904034070f4507595114140900c0d503801c4081081250b81c00c48007009606420085c0c581caa64024040c50706142d100c034045038802c0d00031010b589079224038143c2080f040c10700c0d0110000d440800e0405074001e0090a481c80380c10351040c010380d4890200603250340a0b40020303a0f10501d00d5031010200124a0003805007400000e11001c1b50407000780d000f180c089503100d0380d50349840501c0002902e201200c0700c10310501c00d0f0f04017800000400b202d0b00300d42e00260b524004200503409110b104040c400e41d81103a201703000400d03088034500d800c0818580c00c43d09401030100502c07049a02104c115540021050001c91000c80c0d44d40060fa400b610241 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 841219550 1250 841218300 841218319
    0x20906070602040308040303110102250f1218090627090503030f040b090c130209010207050d080a0915021b03250501030b09041505070512010e100b070201021209 71
    0x84907041280c1090f0022110100001800c106155011034181e414843c10301c021441e0541700800802c1400e404000c006001c40d40e01942c17028800380d100203610031504180b00d00c1c0303030030313000400108485034130b9400c007504081e8003c0110f0703410001e2181c1016a08a0700640881c1d45090301e01000080020742101c200d01d80f500401c40000f9002e1002e580a50035070ba907000343c80d0500e031401e840c0c0c41d4401000342c5050313072210340c071110a035807044524100c0e03507061440180c0d00c42011004030f0500500d030b042560031401084502d001c001c44640240070480b21952401c080c2c44d214201c0da4041c001221960300103900c40c540c00c5082d090618060008800700400315406080280083c0d180c1d82da096107480b880128140e0b0070051035816000d0341d83e1a880466030070089252581d50415110f0102c0c1040c0c01203682d800c005a032150240048940100318002d00003c0c0d90b03525070f41d02c1800d12045607803052524045100050604c00c0105071800d09505070047c00c0074002e1806620001d070003101c000c40d480351005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 841220800 1250 841219550 841219553
    0x11e1a1c0510020403141f0b03010b03060108060402040c0c052a100906030f090f15090203030304050c040b010c150f0605040212041b0e0f0702010212070804050606030f0c0402090607 80
    0x3080802e04444141c1c00150b115031950070085d0502c110b03d8040301c80364010b4103441880880000c0c0111a400e608240080c3e40b880c0030000c21b0041002c0000941c00d0303c598000450a0500010171500c12032080b10240310280c0840011650502b0000380188254440c1c40d100715044415461162009004220307031740c004000c680082c0308010505025408600300e4482404001ea0500616410308040302c81840200c500e90340301a0108000d07100540f4151000c092941d0441841e006051991f03001021a900c9081c18240035441da01440c2e641d510907031408a022500b17500070b108030500b00fa000480c90b84100845540400a400340003000f1140950360003000c1041c2c0e50300e00c042c0c0030180c51b02c0300350b10142c501072a00e41c032044031928075200d04c0e80ca0850100b000c04c030b6914100381d2101c440c0443c400a52502541640603004214103a000c060341d07030081044c4661302c0740310184107601510880d556512250285030310740c20600324504071600204075014150816400400d81008040c10252403c10035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 841222050 1250 841220800 841220803
    0x316061b0c0e06010f030203220204020c060c03150109030b0c091912061103310611030f0609190902031606020f0d020d08010501120212010602011e1a1c05 68
    0x40790008002c4003000c00034003c0c0c5580c00302e9003c00305511410210f00e181020a101e405050030f00e0217011410403c4154503045442e2a0155200ca6123060b04450032030421030320130441c6420807510300007c8030714880e8643d01e6620440301c000c1185d4010307015050544406a00a041c2c1e400000d005401c602846040d01da10421044102d00503c50358032540c45020461901c1c0c026a4015800010480000d00c18480801c800b600d594120541b03104074441c805014680312405585e16102c003070001481c107910503c28140c403030011846405055813408260740d0391410402e10314010388407540300160310005041440da003030380004500c0d400181110b00e03a0541c0307031556484031032580100300185c02403145045a04403c0044940f826981c1c000b4262520b03a84c00c009180a005208660410041c10000c01c20b010b401d074112000d4908000c000071040d03171a0300000e8060130324210350050156021008a401383c40c40e10130f4020b00c42412134002a140902c4d01003256550300700d1014009483ea9000c00d4000480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 841223300 1250 841222050 841222073
    0x120513050d0e010216080606041509050c0417030a0c150e120a02010501050d0f0b250c1b0b16080f04030c0509010b030f0a0e25030c050316061b 63
    0x262030382d03500a000c2c04500020b050004181900e030408424820522600348041030740b0b139102c0425a00001e040c1c0003240707115070381341c1680e009400440ca80402e02002c051004014001e030f408803012020b405ca02c2c00c40c169030301d01c90041410001a04003100c4030005502c040221034041d080e00700424503180f1201c00f00d007800c0c0c40092030b10b010f01000520340207294081c0a03050041004441c101110b07441341d21002c41140c00b030717000140442d010f100040d0502e031071318002d0041c01204902404800703441007400b511107110f1031001d44900b90502d00e82520b0040c5102020203560b54200c01e00d040520082050b401000e0b200341c200c1c0c0b002414466100c20b0048440644010350280c0c2441100514100038809000810380069501e81e03030801c02c10101040e5402140e4000f90601310000701c0300c003205112400c15585040c1d110b0203100f000e01c2c0e03445d4903541d0380d4400180c80c01800d80440f815034482c200f60fa00c034041406c0c03180022000e54100080d034069500b9210340c1c100b904403d00c45403160f507a100f9007085c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 841224550 1250 841223300 841223323
    0x4060f0603150501020d05030426040e04031701122004020c03180d21020a05060126011506050d11040303050324010212281e03050712051305 62
    0x7035a4101c040208030700c1c000042e005000a001419030340c06991002005840000c0000c2c0c45150380501508a8000e202c40d2141e01d9001d54143c581c40300d444081d62118044141c4040e4005a00c0103180740e10002c10114550494214401030031103480380760750348651188035100200c1844070b0b90101c0142c03521b40b80000e04a01080700003860fa00e1740002046490b20903400d11950185404483c00301c00640c0d1008030040d0f0b54007100b1400380400c0900030803494403d0380744006140c0e000d001c0c000980c0a22144016003a180d0f20509104012001c1c1c80e038500326a400c42080911113411841001058000e030010311072015642400704000c04003511043c00c075401a4821000644000200080005c803040c2d01001c2041d24400811000003150000f95142c0c3c0a20100002440014443c09111000f20301203100000d0000381c0d145049a007840135180c401c0241514003080d00200b004000030388603110307480c844c90381500d03101803143c212803500c001003000801c00500409047d928502181c4100022707220207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 841225800 1250 841224550 841224557
    0xa5c091503060106170109020c0a0210030f0b03061e070908010c1d06031911090a090c020f030a4b110a030203070b091e0607140c03070f0204060f06 65
    0x1800042807518021050307101404111040000158480503d0300e007a044951050002d6181e607246400380c1d040c910b035400700a40c0080102a65000070342c1541100c100030106020402880e07a0000c18151074040851703c11710880b40026070040035419050100e0780100d9513103000d11403161101611070071542080907400102e440c2c07201221000103615500b00040406440c1d450030f6040c100341002a101210b0101c1c0e19a546400c1c026645100c1c09080d244030740001040701481c55522204040113000804040b001801000d4195000c03000010485149003929600c40300c0c0048220300380b0403094510010040340d240b00301c0b82c2406503103405003000722002c1070f207480a407950b01c81e40014200d20301c2091203c6d02500306440480119030040284d81000b50004180510b540c1c50401003400c101c90180b490381e45035000c2d6071100b030803500090391611424040c2c8460480d86800320080049000d40c12a45401d1f51003000302e400020f21084900301480d1020740082509178846940e40d060101c2a00b021000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 841227050 1250 841225800 841225831
    0x70219030b09061b040302010e040504080904090b190212070815130b040b0f060445050a0624030e0607050903151023030a5c09 56
    0x400100034004c041004101c0c45614061940e40040c00600f85540f14510490341c800c0010f0030300c50782004445040c08014410080b14543c1d00e045031f0703882404da8000405144814520703070410b126100321a4880101c00e03c0740e846a0b02d2132001c80b85c81034000c04909106160107418417864445060f0600c0500900ca00455107440c11403c6c4030803941c1301e50140b0b00c034400f901d6020005440784000c58061380d0341c111140b42d046d4804100c41c1c0a035175a4443e44440c40a6500c03c20080400805640301d41a008000900243e00c54503245000d443c01c0c0c1c000c2184d1402c0821180c0850000c0f148509521022400d010803201c0c0d80080150601d40102c030000701107180050458000d180520000100f600c00c7e11641409041002880c01380d42071074013840b400c0038209075181c0b01030a0320961286003884000c080320205c8200f4640360b664400c000e1014924852076600c08804614005800c440710080d00c00051450b0440c840196035054440354255245d29203403009460640b6074500480c82005071007180c102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 841228300 1250 841227050 841227061
    0xb0408030a0507020a120516170301050a060e030c0f01020a0f0c14010309120c021809010911120607051c0504120f0215060609011202310308070219030b0906 69
    0x41d10302c0201414215049840b00c0c030b0000d504884138404400c107900e0105e4907200554902080380542c4000035101c2c200f0301e080180560000801181030315029112054403942c4c81c041641c01d450941e141513410f0300b00c13898141c210705100d0802100c50905204440e003540e039946540c0100781111405603a00148200c050080d1a5180c15902550710f00b0710302000780c1c41d46a00c1e458400d03001c2d075255208020b50241c0450641d81c40020407400804000c941c14094105650203500a10060804440360942510038000a01c0c0c41090396400e1646040501807a684031401112903a0050a440d0202d24a400802554411070b114082c840c501c41e02e041e2a002c807600d1400b0b8003004080d44d001b000c6501122600c074a20a9044020342c00c80415545139450352014001071302c00301d10142c8482096840403038000c0400c00c0340004100d0b000b03181ca84029050310012800540d807030a0780000b4006440030882072005041c07404010069460031400740890031b407a5a207807901304c10182c4200300340340e020f2014000e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 841229550 1250 841228300 841228321
    0x60c0201050c0a09032603071722021306091508010f0b0a030b06011e0507061407020c01080a02070503030c070308010509040210080a0f2d0c1e0c0b040803 68
    0xa40104906070340c1410a00510001801130341076000c002c01904a2548910351a00905001d10703039401c0000c07401c0d40342d00d0300a000404602c81030310040307640c4000b42c011034404e940d1240074003080c10100c00b00b040c6a1106400340505070580c48032801842e035039000009520381043c400c81c0041c2d00300b003101c07401282ca415145829100807004800c0e00c80d18083c044150340e502d1106040469510000b204a0b40d80c6040050b9121a81c1191401000600a901c201400d0b484401415014800d40003044800c6040c1c40032042c450003241c040015a001100100440d8000d000140c0d1094110502519144c0380b03581c1d00b41180c01c151443c003a050801314070081056005244c0307901601d01a00e0011040c606500007501310600000f6080600500c1404508a659030b50860380703840382c10340c0c1c3c24028400f032040040700342018603001200300c001c4504010b480340014002c0e252850100d60341c0e44000c41aa050f05610003044030144000d00001208060001d0b01c660388641c8502e01170809907031039240080041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 841230800 1250 841229550 841229561
    0xa050903012301050907030209041a030f060c390717030306060703030207050f0a081b010b060306010e06070b0c030f0a0902091f0e090d02010b19090c0c020d060c0201 73
    0xb60001c6000756030050030402507a1041d046540445181200e500c0d0b2a609070003d10130701d030b51141c220741031400d6069501540010400d0200301541111484590703180c507507403514419038203840d9a503002c00c11030507038244080701c001098103a02d650100000000617204641c03d41107690030700035001100204520200d4203005c400318024440510b241d80351401c0000c140c0e01ca500c2c001418154003069140601004201003070044500d101110b480c04811305202c0b100390044095000324120381040d1041c18201801000414a170161205045440d15001503a10140050701c450b04010705004a002180605200b940105000501030396030307051070400c05008040052a00c0307030440c103008843c401600d480d40301d1a070001783c5003408500a9512010f9003440b2900d9404a488003420106102d000040071600d4848108207800030021401040d00b881130003c1c1141100f2519503c502040010003d10b41000c061a5031520386064a00d6940d40003400141d24a0000e8072901d41d281c1c0d403c5107041d02440364 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 841232050 1250 841230800 841230821
    0xa080f0903090d050f0111040b0405060313060515030c06070201020a020d021f03091101090303020d110f0a14150c0d09030327020316051525050d090b030f04140709020a05090301 78
    0x69180c40e00740b01140d92700740310311703c1500d005001c0080061072003101142005170543d40160300f0f00c450f0416216441c0c05019019406109000b50b02e074500c4185800c504690840b035060b009000300c04510780812185038180101681c0088030000f240b1608402c0b095008016030041d100000c07094954103005d1442140c0300801c5041c8680302c1d00600100307400007036050410b05030380f074001c079806100c10040d42802d0107001e5203903c030302c03c401c580e40030804000304041d002e9004504803841d0038003850b01e84400510942d18041882c0301041040b81c1b41415402c01188640039040128060041c52540300002140750b00d1f030001d440d807a40c1c440301107140030b0107004c104281c022621107001c1e080074001040103503141d1103400084000644411a585040b84810740e0301040803403a2490502da0420030384480001c091036001414941c0d01042d40b2180506030ba0207200c00300303040e01240e540d0359184041900d104120f02c41c14840c11400064001650006040b0007855942c1e0b552075090800a050a49408251 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 841233300 1250 841232050 841232081
    0xa020f2703070e060f0f04020307021f060b07030f0302130312120506010905040c0207150e030706051e071407091a0109050d02090618090c0a0b0a080f0903090d050f01 73
    0xc1048036a0000300b211390440c0c011506103074810466800100e00c090803008141d00240040304200d451500410003200b61a5009103420071b0700c6a9403085402c0351404d0040c0c01c2000b00c28821500400c1c8140219210000c803030500500d0150650100031104a95030700c1107404008410400700304a60000c40444880400d10060101e802d040001820906040c01450701842d541e200c03a0480910801c600c4004104900c5142828804040c0060054284035a014000d100e242c0c0c0014001e48140d00b01c0700364103614039504c0503402d0140c488900b1540700741e200b0388060303e9203945c1242a4006218900040c000a5400242c91200a04106000602c000b0403410300292020400094171103003240120320340d045901000d01e5a41500140080b40e200d6000c1c06070811034010002844000680240c00c080101e402080c0039a861203a201c407031041c01a1240018012008520010030034580740f504030303444005880c02d1000900204220f803404410070784d1994082ca80400000c1000e101d40014200402c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 841234550 1250 841233300 841233313
    0x1030c020625170a0903200a060906020909070309060b100e04020d060b070305090a14061606020904020f0310080a030207171f1a0109050d0b0a020f2703 67
    0x25031159990655035034000e840346070540038403006100b5400400c1400e45070f07800c0301203410103a2148000b411240c0341200401c1c040203055590740d0114a0080c116068100141840c0c20399036940e5001e05040b21084502d07903001c0c400242103648245a00340701c0d81d1140c0c1c00241c441114140f48080d42c00141056019103940912200c6c80d80c0c1c00028856035905c1a100960b450800c5e03201c400c0105050380c84101d007204045080d90405611a006124040c01100c0c454082c3d0340316140030440c0300c0c4d41a200340c0d0003601044861100c4100e01d54503040a401028014180790200b40890240c1e40213101c0e80164140001c100b108050307603030792814040c080200003456052076554010b03543e1030382401109080703200c0284481200714200310400400240c450704000480e4409003940103003d41c60003544c070032181842e4018403940f140005008a40d401441d9280003030041d1a0b607030340004082c4c029558207400700483c211017101040200494650001503109500041c03d2104810600032001c503c00d40001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 841235800 1250 841234550 841234561
    0xf0411040513020409020a031703010e010f0609031211010f0207050f0106080d12091506230a05040c03150b03180604020a03061817130501050c191514010501030c0206 73
    0x40c4002c803201941a240040c0340c183c0b82c00000c2400a46074401084040c40c40421800882030303101540c101c919411102105980b03402030106040c2da07601070400090400c200400206201c0e50649044d10b100381004040c00c8010f150360b42c250b401d603030003902c00c031600090f1420070010100190020801040b000700545410060801c0d00e500b9000800e1007005544080403080c45441d61152000ea64420325902501c2000d0381018041c010922034507a511140d01c00400b44030340000a40c3c003c01e40d009025056440c10901040002c0c001c3c1d54134081015900d5850000011001003072502a0011161045d1a4682602c13420001c050380c118090154110205000043e11200748120580f40d000790041038810940620850400c44400c01804805400c00c0248003401180028100d050b00211409195600d4000540d224445d210451660794402088002e1600c48090010300e41c42c0302c0d40240e2044909801d44d0001d8680704ca102048c1211402c1c0100419130300362040074081030117400600f08a1800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 841237050 1250 841235800 841235821
    0xc020c010309050a14031204060f06080c0907300902040e03040e0c0702060909070906021b0607080a0309151a0a0b0a35061203070c0b0a0e090f04110405 67
    0x110200200180500d00868031701900c180107807402901c0340e00c0b000503645401e0805030041c00c0710090140400c2c0c42d058000c1151200445d0340089074002902142c49a1680102100d104250300f2541e540ca1152003510380a0440b19500d0000d040c04100c00420030400c00d00401007116440d099a0300540c0c42084204108810712225542c001000c40f075260b1102014008500244a500006507100a00d8001c10183d0307908202040152402942191120601212041c090040320144e07650301c80310030302c030309000580703080d0080c112840a46000b244403542a50381001d1041c8416403400070f15203502040809500807880c0404240044441c002107516080d414825481102441410440900c0c0000d0700c45c0c0508104070f513614402015050300d030082a400d80341c408000d0311201d11032064241051841c90000095881941c0c00180c000c05840c5806a0b0300b50550003111b80606210180002d1100c5954202d61a84075028882031108a480c051800c420780d0381e0302c1050390b0701c26031500c0b00f4000071120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 841238300 1250 841237050 841237063
    0x13091a100806150406050d061d030c0c06130b0301080303090f071d0714030a06091a060a0807020c04060605030a0f060608070309021201060803070b15100507080c07090c020c01030905 80
    0xf00c2c2d00070400b02d00700781d40850301803d40d90300902e8109140010f07031310030800c507075010003944280c400c401c409031014164490740307900c50080c2c000c00a9208510004480c80c1c070381c004164840c108180e0040403903491440000640090784904800c0c0c001100300728000c03a05100070390b00c04180401800d0801c1c206280072040e4000c801d80c4103462030071840000c41c0f150042c440080303003c19500189450b86003a01c0f40c5406000740740291078416042002e040c0c0d4040c0160050702070410001d1810742008a040400c07211110010820021441443c207801c0d11a111445500003070078079940e40c1d035543e1800424080680e200000d140c034000b4a00401000041d42c0004400d4000b02c41d46070105051050340002040c2000200104a980d440c4c140c0004404400000400f241882000d24150b259100ea1480c0c1140c8500040c060b003041c41000110b141c588203500510746d40d80308041990030208841e8081d132800945400003880d890f0780e580d420004c1501048507041c9240240b0b030500850b40566685601c1d8403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 841239550 1250 841238300 841238311
    0x8070206070c03080a0e1f1a09010e0702071d0411010f0801140310060806070f05070b01090209150c06010501080112030e04020c03040329060405040b0f0613091a100806 74
    0x191400b050410f000c2e500b1844039051508103d0315007851b0000c095002805e910b0400e40c00c6450042d02002082380c4582a0070300e40402001044540c0ca000e0000800c144001d08040440c024910085506550012045190110074142001d07a103410b140050080300003800107810f00c41441c4500320801c0e405044c06044d1754040b070b0820b48111205011a180002e40b1041d480c03002c0c2000e6002c030380b00500180d647d1081c0c5869480181c0c0a000e40c00580715486111006044118048014003085144d5001041407400c00317410321651400c200143c4100e07410000c044211604848e004000541e80601d5940c05040340500c1400304818030b0ba006010060184d41041c001ca40106020f01001d100380180c9000f140c104240d50a07203406120104d00d248250b65101810203203800c040b17586401c151243c01c0c070465201c1d600d0045600c8040040740c03903060061103658800780b80e1130440d1040d5003600540b03904500c941403e40c0c661103070704070048007080018005c01080d0180e000402c50718034001034494109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 841240800 1250 841239550 841239557
    0x12130213110733021201050103151401201501060e0d0f050a02090106020d03060b0a080114040e190b060402130e0a0207081204050c0301050c09011202091f08070206070c03 75
    0x3e078900c5034451141d2450b800505001c0ca602c40c0c15160036259001041d81160800910005070780329001501110300c0030f100050300000d02c1e0003d101040d4040301c40d09008405040c52040240e4180040c6201c0c8152013030510b2540040186042c00c1000d000d4040c0503011604000103505481e0012484451000c50080c00c1c40524182c250103110342400008483c40d00034005e1846503844640c040e507158921045080000d2601c180040c44d207440c02c5c10350300c440005ea915001142d280c01e07000100d0142d24845940d02a503030b00e00c034402119040060340030041c4411540d881111041c10481c080d050300030301850285004000c2c9000420314900010300760740b00300440d8a1103449003180750009000342e0300c000341110000501074052811048415215601c00d03001c03107030211140740034982601c0c010740788412b030620280042c204a6000e41040b40e940c84000d4801400c014000d0f0019511440d030501c004107810096001404266112400f41e0b4800304500040c0a0307070030070140c002d01f42848000d029080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 841242050 1250 841240800 841240823
    0x31b0e01230c0a03020a0b1302060f1c0f06080d14030f091005041112032706070b01030c051f020706050d0e0a03090e0703110304060908121302131107 66
    0x4045214196011000b0711021501c018000340b07006545c172000c4c1807064410254110015185410140c1003a002030750140c41c0a0400712400c1504840e600301c0518403207000701080748030805185034401d03221038101240c004541c0b1460f00b0045401c10346900b12480c20441211050800c1c95410300450ba006101c5051041c1569501c1001504091044001c1503055003000b0a01081c840510400501e9540844206c01802211540280d0302d00c074003072040300303550101006650454402404030001d450003415003442d001180d5602602510260000c54128450601c14052401c010043c0140e180403c0848418001c846502a548802912501c0d04010000591100e440c450381c00c03040c1401e0858040307441140c2c4a203809070a503599401200300804501c4002840d0074468040c45020809500c00e1307600d19240c0e5115440689140c203403d071094442000302c6070f400100690328034404c1c43c0707000c403010540d4011710400c00001c6046681e222a6401d00c060301040504680484101c0ca80c01040d4002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 841243300 1250 841242050 841242107
    0x2280f09090c350c040f170c0904170a02030414030102040302010c060b150418050603061b09240a230f13050402031501270524040303031b0e01 63
    0xd0f0071a0721010101804400080c00a0f5a0721341e4003410a0301e213220210b08032640c0306c4075004440c0f240d00c0315042465000d1040c24900c3d05060218039001401100151514071205910303c0030b80d4030002c0e0510040e03000040811845580c249031a03030041080f0025494a8559000245400c00c1100060f1045940d200404a66540c802480013102e0032650a40c0d10b441da96450805a9009032044171456402d00b0000b6145250120f080e030311481d545030341000609003039926a07809030802d6982c00d4100710b0004510110301119031043d401c2c241d91003c0d059645104400092004600040030160f00c1506100d07604200c180030151a48848422811501c0341e1544c2802e0f001050203903c0960018400014055003011054506000920a0320703210b8a208160058a601ea603400d680c0410320340d00e002080c4901e00c0c00c0202001c2c940c141032010201d4406248203c403490707105a004802180c0d80d840030007502824a0f4088011840703504160388054129800030b018114195402d4032480d030018034402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 841244550 1250 841243300 841243367
    0x12070e090c450403030b0f03030a0e0102150907180504120f120c0503010504061212050c102a1107030311010e07030b0405010e03070302030a0302280f09090c 69
    0x14440c00348501028001c00c070b081d521a05018042d00c007940080d017026494506401c01c0181d50310151805001940703404203040c0c0842e0342c000c000d000c150450242e03016200184510720b00b041d00590710310000e03102a528102c110f105014000c18030104903070500f0100320124107640d0050790180024103024603080340000c01103030607042c4280c1c050b403807914000c06a103a065000010f14107880c0d081da010001c01e51148005045242c1140c001004180780740e482440251003503020b040318204090071035580745100721500c400c4d0742d0840102001c050703010b809260b20f0100300c1540040c000c003074101610003035940c1c84015182ca041d8080502400230070060f510300d90600358031081c0c0711550030081d282003944030f1030036212180c0e042d07a003038405609140001c441440b0100841d422554150002c42c5414202c5009902941004202100501641d080500c0313242d103094203060400300507501d11610560803807024100801c203801085441c0c0c5070803d2144043d4026946c494180107001001c40c41500919001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 841245800 1250 841244550 841244629
    0x30c0224030a1d07030506161809021207030204140d0503041508090d0503010e01060e03010603080409020d1a0303040509041106070804032609090a06030212070e090c 73
    0x4100c5410000401900404503072009403010980400350a60380000e080c65644d80c40e80f404090400d41181012510249004514004055590404a501d010341502c03813100d0114035800301858940000d480e1114144070a00164007425074281142001c0c1805080c1c030410b080020414041e900600e0303011306211040094030000d1882800f43c00d05c0203080a00284880c6064074064010702c00c00700001000e90040313040d41e041e18809a4910b16a82c60854129558055240b425405540e0340300040042000c0341d00400c054003c80b103025980e80c441d802d680c42282c10408041450704680c0c103e030805940c010045034101c03203080350f418101c0d44950801550340394911482c243d2000380003032542d0420040750060710460340200b905071480c0f182c032002e02c0e04a4a0b000303240c42440d10104003404981c03401040141c6c000e15070b100d000170015100c0d4042140404071034800401d80d400090100b10020056602c1603101d0311181c050201c9603c0e5102140030140300200b80c00e501141d0325100c040c841c1c0e401204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 841247050 1250 841245800 841245859
    0x8030705030612070f18091113230708090706120c0e0d030e0a0e130f030c0210030e01180b130317010315050606130306110904050928030c02 62
    0x140d480140d5910a0844c61740390b5032184201e0141c80300c420821908a51040701000b0ba003012307003004254030020412a44029601507190025525284640c0100414166500400200b0404c1c0903504100e24080e11089000704142c0346640907513400d208142c1e0000c000c440502060360b0110711030020142c00d5690a0b06140210b41101e0190055400e160344007091802100702624618009a1582060400c0d020100c2d0b42c04e44520b0604050320008441620442502d8028507240342c202d076080d030000340c61707000c44070315500003944820742d043d00c1c42002c0c440d030034040010b0480800000d81c65035034540703181d90041050000c9140354051505060040e0040800c110210049016540e1686010ae08079000b1514030b00d200d074034110002d8090301741030007260f141c3d10343d0b002604591840c40c0e58080c00303880f0441440e03203070140174404964075850b640a03650180324030078080c22850b05000301d445031171740301c88905003108a8415a03640100b80c00104840840b40c05544e40c52119215815624131000c01004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 841248300 1250 841247050 841247053
    0x12020d1107052b0215060a080105090709110702031b12070e090d03050108060402040f022b140606030f060105120901020d0e0f1b0f271308030705030612 67
    0x441ca401c201020540303101c40f9601082d040d01d880040000c64240001048002d80564844031220800725025940e203540306e64018050341d1301c1e42c1c0704d200d000d080d90003e403a221060380c02013100f0300280740d19000350314000903140d8429007032041580005e560381c6070012000c089000705d2003090995031569401c038403c0c2c0007120111800b403903035440c058070703030784000c40d0001c00a000b5100300b030079658400d005060488417140c00070089621660200401017005540380d000090342003040390a030706c1c4c403440745c905410416031817006005c6020456000381c460712407424501181a00812000e9910241640d030052140b541c5a002c0b680c442d030060311648160034490101d00c0c070613020001d0b0b43c0415002000b12400c6a20180400642e00074500c3e902c011002041d03481d0741180d9000c0f602c041c4402096101624000d280f0405035865001142d45100e00c5c24140030030220000810031096442810140c11001c03200c04160f06000a8541c840300780006800402000000000700b2140d6440e01d20103004003140c40e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 841249550 1250 841248300 841248307
    0x6050a060804030909022106040608011508070807260109152a050306130b06031608010816031415090f010f090b01121a0709140d0312020d11 62
    0x1070a10081214200c000500b08200845d110055000342c41c003401c80c010048885081100c102e10000c1c0006000503040340d80c4040004900d1000d0052050340d49520030855070031402c1006450500d051900104401d612801040048004080202510500d014121050003e15500ea00d02404080350060524401d031200341c0e0000145511070a001d81031007414410540241c00c8118102d032200d030984020800c2407000841a0030302351441841c40035850310004011003003400003038160b0000c0c5c0d0614085c404c5d50b058811040d401107086070140c40013400030b01c22051640c504d01c0c2d100c0940d000003019a0704500e450070180404000e80704402c27005052169603864140c5500f56a9110035000740119030030005c0d10744180c1058480c5120340c98119405805a071f081110b10840d011031010201d81c10100c1d0510301d102403100b0a9200d0182c80a59106160301c1d02e0490714030564601003280c83d2081101c1d440100000e508060708804c1c81e4400c041c05038039201e4076200b20006143c0b0328010090104001f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 841250800 1250 841249550 841249559
    0x60f040609061106070807030b0301090204021c050f01150309031b0f021f0c020d0212032215120c140a0e0306010b0408060106050c0a06060e18031908060406050a 71
    0x410406460440ea0341821110011080940e04e85090758400e02040501000c2030090781720ba045075001410240c00490781c0d1010b030380070600300c0c0d102c0003006000000200380041311440c24000c0d41d800c400d580c44030101c01c0d41030a40c4000311520f00308400080c503039220b104004040c041e204c40360341e482111003440740c6104103041032000e03120062030803403042011a020100440060035403107480010b9555003c0312200650900c43c1c54000c0c80d0b001d0f0b90001c00c3e09003600307680c03404000405a420040d0410501c0c01c04800c1a000d0b803040079000f050a502a282400d0380c1958040211100903418100100d44000010310a8400c0f281140d00d082d820100010480103468111103403030342240f015011141c080e030341c0780d05400782c0340200c0c0188030301c40d04074000404c083c0380f1410250250046000a4940521070341e80c0c0e080844010380d0201c981c182500b400c00441241c0e21710441d8003543c8402c041c519141c0485120322800380b40a440ca0140003c280c080389064603a94001c501400300a0030042c00319441c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 841252050 1250 841250800 841250807
    0x120606030237080706120b19030506070512160e030708010603030801050303160f030e04050f090c09160c1e0803060306010f030819030e060403051c05130809060f0406 73
    0x1070384480840e074107042d03451541e00080b1511440444880d2000340003000d00300202141d8148003002d030842c0e202d403a2030b00d40002d55104507488143e41090181603544078594a007060500702c000f0020720600405210b1902480d42c9602550780c0026203400302500035201e800242e940513003031908190503104801c07006c030b80d00c18154024020b0703034001d413a180c0c0b860380c0c1c4604065907403003521031042295454040382400a108540e400d15082d203e0b082010700c0c0c1c1b8100021030101d910484400107104040bd0a02a82d02d00034007103aa0200c909550210040c5041d403003e03202c0003d60351044003007102495009c024840e54414662021010b4516401c4c101c00070704010107242c00030345542d4803c2c0604000051112000a00c5400310703540064800e003001c42d10b0014185840301009042c06068a4a60100148405105992081d8425100c103034903242043c5041c1f100d0b00c0d010000760740f8070f850041448034084a543d4014200f1340d110b45011f1f075404034007022691a00030385c400e0381c0711060041400301c1c00941 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 841253300 1250 841252050 841252099
    0x31a13060c021f0e15040512030a0c030501142220090f010908100528060f120803040f03020102070503030f06093409170a0204051602071206060302 65
    0x44210661200c101c107540e500c2d0460720b10071026200369002d11404e02617001c040b070560760700078040c1c4155048801c11101e010303184c1d40f0440e14503010640e201c15000745c064051050703601500301a0000b205900600c0c2c01302c1c2d00030040c0d00010900441043c00c0d007004100581188020f0542c04821300d1140c014030301809090341020042910450120350300800c69480750741c0c800201d0340c102d402171045400303184000b00102000f800c90302d000a25105180465070109400080100003d8000a0b000d072410a40344190304190f08424850b02106005102040c50602030340d400035040601e448004c11945400d0740207206000c0f009280340008010003061940b40c0c900b40d4410b0000781e55040541d51803100410030307000760900850b0100380150021540d0614520031000c0d2016500b042d01c030300c0d6125900000a104169803408965204c025524110308050060a41001c1c90000d1000500b2003100080e4036560140141040d8181d40203d007c00d1003181e4000c00c00445d00500159040d0104c050051032152 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 841254550 1250 841253300 841253323
    0x1e0902090c0306030a060b0d0816140c010e15040e010b0711040504150b0109180c02070f0305120304080d05010308370e010519030209030d0504031a13060c02 69
    0x30180000c4003240c1640481e44107035001405807079480e00640c2c6190043c0760002c49541c00c1090340d80007100080405c00217150a903003010010000500078584946038840a000861058000b020340000d0303a604440c901007089012500300d6115081c85184241600031580711581041d455000005c0044801c03009104603400350550600c5040c01c007080c030044e038801b51001044d88640c00c1464849107410340c00392a0008052408500d4560350f6941a0990700700001450340d01f96840a01c146040d40400c00c00000340001d01c681d62156142d525681d8403407c02c0d0407065407210f0004001000c1000c01802c8403452040800c04100c035584904209071a600942d003601c108100c11036200f00440880c2c0040b48135600c000c444151003121240c81100c02c040d540c0c8400341844414003a0040d176030180141e40e5480e001e40d0b6001a100d102080400d45007102500c510010701c0030800040c0003140b200e042d07004106a5102044906480310b40d40003000589621001d020245001d601000b1a94017246402400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 841255800 1250 841254550 841254559
    0x80415020f0a1202060a0207020f0d0204020714030406021501030206030714040f0602071412060a1805010207260c0319050c030a02100e071202121903020709110c1009061e0902 77
    0x141e1b200748414049111720310b03010758484140e110181083c0340003601001550710250002d420b200d401d95500340e4500503282450a147c0020906000d001d0703040081d00c004a005d20521300540d450354001c6400c501c005082d0004100b034803801c00c14941842e03011180100380003104810308554401b0005d440340e203d400342180507200110511514034260142040c40c02888000d0001501d5200d4500b0040000318a49603801440240c0400440e10030700c09090400e0207484c1d00190060300c0c220280c20365400390141540d4440034000561010700000a94120548000e005900c1094040064505014065806c1240d100003e107803030030682d0106802840d9811080107016001542250315200c2a2074000c0da002c1800d107100358805480d22401461001c50a54140d130384592070440c14142c4100d02c4078054015a1100c1000c001c0c841c038611030141da05812400c218203191103806216180c400d82c100041821340c8900c0007400344142a0301c030922030721300c1c005c042c815984280803c4021b0f04007031901b40e10a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 841257050 1250 841255800 841255813
    0x60c060606090b120415060320150d0e071a1305060c10110d020f180102070617190507030b0a0f06050a050705032a0f0109080415020f0a1202 62
    0x4a406400a04251448803800c582080c0c12640c4403080e44000034006d0f40e0003141410254400b00d1079104000146003d00043c03038495107800b03104012400b20050040c010807107103c602c0c04840861042c2d03034594200c000007050381410035400c14a031070310503003105e100306099940e0380c03d1034240d050040184c49004402c22840942c0c504c02c10146005000809025404c044036280c10300c03400f5400255a020007030012800d110807240140101c2e001200d407007540d9080090800d046030b03034103280040c80030000d1008225690401c40b008000032150208126540601c0c8046141d00179a852610f10f05559181e081000d031601402c0100503060100d01280540c104001c0072070b2810600c3c0d542000c3e81c1c650b4407801d1a100300c14170110b0b0a64010704e41a2600d02060001491407035001c440c0d0746415a9000c0d0041c14030700984506420200303603c00d401e440d80e2402c0c801500140c21201658100e40a0100c0a8010f211080090342000c1038590150b03558010300c0d400030200300302004100449a4103502f11010b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 841258300 1250 841257050 841257059
    0x929240f0a110c090603120d0609020a05040f09110d05060414100f0b0f120702030d0504060903030e030c0d08190905030310080706080606071a280618020702030c030304060c0606 78
    0x204c003e080e10f0454164001c1040e8807212050180205014102d0280010742c0c1ca03503400d0804100e8201180c544002900002d080244c840c6410815014003041b41d01005100c042da560048288141d01502030196103580c0000c1d6140c1d1641d004005e02e88228100280900c1c003800b40c1442210980101c42900813104d001081d10701c82c1c3e009032258003417003030405132074814402c020180e107040040180e82103110070400004205003d00505010310710444000c90103c00d14500501940d44a180418240e4020f000340514100c002440f0041642c01d4202810315031030718512080c84880302c031800740da8a81461704400c01c0040000086106106003064040c26946404020352180014810000050100c0c0c001c1103c40c42e1003001006058031448181c454900c42483c000889581200c0000140c075070b20640c501c04941403401580c2c0c1079840d15040062500303040707502d041b1207020007100306100d60106503001191800c00c64200c0000300242282d80b1903a540800a001200d0403d00300e59680c2094000613 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 841259550 1250 841258300 841258309
    0x50919030b090f060714090d11130b2d0409060e0a0c0513050115180e2403060118050a150b1306020a020108010302100e04060929240f0a110c 62
    0x851004c3d24070016468148034034104400d044c200141607440d04041d0712701d0a0319503280c1d00c030000c0d060f01d00d88001c03c0780110f0504000b100c001c009034000800c0e65141401c1e00148115036007204041085030f0004619880e8144803006120700d0400420610400c00754906000d00c03001002c0884904a802010089228102c001510000e205a264580c1040c2044400034015882c09140f460400000c600e11545c40b40040b0f104401079800d002c240d0130200c82003880010031980d05c240301d14103a0050840b94582256101c0c0703103140b904020b5000d42c5d10004101c2150300ca800c0103c151218500d1030031121744484c810492644140f2181d0a401d001010000d80c0ea4001304028407019016190451a61f00c0d42d02030080d03409030703081100100420303108440032940d210312800d4041c1c4a2070400141d5418222100c9400b4a02d090882c00741c015103010400c01942d40350034608515000751881c83c201d00554403000040c2c0a1920280c81010010540b0304071180e10500c100c01410100c0120b0300544010030501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 841260800 1250 841259550 841259567
    0x803070c05061e1b030703090311010c0c090e0a0204050a051906030807080705011b0e01020f0304120224070803190e100b010207031a0f070f050919030b090f0607 71
    0x508018802d0030700107102000c4036001c1d150740c0c203200041140e034042c5200c4d16821503000c8001200490038900c0140280454001c020302c08600030300380800301d100c65495044403007034a44110b040e0507454a103803c00145040c492a01c0d0143e020b4400d0209051411107040641400c440706298584620320901c003107010740c0a103a04030303604219042e143ca120b0352203070711203030703122400940c0e0541d02c81c00b6030880c0e21408625085c0008843c1d440507800d61640000a0501e400702d102c050050348144814001c40f40380c00f180708203e0390b0403a1402e8445810b1900d07400030350f084420300d003035060002c82e00c0b1091103200c800440c403440200b4040c80402e214001001c04032083c12111914030b51040c2c1e01c00c1c0e907843c0d465000f4144010f05004660391a81d40307a60b1030701001150717802d00388008442c0c3d05010a01e944040f2041c0c0240326420940401d403241c9600400d6400340c0c10302c8510500259081241c0b000c02139028002440d0011102c4900780781c005041d07541d485032605002c400f4032500000401c1e80e441000340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 841262050 1250 841260800 841260817
    0x150806091209090a0e19030f03140c0714060a0e0705151e13080f07090b0d030503070e150c0708060c0f0c0102090301050709080c09040b04031b08040803070c0506 71
    0x30300d00b40100324040c0007a9800041101015690350b00401c00109410018010041e01400391000245082d10700200701d4000c0440030307014141410f00090501c015043c50f02d600088600b0100d484501e43d0900340d01d803200e283e556080d1401110705110424030150003001054180038200c1d00c00070343e81d8090012000c0024480e80880c0c005008920f0180c030103d0300c4248e012624001d582c14040418405400624036601046040d03000002000c0790b03403800d210b601c0c000c08002c0c01c104030b010340c2d540228192a0b07043c01c00500300440000080c400601030095803a080c800501010860800134904d030700154400030080b141031181440020b100000040da070751154038070003007150500e07803c490681510303000301d50079180d155000e010024803501c00b482111700c44c04180d514500d0040c42c001c11542040200150fa80c000d940d400100304c003007407907440011f0b006a070501c0c106194000381c8083c160002e00040c00140410000200060120320000c094103034240194a0100041c1c0d540042005500c90020b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 841263300 1250 841262050 841262083
    0x170d140301090209040b0424150c02010507061503030f031a1e0a030203010f05180c01020d050a0215010b03160c150b010210060e011d100302101215080609 68
    0x10b0089220340c0d000b03003070001c201030000305003510594005015505503081005080b05481d0460700064005011140140130b85501c0d240b41309202c020080001e030000401030305012000810500700701041d0300c4111071014500001d1280e80d01d80c0f6000f0060802c400c1c81400103410800200c4948081d01084141803078010b01111800f180c010b224130811100c1e40c07580340d0101c5a40750000140c3c90a009844054540b1240010103140c58101c1c0c854481050000000303035880f6030000e540d143d03000103214203509120700305246c8034500d82004920700f41c1c02e1142891a2001c210000a41d81000c401a50080c2282d200c2e0041040321404200c5143c6c200600250410021540240c9415003680c0141c40705001841502c50040c0d480c8005c0003a58016403205070320f404407200402c500600203000000450461740e03041090b0030110041a84141e0901000e4454907106250018140c01040e4100000d02c01c00301c2400b0708403402216141403101c51007581e0442c064800081c030941000b03d00c40d14038804015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 841264550 1250 841263300 841263307
    0x14060a0f27110123070c120f02041e2a020a03050316110706170f0106051803100e0106140607031d03031b0f160b0702121501170d14 58
    0x1103a4110079071050180703c1c1404a1020b440310344241040000d21005440c08505a441c000f40c5001001111141d0022081459040b030000006000542ca03c0c101d5030121804941030100342160f140c1003402e0030f440c041c081d00e4034800c00011050340b041010101c503411684510039081000036602ea0701c1b40400180003c80410010300008614202c030291034815140c051418400080c0707461501a03144c10130f80205400c0200307690381401c00c06403039601c4805401440031552411380050514010340e4450540500c0c5100c81c001c01d501e04100c005030054840905000c05c9a030394082034028582030181c1c055a1290f01540c00c820b042010413595440e0341541c2e01500840d51490029030412000d100761f0381030104011805021301414413080700780c25017001500c01214031500e03482c5049000f41c07200d03481148900d802c0006880500c180c40707038250166a05402000340b5814203051025145400b014481480b00101c0c01075a8083e8010308040d044046444814012400340d0746c0c9184101c402c40d0415040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 841265800 1250 841264550 841264553
    0x1801021606180b191506050d09030c0b0a1e050606030c0a0e0303072f100507050c0a080106080d11030d0b0d0606030b0a060611031614060a0f27 63
    0x10342c001007040c0300b1542084510b90041e500d4010186061310511403000e00102c00d03007441c4c61340380324980143d10b451307801404c014a849005000b0f80a2040340d143c0b02d0b6501c0c070011051502070401c6c5200c860f80b140d0b600c0c103c1d180c81c490300340c0140715003800e12064208030210007481c202ea622519008550050142c2d0031a9110070000d400396211030300303007420005850024041034904001130302007244904042c00b43c21103882e00e1081030a00c11900300020f40030340184609591591800d001d6030301c0381450b2031544c44003141842d91520740441401038118040e440c00062140065004032b041d121184145c44000e04100c100310f40f55044d100740c005894004014010940d080c5a000d10040c402c05042c90f030346220503071107500c11a2a41d070f100351843c0c10218100030080d003943c41120094009402c280204040d4422402d603240507508a400d500f2404500c407105100e1405c0390b02e4001c40980d400c441c42c80c941144a070740070780800c1501000e801d0a090421104114100d41074807948200704540342c418146 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 841267050 1250 841265800 841265813
    0x1081b06031f030f0503071109060d060203181b01110334020d03080414030403080415090312020a15021207031d03181c0302150a06090e0618010216 65
    0x81402500c03002c1690140000056140030094910034000d40180d41c90303248500b0b140d1000c1001c0c3c0200c92042c480c0d40204000c1e1340c0c5080c1d0011000343c00840050700c035034801d030000c6081660b80100c00b0380d80c400c081c82d84400c0940e60180d416109400c2e41c4c0c0020f42c0d070304210180c0d501c0c0102c01310403101140960744107410400c0f01038114144280e403c37100442c0c0a0b9074000c180ca1410303860060b80050110420041401003d1105040d2030000e00c0085141174910386130800103004902580300040e510030f45001d18144604040300103103070072803510541e50304a5900030b9601c2d050520100e488000c0400c100e0142c040910a41e612480100d55042c115038030301808a004040e40b00000000520015103101d940c0f20400142c60841c5180302501d04e100e0912040028410740d00d000158424541e00b4003030002070b8003183d01044203034207151001031a1244024bc8002c5e00494004440c8275142510085190300001106400380720455414008482051301c81c41c00d0f072140c840e04510030b40003183c544001810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 841268300 1250 841267050 841267081
    0x27040209041508011d1f0209060304080c06010e090a020909010b09190501270c09170703020114070305040e040305040806100915081f02040b0c010501051905010206011512050f01081b0603 82
    0xf00001884c0c40d01d402d0001c2c9c6a03800039182038409960201e03004181c09410070000e405003009000d00c080e146840810740303035940b0416200070f0080c0614008107030008425004000364150090403100c540c6890301018044481c054401d00700507051200000d891140c0010b2503c040360908030900c2506942c04610000c1c01945010b107040140d20703240080d582c502d80004c14030000c9580054404146180001002c8031185035610390496010009600082d42000803070f8100d4011560030a443e598a0a003680d2074040c0340d112103000e0013050f04000c44c0421410342d440544070109410050b040082c407005030880c01a008400312680400004003a1508128195100c000c0070903001d40b509407900400d0034981c000f02d0010700c45030744420051049291605c003140040d00148190880e191810340000d503030302418440c1b034181c01400041001d1483c0310328121043e07010001800c1c8406d04100c0080500c1602c240728803105030052603101c014002075140201c03001c45000740400e0550b2075803200d200000c00b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 841269550 1250 841268300 841268353
    0xa0f23100621020f13080d1101060b040314120d021b160303031a120d0f05030903091012051e060111123f010b27040209041508011d 58
    0x50040c440400c5002d20920004090071b588000761100301c0c0d40c08400b4005441000c1001301c1a41042021311550840c403081d602100d802074609030702503c5030406036051000c00c00440c0055080003810660810b6960000c014544510303800c0c0306a1464281c147e515010000c13079581d04030b400000700f0400f02e0f200307402842034100e480f207009001c074034500000741210044016481442e040b10107030fa030390340d0b4001c080222601d250b070410350303d945440c5c0e20311901ca200b49a1201e00c9403101c8030700d02c041c2c207100300c40c03045102c91340c01e108005508125099604019070841c0e040b013048480c000068003540b16116402c420f0b4034860040021201100130b2200d150020600182e01c0c04419021101004005040030b00b0004034449080d914020800c9540707002405800241070101c003084885036517002c01e0715050000080ba1560503411001c540010080d02c1190403403903000c0c0c2016404840048440c080a048400c03840c02081090395a5440507401a00c0040c2c003078198110200e00a15071989000c0000040f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 841270800 1250 841269550 841269577
    0x6092206080d02010e060604050601140d09020603041a060423040f052e0903051c060504060602010b041b0c0b190204090f0e0a0b0a0f2310062102 64
    0x21030311003a4642c42c10002020110060b910381001010700d172024048150001c030103032000d000510f018000a44465244100310400c614005042514954990702021095074010040c998908140c101103404191500d00c03034071900c1c1e038040410264645845010b0f4003070840f8a07000c11207543c0f51081704044900410507110452813200d241c002400601489a200c2140d45a06404988681140000e41d5594103031404161070070400c040402d0704802560a140d0380210114550103003010b45502405650f071201d60030600b0b21b00702144054064106802c00c030b2054408010442090103078103405900711070110040b62079001642c0200300e158410580c031100600541074460b4210546008982c025880408641ea8030344058810315810f0244844c0c0c0000c10000f4a4000250f40f20003c2640c8064204c4109503590042444002559007010318509041c4182c80521100302543c0e0f03032030100494440aa542106402240c40e41c0145000081011007801a20742201c4083d690030081d802810002c001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 841272050 1250 841270800 841270811
    0x110c042c0a08030414070626090f0d0906020d090513020703050705030301030f03091e0b0a1107090506010e030706081f031209090f0b030c04091e0f11060922 69
    0x420b082c840154040c0d403280032600126041070204500f89041358000300208903030418800748204a10103000c100742e105120b10005074880f0800b113450000180c211034002c2c050001c2103800c45820070b010008030307005030302aa41c2c403440801c4200e4400c1841d02907150f00c081c840780700d441125515406800d400e40700b800c0c91071a2032881d031200f034503580090f802240c5048400d440c0800b010341c044100c80040c80302c0c40e83c040e540c09200c1c0c035103011b400381405117065002d0f000c0f03462040944510303400d04840c0c2c01c84003076980036034840d0a2440601400c6403511b02007072300003400c0c03031060800003140c00c22983d5a07580e03411107468a054610740c0076502100c205620f03142120100114000d640b14000700c44080d00e819121503c1d0070f4071070058034001c400780c1d00302e145000584180d94801141c44101940c0840d4005110212850403c02024414040404d4480e55414101c200300070154103090142c01014000c01c142c601004020031803080c1181d42c2d804c1030442e420402c81350b00000360700c44016000300001c02e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 841273300 1250 841272050 841272053
    0xd180602280f0c0f18020c030a080c0f0705030d0c02073002090c0a0f0815090c0c0607020604060f02180402090f1e04050a141803040506030106110c042c0a 68
    0x160821240c00c1024130b401e0714101080781e0740d5103414002c0c2c904034404003503003080e41c6500f9403a103c1c010481030340706108145001070521061071044800d503c1c0c0000109441d04854102a556a00b14400f6020b03418501442000040d000085201c200c8000391030230400300820540003602c07154030051031804141c144a0750401641d90b115203620030900e0346902c9403140918000107204818004d1001f0604c042c600610550402c000c400641c20300c815905182c640d00c0d039a844010703521540342a0441030040700d0521526590202d20b50740114016101448984191081c0000328404c080b5903440d812000005a05035003400e070090a07a0000040551b80c0b07800903600842c0c0520180780f01d01d01c1030240301c000100145001d20640c0d070030510b40720041022000080741c10b40200009804070f502c60480e00038a4044071002c100300c1e0080d10026003115200d5035071b000c020b0b00c8146203a1189140d4011401c85520a003086d205010130300001c4c080d044010310469081692046c0c58509543d005c0c05080e40100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 841274550 1250 841273300 841273313
    0x60103240624110615012705010206010e24031606030b1302030f0a02090a080d080105040f021306050901030b22060f080c19080d180602280f 62
    0x3052400c8070040e81c0c1042184561030005150942000d000311140000c03074110000031455484400700b2146603860038901d005032031000314000b0344001c82411041f0f102c041c0d42081000c034102d03502a021184180d80324010403018510844907001403d4000008900014100390f5120010001400799104000300d0400c020008180b07401c2000403030380b1040354080c107040680c4c1c104501c140d1410214118203118007101000000940301c8440280c02240084041d03031040103100c01800618100c6502c0500e08901528005091280030320a602c1c294240400141ca8002c0b2440c4400004142801c582070000c2501d1030f40088013024101595002c3c03090f015202c0440c1107145a41324401d49107642c508289c68003d54200e9005088080307002ca100300b010030f00004400c0c1c01c04070101d60074504424626481754200c405980710031407500c07e81e140e80203505e070040619400c814800003c0045a0303150320040c0d82d90755500c0c540c40d10030f20100782a00009152046009009440f81c103903405164040d480e0315 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 841275800 1250 841274550 841274561
    0x40f3f02030307030f14070c0b0a0504050a0e0906100501020a0b18030406020609010c020c0306070302090324091006050d0201050c010608030f0d0509060717040c05030f0c090c070506010324 83
    0x21404100e1a1090b00f90303054001c051b441c0036841c80c2e0131403441c014141c1d8a880c4441414482d81e44101c40110f0f4100060340942c0603038000d4a0b010744100561f55840504070a1000192460aa1402181c012500980707d00b0f038500140c80d010f80007081010101d5036542380d40940146101078404182d14003a02028060000f04020203641c1e000b0f16040c04d01740b01d49401c459000744e902c2c00795070160f4140c000030744010802036888052800d0058441c15084080ba08140300f100d04004030240030322440840071009410140104a0901104d81400702025240212185401055801654200c050740198414402410128481000401c0550f5a4035180303165810000c60800c80035004103001e5240d001a1103010790046540c0700804050030120005881210f04080e045c64215020b4005414030803d8100c2c00300034500030342100c00d90040107031803c2d118882e40440754031070542580402d14802c0480d0543d9949500400901066480c5a5451104800c0c8840310701c403416044121400b14009880b44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 841277050 1250 841275800 841275803
    0xc03040222090c0e070f120b04020a050a18030201120906021308071a09090105010e011806031512231905100c1e0e030a0204060902040f3f02030307 65
    0x22400c140340380f8041c1900d0f01140c1080f079486058100b0000025840000002195000c1c18041100e048030b80c2e269025105020b150381c0c015000085800c0c542c0e03403110080c0038a00c1c2d103a0399002c0300a103100c80c40c400107402e440040e0020345100c64140307080078680c0c0281c6105104003401460807118804185103480b141c1d200d842c081c2c01010b020480811290051102c1c115041034952401d03001c032000440180042c01000d0401020f00c1001c40c042c1d00811003680310840b0480c003c1c40703c655806009000d0702d4518074500c0c1003482c040340024950a44501e40c0e90640c1c0c080140c88403440c15102440c58110a600501d0403031080020080c0d0745291802e54009050040000d1300e002d001110203036054032006060602084080002003050754443c07502c6420a500030b2400007485105000000d00c0c00805500281d4414500342d000251200300c0d90042080702d1400042c250802d035126441100e81a503103480b654880801c20b0b0340b03a5100c103840c5402c02c0a0380704000d8401c840f101c64010074503580107940b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 841278300 1250 841277050 841277119
    0xd0c23030a0807050c180118020d020c0c040e0c032113030602091f050a0c030243031a132001030516050f0310032a0b0306090c030402 59
    0x440c04180071041c080d8007a1007106545001000c06d88074150384102c901407143e10000c030011314156a01c3c01c0e16030101d0b50b0201c0e02c440150f40794828030284603100c620001340c8600c218502002c10304625004150405510402006032650700303505826421450013030303840382c1c3c0181400c0010318410b07090b41002001540c0143d90058545032980144903032a034801c0504078100c4500c98001074400e500508480b85140faa1030625010075580c175041c1c2c54440880824098900a00c2c0042003141c0c003800401081700301d000c120740e4107070644c01051070144464040544004d54048a03140342079002d01101d90407601c0c40c00c2c2c800d520700c1540c4031242065014000354403900d2941844401d5036034103008294002140d464510203895003824040d24910424546031070380305010000442a58210f8207460045801600e082c154015407900c400500c044160344550b980e002807004200041810b040d0303480fa2001800040f9140c0700d1680320040780c0c10080c0b0403640061529050700145e11400d1500c0d814410700003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 841279550 1250 841278300 841278307
    0x8070305360a05160e010f0b0c1501120312021303030c111806090a0e100c020708150403082409060d0606030b18010207020a030b070504030f080a0801050d0c23030a08 73
    0x501c03400310740f02c0c2d10a40785101c00200611101e0340481105007223402d44602a42e503640c503840c6050924600300c00c2400910a0b403000007031034541145440216500c40d66945071502440d8100070224002c481c200305041015200a000080c001d044402250380600900424481c0c408001012104006580c00618011000b48030f59400c000c0002c0e600710b49440300511030342818460303445c4d4a00000000d8000a138a1f501d100c5585c42c000e01c220405001c84100351802c01060402c2901c0074001524100d00095911001a242d040c003a5610000750310003454482e4001500f4080100188000d4a4aa88481c1c881c541900040c0c4c60300c6503000a501c15a080d4026241c1951903094040d10b0f080c900c00b1590040061400507a141a5642c0a482c0c0c4083d02c111281c6480f0340444041c0038a8000620302519400711209028041d0060b103e56119503031a060607a1329a030500c0368450f80000c006003d940c4524041c441e2070b050020b010302c1a07020080c4070601c0000d100c0028600502e121050340d9101000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 841280800 1250 841279550 841279573
    0x10120e010f0f051515040321180b030112060e030a110105070e0904020402070c1a090a120506041203020d060b121b250b0f0708070305360a05 62
    0x14014142030081000703007000b01d49010300c01c0c00c2062001c20b441c82e05c22210340520a00040890060758095a0801304861101d030403800c0030304c01400701e28135840110344400c072250380b00b0042080010a840b8580706d044e0450340b818025400120000380b04441198070340100c1c145400d004c201411280344075503150b19180640c3c007a11801c407a00980f02d1402c021007140d40d4603054441c041840c1e0000e41c156030043c2e5078640c904003c1001000742d00001c40d060812181318060305010000f805a0400c1242c2e0b02c50f40940e00d4541c44a003441303400000340160440030014020070285001c1c6901340480b0706000d0302e04495100b00204131492500440000350001c291203669000e0201d003503a20068441d20109544841c0c5000c01044c042c1d040031050f0910886d882c4074540c1e03080398800080b180d00801108080c204a01d1403810b15100322040000908210000390800d07102e401080e0003202032681030039003041603215001c08072444008000002c000c81050b02610202008041d82c0340740100c010305881450b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 841282050 1250 841280800 841280831
    0x2706161113050705070f1109010330080a0e070b310f180f050a020a0813080a270f0503071a0909220606080d0503041110120e01 56
    0x107a206254105140a08110400340c00404903494943c00000344140030105142190030f2200c0b10b48075640241c0a0704c000810041005002e405464030540c01d00c225034403010017590045000d4414100007000500450548400d03a4003640c21070b2250000d9842d030743c6d140d480c000811f6020100386501040c05050382c60300c45c0c05451040d02ca0300920214050007500c0e00160300807540d103a0203035903c2001a010700b2a030f068140d511050820100007010700c19441e101b0903110080d081140100e01107400300307001030304841c4003940d10141140c4c8a500c4508010081d1012a40c8a07550365541c036520311b0800e140c9600d0080c1c40301000040001d1228044102e050030181350a0411643c4801e03000402c02061000014640c0142c80303103107074252420080ea9959200810440304840020a030306140b590464040c040c59400940586404808580c4403a10300c0c20300702c541d0b01c421500640407034001903c224651402c03200c40340d4000d5851414840c40b1220324580b008a0362841e4542c003140c2c0d0344083c0f4407500307400e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 841283300 1250 841282050 841282069
    0x90a0b031515040e0601170f0a110a0b0a1d0a080604050d031b0c060209060f13053a06150e0103170a08070305060111070306050114030327061611 64
    0x2003e072024804444920181c690f01e91043c000c062aa000015180141d04020022180d03130780806c00445002c034900c1c0c109241d081805044040c0507203a110001701d20041c1c00340445428108503a41c414440307400e2030072030081c8113032b04005503405100740c400040c0c0c060003004100c0c0114005c6025203a68141510090304490412210b00c2c114109502c00300c08140c0c21a003803101180d040a00035950310740c42e10028150344201c0c4d40f84180c1010100e00005030007030100101302503950941d0a0900580c6030010403c10000303180c5041111450900c114890488658001d81918440c24010420503a8980d440130000380d80d81000207059040c100400500464142d90400032075180642c91410008200003018688002c10500c145502d45022803003913441803c849400040320801c0e140f802c0d803a8588100509030030301c60350000c0029118982ca0f140f07408011640c4202c030400c41c01c800c1251071890100c00450841c0583c3c1d020206216280030407090300c07240c0c0305240c410410000c0707151252080151894 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 841284550 1250 841283300 841283341
    0x3020f120d0c020f032709012403060812092b0c091103062e050d0b100c02090c0909130201030507080114150c07080a1a1302090a0b0315 60
    0x180300e140d2103a00c01801004450351b40c0202800c00d0140c110549001d46042d01c420003142d000180d07400000384501c1d4a14240303200c22480050400c91038045a012425910a0f0050481a410000600030100701ca000140348810300034001052400d00304800310035540b503000000031400c516030303040010003400d0300040000c0d03c10210100004050b018070044280070003003c040c0580c1031800982407511703104888618070900c0c00b0f0b0244401104c407600500d19000392804200706030422500701d0051906100c00b01c0d4003044d0340c2d07542d074005849808005d108900070340754450118080101407690344456807851300c01c81080468403104030207440018200c1d50010034110402c8202801440818560780c1c9512581704201c81c180d80000703003503025520510074880540610b1140d8140003c0210f40420411306807802554901048420b8800d58101740504581c2440c2c5079040345100c00040c588400115000700110600255103003400011030319268003c0b00302903080c490703a0b00b0446084c610303140e07101090 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 841285800 1250 841284550 841284553
    0x130618020901151704082805070b0a0e0f0d3005070903200f06070215090f0a09060e0106180e13290105030f06060906040b0a180f1a040903020f120d0c02 67
    0x307c602c41c1c010990701071000003d162030040780101e0248005500682c40c0541038405a0703c5c2031900c40c400325a5010b06900300404120f080c1c0c03407070010b112408904000071000350701c0d115009049006890003004003c10080900c8458440840412500244044100c000c0041401c120302080100080142881da000740305440800c95400141c550041001401c80d003a00d0150f221007a0600007515007014a400c11b0300700146100010b0908465008501141c1c24260610b0f00307039803100400c680303000c007000304001581c00c281c2c801c104c91529010325503444243c04444103048502507903485a8014036095a02200d0098902c4d4001e94074000c5005004000460040c0400c1002c003039250b44801d0018806880b0390b000100186807519a900401d0f81c040e4014000510b0310340320104081d082103d00300032001c0603d0042c41800600f21445507140748a5400680c03a81c01c4d42e1042084050811a00d08a0843c01244078501c40c0d10410058078417050f0f501c445485d100c880044001c021143d00c0001401103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 841287050 1250 841285800 841285867
    0x614090304090b0d120305042a090c0203071a060a0f0b0a0905060a02101a0607210e0d080715050106110c030610030201140c030313061802090115170408 67
    0x181c5d4030003506070740392050401059555030f40c104214849010121611a2484c12900741e55038200209000140c4d513a0500c10044580a0742040740e0740c1c02507035002031101c000301c4041c200c0900f25042c006d40c400030042800a4440e15800c0c1e8002e10348440d070059250500215a14101c035400c42d850401a090a450321750900c00e04d800001d699005079415418040c2c1e80e240090030030603118005040303409014250310b54850043c81e1243e4514070301070f1300c041303c00d00c0303180c02c20b107014400c0403030324241d040040c03007050311084540301e42234194046d000454082c5103a2101c0341c421103250080ca4000e00241c0c9a21040c0380040b0b0042c1d007499134150146106c0d0b00142c08000c5c1c0f802d40d03d68503406a83d020300c0d104030302e0060100207640740e11902441c400d0510000c420000003000039131a9002c482e102c0d610501c001c0d100b450541c0c601a00b001070080d4811901030041c070103e0078040016607103585a10b4081d0b2201c280c01c0d4106002c0f501990103a80c1a0700010f0855001024034400c0c0c807030144280d05c41c0d0300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 841288300 1250 841287050 841287053
    0x302030d080f180304030204090803090d14070311010b0d03030b0a08240c0706180320120a12091202070e071407170d0605041b12090614090304090b0d 66
    0x3410080000f00380324150106000944030800c02ea5000e1036000e8004c101c44038003800c08009170342003102c00a195100b610040080e040c400c0d040c02e281c250320302500d00e00b40155660706070350b01c0c445418030440b81d640c4c1d00c111500350396a0fa05a420300d94029100002d9070003120045c00026681a0041d07892548020a07840a0350002c0c540c03400002d14600c81200b854a4004151209100e0f07680003030b150300c1c2030403204802c8082c2d50052291092098840148070094840151140e0b01850410801600300f050740c44148003241c8010011080300d07203031050742044134151000894200803010344600b400b59201a82003034041002c400030b0b00941c41454240d01d000340c8020300c200a1102c0031180c55001090f400700308121070a22902150001411070345907203c07601044024401c62003450320a6060164080144003403140b80075136145680e5440481078100c48211010782000101125410b545102440d1400551800940245403c0018665a40c0760180e010140d6624440046c80751048903010720 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 841289550 1250 841288300 841288321
    0xb220b0106110a0b0a1a03070801140a0903050901140903010216050c010320130f15020d030203011511030d050108060a050a140402240d0204030b0f010e27160302030d08 74
    0x180e1213200c0c0c176000305103104001d5000520801c003c8400b5018130842c1c4020603d40419001000300d540101e000520f195584981641038514184015011450402c000c13107295100b004489080c0203454002c6113000034010110303089a1111200c00950091100f00d501080414802d01203818001d00e401c0c0f051700d200d40c80c1d4030000442030156038050480041c1039100712130517560034801030882a480340c100c0e56440b290703100f030314280c4508240140124034010083d54040d200fa139042e250744a807a0010862034a0042c1da0a8044103401c0c90303544020f000701d502e50310060041d0341c040d11844015241909204103000d090300ca0181c0080340d210704144003621050000070320a540150110b440007105c5a014903520503c56400c80040160040010144100d031581e80040c8110383c800c50007144140c0d204104100410380c20f0240e4207454050740042041d1407103005044c0070351140070340324141c41281703048958601708405441c0720b0a880e4228080085d840e0502c00128501031501b0001d01d213182041d64172 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 841290800 1250 841289550 841289573
    0x1e03140c0712150f050906090105010e01060f0c08030a060e101a030718081f02040b0304030e010908030301062d0e01031d1006030c0614070b220b0106110a 68
    0x480d14440000704940030300640f08500c80041d43c0e0800108402040505548007030701c0d080b00c1c50940c42c4240b0010400c1000144035150480390103004140380d43c0d0815600b240c01850011b000350410149901e03580c041903c03000210f0292040c04000668589041c5800881e034a00900941411443d5802049200b8804441c807059801002c0245e642fa0f8500c036003078552064048103412502d12403180800c1d1650002150002a101084200100d84145074180107034170440c001ca01c804c01043c008600000e0103591072003000c480505181400c2515101040e107160003d80c4014001030400303201d0525449130014004000701031100f440043d5100340405858400c40d40c042030304050f510f45074201902142001d428140c58a90161031280e9050036000014020500042d40d01080540c00040c0fa640509545003c0d400745420450916110340c5803020126001040141184000040862070254065030060302500c1045800001c0d41014801061400c0c000450155075114a00220125a1788001c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 841292050 1250 841290800 841290809
    0x1e0a111c0b360604110703110c0a03050703080a091706190e03071b090608010f0b01020609121e07051c033305040c02070801150308030c0c07031e03140c07 68
    0x469203c0d038021500a0a49004034800c843c0081855801c142e0f00403d1007140039800c0d000c43d2156411401080308034885480014110740c000d400800014a48a001d0840d02071142015840305035509200820070b540d50010180641001040181004000c41c50b041c590803084070401036402d01c0c484540d5684500140030b00142e0881004110304410502c0e003c2c060401007000744090780d909c0e810380380a080b01036031003040242400c03140f880552000503007a11507030141d002000804020030b0481c000340d00810540c0c005526100d00380104010000003022003070310a000038a0103c06115215556081c0c0e841400101410110242c2040010f07050070300600c42190130031000c07001000f110721112032a0ba07200e2608182000504596640c021420404441c200c500901c0442c211b140c0000c040381427408000c02d101018400714007100700700780150580d440624102c03180c0701d4507510f0b00010304140c000c44000c003800d44210101013503403000e1442441c003444240c440c00c0c038941c9181c00b43c64180780c8c080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 841293300 1250 841292050 841292149
    0x103120804020a0b0f12010b0c0c010c08071b0302180c04090b060702031006031209030f1e140f0d0305010b07080c0304180f051e0a111c0b 61
    0x807606554929000c00c00400e440d407010707a40c8031804508224150051252450b5921044000246000308881101d00b00c4010102400b9400c009400541c0d00b00100c49060309d54110501c450000102110b0030342d900309082c420241c0d952440c4d072040081550000340c90510904044040c02541e02c0184161420f80305050000708445c0080b81c081401800b404101a61600c1000ca50b400183c2c4281d1215041d6401011104500f00d0407010540f8000000c0c400100750450404058001c00d414429400142c4140d240140d02480d5548529030824122540c00c00c098010f41d2440ad0b201400700308450714036000342403e0000d50714100c00d9400034081e40b04090621140060400c400d01402d1040354060400880c00340c03001041602040f00a10700c42205140c103500c1c00d00491101040c078040c5000a0380c0c5030400000d560359401101010f03103000066090800e20038020b03040c03c40749140302c3c0005142c0c000d200241405544007044070074444500c0003a004056010700c9440303240101c403038881c094149034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 841294550 1250 841293300 841293317
    0x20f0d0f211b091a090f04051602071401080112080f0a0302070b0c090d060b0a0527010e070507030305061c05010b03060c0f1803190308091005010312 66
    0x8001d4403414503148003029403040c80319001e00d4055495100701c2200340b01000401c0118104041a122040c480c092040121070418545040d00c0706400105003070580608186001e03100340340400c0c1540c1080d01c005c4282c2c0740404c3c0007020554108480402001c03564500c0170440c4407040040d14094040c01407009900c030113060300307007031005680440310b2041c078280c005035035a40754a0000300203410050045520090040100e04070300000e0042d201c445000901a00c0000000c1d03440308020040c400a00e604420840c00004403503076580143d0a100031120250025454030316865045404160010400300507030703409010100e0b41c044181e8a20303035410300700003032503403114000604007410b4609045414902141914200b04040d0000c0c16801c07825401c6604070b4071068040c81150098000303d00c0c942e2400d0122240c1d00c90302598040c3e007003c000e0240e841d00d08040c0030007030381e0701c0c4a0340042e00840d0401c4107210650070100201c80c80300c03a94510070803065045549001d000e40e20304605008026121 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 841295800 1250 841294550 841294577
    0xf1b0c0201140c0706021e070e07030e07080712050705060f09060c0f0706030204081005060105090f0409021c02310c120501080606030c0105040302090a02070c0306140f07020f0d 78
    0x140b0840d0000f1400104076003d46568000003591656007003118100c031210310324003802600000405c0c50541d000d0305454003441e501c01c4411001802a03040c1c060707403485407290008030228107000300307406403e0700c5001c2d4442183c3c50811620b414440e61066004542c20001c491481c100c40c0240c81900c4411580d480c0d540d00d580c1e03101850304c45015022105d5008554002524a8241d8001c0c811240c14034241c6201440e5036201c0411200d048400601103401007045014030701d48205100c8613038500a00c0020a007900d03801043ca090010100c0705600b5600361004425840d0070040040c204400100e0740310100e540030200d0340d61040070264074201588540c003181c0c005003e65a0340044141d241001c02c501d40c0c1d10341c0c401d5511783c02920840c0c000d000344c00c0c07102c2040d440380d01141d050702d4001e80f203010b039a161081d0000c0254850700c42a1156070402102000107507150042410440b02003442c500303682011000601007000180c0340f41e05540c02461102200d22020815082101d19420040d2094050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 841297050 1250 841295800 841295837
    0x130314030f21010501021606141c410c12040b0a180c26030c010c030506220903020c041811030d2703150f1b0c0201 51
    0x201c2066508010011500c940810704426054460490302c89808180340d0f41e84005a880b2051080a24600001c500c814000307075002d004901088100d81c03604510f00400442e41c001c007068228603902e0b04988441e900c0480d140d800c1c000c1007010000e0000004405140a40002814072006000c81040e281000040c1e41b000c01c0016201840f0418241c41c20b45d1625143c12803047d6000c641c01d01c6024502481d0b1404640051040d075000395000103025016400c03d01d800c3c0e01d081c0c00d540718560792840d00181003c800414000307007070b0b0040d00e1000440c402d1400e00004d01a01c400800c128041d6154107580040242944211080300c921040001148013990504034144071034104029003181c18005000b131500b00b018034440c403841c0280207007000b013141c0700c1c101602c410000c814071000824900c1300b981200d042005403a00a01e20a0507581c071545d9981d03070001081c80c06000071728141c3c2c1c4c80c1000c0e20340000e540109969030302d0801d89948014030941020304103146581d0702904102e040003039002e04080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 841298300 1250 841297050 841297057
    0x43003090f0b18100b0310020d11040f0608220807030c1410180f020121050f010e0a06230604050904050c10090f0e0a1e0e070b13031403 60
    0x4000720300d0300b41032400348000d200c2450191a12283d900c600c80840c4805038882c42800425040140a00640d001c402186800303900701c840c507040d60568814800c507206030810010070081000103181c400d10380c500000503113064030050594410618180246a44800b40c458002c0c92a500020141d111201402d0031514011688402000354500d0380701015417090010b803c1c40000069602400a0000004040c04d00700140c80c00511401d04032454400543c0110384a40e5960441d03464085404102020b0717005a40013504d5500d090038103400184030001020f90b42030390080c0c403404240f060034648520354140d5051354507501c0c1289900f000d1040d40380d9503001101d004140c001c0a4001c2d500f000e0802d00d8881c9110650280320301030304004010001d000d4030b132480442e185540c12009207071801e4060640b41400a0013589a5070755160581d1000e150584800c041a032006000030b2010301c030390012460030300c050308801400b100c02d01c4102400b2040d4590340e0196a031100c000a010003503a90700358513501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 841299550 1250 841298300 841298303
    0x1180302090612100906020409150b07110d120305041112060109020a140f0306102604031101020a020705011b0c0b090319060b040f0203040521190503043003090f 71
    0x181440741c1c8001b0702c1507131740181c0192803181204101990b19159009001015403069aa51110501c10741010034105c00107402003038000ba00801214605503581580110f0b10b4a00701e0109507078400744010b110348450050000b00f01039030b4039200e005000424030354440d0144500e100366500065402d001071300c00c05003410450340c0d07004c6e404d460344d1949504c0000768108540440c050106080d003203101901c01d0b114200110620398000c01c10002207090082200c400410580a01002c000000c1e04003000348002d0150107903e50140000a042c0b0300018525200020481e01c0025140c10b01c20200c1c61401602c070480e050101c0d0203a03280c0c0c8403404031b40ec19941c140d22007103004400d10780754184006070b0080814030302c0403102089880740c40b22090303040f400190380c09404d607408124025058810210700007640616401d07000c2c04e0049100c81e200340c2048117064500051408400e21017004415024030b060040c440180d000e0046000030710841c101455503401d0101905c7e40b0591050006c040c20088940703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 841300800 1250 841299550 841299583
    0x41d150310140f0c040303051e03010314010f05090d0c1506150201181101030b0d060e0307110301050403080c0703090b0d020c0f061605091305070e01180302090612 72
    0x103849014001d401000340301d10003542c59100b00c0014040720b98a140540c400c1038264100c9041c20300b1601c04407007a402008101d91105000303565891268516005103008601c507030105080c00b501100d0490a480000c031682005c03e0400b02444130300e10b0301261881c4403104510344070050001c1814a40711108100e2212000030b0301e006400302d04201340e030142071f040d040c081d0000d0100c0303d001c8100858130350ac1c4e0140940303403800442400c8c034a5880b0786c2002500050050034404045500d0f02c404048407450b00d134050551f440021900c0030000b0b281070f51100e5a004a008000501c3d00703480c0a440c0d220b005298501d0f00c2c100080740c1d01010b005183c080050000c801c2580e85401300002600007d6101c0c2280350300e540f162a070400e0007050000ba00920907640c4200c120309407082100e069485070040c2c03428542c01240019944ea5025513880b0320743c8224540d039640e403002120800003404044d120040402c0401e114041880580c40d40c081458122030b0076030710700100c071160300038071401c00c0103420b03168060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 841302050 1250 841300800 841300813
    0x1b100903050d0c1205100f0e09030d05071827060b09120307060603060b120a17090a030b0906070305010b0f04061209060c09030201080903120411190f0306050c041d1503 74
    0xc4059420303409040e1504148010021038540310782c23001004045400031a154802c001484520249402c1142c20226a050400c07902c05200824080c64415400c0b81541030084c0749158060181c0d4074409030012040c4004000321401c02c200200c082c031480d40000e010798a10341c0d01c0703460080d040003101c26560704868104045501c3c1e180002c0078107910101d803442907080980700310380510085141143d49501c40d500c43c0c040a40d40d80354403c40d411180b00c05078080560302001021624918140e841040104013030141460411000f03030450307006170026207085005220003820b84040340116000d40d00a0b04019051061050180010703004c0464014000d600701302081e03d885801c03007820300950b4800d890b00c0c1c1840c0d880c0c580b1155640112070650b10364401080100340403c181113a81c0c3c0c2c038801c029000c002e60f00159014180381002661000180000c00d00040061000754880c8e290048140108545410324008030340d000c280b8036007208592041100081113414210760b104108414002e400d4400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 841303300 1250 841302050 841302061
    0xc0b0a0e130603060c031e05060a0b071a01140a0924060206040b07020d02120304050a0501060609090c0801030f110d0b0c0c010609050705031305121b100903050d0c1205 74
    0xd00304070b10003140c190b405c000401000b64000d000e0305070082c4a082d6100d07807006524408a002c1c0c003000d4101500003100100c081018030899008244d2103001d0311602000a0740070880c000340d900e059000d407424804000c503a0010703039a07010400f130842c1d40314507012079050640c030003841c200c030004031218407515410300e000180241c01083c00d0340704078091000701082c1d0759545020b80e1140359491407140181c0025084800d0603003160059908580640d0843d51a50900d070758150031241990400d002080e480d4400f0088624640184484050903290804082d4590341e5500d003041d9040303400400314500f0001c0034000d6126074440180c80354000101101c941864100d02c0c030264844e040c1d42116508120000c0b4112100380900340c003c0c1d11960307030586140e5560340800c83c2030000b4001200c2d14012420011130790350140c0050185080501651310100c3d854003413161a0284014a8601c2035060520320b00c0420703000383c1910350780f50140801141c100c0708007208131007501403950b035507140c103281c4400d000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 841304550 1250 841303300 841303339
    0x6150307030627050f0903040b16021207030212010c020607050319090c0f09020f120709080f07240914040906180b091c0e040b210d0c0c0b0a0e 63
    0x4002c501c1e0f036004201c1900d8003070400341c1d0200100c030310030041d0713004010030440c00d4241d400a080c11034802410aa468440c2e90000d2150740b1511070b403145070f6024180510561801404168224041d034002b0003540d40c40d481e003c0c0d150a0300a00213414004003000064103083d090380c0402c02103811100c00c11490002d440c000040740d55601039240c2c100014070000c00e4010b01e84c802c403440411940c85d41ca0030007451402120500c1c20041070b100030407040050020700d0080420000350075080700c00213450f58a0400c410510b0f041c525502e509001c2c80102c2c02000585c2c0c0000d410030558040400c507500c4814481c001ca0054000ea44004006500d0140e81550000014085034a2248100201d080ca610340d003114640e5502c5030640322410900d4101154017190041c031152404242c0500045101d914400000e600f0308921403d91020f8a010555012140000c0c441d0b01e101c00198140451100103940303410018044500492005000016610480340d028004c01c0d80c1040c002001281001c00908410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 841305800 1250 841304550 841304609
    0x32a03030f0e03040501212306040f140f0a0e120306360604060306091a06191a0f040b04090e0303060609040b040905060a06051206061503070306 64
    0x355074549000340038881c84001000300c1d011120165100c808489800f007070702c4007600c0d00b1440c3c8134009036a20000c000350074801d681052201030a4801808030700d042c0c0706003c16250b1584070389900d2880c1840404594200000d01c54000343e40e1071140b03000340d031042c94507801450052070300c0d0140e114400c4000340700e100440055100e039906a074019548107841c0c40c5040d40060313100307481e44801070400c203980749080d50304400c65109030014404503440743c0d42d489100441303200310425502c0c5a00800c101c021781c034003440d0703482e0010b6050714280c2c1c10414250704902003800707500942c22101c0d02d0002c00340000c220b4030b094683d040851092150384544da142079080307580c4a44100b07014181080d075210090200482640e20030a4041e0140346440d10400c01c00c8010500f03280c0d86540156030303412810100700f0400c14a8400c40c22400d0000e4502d04100c2000003280340c030000d407403090f44103030100580d58450b031005021809003010000e481e6116500144c02421458000c0d089032076034420b0803c00c03440040e000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 841307050 1250 841305800 841305821
    0x908160f0311030f01150f053a0c030c0e060d26130803042303120a020f070b251a072016090b0a0302130f090b070206180a032a0303 58
    0x180d002580d03603203003482402004001c27030140c4460030244244c81020312108000003d024180e20b0704000c0f28507a505400c2a0050b081603c804103044030500c1407403d40b01c8a55009001110300b107403a0038003503a9000c140c048268a0748180300003080e0b8580c01420342c50654921403108000c02c060192107040b613aa0701d1b0003911410307082c40303a00c07031051183c540050b110380028076000e030184c1a000040c070100302042d03001c600400300318881c0c101000004a03090210360090455010300700c0c0d840e441c500500807400b84140c0c218039a120320440e0000040c4100200d001454602404105155607805040da415203c00b0f042c0c1124151200701c002d041400031030441541802d81400d00714182c1c81c0c584003030441d0422042c264000c0c562500620144c5030040208040306507903000801c04403003000300e0406a601500c81250460062002e1204042c0c0500ec40da034086030000381d000c030340c0b00202181c0c3e030340e4807019a000e82030000d0500c00c20b11170f10341c4c0d503044c0116010980d0466402c40c000d180003070050400000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 841308300 1250 841307050 841307069
    0xf170a020c010b09090d052a07030516081905010b030307050105040c0603090809040e0304150c02100212120a112101050616060209130c0908160f0311030f0115 70
    0xa020510b449413415000d003404d40000d240d54881c01900340c910b40e0101c080111610302407020030492070410741c42d005110107030402404620307140d841c24038980362005020001c0000c11482c24468035800246001e14a0004480303020740203000d0601d14010000390034510b81601002990b001402415004540104d108281c81d400881e5190801c808903541410024200c0e00d00b0496504035180542204840c1503000c070030740789029134400304020028030b48a01d41303010130486607000007036140c115220610102680060260800903401801701071284140c0d03401c10711841d2000c40c141c4841e95005031580030300c46034000d41d1010f00c03502070000e01451010703020701c0041d800b00104050808100b526801d46103402c0c3d02003074150320350741d01c07000e0340000800d035400c01402d41c0c000c2c00d03002c10ba00501c802e6407034a4440016450a101420b0b08041b2aa08401c001d40080501040700d44a040c0d001005c60340c21100045154014100280c02e100034001090728940c240040c400607200b11030b045c141201d440c5c08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 841309550 1250 841308300 841308311
    0xa08060f09030403080316110f0c03150705030c0d0e010603060504051902090c18090c04080708070b0a030b06090a0b03060109050108060f0409052104060f030b0d030f170a020c01 78
    0x2140d241e82e80c812400000d10100c000d001159600d0403d09241003018414204003094241c1100710515060200034425800e51048007402d0b21418188060412541d041031045400c1c50041e402038a20b110190440d820180006255807007400c0c140c0c4691406401c8000a01025980e4108030010f88000c1d10142c84c58026030b022406140071941c40c2680c05580601070060325503c880b0146a6a001003007645030a0607003a20f0350505d5500d5003401c0340b082c00c07500e42c010b071900c0c204254645040703001e420100290703118010500c1001c11003c01d40340350202528006c215040e0340c1001c107902d4081c202a01da000000ea8101180007403002c00654441d01c0700780e8400805507a10401144c0500054440d81d4100d44041c80c03d15031820203030810490203021304122100002c100c40b600d02800050020035408800204050140c00c0d80b080001030b0603030551400740058040400064405540c500d0001c0c00e200c2480c032002c1ca12030240c0e00740850f00300c460714103491038500074400f8806540102c003603040c10352900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 841310800 1250 841309550 841309561
    0x3020109080102031905180f0d0e030d09121a130201020c04020403020a140d020603040302030a14040e190f15051809030712050706051305060f070221090a08060f 71
    0x14400e0b0b078400c2036161405c890084640c000403008040207000b038145000c1b0b000d030111160b03001f048000d003884029001005107005030074000700003038032400103036110350049264421129031008001050350303108074803010486818540107011056550410070700404600401c030000c0c3c4014100300406000703070261000e0054202c108000c034895801700a501c404650320034800d14180190b0300100d050050082c1414425a0b00001c0441d00115801c42c0144e1002654400e1590f000112002261320900c1c01401c280c2020501400c0b14030044c1000e4075005050f000045024194010303502000044004009002020441542c008164003409000d0003020341521041801169020312400c401001b85041c0b45c0b4540d140b44800b110000ea1b1000c1060501c49034002c50020b00c68280980c0151001c03040030800c03854a182054802014503000c0ca2200c010403201c0d42d008a00041c0f902440e9032000c0340041e03600b9002c0c40302d000352417009400a03048100822084000282176004960051580d400f642c8c92 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 841312050 1250 841310800 841310803
    0xf07020706050403171e070c08011a040b01020a120c061a150a02010b0a09050403030c0c02010203030109110d05070908100c02070e07031d010b0f0604050f010e0d1b0302010908 77
    0x54071403100082e8041004101240460084003c44000c0d405103070300d4071942c91041c2ca0344c20608940d039041180e00048410802440700c040c080241402402030160055002c030000529100c0702900d03001d6501ea050407881c80e8801e00500e10f406503c1001740d00c9408541d28010032210082908803015490702e055500749020340030044044520080482e000441842500501a04000d04039815592a564141d6080d92140120b00141604410005880c6420308008080c1e81ca0b1110400621001711139900150341e003c81124151003401d82c1c003044a1090111000951080b0201041103d00d0a018480f8050b4031410f8481110480ca00b03c0340c0241c00c4484801c1110042180d9801603840750360b0030042c100444d598954409000e0070000f030140c030f49101c3e04443c48211602c80840ba50348071942402c2d80741c1410141e01c1700304192840d508085c14003000ca100c08103100e603094107202e1190642e0a450f550b440d80c402d082a480100403403090181c403186000310907180030880c0401c01801000c58803500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 841313300 1250 841312050 841312063
    0xc0d0305042102030409091a07030b0a0509091509030c0606120a11060c0114043309080f040f140405090c040b03161d0a1107120302070b010b030f0702 66
    0x104030824256000c01c0070b0185a1140811100505600041c0030000d0070300301c01c2c130415071494040c4880c0140704400c54500b404550006003588141480e00c980a100c6880300c8a46409548058031481207030307114804505e05d40a40c40c1060041543d61208101e848900400580114103490003100c03400e0700c0c0c56007044154881c3c140000340d607501c50320b031000100b09840000350b001880580400d00c1c1c2000c51103d5400c4d55110740d8840000302001c4103101c10040702e0721804292840c0c21b80c1d1500c01c03403420000700311240102d900105a941d290136410092041d00f404440c52000f110000d02d54a555502c040d01e000e06480c4102049500c06030000d001600701405800e100c0c2c5110006420594010000c010050406440d0540c0620402440e400444440d1038144043c1998842d81c0c0300c0e440c582d440b140400078000700400e0901c1d0802a10b10701c1407115200741d40d58290b10614405a001440c20120024002c07400c018080c240c0070000090181300782c030000c500495191620707201c2952828810390b0b8844 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 841314550 1250 841313300 841313303
    0x6021905090d06200301030812150d14030906071b0e0c03040609051507030204051203070503160f15060e0a0603030206071101110d0209011211030601030911150c0d030504 75
    0x208200310b5100050826401422504040300041e021003070031801368540c1d84c00981003142d1014000500e000e5a41c3d91000c0d9591112614030300d44100489032021910069070710720001c2c0310083d405e8a5030b09100e010310a035400c01101910306038640c1c005044c5000d00304030603615500414500f4002051032200ba0780c000b03100751060b103501403558440d5075a410050038000001d8a95014003030140c0044a1403100f0035000f15000d507000340c0c4840c01e00e8108007482c1e01200b81520359a004110072030005401005680894029841c1a13180401c00e040c905000442d60744010246801001c102d95810a13541c86841a103088201c1801c166444815000481700f16010140161b13001000045605114615040c01c01142da00046094410120a40038a4101540c001c00c0183c011505001550348048480c01d00c0308051001d118039200296441040c1c03001800f420b04140d00d6500320000d0060100c1405040741024000e580c61000c6000011441d0b04004940f0300e103402115400c1402d00e01c17038001c1d1400f40317 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 841315800 1250 841314550 841314559
    0x70c06060e13140a1101110c0910180506061b241e01350f06010e130b010b0c19052119030b0f030d02010606030f0b0306010509061c110112050712270602190509 70
    0x3200f040b00340030303402c82205043f006441a0648501c04040c000c840c0b5450200700c518111550070b1185200801ca080081d52600036805480100864645480f95260301580300580314400d034860b852103216070b9030380190b660003480f40c2060204a01000107030345049520509042d041c41d12024011602445003910291113911401d005112407500c030001000fa10001c40202c454031078520b41ca14400c072034030040683c2c00350444006a0201d10ba00c10802500e8800483c58901e00002000103185490b2142005000c040d41c600341c4e00016101c42ca00c404006000400701e42c01002013500082c060041d42c025440004d0400050300080910360040b20b1103030800030068001603081606209001030024100c6600c030140c40c41e02003c1941081c4001140750140d40b009401c504207000142a00005803010301d2024900410000307029400183c81c90450908000880c0c01d100c01000e030820403c60001049001038003100c0d100c100728041e402094011118080345190340c095800030350b8540141108546c22 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 841317050 1250 841315800 841315807
    0x31b180902010c0b06190b04050a090b010815061e190203091c0f022112090d0803042120010506010206070c06060e13140a1101110c091018050606 64
    0x13242501c02030340c0500050207421118440340c2015903c1002c039404800b504900040600c881d04100714843c024001006040c07180c0811f0341d0009110100090160701c15041c864170340001541d40c002110038040d405004403280408100d000d880700e600000160946140103115440b8150004c4151004140001c04144402e0a904002da002c1c00c02000100c2c4d0303402001200b81c00582c1cad054441c1502c1e000e0318111403040189109401c0c90038910f40389920158000348403602c0342d9680e080003c00d420ba8011003640d1241c94a1402d074641c400d0b001c0d91900500602d01001112980c01031480300460300303d00c01c5180551040c0b001074200e490590b84607005802500004403101c0c042c01841c0d40840c441d41c00002c645564441031002c620b82640c0b00d0020390a01c4d088101803081ca030000d01040040103010303140042c46903072a180380e440c5001c2d00606114240071a000140c0080c040e0040f100c00c050001c64491900321b2400340380c800c4600a02d000c040100503c0320038001c42d44034031403040300c0c041c4c0700514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 841318300 1250 841317050 841317053
    0x60610031104081507140c0a032d1d1e01031e110d06090e0d031a04140f07050406050d0225150501091a090709031b180902010c 56
    0x750001003030480c000c4000700710000f0040420810001c90107099000f61559040444004242c102507003281c0700c481c40300713000001e54540b01280700d035621039040c1082000c0c090503540060718502c413131a030000c1084c0c0303034501d9000c060303086410f02e90401c2541c6070b2078281074110000c00000d40e241124001d025060550034550a5020b5807011001e4400c403103640340005502e542c0807044d603104840c5943d0402010580070346216503401000702030b241d065030500804940500d02551203a08028683c101912585c9502c0600d035801d56007640110f01030000d00c1007158001c0c0705210604190b61080d02e03c001c810000b40140c0c82201520141c81699031401d00d420041100c15000e504001c0b0402a11042250b464146078015040c5010040c8500e2500280c0000080e0340320032140164000344a6a040001c034024144034804c1320302004500b112040d045444e118401c40368118190401046090074052000411407a549508101d0703a640c1030a0300c072865450032200645400880007804204c000e2000700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 841319550 1250 841318300 841318307
    0x302030909100e10090506012a03020703081c11070302060402042a02061f0f15140c010e010c0e0a05090c1e22180515030313050306131e0609050312011502060610 71
    0x740143c002c0c03044334413840c1c803a161a1040e41c0300e803a080b814500c02851440701c010050061898481542c2c10590400b84291130194640034001c1c0000d10544e5100a68a0b07200100800146405a140d4285810300300300c0b1406980d41c0f005079074246140e41010003079100120b4042946054070540d0030085090b61400342e446402000e940803100c00d00c0441901c00c81e880e1108006001c140c032800740007182c1044180000703421207007140c000500b00036100004540315100d6044402c21130740c0a50361242c0943c1d80c0c10540d101d50140a0300e12800348400d0f034003904403242034400740039518003022400d8200c6541425214442050b4844c01130803168a04401450724482c0c0c0c091036000c0c00b15213a80b0340c0d108480c400a41507520005035007041d80084401130001d810108070880e0300c044c1c82c50107080180300703644401030f100a10b481440c900c41c0500b80d00c0d03000c0003078036004200c4040e03100c002c49072942c1e240004421102800d00035441d4203984400c5000e1828070000b010f50050001a20b0400c42902d005001c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 841320800 1250 841319550 841319627
    0x30907030c060c020f0409020f130207120306261c0e13202713050106050c070f08060c09011e030f0b030d0e19260106050d0302030909100e1009050601 66
    0x1a906d02f40d00740401e5001ca40382d94a000595509540c0c002041803c000301c09103c076900000c42000c50910003540305000c440068600740100b210000001040340c50342040b210780c2811090790340c2104856002155203401a08041800076400c11250018000452084110702580015000c8400c0d01015400200400c03a002c0d5403010010300043c03101c0c03803100c0308201134503820781c40b51001803000500b190f10100d040c003085010700000c91010840500e000c105617079404008e091440440000506000319030b000381d00c020090240991100300c8404c40b50406401804441040360700301e401c101c104040c529000c40d003685d1003495502d5446090b050101400301c98600c450604a120381510400300700031503031005c10207400381d03090000e80752540064246400d4990941c043c0e0702921004c0c00500010b07402000741c2d00750010641d07401c0349a03969007880c1500781c50544d10503a6031140c03010501035552924803000050b107807003078810f200710303111480112200d50003021b20501d060452000f10a4848101018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 841322050 1250 841320800 841320829
    0x30105010507030e10110d0f090b090a170d0207060813061a0303070b040204230106050d1b0c02010306050a0f030206030402130507020304170307080a05030907030c060c020f0409020f 80
    0x2807281d045038140801d085d5003803002420040381d9210f004040c4070300c08100e20b004000152415003071402040101070161415405111201c800100d03400c64644c841c01d4004004280c03114001403003041058481d40c441094585420050180000c00302d1480e001b11017083c040c6100b00c0383c03404061071644a890043c41c0b640141640036201d402c3e5011666402c102601d065030146080380c48509081c41040111144031481c0c0e0740e01400c40001c0d180d8240070f511020704641031410050b50720840c02c204000142001c01444500115055103c2e80007907100c0c00b80ca0300b2a200385c03004c0000507100c3e01000702e181d807144108840c800f03900c0e0041c030041c00c000020f1600984042c10241071407100321040d50541d0000c031080001a880424204280040d110700c80001100d4039000c1c52070007045841d840c07510300c03515800b10b0500100101240e00d50008024510045030445040c142030f549900004007070700c0221005910440a07024041040c3c5403602c1030354041c07503000b03180590040259040c011407001c0c2100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 841323300 1250 841322050 841322057
    0x2210c1f0810030602030c13051c0201050a0309061b170c030106030e03040306051e0c090904021c21091725090f0c0914130e030c16092003010501050703 67
    0x20b0000002e10180007450090080d82402c98940f00d81d10400aa031403059401a0720545081c04c10100d0f090500c003031080c5554083c80d00c0c5a80300301410068001d40031100b80182070b14a0050308140f014800394003100040c01070f0b650b41c1012100381c020201491801d40d1943d000c000108010031102c0d00a50002030418040001d82c0d007010f60725200d00c021114201c8801070b01202d1a240b00411000082d4000c3c3e01039911070106050404140100303241e4180140005d014003907100400c040200c05003c4041d00e140e10490200c00c1e2522121840b6990144081c0103010881e540fa01080140f07499482c0c00089811100401d4a0704c0d000002c1106511003013154003200c44400004200082e003802490f2240e40300b8a00401c80521011004181e000740d80c1c00159144040b400c40c03c502c0c2c2c0c0720040c3c000c010003461004200c84080b4620700c1e0841c41841620a100d01c5041d10b852020240c4c152507400f110002901007000d046001d0343c0300c1881080c61101280c401007080140b003650b00940241560601924 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 841324550 1250 841323300 841323331
    0x50f13030905012708031b03070b010302040f1409250501020a080d0213090b0319031b0606081b090702030301050a17070504020d1a0f181302210c1f08 66
    0x6005090144d466005040a90000108840b500b030744203240050440d6200700651805450303403101801c000040c0002032041d40c66900ca08001e09460300907140e04080828108082d08210010b03590322542210600c003100d003014250081242c02c12021011680c045e00500390811441d920907009609c40445440c0c003903800d001c05130305110300d00c80007400b8101200001413101c14040405141a040d0700700d1070003c0800201400000781d0013a542380503030f0214156412140b02d140390030b01c06040c164004203061b104400424103260603800c070912414005031001e004944800400326201d00c800d002d41ea42080c0c0c00c0c48200005000010840c2c2d80030703441c40c1521400f548400000381030364045c8054901088e05d4810300700f07050101c500c40e2421090200c030410007111001d00030500c21045482e600d0018400e25000510000c0c40602c82c03150581e0080105520803214a840c51503011901030a0120303100c0ca41c80b400141c00c291005d9102c00042c00403000c6c0c0d900c0188030841d80c18100401c80ea65106258 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 841325800 1250 841324550 841324607
    0xa140403140604050f030f18040608030d0207140a12050a0201150b1207090f0b0906131512050c030609130213061707030f020108040f05060109050f1303090501 70
    0x4a4806158035106000c0d003164209070030961725040d0354030001851a0800c20807400c0c20560300301110303e40d13190420214034000b906000034008001c9503008001900000406034103078186c980c0203100d51407042c841c0030340d4000001c450580e10308007090000c0158118000500c0030b0360040000c2c0960030440e2002181e842c80c0e1481d45400704d5055841076034017010109852070ec103070701c2409990b03001080d4074004024926260703c0310f0600ca072130310880710480c100086540d1151100001c4a071031014046810118543c0d07207010350032226064402c6400240c07804d00040d80e01441e8018540242440f6072828110384403c400c1102c0528043c12000882c3d400d001c030340d03005850703543c015090300820140000c4e03050719000410035a4032114544040c3ca8109180c00d100042c502d001040b00300f50286400030442e9183d00d080f121505402c20301400500c54440000754440d8250003423441070715000b400d0a01600c5031410520700780c405910090200700300c0c5405106a521840521a1000390203001440d8086075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 841327050 1250 841325800 841325813
    0x2030c1602121015060f0e060c190c0303170708041209120c05011d011d0109031704080c09060915013e070315020d020f0301060507110301110a140403 66
    0x240d100d0f00316240c0d01c40b098942d418820000201c020302003401c000300c509820130310040400c4951781445104000218039050001c008000d0b1601550038480703903080c580714905118684651901c021070004004a41c98550500814013303402403219888880003515983c0c2c83c00c3c45e1900b00001e201c10080590000503442d07480115024429001e1950308030001d081000060040d880202c800c10400c1c0740850740d4019981c03208802401110042c07180f1185104100103e4190595620103040c0300100071f001100e6912a500504c04c071180003040303c1013810704038244118800210384055100c0d0040c0d000400560b40341180c800b202c20b0500d041049500c80f940c040390040006842000120100410103501100480960342c01d01441030040068a107940c0c0c400c030115204050702e14115801040300d4040c1e0011f034069604910400b00d4164481d84c490030000e01c1078004903c04d0340c103290503105611075814180f1a4207182290b440303005150003a0301600f540c1d240390121b40142410f90410000010805 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 841328300 1250 841327050 841327063
    0x60e010c02100c060e010507050a03020309073210090b0306010315080a02030705041a1905040501030605090d0c080a0c022707110c011b06091a0a0e0102030c160212 72
    0x20b06031901c0c00207491504007401100c02032060084a80e24090034405825001401e44821464601d4003603a2503940006003403c042884e40035000007100311491540045005000c04030556802c00e0407482c18003a0010420090065401200480d81c28070b4140160100c00c0300942e030002043c140400c2e400b1840181181103003c941c48080240c100c140d0002c110329041c4503007030062400b12424000783d0b4440c1d4101e1030380002604510f00c9069008541c1900c000d001000d6001000300030002c202540e50b1b418420094078040701c9a0541d4056007900b0704065000b40d00c03101e20150407480703990070841c0500e01940d10302c0840300d080c0d034003a060001508903182d00341c10318180081515548c1003035040002c000313440200c10076158021504003070481c0e00d19991020030f0b40c0c10104015120500e00b01d8600308000140100d007c01b4101d10950820a841d006416030a5402176901d00010480001c210400600300c0c00240d0740420101810000105520058407046103403900090210401c028030701c0d04145000e6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 841329550 1250 841328300 841328329
    0x80c1207230c0d02120d02070f0b090a06060b12010b0d09080f0901090501050f0a050327011b05071a0621070e0f0f040f0507051e2404060e010c02 64
    0x1c400070b00c1d1602c2500078007943d0065030042c001803820b400300046480c0503026481218040e1a8003040c040c040c01010b51019035201d80010030700e102410445003140e29594589001d807085812300340009882d500039811170300c00d2048402c1d40c400d280d080c400f06030020f030b00c030303184521585864440782000701d9010402071001001c1c80002d10b40e0348900f540058030b98042c980c4001c3c14807100380001101450000202e40c10009246081c5560356a03214a0321550084011100500c03440340000d0201088150304c244000001d803191140c101c0c40d02c840c1150f1500c203507500105034181c00c140d080b015171044d051086d0000d00082c03048140300c42e0203001c4e04210603251104080d41d40180d004010840a0448030754000a001e01c0801541c600800c110310680e1010304010b090041f00410032040c024240b14040c003400004210094540c6c400b180071842d0020302200901c41c041003281200381d1804081c50401c84048540703200d04061520001b5280c8080c07440d03803103040c00348080c904801651181d01c09070180b03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 841330800 1250 841329550 841329617
    0x30230071d07080105030304031203110c0d0905032d03070b040b102108090f0301020f0913090201020a0f06020409020a03051503120913061203030207030807080c1207 73
    0x40c079650810075211002402007014499400c0061203d92008400c94041d41c0e001a8080c4200650100450007801320380030761000480003141d02c902c5054049032010090b94980e6500d1106500c400030141c8610030202002c00182100340070465042c101d5030070200a19000064900341901c540364801c03901012030b82115000d03080020001003600203042c006c00740403074042100259a07094280d002150b040700e005010310201140c00385841d911541400400c60001e1300039500c500798000c0d5404541c000683c00d070b22802100001154103c01d9228811106030140e00a010240140d29444200f60b0305100035101d031602004041140c80e0380340001c10140c0031664000540746030901541d40b000070351448072442500b145e460144843e40000603912140002c80760b505003a03001c800a8001000b50340d102103201c02c41400c2000503d9019800780038118040d48941c191030340c2d202da041711440d20803a920038940c8820b0110009007600d001d030707a030b62102c0b441c10314000100790b4041d140042d090080001216 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 841332050 1250 841330800 841330829
    0x12010219080103023615031b040b010c0c2903070903151a1207080a0c03110a080304030602030402010302041d160f080c0d060b0a052203023007 63
    0x860809100001d8a003000b15641454140c0d0f504104001d40030170140b54a06800d02804a910750910302800c002d07116008044898501041c030f070000700e0040c1640041c1c4954902501c0718460350103040b8140b205a8002c00ca0901141031185081e51000a08006c1c0d414140004e21000700c141103034011806041e043d00d071620007520710325103030140d003049894002003903041c4140e02040802e5626141c04024080318210322101420100625043c0c4990006000e0b1203601c1c0e50300309001040c500034094ac0d004000c0c200243c1c3c1072134240b0452149a1040c420315610400041000c10095030103950010310524001d4641745e5585c01015050401c130003800700224807241440307417001c643c601e4001c817130300329003001d040751843c100014201c0d480003404040d0032030001850b0300651206600000140284c00d810544070040c96030001c2c1280c01c42c5412040f0500581c814501000d00364240317508030f9500403d030070001191841c42011400ba640030083c91400309801c2c920100d0b1042c81064050b10517124840c2c072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 841333300 1250 841332050 841332053
    0x4230405060612270109111215010e040807080d0f0506040e150402120105010e04060c0503040206040306020706110a030b04060e0402090f0c090a12060f11030612010219080103 77
    0x1190009070645100d00d40c1041200c40754a00603550030742c0b10704a80340c0a000c4403803500f00c0b03442500c1040c50848095182880c22410400804410601d2035402d64a1115940d84240074a40e00c140002020440741c80e2800108454510010440d038040e01c81c00c06c3c3d42c2800c1d1103680d0140140c0141c841c1d54042c03903d580c1d1943c0c602e203061150b01d5016400311000c2c4102a548680036480d40c941140810310408050f000900b55101c0203115681c0c050000003c000ba5030355400318144288003a5001c0340c1032810820f09980c00b500c986d00345d0307016540003092145050700d182d6034800254407084003183d200d5110711543d0401c281c814040e005c02c501e00c3d2404503260301c2030000c020450342c0d19040040c42e244500f040c130002d41c80c1e03801c5d030301d60201600741d610a086e150b048155106020342c22210f60701c03071100c29011a6103104004c0380c2c1c000d07030302c02ca10a02c100c460705000e1038243c441122268007425001e000146061800c01d00c001907080c0607200042c070f412012036410112207070000002001c03070b004400410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 841334550 1250 841333300 841333309
    0x5030609070810140f06070b040c081218010c0f0b060a0806040b0c0703021c050403030908030c0c01030f180602040e010e161d030f0604030906031509110423 69
    0x603801141454000b030680b4000021440e42607441c09210a014000a4a44400d44500c1c08440b01c030040203002c81d849500b00d01e410119540c084804a8100066060000b280000000c07540050703a101c2a0040c246071000d054120001c180c03c88103410415040c800c0710110301501400e075200ea00580409405141c40000c1c030a4040300d55000034055800380c0300300310101c0c0a9041281d0040c070000080c0d0390300d100606040789003420348000140100d10b1044242d0500b038000c4010310483e8400c5d01c4410103a030f554000c89403a03000b440c12075580b64100c100484440c1d0b101e94411204201602c40020f604080c005407201000080d0704d0480c3c0b241d9002805010501050300c500d40100800140c0c00c1e00d92901c14070081201460383d90b0f0b142807040142285510010344826001012009811241c6010040c03012f156136800940d01a0041000d2002c00b01d917891003070140169030081d201080e014140b401c0402001407141e5000300e68250b00c2030001081180e504c0b680800464820305042e12005100030801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 841335800 1250 841334550 841334569
    0x5091e04021309031224150509060c0105040512030106020a121e0302040914010b0d0b0303090607110406080d0507140f06070504030302070f050d0f331b020604140319050306 76
    0x111b100306403080ea2040246443c0c1c10a20981e00f00070410008444c2022090341c03140103e1040700d522160205402d40454815400035115900400460b6140705002808003070a210a00400717005810804101c004518641c05040410410f0316048001090200c00c10407204e149900c80340008e0f40000d420841c407982c1d8081c013400908400c641c90381d694507095004074540300b88a12004020b032903d5160340c490b607092096078007052010f40b021b030381e40c2c9180c07401d68009035490302541d200341d00d0480040740e150000034507081d001d06a601c959140014a4030303102907410135940c280603280700d14607a1901c200d0007400111b001d42c0c480d03203403e034481e030442c980070307080c601c194000301400c00c070800041007107546507954441d4050b08881e0406481c1e5440c101843e00c07550030164040003035030f5001c0380030a001c00042307182901d400441c8104070001c0500d00201801d07026100c1c0800603842080810040b40d2034110f401d110387c101c5011030703203407113840c94020720300701d0580c52110003141c808401c00c80c04c2c2c10000c021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 841337050 1250 841335800 841335821
    0x7051b100614060f0a08040f201207051c02040b100929040603110c0604140d0201140703051e010902030106200a031202040b040e060a05091e040213090312 68
    0x250f504200e100100510f0038020f680d0f01004000f2600041403d015a944844800075048000755801051311a80001c010461102983c042c1c45411a041ca14240109850b000d8801c02410030b540c070300071a6a100303c00300082d2030907a4429034031a0307101c4180d5600d040f0040e9401c3e4a40f07407030513001c1c607050654007220324101c0e061151103a0450803c1c403c500c080c04440a60710b0600740060000d0604007050154001c1120b8029184520300a000600081002d00c80b078001850302240c1c125203003d41c0803800d13030314045250320a6075800c0020503880e074000d07007083d5403002c0200c50200c0c512004840b00407016400f0f0384a20b0440b5400001406400c6d4444880882c0c08061010204003414040c00b850350b0b20a11a00901006501e00d08030b882284640c0468005095144502d0384940c1c80e5890b00014500641e203091150021160004079070400c500014824031140c00f050340481d501031040307046e0540042c02242e01810011902010400390b104000c2d62900a0b80d81042140d00c0d840b64508903600180c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 841338300 1250 841337050 841337059
    0x30e06011d160c0305030c07050d0306090e07030b151c0f030801050405041104110910020f16031703090309060705060a0c051e18030114070f0c020907051b100614 71
    0x21005001c0e0b00f0800c41c3c506103516250107540e0b0b9640806032125070044050041407402030310445540d0991541107002900e002c40c40070082c0704008113600303a640d2264400200b8500c444030000d0710024081c0c82c445184000a011500380101c1c1d80d800c01c2c86142e10240890303c4408031484c010034150301901035805400180c90810284c24130f07460f1418520381c040c80c1d982c0b0450b12410754203206110300301510f841a101030003040260100b0385c1c020352298881e0740380203114841c650480924006010050080f282c000360185034210b082005610164002001e5040c103101c02c0000a0b11340c0c88007002842841d01400180ca13203801d091003808265000c0c00d1018041183c00c1c49072421107900d41c111100142e03140301d4015a15101741c00c0d0907488441c8801c0040e495442d20301106a2400400101403080001e0f5031031448080d800d032801d031040d010f115001f03900400070500280310301d0700402c0107001d400c580c00d0804e4110303007103140864030f030400500301d10343e20a413036600410a0030440850301c50101c10440c1e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 841339550 1250 841338300 841338331
    0x20d2c0a2004090203070602030406030e030f0415090503030a0c050d090e060d02010903140f0607091809151a0f06090d2307080d2706050a030e06011d 66
    0x31511003034801d241580d500060442180100c003a51607a0103520b007a94081d040d900880c1c1d0304c103000307500d83c4c00c144510400320b03040403c02c511607034002c0308584a00000e01039650a00b410000c203000c0c41141c1d00b01820174060903000102e01550200041c00c829580d40d40c4800030400303a485c2481c2040e0051414030103020704e0450038444c80c5901d41540d80e00c4402541d0703020b440741e4a0300040b079001324554409001d20060f14007070302c00b8082c0450b0181e008222201140c2854139200d804540c1d1071100e2151030300c0d550920840d1201c0c00240d07080100c085018880c40898600c0110340703a011030320b60003401c1220884800c605222801d2440440c0f502d24800c6a003242001c03130170004074021400000e00100060f445442c1300f04034a0307a80400e4190403600d1000c0b581001e448501e0640d85c0c581025141c00171502401403284a50300d8102d0440318403026a00d9030303400b18680201542e850b040500040f042c16206c035468039291808000d0300380204280c4106403040311052a03282455580a0200c010f044204c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 841340800 1250 841339550 841339553
    0x1701050f01061202070212030a0e010807020303010608040c05030d0c0203072106110f030a0606080609010b0a0e030c1002150f09060c070807060204031a0105060406020c0108060301020d2c0a 83
    0x40e801d045403001d0034565007500d40540008000c0c8500d14009601c180320741d900d440d08450000c003078061000c1f5a211b80202c50031070030040d03510060031100240168010401480b005215211460304944113142c01d0749034544a030002418054070038a81c00020340c840400000358a010010600185070000402a8141560400c01c11864010102800050305d0304e01503c0000c52101c01c071410303003000080c42d0ba142d0500c411514081c240760b100e0b210018003054080b9130039140040c070050494840c0c449491620100d0601980d40360f060040707040e03050103110002081511070743d02c3c0b0004d01d04590b019200c0709808680041a00901404c40a07004086c4001c0103811140042e003660800c1d036194919440b500c107072414290a105a4100800da907001040010401506a506009200c40000d040c4203d81c1c0760402d110f443d005902c5107030010703030140101c8506940101011a04400301800151818220100c044145e4002240740b00a4143c0a103003100e8104408003002c1c0e1000035000507146000d00d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 841342050 1250 841340800 841340821
    0x90e0106120e0c06030c0301031a07170604090b09150c0a0f111f09030806010f1b020105070c060f020f0d0512070c060e07060e0103060806040b0c070813170105 70
    0x80014408401d40d071a1904903480c0d10400c0802e0100000604455a03890440e4441805d50400e110032200e0302219040c0c00914075400000500c0751400750744401d044102c09041101c18003000d00003076001541c2d880b07040d02150040751540d11407000c000081521207252043d80e540d0050007804005216028802e00d01351950003900714281101c4c901c1c3c41003120a11040f41c0f400c000c1d00d41c02001e0009022034104265110075009071318054040c1d103c0c7d419a55404006480a48148410304005400c052490720490084000300b17103424010714000d8100046641c0354030b030404c1c091300003401180e082843c0a00090703040020f0029855110060b00000640c2c21000e4464006c1c62059900d0304e0590780041c15651191282810158000341e013808082e020802c82a280c4c00300d8042c8500003a1241800095035000e40035044c212803220000344126070320340d01e901c54010780c040c00040e240102000104045503440020708010319642c0c41858810b03140c045905070503100051290303080e904210800612415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 841343300 1250 841342050 841342067
    0x1401060809071e030b090f030307200c310905150112031205060103090816120507170702030f07030c05012d030f020918060406050a0807060f1b080307090e0106 70
    0x380301000c030400307403201b1506a007003d550741c540700c00510000c020031107840c0c1d1204404880d402c0050000d01d00300e944000003602d403640c8020317064020041c2155050781c06903040405041801c800d0406450400741d54a00050f1010402c0c00c3d0782a5100e00c3c6100c21031303004050b041d80100a40000880000c0546c0d801625101034407030704164542d40d41001905903402500507600055004e200c1c199692a00c0d8403107044803101c2c500035140c8030303031121001610600940231038a400fa004204541080781c03030703804e41c0960b51000304100d0b0980950b510105000c002000032101443c400c16100040606260004203020750502890803c0003100300000d54030311510307194900010213450089005000d000e4600c01a100385030b0166040340046800c05250105aa200c2c0c2c0244801c46041c002540c3c6c41d010032803c00725a001c0c0c00800e801c07004081003000d01940e54942604003e0a08000140b100600354600c0101041c050300c40d00400400c101c41c10390300410320000b901d041c050f620749550400030018003014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 841344550 1250 841343300 841343303
    0x40513060501020a1518050607030b030c030c1905060c070e090a0201080f1005120f0f0133050a0b0903010f0c02072607120312140a0506041401060809071e03 69
    0x1560398a611064a01e143c204c2d0003240031100386c49403990001d19000b592150102c0f111000203250100c48042c524010601001a403030080040900d00306000812150b0910907054019141e006d02c0e00043d1a12000b014000c090182d0014141c514500a00302023000f4008240c401682c01c584c19000c0117070303013001500b03401502c90444402036984070981000c41c03ca280d00544c1e4800c48040713141c40030617000500400288841e03001d4034a84022103900704d090b61212041d84410403600c2000042c02404481b0f07650780855059070801c04d255850010901140464004007001c00d400030343c0c445641002d00503036032a02101003040041188080000b0344455050051a00704003a480c0340764500d610908408003054018015503200c0c40c0e81f07031543d05140c5135121086000c904840d600b82a1152035202c2c0202108680900300c0c0c007680c80c5440c03c002898000c0c107880d4055900d0040d072041e40c104240b81806030241e41ca0701303403a900f030100c0305525105460f488039040000c011104180ca031304565001d002c89 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 841345800 1250 841344550 841344563
    0x150f060e0a08240a1e051f030b040305221d0601110607080c070b3d050904060609050a0506011806090b07061d07090c030b01020d11030904090305040513060501020a 72
    0x2a191070142c4070181030032422051000e04505c0c01d04c04102103075480140aa05084460411104a10052141c082d001d202c050541a40040044d0200340940003e101040010301804e2145011401d41850f404145d04007044c0400d807100d200510001900d405030704030000f401e24507403885407251541d0361508000d00900812031003102003190350300d652085c7c80c07013a60301a0010556240c0410440c80040b1007074550101400b0700a6161b0311503042c00304414080d501e401f0201f9102d42401c040c4008010b005d8000c0b10315917914a40040c005002e440b403607002c3c82c140080860035082050005010a5150000c0c04011030b101500b045160f41008083c4200d40315a04060b0b10703048941409402458001840d9070a05540f00200299200c04981c4909907100b441081200c688400c500305d04580c6245c1b2402d0260340908200c100c00ca0052410703070308a510040c2100c0c1350008a9010030140c50361164100d0200d00003040074002842c24084d2000c40241c08482004410316000c0000d5440451b0100907250 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 841347050 1250 841345800 841345873
    0xe0d0509031f0f02120f0c090102030417070b0f0c1209130518010e06091203160c060905030417100c091a1303030806121c03150f060e0a08 61
    0x46666034009280c900001c00d4219207801310840e004c4170700c034030458400016107001400100364141e41070a0b580f0010b410f80c000c44c00c007402c242900c0411042c044981c0700a100c0c40c20700140400004000340701d003c01450f40030b615865a01200c901d080c03900203c14049407024080da030f030181c680c0e10340c482954540d40c0c008902da4035100c56050740d00b0600e446880c129402c02451039403500b4001900f0780508001e0b0116035160100802da10304030b0100f61040a41641401300d541c01d11071060314a4600d043c017501300028010001d0361a0f070304d56400391f8480e070300541030122442c983c00000d000d941c4580d25000c000744110402c2a400415201d030901448001c0b05408030111000c0340880c05540d070070715075004120b44d078944a05014110300400c0302c00502c01c1a1840b0038041440c00032070740d480c040007036100703028030a460460300360040c010a00021942208102001a0140214039924020401e5899000140c14490103120060142d50400349041d44400d0019411032100c2d00031407c603007a40c0c0c000d06c18 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 841348300 1250 841347050 841347103
    0x8010e071202070c12051b0d2a091a010804080306190305010c02010218100f120e150a14010f0501050a030f0c1205011d041407050d05010e0d050903 65
    0xd010f40c00340581440850000401d10180d01040d803c6000e0080d01160a040d4038440100140d00380c4a400382d801009551480c0c0004840802d800c1129005400300d8450000401840380b241c1c0f9164001080e080d2603440014650300e0079424002807400a18188403541b500d5101d0f0221131001400d458000c504114210424a50001c00000036581c424000e129401d0050402070107900810144800400c0c0c4500c11030403403130809840309000c0c0301c5072140c40d4aa1918082078404800c080150049a1749a91065050f0741081c0001c5600380301001505126040400c61041144c0032002c3d484070642c041c400511000d600c020640c022a0b5003460255039070118288102d014100c0071180760141c90804203243d200641080350305100e0312400104015681c1d0f100c2148080f91040202581480e1001021902041207880c50044c4036071444100c4002a94480c0480c00e0b11010142c01d60310340c0d40d075200103201d400c130511442001003240c0c603007941021414030000e51a54940c0f0b869008500791070007200c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 841349550 1250 841348300 841348337
    0x18021204020d0f020a180f0209030c01200f030304120c0f0f031205070c0203161412072402060106020601051011010b03011803110714060a0e062808010e07 68
    0x20303d80d42d002d06000600f990340d440080398031900c0308030f01080904100c51802000c03013500c2500c080761030080080203e00007010040d1080d000d4030b100d1140383d802d16494a80f040d9410052040c0e07030780d00040196a42d00c1d02d030600d1000c01007400080410032041540003c081040f43d50300359412034206009142c118201e14040d65180502e600c0a0002c600b8041004000d42e044403500c04458001d905850703070104402d1001143e10018003403061940c400f000602c0c0c59050412540110804010445141d103480c2c501c0ca22010003c00030744040416055a0400390990511940740104554002801c103541402c0005040c4450314010700100040243c803000c0342c00003500102e40015014000b0080c529134804829080c046ea40300c10350105500e41c400f1030110100044048c110b4441030100f0004044c210200300c0c072684880302040c2042040441d82c1915980c50004080c1c0e00075200719898030020440140c0c0c1140d51000300042400b0303042c00108841c1c3d49181074a507014070f6a20303100100d011100c503040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 841350800 1250 841349550 841349573
    0x10150506070b091c090531020d09020a0b030718141314100602011505091b0f0313021807080a020a23040f05030303090c0402030423060118021204020d 66
    0x10300710100104d207603821500080f101c415500c09442407032020780c1040a030700070440319032400350901c00c1032084c1061104043e80a84a44100c00070080780741003054000402180e5940c11400c1c08601c00002c0c8451550450140c0d14a020315540c07503c07041e4a041110351100d456180031a0082009081c50140f4032071b25030242140e040c004840c40802e050100a8140e4001c15002d15000756181c49007070b03116404c4219800342190b0004040174150740c0d40402d6180c17160380303607441a08203003001d001010441081c1d0003e10b00c140c115800e1440303040410300411041c0340102d160302c4800342c548814049040e50000e456a0300c0001e9600161b5504444d0100b2958040461a11180500c0e132000502000c2001c0d00280100d45120401400e842d84840402da101d07c0705a0304064140d10902c101c3d50f05040c141c01071580a801a40d0700e401030407003801d100104e22082c00d680da186400c0071005103c030001c04440c0c100c91240c1e10390110305045107614031035030080c4041c201a00c100d50020030380003081200d0010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 841352050 1250 841350800 841350823
    0x40e0937031b03020a020f030708061914090a02100e100305090705120c0f150a0f0e0402030115020d1805090604061511070617010e060a031410150506070b09 69
    0x20004642e82504009480da800220200d206152502c040d140714a00052070409031000b400c080c19260711400e61020452418005124800744c80b655148045c044c00c4240c41d1044440b400902280229841000b454050030f045507020b108204904003c0c40d201d59841a4241c003081c10001407503216420054034003800c55004660008a444e5880b01ca008082108003200105640003d00419608100249880782c40000200e200003401100c0140f442035003e1512000503090121090300883c0102d02a41d009030445260000c0701441d49c40e035580d0402210004c031400b46072910b1040c000d0410241000d030755204407446a20030b88003042c1e80c1d903600c1d80408001d1101b0450151074851402014001d40c03a14030b41c2c900b031030061020020741c01e4001d1070901d020000c46941c5038400c0e820b041a08c8102c04002e010700780c202c09030000100020b2501c0c440d031541c000070907004100380c80d40b0075500310903a603904410400c016415501001161100016941c070560301094007400d60307659404070b0b0f140c241501d28 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 841353300 1250 841352050 841352087
    0x5070c050411070b0a0606440601110106080d050f0c0102030406140f01060203031801090b0a0218060c0c010302220306061d0603070501110a0206040e093703 69
    0xb80c2104110318000030300c0301903c00d4000d207040742d440d208010308841e0341e48038030030105060740520030000443c40800c85440350044004c207000d114008250342944031500c401e141045040040c4804c075a00b1a001c01d403a441d103a0001d0001c182001d4105807103a0100e20000240440412000c041305134110a90720848000c038021034884c0f5140c200704002c3c0c2a6400329070903078203001e40420001416a500c9505803201900210314540744c03030008640200780184500d020755a01d80351100043c40509805006080450001d80c4a0900005801000c0030030320306144601c00c10080c4010b40781021405500040702402d0042c0c03100e507129610545105042e214014102c1e604001100304152584903100381c6829443d03220003c442500300d5540c00340240d6003960f141d0301c1194108455071088418000046040c400d4550015050340898486e8005800010604446008002040c013040043d00f469410000c1c08000c482c001000c0a000c0364030030390545000c0420344a900062601a1303581d200e07084076894 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 841354550 1250 841353300 841353311
    0x241314030d241712030a0b030a0b04050c12060c13120c09050c0406050724090605040203010b0d0b151504141503100905060f2808011b05070c0504 64
    0x3035490310241e000041c40d00080d0500d48007096900300700f40070000e030301d01c070384000d0841500e5082ca09010390001040341e102c0d59102c000b0034515403014003058030400e1240949605ca414030b8540300e801c007098906e0241c054440440c082e201250002480d54104407000021552030300503041c028603034002c54100200503503105c8c10080402035520004000c6075101d0004114a0315001c1c2401214403c03481002c0c0082e005001c00cc001c960003202d804074100d01c074044001d1040852100c44255042884141c440070350b14820042541005e0045402c01c403411188452031424540e9800d0309040082e00d110110300c506a1622030580b141890411034600d0a066151940c1da903680f00f2601d001c144e01c3c124050711400c1500038680d2851400d90340900304600388040c1c0142001d026400401000304019409423407603420f135425456485a80f006029259804006806800a5520488403541c07111101d03a14101c032500104e070402c0814850004949040360369950142460f4500446c2500540c0e0b001d45003c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 841355800 1250 841354550 841354571
    0x501270303020f15060a03060c0306080607030f0b030309031510030215190905060d0c0203070215071a09030405011110290402160318030b0405241314030d 68
    0xa5010303076281464046030104c06180e68940000081500e0303098001401d03500502c0000c4154010901d281124540040d8455941c3c4406140c08002d45c0d0b0389003c266a000d0501d1144d03014080d620b0241c20a8004600d01842400841d595256580a00711300c12442c2020030340c1e02c07100e142980c000f590024a569618101c02408500903445000e41180c28121a550000d01d42d004168240c101c1d000142150300744998071030303c08050303c4c1031040c01c411070104214200050383e540d540c0d1500641010302541e10b4074040e02e400700c280f00c031008003002c000405004003c0c43d0840041180c098072000e1919200b404113109a007480c00d41e0301520406d116080609400c1101c084080c110b1807010001d0b0103608410311402803000702e12071025034440103a9000f05040c0440c0c0207114456205d28594250700e4035564a403246c0b901940191400c481c0c60700010310481d443c06414404110030036241c01050758500b441110880e203d80012001808894240d2592440040a2081d00c01c0c1e81004401440f020307040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 841357050 1250 841355800 841355803
    0x20f160818040c0c0b09030c060109020a0e01090311130b060c0627030f16120206010302030d0921060e0f0f100c12022a010203100801020a0207050127030302 69
    0x1e2061180c50141c0507540c000d02c1d0601501a0941c001c2d2210814411240c542c0311001000910500d407038403081100c0c503a40f100c10400103000f4080c4050060700c40381e0b0020001e0035059841d00742410003402c00418408908981c03040c075001a82200ca21440d000e00c03c90311005000b8160403241d0202010900040f0f10700c01003000d03441510122548044119075500841ea02c058112001c0304660003480808000400c81c0000d110088000114071512011682c4180811140241890041e003111004108508082208810096150611468003070a241c1601042d032540c0100340000c4060209120034009035034040d40d00c440b030400c203480749543c044813910340c1c034641904a0801e07440b4500c2041e86444191190b040c120410795242d00107940c11081d0030000e50410610545001ca802411880003000100024280c4003141c0000d40c0b40d14202e41c2176026904258800d042c0769004105010382580d011034a0740c1561401d080107244103041c00000500000ca140d1004100015900080b00380f580 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 841358300 1250 841357050 841357057
    0x12020f030a0606020601120f0c0509040c170106122a090b03100e03030708070e0301020703030c1107030519140102040b070b0705090a0b0a03140117010608120d020f1608 74
    0x1c01c1409010340c0da42e941c0c08980d0b40a0901c15000804d13048042c4d44005002c00c2802c14003030f80252030040620751114000380c503030a002e403000c844010319503004001030f603c2c00f0410202d07010380b02c0c02080000d103130041c0d11018244028000b40402d10f05194104404840340d5840d0102c00c0c280c00d004504c5840d145070324001c007089c000640c86882400d0070000aa0354601a010002400002030b508588840c08140c070000d20152134602442041303126203015440910280600f94000d54000c144600135020280184038221110f101c20f4012120030b01c0404c5000900701e10102808c40d00c142c0411290411260015075050305000c254000680002e60700546006024198040c00650010b038840c10001d403610711901d0415034204031184410051400840054444188903003000301e0920b803402801110f2607004d8200c20400105007060346e15101c8244540310250040000a01c404016210b90a00600802000350b42454000803203401075070407a02500d4130302e420703110319540001992801a8480e007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 841359550 1250 841358300 841358311
    0x501050109062f010f151d101a1e161101090b0c074e0b040302151b03060d03020109080705030915030c0d50010e150112020f03 56
    0x5050110601c055292107040000300c071f40d01505656582c2119030016200e2100810f5440300e901c0d5800d00141102c41101c180000410051101d81d9070300d02c86900d6030000d0140d544c001b00c42c11050058410001c0590001c4142e41d401c407110f1460804140012a98031500b0340014028010200e032202a242e0001030160075901405582c44844903117613908207071984051100b480d40038001c01210360344100100c3d4143c541480a5082d04009070503140e45d07150140545044005902104030820020a030f21540c580044c103000003088a501c01046840ca580000780089201e4160410301d102014000d5114a1803190700001c540c0e12400c032070814640341d401094660b402030440c001c0000c1d845294000f10f83c0b2520164003d9810280e081c56003030010484800100840c006014080e14001781c60481c245403902c07807070410180760309006c03000f1410790503140a011881d01000014410741d0440c101e600e601c602c3c00e03080c2c8020018050012540b82081c41222079015100080c90010242c0041c029440707070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 841360800 1250 841359550 841359581
    0x70906080f0102071208270a0210020102030c09120a0c0b0309010f02700b040803070207033f050906070f05030a0315090501050109062f01 61
    0x500555101c0c509070300c40d600000744071360b08a07502d8550481c081d804c0c06420140010300400322600703a8000f560b1000c100c2e455072820b50711481c10034003180b401d110300091403030541c8025415400c1c800095241c0f80510341d6184c1c03113007584042d11196148100500f0074410381040001c49686e40d10300e030311415580b041e80c0303003e500d500b00002034006c07017010b00807070f0f42d000c9503007200c000d0b0144482080440d800e55103043d040c2c01486c940700c0c030700c0f00064075000e400c8014481341100809d92521000b501d140c82d48900c241d504140c4000b4a001103142c03219016442500181025a00d5858410403400d120803500020104d00801c00c07000403425506582009c4107600c5044e1130f81c0c400620301100384d040380803880140064010040d0003a1070130064043c00c8c1a500c9002d60300c6c6c2c030140a85d10749040d500003000c0680001d5030f488480c50304490b195050f200400e0350706001c0116506040c0000c180c010540191824046103000e40c90102da5200d000c0d01d56222070b00454800c182440f525540030304900c0d4442d0003031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 841362050 1250 841360800 841360813
    0xc03030d02070c120210200a03020601080714060a0e0d0b010603090b330f06181f050a0810080d0c03030c030b0f040b010207050a06050702091302010813060e07090608 73
    0x7068401042c0241403038000b41b0054040f8001c0201712200c030113420100c03414407070a50030700c1d66860040041d03241d101d1107500644015070400d2001d0345095040c0d402070440440018018203503442e80d01c126034940c001441c01041d10006c2c5408248500b0113440c3c0200b540003040000205135a043c0d2006601d248240d1941d49903450307841d03a00c020ba19415510b00a17210501c00d1700c00a881820312036030440b4401402c06500f20100c0300001c3d02c5a041b40f403500310a040101110f113620700d055500c441088040090550001c070f030129006105001d490340940502014001007018030580c03015210052106108450726180310032002044100034001c2200801d0801c110080654002c2c06101e50508010b08039854a0800300200405420300c0c403020703415405010300c0800d150311801e503010050b050342e03161b0039a51006841808030950000303110f40564003481f1101c0740107030b0b0701a004d10740000160a00702c151410506003032004041d8519425494030a1140004902805810820444030400160f810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 841363300 1250 841362050 841362059
    0x1b08040e0c120c1809101d1b04061e0e0603040303020c060f091f150b070309090207081215040e0f0c040c020c12030c03030a021c111801020c03030d02070c 68
    0x80e54081e9507214030030f030480d041180a0b20300b4210411603001e8021960610105d03951103900d0808000e04c1f05032509580d081081140103451101c100309259140341d507140c94586001401851524079a00c6a80c81051140e84600d02d01d03c10406442c4c0340d4030062100303a890800b894098025484052481c10a00940b00080c40401c901c04900340f2031030315040680b0501c0b03064040a01c0e0b00c10b5040c920b292941d030303806440041025900160020b80507180d111a902c03425400d0103404210941d01131003880740100900e4002908034003d9404403a40194250a242c6624029100c043e24008080e80c000340b50103058559400b0000d6881001c404600c166181030192006010986110803c50400b41c0d024040343c101c1c0e4203290041140f038605070b20a036420580d003003d101e4110b52007610256407484d0042042c03c84500001e020504013820703140c0411980c00d4100303d0100318011030311120040c1401e82507a000d42d90080c030501250391070040550750745800c1c514520009402800050740d400f041c112000c00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 841364550 1250 841363300 841363321
    0x30f0509181e04051905010213060e120601030804060f02030705010c05040609170307080a050d05040b060411180f0609060d050109062702031008031303050607030c1b08040e0c12 78
    0x2030082ea0070401400b0b0605c900042c2c8151100e03031410440e440e6500304a6aa030301040c0088100141895541e0680e009030900200810341c02d072600c0c8401d10381c20103001000040e450a08840848025080c20f405400046105900307501440c5000341165007803401445d03c0c2030f4031000034420f40c0c620f52121000709482e403900c40d0400f80c81c056401003550041000790085050071014001ca64001d14240386000c2c1d0140d441001d8031019141110100c01ea101405494606030144419002c00803680c01d042000034032400e134009401d0100180200c260710881d00d1903480f00000c84080c20f10191026903190003c1c40c03e031000b0182440b4000c0031a19200020500e04d501d0f41c1e000d0f4800845024489001c074800d100d540c029800a480401c1d08402180002900f800901c09404200306d00c41034046c20303030300c2c0d81480c0d410014000d240e0b6041624004c2010507a5820403100b6005c0b0700700c8118606001c00c2c1e0305c1c18400c0b6200c0d5030000700707100c40040700304410440e218005040390201c0c1c050089180d110b086401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 841365800 1250 841364550 841364611
    0x103180503031b070c06030f050a140612012007140109080a21050106030b0a050f010c0f060e0a1b060e0a03020402090f10050a1404080703030f050918 66
    0xd055030800c0001c41c88140c01da4100303826081c858260b082c40e25003203907102000703091700768415000310f521031010681241c458800d0700d0b84110003210500c070083c00705c09049198107000f4049807141401b410402a40b64096012040d220100342d96000b00386517504443c2d0450b04810001c88156841140340c605812041c018825000c1d4442a03182c2401117054003696440404001a8071115030075602c59400a01401003074000c02071070320300244a001040900401c8551504101d00035442c0d1501815281d90080410308040c1c1c0100d100d145580c118540b040181c100100141038520400780d090050141f0b10a0322000b090031581c5250b0801e030744840903142002820212a4050408403080015040580040030a1400140300341a00f44114001a5080c6014211000000e4000c0307002040f086d0816540d14210180043d40c070300b02882c1c890036983e41c40060000030308101700d2179001c0d4107203400741090b1088100b0003010195401c8440302e100c00d0032541240c8500800c038401c0c407204043c12812202 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 841366906 1106 841365800 841365803
    0x180b0103150606050a030213120506160314160c0c06050c070b032514120a0b0909120a021e0a050147130b010318 50
    0x103400c011090300076040300324a0407100b0700625400509854130081e16182c050390b02c2c4448200c0d24141001ca60104035914844101c0f482080000315109215288403064500e030f48024081c110141c03806216420910030200002c110004c03001009101c4d400c4c2e550801c14940d898a0352020144140c03580a000062008240490705103014031044001303140d429045811420208c11107180408020102242080c1c2c200754006c0c1e042c010314103d010b0000340c1107115102d00d91a001010544c45c112450000c0c0e9160164041c004c4c9003010740d182c0502c0c4450024581881307400c2198116074031030007540044d8031801d0009803c12402e90711001c0343c3e070784060241c85091610300d095401d450443c80d00305503201c07254a4800d07034452036400884c441c42d80c00d210400605001c0d001e072001c0f5003113807030b1842c0c002c2c0f442c0003108881d27003594000321a2040d080c0c1e0204140031130031025036105500480c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 841187050 841366906 := by
  have h0 := BRFrame.cov_init 841187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 841187050 ≤ n) (h2 : n < 841366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
