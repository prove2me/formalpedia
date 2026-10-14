-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1726
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:26:54.044774+00:00
-- url     : https://prove2.me/submissions/e8ad8e4d-7550-4d48-873d-94f123ed4eef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 310251798 ≤ n < 310431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 310253048 1250 310251798 310251803
    0x171213031e1403070f02010b06210406090f082a100b01021e0105010509060d050615060904060303080a29090603160620031e180604091d060105011b 65
    0xc075402e29180d01d00d080c66400890302000000ca0301c07003070507082643c2406400758642d02625001c0c40d111840940e042c0c00712070a040100c42e50f1003100030508000f26580b001ca0015040400b240440c0514640302200b9480340040307010011040720001d081c0e090030300c00d42881d203040b480103101005141c822400981000c40009066000d01e132030107802e107669030048a08400481000280c150304000400c0700c500340141c003460203100243d00c1d000000d900000c2d00da82088405440b4242c0e54030312000a407a5100e26100d00d508142046400400c01d60050b00c0030340140440001800380750081c1812171034138180b40c3c07445c013031045080c0e15003100ea040041070326811010103005d840c2e07600654441c01e444032032140c0c40301d000120080790fa80d107443c03540315242c00c208602c10040e5240030703088180000944054204084008000034802100e64034100240f03040035400740c84a0b40300c0d5a100409001031442420a030f070301e0107a9901c0340b8010100444c0203030607200141c48581784186100d088221400c0d003a40e04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 310254298 1250 310253048 310253057
    0x50910090801020c030a020f03030c3403031a090402030303012606070c02010908010e151801060f06120902090c13030501140601090602030a120b01020a171213031e 72
    0x803400344070a00041408410400045a0b241c101d90002484c007000c1c072805214a4100b40188400b4025030000c8441d402c80c812004030b42a0800c175100110a20658141d1907540140da40840c20107802d40c00a400072a0200d07140011200d900c802d00001140898000b545038000700014040c4100c1040000314080740320b80c60081c0860001039080c03070020150b5070703030313001c03482caa08103000b1507900c038044002a0005074000d01c0042c3c40c460300745a40d01c00880c0c0004c40d10541ea00041d50250a5880c5241c0154100700240035030b81c0d030f40006e100420054026800010340110030280da055281c0a0104129400b17040144103070748600010a80c0d800c0082d45061104c58180b001002c5402405101d5140000701d44860103803c1c050005441e00c2c205520400c00c0d500305003c204d13907580e000000400d0241041c5004074461122900403810030080c01002011220315070711986c06802540d001e03225100580c1c0031100c10f501c800303840410598801c00300500140f101e00d440b03201c1d810100403503818495a03040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 310255548 1250 310254298 310254317
    0x703060f150c0201110c1305090c1c061e1d01150803221d0a0b0d050d140f131802040b07080c10020304061a010f051e0d020c030408010c050406050910 66
    0x1072000c2100e0b21f40d103080d0030f403120240003a000d424400d00c0440402120101c0c811131464445080c00303000c00030054845992018800410303600c204500c120052040030400002c840d103004c000700d544070700301c3c00c1d4011340c60a0b40d5524203829006440040d165420000c5051400c40d14198154005806680310003e4400c0c2000459410080038130590b012414150501d514040980201325103101412f9441350146000e1400400d5000c6000618881c42d460884080c1165440c1d07444c8500c00d07189412078009000681e4402020300203082e0041c1e410b80001281182c2c03800c0d0059042e4010350080044019003013003600c000034441001030000c1c08409003a01c2220440e1510388040741c10440c2c050b244107032a04004205510307600e22010b07281100342404141000307205030003001401000014400c56128142c84100c07000c1100a0307a824118021041d0f58841c9100300650f240e42080c810070351603600b80341500840b00d0140080d101070b1340c4070786d032142d00b00003055080018800040004105004540c503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 310256798 1250 310255548 310255573
    0xd0209060712052d03010303030507020a051603020306010807030506060d030c060908072604120302160f050306010801141302060715020408070e040213051e0703060f150c020111 78
    0x41030000055641e403a410b03110708481c1c201310011200c400c0800b400c0501e0840f4107803008002400e5a0650350149000102541c0d0301f0804e07498041c01d081c0103086880b03001c6440c1040c0c8007014140c020b82e482602514800d0740c1c2e40d565640d0300e43d80d50200a20540040d80040c4941c14600d4070301007038078042d1401c03898200d01900d50070111104000181d0b003900700000c040090040001c5207020708460031011107940e9009040d000703014000d90065207031000302c0c11300c601301f854400c000c1c54424071200c150003070071f090381e6400a40e02c0f000103209503030107405000000074610106100e40c02c64038080b1941c2940b2599020345803ca103403c01c42003268003100a0081c1c0d4041151000c0c40451400b150100581c1c83d820300c0001032400c14680d0000701d14401c41400c010058032980038980c5040d40410020500c1c4e181c04280076520350035112407151000c2800300700900558903400c802c044494110546160700e484103c08406103489a218001040d2600e0321400154418940c41c2c0c003a22001d0280c1d42d840540a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 310258048 1250 310256798 310256813
    0x3030b012001140705070c1a1209030a020105070801030c030f020103290f03010905071e0e041101030c0905100c0c09020703090e0f0403080c070201021e1b0f060d02090607 75
    0x100c4080d41c003695074100c5018000b00c045101600500b00c1e042082c00d0400356130360344840c00700038000e4800caa802090071028503500030041d2009840034409140b241e280072008a541ca0700b00f892410010360038500403941a40c021b44d0118180c03900040e11a00c1241591180d01d000c11000c0400c81c1010b6881000305d2203c070240240780342840b0340380f42c9010042081010400412681d049091107a49484402ca000800c0012108111002500d00040402100c005510011420782c800007903a140081044100300c04c07004031004001003601c01b000349000d031a1088070003c10900680e600445442000301c401e900a514104005214410182660307403201407540903038100b19002c5011070034008040c440f5400300024175034130203840c1c00300211034500394500400310b41c1c0c0644064540d40d80020001c0c1503900c01d11901c80a030b0240313032a1072001003074416050b60302c0e090007a03440301180e1840700341c5001c0d25168548509041c00200601d00704030600d0a03000c002c0d4050034510350701c04d20410010300041c41e40e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 310259298 1250 310258048 310258097
    0x2a12050a05060307050a0602190609080301060207180504030f110f0d05040f08030a0e060c0c0d0308160c050c060c0106030b07021509160e190608010606120b0d03030b01 74
    0x14800c0812942000002c0c1403504942c5d4009920030904902c0501007d0f60014400013484201c00c020081d0b00c1142c20071750010114100050025000040080f440741c1c3c0010b9104203c480c403800130768001c0001000402290010341d00180080c600700101c0d00c40d00d210b00d652604110814003030300d000c0c651083c4000c0c80c1041111080c07003c160007003020080440019071660040c24081c0c01b6515102000c00c000306880d507400e007070622800c0007140d0480010000c00850b1350382800645011109145410043c0524000b16150b00d0042c04070904404280d20a094140030254040000c000e2011980204400c582044699904940d61a14000003049103500d407280203000c0ca4029092540c04000c00101202000703080015603401040304001c408110b00b07130781041304c610b201c418205407150340b00d0320082d0092503102ca80c29800c0c2400414403886c194011021070b40c00d900c43e00c5080000b15032110503940c0c2100c0d069400668100b074031021a001e0b4229a580b5581450a4442d03100e110b0700404407080d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 310260548 1250 310259298 310259311
    0xc05030f03041e05010647040e01090516020c0a0303140f030408191103070303091703160305101d090f06040c151e030c0e03030f09030601092a1205 65
    0x440728010021b90151070340d0b041010101901680824012840c10315403401c058101c0d6207107410792000f4507e0711001c4825078014101d0519580400c1d6558512500601401e41c3c0c00d81601408443c02406c0c58000a0302c040640d80240c60449110710f5524180c402e040003a10514076480c003088000b0203861550001d42c4124424002c081e11010003000c200c2e0841a01001a803d2000102e002d112000c4004241c0d80f44c240c0c10700d00416a104940303048001081000300c80d00d9140c0c0e01105019007141017402114007984241d074100b14659911007541030030700362482140c0b1850800c0d0701480c14011000c0a4540c040622000c803100701a180802030300d0042e02b02e40684000303200000501c40c006075110396844082c1c40380340649075244022407416800300341140003400c3c141e951402d041914001d4416042ca0780300241501e45450321040c2400365035104041c01480790248a001003003128080c880e00c4a441a4010514545005490280050007501018005014440e4424200104a400307817610840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 310261798 1250 310260548 310260551
    0x10204080d170f090703110d02041409060a02040f030602070503041226030f070e0a030503030106020307030306050a0602070b070c05040f0b0f040504152403120206070c05030f03041e0501 82
    0x1181091682c02d8540302516001c0158540f0090003808400055003200fa02d42000c11011455154000510703c42c4603078800075040381c00c001c82d030703194510200c407030030710903840b100c00d651117592115004d200700d00ca18056081c042c0c1800d9002d2000c903a00740e01428030f06100d01c0440c2d01e070a40754507071100b440400a9048030b0b500101031501080c008540042c41c0340c070703800703401c0d050030f5042150b00340c092070a00500403c100400420784221079540c0036901e81c015504041926542c0d40c5130000292254080d200a4010904003e400105401d2114404040725000d40c0505589818826403006942c0901d20550b10b02010b2100810190380f1032080180c00040494001169400718041c030000300c2204145034401da1a0600300170102d204d4425001e0310710440c1e00300003502c01304a40711545003002034501c1018120308400100070090351410083c2c680700c06400300c41141d40c502130201ca0072a1015401055070704140021406d000c1c0c032102442d0094400c04201400b20604034018400b014400b10039143c1c0e1303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 310263048 1250 310261798 310261817
    0x120a09020a080d0903081c1d0f071202040e0330062706012609010501050d0804090b120d080115030b0607080904180302010b0a0603230603010204080d 66
    0x600d440d003403400090110b2800340c1020181000003078101003092001034101540021255282008022200310340e100d001010407400c00450300b041032000b03440c0b080202d107100318203109044620007d1201c044414494041c8480c001e1f40e070911002e8031210390091800d210503c10170b102180c0680c000c02d120200c0d4140100b80200450b4280070b266800382180b4095440c0d02540084511304601c100b02506050000010320b496040048448040c0b000c45c008010882307941507404007030501c403001d0081402034024041c0343d807503804008007144070810041a03c101040104040503240d041300d4040c03400144402d510400f2651a07904080c0c0d50320200300058003071401030105408040720a0341045880c81c080020403040000300740d0501c941c841c058480000410250455602c58000011000350840740030b0003000b1920340603002c0c14401d07403503512801c170b030388000724507a0701c03900c01c004002c9050200840c03100d200b90030907443d1040c054070f1103405540030000895445403c101c211001c0449039200380c0742 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 310264298 1250 310263048 310263053
    0xc09181e0c0f0b07020a0902180409031103040f1706090a030309020a0f12050106060e0d020d11120a06060509041505150a08071a1e0d0608100e19051207020105120a09 73
    0x8024064000a074881d08c1845140743c10103030302d00070000340c500c1507d0002d6807503410b041c16540041030141600841c8000500402c142410405110171241d02c448020090441b5502d1a41c5030007080710900c0d47c550040d1107a101182c0f0a40200c68101e0010740181c0d40b86485005102da01c442940003000788104e059443c01c2000030074411440180340b1454001100d244010004110240016001c0d00c281c0100f40780340305020408841c00118440105030703042541c1d052040d652601d0b407441d41646d01c5440c21100060790f041c401ca100344210f5106070740030051a107104d508801040c020348107103141f154000f00d07000240c4640d071210014090030b400400b051485e0001e4031079100c44554111807080780603c100e101103034140c2d40205c1070554210f05a5110b860b41c500c400000d02c0d05902a01480c802c17141d442c1d48805032039100000c00340c0080103450507040c1d18140c02a00407400b4900604688c41021035070003082c003003005080c41d944145016071401500d41d107940a05541514640c840320f03600c0030380381e08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 310265548 1250 310264298 310264309
    0x3090d060f0207082503091e08010906060806090c090a1109040e072303060a0e1606090e0a1b080a0b03100506100f1704030e0d0c09181e0c0f0b0702 65
    0xa0705c2120702030000f0400c003513034010500c0c0c04511a0309450f5030042141d0a60b00d100309404001b51042000801011829080c23450280800d4071801020340500d0010481c20304010030502000c1ca0080d00c0e501a0380c540464210080c0544000350840000a001d074107016502c5005403602c802c121402487c0341e038208650300356603030805d480700c18079040c1d10400d980444c2c90100f181948601d12880c001403d540c0400564100280a00391b5a9400604000481d020f60040321a40079074000240c000000d544a50000c011075404c03c1034600c0b207403e03140000707039098480d40c0b07240d500c4002c0c50b001155010907080400e260010142107010003d4450013001604c0c181095000d0140c640b07072030144890038070620301800c00340f000f000910b6012000c800003001e050154106240003400a0545100c40d601d0b03007030044038884035024611009040c10750344000344c1c8007034020f180d0494104040c8628029550480182c50f42c800004440c0741c08100310008a6000402e600310061009548495540d5010f104021 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 310266798 1250 310265548 310265587
    0x90506040b031c0c08030103060c0f0e03031209070f0305070305010c020a1a0705070b240415060804060b1203030a050703140402010c050a0b070504031406040503090d060f020708 78
    0x1801207250180d002025540040c2d58803000c448040040480140850b0455003010aa48080c0c54040004000410400194452400c240302c07540d4070201c4207444a811a4a0410219469416401071012600c264005000340350002840700848014550b1000030041540082c2e0060310260412002041480300a00450140141a02c090402000c2950360501c03120710700400c514070702e0600800204864099070407141c420390481c1c040d504030700c1c1140003400e04a81c0c10400300d4403040030485480c0203090601a0340c840e9000d8080010040d410000126840c00c80280143ca4080e120440c0b010746881c1c180e1180117104009001d140e4916103405003406982d8050f14200426103010504000910000701058000c0d034241b81c100c4c0c21600600705140340c0800307a040640a91040f00600c001150064020b0044034442d003504103001c0144081c0310b84070300c011a0090f1540d0001c002008440c94600040382c2120b00c22000040c2a80110b07100400301d0700180411944208001615a0300000070744504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 310268048 1250 310266798 310266811
    0x3040317030c030c03090304030605151807021b010225031707020a060f051207030c020c01030204080d030b01110d0509130905120d0603140c0a0617010311010507080a08010905 77
    0x1107185003408415000140b0004040160071000840810310b40342c0c0610454000b560420028051414981d185400700c00b24020040e04c21010031030400540140411024811700058025150510810b21094500c0e011102c0b20f0b411030280345060000b40f005c8100007000b01d002139403d20081c60551500c5041c2d00114a40aa480c0c60280f100301c00695901c240101900d82d103103840401030101e520103407128001c070551003080d40318942c10000c1031a0316500492811680d54211054200314100540881c803a40c010103800e23130030505440203198000c1d0401c80d2600c2c41071624808614076070191a0030004034259031000140002140302c0189002081480e1100418101304007605896a0300b903035a203d94451500d90319008904614440e16540c80000299002034000150820309451103032a502140c408512610202d00d011070002d200b02d020102d1440103841580f580c0c0d0840c3c90702c6088000012a0604222041103103100041c0054060300840420707072204040ca5042100070001d0b2040205031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 310269298 1250 310268048 310268093
    0x507121202030304080a030b0d0602210a020c030315180411010e1c060903051c1407030504020901030b040206040906080f010e030f0a0806030a05010507111006060512190e030403 78
    0x10301002c45c80c02400c075081c0700c4d218100003811035564000304030341461001018220074800315a0711f12a400310264034481101a4218091aa964a039594124014041c9640441d4000c0c8002000100e4406018030501c0000344503044d04600c0300d8103645a5001114215900c140e582c0d0801d0180d608800c400c0803a00e41117480c2c1c0300100300c0c01c103501e80c40c103111003010340119185c401000038140940110781044640140c00c052075008901d84401814009a03181051400c0100090340b15100f446000d0050b603004000c003295900e1a202d0f410641d10180c01640d000c54200000110300400d031240d04020900100602600001c0b071000c07038210750350360420034400d400812245951000540403910151114100742d00a03850300c80109141801d401c038024500c0d0b2a2005121241c0c1e00106040c4000c0442400c42c1c045802840740001954100e1165201084082c002e19103140164100e20b80d200030341007420409140d09040c0c0360151148115010001d4000003024001c3c040041d80341c060414100c8070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 310270548 1250 310269298 310269301
    0x30319020c0a142401180f0b061617130303051b0601030c15020d120c020f01020f030f010b27060706060e06040e1504060209030703120905040506010815120a05071212020303 76
    0x1451003003100306c11141c150242c0d240c0d0303c1130000b0410741c8034910340507002c0c006940f5400035500704894403552010948d00403003512800402907100b14202d5103920690042c0355555031031903400351010340188941c0d030b80040c0d4094400717070141c0040000340c0c001c600460303291008510780784800b881010000746d0301003150028035602041d690021000d107000704122100080c94250f41c90102d04108011901c40f1417540009100c5084402600c061401a20101d0800000e41d82e0380301400c01c54802c01908003c0d00d8203140d103006002e410f0b01002180403001a18540c0740c507005039241c4084900c2500500711404560082c048035061034401c1d18442c0d03a4660040100002015640c4441900140000d220300c7d00001e601c03e107a103050240c4001164000820901d41140400180c034100da64002c0c06e0040389001c0009000d0742c402c9140c01c1c01004a0401d0340d1080380f00c002880042c04000750b061490341325200f50640001e07401c1180000810201780d0188601341a450001c403402204d11041045500610 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 310271798 1250 310270548 310270559
    0x14011202091518160f021c03020a1b0c0311180f040804170601060e0418060b150a050d06060f0215070e0603190608030319020c0a142401 60
    0x141c0e000740141048a412088101c0040c80c10a074110065a60f200c0200c24044410f004d2406601c102c1c007140c8501e168803002440032661024101d503c105500000b03050109410302a6000b01140c003114901040c80500c01404c80016450500044030402e1007a07070108140120703d0b04a001c02c810446444003000c04400c040d1029410140c802254801280d000c10f08100282040307030028007401c2e071940444800c0c808240d403144006d00c100300104000c1c101d0110f9034a4148500c0f600107070700a50404013040d0b00c0d103d40001308501c850b000d0704034040b98035007216125890301800412105680c3e69075210703254500034059814507030040040c000141c2c00c8948240d00813441d0402000b90f411550011b540b9400c007142c151f80d49880380ca8003c1750010034488010882083d2007100d81211200388881641c03410425a2403208940c4d010644139090000ca9040aa03a001429101100c40450f00c0d1121240c0340c0c0103282e4403201603805d0683c442c650203030280b07464886a0b00d00e0100040d07105580d42c03410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 310273048 1250 310271798 310271809
    0x10e040203090d030e0309090708041103030a05040b16060e01020d060803040f030305130e1302030607020d1b05030d1103060306250804050118050d170618060307031514011202 77
    0x1001c0320f4040c103841c1c0291201c0c83d41c2c20010703522010401444415103080c035000107454984107580030740d02201c01e401a80c005003400022102c960380e15a03240c0c0e192a242c40f500700043d80094000000d004011555000070039018008c50b00c40074040000140c1da0880280c004003100c28990041e804d0b03820030b0104001c4081c0050380d843c212501420002d68950509079100c0d815006074000c4801c1c24070715810700058460b030743c07081010f00d4402d0382190702d640c440280030f030f03a070b004c020500600041d0701180d0095402070310150310440c1361180701181c0c24028044401400d48203d602d040c40e0341400882013200500d0304109040e00704000f108440c80c05181000c05852071000110281e003032107080c0300840e0403c9400d510074981c0501c04980100031600700c0c6061901c5211591004c0000b40070503030904a0011808022030140c4001070820403100c0c0750f034000e5410200000e040b158140601c14001011a0f60503015087e40d4540d0388001a1091558881038650101a0005003010f0b106040120058440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 310274298 1250 310273048 310273063
    0x907230d0305210a0c1205090d0f091d06180708060f0a0902070b060102060603010e070306152c13020d020f120102120906060303070b4002010e04020309 67
    0x40c0781c42e55030748588081002455075035034500116840a6010003c0005040e40400e4910500e5515140708042544410050720000e83e5048003c0d00040640741240380a200132044452043c1048650340380d4038482910301d2018240c085510400c00c5080021a20301810a01c06001132745840c003e0300c0c242081c00510b0701100420700c60051040d03282e0008590b48070403000d80100001e4800f5076840c202440c2400320302c00c003542c016000d80b1824010801c14641800346000300210240200340e000e24580301d00c0040c00d03284000c0342014042001c041a00e0044104c1103040300380b250000c40180195420340c501c080c1004000c242c14880d040c10311401660390760346000f09160100d41c1200781040c40340000f040a4400707801c140c203540c4000341c0c0c4400f40e417404203107d20504980d0180c0c0e010f641d401c024942c4920840b2001005144036100240514a101d0340c91400e288404c0440f0000740d02a070101c40460f045966101a002140e8900c07204540e84410110480c2c0700964082d411400d1107507070076965065 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 310275548 1250 310274298 310274303
    0x206010b03040302010b090a020904050c042102060706060f03052103070507060f2c0304060f0c0303090209010e15040b0a0501120213150813020102030406140706050907230d 76
    0x30008041820f15101750440c0100351b100034101600c60500d180200d0095005403926030040f400e21000900c0c1618400984084910184650381d41c01c4000020380d00310703c1c2d400b0040b64042000c0c0400c40125940d44100300140c007144002101c050b088d4201b5500c3e1840d0b08040c4000d01d841d0600b030668142220003070300e80040190924070385840b210724018014004806a4410f80d6140c003c0060810700100d4000b030385035090603d43c52651200803d003548922550140c000030803040290548001c4c071421140071414001c0c82d000032900540e0740000c41011081e84014801e10141d0140300003c103c07480c0300c0729407200441c0d0411440d490100400c0201c3d019200fa141030105007a910748803085160111900302001c03494006245031600c000a55040784101c6510000d000f90000605c515040c400c0010700640507001141001e1418104071040d90380d81c003194000d820103101410001e0350500405007e40200130203014003608102c00c56044810082c0041070002511025000a442d848040c00d03a0741d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 310276798 1250 310275548 310275569
    0xc110102070c1a071a0421020102090a0608010b0a0c050a050a0818030c0a0e0a2007030f02070f030b18060709080c030c090a15030507080f010501060509033004061e0807020601 77
    0x11342d21b04105210507207840403546a51502501c01c00c1c243c8d419030040c030b0380c1281107401d000c80c1134a44a080781c003024240501d041082c8100040c9003014026045400024841c8044555408166071400e0034008005412142e041e000301e405505540344034021040c1003000e80040102c032100000003030901c0c03142d1140c050340204500104500f080c8a40044c1400c515951100c142c12288081000c850740c031201c42a80001c6442020403102480402c0c10411141c0202c04000040e085481d1aa022600a40754000c8441d500d80c0c5c1501c0349805010961080070300d91500300c111450160420305040c50002840c2c400d401030040c421480e65048281d0782c010a15440c0022007a000c2d00b121005800d507904060003c3c0300700b000001e0309500020b516180e000c900c0e002401b0503665a03106a411340a265045941908207058011031400300001480305104611414001e0400300340705480e060b40305800c4400082c1d0300340300039452002c1d215402c4d40c242c3b640b8900190700d40790800f0b0003910b17000c041c0100398a56 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 310278048 1250 310276798 310276801
    0x1030c1a0a110705190f0f0b0a050c010213060c050606030c0607060207050c0a030507090c050328090206031006090b0304020109061419080919150c110102070c1a071a 73
    0x20b8200300180181c2409003d5141030001642c90094402451003184129800c0b86408540c0501c1d0b14580012100003000b8107052048086040d10b41d40c1140807141c0c0c0d19942480072080c00c00c040b01980c001416070361103c40039500c044c103000d410100000d1606001c6e41c0000148162502c440045880558114000503100c2c0b4a03460103c0c10310058011255010b00444d1011091000c0801d1500480d110010108000412040182c030180030803076205a03012400d48640046416101190060710148500004c500000385e00003199030300251044246003145900030720000d50002005000742c60034244a074250b29096000900f0340712140508ca00300081034011500c0701c5003400c1541c0d441c40e0800c0c00c89000102804004003400300c100c522810301d201e180714183c1d8004044540e9040d03540c00c840b4001c2140101d507030340d10250900046400c20886803070101d00d4400000e2020f0001c00b442403054485a0b031801d03801244c0c0300c10050840e456202c04200540000320500e5000c245004241c5400710103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 310279298 1250 310278048 310278077
    0x50f01050705031c051807030803161205070513060203071e020111191a0712020c03160b040b1b09041a0301180b09070303080604020f090307090501030c1a0a 69
    0x1580a2030204e2030041254a00400c6449455041188034a0100002c0c0403000c0d000611507035120301500c0098038200c010000303da14190540c0640e0480321440c2030043d140703a2500010011500c1c210b502d44001036020a42e238454000e40c5184c9001081c03544025030405586441d490f03409017402a0603120784c90340d0b454140c1164068400c4480000807441500c980600078010a0a41c03500d1500c00c69410b510b030300c00901003e14640105010700002c0c0c0d00da108e040b208810020080d40300b42100c0a040c8800d000040c20300c803000c2c00302c0055501c2025141c42d0380c103181c9031121001d180508105006c51411351054403403803280040d030708000011280400c4003100900e00e042e4000800c980c0681550802d07031000e104008820686800c644240c0c1e01200750740e075160350340c0e464100501000700010700c0040800c05a00d40307074014001c20030003008810302e0080c2400000e8540750841c1d010040840e1900010000d11580000d00d400801100d480b144541c18107145010452040080080501580d050740048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 310280548 1250 310279298 310279303
    0xc03101d03031e01050a0b031609051507170403030c08130302040504060902010f0302160b04020f060a181409010303082502010b0f0f09061003021201090911010306050f01050705 78
    0x861150354068a40d60308061040e0300c07a1204024403201d0b10881c0f60000201030800c05200f5080390082d400190441d111108002c8184800342501d0081002e90800416250340703602102070480040c20700150781e00b0107031410030342c0c008108a03030380800d80e401e10003000484d80014010aea06a80071551955070030b10718a041c1c0080c0f134a40c0021750001d150004000400815510810300c0d24000d880b20304143c1407007801207050f8802d40941c60107021643d10508000790040074015082071004040700c80483c02e81c008110240c004010980002c3c0c02941c81d05000c0410000b650054160803803808000350452000c42c4a099061000400308130070310340060380804540080f2045500c41d580c403204001c04145000303010303004059215200300c0300840f0600640c0341c9030038048a5414080c02c84111035940504001241d0858002c11090540810240b48110240980c240c060304658500203240183d50400e0091a051054064180f600d0b0007414015552851450b605000c0d0929060f551070b00070389031260 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 310281798 1250 310280548 310280591
    0x105220203160314250201020405041401050a08030412030f020a02030706030608010c0816080402180703060e01080a030e060a0e041404112707090e040f03110c0310 72
    0x120014804024000c10342d060340030051a01c491650248030301c5003c503840d00124801030315103828107000035280c5a1115401c41c1015000c035405d0000508065452011070160b070340c0c8002c4041a115500c0c010b200030302d0054184030180401100960805080240499000e03a8605015043c8106442c2d009178051081001203000f69025041d1031111390385101c05000350903a801220300950078040020142e40c0314001d0785105908403140501000d4601d442582c14040191082e0f030401001203240301051a85100580200d14681c0c2c0050705601c2c0c0303501c200c0300c810103800c890b0751504804000c0300807984c804001c0011602c00c40e500c954078154100c0a481685080010a80060410703a40000085007402c00034800d40c0a4949940781d00000c10400c00214150300c406042da03403000f04514640c3c10b0103d1501e40c440a6814a010916142d0413030410795001150116202000005e40100305035010075004041d1800c0001004062500b000080d02c440d00d22050405145d80c4104010300000751041c00d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 310283048 1250 310281798 310281859
    0x2041e080a0809131107050a060501090e15130b10050901230108100503070305011a0a270209041e1415060706020409020a020708120a080a0b04090206180906040903080105 75
    0x1155921268038125840b0036234905c00752210740c6031100000340ca0106014164542d51040080c144503c0044590300e4801009411503440500c99a82c00d40001d0b800510540a001c51440018100e803070503042220312001600100600850081d0201041454105850342c0c0c80b42401e200f0f9043c2e8a06108100e80d5049600441c0c0c03600c610ba000005020b811340c00303d003469180d00d040708098103d001c14410803141d14031a0038051402c05809480102580d030003940c080d0b5000c4c0001d0310300f14001c0001000c1d600011040081c100d0080c1c0c0f024440500380c411000d000c6a2001502c28525003800072120f06a500c0a5482c0611800140341041140907030403507000e000c44000c01c5482c1d46420784001e5503504503006281c501e11540f818600200302d4801500d4110a10750303a1000c580e075802a003075001e09131a0701e1450300981c0f00c030917420041c0e42d01000361104e480b4030620221105050000c1002203000075101502451500c0c5504011950200e1420b041d0366041c0d03240c03c0660300c508079443da14219070100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 310284298 1250 310283048 310283081
    0x50403020c10120b03070e0106110f07060807180e0106030f02090d050c0108013201020f0601180b090108070506071a0705030f24100207080102041e080a080913 70
    0x581860503000712840c0c2007104803d10800012803031000745540c0b890140141600c0e0141000100500c900c2091400a4111a042035a40a158000c030492a2541c203030040300c007283d070220030040c0160b400110382010b284034441d40c1c01d00b6482c1c00090380e1203c10600910781015203484881a205900741c040701e214510281a505e11142075080c125120301210000c80c0c00a101d050001a0208411650600345443c1c0c0350040e032450041011101f041c44c0d462021410360282c50b80b010015407060149500030440303c074403922050110340701d5030b08940c2042e1006200302802001400901000208101610000d40c2d5065076802907007007080c0303031500c2880c0052460049030b0800034900d030701c81c0240d40621440d08400c102519201c06c0000140340080900300d0a42050003445518035003424242035a883d42e00548207684c1d03d95507a1030982c0e000d5000342112444000385403441100200d40e4000504145015000d1001c0d15942c0078158814208a148111b176500ea20021185e045d0b4055040c50040403039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 310285548 1250 310284298 310284319
    0x5130812060906010203193608010b0102010c020715140304060608010b0901030b0402210102180a0b03060306040602030c16030206070809012f0d061706011401050d050403020c 77
    0xe65a100108450090082c2024004502c0e1540000103075102e10990089550810031000011184034000404203d11900700c942001000a0850460400c6040c103c9941c54071a040110030f42c251038040000a045a1520054150f01680858444d0503035000f0103400b40140001d21301103a0502c0c01c00c8120b903c101c000814001041459030011003201c0450b0002d201500c1d0000802071120301c03d00c000b0302610f003000e000030300600d01011651f1000c01c0400c0d4048600180d20702c01e03822a044402007142400790901074041f00c0c500f010940c001000164000c40c40c0d4581400482c0e1503000140008202c1600800854000c0400d80280d400b5000c110000c010650f2003810020b544c0c4c2010380300ca10204100c0e00c04954100018040c12141040c03d031055400c00003101d0303034000b0055055903240b040070b006001d1000050000d00400c0b0003401c04101001c2207202c00c510b56801c0c0305041c0d0109110401600988000d40d805c5010f07140d9103441404002a141d42d141000d034100b40040341c000c0e80c04103000d007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 310286798 1250 310285548 310285567
    0x50d0e070807030b01091e02090411040801060503190305041809020d06290a05120f01060314100b0108060f01030912030e010f0b030c1009030b0705030114060a12051308 74
    0x29120b8220713401601141c03001d990790559441200c40f03c503102604890700c0103510880c841c0b00e030010801848003800c006201c202540002040b500075800c80180d994544000708207030716003041041c0d1048c4000d106261a80d0b400d070b03001741480c030440c41088c3d58030696901c160540080784c0c0c0888459500a008809004280e160010080000aa50100c1403480c00c071883c44200d2048010001104e000c0c0000d60b60500300410000d85d40040080145184a00303034022041c440203000b40c00085116109200f120101d0100443c10088078983e1111404d19115440c201d903a40500703541d400000a07078402d0324000582004030081c0000a802802545c0305c0031006814580c1540514498508030008121344080101c440b800c0d50031403050030381d1591000080c50740303c1c03803c802d041c0e010f0200e80c00c1400c0c0d95a0380795140100721130100e910001060011004200c88051007400040d0007a0441c0e0451502503281c0010346007200440c400210180e0f17890014200781a2010368105c00d80d0042503040e00c070300d00d81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 310288048 1250 310286798 310286803
    0x80109060b10030207020d0b101806141002060402010807030219020703021c0309030618170a020d09150336050f0106180e010f1434050d0e0708 63
    0x2001c11602915150181e07000440c4a44240d4035401da0040038140c001d0200d884034a59148050801b0b940703132800720381c00103102c03c90780718200c0c1e840742e07070718001c01d0722458094180390b2417200710301c0b0500074002200140803055000c41c080382c2c80703682420041d00c5500c648104030002e010304400040d0180700350a22480c4e050300058800202c074404c80300c90500840c5c2c25441854090a80c10003008944a40317402d1001407019040454584a00c1603140404009912401e10b004446005080352180005000c400c10b6818000342500400d142401000d441c41c4c201c02501c00402e0900d018105591b8203031540b161003a424403c079603490450001e10140c210459481007914014070110765a00c181d640b409034cd81b1042c00341c03600f1145404070300c00280e10f5220b440b030060180701c1c1c0340c417041c0e544e01c104441c0549954131a105003000c04080c045414078100d0303c00c5400044045011f00d41e4085550401040200303030480260803451031401d01d072603c4d511030201028289501e2601664001d560000c60b01c030000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 310289298 1250 310288048 310288061
    0x10e0405120f180d02030a0f0308090d05160201020c093306030610110102030a021c110a050c0f07081f0605011409030c09190c02011b0807050408010906 67
    0x15401e88111414528400081e8840c84000c403007142030500200980c02c0c4044000b03038919001400118038401c4da036000a080c440a000212044070f14800700d502895131101c40607500c0480500101140c49150030058241c3c0100d8060030002c0074031a91203800c59109000c000c0300084090030031703007807420445e004503840c54000807448107480300380007202c03039961000c45503441c04a000f0381114034546a041c2482403989054060740203101032550b001407420f409200851040c034111100589038602c0614000000c1c103040564032200341010092400c1c603520b102141c010b42d007103050056507010341901460500c1880310254523a0300513803a00045080000c1071403032040c1c10000f880c010480804a0b240e04171100e60203002d00250499651341c81052415000304054400101100c190141680000301500400c584050036003003407000400781115207010301c0e89030340640e0009000210150703800350703000180741400d03504000d55280461941402101202c0180c00d040703000340f00e05041400c00b280917140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 310290548 1250 310289298 310289303
    0xd060608150d0c0b0f07051023060307050f0a0b030c0c16081903030b101119080708071a040506090706080915150a0305060a0b01080105030d0f0512010e04 68
    0x20590040c01c0640780011032806a141d00005411059080500114094100c46186a040d0404103d503a000c10000c0001444030001d4101c04241500300704150038010300b03101c1100399000d000406028aa81d0301107049415290203541d41c58004511800284108005a01c02d8403004d0000040c003001e0001c0b04010302c02c0c4a0103101b2241520743e1400d400103c084584101a402c0e000105aa40004010900840180d010703260100e4641742410019000b582420244400f00d20f4801c036030b60240d00c00340241d10407503047c1450358441d94166124002e403403080f1a8000e008040c0020030388104091031007100707000c120a07405158286000d28240350390700400c2d02c61144602c40c50b440020003900c2000898491080c10303002d841c1d00e40390130800080c034980c0078024841618004043da0030684810702820002c5025000810300342c2084900c06080790300c2c808900c0e04101820b80103205946000603240030456841c03400c4c01001308021021142c5000380c1d20502081d80994000180004400c2c190303a00450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 310291798 1250 310290548 310290571
    0x1e01090b090a050d0c020301020904140604050702010e0703150e0706090f0b04051e150d0c030501080c0105120a0207060207060603030807020f1902060415081605040b0702040f020d060608 82
    0x445950349165142d25004008000d9030200405129151207504211a80c1b48080c00243c02c016542c00058169075100c0005110070042c0c404210440c60240191500b0000314002000700011150082c0c0d1039642d0f034000034125411596030100b55103e258030201078034007082c0a03036003003503110709001f8903031a054451903010046444011400c080c001040380c00f181c2e4020002001401070b002030401480181e15000d52101303d4001c08000d4440c1680203000c4450201c000064425180d03101030116101a048050240e0281c4483c26050341c20008841030fa08103840340914550307440ea0750b000a8859220000d1141d40081002c40c20494540c10103004c0d00d00c030340c0304d1440342d9540c1c0034100c0e80c603200c0142000b81d641c8450b0840c03c4822002c00321000882c0043e00103071829840700c00f10200c1050715034090700050414010001c03051176942c40c1102c9410300d8a0650f00e8a4601218101c0c0e5000da40c401a110b207650b10108200c90720f16a04031082d9070041e01007880040d944a0014008007800c540e15003406 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 310293048 1250 310291798 310291801
    0xe0a05010302010909150612140c090117060d0303110409061409150a0315061d04050c060403081e07050a0b0f011d010b070201030b0a2921091e01090b 66
    0x5811b8002e00ca442541c02e1489003905180400844000b40a40b90807881e080c0d8440d03080c00122200502980311740da22494850f502c2114000041400074001c0030282140010024000903a90311039a4503d61501842c0104000c035183d4041800c600c2168800d80d00d40f0303e030000000e4a40f841c21103c0100b14000c4903414040da0300c2c1e00440d080c019900502030790020186901f0b2000070000c5050843e9042880000034140c1d84403000740c400c20800d0042040d44251400400041100422080114003026208076082c286140d84e1020140201049203041d03910801c641d8100c6454178043c0d0303000740e40220480355881c43c0c9080041e84e01c28140d03400002840c0c00d00000c81c50303044c0d40001c0c51079064814071142c0668a07203002c9a0681d040400700300d0400d616851801d12030f0b501c96682c40050441013424443e550130203130103000706401138124102c20b01d9041c040c032121900044680019070b0600c501c8412160340d43d064080c04d04842481a4160440b114150784040301c0540c09118050b22401a0315140e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 310294298 1250 310293048 310293059
    0x120a02013902180108061b0f07140c0d14010e0111030a0513080f03090706090b0a03051f080f15070804060b0102070503010e0102090301051e041211010c050703020d09080712020a0e0a050103020109 86
    0xa1007032301c0060035038040030000d640c00035142510265090fa401000c1e20003603100080043c520064001c42641c45480c104800311038280b0a2241040341d0700180000c00600e0400c0c043c034901400018200e040c1c0a03a10000a030b0f030301010b80503200d011607202e00b407140d44036280d001c0d060454006513441a458400d04030046142806400c2040c00d60300c01d154500d080c1542514124094480105070500e00f880c10344220500910750069040a081d401001d8441241598101c51a1a4100620068400c0c0c0b460601c1806d9801182054100d80c0202e404038011580c100147d1800003e80e201c00d405600c0c0281480080d40194040d046a000c200d000f405580c82d1038442e85101840c01c030920a03240e8a0380c01180c0007600c041c1e910004c010050a0001d4090440c510040c00c551105016101140c80018054100350f030501031a070300c014160612480043c1842030031f5654220500400c403000c0700ea05003c0c4159030703507100000c008000c1d619910a01f850055110800340000703100480c040381c8407150200b403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 310295548 1250 310294298 310294351
    0xb010e13061e050a0c05030a09110604080a0b1506030408030901090203060a050601090501081b1e0c01050103021017070e0d06052d010612051005120a0201390218010806 74
    0x2040a41795031010f0454460700000c0c4020000e0701c00403501c038003904508058a40b60400030b4001051190003070b112050b0035080c21089640010b10311a40d0060707011581a090351058203998215400480c029165030710b1144031401881d0402c406035041c403030340b0200092844240c04c40c074414002aa50040410b548500640d81000141e4803034003029080c2c0740d00c2c0030695002d4082c001901103084c260906045060f90175505d5030240c903420300c141e5160001031095050141c08004420711525250810984003944180f00f200090281002c0080620328441781c0d658000300c0300c984540014040201d41010a80d910301c0d1101488038030340c80309000d4a00720740110010380c440c0c101c6600d51240b00300464545031041c001d000c0100040119446041e02044680760b5900320844804e010005280401140c00058024031915050440304a900c40c41c0c10115240000182622140d82400b1307842c880c0241300041f042c4000341041d00d04424148000034020400203071007402000380c24092509050740005240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 310296798 1250 310295548 310295561
    0x1f08031803010e0a031d01090312080a0c08040203190c170601030b0105010e06030708091603060c030509010b01050d0b04110c03040e0f10050d050f0115210b010e13061e050a 76
    0x6004c01d8480c05c0300e1402c00641b840c0c028001005240a45005440c2d0351040329a0228081e80000203820204000c6000f147d882010360520450600c1c4440340780550000b6616402c400140405038450304400c4108102d6802440107400c2e504014001d810f16800001d60b25902403005a0320721510740000101540501b4411a4940003c1d20f10362555403103500c00d0300e400c0305c044c0140110344a41108110454060103039907025512035400032443c0562010014151900a0001050350340340c0340311001280c0c0c0000480310301115240c0d010510305005000540140400a543e04006a0014442260b40d0020000308169250648801d2054450509222070311808952500c003011110b41c0038032140ca0000706102805200e0422503034084c10101c00c1c282502e01c0800e0110251480c118144560610448003034a803041d0310140003148901511681c912100610903a0303102c02c588004200000042c88903a1080c5821110038000071401c55070f00c07980c04e00390304507a48115143c50701040c50414030f4082e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 310298048 1250 310296798 310296803
    0x2120c01023609091c08041a0f01090f0204090903080f130503030c0d021308010501051206040b07050702011412041104090201080f181203100b03010e1f08031803010e0a 74
    0xb1045109800a1120044020303144200d80e1241d110a101c2448080300748108200c00380d540d1340001e0505242038014166042e1000c0f6800c0005c200f00003814600582940c1150820711021901c9402203030400020b210720b4111081980c14914000c0a160300604294094102a1028001c995808030034650462494100401300e070000c00106810070300c0400a40310904100c4001884d10100440d90703108201c40750b112000f503075140da00401291400c28410b000c0103602c10081c082c01c1c542999040420791005007050240a0081a0341d001d5903c10f541104100302030350760450b6120b11a40011102c01c4007200d0440d418000004070401c5230505006060a0540c1078540540e26110821a85074842c40104010041c213045010018034010802c12800c2c0c20042c10b83c05a49c900b00703004041c0b001002c9400241004000304010464042602c1d06150300c40051010013250181620100c0d14841c8180c0c0700c80305510002c6100102600c20350160036402404400030400e48044070202c940307851551102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 310299298 1250 310298048 310298137
    0x14031003020105030c090405180105090d0210091e030306050a450606030b04050a0b0d080913020a120e07060c14030705030a180807030c0605070302120c0102 69
    0x308010350145014580100f01011258101054040404c01300e49080760000d400301883c1c1c030000301255080c89020b4024811001605e40244001c10203950349840b080b4041880d43c0d2860f66506104404103030120140c07400c50415604126410001c000e403140e03005036807180d1194100050b25400d03270a03d4403140c0c0305100e500700f0402064105a940c03040708481e04000d24440c000d50b03280002c1c82d0710074140607147d9610006900101e50342800102c2d032000300b04100d42413420700307002203a559505500e0800d60f804000c041d91405c02d50085440078460400c031151007030000c100000c4407500140e903201c0d240740361601008030011010b1000e80d03401c0b00317100c1c010104142d101003101151600818205d490b081324222032a119103644d4180c07031a40b09249e501d001508144050032010f5150240400030074860004001c0242140c4500101c64024401d44060080025100702054000d01144851503036262401d0346511740000d40c0c9000c0e5000c4031500c540282c0103014001c50100e0b00981c402185541e030b41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 310300548 1250 310299298 310299331
    0x12130b0306012c040e031309060f051e100f1101090b0106050d06030210050307111b010509041409240c040512100507030f0b0d02031f09170a1403 64
    0x9802e02840f600e40c00c2851000810524819030300c49006882c000038105008560301c00e0400c1454401d4100380d004102818289041005808100311142042c2d4600726040d5240c07101c211140c01c4c880411003882c503042402c40e5600d15003690048501001c400450300c60722031038900d040c00030f4200c40c9828002001c0b80b200200600815114101500f010241c0d48800905580c60b5000500e10312882c5900e203000680c00003c100413580d01540d065510301600d401481100701003000c0243c1c2c28004440c40d4100b0101086500d07050340c441d0440d0034000c020b01035400050400a50f41c603140d04104450580c0c002034289030310706101c142103010303210703001e880b4600d400c2900f4481040078030746070700780a000941708402d201c0040100c14030481c2d000d0041c6480c001401005d5003000710913a0301100301284240c009052000160b03c02040c170600202c50b420038181000f8000304000c00505540c08058007440c080c3c04250211079000300109544601601c0b01ca03d1500456040c900e54401101c951411616400b03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 310301798 1250 310300548 310300577
    0xf040308060102070305010e030d06210b0606091305160903030905061e1207030614011d130207030804020a140d032102030703090b06010311070807110312130b030601 73
    0x3008941c00c55414810364012035503a07140c280c01e50f269404004090f800000d14076550310158401d010042040d000c00412000d050200340701101982200a050103004070002410f40c1c1d141c0d0308a80c52814000e1502c20b92600e04038442c0c000345421122424500c180b4812081414002e66036071048a5041e90394204050404080c000307940c000b968801841c04c511902051440150005400c5c0000d0103031a212847ca0300f19001403d41e4419806a2048507410700341c1c0207a03903804400d800d4900b15000c0051045182d540124401098031806d07581007501c007148034804c01da449804180220b00888854182e16103e03101246100a50000990302407206580400040c1c0100b07401d040214211180205403c1c00040d114203a920490f410030000f995070028104020101c855240c1000083c81c040202e4614240c00d4403491240410182003050042102030400540c4440028504000780c107680001c44410980c0c1001e80102484031117000a21001003005d644403000e5920901c0140d44541d200010380 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 310303048 1250 310301798 310301807
    0x14150409060209120a030e06071e0201140a02010b18010501050a080903070c0f0905070806030304060e030f0102040605122a0a022d010c02030c2e050a020a12050f0403 73
    0x10348100c0d000d540a00103100c86640303100d06501101d80754405003d040e4202d160050030b446070303446035521a00b0140300c0003020079002405800c000e42201b079a001081c04500050300d00401c1284140c5a40c000040c1600101d40e041d04003007110302040c1d42c040c18441d140c81c0e031103c2c0001c003401858002201444401d501300c0c8902d0315980c00484440503680707800c2d11034840c41c8058070f603a01b207001d982d801418204520b2070544038641d03102c1001e01d003424071400c0c45c0c00000e40304d208502c611030800000c100010010350302440002900c0f040790000310341d25070341c9060203045030b0040300d00c00c0c03088a0f0305000280d051103d09810014046002c864001227800c2c0e091040880c1c10810340c140131445107004402e40f107021005500881c4151298000d101d2160301001401c5d205403002040441d00140f01000f65500c0c0012071a283c06840018103079010340042041c40c0d0014030501c0001d29a040000340846c00248c3d50007001b800750141c0d2502c1c0d1a4a4003406c84066174002d848514517040464001004213208 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 310304298 1250 310303048 310303061
    0x30b060d020d0b01030602120705090f010f121802010906050a0c06051003020301020c011a100210090305090307060e09010f060516111503011d0402030a1203091212141504 75
    0x380300128002c4961640d00c11080c09800845855500141e5a2a952078058006070310002515002c2e00e00105a4041101c01002d003003950f05100c3d18100100b009400341010740507040440d0030410408038604461800c0840000040e03022034210800403c07600e114000310b940d011641d48400703411405603910340004140040810b120802161000710040c0c7c0c0031f000a10407484900c0c008a86600502010001468101c00c014855081202e18007411900421001c251209110300000c038140c3c2070800b0b490901c0743c401c0180c0e16009540c404901c89401082d10404490292051121a030300c807100d030401204180144004210300348411000c01c154081a03101d0036100b043c69626107119a80070800c50040d0b61340c9011180d10100c0148440c4424136900030034410004090561400d090b00400d4440c0c801e5480906a60110501064003501a8005403000756000c0480f02003040e140030010802160911203414035400c10200041400c2800022402000c5040d4001740d140d03041030400000700071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 310305548 1250 310304298 310304303
    0x7051906090602070312060803090a05040b060c070f0305060c0a05031314120403020306060402070b071107271802030309040c031806060302180c03010302120a0212071e030b060d 78
    0x211041d031440014001c2c005012154425200c05181c0740c500305808050b9100d0f07400c0b0100f142d105100c840c03101d550310320519040726010703240006c040c0926804a40745104945880b03000c2d2045990018041b150421900100ca0154081c1d80d0b071038884509620035480b4840842c000580188003043d9a42004c00000400b01d22801180525200680c0d1103400c1c0440c1107421700413290701040410941c00c05104c0e40c2da04c04002c48046140007042da4869a2000e0040c0240040008541c3e5010f540034007000b0304070182918405800300d01903003450402120b42c0700b10340c005c80e8604007080c10040103886482c1e49075090307005024500f89543d00c81484010603210159204054607019100840441c3c3d40188040502600011940a0560050011504010444849002c481020040c41c5021301003a80e043d81e0741100c0f80180c5941c0095540d250509465000c0c1d0f04c881c2010101c81e04001c009410b1080b901811141c20f403007000070b403a00304084001d00c07000c3d2148029100043c160300d00711300420521813 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 310306798 1250 310305548 310305551
    0x603043801031e0b0c1308030702060406210905100b010c05070b030907120c0602010e0d0903320706020c0f0303191b0c08100216020d140316020a0b07051906 69
    0xa501c4004201300180c038800c200d000c2c009600b0516891800c0348002400403040110301d08030b40d40d80030801c7e41c03003580b0442c1c0402410301c0f45010304c44070052020090351800c030703401d1281d48a00d05183c3d80319500039089544003450040b03600f41c1d5500408003401102d800c0000f8224051030701151240380d40c0000c15552540c0108000880c507545500511402140a803003500190340c140b0340301900b16040e400c2503074160350207200703130b03032040380d8444080400d90ba8440b40d280c3c4890b500d01d80c1c0c0c40c1c4003044010000395411650750815031000d000a20f00d0211003d40e82180c45941c01c02061107001e1901840903505900204081080318106032405c0000012604d00902414100a00c608651411400413545580301a0042003407207802c000c02d100280003910304603e07085141040000c3e0040707591009000759030a12000b8203001801008008402100c2c0c240caa0b00c000003440c0c414403400007142203100311035000d40891842c40c21000d03100260340c000b00810847c0d9501542c0328885031115001c460f000e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 310308048 1250 310306798 310306853
    0x200109090c080603070f12032601170607030c0518150c03071103010b18070c080f1e121807090c080a0b0d02010503070f0c02060304380103 61
    0x400503200d00306203803010381d6400b5040d042c050205401e103a2945d0000a00614413902800840c00003150511034a070b05050440c1c4c0c40444810300102d59003964441d05140342220000141140d03400404004441c41e841614245ea4800605072708980300048020b0009005120f01c61200c0e1a0300030b0160850001400720200c05a9260b0007003059201403180c05550f0004211042046002e00c17070b582e0885422002403200c150f003100810725501c00c1d4200342e10103045503070220341e081d80a044000001600604441d50740d4842015006590f8414400812401e5104e2008401c1281110503182c001950b40d5103280d190f229060300140c00481100c0720070305805440d80000f0851300c6403084800c510415250041c6a151060010040300c1000172401d0180d0520b044100050f0307072200c2101da00041c00c1c20700c1c0c8003504850500300c0e8094141c240007500480c0020612050102d1804040c842402c000030426002d128a103403004480b152900c030317442e152036080041c00061205502c086203003e0030703030411002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 310309298 1250 310308048 310308059
    0xa1709040e06012c0f0f070e0a081b03030301031e1403160209010621020a090503153403021e030a0504031404030503030a18120315050409200109 64
    0x2c222007a800250032110600c4034090020082003407030310111980c0f054081030310f40144083c0c4102401070441c2c0c3c007402d0900c00907031414003d802402c410074014120420080d00c40c0c0d440e56550301e25002c42c41c130004120b00c1d540c10700e203070001c11641a690320040d2100c1030704c00d04030b071100c1c50401910203e40c0510040502c16a08070300b00041c05202d6010100030110b040a0300501c0902c0b5010b0700041c00700a54104807540c51514000c404172042000c040050f6201c11000302201d104d4071941016900d801071090800110030b8401e241401140408007130b540c0342e4542c2c41c02ca00c41d2003c4400c0503035031004407507200008501a50103840f1070021131003012000030301405a10308543c0121a00602e80703030f43c0d100348000d041d405209070080f0700510006518050071601c1c0d55681c1c0c00000d000c4c0303960a031544250030049548801c65500316900018055414152180250281911003245c01c00c401402400060510f00703802103001c100d41107d0010501035114041d401c59800030700296061003000200040c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 310310548 1250 310309298 310309303
    0x9041a090a06090b0909030304030c030905130f0b0d021011030d0e031c2c07030209090f0d0e060d0209010306150e010212070b131416050f030a1709040e 67
    0x2060040001c0060324604100d148000c50b81e100d03400328020345003241002034264000048903041501410002280b030810301d000c85020f00c0ca508225000380c083c42504456403440c0d00035507601500003030180503440c048014046054410741c4c000e58004a00c806140368203002e05601e000700f0325076906803440c1010003040b1303100b41e5003143c00024803a40001000080c0780a524242846112010410b1215180d0f03030000c0c0120300f0152540c0c60764203290b070321099207030f9004200c1c0400650b80a08241003a00d00b00d1903103031700e0318400d9040485601824540e04900d078499030b600600d1001c002d010500340303110480c11500a4025000540c140742e07030f0719008110480814200362034060b42da5130307105410030703060002070512021070080001c1c10018841e03200003600420b4510351090051580090304401030a1803541d00b03088c038100802d00c1c0101c80320911104514031910040c0c0d4002ea440308200041324040c1981c0782c9181c08003920000200c4c0140b050381900100420f00050000c1020800c1419441070b0360 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 310311798 1250 310310548 310310551
    0x1e03080612031e19020d080a0c03090203010504030509100503100e090102090a08030a140309070e04021801060305040b18100b040207080c01050105040608070602061b07060e0604020406090b030309041a09 89
    0x2c10800f0114200801e0b4803001010743c0509940c1c030107031180c0c00d810000a00340b6000a480a090140c0710307d5200c42d00d610a611009443d60010000d002d02e0034642005046980311a501c0e034010013080300000c6d51540103c0880340501e0080a0043e0364510b40784401c202c1300d07000350000801355004c2202e10b66a5403607850381da01910320300020719614080c04401a040001000e4002d200d03500c103004101407540042803500440c1c071820081d24499031288002141322034480304210004500340001b0401e40e9050b4402ca2066110f54a590043d44a5841e0460800200100248a0340c0044407040b09240d8075000b02d1503003407001d0409030a082c101d603030310788d029008110140c1241e0340d19030040090f8901409040000c00f5400064800309041c100c00075140c001c020100c1880c00c1c0c44544c9807108603c020119200141c020b801000024074085880d80c4648040c0c8060384078501b016400300d4440c9440c03080c410001401002549000081c00c00d12001e0128014a010182030240041e0050744070040d813103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 310313048 1250 310311798 310311847
    0x203070609020d0221071e050f010201110c0c1005030f07140c01060608060405010b0a08040f0f020a0306020a020c030f1b030a050d0c12020604110f0a1a071e0308061203 74
    0x4040c0b000410401850809940d2007602280c0072032071947c1440310020281d1054400588000000443c80b034010307809001d0b90b40610380403020004246441c0700020402110004046800042520311002c0440c0d65002c1611110b1504042c1c902180c0d10078003881400000040d0303031768801c2c1803a254144443c2120f0017a030008002c900c2d01c1042003100d25151080901520b48403882504254095100a09401e4003c100a00180e4075940060070b021070300e10801101c0d68020b1280c4817454907468613a002c1d411040041e800752207910804121440c02042050502024038010001110240030170425002c0300c1601c0d03034050090301d40400104030180000f080010780c507140c24003448402e103480c00c6074041c014012011904540c090000044500315401c10f03c4d0030803916484903000c02000124881d0840d840680404030384900441d0780b814144c06001c105015046e03841d4541c4103c1c04090403148032040042c001080103000413024035010500c0302d52440101c04403804d16403a43c8840390180900b1410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 310314298 1250 310313048 310313089
    0x6090405130506070906080136020702060f0a0e0901150521130308100e1305030d0e0706030f050103050303010b0c0a0c06171521010e0709090519030203070609020d02 73
    0x60080c0347e0009a110b0040100320002d50600c02165049500c441d00d072160042802101f6113018244ca80c2501660383c0150000c101964034000ea0807001c001e503000140c4440821440c0507101010300e44800904c0c12a04442c035800d44500010342c049a166010707030820100840c6880e08664071241d0940c00c54440c9000032100e1103100c4c028207021b090420001d04008000c4a401c009000000f09819002c1d0045004110080d4803002c1c1e181550450107030b051040021441c01099101403040040c80f803080310341c1c03620200843c134048076000c01595400d00004d012644108010855111814003e0140c0340040080d00c01d450701c256513802400c1055841400050112561002c002146008030364100500c2e40c0e194004089800100351405940448040c0c1441404503208480100303401c06061295001c00391499241c07a001074000404d01c81005440030700c41e50240781c000e9a8000c89076601c0a40540055061412035500c03c40a441003a00890304000c84400e924010f8032526400380e00c00069402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 310315548 1250 310314298 310314317
    0xb15030f04030e0d0c0911070503070b1501020f0c19030c06020303010e0601030b0f102f070806040503070b09010605060d1b0e012705060310090e01020304020609040513050607 77
    0x300180302c0903440c841184900351480403c400119900b54841c1210000031020442505480a5030f0707048c01290700c094118000061441e0801180803a4644507c0e0310003003411402031404012681c032074090705480b40035070088640f82c8203880c1941c000c12809482c4a00d1145240e00da564030800403c160788440050b0344048014096000c1c104d149542c400d200b840d040107900d81c240f0005840c0700c110159580254401d0b13454480c0c042c800c07800803502107080ea05080045160303402c2800005452648800c86020712a07001c9104000400c81c2805550000000e40c00c00e0120b84406050030009001c6802c55940e505e0009401d4550707202500725080261800104064034402841f40550050b151104002495400c40040c1c3c1e001014265491130442c4c0308034488102c0100e07207101da89a508415130011001c41001000b00302d10f00400159210004103000c88031008000c2406d0740030540b0000c2d80314609101030902c40c20b1a42c071955201740c61800003020105c00391a003604000d02036400c4e1001400d41c00c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 310316798 1250 310315548 310315553
    0x3070b0703120f1a0409390b0301080706050c010213090204091d060a020c010902120a03090f060f11030d0c0e030c030f030304030c051c02030403120804020a090b15030f04 75
    0x1090034509150070400303020580c2100031000842d500c0408040c8141d07a1030034100d09114004c46407500314041d140c003050f81e040c510074526041d02d4090301d41e906000411440480c3d1482340b80f00356412100c510f002010b010f410441c0c03c1c0c0380f42e00148e030082d1481d9801e0000a40541c0c50801c200000d00888000507942d07405d01143c0760968900700c1212100d00d0101400c000385030b0000411580c0090140c80040e00c401a4494007030260000941c085d51192400700125110a00071500a5500c1e00c2030b101c001c511503a6010003900c2286902c1540d010410000b0030844060180f20b9140c8440c80700c40580345000c4001e081e642c211121034112800044010340d84a6050804124840070902c2c118020003401d1080c4102564a210050000701041414070a040402a0800182411441c0c50b00300702001c03004200003e40ea40c100340700540740c2e03101d034081242c01c2038040e1f481240525005040000b84c1410103003040c010342590701000381c1107241204008081144d000183d4000c2c05040e0151031030303081a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 310318048 1250 310316798 310316801
    0x150705011e0c02030c150a0e03030f0601200a0b06150c0a020a050103060b03182b020607090617070519120f050c04171c02010b01080f01050d030e03070b070312 70
    0x102e040c00e096500c00c0020035081e007400100725a00003180b043c0f80c24107030781c0c88109101420720502c00952500c0040148010b9049010380584034030002c3e0307200b901e05485001d0032124082c004010020541000049074041910326411a600081c003500070b80c00301c0c4000320045070541c4052000001d64024503004021898042030f503000518003407070180261030403c041c4135040d02c80507180c54001501c2d071004c0056410140100220306121482140d260150241202c1c11400e20322074060041c058100020061401580741d64140c40b1560b0742c0442c80890142c1030030070382d00050103000500409001303100d11260181c41c140c0c500d00e515078500060400b0500341006079404114100240d5003800100200b150b040780603641114106001178a581248402c1300c0d051060781401c10a20591079601110a80e070150030564000303200381da4840c90b55588005020a0840a000f404d61000b11020b190010a1140d1038015030010000c0c00c3e40c1c081661604807884070f40c000d240440104904034070260101c00907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 310319298 1250 310318048 310318061
    0xd050105090c01110304210b010605040e010f0608040b06030106030b0108030702330a14040303210902010e0432011d06010906050d091401050a0b010e060306150705011e 74
    0x30300b031003c41c1c0c5030055462034486c000c40c01a0280c540700d0700710042502d85038285402c159900141030160550315480002d085034081e001d2002540395090000800322042c0e281c000498055550b66802e94413a40d503980703800e410241540e6415034803510003201190000035a14000c0400c1001582d0320809841880590340c5808000070400885601e0143c21030040551401d04c1c1314010851591411034031030031b0301d90000042241e901070401140100805801c0358100070303400c8404005004180b044500300040da01e060600070300107034528004031001d091a030040088020300048035440801a41d001c00c8112039040da81c080400e40c0030004008012003642d0b4540680008000b0612038609440003800d161410312841c01081800034407603803464a00d034464440706a00c65118180c2c03009209013036007e85025210900c5c0c081c038104042a083d8043c0804401415000d40418110340d10070003004210351000301d80c0c1908030750402030900010000e1041e414581d420000301200360090340504401c8030107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 310320548 1250 310319298 310319323
    0x409150e071e0806070c0201020f0303090d031a030c010e030a15020a0905031605091e07020706080c07020a0302120111070c0306060f0501120e250302040b0103090b04200d05010509 79
    0x110b0b8105100041e070100300d80d5070210b441e090904600d000341c80102d1600c040c00e8a600141d000c04400c1c0720704002c000c90303140700100ca19038092144018040702030503101002e94040d48d250b80300811004040d4014a000c15002c400201552090403098941200d054845042e8215081d80041c054610b00d4221111001030300c8140d00030020208080f01c40c048004280c01140d22030655400025180c0701c0259080c4000c3e030f60764030035071407031301b40001c000e5982c1c15907015980110f90004009503480c0c2e01d20083d200450703001890a4616840e603004d0003a00c540d003540c8000366540b165650004047c80ca4000c0103668400c0c940090442d02c1c50800808a0701079800c0304040c000c4010b0701b00085d0b80e00c00c50034004009440e40002d811a040c040491420303110b0841c0c00c15030103c00200301c051207a08901c160490380281c0b028400240d150004404840c6c1c5641e00070b16005001d000301c0d001c1907200ca801403140081000040d46520039000180c01c0b541003407021640d507034440042240e04e4005118003a011030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 310321798 1250 310320548 310320599
    0x708240c0c060a0203130f08070203010f020f1605120f0315030c010f0e040b0306191404020d080c0a1e03021902100c02270f090f0304050409150e07 65
    0x146101d81d45941c1c000e00643d41c0d00d500400071610040b0b10254203101c0c15801013850907060850300d00402d00c0d42114105900c00c1d443c240d58030305000e419008a03a203189000542901c0c2c02d172440207200d03031104c1410054035075100e105103035810a1541d000500b13444544081e10340d101c1c5008050700e500140883c0d00079000360001380507071250b40d0b045041480d117182c0c60300340950f010941c00d01040080c04055003a0b507051241340240000f00c189000c06001c40817452a0078411001e0f90703800320200c103505403402500407042d0709802000c15a01030103030440380c040100b0741d1400300013078492481040c03c601240300c0d2884001400720405030100a0b91a8800809034104d03c201c0c2c0e03940014400303940d40301c2d0702024000c980c00c1c460110f55079006045000703040e800c1e10040319401800c80030001c5408031006205200c4ae540410405040050010384240b40d80c8000c51405051005107c003801c00707482c1c1151402d400302010101c0080303a001d10040c1c102540300501006240c80340010f0030401c0314078055101e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 310323048 1250 310321798 310321807
    0xc030301150c030c0204020f0d05150f01080c030112080412060605090105010c020a030206030601030603080705250305030d020f0705010c08040c0b0702030c06031513240b0306120708240c 82
    0x4e4201c911101201c0d0110b40c0140c503802c45508410491003051000395880f071500003081130308001200d0640c080380703040e50004d600e600810019911560140c0b80000e170040184010270406544202c2d9038503481c403035080035062559429070411340080081c0100e500035160001441035040034a0691300600003481c0110184040d50080b5115601314040640100000400a01c05034041c0e089000110780c0020b41960300d42c3d4500302540c0311545003503848401744200519100701c00c507145c0000d05407504040550701d05603640c41500004c3d803086d40c0c088001c0c0002e01520011440a109264000c00320785c03500340c5a45400d14100c0107003032841d040019204070610840003d620001140c5920420a54900c0e5498603800c4a440721400341c01d58882d0b02600b201540000320015812211500d1503100314000341d14107d0301c441c0340b006158024502c3c1800144002409407800c181540882c4103030b14207a030841911011200e040c248140a10086410344000c100c141f500355040700f85e0701c51250034625080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 310324298 1250 310323048 310323053
    0xa090506090f060c090f011d030d11070b1207030216020a08010504050d1107030b190510061b030e0d030e0a080d180e06010c06180f020102010e1c12110c030301150c 72
    0x40c003486c5601ca410821040032048501d41c003900c201066100c0202180c080f080c1c00c2c00000e1602c0f50456001ca9640540403000610802e11800d8031060414560290900ea031040000ca000350094140840b6080030310f14420096141c00f058040030300b034803c00114503803600f82030031880c112912032440208802840380010800d400f0038014180c9034410040c02d180c0d217880030f030103000951082d5619441460041400220101f202c418022a242500c91007404002da505091403070b42840d002802040e42e0b6600c5401901c0d011401c0c049580c800e091000041d142c04020540c000c080f6080304819034002c00d0114019900040f504613820541003400d0351403410010b01c16212500901038038144000d803c40c4208015454200c0c40a240c0c10144058001c581ea003440c000030600d02005034099460001155100d071004502e103e1904000700c10302d10554210b03c0101c81100d40818444d000e15510990900720044d10402010400441801103480354100342120410b010f03200e44c240c003170041084a00d0300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 310325548 1250 310324298 310324309
    0xa1a0102060c07050106080d0f120501030b01050913060507030605280b1c091209140d02060d140a051501020a0b01060e060403021c0606080a0f02090a090506090f060c09 74
    0x501042c60007a507500c0316058500103024140f5a00700b20600e0080380031540384107a00c40e4070403469595030b07507501c1d002e02030302100281211400c0c00041c1000710b003000180107904020308550341020141c170240d042c0c10b04c2078544404540d0281d0700680007a40700d08003042146001240c41e4201a0305085110340090a81d078091800e100c1403145560443c40401c108212020360b1a2020492003408001d110581040c80d002124078403550499010991003100850070341a0403490380d4040c10007030402c2460b00840e400304142500503400c4011100d8070b40c000c802c01c1e40101045680140c2c4451408601030511002e8400b100240c48191070441d4000d4011002150b214032915044a03502d040049611031500041041803045400184d045100703a902014410320b450901c80c9075a014500c200002900c0d0701d5038540303501b2003020103042ca280d40859600546003424005400c401d4400c00027450703200c140c1d606130038840121145001c58201d810b0389000504140103081d48218a00340c007500d0b102c4c0e810300055 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 310326798 1250 310325548 310325551
    0xf030305041106042d0b0f031e04200303160f051207031d0a090e03030a110c0a0201051b0616120c0f0809010e12180901060f050f130605030a1a010206 66
    0x403500001705841500600212807a20040c01d0300000140e52010f004401610301e0348142d5801082c00301181ca5813206100f400714042c0903030f5000c030040300c0340c0f80c0511100510001088019902d8001004824241342040c200117440c2c0703102e401c11039a81803081c20041e0901442c00305040703406008011480000b503000302e444c00c50388104140d920b00c00c10301c840800c003020036603003042e0021403602c0940000701d031000020314850341d0944018401185601e400d40703494000c6050f1400c5075407022060b0401580030b0005058608040f034a2403441d0401044001e02e090b50170340e00401d95641c00300c05202920350182d81c1c10341c1020340207414041c01100e603078014100d080d0300705074004101c82c1e01c0c003003005a1401e400c01e0140d8102c00b011603100035118076415140d03074031218469403d48894500c41c60103081030640241202c20301d8580039942c01d04c03030f4400c0d2400e0348001180a0351220800c0280000c070103040302500076208540e00e8540f81c0c5405c40804c81200c0c1e20386442210810426401c070712903030740040e845 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 310328048 1250 310326798 310326839
    0x4050105070b1012030503040b0603070305030f09151303150509100b0613080c0f091e0702190308061201091104020901030b041103070f08070806010c0206070f03030504110604 77
    0x142c0d29660b11542c1d810700088a4001403015800c03088890103266205001d140124001e000c0404561036a60406079201c2c0540300080c007540003844411010f850040c05031040c100c000d0f104c0c48200480800074403084d400a080d42c0400850050f060040c842001c441758841c503e500001c1059050428003665181480c455840314503441d441c108560380c4460f02a00c0b629060485000c00e2141c9400c100da490f10030401d80d103030040680c19120802c0307161a001c0140107a00c80e1550541d9018459144400814000c044605502c180d11110030504801e030303010000309000e0340d650350300342c00d018040000480783c42106001c40d030304001414010070004a40c42000b62012100180d540c1030402c0141c02500b2003030841603005203000000e01142002c00d00962090b110340e43c071001d0054103814241d030130707840035240c241c0024050000514154024115402c899000030001400d100d982c1d5540c064008a065080307001076119000c3c03004101548503210140c110403a00c19081900b0b2081d242c1244500d04042d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 310329298 1250 310328048 310328063
    0x308070c08070e07140f09060d06090e190b04050f0a05010c02190302061303180f15020102070c2d12030f0302040b0904180209010e250806010c0302100c020d090b0405010507 76
    0x80150401d11b0004864540401a150a80310201201104010080c0b44a0240d0407810a822410914004952503040d45000f000324040500913031600f03032082c04010030488541c401c1014100c80d4a4081141c044454030540020816403a200c800a081440541500001181200c0417000083d0003041d2240d10074100c0b148000018800d0030b040b81d002c00c65000b580c0201c0c2c400003002c6a030500c0c1440010a82c2d00d220580016451004012400c0384102500501151010201404103802e07402e2246094040c40c03541c40b00c00c01c07070a6844224402a40d00c09440800340821100415030000d43d0203202c98564241141010b140688881d218031921414601c90760752402090305400301d00421501954010744010915a100c403a15184075206490880281200900d0003141100b80d82c0c825511142a039a21401c1b42c4400005440d4100d10020032401e41c0104100201c44940b284104108501d10394002c011044043c5000b42480b4203e400007100403200300b02c14810b590f0040e04669600340d11146 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 310330548 1250 310329298 310329307
    0xb060102010f0e0109020117040b01050d03020a020415030b060306010303051605030705151e19050415110a120b0303220e070513050928060308070c08070e0714 70
    0x100e00500b82081e03200b00b842c0c9082c61008291105510120096100f80c03a0b9040c48441d154001c84403030421240208440c1e0604018415414008460610315101c0e004445a802c2158000f405030340488075441b80d100d048400c20002c1c08003d0b2007840e0005c03400e8005e44011350441e01d00030424403421540c0700e21844040c242e03804100040040300c420b81d40200603560900510301c07121070580015900c810943c1d20b4612020780040203454024004c402d61882d40e4002c0303110749041400780000034010b4075100724106001d41c5084450081001c296540904281d03548610b40300541a02c4003c40141c01061610101034000d40b000130403224410074044c07044140e0b0304594901116030301e00e40c00610105c40030000b4030044030b07001806003c510158400c102c0c213090f01e810600c8040c40080700c1c2192002c8624408882442040540c09402075030988003145454480e01e40b41525441841c00710f40c45d18020904000c1c24000f481800040e1200f01c003145043d040c00c05000300030349040760005c1c0c80d5410020b03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 310331798 1250 310330548 310330561
    0x506190c08011a070503030c0424080601030b01050702090a0c080705070c030b1b0c0f0705090f070c062909070806030607030507020c04091a06060a1403190e1006210b 73
    0x195000c44da800011246d0300d25040c640d000250708a4402c801d00c1850451541e505c009140303910782c9011400d0303900d4044958a030001100600706020005040c0041004a803016031580070550b07105401000d800301da81481c0101c0101890300c01400781c1c00f0440140031110015078032010900450307400101c0000b40391a003010040520b80d6200d00841480000904200400801304441c0d6a00d805041528045035a41040c4182e00c00704544020b981c800050010340054000c110001c0214010040080d001c80308c00840211429141601d1288144203c1040301524007132030842e50024003894410402c0c1045c602080da00e59003d84030030241911280080c003418820082c03c81c00d001d00801c14040d800660824a030041602020340d0940704004000442a0808030700719544041c051361801c24046510317aa40b0302c50703000a002e03501407021071407135107104501600480c004000c8a0014104081086840404943c0154480792803a507461f51054140700d9400d06001c841074210000c0c0704140d441c1d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 310333048 1250 310331798 310331849
    0x6081f230f18040c0e15010309060605030304060201020d0501080a0c05060a121b020f1203060d081e03090f010915180209070f0f050304020f060a120204030506190c0801 74
    0x1080d03610303000000d22000000c0b02d41511809030141d0b01444c00f0148098840403040a4810300320f0722544920590000c0d1507095100b640440440c80c05120000341560f105c0d400a81568441d503c40c20050390041000c009030145031060b5401400b280740107084c90744842e51010f07501070862041030310900d000b05131411201c0c058801028080c201c14410804a00f0b840310020580030040f40d414014482d02510f03036200c9000080042401003550700c030b5410741d0750394010030450b0341d4041d90132203c541040c0602041d1145840c2035841d00010032681640701d15103108001d10300800a440904c0c1a818242c2940104221008444a0383c0c1440000304d020600c48804001826554400940152141c0104100e40354031618542141240f555000d03038504c1c114200710707568081610301035400b0300071001c036107030314030740400146070a9000d4200b060034543c145120800b240c22580c402d580980118041009034541c03101d0368610580c80007020441449100c200800060741400395aa0354a1501c800304824040c0d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 310334298 1250 310333048 310333069
    0x120109051b0a0801021215030a3504090605040e03040b0d1508030a0c03020106050118050607260910091202040504050c060a03021e0a0c08160c06081f23 67
    0x483d8025036581400306800c0c1c2807018125803603401c008040d21040190b29005c1448104c460304010182c942d482d03d814221176000030400c50f03180f16804280910441031005c0301400041c501000005102ca00c1c02c1c05000607100702c2106e00419130002c01050241142c82000c0d62003003044020005070b591103007464088241d07490b0b081000725100211300b8100b40b0b0390064244e00720a120758002e1204503520300044d1000f2400c013041000c1c0e0b58030281d081c011401c000000c1c2181314040c0c4480442502c841c209a206102c1400782a01510000121404141050107800c40f50b0462468009031a528107c0a06825285450020310840c3c481c004101030007030400008021b0080206000d50356541d03103d002d00254000105540308020266145040c180c060007501c446940c99150880749444c9036070b40030701c194882501c030010918001ba02c40041030003640f00b03001800c0309440d814181d00317046082d000f04000000743c018600c0b03035040b0107100003101a114200740c02e0502c0208020004440700040c00c0308403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 310335548 1250 310334298 310334309
    0x810090609080d1a0a051302070501150b0a090b031005010c0302010b130213120203030a1b080301030312051f0b0c1905060105090f04020a060f0509130b120109051b0a 73
    0x60128188903c56000d5000000d0140884d8403151007841c104103011650019200700d036449442501281840002c6030000c160440c810400065600700c480700e200c2c0c4814507508628030400c0082100707104a81c2000460000d418021100390071454120301030500c904203401001d0400c0409850101058000d40014509403002400d0a1030380a41e03c0240c0029000703900c40013405008500b00013144100c40401014881c2c0150244d07290800001c000d44101038509583c2c0124079440b40d092011076030210145028600c240d49036001d081d0b015a04005503903000d480c1418241d81100e60658035440d01c050311b0304a5036084080c544581080e044142004520a00e0701d20038804644028104030001ca0b10758140c07a002c5581d40c0c204e4962000400d89501d003298025040b00394407070240000c1d070107950740c1c034001c1c0c40343d280c0345142201c80c40102d0640b20391385001e503000315150888000285000820200d0008410008006004450311403941e00e1001030103004100c4410107441d400791b100c05900102510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 310336798 1250 310335548 310335563
    0x60901180b0a0909050402032503050303070c02040614030c041d01020408032808010b030a060305100506270f0c16110117011811090a03030207140102010203010810090609 75
    0x25a141165055540b049103840005040c01c403000c00c8a00d8240300740303405541c014000340304012001000b00120000400b0035401d43c00c900310000000741d02000210301c1660683e545a00c8801c0c588144419602140c11041042540042500d425100010400c204240444011a60038100c540f02494441c1040c2100ba9a500019012030b1260000bc028a8014110075800b0420707410141000721480022040500003410b5000400c00e50303140340084d54011200030400904641c1d290364403807400c00000001100390742c44908102207464510441c00f565801108d105c88200b0440c0100400e10300024403070943c0052440c04600f20000d00c0741070728140c1d40070081c1010000c26604200c9185903510380341d00d000841c1850f0302c902c914203051000b07040380c001c00c2801d010510070300d41c2140a00b4014880c18030350032040c030481090743d80c0d0400e400d00960198014000041c00d00d01025102d081000320700e03056a0042004006a480010b4a08001809090001540021882e0150203014441c1e0082d1002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 310338048 1250 310336798 310336847
    0x4090303021911070e06130209030709020d0905060f13060504140d09300f06090c0906080601120f020d030e040501030c06030e0a050d0e150703020303040201120e0a02060901 76
    0x60b411201e070f81d0501c0001412078115035902d20b2940080f000c100ca815402c10960310034403100300c180d600500300c03202004080e6a911500d0b04088030490f00f0200c14880819201da002d44248401407080c5500100d4005140289160034018041410407820008203220355400000d41400b4081c01050700b18015001130340d10398064140000c0a00030240590803803030313100b80000d440e81030395940b010319080c0710885505681c0003a6210400c000c168008250342203900d0b40b09020014080c0051a0003404021100241050038405100d24082050f042000700c440307444825000b00e80103c3d1089050399048402124a1000749000c8811120102070381e500542020004800c03c4000603181d4160790f041c0d0303002c0100b0982c0e010000d1b0b98038000301000c1d0154205c0070900f03a070240305d40102c5070703502c8014000028105180070640781d954007040b0143c0058002100740003c56a00c0b85401009491103c0140311009688487d030ba146e0044a07402486041c00040540003079004090541e03240e4105810003211 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 310339298 1250 310338048 310338097
    0x30c01110f06010b1917061e1504090e01090f0809060d020c030a112d03040305120d1d0d051b030a020f060a0c08010b03040516080a0606140f0409030302 67
    0x150004c005c0300704084404071920803510700c1070700303096054420708050141a031a05400e0100303800c00060704000804140c031070443c40f0f480c2c0542c0c1c0c28129200000700d42c0e0f141e1030b0083c500100c0d039013922080d400d40d051611060118100c1d607940c900d0b4540040707003982d81d618860300081680c0305000c2d9181c542c6001040184051202001902c440206522070300c0071403040c5400380f600d4603034038400d00d94000305855803280142c080c80303c068090408181203924181c1c0b641c481c1450500100341440c1d454800040c1401102c9040c02109003680510b40c211200c80510a000340d1501245001c280030024081480740407140d20007450201e10358103030b007901d03954203141c40025100e0844e00c00c202c1c4603104000106402d0300040c803035000d10500541d10b8050590900180c5215903002820544039440340400e8074201e520854005001441040300a1001100c18500a8107550007a0f00904801544620030603417601c40c0321801001135400c503000a0400c1640c9020b40c024010001c51194840762240134128 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 310340548 1250 310339298 310339319
    0x18030302071203180b101205010509070501021609110d0905010b0f010f120504020f04050718060212040509180d0c020f060c190f1209030201120605030c01110f0601 72
    0xd214001c0d0500140081030060980644496135907004800c0b401c844400d0104171942c6803903070004802c030100c1030840ea1701c0580c0d40c00b1041c1c80d00151030b0ba03550340041c0284c4030810041c1d50000d107020300240802c0011500030300302150381c5105009800c0c7d100e040c0d02595490090845400207184a001c1160401c00c0c24800d000301819a401805400c190410114541c05a01000115022a616880aa5105070690b0b0103404040d00490700642c100040310713001da5550107200c2c1700c0c0b001c1d90b80700f040d0440407445108851501d5400740007550081d2011001414102d0121815540d00703885203a4a034460071103451525a014140000d6400307600c10190095620030750a00060303000712a0b00c050f801c0c21000300140c61162031190119a40f002d6001c060002509008110403409448141180003581d1030307010704c07240c90070309440001c5c02c014000d00442da00440402080035464100300301d11070924003c2580c500584509038144440c0941101c2264001c000014000001d502695080d5039120f42451 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 310341798 1250 310340548 310340557
    0x31f0510030c0e01140f09010c050105181b030a0b0c0c0d0e03011a0d0201030504031e0c140a030f080603030d061e0815010311010e1e0306152218030302 67
    0x10000f212107480b1561980f090344821444100d00ca05240b804007a200f8403000c503481324981505108062012601298084c860309229101080701c0005a048c4403100130b0a00301444048440519503601d901115200002c60210003544100c00800a489555401d007260098540ca000d45109203750100f2507a0303ca007642d924002c0c00c0c0c009000241c1030103840035403030b0b150480e00d9030406005402c1001541c4a43c101680280c045d0400040b1a11100f543c0041d144000352124045080c68803403100300300d048020625200706074005442e50312031542d00200800308000145003041490800303d501c595041c0116941e80001c46030030800311383d07500042c10883c001c03601c030b85004040d940700001ea504008500500c200f0000c403403455190b030940e42c1e6065000740100c1c0d803904000c820028015591a032040506840f140706c1c40b51040d9100040802d03262040051000b5030181c03810341c0e038000036200c00d0403290004111001500803031651102ca0001001c0c030304c1c00020714084c0c4000f01014903416a0080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 310343048 1250 310341798 310341821
    0x114130609051203090913020d050705010e100f110c04020414040606020304030c03120c0c170f0106120f050a0b0c22050904060509100c02010b01030605040e03031f051003 75
    0x4a050781c0e00d100b00100708030f070007000703121607041044600854070703100d034034140e211b48402c80f0824041c0807074010645468120710111200d41c8124014440c1c5e68014070b130a00d0340c0c10204c60039000c07e4220b200c01031031030701111a10814800d01c010001008801801002c7c031a0300003030011500c9035039270b64099230305400030b4224a0299242c414007150a03840441100c060300c1d04540444a0145940e44240c2c0c0803418082d0b034800c0081d000796450001e02c100c0701110042c1010b80920080c2c46054492500740854441c0c0b0318541d07032501100304441c4898150544130140c21640c0e080c045815801c1690900e25555001080c11205208000d9050f01c1d281c041d180058a00100700800240c035030104c00b40b81174a0040507806580c0b040000c0004070150403841d4840610b0b429903e090a401d00070100340d8050129600140c0d4441005420650307252180c00b0007014201c50038000c011400940e20740320320010b4884521540704240c0b1008184501404500501025001c0032500e010600000d00070410b10201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 310344298 1250 310343048 310343057
    0x30720150c04030209010614071a0403020c1e01030b030a080a03090c0f1406031504060b09041a0607060534090803030f0117010b090a020d180b0402060901141306 71
    0x40380c08000400142c50030340750f01600801080c0d003000300035a045141e075200b19080c100108445000903000110460a8002c620403210076402c043c6070107402c20348480c141d85d0242d130a07080031120b9520b00c05841c0c80303100028200091314403400c0c40440d04268920f503010707202e80030005080c5045541a40446411801aa0030090349500e03a4038144c500315a1f4491841c5c2d40054041d251401e2074010001c50708010704681906294064001003410ba56980d40704000301100410598541c0c281406042020001040484410b01000c0001840c900403000c0140c64035a0700c1d03000540e5828415400042050107900035150401d0240601120a540000c4000058030319440003950744000419203002d01c840815520352a800d10f02c0600000240308034185d055907c444440c155915108122401900d0065002d81d03188800960322050301c0d48101400c1203502d88880d1040441e01262400d50810350480384a55103140d48030040b21000850a002520100000b50b82003034480d00005400c102c448c103407034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 310345548 1250 310344298 310344301
    0xc0909020f041d0c1801110d02010e0f0f0601090b0402040803040e01140d0f030c051c030518030403030f030b13020a03091110050403020112060b0703051e130b03072015 74
    0x101a601d001c4e01d00c81c0100c40c3c140041c5840681c0c20100303402840061514040b03003d1030f11806440e00d1180300351140980d550310014890000300341b210071400701e1000700501c0150121000d4541ea4001480380d1600d955580c03109202070343c2d07a41c0446004280c2c0ca000c494545c0e032640183c3d01c00ca4800c0c45043d41062003032800d000316051400000102e660819545841c6822540b000c0d100796415040c2202e4038010782c0040d404110441c285450f1103000ca550000701072404201d106003884a4400c504400c0d4800c2c4030401c00a91300000060903180c4601d070208000c0410b1000c5107001c01c00426240c5400c0c00401c42c03812065140c5d00c0310915034003c80503101e641c4580018000103402e100185400500104001c4c4095409110301c0902d0f034000210008510381c1e140241d0001ea005040e04400148001500361401517458a60b0724031040c1d031f424280c0c075011030040e07021021721180c0f0624011400200c00640f40c207018150f1246080b0140c4100d480080d10300380e140b5150002e003281420809050300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 310346798 1250 310345548 310345589
    0x80d0801090501031a130206180f04110901050f1215040b04060b0306010507032327010206061e0414011806120f0c0b0703170f06130c0909020f04 64
    0xa114100c0703805c8407031210303001604d210f078210b1a803000f0903022010700440c03855001a150f8000500c582c1e200e59020502c0002500c0801129071010a07202c0d02c110300b070156204101300543c04071100741000b42000b81d40c2c2d10348201c0255040c0901580120000c01120403c602e02c80d110108a0319214221000c00c5462101c1d82003208072034280c0200b00c10b0103018400141254015030040c07100038020308060b410100501e00c40031900e03000b1950501c0ca0030000c0b802000303107141c46100c48a8000d110064014070324068000075507841000305598415501414409800c0e03400c4028507209007000340c0306002c007140032400d20320790507020b00c61b52220f004000b07149024425580700300010f80d02c5642c0d125840240755210015205204401501d850100810004039803d8200c014420390b4403c3d00c603181441c1740c02541001060004244100780582c08040024a9854001c460009558601c000500f80c078200c2007110722040d80e400c003401c0d0f00d10000c4c064801600c0b00c80600200c0d404462461028907058 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 310348048 1250 310346798 310346801
    0x9030201020d0e15070e0a0f03140c01080f06010e04020d0e0a02030f0c01020a0b0603120a270608070c030302270a050612010905130206120601031406010c031d0406080d080109 77
    0x1113050700d009a1002c100301d80d00c120a00c420000b00105800d04164940700c40101408050340100c03054114010b5401e15902c1c1400400c21880f401d00700120107142004a1403c9400018510f40c10001d5a0b0b18412155481e82e040d02c00c008180d541c00c00540265076070899a550300d5802c141d1003445201c929481512001604c0122414181e01400206c4910340c0c84d08400301000e8182640750240102041403c003400c00038210140d16a41e90980700812061541000000070005040426542c4010700031590000e8003503400c800c0030310b001c10074039050b130070220001c3c0102c0d281510b0910b40c2c1c0e0304803031000554039414284500111000709815988200b00700c000e100b11224195420f20356401003091021650040e94041c40d040034030101d03400d00d41c1c0000c0d00d652080d05c2501044042109105441d40d041c410222401c0318814065400e04080d80060215642c1c001c00408008103050f4040d040c601c2840803001c1c0001c00782c81407122586034020140c031102040803020001d030310700d000000d404415 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 310349298 1250 310348048 310348063
    0x5150a02031611010204150513090204050a0e040c0302031c080c091f020c030604061b0206061309021804050601150921020f0a0e450a0609030201020d0e 67
    0x102c00d04401c9203502000e09943e100a001c1d042c036903556081c04001409000c001c5101480e50700b5584d8603540e10809101d01c20044d920b9000b138121144140b206203c2c0d40c07940031015082e01c030822000841642e481c83c0003000062590002034041c0500c9209140c4468403000c000000704554481c0c0146a548003c24825406502d44943d0701c50710440040800c41c11b00c1e0150502c480c00c40c81030300e0072100e5000120b031429605a804865461352218020a4001e420064007418150361000e0a01801c1c00c20005445c0c09049046007005540d800f0350308110f69899913aa903105142ca50141140d02c1e090030400d407190024420b00c0f541425003042d4424052048090500f66511803000c1100c040c8503803512900b940c0f01e15804c80c0c1091400310f140601c1c2d9281041503000346848584036025142511104202101660008078469010280840c80644980840700021035100b4110314039807411021920b410508031010f40404c6c0382c0015032041c10350640040c500c0c404050424400c440c240c0721042c0d80c0b40748 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 310350548 1250 310349298 310349311
    0x30f06060307062d2c2416050307050706080403020d081009090f060e070509060415050616031803052e141b090a030b04050a06020705150a0203 63
    0x1001c00140f115901031303102c1840c040c40030281486030011546441941c0e859100082c00420707621105039880844140001e65600100100d15203508800c1010924502c18544d407110100c2c8040c841040750410a07081d070b25202c03004003030034200030f506003003003612a1300026040d41e17103020303d200100310a40525170040c042d42c0d040e40140451a21140200c42004001c3d059040006020700c0004600c0001d0184068490282001050100c03041c54080212111003000301525001000100240e83c0d03001d0a440d800700080d14082081c0610400707440040481c5e8010943c412804110081c24801c402e01c8015858800d84845540800000080c000d42090384001003c80d8810030500b116507244030404045642c044841c0c02c0342c420010b48580580d50040041c44207100c4034402c01000d5655240c40c800700071105407405140c02e840c440410700401640c000607010b8400070000c10704000c0200300307080309560400800c64440019283c000d80320b00702ca0100c0c403100d2200c3c20210700c2c100c00764802ca900885 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 310351798 1250 310350548 310350553
    0x5090f040c09180204030c030302030c010c080106020703170c07030b150f09060d0507030b01090213050609150f040b0d0c120b03060a09020303040b210109020708091c050f0309030f060603 82
    0x20320302002074038003c8924042c414555001d01000000440701d14200e03002d94401e8001e5600c0d000440300540c03c403910f0408100c10000040300401500da008102c90003501d401142c802c0c0d10002c8550f440845114a224419a610462600000348034410719501d01842c0104131625820313250b401003260244000d90311540c821f0b519008a49c1a00d401942801240e200c2c42c2903c0e4800c1d5203856905c004002607000c462110f4000034203510f40210350444c04046e00d4111750282c140482100400c002100d4940310fa082c1e03800000d80302c080389981e8016a80100041c461140c0e0303400044250b180a0013048001d07002185801120704811005805028541c0001500800e215a03504540d02c0242c40f08080c1683c040c00104008902c0e80240401060032680480c6c900c40d5480300d6001401e0644016071041c000c1d94410301c03c131400100d10104949003031104503000841841d00c10060203184407074800c010040e01c24041c048001c0c010209c09006804022010340b400420300b801c0944c3c45242c11540c81e649078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 310353048 1250 310351798 310351817
    0x7030e12030121150903050315120c012003040801061802030615030604021c0c020f0f120a030f0212040302010606030209061b0f0607080f07173405090f040c 69
    0x490300540801803801014400c0c84580004c0611046604c99042031b40040c070700108100d0607080c10744904524000a4a106551180d11894107854000d01e16104e41040910710000a0009101200074611318400c82900e0f5600e90300d48549008001031310480b41c103a080a44440d031501414070075603104d10006071840d02c1180000e4191384c000d40c002450a94480e900303004421034240550030f6034148810710b440014008104d504081d182522980d25002c0301d030b000f0300d0580300d011030204407200e24240a24140e511200000b06c15400b8101076407124255a101141c0008120003844545014500a070000c1003126203c4100304c090384074016445030021410408854441140800d265010f030080094407081404000b01c281031030826070703030000001c0895091085400007a1225600141130b400c003240711050f41a0810b524140003401c1d942c1c400a5464005510041c400008081001a030030200d40c0b030071042c1003d0b0142d00400302d80ca004841145c812055030800d8425a41805415100d05550 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 310354298 1250 310353048 310353089
    0x40506070512060f04020d0c2304061409180a0c11030408030702060304300201060e0403080a0c111f06121e080405040207060b040f0c08060d020103090b07030e120301 73
    0x13002012000f107400c960300700b004450200851240384001c044558945490300c8090031142e1086407040d1030030085150401c410880c007038200c1c1c0c1da590040c0100d04640e0b103030701d00d5400003016100c0103d14581c14034048030410000c550550b0240b0441011510348480c102561891603540f800303a030152445580c400c105600241c80e00e0303805182e025100c4c070081000c04408031a01c07010480111040f45000700b0740100707500e001d42c080c01288050440d0050b0740c1a0341ca0240c0307008002e21400b400301c08c4ca4541d80c29150354031602c02c2400203007070344010341240c0768040e90030511110341c0a21014407112929151000c02c8416100c403108450503085074030b1580180e02d4040b100c0400d01d01d82e0082704e80d228200300000712511503002400c0a14010b610000d000c0d001c04090105540d2001c0c1d500703001c81d10b824031400031241c000000b260404030075204020007011a100507401000c0c00134010b0300c0b1104150400003a9507150304151107d0780e0020039191112110122809940428055a10803041d00042c0c00390 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 310355548 1250 310354298 310354309
    0x7020d0806130e03040305070302090a0203040c0902030a020c0a0507060212030f010b090d050d0327020d140a0209011202030f030c03030f0c16201903060c05040e01060804050607051206 81
    0x10b0125004005050310140f96850300e190300a520407141c039000407904009501c0c00018950b171082c4080c400f5440c6147c50350b12030740003d0320f90144a00459000c40425840982907060b02c40d203041749021a9408402403c000f81d0342c1c2070a10400b40144243d28441146031000410369000b0f95500000134143d9080c224280f903250000c04c011070b00304019a02e1303030001c02c10400480545010b652000500b0450902150080f08001140700c004080c40e20342c2800142c468905101c41f05801c0354420144803d01c0260700c1c10044d940e54043d500408103c00030413495910902112010300c01c40c102c1b046180705100081d264054104c40d103195030000d100144841d1401c100c40d80d40040460340320340c6045010803891604031a010401d5904a0125800c07224035110b0b101808a45035045a13912107008076803081c080c000105000c0100303800e8603100841c09880c00741c0c050b64081c000501281002e9a141c0303a0081c03800008681c15519441040c010030a400c0c0034804a41c078061101c4949502c030b5a44205100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 310356798 1250 310355548 310355569
    0x402090105091e03070e070306061b121413080d14040e1012061401090204080304060e060405120f010506100f050c0a08042706060c02090c09060304110907020d0806 72
    0x20300000a454143c02590b8061122a001d007000c01e01e105000c2c1040c2d5801001c55050382c00c00010321100a0341528881c000c0e0481c1c01e03044c4e0f4400c0442668a10b8034000311030280119210900042010a10844500407174484800f610910400c580807020220000c80d0460a41c200400c1c6203d0700300018441142e043c5082944a000110f0a200d62642c0700015420210f01080640300160343e40641100180c041c2c0c010781c01046840000d50405051408003616481503110340c3c401e0203070841100701d40e070b12140c0c10344001303007402448140030b40820b07141c084d02e403004512080c000d0752905c4002105490725280703054403038031555590354440144280903240c55201d040841440e110b883c0700c00c00020100c40c024005011600d072003500080300700740800d406140e000d140000160414006200407036010018441603601219500007985400f0803450719845070b00c00b41c0b500300d04000104028004075040c4000450f0082c1ca2007030b415503a00c50100d0300c444400c4200400110342c6404101545003020006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 310358048 1250 310356798 310356829
    0x10501050f070f080a09081501060212180409060618020310050f01021e0c0f040603051005070912050102090a08033603150405060705042108041211040b040209010509 73
    0x1c00e2101e405403240301440e0485c1c0405000100b10765018000c2c941e080c4690f600da9040120700764a503506243d8065102c0494a100c50004103002c19025681300d10440d411078042000f80003040314110b6420a880900800d02600128260f40710301540201c20034070803217106203580004200038504000030403440c5664030746098110300c0394960400304030714942540c80500c030b960070041640d201e803041032090180784500c41074070680c5840402c102113040401d0300c4490300001d03d000141030303070340120079100ca07002030b0084104003810116290070448150300404407020211122811950344544150750382c89030018a038104040885a11408211403442d8004000d030940441c80202c2000040703440c09903850840d00032660f000307044c8424020180701058002080e8504140341c10704000c20400581104c40e0401c44502500c00000705205d02c060640d8040c040b6146521180c96150910b04030648208840a02c40d40c030f065201030440c60039200b10f8003682010b84680c0e042070350f0001006200f5043d000398 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 310359298 1250 310358048 310358063
    0x102030c0a0b0703021b0f0f0a020913030c1703070923010c032309040c02061303050a05120c07410c090106200703080405060c150c0a080f010501050f07 67
    0xa4880610699480400d1b40310003001000d254494038409482c010503d100302d80306801004444025803501550716610500148000303a0301041c0345411aa241d80c0120094254440c0755101525218420019030188151395501c8070100d860b01288809205503051490a8203461181011654003900c503008800d802420420041e44031811481c1c444000d207507a10584000000e4188007500c0d1a115400390184148024003941c5003025000084c402c80003800390501002290000c5070911540895034036800c140008185410085150701080d0880300d0704543c0030100c04496032800c02c0d0081201c290290f24602550b580c0c4080480241d1005442103411142c001d59a12152039100c241c035441c000c0440307540c2d030b035902c2e6145207152451900301c0d81c03d4003c0b5000143d00304045905081034030305980c0c0440e1555a9095071071401c07441c0440d60440d4402c495030550410140351883c0e006811340c0344c69a00c03215241c0d990b0310515504802d090050601140c0103001c130200b04c040300e070042c140301e81c400c111 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 310360548 1250 310359298 310359307
    0xb16060b04060317071b03020a0501140c16060e010f02030412060e1b131503120e0d0804050a08070806010308090d08030a0b0a0803030403021e0a0b0a02030403030b0102030c0a0b070302 81
    0x10f81320301c00d031201c1350310300c441c802c0024068080002c8550030356000c8001101807040359083da070010b009000700c0d115240c10000041040d0800c5a002c204407804224100c0450348401c0e600203454146d02414030400e030200b00c401c5103466865000e5464103060100c40c3e80603514150074210090414540c5080944082c0d03500c8221050b511001c010040e0071884c0c4100342d000c041c01040030400d180e40100b6040300e00358180b00103c0130000034010510181c0380e00810703024031078204010455540201c0010715600c40c40c080c00031414448500010426502c2c19260748044544607284035130340781e085218060565010800400c081800b01c40601141a0018115001441705031a03d8049401c2520f40c40f03101c643d5455066040d00e00f07129400014000000994110302d0b00782c40181d200c504940c3e2546044915048101429509008229000303520880c960b0303581c109200c0c4070000350422207040f4042860300d0361031030440d0300001c10795140148903402017485914940d030f515540344024165006040e002e00c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 310361798 1250 310360548 310360553
    0x402090717090606030610060f050306012a0b1f0302131b080a060e0411090402040e07090504060501080f03220909030f020c06090604050607050f0d12060b16060b040603 74
    0x814031400340c99080300804681c04e00c0c000300b500381103000c0c01440d00b415040070104070050b00513800c84c100b03000a080458480d501d800c0160381e03803500d010321201d01c44203018000341d05103485240307000c6850159204100580d214a080310007007072040012403a1075130102c0c00b00300504d080c8260402090384840041140120140000c103120300c0c64006602191900c001c0240d00d1203a0f204441c010440c0484a10305414103071101450014604e842e1800317000508001815506c6903004103603006d1081341261901503541700c0340c1300200f0301070350200c60060400b000020000d000051043d01d03004404080c5180200342c0340070104181c0c03a0b00d1403240da0341d900200014034240320310076603505c280030351100c0340c0b88111014001c0c01c02c6d17000e00100f4441e0340240721420280c0c80d48402c0d50191441034400035511041c90a1203881c0184444104940f8032035026180b081c140c3c8800506050b10740060b0500501c1d88510868109018640c0e4603c900c0a800c000e80c07010030202d8000306104280600000307652a103a8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 310363048 1250 310361798 310361837
    0x3010f050709061e1b0203070e0916050306090d0c05010f0c08010305012f0f09040213240e0609180124020307020f010809070f03150605040b01020604020907 69
    0x7180c40c44082440600100300f21504440d6140d11135400060880c110980018083d00c1c1040c0c000036000e00e0f4000030681411504c00b0441000545030380c0408181c00d10341140e1a99544602545900001d42c40b0031001405040008950b0b001e00013913006080c202506c600101d4501c015901c0640e015074a0780c40b485003a41462050307400303010300f99454081940c1582050350a4500c0c550822880300c1d103a9000300907034140200004100b201138100b00342d4503190031102c00b001d07000e200b041c158070620000e262094018a5540075084409115100c1ca180840c01c600080419a5442240c04900b540801c140c2500d03040c0c004205489000386440e00c032600328012084010b80903088107450705008660004041241003a40c1c2c1e022006200031440d01319030703070301284090310182d050070305226105011580003041030087c10013500301c51994414141d0340c1c0c2007000c1d500c0c01440c99034010300c1c90b01c80c02141c541401e00840c0c0388048182c0083c042515182e080c88de120500404401c1000420901e29104090740b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 310364298 1250 310363048 310363051
    0x15050714040b0702120f0615030703060e0105070311040f060c02040f0e0a0506130c090f06050303071b0e01030b060f120d0c062706020f3105090c040b0903010f05 71
    0x14a100b29207444561041c4042004a8107111015604c85d001d6910102c000081080c0e0240800031604d03000d00c000382c0481d1030030350250001440242400c80e000c41030601588a58030070b09460760180306c0303c004500c00102070711490003039400f01342c8014002c0c0301240c049c140e2522002c0c0b0140c030000b4402582c2c8082070880d118412200030b17039001842c281c07051000401040c1d07013100500c0720115244a403542c0340200ca80c228402d420301e540d1150511b54040d01c013a48007a00905000d4240c1c1d60354051881d140c85040d106101e21f82d4900c520b0040407a081c054203102c5070607640c2c0241141d9040d01d901c800c200303684400c50355582c0d100c05c0e0f00054156501080c4042410044c558a50003420080d82c94104140e902c40e031419010207160b01c20200f005480c0e806060660b0b50469801a940c0b929410321210030311074048218080740521082c09626102d080b40307000b85544101c0108030032a22101005601c480c25151040310000900c82844402c5a0400030418020300600004900d07104488030340c01d5590 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 310365548 1250 310364298 310364309
    0x8121b07230f030909060a0312090608091506190b0d02040306050109020c06130c08071508180c060c010b040608030901081f121407030c061b1505071404 67
    0x78402004051030040380c01100101d4141c102821880c469180000d80c2c9015890b2600d108240c244003141c11900c0f0b900c0004050354226121768000840301901826060340d9101e00c1000507a4030b400540c002c40086070340c0c0420107103c7d41c05e11141d181d6004006002e03182007134010080000d01e0002860300030403401070000041c2e00c0c0004d030715507165081200c21204140d100300422401000720f201c0790f0001184081c1d20512404408500300a28204012400016000310502c0c4c03260341c0740071401c50103d21210600502030750b5505d14550b6000a602d05602c0681004901da9200c2d1082d62003070714000016100d80c2004400000321040c200001406035015030b8020301c402e40001440703d119591042c09503500503110f0700a0281420041d200c400035100b00d12581e0f120440143c4442c04110f2070049001c00e0550103421103000c140c80741400c4011008600c20000495211fa8000b803440665010030341c11181c005840e0008900031b0290b5001900000300301c4020004895840a000e136001c3c1f014001911 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 310366798 1250 310365548 310365563
    0x70c062309070806090d1107151814010906051803030301090c030b01090e0c07030302070f05100b100503040602180d050d0e06040b16051e0c0f0a0308121b07 69
    0x410740c0440341402140d400203003060700301d84100700782520300091809504441e45086506060000c0b929030800c40303540c021020140000c0080155250321400041d01c0c01411407000c241583e50f90280c101d000c83c0102d09a01242c0c0b90070301009414024070140003608004136a01c00031401c40e04c0084c0c00d41c0c2c026000110380944e52900c01044643c1846506d2030980d01b0b003004c8050301d0410702074964412000340803080c3ca9200050350410944250151207213036512480313200320030501d4074100c0d0316101c07250792041e05540740561348503851500303902c04805544036440b0795240d42c43d162a072002a6001212112b90b83c403142c150060b040d1640d0341d040c183d09004130090710f49160800e4006110000001d04644145c0b07040c130091000200400446450810b440a180200e02d581c0c9401400d00304007100e01e522030b042026041140c0d042c00f080d508410201120781c0d441052040c020440109003500002d01040750138000e8036109807422400640000441c90041000da40d6155180c0482c0d101c0101140c0d01da = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 310368048 1250 310366798 310366801
    0x901171801063201050316050d020301120b0a0506100e0d0503160b0709050a1215060906030606050619140c1e0105090a15020a0e0301020a020109031e08070c0623 71
    0x48120381c420700300680700380c0d50710082e40a83c3d400080031808050504004017400150000341d890003170080326a03442c0120002d548960391803c0851925102038000d81e00c7c410501e0029955119238031606220310402400e00100303a044c01012102c00c1c0c01d509001e0b0f04080306080342c0340410400c01c085d04182c1d42225003078450003441d20300080c0c4031402600903001c0c8021004103000d5a503464020b00b0a0710700300300d10100403246c40c1c105000e80d14003a00710200c00c0d51810a0100301c003613140e0001c0080ea80960000d10103966900e007801402d01c00c4420a010715904840003000d00340c45030202d80304011a001510742000b50115090342070151003400e4004a10180aa07800d81034001e0080c25404160075010f413900640c242c0b243e101a1b480080030390781560f4001030b4402001d0042c0100540e851014000710340364a003400c0d01134000c2c43c41c5041607000c100340382d143c41e0080d004841140c1d00231900f69240c80c41a21101426a2046500c0d0700072150141c880e408141d4910403409000011000d600080c1640d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 310369298 1250 310368048 310368089
    0xf0c14130906030809121507080901020d09030e100e0a090c0c1502271e06130314060f09101806020c0d0906090605041e03050a0b0709050402090117180106 68
    0x20201c0b061b00030740003a006112150000b0740f43e1203500303900c1107590600c0d40705030b0749020201d4024030408100f0fa0030903281240100c1070661000107031130446401d40f9501031202c0790440c1038800000d0038070441c1c0c0c030481404080c030001c48240c01c41d000820442c00d00035002c542c25603800d00e4020303140ca40c40d550150b021440c2c65146090000c1c0b1540d002107040446005c00c0f800011518042503510f04642c2418400344012081e00c1c0e420494125140001e40c640a031a01d0b0300d010100104100005011072046901050b050943d80305442e0064480c44020001200e20a2295000e4102ca0040c401c4d540903e0507680c0116040740010306003102200040e01c0102110f43d0098101312103900441c040040700343d03042c084190003408482c19a005004500d1060101040400310703040c1c2074000400d903000d0f82400000704072640a40780d0103054507440b011540b40d20781301848100e00a9034800c6000451684403906408540446250802411b40a588414103c100c1c003d0a4030001d5000e1800102101c103020030307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 310370548 1250 310369298 310369309
    0xf050c1302070209070302030105010507060507110d080415050712110d060e0403021516030902060408010e2a0a0501030207170318010b0406030c0e07050712080a0f0c14130906030809 80
    0xc1c00017850408500b19414170000038001e0048a900a040d0b6079540b001c903000c00d00801e60080d04040c614100e1f8000a0f4a0600070440f850580b002c0f1038507804e495000b50414498064a4410b603507a075901a80c0c001c1070050140a403031806806402d60f103003040406a1110a402a100038246010341001c80e410710340383c000d01c1c01d03103002d8007105408440c509100c858010100c044c071480c552841e010a800c003080c00040c46e580701703503030080c849503203400000c200007400401d1011030500c4544070789500c22400c08030641903881844905900000302e030000d00440d03010798040c0c850ba902511441000d05c0c000c0840400e240e2080c0e600803414414003080088216090046401c0c0140980e0184515403a6a035907000c40441401240a154000c00005844a00c9482510f0a15400584000780f4121900010301650f40647c4c000c3c0100f4141600e46050421a01606c001000150b568940d00d128110604442ea005140c007089403841c8500300007041c0c0c0050040a02450090342641c1c0e03039140c81c104001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 310371798 1250 310370548 310370551
    0x61a07301d0105030a0f020903030a0341070201180506011e080c06030c0f031614120c0a050705070902040906051512040c03020405130c0602010e06040f050c1302070209 74
    0xd001c02628030440e0590780078041e80d8020a680d8004070303010409088900280c0100442c0c10303054400400d4051250b64190403926000d54007224a0101d07a201101c8000000f1520000d0034125460803100000e458514808030340c003004601c0001000074402c610140c2d207010f80340007030300c1e6907100d00014881c044401c0c4046043c000c0400281c04483d00c0d019400d03498a001c12a010300c9440088001808000c1c2d440071140820303000350a580d580d141230f0580f443c1c80001c4070303070342c070005020b05d03100d407a0005004080328401510302c4e40b40b0405683e481c004030256409905044100b02c02408240c000407401c01401024090f20100035817918240b0b10f0440c200c6481da401203100d4011184031300301c000d4404048820190301440f000b01140c2d5581440d04000200307900081d041032600b1704110704240b02003040000c20f4800c40141e0805951010101d0a88035242d504060640110001c28001340201410303421003031140c1c00f51003c4101501c000380e40c1c3c903c0d4403803100d07003150000707260400c501e4101c4549 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 310373048 1250 310371798 310371827
    0x105030304030f08070201200102030f1b070219090f0b040b1f1b0f03021c1e0503040c081911040603080a05360a09061a0730 55
    0x8606081c55900c1d50101100101005131003114005841029a440744084a4450034041a002200c06011b00b10314001e60040b1244103841c2c81c100c0200300c4110003000c1c00406400303180c240504000071502005400904d0280405000da40e40c000081c206000380140d0003c0c0340c0100b00040c0d2101100140700507184110002c6128101da1540010305e0b41030400310002010941c5400c108500e800e40075001220005c1c4405013401e01c41c1c500300c030b04060740041d1519103540d09082e11800394032824801d9441d90401071018401c091509000c5203001d00c140702440c0c1c094041c401e0342001d0341d91140820b040c16040d030038150941031403903070050070300c107101c1000d100c10300c4160f40c100709071443c64403000310310300074504007800f0000d00055441400720f180051040006101103030042d015894520760240415240b803d600810404200145000b401d00c00c40049441c182d480721032402d07a40c9080309503a030010004450352a0800590b000340d0449d82e4044c440201e4803400d65008031910035000e4034000482d61807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 310374298 1250 310373048 310373053
    0x905070e100e1e1f0e032a010905060a0c0501140109060302030d020d0918200901180f0603050c0d060806070801140d02041109060f03180303040b04110109150f0206010503 75
    0x4440d482c1c45441d01100c04000b1300b154003000c0a8400c400721040f03051294020392510a040410b6000000090038031001c010200c40d400c2c049241d480155500360143c801d880e070012080c0f004012141c081e240c40c01106200f400002010004000003d6002d2000e801c0307440b0080e99001c0030700443c10304200d00f12040309280020f240803000c4040040c268032085c05003212071400c00340648109102a041000b040941c4940340400c000200001a10380c3c2082c4000b0f80002d40100c10400001884d4100301d0a030b603009005246c1c2d807411300200754094600a003240780b02000c00c10002c58821020301c1241d02038141c04000e003c242c180510000d010f5001a0002140c42c1c00d54101e404441e0340c0c2c01c85100c02d05d0b60545d0702255030092072071802440e00a0000154000800042510706d004944d802544524003800b082e2456450810819940740021100200480060700224005c111898241e6184000524150b1750b03254030f603900198030a644c000c4007004524821124203086c0e4043c07108a000d44001d600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 310375548 1250 310374298 310374349
    0x60b03040503040524070b071b0c0b070f0507060f0311030f191d060a0f140f0c091806041b14071a1003050709020906040905070e100e 59
    0x560715164443c038402d10b131160526166025800b0a00d241190911150f00c6105403039080030304200d440d16a04848940010301401d402c0480d02401041501103550040c1e814104a401d040b40f544156020f150151009040c1518500008504003e0000076000c0d96a0b111200840c00340040c00350b4400000d038882d901014820000b45510000c0b0150703219194010189807468408054030040012420303c044091501440428034000060070900a401605040050640c1840510101c030080003840801074220300110b042224400501c40d0008031049031503252400050001e29140140c00d100038407800408100400c0e40f50600c00c400c418801810368800c4200c078008002d0403108c5003ca0403801e0140802d42c181481031080c005242d01403078005021035403c01c03001003001d00d00b0030312048032140300c0d04001003a071010301c0c02921343c00c840c0609900d09041c24051405c000e000c000304890100042c401030020300d940e400c04e580e03400322541c0c2c40300c504005200051114601604401d85c107a85030242 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 310376798 1250 310375548 310375553
    0x40b03060f040f020414090f090607080c16030c061401030c090e03070b090307150b010e04020901120903050c1501141c0507030516050f01090e130206071104060b0304 73
    0x142226800901140e20744040d14030980000e005100c25880c00b590300d4404540401d00303400040c1822034011084485014668416545d0340c1006012a0094402d40210f004108a14000c2030103a801c01069046203003440e00d034561004014100341000d50020764421106001d00c48030344a10f5041400c8060945219070554440017900c9007940309a054080c0d484100d00920041842070700e000540c40f0340010003c2c141028500e07075035080702d0070647d0054607480d00161000100e00c00c440741c3c0c24044c1c40d10748044042c801004029000380b100702c2d0600282000813421a402c030300c20300080b107110303846a80d21500360340d407480e140c910805440e4034000f000000500000180c444588900302085584040540e2150a4075031202840c2400034094480d80402008008000c40c0c1d48003a54035100c04590307840e0345c6000f0170245440c0c4443d403e02244c9a42810b00c40300145482850740301c8280500c8101c48403c0381d0108e180d55019500a0703d0030452040f410842d46420b0042c200200032242585086041c86d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 310378048 1250 310376798 310376819
    0x1b0a05060114040e06240306010f03080304060603050d1d040c020a08030a090b07021f11191e17060409152a0503061002030408100203091011180604 65
    0x18000c1d0400c0d40300a006840b07155480c1d422011081044c9000e580b46810504e54400382500c0102100e0b0850381101050308072030400045550494001100d05a48149541c550b0322a50344003420a0312240d0700c40030f010003c508100700111040c0e40c26642c0001074003034441d10908008060718818841c0782407008400c4000d600003035140303d090301f0104d002c2c0c1e41d465400705600100244d1100600306100202001070290700411420061294010310742552080c0f17449880454042007550100d40038184410b0280384441d112801941146060076101410040c9441c0d04008501180000003030400b201220420b2600002c1c07900000e081c1c5060010400f640d44040c41c0d683d202c80d1034102d40b5075442d0181e000003003040302c0d400e09016800521000500807080140264822141e55010311400025030500901c000b0803181151f68a8010308800700c1007003038a070083e601c0030f00169000d21425000e0f04440d2000d00c16811032500102506984d05c090840c1514040301d140d081d240710b290700303000c20841c140c0003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 310379298 1250 310378048 310378051
    0x10603050702030a1b020a06080a060f03020607110a050a180f050f0613091b08010e0607140d0b0a0602150c03040f080c0109060501030c0501031d0a1704090c051b0a0506 74
    0x11401e10320a1051220060308076034070041c05c0a0f5020052100c00101e15800500d143d018000fa004213102060721082080d034055072603c4000c2d0000c0d0101701400100b080c1c800d603004084d00040601c0b002d00e075100300180c118a955080412001014210340200740a244283d595404100c5410b200c04c5c0b800c17405c420b41c94580100214003d00908071001c2580c44c00343d019640c10b641c000c24190b56100311500744280351015000c0c19070703d50300c3c00c00104009980040d40c50b204195079918180901c0f08480c1c28021500164000e500c0951a042e03080d180343c0d1902c0e01c40002d05504c0d03000305440340800410203490310000c0e002d02b00d00324082003884041080d14459407907075034102007820740d10f80c020020705005003050310020304158542000842005241c3d12490304440c000d0380d05002e009803040049144250520b1071000651100d032900300020640c60005061820716488641000c0d03403940810150fa2403969000c2c00520009640000c40e564091351300c0f00341182d04010f003035240700e65542c1691080e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 310380548 1250 310379298 310379317
    0xc0507060806181611150403050d0204050310050919031e20011a030114040f02060f031312090501020a1407080d0201020c060703050609040f03050702060a1701060305070203 76
    0x154500040e0b62a10784038250500c0243c0c52144007018506a0250035060300010700309800190b403042c8035100c188001600d2000750340b0025040d01c50b0744850340d044c0d0f00c0e43d002440045100740c00f030000084c0d90f90140300d5440c50b024a40004196841c1141032241003442e140c62811b000c107100c031105008241c3c403030340f00300c007006d24104901c2d00340f4001042039805980e490015140c181c1601c071680020700c010b4000d44040290103c40c030181014100415007038505410728112100e482c0c600241c04a0315400b0303212a4a0b002070001403600c20745100c452070541c006ca030180090403403454440100240b2910707080d0032500e145404428182000f0000303448102c0454080c002e980000050b203240081403003072500174481c0b01e003202c20800461402901079000412134600902801000030500d80c0070b80a0030340f1907070008100741441d59850b82c4031800007605003c143c0c1042000e014030001078a1303601c001e060780e0126071250300007140355900300d1004820580243c010507080c4070610400307035000006d072400c00c0c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 310381798 1250 310380548 310380557
    0x11806020d06051203120a0203010b07020103181b0f0506070206030c0903010b1f080115091503060f0e1501020109031d1311040503100905120a030b03061008010c0c050706 75
    0x808401444000d007400f0380010f50b001603040801c603000380b130010003480c060b41c9202421610307568900f0420101d020034821050a00010440c1000540c4268001c0c044419070302200308009078540c5132154040304501021b031304180c826030148056500054050028003045171203034079000940d4040707061404003900907407645402043d0b60b44117590030b4100d58030207407020f080a56201903048030074400a404190b0800814510b0b000842d40c850300035000b070100a80b54907040300080c6042008140d50101140b00d9040650f5400081554011941c3c00b40003000e00401d00a0b40d070400400148104081c600300a05581c0f40c0b0603100b0000340c10a101c0c024070000304039403a0740c02181c880800c07001d40c98000110007803032920300298030100000b400380050b20710903011502d4038040034003c4030850346042000340c0f040d0b01c04611400c8441101c0004e20a83d1070a190203d2121800c3c00400c0c03416070103a801c1c0303220840201c2e00388982c500900c101c2c0952500e038a003100714032881d80c82c5d50361a0f0645006880400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 310383048 1250 310381798 310381807
    0x90f0609080c06090309040b04061508040819030b010f020d140918040b0a05010816030b070908030c011b03020424030905030a0f0e01110c0f0112090803061201180602 73
    0x310282074682d80c458100c242c803560315050880f540c5a50000d08001d20640ca80182c030b08041c03c0920030381090790701d000105a03104029440640d800301c801082152030107020000d040c1d41d5041545000b5000b445900c000c030f1010038450024000e80c0c42c441d00141103600c519019107015030312050f0b80b01f24104006485980c0c50010340800c441c03480c00a00714841005c503000b40401c00035211b105c82d02c100e664440402c0582d894108264444c074840101040e041705150302400441d44042c0115003080007420240c0440d6568a10b00c1e0540d046a020304540f07940d141040700300f10f044050040b103402c482d803808610b0203042107600d490072000b0003d04080c9401030a41002d0682c000d40c0300000c482d8100c821691541205400201100d03044407030000040d248111411140d40122030004400c09034002604c202100501131052072144151042d040104411821a91811510410055a0241c0700d0709690346072020601468001402041416030701d8040006214840c048100d14415400000560784 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 310384298 1250 310383048 310383053
    0xa0c1409040f060812120112051f0b1002030a03060e160516020d050f07051f08060f121e0a0c0612020708030f0103020f0d0c05100306150206060112090f0609 69
    0x800c0a130308450b20030b11844510b050343c1800309006d0600060416054001da80e26190005141e90620000520a500680c044c441481c030081b21a10b400002c00d00015040b0b81000000c2c02000354625a07001680000691220300c81c2e050042e00094a030042c5204030500380105c40d056041400344603038003006030204901c08c25a00c00c904129015400800498940d4243e080c0075480d0521003c11507143c0c4203144000483d41014204102c8400a02e4052140701c0c4c41c00c642540c4001d001031a00390302160700007291240f50b80c0c280c0556403401d03c1e9001801c0780a400150104000c401c10344c980c019074044a100c2000500c2e41c8001802c1d10034510788024800308007030319400640204c10005151090100801c41088040c05a080c1200e00803070f01c241628070f001050003643c038a04e00c3c000e40743c0c5003248410b201a003400001280d40c008240307030008480342d9a201c041861101c0034499401600650180119580e00c142004602204803800704500700c00e5a031060b51aa01c107500c014000743e00c80c0b04980a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 310385548 1250 310384298 310384301
    0xc08010305030a0c150207051606020d08040f03030b031002030a2406030b13020f07021011100506030a0c08070f05030706051606020906030403030b0406120b0408090402090d0b0a0c1409040f 83
    0x545c0f00540505644610440c0340468485225080d4110450000c00700054000d20010300012200c00e9615040010b03222a100d080300d5020044055003403603200c3e240b030506500c0401118191512100c0016140c0c20124514426035a0100c0071480102c0e4076110b100d07580c2040980c040c101c81785818001401454280480d0130416415800050280b01091448103000c01900808406200b102c00c58640034a140f41502d01d64007945040b5035aa11620a04010f001942e00040c2c010f1001000c81e034011080c4d648100d03510190340c11402e0541c00240040212847c01c0c50401c001d0107044014003d09800c0c2200101580a0b16051940134022000b00a040c46601d030304841c080c86c0044e186a0ba07915190074041c02605072588218005e518002002800f00b88044080e288942e11036005c403040d407250307210540c8a82081902070341c001e03802c2180c0e03000d0b0756480703007803d80b2213119800c2503c03180392040400013140e101e4a007441c01e00840d403d00c5400488114211000b038201207500180b00c2400048460 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 310386798 1250 310385548 310385573
    0x201140a170703020304030f14090f06090604140a0b0304030c0b250e09070f05070b0402130204170d09140d0c09020f04091b02070b07060e0307150c08010305030a0c 72
    0x14801d0000d0381802800d6505800841c13084d03019440740692020401d40803141ca038500300444000f01024003541107686015041c0818601d07009020b1818840b18200052aa902540c4107514002d41c50540203102e06003d046c0c2c0c801080601c000360704610382614050411110400d0080502d500a0005400080400240c205c021003411140d0364008005102900e000c0c05609890302c1480f4503000034151a20075182c0c050001e04940c5c580f42465050345d43c0140880e4040c0080780e010b0f1242c1c2c1d0f03c0b203a03c3c409201074802450b044a0a444c0c84460302486403c1c4044800720004004100e542440403030140403210001d0030f030684e04040c0d880e0135030504103042c00d00c070f030400d04580d40000745031031050040301c0142c401e581d910b0400700548040860514822100f00d250703080035800642d8108841044480a841c600e405404003288400c00c150429041d94008032003142c84e02207400b40307a8504203691007100301c00d40443c201f10000d9411030f29100d64034000c8580394800c02c10003186000820000340a0710307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 310388048 1250 310386798 310386827
    0xb0f0616060f0509011406011e03020f0a020303010608070504031e08070b070e151810020a0501060b120f0907090c0e15030405161404023004020406060c0201140a 71
    0x40041010452030b4201528042e145041990308102600001e00c1b48031841c0340c00782c00c058544c00e1049401e10703155544580480107001c24164240f00c0d0138090b0100e10000d10b90010164040c6660303605014004e410310f60060a0203040007000c2c4014000035800c8100c8020409500d1070341c842d070920034904808144200b19004028026040c280301c141c2e5000108009001e50440303d50700c00f0036004d07841d0016401042c220421940c4590306034009410300900030140c0b586240b05840b8030703981c0c075100c41c0d003911204d9005601d1a0400030b170f1f032603e00c9a400c04071500503080d4445c1303103110f0614034080351740c0d10340500548070825600c40074004594001d40544200c140d0142c10720091400461411255405c12501a103250048444c40c40a54141507005411b0350108042a0503d249100c10720000750841940c00e202101d00c0098058840340b9441542c500d81e01400c104900d601d8144144000d40360745c0e81c004030510401c03408020040c0c1c2c02c00c0e540340403425511080b075100c10140608680810501d01701 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 310389298 1250 310388048 310388051
    0x3180f0504180828020a02011e0c020303181e06030a0c090906080106090506090105010906110709180203100209030c060d020f0a020d080912070f0302070b0409060512010b0f061606 79
    0x100b000510703250180961001c4940e80130f4140241c4142c00760380b5503078601c800a00244400107044262004681c4e4403811460614201c2e2111072141c2c0401e00d10741c0600c0d4030307090a02c8007444040c640e1401e10313140352a00009401c8011320a2160700070a501b408054a040215a141d0840c00348a070300c618141402028884004c0c0880c070b075100a468000e08480c00b861050a007004006541030600d1184241254410394810305060324080b03003160b47c03903004a055445401050000581c400303060003810400b00310512014007204043c4109031610b6800c0d82d0035900c90b40140841055540e001c0780103400909d0507904650390700c081804400080c4a40803540c0e10340100440c1c803034500d950020300161411040c8e158550951070762860741c1e07540c0340c036030311b00016010003040310303070000341c01ca54003c88903d1180c01147d00040d01c440640c0075942144c0c11402c1001c1e070716401041107103003000d080c0710100030844c0200046101d02e4049400c5108480750b09002c1c207000940b04a8107440d58012a03030013600400f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 310390548 1250 310389298 310389307
    0x120103030e0d020a0b12060409050a03200304030c05010e09090601060c0303020c03030108062a0d09061404080d1109090105060931050c03090a350703180f05041808 72
    0x40d00c010b60f41103c80c0c0310311b0241c501c0000420034205846540d0041b608500100340d143c40954003125942044820450034890190300300c1c1042400300040c0026511602248628500b8880010201a40504100d200d82c00d0b20301403121940000c82c00a041d03c1d81c1d0318007002044d042d810140c020344680c803c003484c03c1c400040005070540010070350501589070019801a0100441048800648041c443c1002c1c2801000741104182d8035a1148040b60710034103000c10a1401c4e40c40150503400e04407010342e04200001181c0207900da40740710315036894505803415410120342c01d000c50403a040500685004950020782d4010343c0c0d4543c4e803901010a061040440601012201c56907001d0110500007001800e01010901c200c1a0310127503032240c0044d0004188500d07039030b00c4035a002d80d04040003018200604100b01c2d60b94030080014403d540b10b81c04800e9a814032807800810a0700d2114100449a42c885418492004801c03820804c4501c00c60b0007044e5880e0000e42c40050090f180c01c0144615030004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 310391798 1250 310390548 310390559
    0x1603050c0c030d0501080c0d0b0a0b0a090f06080d0203070c1202041d0d140328020913150f03080f0a0207090216030e03011e110d0c0507050d05120103030e0d020a 71
    0x2004135050342d103010140c03105001110144102c04441c15801041a94175800156005070306521601110500401d01c030714040d41c92a01c1c0046a2110020088103134803100148182c0c0701c100442c404503411440290300d04115501c400103e603071107002d03102541280a00c0d00c400d6594540000e505180d00a200b201000030b0390000b03030741e0703030030001c400d2008500b201800d4148026030f001500e00c9154400ca0403007840c603e00507043c003605902c42031900c0150382404408250380b21103449a81c00d91018900041c0030046080700d2050075080e13804003040c1c2203007031414030000c1c0d0f0b000c0a907110f910307260103155295502040240d0070a00b403504000f03a9280302141e003015640404010004450180d110901120801c3e000d0609940c81d4007448080512810509991154594081c200026111044605144503409031800740c52a0072440400520f0110f0158203004052101000301e00090403da460440800440050400148800b50038448414055215a2180b0064048155000380200c040d01e84a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 310393048 1250 310391798 310391801
    0x127050c0c0d1d06040e010603020a201006080304060c1205040504050c04240e0607020111190b070e01080f0403030e0610060f0201021809040206040e04060902090a02031603050c0c030d 81
    0x6040103c5150035207881815142040c0080f1010b440d01200c425503942e09000c0160040d5000c6951441001000d103070b04201001402e00c1c0700c00e100c2d4140f004d40f01c0303c1da220119805030740c0c894000c14059081000b00300300c415004406401d403d40c0c48010a640c590711001c05840c0e0f401954441a0024182410400c00000034001481502c0204184041075280920004008455407440c0004114410400301305d620300b00000d0000c26205241c0700c01c0340028030010301d05090154030501d048600c500c40311005c000204500d140d0040852074404007400410300000c0412201030010a00e0b1980398001c81d06251081c0c219200c080d50b03040031103182e820801c0541c1d6038130440d07104690014001d207028003c81031041c001c841558002d44981c2140b2aa03141c1005007410019000b00d034000e8082100245100c0c1080c600d61055000f050000795000840c0140008a6001041c0700c0f1000e20420410104801c54200c0184611031440c1c0000d8665030840890441d00c647c000c0f006203403001080e01004072140d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 310394298 1250 310393048 310393067
    0x720070501080a09030c0206030907090f0504030e0114030103061104320111031c1e0608011505060d0e03040b1206100203091f0306050d0b09060127050c0c0d 69
    0x82c1d07509003580e0796680710352040b10300e009030040004840101041c09850850090754010402100303480c0e40039aa100c0c50002c036004081c20b00340054859041109240c0c0088100c68004402e09141003008003905500f00341e48014000101540d07078903d1a8459410792038255005071546c88001d003103900c3c5003030712100108400c0107103007007594100d40305803515482802d24084205c0a034008504103000481e501d129030f2900443c0b2600345039196a0040440341001101d000d15890a1000031103505120f10142580c40c2c1854400c1d1007071142200300090745600d0308851900680e180000707820a0755811050441c0f096a0060710902c80228000c10b601d500d80d009607004440480d00040700c108101800e90700c03400b400042952040f010100340301d011401420030100b400b80c51500056045e202d9001500f01c1002860a0716440c48080030804480020400c0d6801741c284141d0300208180640740c0112440924141112081d85031804550074260003025103000164140503207020310500701000b8140c010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 310395548 1250 310394298 310394309
    0x30203070c0b091c060207020306040b010f080d050403020409060603050601322d150703030c091401110a080d14010902070c0509090307240b031209010305072007 71
    0x4003003400102c0b505100304a03032958401401d09043d401c1e0311004c200c80081482c4054588540030090341c1d006907028030000e07110f584151445003007541010503014110342d0b2600180055802b10424502c03407a08402540e04a07a03044801043d94a11481e240000d4009940001e0052184000204600e80005c142c40c404607001c03036170032040343e03516100c0900305201880c800307030065500307010003189982c058101e80e04210f42c4180c03085d81c030703120001082c1c2698081d0b07000c8020ba00d011031010100b5505015040b01c074607107480c0c8903209504100220341c801e00d501c01d4003030511070078035440031640501b801f580042ea82c22541c0240c0f80c03061480901e024102541e0703080c400c0851a000828907201c40e109540b003154110110340c800c54101780034051050400b500f04143e9100c2485450001009115088991202004c42d10164080d480c14001a1807540ca0b11074803030380004110381d00d001002015134039007a80919020405444245098031624112120a400307450003a07048201c03000700140400403250b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 310396798 1250 310395548 310395563
    0x6161701061110021608250303021810020d08180703080903011404031202070309090e0c01030606050c1b0d0210020a120914040b0312070c03050705010305100b1e0703020307 76
    0xa040152910482c0708555040710f25a03102a0380c05c1c08902003001030006190001700742d0002c80241800e403901c1c081c0074082240003070b03000594001e407480105094100105c1c02d6900b10420002990040c0d1690418054101008003000c0010324000d044800b0f2000305c410b00094481c030640380d0903d0407803030b8084a6030750300a43c2010081c240364892402603912a0b9095942c080803800c10b8186c1c98069407002d50143c04000d8480d2001c15500814030452001410782e034014800c000c1101c0000d02030f12001d9102c0c2062220611000110640c003041d0012141d04181055a20003034000010b802100c11040103900a00141d040985103600080c0e1b68640c3c030700407005403000982005003190710076098014264079081c0840ca6105504054001e00034001d030003400e581240346074890b20025504907002c10390b000803102804105200040c406071003e40401c0ca000e0100e80b42861400caa03649c0701c0c0c0300b84881c5000016400d06141c214100381c03200004404106507071502a800e0080d0749800840003a140794 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 310398048 1250 310396798 310396813
    0x11040f08070608070e031c050c010e0c010507060207051e030304030306050a0f03150609020f070b0619051210110306030105060a080712030c021306061403010503061617010611 77
    0x8000060290455085070b03a10b216541c0e5080b0211160410810211b4152060f448141640030041051140190b0117540e16902d138200d82180ca800d40301ca1110320201e58024a02200260b40d0000448800603007014016942d01300c9841c007a4a009200da41c0507103c01c9642d100000021408070065000b079000b940c042c40440c0e16502040b007011894815102d015950840070800244140e900301c643d006052000519140e803200001c0c2680d1054880c005800400141c00040011440d4026004603051364130a42081c2040003002c4944218050b0f18801c4201401d4042c90150800091031030120212007844000f0680603c50788030380040e102c8a20035404c0500050242c10101c2c0c0c41402c403a2110014500e091608458104d009440c1c8429000c00c900c9503010303005a11030b02c42c0c072644100c5150000521903d460001400036100d202c03105c185540400c0100301954000459070b42100c0410300c501d07001c0800305000d950200c4041c44280800c8100030000410603000b40c0280030b1441183c081c0d5140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 310399298 1250 310398048 310398059
    0x117032106130b09011214120c010c05120f0408040b0a0207060f0804020922020a0308040312050c1b0f040906052e090c030209181f15030509010f11040f 67
    0x30f4445010080ea0460000001008220384865086172554082c00102010011001416050480c000902d0350b0502000580060302c0800744901c0100e041580782036800c0000c001101660f00308090a40390400d42c0440101e01400004412200109105038005507907802d61a0040d44a0b0038610031080442d440c14030711f212144c040c40c101407040780d00508805641d5a8444c41004810700b24548481040d40302008400580300c1021203006036000310049a02d4030300d503142c10f682c940c0b1040b11b807508002d42404513001c04600000d03c0e5005031800d01401c4100c01d01355010072109101e00d40314550203070810b0401e1007409440d601503400f8060301d000009010818a110002c480303c02841841c800c00e070350808021114090740a658021000d00d0098581045c007000100c0b46130601c015850700c07441c10b07818800c04010348050560010030b071541c1039603980d01c1c00a200001da9407450543c010b0546800009000041c02c1d07000750400703200444e00300700084461410395160380050141240c54040072601064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 310400548 1250 310399298 310399301
    0xa0b0115030b060a0f0e310905070b21011220181e010b030a0501050102210904090c231818070905013003020303011703210613 56
    0x4603804050f2405203043c0c0260707003c64910296002850800c0504108180160354440e00444128a41e111141c0302400c80889090110240820300a05615001c0064001003000c141002144e0a6500e1240c070780c48103651100600b0341003840180e8810b000300000c221180d0072943c4002c41e60046e513142e03815450a10f0341f50f425003c440f2605610826201080454001e0404c0090b4015440404000868035140d810840900282c00580c50848040204041c1c061f5900c00c2500402d400d200401075a441c01115545a0114085498540b200081c01e40041d0300c1340c1e040100191341c44100e03410f86aa0710544052000b10008003805580c5004641445e90300d0112546010070308005140c0722162941b11241c80651b00340310a4400d10b015040d0006044a902d101d40c5008105020361241c1c1054981c1c1c89442491002c02c40d2410008080301c0380010039800000ea0307054036807040d0300303a552201c045c420919600405180344c0481c20720a960304e00210784440740a0045da8155420f50310b010381500c01c80c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 310401798 1250 310400548 310400561
    0x30c061a01080112020d0218040512040f0905070216080c031e060a0506030a0c03031e020f0c04020f0c0109061505090f04060506011106040b0615040602060c070507080a0b011503 78
    0x10300048912005202c0542c14244d00800284002e04020350741565070b01180440b01c016101840390300258042000380501400200e184e04d14520310185028213114803502e0403125401154659603640f0009804c083c002c000307070b2402505842c80e000720240da03a4403d0760b0341d800e03440381c06000e80039a100c4840fc01340315103901240c0b120700d00d01501a6036a414070800c014030300205403a0741803103401420320118099040c1100514002e60755903e03401840644945e0028602d45030208640c4040c02c1c0c00084100419510616030003200c000d607481d038448078480080c1c002c51020704129443c0c00e00d60010040603a1042c2004000261030350b8041c0ea54004128100c0030407a40452400d00200000d0700050311741d8082c83c3e00a03014144030005c2c50f18152001d14007a01220300300e1b00070782880709008803480e00c1004c2803169a03400312000d2910f424440c0094844c0400380082c100010003103061400c0100500009000e081e07240101c90320707049141407074150346500b03200e070000c81003480345114445c0d4428020030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 310403048 1250 310401798 310401851
    0x3090f0308120406020f13080105070806100c21021c03060605120601030204030b072006130803180d0f030b150403030503060f0301020d020a0207170a020d0602090d030c06 75
    0x541498040d441210382e1440c01403045030701d00e82c00c0150880c6903003088054601c0c1d40c040c04070202103d0034440d0140c00c50b00050680820f120902c8200046a6200201c810fa6082c0034609005140380b207181113416800781c80d0600880168206400b06442d0703000445055041800050740c51403c0c11107016000ca60150190ba0005241040454441c4030701c04c00040e001401890010701c0c0681d81c0d2241666040b05a6040303000039105183e600c50043c8200c540c0f29820180000b418450a1140b100c03026024482001403d942c070110000d00c06850900c088102c242132507007a10b1039641c7d01c00008050745004911800070038078100c400301c4581041ca400381c5000c80c40b40b4006140c14250744060b030381908018010350740801049110310032901c2c00c0c0081c3c8941d11410002503200d803180400a0f007400c4094011441d181010100400302c80000201300b424a034054481513003e842c1030502401a20405036940c0d0800900c454003410964400d101050107805013000700300c880d4901c184107424041c0803e54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 310404298 1250 310403048 310403063
    0x10b030103030f141b101401060c15181403030c090405150414100905060616140d090905070806010206071b02042c1207030c2301050403090f03 63
    0x520000f0b00800320001d1900443c100340c00841506103c0e04050b80c008000945103841143d1002c14030402000f40c070f80c13040c038803410903c42000c001071030101040f01481524100078031251035009000f401804202e484000d03082c01d00c180705040031094090308207007c00f216040c104516170a09100040162401209441c948a260280350410803003e000701a140f020107004141002a4a0b03960348125129540404407480051034028a080c01d400b041d5030100d00314030309107803c0101e581e41c2c0400b220110f40035207401416411755420800315102400100c09541d120304425a05581e810904d12012581342c003000340b007140c1d00c5400c01c60765101e0903224540075a100d100030a618501600c0620b055422030550352080164540004040e68445010f0400201c00c8074ae005200901810002d080d507031580000b000f17071100512888910344034002d00501080b82b8018002c00300485c103060119a02001e01500c0d100280f21088030b4001d01c01503404401050322000b00040c440c8034061030310b0440760803400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 310405548 1250 310404298 310404301
    0x20901120b011214011a01080109201602121b1e090403180f091d1b0a0906150201050a0e0c12012007030809010902090a0c0c06020a11060f010b03 64
    0x420543c1480c050011030b0b0300c483c20420030003c16401d204030000482c0080c00035000d41c52590001d41018010b0304000345850420115602c80302e82c03640d07151008030764102c0316640c405185d90242d21554100c071000754004010480c01041960010306c60a00003548610704002502050412100e40902d0007114803c40c100700c0c18242a1418200040d80507000c0c0c14205401e0000f010103174034170700342a04405042d461450050140141a1040c1485841c201144400c291542a403069036001c1000301010345030071304465006035842c0d44082c070000301506981440071586076000c07040c1503a80c0b181c80100561a00c80010fa400c41c490003180380046480c0c1c0070700310b5000b451040c48403005840d103007225907648403444500403e00001500d01f002e520b140c1c54980b580ba8514009102c1c40d4080c001c41cbc1244c0c104506400965a44160141c111100060002e140410300500307442c0840380100c0a04260720204500da41941c000c10070075591091442650503980d241915003031a90020f000c4c03114840000e00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 310406798 1250 310405548 310405559
    0xe070e150c011e0606180f1505070b07030603021c1211030702030601060c030f020105010b03070c021c031d09160c020a150302040f050103051b03060f0d0b0103020901120b01 76
    0x10001c0924000d100d0010980c540d03000b400a04003400f02d00d00c1c100c3d00ba51190104410782e44040c080c0a001c01c40d01788440214038096090700d503c040c070302624548582503000070020900a40032143c1183e4040f803000900c1c0340c0400064002c0c0400d200680c000c0040da24000054510191030745812a404030a4540101003464121039100344122100020310080112502581d000c1000600134040c56440c102413103a80e14000b0000101c0c0f010110641e8100300041c0704e203041d90400e8951224203460054440003942c00000c0c60200d005100ba80300791625a99041407652100001c800688140780003480c80c40008103011010300201c50001c0280d03038543c0198501440b0b040140c040e5030008250702c021300c0d291071030003024880c140c040710702207a8009403c001e080b2000c140100107060909041245140408003107148411001840b014240c0000015105507100600ca01e000c3e00040c08882841c1818984020700780c2080c0000c3c1e10800a4100005421003400100303004681d0140c0e5401032a442c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 310408048 1250 310406798 310406839
    0x8070302090406170f15040b011418070e03072c0a09080f0705010f05010806130303020f0409021c09230a0803040305070b07020705030d110a06150e070e 67
    0x110700d40e80c0503403921800201c40f1650b15078810407160b110044d0001c0c01c3c10003001ca1030411481c14082c21510000b0400000c0b5000624031811207440340b5200d92981000c1c4001580c04081602031078840020005100707820750b00a58607019442c0c164200c486441e00c841c090040e041c100c2610b108581a1154071550070100030380039a4001d0070012000c070b4100b00070341c2c1d96012900f120884081c141c401154800c280b2009001d0801d0325160074401f04820350400703c2c41c2d0345400b0001c10341080041070540300340806200c0c0d0b04036410744440c106072940712600d40c401070010b54405503140c240c84a01c00f8581c46038064034420500301992000d50208200080000081d410003610143c0c2c4072406980074001c00320b82004015489144282e03191350f43d6002600d0882c4900d0005000310381150b05c4008140903648001501c0c0d040344020b42804102c1c06e0640c41142d280081907080242050b05080c1e5034015a0410420641510303403800f84015070f90303141c001c102d5a0000c44650503510481d2900d00a034031100b40c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 310409298 1250 310408048 310408057
    0x7030c1202010204083c060a1401050130180c0b0f04032310050a0e06010b030a0b0a05130504050f0f0307060203130c03050d09091404020913061506110a0308070302 72
    0x754004a02a00e51b2490840e031204805c89106074660407001c05c20118070114841c001c4400d010548406075541800c0c00241140c5140010007642d090711003040f0b00c2041544061525106c002c8018001c0581c405041c02d94402c44400468484e80d11800114000719250183c5030702c200b100d01428145860754541912000c00400104a40d01640e9070301c000c40501032064881e0703803140100218450030005450022244400100061600320900510407019640216074110140b008041041d10b5620300080045065901c03e550007160080030f0b68400181d030300441e106a0144054130749000c601940c441d118a031042c951006604201300c1000001c01541c0a96040800700003d4074252015a0310b818207500b442d00151281d91010344110b84440d481803407000600303550f000500c24152500100c0300794603000b90009114a40b5070340011780400c0361070a03076983c03140c1201c0c0c03e01100b01d8000c103e42d0240c0080c0244000200051880e1103d404005070342c1c410240d0650752440e0594442004500a401c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 310410548 1250 310409298 310409353
    0x824040c091806150f26041401090309030303110d020d0c022b0c08040504020d060905090304030206040311010e100c0501270b060a08031803060609100605030a1107030c120201020408 80
    0x61410442c21100406000240201100c504800c0c1b42d003810b0500001200840b520381860360b040000900c0041c2e4009046812243c3c9803d001c01c02000d11400c0c851280112409078024620116080c00041c0681d042152000d07140d03000c0c2c68030704205010703481030703511010041c484030010201100c3c2018400e0015100c4140505111801c0a03190b0740000d05903030045900c0c0c541d4031307103c03034041c80780800c0c520901ea0440c0200001b10310380791843c1c0c04521640603070f100c0a0031007020201c003c04a0303401508001c40417000101416040f140110010344541c1c000031040d00c0b10f610b0b01005074a845419041884861205030020a94500c10f5523250f89200c070042203039030094070540001a110700200050070320450200c0318846080c4400082c186081c4c0b000b805280700c0c070780200900c00e00c10f00c924100c0058550b9890a01d0740ca6844130b041c50041e04840300d146080c4540007509400b490343c8001c05103c914841c10708007191146046049082c2d000b10f006048240d084040b081080c1c0b4104400b80d4043c19 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 310411798 1250 310410548 310410557
    0x13110a0e010302120108030307090806060d03051804060f0e060105030601170702010e06070203040612020f04030305160b0a0221090309041d070602070f150824040c091806150f 77
    0xe200b540c134003060031000e91052030030354004000e200c00e081d049010000a0140c41009042e00c0c5007150003d03d40c1b04c05038402070140140054001c0303034681920b603c2000d150002d0000c1c00380982d100c501c0780b03100d113052181c0302d410b0f05e4940c0841c1d8598412401c80e4080c8005941d41c66180b0441814900714000290610f02950b41c0c46410020105d41401000d1103400705801464603103240413006020200b030408140c2070381c1d204103c42900c10409805807010380360149809030b01c0780132003400e003662172111207805410030000701d0070421040e01940051142100041e20f521490aa58a0b0b00f404407400ba60b035400319800a00605040b41420f0b480281a40010040c07403e00b039102000301400e02c1d8064020500581129509016100136074900100030000400c1d43c5686090322000108000340280c005009040700c031400070f8940b038180d041d25a1150004004215074a08080c01038030a00700c500c220150014041d001c640820410b101e000c04a4a9084101044400c13241c0f00b26602c0b681500c5007818030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 310413048 1250 310411798 310411807
    0x11703120a0b01030612020604030b040c0806040c030c0e060a0b09040f020304050c040e030a12050a0e0f070302010807141818091b0a0b0d05090c13020913110a0e010302 74
    0x101840c200d40500444071002901c1031450000500b0b550721500071284040100c034042005840b4501154101c0790080c1402c20240c45910b040310403a040c40e400748a80784142d6051000b88500e4010560449200e2a040c148807503a0360111180740e64200e58842c3d11540c0c83c0000c200b80c0d15800300400c7c2031940100700103000b2030000c0300c2ca4200e8000756000c2c3c60652111103030200b10705151083d4085490f00307400035030810390f9881c4e00500d861444411f4560241e100c4000c50148446504110380c00320f8039905482024182c10719265403a83c080c401603001850540c0030402c858001d00da02c401c4d075489514a21710300b0320005403151180c0801c2c03d8080d008101c4280c1c6190410740c000016001e0b031180380140c4804803545903044d11b20300c0c40c0a0028400d075400caa04103c44001c01e0202c44a22203500c00100345580c035560350343e00b8a84150b401a42112030650a040180c420b54005c1a00f200c080f10240b14680d00c5003010012100c4504440031403490400032240c040380281c0d910410ac003070500d00540740 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 310414298 1250 310413048 310413067
    0x503272d010218030f03040e0a0e010b090a140601050a0c020d05030403080c0f010b030102120406051b030910050a090506061507120e01021c020601120606081c09090b0306011703 78
    0x2c980c0824410100503d402c40310340483d190138402e001c094080702004504240c2851030905a6290103440707403106950302c140c1114080429001045900740082c0b202030f0314940100f0000160140e0403d009400c100f842c0003540560103401a900000025601d032a82d018144d800d0281d4038481c0d101c1034031544030902c40000003500d01d100800311002d064000c2c24515840c20406070070345814103941751007031b4014082c6004444c1e09111003075000c2d0b044140421241c031202c4001a6904000c1a500e101d10800010000014030005021b2400914400d00304070a030f030340d20380ca2000c0701e2034404001d255030880000302d0112710f4913044041045d404000140d00d41080350b0b9451002c0640b040d10000442c41042c0720481c06c2da01403244000c030301c3c0f1078070b880e40c0c1c01c144000d4000c1d20f608050041040841c0f01c0700380c0c130051014607484007016080900071507032403612440710341c1300382100395000c00006511103a0109003403501d80900110307282302900034043c330390900e0016800b1810440d0303103590500c4280292040d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 310415548 1250 310414298 310414301
    0x9041113021905071202121e0705122203080a030e16080a0c0b090d02060a03090b0907050a1508150438040c0c0f0303060302100503272d01 61
    0x90380c940545400395241301d285400c0b945001d0012440095410442061554a15100c216240440082e0344110b10a003000b0101c04a4040d428020300503100b104041101070070f09100820710040180c50701c102040342c03070061a002c0346640c0001007109405001541169010390002450b0b1101d440aa135848140d0540044514015a00c40d40c00c039071041c0b54a90500041c2400100a4070802d0411441c105038000410030790090350030002d000c5d250000f04211407921030b504c042061548101c80e0b69540c1802117400d03070f84403007902a55201308017031040000c2141c9049039510340f0710159103401803281d803480d1181551449141403560441d840344025800440300d8004000e03660b1411108041e0741341c840140321081407a01605a000b50b2030014903110440e0809203421900e41d0151b2860004000c92038201c001d00070b681d0000b904412407031000d02c2219003100195100d04100d45035a0f00780c1551f094012480c0300780b20701c011840e0708002000ca180c140e8034a003030006c421501859100070003c2104950 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 310416798 1250 310415548 310415587
    0x3070b070c030308010e06030d0c02010e040f0509150601091211061b280b04140601080f0c040b090c07050a0c090213120b0c13050405070f0e0904111302 67
    0x121030302440c1400b8420140c101203501c1c054540c01a10500303d10f00803000c00e0f40c3e000a480d61000b404600c1410b14210b83c8503c020b1000184003420a101745090303845580e02034070040c0d42240090051400300c0201a0505c0c14144c402d480507568554003a2800548900500c0b89460a64100039031491103001030715100020140b05a401110306040c64010308404d0828402c0c03d40c260700c214000c018a020340c2c01480c3d40898540d00300c01d01400c10b803a24034000d040c5032803112810402e402060000903e9485c0402c160842c003030588190758280d80c014040100300c1d25000c3c075040d40502d2810208041031001009040014070031812900299a1511071006a441a03404010780f5030b0001481c10b0942c500050b918000c001ea50010106d248007039440101c1c0315801002080c1c050390200b42c6505027041c000c81000107040c0544100f103203003400c080003014040d040d1480d07808034080143e14001d50402e80d12240c41150040d44c1141541c1c81041003110600f404941c600600f0b0302407090480c00c540406240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 310418048 1250 310416798 310416803
    0x40b0d020603180610081c0504060f050706090507030224180f0d0b011404090c0b0c0a080408060703111201180605042307020601180b0a08010507030e1e1b03070b07 72
    0x9171002880e11920300d20f480503007584041000031b0780010326002c54000b010360b007c0d5220341c109030700015603006048403180284032000c0d000d03904220320784051010101d108019070307000fa207621843c9468518080303604070321990604900d0703404006c14483c6030724021442e95141030040203403c1d00c101100004800180e40034060701d81c42d0721074004200c0c0d0100280c03035484040d4182d0f0140b14041c000e85440804900e40d00c030340110044005103480d200d8006101140c001035021020544860301d4003e0075036107600451364100801c1c0b91200146034601010b05076051000f002c0006c41c2c060b07080100c1a10700c6886404003401c0c09844813404645540ca80c02400c0d424410204a40001e02c10f07103007903200242000e4940d0055420a00052001c02400d800700d076881c0685600c007150640d1107901145d210701440d070014640713500c0c0c80d044c0003055a15802008101542d0003c403580c0781d03400c9416002400301924040241d0f80810298000e8440c00c40c901c3e06003801c01004d4540540d92280b90b1040b592022004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 310419298 1250 310418048 310418071
    0x617060d0605150405060f01020304051912140c01050903100b0402041706040209070e010c03081306050702010b040b01080c0414030a06020c030c01060614042904080109030e040b0d0206031806 84
    0x3c103400c10303124003540712100f16458445912a07800203901e81c0320724003c0034026074401c0a5565802030b4004000c0040004814000002c0d0380b5080100082500300f4001d401c0340580c400c10306040d0b118030141c0d40d9062000f006032100c00b01d01c40780c0000a140c46c41c19070f40c0081e020300000488503490200e4003414444a00079001c949400c1c410840ca00c00300074128000d0080704501e10344d8590380802c5c11108950b0506117070700c6545802c00c2c158596000a13030002c21181c281010401e0a80d41900101100d90095a0034810500103100550760310904480d9403554403020b1108200000b008200c1503200070740582699a813400c03d03182d05c0180c0c0d200c607107642c04075400040c050944490901c41c4c03000600311b52600f10b81007100d03000a51985e100d903214400c042071500084030050607070444072414100b5901384d13866a4955451515010b0003051034140c1c04910000509103080c10320303000344074000c080142500500f082643c00c00005130000b4001c503c015600150222020404210041c09003448940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 310420548 1250 310419298 310419331
    0x1150302061b2d06010b03130b07030908030a06080f0a120c02120303010e04020901080d05040b09061314190e0a020a05252f01030b03010b060d02130605040617060d0605 74
    0x241c42c50800d060380281b4036038a041081140d2540306228a011103640f003a80c0e03800903241c1850440281c940140c02501c500000003d100400002ea0b10213011035900c4003c0c0c0d440c4c5012441040d0300d502d803d42004d00156001081d45c51420311801180702c640788014003040d11188045080c0c0d2540e0000d82184d0302d4448520b00380025881d0040c1c0c030500400c0071100500d100403040100800758016803113540007040012075220030a6482c2c8098440303210344103140106c0581e644402d070002c017107548907081c0680003a0041c01049500805c1d0358007502c928a071844d0403621950681e80096000c0b884210400500f40a418078016041d0303003504110004807601c0312400c50b581041c00c1811104a040c0a00414255440c90012505d124184a40c4000d081c002503003d501c1c0302281c054501880441d80c854400100311000c001c013075000d803030160004801e40e52141d4803210251001d01c1107000c2d21021460340014400500d0486100c250b015101a242c0d0800850139901e11080d07c03010380307410008680c13458 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 310421798 1250 310420548 310420633
    0x40b09010201060f06140d06030807030c0221060f0a14150f01050306010c0b041707230a0b040f0809220b0102030405010c17040302031c0201150302061b 67
    0x3c1c140a07116901c0841c0c0164541403014000c5001d8044005054101044034106030f407555000d40c0c02581c02082081e51798034145001810383c2c0700b0403022845041c04400e84240d02c41c0b0a075491807501801c400404841d02d40c0440c411003000002c0c5144205512600b0b0388c0c2003507000d451014003a00f001c030841d000d510129000c0204418042ea0340f40c0c1040340074020032103240c0e40280010002a0801e20054294403113013424007106500e00c1c5c1c89565030b500050030308100308000e4401e01170400c40f14203110300e02d180e000c4030b00d40b07880c1b8481010746001060800308011030100d0040d10b14443c881c100052426100001090703502d0079910120300042400c1290810000050180424404c42423003d10b15050410001a2242030b0001014164541d010445c0300341d50910380444020b90740042c00c842c50340f0100c40304210a0306100c07800b44015400d022000004545000085058a80c0240a0341c10062051500d01003048105e9031600c1611500b074408041c03800441009161140d20300c9549a001c4044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 310423048 1250 310421798 310421801
    0xc0a0b070302030f0606090d0204050108070603050603010908091314070c0308070201140114031005011205070905090d080a150611010c08040c03060e030409020f0a08010b090f090615040b09010201 86
    0x5042809140c010410001001c0c4220501a03122000f106ca95484400c1b01006c44e40c007040d0f404c3c00941140c600800800c2c16900004c94004403103081e54148182d0b642c1c00c05250030307541340d810020304202d020300c818070552429100c0010403188038000081d00b2100180f00751560707101070741d50794049070040d08200107050741b046240354404001d000030700500b90310340800c95045405208914507502030300d02020040da8284001c500d0f003d20064144829611050002a28250748000f10b840d0f03c950000001c5d840320b280902171140023071030054008640c801409071030080d80144911405556060030204800320029150040e0503d41d0303983c20740c01040844c0300d08442c050341e0080180402c0d8001c000000c0c030040c0440c01980d52044011500400d0f070f210152039070140c0d4200c0c4e24001c0c0007180344141d00c0090070286c004441c0d00d50b0f80704140c0c0d03a03440031380390a48511150760b40c002540c20720035100f0341409005540c00c120040c011450f0001d2400040e0402d03009a048418410b1300050300a0031036070709 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 310424298 1250 310423048 310423051
    0x506040e03070c17010609241e0b0706060e0f06010906020a020a0306020a110604030e090109020403030c02090408160c05041b1706030c0a0e04031d06040323030c0a0b 73
    0x15400075454810070f070300d408401d44524414070000e41e91240a610300100203401110050055410500c6200c0030104d00a01c010701c1c40581d05010f60249074001260404155401c010f4031070100d04081403403c00505003502d174001c000548016864130b0002412802203800c9510035070500410120604140000400c00702c074540c810021907100c5003010002d0703502d03d40b820b41100e901441c0180e43d568508020384103a052442031983ca8090700b4100424076800050941a000003110214002d07a00d51058000300c1c061404040c00056004030100010b0609004660b001400f8030445402d200c400c2659012440c2d010204491030503980f0020405404c080c0150130341c045d81d02c0d5004c181c001c0c40c07600c0186000b5034144002e020741032002c0402c590380c4050208030a8150044c00c03800485880d40000c018101041c1c804800050600028103140f910018901c8124a070041626103064a9600d0fa6165900618150041d0094407a101030000004100030f00003504201c0203400c0800382070030300c032140000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 310425548 1250 310424298 310424321
    0x5071707051e0f090906030a120c0308010b0f1909080d0905030c090402010813030908030406051c0e1b0303040b041401120c0e1002030909010f080f24060d0503030703050604 76
    0x414001c00c030400c0000c2080d903841c2e131420f40355000e240e5a1800003e00e0511201e1028024405c801c0340040202c0d4002d5280040c240a074440c2c50303090366a10300420513403140441d61040714900b03212420744080d41321407080f2000184e03d80400c89545441d034660030081e908841c0000300e200a2020405414140000804240c040f20200d03c1c900d040d40000c2c0c2100c00060601e92400840b03521002098060000c03100a8003040080313070740310303074651002503d99484000d8000320300c0640c0700c188181030700d1401051385c0219030a01a062102d0040340f040d2480304010b03140e592501060101164160328140a40001c265505c007a02800c20070100140420350b030405440140c0d400c1070b0308403030030b0350700301140c9400104261000307a110809240304908500900c0c0c011a4031400c0c0c040002400400c1b9650380066540820a9035450b840e4011a103036502d8980c0c180710403003401141e40c000011021180160301c510094640151403145a403480c0c15507004071208000702e070340c6009101e03031401c0034420080b0055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 310426798 1250 310425548 310425607
    0x110f010506031005010e04030e13020403120e030f0c061b0a2108100b1303080c06090d09030c0e0c040b13030b070c020609040c05160303061d0115030507170705 70
    0x141444081b101c0c0403001000038003400951030f1089210707100c07101180495054508119206e980b00e00c2c15020662242050384000745502c203902d07540385004140403003030380d41203801010042c400b0713003e004140e0042040d0b00d03405020366405000880d014172810746141d00c64080400d010381c4012031840d49003035210325803041010380b100f00b00718050605214820f54070a1030003103403034813210f041900d91440c054200800c114008600710324a040005582406207650200b07031004048525000c403070390030780d40c03002621480c1c10800410059052403804d0f500804421039403480c2986451061000385c0c803086a8492188900381c081013440b144180c2e46030041900d01d85502d54802d16000100e85000c0d80c41070b580310307070303580e00214004600490440e0350f48965040f10200c0c88020742400341c001e20040c80b81070341c200c42068001420f8803ca0101a050b5800700c0035040c0c0d4260740620460042600409010900c4840f41c4c011200700d4405028038030465a942d100d07552a0194010500841d800039071403103142 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 310428048 1250 310426798 310426801
    0x30f060b0409150b1602041e05060f010516031107121a0702030a14031302130b120d1715090c0405120f0304050105070c0e040b011505090307030210110f010506031005 73
    0x840c044121000032440e11105c801c64220b86c0001070040c541046040e40c039031400c202c00e92010030550480303845800201c0d101001000392800640c2c2c584142920b1070504080e6003800700c0013070300403544035909441001c200c51010303407034005c10030002800b01415540c070700c204000d500c810b055480a070759004280344081c5051940c0204094210388110034a5440d4110220010b000c03803c085504c5104c040d0002c0015140c282800c0c21500100708041e84213000d0201c5141e4440011000a00d813044503466584600380d00181c50b0382480d05803406880b043d000780c08126840c12541e0744051603030045451480c1c059407035150400304031a56000d00c81d001040d4108502e6003042c0b400204c1644c00300e68003828540c0e5241000c0c80c0ca6400c103206130b041001c8a250180c10b10090241c0c0ca94414142c4c1c4c0d80126622810b9544001034586020300301825505501081c81030006040030103105c4104501c0d81001c030039038000304c01c000f418004006015080340c2c0d5201d04100a61908200d41c0c103406140800801c10b5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 310429298 1250 310428048 310428059
    0x20d06090221150d02040509030d0c030b030d0c1a1e041104050f04150b0d0203030c0609070e010e1603020c190302060703110d020f09090f060103110c060412030f060b040915 76
    0x90007a13592000c0d10480d902c2000a040d0901482142c9840808503410001e400549a01030000c0410622150280c13141d2903281e0300e0240200e0b00b0352000790700030b00c448220801080b11140d13407120090038112044e820078020b4002030002a20140035511880d030041044c00c45209000440320010041d005600c0480306202c082840c402440c6121943c0321808030707032900c10f5004180050100d00000350180300000b141c000100d03003c1481401440c0c100282d90200d5540c2c1650ac581d8902800ec5403141d80c822408038000c2c03429401d20b41c105001504015041286c00c8417120709140c502d01d149920b005007082035108040e0305204007035014209043c100070603804400d10319014098845070b0050184c2c00901d400700d0140381402d841450000070b203440d03102e1901b1040c0c0d4a01c89020346072203000c64101918410b500c8265401d490144007070400030440c03684c5648603209810b080020304070605507507000385001d1030410701505c40035289286126a030b0782e1424003150101c418841d98401c114040e40000d100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 310430548 1250 310429298 310429309
    0x61806090a0b060f07060614131a0d05010509060f091506030c04090c06020c0117040807020a030206043507030219080d08041a04030f03020d0609022115 67
    0x100194140d80d01900c907a20444104020031a155245500a401194080556618030003c02d45c461213030100303000c401d590302139492a50140488540c4d00c0819030780c007818003250b968400254403c40001b03c140030007414000c58075850507102c045d03882e80d4480c8200990940308204640e0032010380026540b0038903102181c1620340041e1000c0643c10301c070f0b940210341c0c1c41d5802c02902504c44802401001007910501e03042a0f81d440e02d2103010054012010307101180c1d8040c01e0741141b07140854001028580d01c42c4d031580485e82c0188012a40000708500110268490130042c2000d0892000c440101d005400c0b9614002e240c916000c81d8803010902c00403a04810224030b2000b141d03030641c2c0940c01140c00c64000c008012068014100c1481060b00301032481394004240c6000b240104141c0040d000007040c1141c201008440103400b0030895107044450a1182c1e00a1070390042228000442032b403554a408280e034000c007200c495852009184043e80c1c410302001035001141e4041a03114100c82001090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 310431654 1106 310430548 310430551
    0x9060f09031103130905060d05010c020d020c040501081c0c1b030c080d200304080a120305011706130309151128060e12120f0618 57
    0xb112000110441d0010002040c00001d1103041500020107420042e2030310ba002545045100d011410a205103520100c0c998040c10000b141c02c80001d1410703455000892103140b8000c010014060005004808080120302801c10304c841c10324241c60395a00310001800c0c0827080040e905810141504043c2500c0c441c5410724a1a80c403140559a1885024902000300d00c10240c03124441c0300305c200e0f0100e00d4a41d001101d02d8651515002401c2c056021000c42d081010040c1a07105540c2501601c2e01603c408803082800500300312507140c0d0782c040075100070303020a20340350f1200a061168030b04102400150044520341e542c81c02c1c00401d000d40441c0c01141902a81d441100d5880c03c68880c6031070341c0c41d145081c2e24480c8103a25403100600d400c0284c0c100300d228010051944440c40720181031003140d0421528000d290901c1040403da10080c00d840c0300b204040c91010301240c043e041035 = true := by decide +kernel

theorem cover : BRFrame.Cov 310251798 310431654 := by
  have h0 := BRFrame.cov_init 310251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 310251798 ≤ n) (h2 : n < 310431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
