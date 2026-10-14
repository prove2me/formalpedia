-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1553
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:32:56.547989+00:00
-- url     : https://prove2.me/submissions/bbf71024-44ae-43ef-9238-a16970584800

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 279136690 ≤ n < 279316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 279137940 1250 279136690 279136721
    0xa051c0603060e0c03010b06041202010c0501021206011b0201021c02010b030f0c09071b11010e030105091b100e101e03141014130b120304030c090b1003020c01 70
    0xd011042100c2a00141003045000046502c07200c806010942280c25141c480e41c2d2041042004200d81d0303841c065246005801414900e00c81102d540741e0900303990201400c44020b441c00000c11040b5030b048250600f00c01c0c2c800e1a042184040ea03400070395591400302881d0180c00d04e45050940e207610035040080c0c41c26018054030010803d0b0030301c82c0e40d104c50ec0e10006114002810010f00300910480741c441032019291580c1c5d0a64050352507040c1c1111801d00e02c241007007828002c8001c0c41d10f003401041d019604150041000100d0304010030303d26442c00311b040e80305505201c0c00428450340400b0190380c0c1c1c801140ca017102c59060450030b5480041528001035200e0010301c54950842c2c040d03010803150416140368030b043c3d9a91402d00040441d242c024a080e06201c400606050304001141000000c0c1c0c42c800001c0c0d02d02440001400034070107200807079203940005030a00811100d04012002006610400e0121403501000112021484004d40041541c0841c3c803091142d001d402c00210901c4424 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 279139190 1250 279137940 279137951
    0x804050f12030a0b060f071407090519050610390c060906021c05031f0b0919031208070207030606230a1811120a0e060a060302060a051c 60
    0x41e98081e42d42044a6224070149025420030603801c1c841c0c11101110b03a084555131500e42155a0300c424001d01c0c007031843c0903200b00c01010610000c179106143c01443d044842c200341486440758136050b240020708940c001d04031050150340103900494000c4d1003c41c0d1580040071595001c03240b030600d0f441c0c445035803008070075031400000748442c507642034007920190340c1c85198590311540160307514001030041c6204a1052101014024840c401450704040e981c130845070080d41d45c000d843c04045554205030030721540018080424900464032500421440c0803201e0a2403440e1120303c02070b036080300f0040501090300c00107848984280201d40295030301c42c038104034007070b2200d640313621980d4000d01d2000c0080d50143d03200c5a51500d8254002207030019042140c80307882001d030f58405000700101c0181d002405200c4030300d0144c08a0300d89882400042800100200e0034034180d4603156002c1c2001464a151850600c09a1150400c0791134801003030604503640d0b12201d501040008404048031415880c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 279140440 1250 279139190 279139213
    0x9100302030108161a090d0c080d020c09010803030a020714100c0e01050c10020d090f08071e030e0402070201110a0b01361109030d05030906010b0403020108070804050f 74
    0x6501071030581e80c1c0c84003100c80200d0245040c14100440c1d008420303810344114078200308811000e0090002c0304015044c2001c0002c150746801140d246504050f4a80c0c114840346c0b0f100f41d0b810407860483d044121400d941952500000648038400500794142403500054000c040c0104c14841610100380042100c014159110108004221024200001404012402400c1d42c4201c0964281801700c42c0509840328070028940700030740c05030b083c14070031320b031039603050808150750011028010f0701844030155a00c0d846d107801d007000646880144410491960102d02081d03100648403002c000c143d0f07006a503060304e0f000580d00140c07a0340c0e1040d403038440c0440c1501085010400d80e070481e428002001811401c0c2500d039400d00301005600850300042250380103035064640c00c800c0c205489041110b24100c0000d010900304402d1514081c0480c1c80001440000c035000c1082a006203490280141050705640c0001c0c070800c4042d00300401c1000034030116041c0300d01440344070030000e00d217400c8a5405086 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 279141690 1250 279140440 279140447
    0x606090d1a0123010c0507050d060e010c050c070e0402010c0c06111e12031b0a0504031b0e04020f0a0503060a091401050103020f060a02010f0c0903060e0115090c0201020910 76
    0x420041e544941072000024000700524044451900d02007200081d020184004507400030001c2015101c40c800c0080000e019220f081d04500b08900500010618103480700d40c550170340d4040e450070003c0010070001140a01c81c0400c44000340c44c5c1c6180c01d0542c17600c850004a4040000c024043c01c02c10038080001078442d0054191200003031280103840340c0310701221081b014280a90303113081c8075030840c8460079800242c103030085501580e10151944800c1c96000614019080130784400e01044000505209210400c04000300c84074948080100c0d050909034504004140030f00024042c0346030a0070030b081740d03882102c880017030003014080b50664a00503176540c2c01b400d191181600c16104002c84000901c406024180c10b0342d0300035242c00c01c8441d4140500030543d00600c29002103540e207294000c9820303524069203100100741e540b100300e29800c0d418240d0403686200d20040e1a6894400c182840070040e076040000c0710f001550000c1e03501080107060380a4480d07a0171903580309040d04d4900d100e584c1c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 279142940 1250 279141690 279141713
    0x2310050406030f1109040f020d14010305060a0507020c0d023f07050a1406070f0533041103030c060c070c06090617100e130b060d03170606090d 63
    0x4950350300f8465820b01d1075203501240c180003101c080511003040761610a04040c1c000e08458901840018030b050b40c4c0201e020225209003000f1102e1b0070076100100140310003044016040314001c4802c010740e0800400103540c0e121120141c03070040581d48945000c0d507940f800c102451121001d5124454800120001c06801090f035481c12070341d180c0204640020800580001a00c0000c0c1036882c001c0e003040a040701c02d00e41d04a41a44c0700408000c00b000240c650007100051500c110018038403400c00d0300d8039520300022444400218034840c918002028840d00342c150700103400140025985c2c4441000c00e080d846a07a00300f0005214840c02d2204052000c001005458011049410165182c6030f084070b0000c950701c11a80054405085200030348040000907070403042074550b21165a55800c800d05004108540351107000310f0724a044828041901c019542c0610100c62102601c1210740d0013401101480795060154024031000a5042d1100300490b2510300c0c0c003d000313102010b6140f0300b0b000328a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 279144190 1250 279142940 279142949
    0x60702010609020c03120406060b19020d08060d02091b0a09050a0806090303181c03050609010e0615030414010216050c01050403031b0302100c0207030605060f0a23100504 75
    0x41c07070a01d000480344018401d03581400c04090140d460030800f001505030340e410141096800a6988600240420010008007440c400341c4003030510781c1c0b00d040d1000e42041044150401400320490400c51301d60344103500125896030446001c0c040c2c0e1070b0f172440c800802040c5500240c4c0d544000410001c403075080900601218130850704161200e0311601c2c0d107500c40b2019104c50b6915807041c8042600c000741300404114078011039080703c141040c030a58108540a4150074840031956a0090018900380b0b006c10902500c02000455543c1c10002c002c100845140b88060008030f10100101d0100645c080d01d181303251101400030354840360380d0400b4402e0368045a00c110b40522418055044a50083c4261130403030f078158407903941e00444d6080000100581000c12400c6004220070708441180c1071041354103a290a500600810303045141180440314081c02d032502c94102181d14440c2d82d951070b1036181c260b40f811000f10106112850450143c1038910100304e900109410003265aa80c0c00b81c003410456 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 279145440 1250 279144190 279144193
    0x160203160e060a290c010516080f01050105030610021527010c02070b0f09031608070b041a0a090f0e0411061603080615070807030908060c041202010c080c060702 71
    0x1500d0342c4007007084210441c490310400d41001014582c0025685034007008282c001d41481e4503021001003000d0031108100c80e85a81c0c188a0030824075203075805000c240d440030803108030f0400b039414880046e0160000070301880c4900034070000d00210f00d1080c0640b0001000c0e1440400490500c00390706013440c00c0d460100006104003140b1440700d90814041e03040c16001c15005007103000c3c11301150110950240d03900302030324142008001d00341e4404110f103510b203c070000d0701811075a0800c0800c1c0d0612409600c90740c5480e6081c441407001d05032031202410301c507000c0310005668458000c420782d075030180340d404002011503415002400700e01d100300b540d200c0c4d845007039000c809018800410110340074441030b8840a561240c039540010703015500701504008002c1c4451150031910320390a0560344081011154144085150f00c100350f04030355101c000e410944054001c03031500000091050080b4440c084011901c18039400035640100001d44040740c11120081e50b80002070398140c1e43d008244c441c480107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 279146690 1250 279145440 279145469
    0x405060609070f0c03050a030212100501030b060906040e130507080a020102010506090708180c10092102011b020402090409030201020a0807090501050a03050a11040f140f090a0216020316 82
    0x320b40c42201050000300c200c0c0c640c1c040d021469141100da64100540a4080c5a401c002400d803c4030306c408003070302c500d0040c00b8400341e050406000400341c66aa1400c3c0c0d000b400280116500c5a07501c0b019901615409802c05075555541203800d41e00555210001e0141e018058021802010200d8001d603064000c0c0c000740111307140c1da42404640d50302203d102c400074446101046081480c0300b10f902030f441021081301c110350320000002e1841560391041c240490046081080f07030b20100b5200c4044441c058860500d10800c580000e450b0551a14042d890004060284000c43d61a07a040d110101d07070181c0100612001450064000e5002030841c00206e411070000401d00e03032003060140300761070041c0d5805003040110345040d009000058401c1c50080e484107451103103e1a0a40584000c21800c0d80c911030103442c0411a41030b00da0f241000a0080c4060444c0340700170348841c500a6000508104010395420020303c901c103139401d54880c000e5050042c5500045840100e186042c1502c80b00300301c1c50b11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 279147940 1250 279146690 279146701
    0xd1e0605060d02100e04091211010f060b040513090f0804050301050f150f0307050d0317100503071a09090a05060109080102070b0105010c0813061205060102030c10020a030e03030405060609 83
    0x92224090b009512859201200c07001501c6180c00d1903154001034004214a21039070303140d00082800c007101e10001042c544441c55550004d002c7c0c0a0340c0c1040b51420046035041011010061003140174aa0007561288482c003d5400130b64000251180c201a01821031021440c3c009241d500c03500c2860321035802d00e404130b072440d01595070340c80c015113039007802110716074042040c0030b089101070b0005a41406a400001150b03110700254218142c40b90740c3d41d000b100194040403844020150040480e800704070030500c582e0310000b8802c03050301c850701c1c074001500b240e03e00183c41c00d1042d0420340b5005080c00051000e0300280d41c01c04c0b80100c6003602c0b5084181d49400c80d02e400c078007441c600640380d03002510041245500654255100038000c0130b9040c81d10410403061440d140b07050740300300300042010071585480d0041d4400c840e0896400d1000d5440c00c0000802c0d55a28a9410050a20203500098150040380660704c0201556000f005407a1685042d04116842d04021152140103440c12000280d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 279149190 1250 279147940 279147949
    0x1510080601020c091504050103060b030106060c050a080d0e0d0207080105131a340e0a0b1806041203050d1d06010e0a2703021e0c010e0d1e060506 64
    0x34030408040c2d00501c6544000d008024901901420241c0c0d100b08403643c1003629112401414080e60281c0c03004207103848801d0616007191025071101c0100b00c0305417104400500e001c10b564164640000f8041e84980d010b0500c1e070028170562490b500d05103d4545450303e180e40104102e0205c41e8900001c100b19591404455004001f8050080100d20011000c40301860f18210b00c641111060038181880c03010790002c1210950224060420030907003803d01d2036043e52142d2003820010f020f030740050200d40707404d2003c0218001c1c6802c40035082d813402c094900b1519040160343c000c00c07560004d4005d030609803d001e00300750301c0220303408201760418a044810700d80d070017032011403100800000e010136803a0281c081541400507000a064684401190f032810018000d4018401c0c4c05004e40c444c5200c1c1440d000c1c2c58596980510058000505408451090041103030740c0e00300000e0a10210b511100000030b4120303600a80010035a01d4a041e038055000b13080121100710b81c1c403401c001c00a40e02da080400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 279150440 1250 279149190 279149207
    0x605210f160501050c0c0d08070c120b0c09010e13020717192307060b1c03092601050c090907050f07030309081204030806211209181510 60
    0x41a5450900c1c900300019442840242282404101625440a50200042c0f1800d040ba01b040e1030b03413200810b4203800d006104020000a080030070030284000c0240d038a01d550520002c0445405d0040819421030b540d000f6100114640d0008200c120000c81c80c0000e034000b500011002d64a00c00704928040c00f5001410444040d4a4622081c1101c1a540d020844400c2c00380c01c84002d44186030201e82c8000c0c0201000303080f26034031989001c10f000c20b1090900034100c0d60061070383c418203610503601740841c1d08020600d00350303034002c100009180c4901d0480c1700b000c0c00381c000e0313451298606002c21580a8115024004801d0205d40403c0360362a454000c8a5900404811030311890040091710000781c025404240f80d60302c155021400c0c04080c200c1d101e41050212410760214031150200310302450020440503903c81c0103c28540010000090715903140f962201c014100e020000d02c2109683d9410001081d403c038a80f841e11083c50100400d845640d0000784070350144503807050702c1c00c1260103030144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 279151690 1250 279150440 279150463
    0xa0b040504050c33190206070c060c0507050610090b100512180a0309090522170f0408010624051602060408070806061302090102030a0309060605210f 66
    0x2c25001440300b00700030001104400ca52040c1c2c640188500c1e0000404400c5488a08504c021a44402030040c4510381c4002c28940081150004820050f4641e00855111f04040e00301030001140001d0a40940b000d00c07a0490152181c0700708804c1200b12520b0001030815200114020b00150041c003081c0244a9450070103000440c02c1449800300e241780f80c9104a50000340100007005c04a8011462380c1060546030050b000105944418000c0000c0d501035590000000b801c580c080c0000e44014800c50080488002e10001e5588070076800c80c038080e4151001503212616203582c80b60360325121170081450748074008100d2002e03ca03000506826444080d030810180e15514a81030020b5002000b00c0e800e2a000ca034800c406020115040364100300510103071110724018034090400300200324a81d81050300c0c1c102014010000b006140c4d90104c2921001c50860070086201c2005107003060141074603820058120980c7c02400724070303200179040582406820b40a0302c2003050001ca03c02e49400d45d0281c6c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 279152940 1250 279151690 279151693
    0x7050604080309070f0801232a0d14010905150d0609050703140d09081b0d0f12050a0f02011a0d061103070f020d0c0c1205030d050903030a0b04050405 66
    0x500401d4121004591210402c0150b84042d0b45480c2e031080103041c41d070028101381c0c0d51200f00320240200c00c1c01802c6175000c4000c041038076180800d107031041102d0301201606003400091143c001c002c840c0c4262210820211028021410718101818450b4400d2140410141c20000450b0b03c0001c511000c043c40c0344003030054410200240c50720400b510080c070007190340b441108800404507440000700c08011440c6409485c5454403400018201d24060f000300e0055003080e44950300d010491642d00c00300c0c1d0000d4905158071141400e1608585940c924041c1403c0b032030283e020f80e03280e0310000400201080c0d88503022600402002282241c0008a006134010541d4220789454030342a00c00701801e500c01c510101d070031540070850441541042d1040d20203c1c80710292041c40380d03014006464403040703038034083d42041140e031119605c1b445244180811038100221030300902a017441110714005002c0814006801c0524110f44d0300d90080b00c01c2d1102d5803411600c01d515203000c0c000c40b40076582250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 279154190 1250 279152940 279152953
    0x117060906060f0702040c03050702070f0b043302010b180f24040207060501030317040b0604020a050412030c020f03010204030f06020307020313141306050108180718020d0e030705 79
    0x60200382c0e8010f019510011a081c865600140ea803400740114180301c80d81d0201c6c0600340342c00003070715000340c1c0d4020303440e03400c51a1418000030500c00c0641f011105559a022441300071040700000c6402101c2100070380c3d0180b04102d1103200d8054004103032440d420f60b80c401c40107040b25840c100c01101030783e030203565004c18400305110006a60001e000e1400c9800103451207854000098102d0388050000c40702c0d16103400041045c140c00950311060340b68440501d18886c58995245034500f1801480b040c460f950104010680522520568015040142c1b03103405146260901609401e00c44000701d100c0c2901c0305a03808582018000e8034122544081d0381407220106a076144043d4000500410440c4014058040c40c0091100003200900c100345940c030200485074103020811680701404010141044810031007070340c0c01111164405421411000c070700c25264065800d1032442c1c0d1050b01400ba10101480b040407030f039801441c0e000300440d405c120b0850a15035203a243c3c083c4880240050b00142c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 279155440 1250 279154190 279154201
    0x30506011a04261006140a0b0f0a140f03150f030706021b040e160305060903070b150117090304050102070f08071802070203030d0b120708030d09032c01170609 70
    0x8903d20242000b1050340c40100d100d60b030034030032a191948051212141d1005000343c50812800a0002d05500c0c800103107040c01c510f221207a80d01c00c02d030944082191101001420000c4001980d0454612905166682c01c1c242103101d907a45180c0ba03c03a00c0f54141040b4070f140c51800140403000ca40703203500600151900310980301000900544e0058001c1d45811640700c0060f800d00854050b807258000304541d490460929030301d84680281a00c0066100b0449640410036a110181c0c0c0700c402c4507079000000c401d90004031881861900d801e140000c4841c20700034414408000741095034420703800c55035000e075541d51076514070504e1320810220f500400820f00c4042242d0780110001402c44001501e0103005901107851540006d6100c1c5020b0754410b8010003501e000d400c0fa01002c0d03194801000160b040c048000e84030312500c0401040550788415000c00c01d40141424111300b01d8445021184170040c01e080c00300a11002d41c3e641c0004c00202d001e006000100107503d00170000908031900d16941c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 279156690 1250 279155440 279155489
    0x30606031f1109060a02012f04030204020a120e060106020d0207030c330207031505060a0b0a0306081209030105010e100308160525050d110d031404030506011a04 71
    0x2001c0d10b070b40003020100000d454940b0340400170410f0940581c000250680740700403070000121005ea0341540a03a0100201500844000c2514252601201c0059403122100c0007541c0c1c8002d00015144480c0c10070110400100001c03030100c1c100d5500e9001c0d1101c0c4803134490202c1c0c81d81c0190000034454941101c05202c2e813030030703004000302c1030320807032440000c502d4241c650029603900c01c0f66100041e07101080c14400c2204c100c040078110054140144501e0420030300107007e04450380a401c0441c038011401404040c8690482002003c05209403142480e0301d100301141ca6116600c9603000c1d6007401c00000c0c22910441001e441036000d0803080e0310b11400d641e0740501301c0d07012940101d81c2d4149124402c020500c1801650444d1420781720b070103200c14003841d43d00242d01c61684080d2003444a0260314010407000314044a01641c200c0d4408450300883c80c0944081d10780d520f45c0b14003110701150200420600054041c141ca040d030107036503403030303050038100030504d2286015880013003a0110140e0141c00c030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 279157940 1250 279156690 279156701
    0x24090501170f060609060318010b0f03100f020d02040306050a0e0703021005070503040b0a0507020a0e0603120304081308030a120605011e02122109030a0e1c0203060a0b030606031f 79
    0x40200105d1030100943c0000741140c10945240302010100a4001c030507030700911608252440980342039407440742c80c2e40000e40303070141d81c490005126112410240d00082c03a034100d580fa030507009011501c2e95100d081c01c1008001c1201d075851018941001d1034005100028060201d90380248910114807a0035800c65054000007401c43d042c3c442480080b90220051020788200017903580d4864603402d0500400c090140d0b10f90000c106001d00c4401c2c0451a02e004c500140c6040b01748003600d40d207403224a414005071003048015903150a2174400880c400e40e02000810500c45e00d1713510140c1c0c00003046241ca0403294244201400305100310707103401c20740c0e181c000c013082c00341900c5c016103140c181048070b0894168003101d00a03110820049a0b04d2120403016150707500410301e0001907081604844010704a43c1035254414440c04c841c400a141c0461300c80e070542c400301e60280c1502c1460604090010207000d81e0502d1603c03c0c0152000103215040008007080b0150300c0d41d1144411000180300d0400904 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 279159190 1250 279157940 279157951
    0x402090d120c0b04140c0a0f12080d0603030207050a08010b0f010e010302090301050108030a030f060b0703030b030a0c090501170a0201021c020705120a030f02070f060302031024090501170f 83
    0x1800242d03003000c0360100d60180d00c00c07400380007410600c8441c080158203212042d28164881c1600303240a102c40247c0300f0702141500c13a6480280c9400c04103050114060042a9503041c0306070030f106000c400c1580c0850b0405c1115016111110840c1c4c950301250301b07030780700c002c201c0b07400160340400050258032400e220100c15006060041c945a8500042400c2d0740090b002800329920015142d1005a8184103c2c0081244da10b03081203076900f0404059401d00c501c84003c1e042540b203a81600c00c4e60341c1030046031441640071114007040c40d40c0310501c1010340424414490b5020303520b0781030b2420407030102c0d4103004140e05038040c01d108084000b107015a410b607020070004601c1781d030002040c5a20345440442e5000e2501000700402c241a1070001c00c4110642504d0045400401041200d07815211803082512220304026807203503100c41e00c1c0304442c560381d84590808400007a4024883c10751b1064070500c44071543d2803400403520341005503841141c80803444040684600010540340301c1d00815500710 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 279160440 1250 279159190 279159197
    0x204021308010e0d110a0203070e0406110408100b01050414012307060203090c01090b045105030c07060207050a05030c0d081e010e0a092f0402090d12 66
    0xa80c4956881d42101c0c0e4503803070700b0115030108544200c6103821020030008524400000d21603034030580d0101c1c0c3c80305280c0c491a802e40842300081010407601e6005924042074443c0440c2d1a540d0b100c8401d66101c4440803894000361a103100240d40d0b51150742150b0030755000c0411080c240c000d42c801112000d400042101020b00c1168a5031540c0c80444000c266507809000c0c0540c40781405504c2c281002a04142c06051044440302002003c11083c00d950403070b031040d00002040e0b504501400600c8242c141c00b160404081c0400a09400104841c4e81032030142c4100031010000c1d00c0e1041da8244420380302050034040030b200d000c00250b81900100040c0e0700c00c800b62090503103140c0e2044d203584c00402c43d44459801489071007110b560701c01001d41c2e1040c4401000c01500d0241c05400f02d03044010f000314802c0c201440005918207080e82c108030310341a40308901c1d07801d4044c640540325512401c0004150000304121641202d0300e0503009681006000a014200d51603069440e000021440703c1e461003030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 279161690 1250 279160440 279160477
    0x6060f1c090c0b04140303030f13030306081e0f010e071206150f031202010b01120b041d010e2a010503040218011e0b070c06030510030203030403050d02010c0f0c020402 74
    0x30710306100e20b4010001a0180d60f100c50a10a619019452442e05503020768002c2c420414011a0200b41c01d40010000d000302954090300d040803005084507400c8508a88500080c0c00c100f01c0ca404011744591a00350280c0d00b1080c0304500321401d031040e03c40003a00e0f03030780401d1080c00781c011b00f000074041c200d22500c4000f9080b5002191000d801d0841e600843c1d5a1134034244c1002030080c604070310080010188020065001854000390980c12024001d000e4140d440c403100e4020344031079000000318168082d080343c1140c1081c2100780603014011803211240503100c84c0880c62021004280420041000c41c1c03503640d03407c1c0004540c550801401a640141180004280c5296900c0f0320f90113822400d00000055080c00e280c400702e400360740d204800e40700c001c01810300860700041182083d92520300e4085040e0300c44440100d4000e0345a00041d6041c0400540002084400a80c4010b40030040d0000d1101144002c0181c0e00800d03108022400315030040505001071a06070300074441942d00c24134941d40d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 279162940 1250 279161690 279161693
    0x1501090e0108030c01060506070308150604081c020d031406040e03090607120f1727012306010c171309060b030f010b0c0a0f05010b030313030b06060f1c09 68
    0x22403000c0c0e01944158000107600144603400b0b000b16009070000361100c0b0f02e80005690020030888005140b080074104107818882c0c40d903648012200180004001c541803036000c0701302a240e03014030b0000340d8007600c42d040c3c4086505003e4002c0d80700300c2585100049890b0348810911018000b03045624905000400c1502c070710360b80b98800380c84564000d5070801350b01c0b0900c240252682803811076800500c00c80c00148010342c9910010503500c54068001c1e900e00400c007904003090050b03145010070082d400e0406401078506e440014200220341400d9110b00e98032900d0040d40e0303030001c0c0031004e001800c5841c103001d51510141e0051a64030f4071421030a2207155900700340700444032950400300022100009100851310041c1050b409020150308252500035500c2070300c3d99450b81090014410580c6c103d26005008080d0302c18200c13540302405581e40c503208951845180031440c0001c544880c4504049007481c2040760546000c0c000c2460031614086480401e1003000550303110252441e901e1b11105030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 279164190 1250 279162940 279162959
    0x309010b1207060315140d020111100b090609091e07120c1e050f190f08060601020d110a0b13060c0329060d0b0d06230f0708150109 58
    0x104200184009002054100880142a50201018941503000d402070600211b0104201030078466000c5401800e520700f540300694401c1e4042040718040d00500440004810003600103030554002111210b00c195240410043d9802c0141c0798014503901c112003802040260003810219075041008070780d4907580e625000c1d113800c4a140c0c001c442c20700005030104a9072400140581c0f03118116240b82c690b4038184804911012012a22180720f010348141c01100240502000c80c0601a0328402986080e201d004c5507540c1d000070348009005105400c030b0381142501c100300245008c206000a03007040246500c2d451b0715101d0250043c03c4810078404090006201403244451520b6242c8021a501c1e0054500e0046090118030b8a540c0c10b00441c529a05661260101c804103101500300090384055200400c9403c00b8008004012034030340244c020151610f4104100100d50500344000765580e01c3d50300b00865442a980f8501144880022032290344002551b1080f03820103141c4903524541c2d0710204c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 279165440 1250 279164190 279164209
    0x602191403070f1505010e04050c060f0d18050f2406011e030921080f0901020418050402041a030a02090604021908040209090a030f0507110a081b0306010b0703050309010b 75
    0x1c913250351811000407542c918a00400d070044c41320f003049002d5031401d40c0303500d0f4a030412400340e18401e2000050b642002e450a1003078503442102c403681044015604a0b100984400c5464280c5861081c0101001200d10001b03190b5190b0071500c04010000d60f00b04003803595110007601c4541889450195004003880131500c64500705e10b80c1d6004a80c0000318141440071001c241c4541007100c02002c0d008030301c1c5801109054100d041d41d2140300c010f0350b60341280c034020301a6400000c4565030042003208001c0194024502960088400708080d103001801c44000d0301400c240c250301078014403150b401510300140859440b07440500003500c0c000307440d408040e00b04a440502e40c08118018180815400c0c00ca003050390080b0b0080081039410066200070700ba5601c0740c600d11040140c002451001c0003816401c503c061880a4500c0014545401d1840e445110038400c40c400382c04d0300118000304c0c1c034000ac0d90b10304940658400383e141000720348045030103901c028035058403036496084001c0c05440e0304098 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 279166690 1250 279165440 279165443
    0xd0c03021c0b100905030d1209050a0503030a0b010e13020a0905040608010e010e030a050405090705090402180108130213090602040803040f030317070f0c0f0c060201150602191403070f 81
    0x10b514030500c08000b0740f80d2500c01d0b800e00700021280240155100060383c018102000c0c00c02809800c100843d11026094440c0c00030120301611444808001c40000a58003070042c0540c107001c0c40c00400300440700c250102c80c0d10b95109118811210b22801541d000305800000c903c0e00980705038480020405855241d801080c86a42d039003010b0050308428855910344907646ca028501c1c103040f007030008110380030718040c15200300107210106001c50700441c2140c200c6000a07000799203400880c1203245d000002c801300507000c5010600041c00004c07801025403c00e950060a0300d90000c000140c25000305a4100200d621580c02c10001c07c191f8400c00c058001054040c000c81320300d81c11480c00074806000c125064444010403c1884046a0003001054a0a04030301d0903040e06403040c100100590217480380a00302802080000c11800d6040d00609643c014842001401a40da20400c907925076054066001c0c00841d11600f400003001040d05200b041da81c0800c90b401c20285848249121054240 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 279167940 1250 279166690 279166747
    0x1030f140d1d0d020f040b0a0305011802040b06070f0b1314010c030c0915050d0f0c0c020123040b0906070c0602030901080f07021c1e0203121b0d0c0302 67
    0x70400700250b04010030400340b00c1c143c5082c5240020755000c224a0620124024480ca4403401c517045161134650304c0d8001190040020300070103401103503102070040114020780c0180d090080354103032400c1c15012548100d80c05100c05020004c56200e446204030080d1a0065003405107a801f00401d00d03000c5050101000180000346286580c4c8028045075000b04664062003140d4208001c0700703084100035a800015030901d1984e844030601198000c10740b25400c849450f00e8107007010110b541c01211301c85018030030b0f22032500c64404041c11a8014284115146401e1010072081c0008088000600340d00040917180c00d00300845955120b991980d0b03508480010780c8041440300c1950307070200380c0ba074001031220701103001401c0c940c100940380c203241c494020050400314421681715203c0d0400c0100b40c0d00529074002190040344000703440c2e50040848008100b1480c0101d0300c41101100410150301c0d58540d85450417505813899805420650341c19014181d0911596101da1580804034011030030300c02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 279169190 1250 279167940 279167957
    0xe01021c03150e0106050703080702151302180c0a0e0f03010606021b0a0506040e10170c01031a0108181c0306170f0d0c0203070801090b16020607020601030f140d 71
    0x600d90100d4160750303120074418100b00f0010401680c01c101102c55850301403404401540e50218168500140780c2a00b00f100b0072610104140041080070b0002c135984200d800d019602c00b402244082010140c1d5101481c1008201c19180b080c0685000d03011504094580c40510191000003421154264852805a0010000d1007170000000c0a220748250702215851286400c000115030140036500802280003a000e012440441d000c406850081072080261010462040c0b01503441e606d0035200e07503000c2400c1c000c50024201c0000741400ca46001a900c084050352400c00d461964104e0700c3d01030180d0702030962299180340031030100000a90040e200400c1d02c1e8070b050000b40f01500e84000317407d5103401001c44031003660404250315014180303500d03188c4014426400001c2c1041010740c0240a00e40c41e08640ca4200000074103c544107002c8850040c000f0309008900366182e070400c507918401030b0130010050002404101580e00124041c1c1034203400c02d1914800c1c21b140c00c0c5da038103840001c00c54a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 279170440 1250 279169190 279169211
    0x1011030f070209011508070518030d030f0c03050606180112020a020a15020a080a0f020f07050109031b1104052706061003020406080406020703020f0601030803010f0f0b0a0e01021c03 80
    0x10f030f1501d004140580040b082e2090004000b40301070000380840003007090010380305100c45000b04000005010082c1698210b0002d00c4024008280d55002c0b100c65504010002900a01078424580714400280586103080300035409540c4c54445c605c6958103010054010700324a4566101504008500d50014a03072440356041c641040d06540c0381c040c0c2c204d03004002421000e40e12521054020f0b001c190003098501480039194040d000e000707070500e042c0e03c02003100810b000d0705411400c074030ba0180c0c0f80c2c0500c41000e0b00c0c840f40d200005a50140402c0b007510101c60f00f90030700d82e000a62044805411200340702c95030761302180411440c0c503070041623030000041c04424901071a80300003040d0786d42030852034246400005804a000104098102e6034003240c80d4082c13500a01941d0700748900c800c141c030389a41e128601003111303400a01a280c0030302c1355114081400c5594078540001c1d549100f940c24140704e9088400c441020111400c81d0444c0501560f528200008000c0b04200c01401d440114414000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 279171690 1250 279170440 279170449
    0x411070506070e0d050c1509060f0909010b04150804300f111203060d0c06020f010b03070e0103020f04060b16050105160f0f140a05040501080f0103111011030f0702 72
    0x207121040d0321031000c6544c1c0000003000041c800c03902007019529200c803201c81100403a12406a02000c5030071000c0080d0300603040d03005200030254058201c49000942c1d89880140e220760056000b28052070b101d40e51407008280c040e500c000d0b44a842203911160468414013004292824034a82e0310340794808089201a03140c200341000c2d9072504510b4641c01480c18500e01c56035541d42502079944101c00040071805c1600d504841146081d006001003800a9031000c000b59112861804c98005520700718080130302d80340c0424043c04075410050701007801d0742160200041c070000803940c507501944d01c0074000b03002500080600400070504c803d1181640050609074251000181079409103407034a03040d036200c03a41102c081c000f084271030700c0c01300c410510041c0d00b0b44000c11403451080d040640883c13003001e000c0d0b100c00140140d500c2a0b940d181070341c80304d40d43c1103d912420f000042004520b4001d0140c41d0a020b10114000055403030005a420400e48a5034107503840400c004005100004027081135003030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 279172940 1250 279171690 279171707
    0xc0e011404140c09030a230f06040804050907020307050a05072c07050a170115030e0607091a040302060301170106060203160b04030309080d090b0606070302100209041107050607 78
    0x9090324244508051100b0220048030000c02c1050203480209201e8003d460804c50b468100e50310152403015100c100419950b01d0002e0b0740e000e1128840d0101c0310035400c00128020f07020320743c01138042c0d003000d080030100049000000c14800031403000348003480205200300710000401e03001310003600c425821f00c0d0040e1111104d503900e1100e80903003443e130f40c4414040c00720181d5120209142c40c98561741e410b1400c41b452f25004200c194095100400032844840d40c00e80c01c54481410b440820010b0550081d060711541c040340e514012500e185410080c2d4241842d280146040e40c900a40c075054482d030000315560001e8003c000711701000041681904001d01c1200c01518481c002182054201c48010b01c00c6402c43c003000705074410042c04201054081c0c1c0044100c2c0b1b038003800881c0c8074031075040f000000b0705400304103071022400d00c004196a4244141107403159070309640984007099040c4c0081010b50702c15501241c209270fa8885201042903680081e10307100e4883c1d4041d00b514203100748000c10054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 279174190 1250 279172940 279172979
    0x5010f0c120809100c08010306050402011707030e0c010c02030c150d150503010e010203040b150f1005070c060e01020307081b030403080d060503031c0e15090f010e0d021213030c0e01 80
    0x189400c00840c81789030440185811240e1014000c5030640d1503100480b8010390f40b40a12801c0b078208014080300319099007101c25003284250450320008170703840044510700321141c7d01a426400014400c800c0d03040c00c59142c0a641e11040ca00303850700d880501d0340710494100d41403004c0360390112181400149828080c0c10b810401d84002541903007426120005a0340018144c0c1c80e100d4800448000c1c25210f400b0003a0302c04000400c42001d0104071540500345910524085404041030b0101050ba0790092455001c410810b81c01541010103070f0b1396454143e8004181e45940c5c00401180004480c000c00041011b1489001c509441d0742c1d00740d0020040d508640c100a109820910004245d107a0892040106130710742d1302c001c5049094254a2800c1c02c042c4801000700d081d0860070070143c000c2c001001142790090400800c800d18486a0039522600307000032400040e000300e00880001c4aa800c01b90159140307010b034590905a0b6941c807200c40c500c840c1c0c0a601240310481c010003165050780c58642240707 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 279175440 1250 279174190 279174223
    0x80d0b06041e2921010e04030315080d0c1110050703021c0c030f03020910030b0307081f05220501061805060a0308030a14040503030f01050d080405010f0c120809 71
    0x24510810b248145600011100d41e40b1000c00e2000c1c0c140181320240350001c0034140b012000d540c441c40e820f071103190704642c1036004c039060480c0a046180052200411194618080c0102c1e116040b412103000008000c260740b6001500120f0300b072a40ca481d144000c285268440d50345e28101e51401a051015810103030805451031410343c24035a41000c0c60302d0550b03504d4940b914019070a20000d23802800340464154118074401100800a07030194000841e018085017141e1002d9515201290ba450401c0c100e03400c51407002d00040f1984403660421504588484155001c0614540114460001401090300c0903910740404014520b070080a0400d1070380c0c2c5400c02e02c001c2c0f03444400704041145902c001003100714000001a100c1c0c66640c4100310342c074140e0a4403070041c202410440d68a800607111088405058400041c903881d28500c04150f0680c04058541002e10b0a40191403ca113401468020310000c03442c3e010014207083e43d80682c5c6c2c03102e510351a0075420050108c074031300000c02001c9442d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 279176690 1250 279175440 279175469
    0x1090b01081612060305030c0607030b0604050120030418021210060206060d150c0903050c030c0a0306090507030b070203070605011403120904020408370f080d0b06041e 74
    0x924100a080d20380c88070960070103d90b450030701d0340280010040da40c4083c007035000220b00c00110b00c50110707202c0d015040329503003849580c0800c0100140e40c0320354880d0b940401c51a02c149000c6504a4003003807807180050003038a0605689214010200b05180d08000680c3d50000d400480c0d050444a4190840d005649920720b2a040000c0a5500d80b005403a50348685070a0b0f080300704208814a910040041c9400c00f8800e503000a0f0024161800c9404210ba1501410940b80418200000d40101c11003005200001c01c0d8034646450380104500c40f03082c1c3e19400744680220100b46140c1c207850160000e50300a5694900d1401d1103422201c040c2c2002251094103042821070350f60010784902100320091301c00750b85180007000a0300902c1a5030141c1014080d40c03441d9152100c60703031007612035072000003000b11012510454090140d48010710041c0178100000900d0007103100720014059080828400160352243c150010700d07e90004c1e80b2080440c0c2140c0e0002c44001ca140c200d10008041a00c00400c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 279177940 1250 279176690 279176701
    0xe0118080a09150f080603010e0d050901110c0a060c0501090b0c03040204291c0b0a0e06010602030f160302150f060102010c170402091f030501050105010f180b0a1202040e01090b0108 80
    0x907801c4100380c1e02c01000801401b0030280e42c2c0030341c020002c05400400315000e68100c480060141c0d0014a50103000c113071078030186680c440d0003082001c1c1d0b001000301410621801d140c0141c840e00b115060540c0c2e10340d61900f03524000351040442d140a101039102c2e0648911f8503204000c1035030316015007150603020005030703c40d10001000c14800076140413940e6100d425455040c40d0209640d01e071010b050b074501d101c244000d0f90680c0c0d01c103c0c0b000440106a800e603a03210101603a0740c3c81181c4401200c50130801c11010301c920b40e03901c0c44036a41c1c0b1902c191054800002d25003446000d00b500c440d45400c0aaa00b80a4550307024800e000c0c001c109810044040019100700b12101c0f03400500186c090400c1100040b0541003203035050320803214051568404a4490401600800c003d0240034081000d00c90040c0d4001d000d020481d064801030a45480c4007400d1440380c21442e08039581c1d51052180641c001e80100c41c00380042d1000c0c2000ca40c0000c0250b00d0f25000d40291040039200c6410300141409010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 279179190 1250 279177940 279177947
    0x90c0309030801031e05010501030b0601021912201014160e0d110d03020307050111040b0a031d030c010b0f0402040f1a09040e0a032c01030e0118080a0915 68
    0x141180d4100d01c010800c103142c409114082d407011725001701954a0800080200540ba04010303000d100d080c0e00312803045c00b4241d0400410000800094071004840060545081c820030554002511050342c1d01c40d82c82000c04500e18015685171405c0c106a1101c5141d582c0c04008070340682e00c404604000340318801c0000003d0302003c200e45480380118000c0c1e08007000e1110321310407107011040260403805403462908000b5207075007141d142181c0035400c0c640c407001c00e940f0400988050ba40040901440d044a40005400801c10303e43d45401c80a0118a402c5840c101031000e010641003050010503400684002c0015031301420b1045845140706000501070301000340030380c4041d1030a000f1442201c0c0401458482540640e02042c0d91041c10200360060340003002c62a4a01c43d442612a0682401903c0c400380c403100301800d001d202c0c2c0505002c0608190710a400903080c1000d41c4000084c541052060030440005408064994000c001280b0360680e0b44200204d004240d40080091411000030008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 279180440 1250 279179190 279179207
    0xf120206010b0a030e010b0d08030901051e0a0b01031103010902070614150607051f09120311190c06052503110403020f120a03021b01180b0f07050610090c030903 71
    0x1010141d490500f141448004d52090320384500c000c0030034006923010f03c0c0900c1c0c2079004483c65031750f5508100c0401e441250b07400b103004840c0344007142c3d40c5040e0740c1c41054130700230042101d0860406403102c01010a108507940214040c240c15034026940c3c50b000c2c00e0240030360b02201d0038100c010030958104404c0c1c82d0310326880408040100d0300700380d641d480307130904510f80b91115821001100e494051024051b4080d071220a48912407001e1201012101ca0150119802c4450075640714004100022075601440300658a00f07030641811014940e45840b00011150110740c4d034030041c1608000c1c0e10003041900100348034580300d440c052210340b01c007001d41216806a0b100003809121024900ca01e00d545480f03c4561038000d034003c071102ca10017400c00a54a50540c2400d5180c107000c1d000090043d4840e40072000024060345000302d80318503218503650709900441104a071003805010982c001003050118a000d02080c0058101031400d0030612421911401728100c20300d40340c48103031030010b90412a0f1307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 279181690 1250 279180440 279180457
    0x305091c08070b0c0d020f04060912030e15040b0705030a0801120f030509063a2903120301080f1c081512010207050312090a02030312100e040f120206010b 68
    0x943d0864644024100c0f00c0c0c0101e03c411040340c1d001003109031030074003020058030454115588007030650b030f55058011034a08a1060150000300490607010460a00007200450024011860b5103050380e140c030384c252180c22505c02150190130000705041c40c503501119450152060a010441c0320070140e852841c0c40540340401414004042641b261559071002925030101c500320303103807440c0e4901e01c0109491200940d00700c5414820b0f0401100140f00038410521008003016045401c45402d00d00c1042814807204941d90600c81ea050885030040c4060156000300200c034020303d14201903505241c24981280303007689440740c51411107100c2691000c030013500813820704402c00400d03d6104c082400302005a00b00b0000d0341c0000b40785e50401400100600008200c55800d410a45404d801d03182c4a402c0319034007940c194014014051500e40040900e60020f0744014005901a5a4100c84d20300c45000c4505450192000c403a0009100075902c06145102d5144060a515814441c1481c4c3c0740c001c2c3d000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 279182940 1250 279181690 279181703
    0x71a130f0201021f0c020601080c0a0308130b040b1b010c09060815041e050105061e0a030b03010c050711101b0228080d02031e030606070204090305091c0807 69
    0x20044250b900900c00740381821001403c00300740004242000c4060420070110350018030559000150414010607500c5d4400302c01000c0300b64a0b4599140d4121507000815160f001e50103d0400040b0718060000410061008a50141c3c440742000140e07240d00302118455811641020180c03254240c5c0040f040080d103841c1d080c141a0385d180c0000c02e0450604d80d00c9002c0c0c00034503040500e040f544580f07545800c1c00480d00300c1841160780b14000c2c07204602412110071400580d10070b02900487c0c28001502409202d80b80c0000d040c1b9090001030300303440802d0301d40304c08280009030081c01e100025400c580100b20998400c101c8a00c0c04500800c0684003110743c0490030003e2404c42d08540e1111030401c5450f99198a03d81291407121410421601303612420f40d0509c141105201c4941c00881520b801a60141d40c3c6401601811031409103a4001000f03503601107020001003005a560348248500c441c001d41d2040c2e00e91a01c41c05114107011110b13088281c810003032030346100040544084450081d0b0068 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 279184190 1250 279182940 279182963
    0x62d0e060d021c15020c0c0102070e0a021606020a120b060c0a03030b13140105010807020a0305040b0906040b0d05010906080c0f0d0201020703050d080405070b0c030d0c050904020f071a13 82
    0xf862490350b80c0d00480c00030310801000c43d1403603441429401810b040342d10102540c6007058040016030362410988200080188000e0008240c3e4445034064504200314005481800e0059a1558100c2c2d10000011010a0515901c282d1500540c4150018080f058902c40d29001001d000740d80d941c58000402010103486085824080d102c10b010041d84104c0428244017001c140d20343c4020100f02401403c0c0043d04090004103100c0c40040c2d683c02c4542c050f1500ba103094141704074144070394004607006400c04401c000002e403100c5280001d05102c07003854400242941000708a405503035031684114103640c400540500c09944403071540c034008600b15807403404501d031480140d080c280503520281040c000c1e840392038916604540420310403446070040c0c408142c1c07615601216409610f00b921402d07070051080c111589282d5008000c5660b860928908143c02c0340c00003416a480034040444907440031989034108117880a814400c0000d4032004406858803170025166040a040c0107802c44030b024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 279185440 1250 279184190 279184219
    0x308060105160f08040f0801020c0d0302090a090510030c060201050916080322030c06080708060d11010507020406030501050a091704050f1c02040c03050708101a0a0201062d0e060d02 80
    0x1c4e0202c50061050440d140c044603540c07078a0380e0003504559000c2080d402503c4155414038824800c030340038114024a0a10a5410505000001c1c00001c00801880520ba840803003c01c0e0381089181c0200515400271500e840c1072741013507081000c06040d00e503105040110a11170023002100b034074a080842507616894244002801c01c0e8180541d101407c4401022030200b142035000f50441d11409040e00c502d10540c891400780045400076441c05454480c000c0030840395588203e00030401180020301c08500307182caa441c1d0f603086404c107451400c5103030382e1030a050303081010552540328a000c6a610f1070742003519080205850ba90086052032103240605101d003003090307080c0701e070f45d110ba50003500821000c1156031000d001000280c1e0048081080140000c01120045010f40182d0722000c0103a034440103042c0124900ba00504804815035498034000b0401c00440c0d452980741074a010450090210a0440070342000d05540007400100c010408116840e19001c6140110b694141e40d00c41c2d034400b44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 279186690 1250 279185440 279185453
    0x30109150b0f070506011e0b09030c03070e15010201021305040903170106080601030e06191512080702100206090a030c0212030d060e0a0b0d06270f0308060105160f 72
    0x11a003020800520101d0382d80d80140c1642e02800c1604e00c51400c48103d82d803542a2000c103043c526500f030410515149050101c1640d0350090302c4110009070440e41c0750440100000d041a895801c81c9888080707180400850381c0c0e400c44e16042403502070000318544502c0c44106800b0200c1402002d002e5503c800d205400c043c464210000f600c0790981101800d940c403044002c026000079118503001904018080f540400b000c901f2a002c1c10582121128000401e007401c000f6200000c5090380e840d16811001aa215142e02881c0c80240306d0a1032555036409031040103404008102010110340c4542c08014401d000001d91202054150400e201c211540d8030000d401051026407190702c40c000401c64000d41e680c160008015183c3d245140c0060b55101d03c207400c00c44104403100da0744092648109400700f442036000215400030444d030310800368400c44240480341d024030422603410319401807400034103074409044c0307030044070902e03015207000315451942200c03103680c081c0500040c0340c40b841c40081004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 279187940 1250 279186690 279186731
    0x1202030f1b0420030a050408130305070312020c0306011a0d1d0705060a0e19120f1202010c05030106030c1808010905100924020c0a0b040224030109 65
    0x80301140c500510010042001038546105640901e0500407101d10a0600040c01005549415021400d5075110015180507000c080d005036042c00d01000582c00400c030f51180d0744040c0d4040c0d00244620741c030303615151041d4101e501040e4219000001d801ea485d50700451010f0445034a02030440500f6207a1100c50100d05c52081c54542262500402032030003903502011030405c1c50b460007034442c0941d82c1d400784680340c845c81000000068905003469090318080c11074801001c060902e4002680d100e141289810004243c103a85801201c0c14072810480b800300b4400004c0d040d4402440700800d004006400303800103000b00b07414503441d0f02c40190994401e444404034a02d010040c0b03601e00f562050001d00038803001100744c0c0e4600441503941340105403809950040d5510802000c2c20410003100500d410304202442c5018a4003000700a0405908005030b4101d2030080b0280c030003d007090b104200440c0804140044440c80c48005203200000c44000d907411143c50032400715448071b0383d0100c90b40440303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 279189190 1250 279187940 279187963
    0xa050c0c0a12020f030601060f0c0f0b040b06120109050601210210091e080a060e03132301020d0807030b041805210f090d0c120b070306060e0a120203 66
    0x8040c00c001a0508810703541000b998000e0f114201900455028103844010034000c400218900361408040346100301c41101c215030144140d08268082d03950781000b40d4009541c11340310032030341c642442a05e00c0c00180003610054030718001c019a1550359250703510f550051007507014030b0700e4080904801031b40d00a00010f80c0d13503000301080d4136440c080f90003400c1600030b8054a400c00c41c0c800031205101008210320425a02c0e8031004040ca0040c0d42c0d122409000c07120020103450000788501c82e445c10b50940704801904403800d0300b031a4484004000362a44c000c4005084c11540000c41c11070b00d564210303c00c5600103200703190200c0c00d00c07a05400f080103442401d621015403109518190f06000c0c000c1029020410b01d0224901559229401070080740a00d06a501c11030400300040881e51424249a0b14054420f036074960f8001d42c3d0b01c890440e082406602034800350300c28410400724a50510a480240140382030032400303060001e000c2028802d403400303107032642403040c0b440005541d0104045070092 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 279190440 1250 279189190 279189199
    0x601050f0d0501030b09070503060f070504080615040c080609070c1106120f06040902030304090f1401140406050301020313061e241409271002041e05060a050c0c 71
    0x111801480307000109800d100035600d080442d03010404541001c036030030084500040091006480d00c43c40101580409040c02c400d028040000144113101806501e1041580311031015020070014184800c1d43d03400f503684800c021088d020001aa510202040d0b082207040c9016a0911038524080c10600001400c4990065000c140d01560f9441000d40c1445259805600e5100303454500034003080c0c5d050540000d50540091100b030007103802c0e6510038464415101808600d188004511400b201400c2c0c00030800c1246400b01d44c1c0c06814140103c1d0002c03e020f034001c62441c07904514507840c56000f010f0007040c0d151a020741c5008481c1d20354800001000920b01000820041e070108803141600082041d00b4800c05000000e07001035111103d038214001030000e0701c65030b03603d548460a6a03c403421080107036004c0b200144e4a410200a420383c400b1070031400680d105d060208004012540118498415403811030605c01e40d1605d00c00d5031000340e00c40c24442e0711095280d42060070462403111a6801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 279191690 1250 279190440 279190447
    0x60e0105090d120c05040b0a03060f030305030f102315040618170616021c0807020f060402030c2709030406110c01080403200f010e070807031a0601050f 67
    0x41e6180800c0e019800c0d009601c4864412032110a00f41c103540304081030f0030106005000412002c68800024070890130f5501d00014215100c1c06041100710f01398005400003600401042451038070302640035040142c000048528900d010b5001d0703912040c2c4101560a00c00c807054541468440030b07502141320041c2a100c3c0d0711180c6a400040003488024000c3c08001e007546800103441400024003c2aa4444c1c00584060356507a8174610f0f40c03445007180842144588903140f101e40003010b00c0c410103152a55111400c0e406e051000a25100b0303004610340c100d81000f814400140d800040ba042c1d902d0041e200414003c0412200b08040690301a030380307224210f103504010420002000800a0ba04c0d55110322010a80c42c8844039a284c03e503000d0380e4041030034140030402280c096500302c03131a10081c0740284061400d0f0030059040c040003207032080c4103079151603008980602c00d10121000e88462802442a685142c40701000110401005514804102c01062060b4440e6080b2511084003890352580d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 279192940 1250 279191690 279191701
    0x91b0f0d0b150f040e22060e010e070b09040c090f0303020a150b0f1207050d03021005070e01050a140d090b190e10051806072303041a04060e0105 64
    0x2900300341030080d100b40c203200c501000c1c4000c6036058030a41100c850110b0f04060511807126100c0101030810070b404c141442c01c400b008549021400c2d1460311510001c81c5814a5010043c02d4401c16480344040b6084141d062005103213034001c2d6402101c044501103145001403205031740000c580c5d08042000c045180e40070040c5600021014000d91203006452036a070480310311181140c41c80300c1c00c079038484100e94103c10315140112283e42c410144000b40d401095603207000660311401901e0850140c0c02c6502c5020880f1060302c203440d4051814204a07104c6400e83d40001c00a104038400070041c010501841c44503c500001554180010410b080041c41424103000c0351861049a0050500c80407004811840c401800303003203500c0e03000c0703070040c24050081482c0d607016180c01020704840d000315110f8159900e104011250107442c06803076046038150b8821207030036a444011003200f242c10080040c8800201060404680101c3d044000c01c07141c1c4891034100040c04c0700d8440c002c89507082006225 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 279194190 1250 279192940 279192967
    0xb04060302040c0c031722030909230a060317030411030d050705010b0111030d0e03090a0e040209010e090d0c050309031005010501030e07080c190b03010801020a110c091b0f 76
    0x10341c0705002e51100084650400c2c0300c00c06c3d00e602142c5c04001c90070542c06503e861103558201819492090800c17600c41a01c6075003500481b00c1420b5085031004040305045242a400305d81e2036000074400d0800d10607d8123548030103621000d0407141100d0000c002000030207018206500e5150228020240c80001c1c1403403e00808903000a1b806a030755503c3c1c620820495801036088201200c080382c013450410701c0f0780030b000c4014040c030100c200860008110740c00c003c0d6108a02003001c1d00180310080103d040600602101c01c80c140c000c0084030034014144030070f00e44000741c00c0d05450580d24285040c906a41380842c2103001e40c000c07041c4c0512882d284c44014040700d4000c0350580b0400e80c0c0401c40d4002448603955148600e1040f0348480c6c0100d03208c120181041204620700700c0c1c10009113414140d0b5603407050700303640c0240c0c00009503075400300307900d05441e50010a8031100b09940b0300401015001c00c001641820700a0304100c031514000301c051618a003034600340e0351410116855191034005641c80310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 279195440 1250 279194190 279194207
    0x90307030f110a06110d05130810060602010e4606050403230f0d15080d030f02030606030f0a0f060303020c031509060a0b0103020906070f02040501150e040b04060302040c 75
    0x140300f401d01c62004100759201c1c14031041a000c00600038030000a28501c00e5031140d0110401e00c1680041c240d0110b0986002c000b000480c0450340c03000110180340c00340c0242103400c84024030304943c2151000e00b0500c0c00e0381c80f501c410061114902000e0625021521414028011059990001e012503d005001d003070751003103203c0c1d80213455942050722038664640c4105003445104008220030b000300655248641c0281441030030580c00028040c4102e401900c1007062684403403203d5000891408ac2598140030304d400a242d441000e5055081c0040007668500008155070031031840c85000540704001500055040111038808020391522410700940b960354400707201c2d00034820411071215114030080002d100c1d00d2820b000e00466284d10000d0700103080da20f61101e04141d001c3c488681d00380d40f0f000040c119107118140900c2d41c03407007510501003036800c142d0043d81c1d0700d0043d024122400d40c2084840360940002c803800144072407903400150080c106074202039086880c01c14103450998210308007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 279196690 1250 279195440 279195473
    0x11031e040509070c0c0b3f04050708010b030714040e2104090e030a0c02010c03090302150d1b080c0904061d0420031203090a1a0709050d0c0308090307030f 68
    0x31208040d1160034810040c480d800191425440c510700340742d5052510b401c40f200e001c1f941e001018807040c1c8181d80e0315180e41e094405a4664004040401c1240402d20030800440e0041c1e02800d009440c1827a105402c1103040c2150340034075203c90028031074410902c92032580f08845040251005d40c0200c031003103d0b8100c1e008114000b40703064010f052904001007581c104000396036420004641c030b80d00468101c2c8070500c049082c061082e50110040e0f50b07000040c03103010040d1500d9503c80d124005600f040e503105044003450503111803c020300300c0b640290b0042c1c0c0007204061050391444240d001c200140560351143c0a80340c0d0310480c0701105040403075200c0c080c50054101c808042c1101004103820520045500e0b4507a00c40740000d80401c2000f4003440d8404c40c2401611111045501c03120342c02c40b0b610094000c010001e8041003101c41e00a41540040d110039104094045210340c2d078444110b11078000035003081000b05107400c56503010840407010f15448448207840c00c0107403428804107401d00d840e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 279197940 1250 279196690 279196703
    0x30e16090209010f090509060607050328200a060c020a0f29090601150302070209070f181d061f08060103141e07020c2e11031e040509070c 61
    0x4a549184185c1441d019100014a030b032215848200820280b1390144508171034501042c400d049000d0400030181907000c4905a5149003000302000041c1401c444840500d140c9010180e02e41407c4000100700300d107680d0000000a916a050000768030746080c01200820741c100102d001c40c100107030744d03012807008100400220480c148810014400f10011100d03680e503030788851700401a100e504040c1d0060111130b41001464101a0b40106400d2103088800c3c50108440c0d001814401d079100e241607401c040c0080d4101c00792410401c1e54140030b10110b440c1d202000c000e001144481d90703040c1e091100201462286c090f10ba5276648064501c0e00101c5405010a00d04143c10400001843c0720301d1041d040100801c1d0420004083e08280f24009815901103114000c03070911592281e900d00d0b40c52840c042102010f0503ca44035103d518440219001c04002000300c90302090700c4000b040da5071141d81468848107105800c0c03110b5030140070329032100d64070942190902c075041d900007401070f00440c0a0407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 279199190 1250 279197940 279197957
    0x70b042601060308070b06060702181e06030a06090c08070806010f080a0305030402060a030b040f090203060a0605091627090b010f230d2c150601030e1609020901 71
    0x1100a42261030b035100280c000c030410400c0100040c000031005038846030003803000e81003002e80d401051075501c0e041c10f01d0f50348138034150500810502c140420554800803080460b0309103000c2001c0b82d110b840050008140e942c0398030a040401c900201c4000103030851608540c02e06a864001c20fa540c1400c1c40b1381e903135101554101081805000c00c201e215150140c48a40c655192075081c030403107a1000d00d28508044d92a0300c00765040d5214051040d0628921102055078040c030700400d800d1000c06401242000d15011003005607032203062401d6400081c441c6000c032a40010745054482046515241d1072b110024000e14040500d00140c0c0c0040c1c034607100080000045140c0107641d42002482640007181d07401e45290082950700c1845030200c9843d8000506000c034070803400c0140c0d400768034042d00b135808082131200c0c038100301820108035040076401048100c804212940d928000501000d04042c3c48907510f0070b003240d042041c50301e0041002035200d0142c0c1e40c1c20112009400121100f0b00091440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 279200440 1250 279199190 279199259
    0x522092c0a05210d06080708070f080606010f05070c060839030a110706050a0b06030f040201050a0c0b090a020108070f2106050a0f14040e0a0b0702070b04 68
    0x61007481c0c1d5980321004100740f80841050011540701c0100c40e5450803802c011042500503940207040040244100824200c0e050070f4026040460942018203880840b4404011040780040d1040c1c2120081c288a0048400d92000310765510070b03020046d040118400c030000c0c89582c00744c2039900c1189051402c0c201c1d5502100c214048116403403d0714500c8145c80c044c0140b10b0403040007550000b2002000080d0a0304912003903d264120181c16111107070fa44d001c00001c090f81c1d016040d0805000c40c1c2c1c0b80d00d186080d0008612480c00504041d0401c0400b02d001c0c002c40380100d142c00a500e412031091070f801c0c50880174940d81c07000d1601049000844040104044601944118001590035101c44036a010003500e900c1c045000e16a41c00d540d41c0c0c0384c000005094840c2c0d40014040c20021305144556414451007031008900d40c0b104bd4002c901d04060042c420303d000c21114600c90340880034036401d4581fa42c080b8905401030300261492540050001b070f000400b01c1d442124483c41200c1c201010050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 279201690 1250 279200440 279200443
    0xc031b05031215130504020f040b01020f0708010203160203160318170f1e07062f100b0102070302060702130b1e0906120a0305070c0f03030905040b03010c0522092c 72
    0x140c3d1b00035041810702c3d240443c6032038990806002001c0c11300c1212014040e82d4500e0f840d0070340d0380d031004005950005c02d200711654405085190b0309014001945803a2140f039183ea409250680041c0070460903107036404c5000c0052501c0e50080c804121030b4440400010140c540710100490401250303c6080035441880c0f0007403801d407414030122000f41c400d45141c20410740d9440c040490350601c039021002d980003c1085550220441c084940003081902c901c80c030703a54221501405030f80e0556206d1076042005075144400c41d10110b03030544680c60002c030407464010191051042c0e00d50b0001c001c0020028070440031050640e020011200c19580d40c03140c40a10900030b003480740654540c0c000014900c00320f4014001040301d1441001101c4a141d501c418500d130b4014035401c128001080030b2020802c43c5054090070303100f100210f0080080034891540501144a01808030340351a4524400c407860301d0030300d5161002000700c1402480700c03030036060501c1c1c41200700e0f501c11401d51000710074000c000c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 279202940 1250 279201690 279201701
    0xb07120b030601052202030906180f0c15090406030b0a140c040308030c04030f0b070305011d070e030712080c1917030a0902180114010c031b0503121513 67
    0x30240103840264204024001c417002d604210404c103004016401c41d4480042c80154410000280606031900384601c8010a4403c611526059a401190880c511880202ea0032140e04000c590801070740705640300820307080c02103160707043d84545401800400d07c0725401041d48078010741c040400488481403801c01c0380200507141e104541c041440144001401c030401150004c030f0ba580114181aa80e03a0f8400c0040d031140710859a05180300f060040e541d07010b020b82409014500d00070707030090b0034042045c4850b44008041c1d00030400001c2042440791414030042c009442c004078003045003081c034200481d00f40e201110b072a84c18403031030b9690b4001225140c41c512625030b011800118292142c1000411600007501c01e0014580d0743c82908016075513420195407005500c048402d05600d4550758003604100307600c041c3d05216082c024980041d0380302902d90044941d41004201c000c180f41001845c5001d141500048010800144101152100b0550252400449011107903641e10100c0313109851 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 279204190 1250 279202940 279202961
    0x15010e010501050c1005060a0315020414060a0e010e1f270e0106030f1b02100e070b04030b04080903030f120603010207031209050a05060a06050108100e0106081506070b0712 76
    0x80007005d001c04d80c0652a04000d80002005000ea102151a51039140c174800f405040269000e0380043c003004141042d02d051841c03143c0448010742401c03e00e10014044520f1050b030103042007410071603611241da440100c080220155545100144070861024041c0c03541c001499005004a039200d4060380401d82c4a1010788842c1e031003d0000d6403801130309402400c0ea0340080e0404946494641c031801e0840808540201c4007940100070048115400d40c04075410611482510b40001d9402d007e8034001c0350880b01180d51007094996a036955090050341e83c040c113030080b60315020020304900402e504c1c0000d84111056000c01d6040d603225101094200d10504030010081120507010040382e0301258414407045018a0660720b40f40c4c9259540c0e4207080c02200d0001311031350b8510f4140240c0d40d01580550340400c50000c000384150401c802c00b4100da005106910800c078244001440c00c00407501b501d400004040c105c00d85520052803d60120201250020005626240803d11841c1140030314440b19 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 279205440 1250 279204190 279204193
    0x10c180f0e0703020702100512060f061b0109050f07050108100608060d0203031c020c120301030f020d05070305030a0c1203021e0904090206030a0903022104060c02010c0515010e010501050c 83
    0x2145070007281e500805004240000b4150309020910240c0c030344a82004a40c00d0581e0380b03075a100312140084040c0c00000d405c543c0101c800d80c2d004034013919a901112401b007030b80300c0e48800d62802d0700d4506003d81182080100280507148600d000c6810014280c015100700340c9443c50140d030b0307441c11f611196189120705000200b0078404a030490810b10038a100d0940081d003075a1801c20f0440b00046400d140280382407109600086082c00303980e0030700c200e65826282c02e40345459940341d030321000c00740c1d03000010180c0708298150402082010400c0840300a60340b000170740703858524004000d0207194400700140c0b45111210003504000e4400c0c401c03141c41d4120403c0b03414640700340741505100d43c0c1010030400d822503070303410303044015940382005188100e01d44007012a030403d05240090074100d041e1b0f6180703d0350030441191400c0244403416101a00c6852801c0b9985034482e0004840d04644044060058081e5000900b480b002c4c581d44281a98614540314029036a1038004448601c9a0b00031003069 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 279206690 1250 279205440 279205469
    0x15050a0f080406060320030d020a050330040f020109090b090f09030903011107020315100b030703090209040812010e06030d1107080106081c03050f0a0507140408010c18 74
    0x38a80600c02658006005060000701291281e1303603400b281442ca541c130039003080d0a00074012246030411120403002c04600c01b502c1c0c51041640e60b6552402214081030034000c50320b004044071099800700b81c400c3e40c00b88000702c80c1420f05003401000b07c2c0d07440c00300340d002460410300414a55001e01a112150390007400303603021913884112200907203001802001ca035000030080314200d0794090107065643c01d07460007502ea4800351031040500d07000301c481003010b120801000300040341d01135010300011120300106444d0b699076281c904030010504603500941c0444081c1c280024040c500d80907141c204a840a407100e02c0c2d8881d11362140b8404221a02580340e0710403802a29030034030400032100c50360000c000b160103c9884641060a407041c980000c2029030140d59165880e00720120b03081504550360504000d182070a4a016042c03100040c1007580650b1180081101b903485403100c82802c0c01c20081164481d0f45a1000c80c1c0030b40a02d10460000442501c0321031507104d0fa098020007110340240c4071070710 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 279207940 1250 279206690 279206717
    0x5031f0207210923060405060a02070b070f1b18150503030403051c0f0f030509031c0c09080c09070804020a08030406020105010e09030c0601030602180a030b0115050a 73
    0x6540031400490324418980ca0510395090456100100880c0544401003004d04104c0c0640045036103000c9100a883d041c8444031942d220101142c0c00d07143d007503518994541404000380d213400140d03407000d81c881c03000150b294280044003070500000340c03007400c2c10392350203180c0e2003401514122030084004039584040900c40c042460750211070301100620050200c1940c446c00241035400c180d1060711726170000071000b0901e40e60308d000e020134403c050030711307051286506034005c0c4044810380ba120b0a2584c0c0c0c0e008108008000c00964003900402010701c40c555000240020252407074030300319408140d68100200d1414804920f600c01140080c220107110f603a201c2c4104c80600b400303001a40c004a50348008034142e0b00500007000038050640002c201e81d450080b0790102120000c2100c8a07507042802940201c0e100031640c0d5045a0f0010703000340c0c8400c0100c420080c0c1d01c4451100c01e521519103d400400c102c03175840c1c10750403101c80d1b000d10100340040d8081900c1510501c202c10000814039940d049 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 279209190 1250 279207940 279208003
    0x6050702150d0b09090c0a1d070f0e060703090503010e030a0518010c140c0f010903150c0e060d050a050a060807060f1e020114070216060509060c010c05070c0503 71
    0x550b12207030010074400b10003008100300f800140c5102c20150043d500322505030400190320130081c04805103c3e6080d1240c485c041202c81c00c007a140104210103c20083c1d0428450340e002c00010f003006050a40c0c0f0f00103840c000d0640c01c070b28842e00b40070b0f500308a0280c145ea403020082c0c1c1c4030500a82c68075071604450110041c81094080c0e03c042c14040700c4c5120310041005168190483c90f244401803404002e00b00820404100c012a00c50410210301014400105108100d07000c1c024041008120342402550645660a1007070301140c00c81c10102d11f02002e1896500242d001c2c149844c401c01c29616150f0b10035041c0c40190141701211340c00709004000c0284078000422802e200b5291100d2030f00d1040c4111450083c0140707402c1d0041c0e4542c003440302c10640c5400140c1d04026140000c0c03a0300c017610a4408842c8000c0e00c1610140980417801032031039100e8504a9009901d0407000b0060b01d0b51000c8040c00c0e64000490075611448800c1d408241414001050011340700e0209425002e20441041d98 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 279210440 1250 279209190 279209197
    0x120c0f080c040b18040f0605060307031a1017010906060b1306050d1104140102060718090b030304031b212607140606013c14030c030a060605070215 65
    0x481e00640d01c0f520f00c0d640c2d40b0701c80801d1340c0518414048000002c4c000d040000640718094199886a00001c0f01000051102c1c2101500e070614065619056507510500c001c45140f2580009182069840700030807442043d030042c0940c5108100400c071150b211060415907000b403840c4078984c90f02012080c010503010700c011f0160034900c000b01107181c030710508041000d03400c039a0107a140614030404c0c000240da01032242e107503c42ca003803811103141210b86420f00071040c00351081c4642c1ca179440400201c540c40034002c54000e160000c01c1c0d401c04070280105100001d0341d5208110400205482c030030703103e4400849a07181560003010b00340483e003000034051464195642441a6400700b007015030006440100d0064460348240d01800d03451400c03200140901c0d841c1c0618040345605c4c0b4000b4440070385048220304802c045440f40d44400014842d040e504c00c0545441c581d441c000200400052449003c015031281c004d140003801450341c1c66109445c03034003404100951101010b081d1300c00144051014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 279211690 1250 279210440 279210461
    0x304060905190c030b0903030f010312020c030a0b060102121201030305090a0810060305060705070f201309110603040b070c0213020a020312090c0a090c090906120c0f080c04 76
    0x90340c81e031a0301c2400c42c14074039200b06801c9030003003010316080040c05040e24090b40d100008001545c6581b400c2c180c0f180c110307401400003c0c403140e90006821262442041960940000034084071a0060340c0c0c100701580450460b8628010b10990300400003002c05241a5621a0192500d0b0303145642517a0b006e440582105402c07681003500944000740b00c010800c40d0136041309244000140e55811414070360304200d002460301d01440400c00603031001801c040b040d2210980c000c445000c041e542605071341000c8410380c62503030740a2020305104501084c1340c1d1182c280e50744144200f90807046271a0a01c0424082103a024144e82001d800042250303009800c13052980b4802003960305910411251241280c2100d40b1120044c1d102040000845140c030800700e0304400804001c094036546140043d2203240c1070302441d51880e0300c0c1d81c65040418000d21001c0c001d1310364140103000898882d490807011140714801a01c244542030b4002801284401203001650444406001540c0d141000d10010382002c604 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 279212940 1250 279211690 279211693
    0x102120915040303030509070b03070e0f0604030c17100b0609100c0c080d1b0f0f0c0e130618120e0105040306020c0604051b010801090506030118080a0306090605060304060905 77
    0x5810a580d40da01c0100041c610a8800007250f0525081d81460403642d41c0107000660410400d100c0010b07001054001c0288d000c0300d002061020282c04201c00d406a03620040c940349842c40045140c0c481801d40300c000d0740000b42111206501d00c503c0006840e090990290021400c2040c8035840c10031f85100b174800f62480c201510003990a584400883c840f551041c0c0300d6811507442f00c0351213940a040c2c02c0c5500094402520054441e8650040b40a03015500614083d02d10000383d040151101c0341100038000040070201915042d0300501c500c1c00d460740100c420500d8036620343d4046081d0201c0041c070700d401c5009803101e03060000e01965544c00203a11207061207814000000000e40302e000402850080d88090300b0542000d16150340380c1248684a5245a1141e07820104140d074445011411910740690204140d220348012900424681c2d500c0d84691116103262020b22103694000d016031b111030381c0c00300990f0b9a200716060495017540211940a503081010030300cc0349090f04107400b540d00800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 279214190 1250 279212940 279212959
    0x30c0a0309051b010311040e01090e070305010609061404090507030b1306020c070501091d2212090302091b0d050406021b0c090f090c0d03020715081f030201021209 72
    0x8442e280780020840024a40070321400340a20342e56450700039480841c55402220b820503040c100e0200204005000c0c08080035515042c60b1030144040200170001d540000082114944900d44000500a240103e910070b604008182441e800e20b4030542c180543c00c1000760010b68296a203255015401400750040001074051078004200640700a00e0516040b030000c128a502d040c0000d0040059940b10301c1e80500b15148030b505081e11240000e920085008d0094402000d803100102c103050102c001070046000000b4a0344d5003904200c16000b600d008480c001819a103180c2d0f07050260b001c2c83c0380c4e100c41002c10322001d40c408a1940165801501c60700c030150411500d040303641c200616010030401c2e5075000240e01c04c030340d080185015030002011143c45505203040701c3e046944041c508605401948100034080c1894824815203000d04540120100402910704009003030401c103881c24001c91581007040107e40140c50048800c495041c1c000c2c021021490300b95070b07032540103103074050381140200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 279215440 1250 279214190 279214193
    0x140903031803010b120102041703070f0f020307030609060c090b0f042303030a0804030e030118030e0102100507050c0c0f030a020603100f0303030f05070207060e060c0312130302190206030c0a0309 86
    0x2a0940c0682e17403840c000140c8451425260380c06000601d1120003540d0010030081d4041600d0040038056550491403128413190584042440e2100700c2e031001d001d040c03808031120100071444d00006440ca5550307031501101612000c8075909445032030f80610704071200300800c100100c484000c00008141040f1221400303025200440c1c2980e12480540e40050030403400c00c400c154114001e090720300403e500801c400c68645080d410360b1a80d032603016061020b00b441410701c07680b082201d14000c14100c40c061055003440c1001a00d9504803074015411401071605404481c1080c1c502c5440b191350040c01052010b1198017442556400504100641801d0110214001c1078104088000b107101c0c0c0d0300064020100d0180c002200c9001d414402150080101000195401160401c00c0d48084801319941c3c0c584010040c41d521170300c64801c2d49c0c0ca807007508110f1080ca001c40c12080060207502038a141d0407170390394600c4a890454500940c812800e00209031354000d244040c1420f41000d003000200752105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 279216690 1250 279215440 279215449
    0x15070207150c120806030615060a120902040e010b030c090903031b0409050f010f0b07110405130b0103210908030a03020d0b0d0b1504090201050f0a090b19140903031803010b 76
    0x1402d070f004200007009010442c1420440c0326846100c10840c06071020380200028100d01c1244503080400c450081603501180c0c695112511483c0c0c001c004002d4038440c0f8100b2130207884164076091103400340354030080580c24609103a910031800030000e9851139581d50160880140500485002c4002c01c1c030010501400a00c80c4c43d020700c41080609000d50b01d0042000618411608025244042404800c00040180f801450412400c40c0c000c14203a40b0721402040c00444110044c0041055000004c00d0101d011143d01c0d41602c00c0480d00b20840032940305881c0c07150321703106000c3e46910070400508128880d90251419003011400804c1c2ea0540b0000034605844000b02603d400903440c3c1848808180c0f01409000154207503414042c0100c2500082d10754055500d4080c0c0d501300018582001c0c0b07105003c4400a00b02c4820410386410000034a2241c000710038040e100844d68055980b43c03402403001c1a10464070b8010001d620b0034418620310700b800004040026015903d9002c6400a65075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 279217940 1250 279216690 279216713
    0x60301030503090307090207020d0609060b0d0c050405060402160b06130c271802130e13032a030f1103031e01050906011407110d0b0915070207150c 65
    0x7420085450307007501010141850001d5000c004a03030b00c1000008010b880300340700241c00f1500544000f4100005090480c00780501000c0e482c0c0c003500d4440c80c45c040010f500c0c90401070310b034207403001c011036514401440100c0c840e45c00b221120074204020440002c00000c0ca003603000c1c0e03010b0030151400c02800e50400981d1504444040820030700103220070988903a151a0310740c0d003003080012a280b403408039a100d0211001c414040481e400241525881840380340080080403c81202c1d0040c0c03801a56000100c00c0f02001240010740e16030300c0c1d541417101c1c03803501e156142241c40c1d0348454500503034003550f9950299400301d0a00890703000050281d407090015610480c010b1421514004c541c49030400da01c00c1c142c006a04c9480580148000c69038400c03030315101450302e05101c0d9035030352950501d405506040e02817198404c0341c0092200400585c0c0c0302141c01850042e0466810741c910441003c40c808007122940e0041e40400c004100d803401c24020180520028108040440c4031a100c400d030b00107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 279219190 1250 279217940 279217943
    0x201803070f031202060c16020d08030703020a090801110301090b040e06040516090203131e0f0606090f050412030b010e2806051804111b0a0c06021617030906030103 72
    0x8901407020014880c0c01c8414406115040c800750030349240c41004400c0351300a10154410f0514000a08000c42d180c2426011005810204060303d9151003000180690701000301400081c1d0b80d030500240840c0d050044400140d03001d80720790300390381c2401c00200042c0814414550300640b28660001c100310300f48942d03030095025034050803043d01c10100088501038990300c03490f09648104108140074000c0082820155400888281d070740d82c080c46207120b0b09445060142102e115000c42c202004080d0707000504039600a9400d000c0482c08c42801000c0320710031503000d4007441c102036400d014184a03911044e0074100505000395102d4034072000c0742c0c0b1150003c1c0305003c04107000a0401c00d044182d03044000600300c0c0d2500c0c13498a001c1240c14442c41c1800d03290349014544602040c1031000e2700c0d40598603d0844880d0a092201001440c0f50355206800010b507180031f5420300210b0f042e480403800c05c0a0031412815921858a070103c1d085440c0581c0020000a0100b400380d070201e41c1d00c07100214001c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 279220440 1250 279219190 279219209
    0xa090e0a060515150c01150b0d1803020307022407230f0307060213120f0c23090c0c0f07091401120b090a020a09020a0306050420180307 60
    0x2a40146055412510003600820110244012600c00395440071900c04c40361403c58100c640320812000b5490240540c9030410410301c8a040000c62000c100502400f00c2013018007090014003426001e4003100d8111000140c01a0000c004038005400e0002c9400c2007080082e0440201d11540c0120b2051038000c500c0c1100c4041149030607021543c01d80d440011401d2528010309842c2c2c3c884106c10b075480c881c09100500254010905840808164400c4002055082d0048407006541d14ac0042e100100344c03021224450340020100b0036040c0c2d1120044180150900c5042c04102c0000f080b10000009010f84145201044181560030b0140800c1c03544282d4040100a060f0800c007014003951000b0003c0040e0000c000c004020850540441c04420b07600700b114000c0342c0e00d50404d01b9040005009002c1e4000c1c09000b00010101d03e00d41c003c105610950341c1c100081910b91003040300791364002510700401500c440c1030190301c8907600c0050200e0328040440003800c4a664010a04000c466803111012 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 279221690 1250 279220440 279220453
    0x72c0604230a0608012d060e12010605010822020312070c2102010509010225080d08010312140d0e1f150303141b06090c0d030507060b0a090e 62
    0x1c5400a6544428500c011100182d03002d0900700010000101449880350f42881d02c104503a0f12100d00d9030109540c1c07400710072440019101c11015015440010116010320b182650040086006105400548a05a4440b000c5459002c42042a24000c1d0700c0c0b0429441051607000060340d00b0441e011009021402d425200c80c810304044880c1d85080c4d0040519070520902c2415421030354480e00c213401d50900f010341d11940e141004038602152045003250511810022480e540f0000c140c08085038030150403103243c40140c540842d181c1d002880010007409003c10800f86840c015030307002140e1440c245070b45041654401e106401c1d00ca5403260103042c0d8100700241c0008000da03039451444202e82c2d81090200d4008600080200149071001a08020f040c01c088003091060404880d486041d220455440740340244030319032119401c1e11104021710600100c035101e81400220150a0785e01521407500342030054440034082d0442c485410ba0120300f1034400704010038184144411042c0c104000d200c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 279222940 1250 279221690 279221729
    0xe01050105041512150f050901090b01140604090c0e0904080c06011215090203010605121e0d050d05060402130311040605090c16060b04090308100b03072c0604 70
    0x301d03002e02c0a200c020403800c810a1006080340803203131120540c482c102a20310117104481070014940395622131016802e06050001ca814150421400903000c0d40d020522644d0303c0001c406625941a903580e04000c080c0300c10000240c0503400128907030580d0401d82c5d54278600000194a20400f140c0c200d55052020500140e840360800c1103d0241140e030040e00441a4107444071742242c807051260441e905d03154118a0210341b001e402c0300300249405000c58140790004a82141c4450800305000071181110040150484000a41c1c0140d403d40351109032510110f40f010030043d210091015401c103401700241c5228582c0e00106200450140900141c6010203000700010703209642e10252058451a050011190343c183c00c5070f01e484030b8a441044284c2003850075801600c07183c03e0503135200340fa280005c0306240e0030401c424410070b500c1c425100015140d940d1890140000e55040c0000340d5100c0c0f003d14450922108141c001e142d402e083c4080d015640006080c603800342d007140c800021500780000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 279224190 1250 279222940 279222949
    0x709180c0f06050405240a030608100507050316020a0b0c120a0b0619030609050f041a04031205040318031103010c030e10020703110d0f080a05370e01050105 69
    0xd00040c01c50340300000d00d03255004040d40038a004103849404555011803015031400c6008030b0448041070915103440c81c00401a004000078030980d1900c1c01003104041c1800394070b12400d48130300c0e80ba03117404d401d6488030103100d10750001088150f01944900510138001c03d07004d4201c24804c0405510743d994919188078010301cac03c1c8001d002d0181e0309090010304c003880c0d03490310b00360b6644441c400328900e01025100e000301c0107024184c0c04110100d00e04418004040428112144901d001d001103000300c4000c50000c0704c0c1c811048078007500064400039414103440094000703a40150091810b070170040d0302e0f40f11300401271a20b9401244c42d245811401c02c19401c003801045004070329401c04010b0403031840030080d00e5500c0703000461400e550010b1a0410507000b9044040d5824007a4119060250070f050054144ca102c0140c01c03020480400001d8900c000f64003d0510461074540740910340c0841a540503041c9122071140000351090301e401000d404100d12421100c1001d040c00400d10b03524040610 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 279225440 1250 279224190 279224213
    0x200d0911010f0917030909090d080903160602280309020f033f0d05090c300c030a0b060f0102010507090b180d030e040f020a0e060c070918 61
    0x40c140701c2d030301400382e10301c03034020b82d45208441d180d407440512281c49000041c00c510a00300007a0b41300c0c20300070030302010000001d408010504140c0f00c003501c582324280d4403503582c040d032140008030b180764401c0d440c000750440d0058030140340802141c044070600b10708a90740c02128002c6c040c000a035160111004d610305044144d038400d80c203070081d0148104900d00c4031421207a11090703041082007030912808660f85507042070040107904400f5070b00d500a000341030340500b1003070f01c054140b84169a401c0b00146065880c200f200c45042261420031b141c2e100f0619000c1001040802c1c103400350740d409038890b45050180006203446106036000900c0c0510400c002d20114402543c11a031401080042c3d0f80c1c1c000f01741000b0354411100b2142c0712807007000c0501154603410312598100100c12120030030180c1010981d18400c000f12003d001034107151602d00300b2802100c101800103103080900ca562410040c0060113800340010680340360603261003082064500724a42840c80c00990132924091128400301c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 279226690 1250 279225440 279225473
    0x30c030f18110f010203070308040c0e0c190306050a0302010e0d080309031b0d020622060c120b010320070609050105040804060807050a020d0503090114010611011406030a06200d09 79
    0x8180051a1100001d50741d007e500c1c8010700f17010449001c182800700c00c0414030014040d00c04810028981038190400541245400c000029110380203800703c3d13030007130080340242d81000d01760b1030384a4555001103a408403010b01c6590005400301c501e00100329030030b0081d44985440001180c0d5a103410440d0808010340c80c0c09543c468202c0032040032059030109400d904203d07050240445030100010130b000c0a0741c4117000130101846c1c039042c280c00c1504075041003210300c0d401c80d0421074041e60000540c161100c000f1442d444451545840d000e80c1385c40005400064024600060a41440d81e41d40d401c4507816103040d500164040741c10402254400c45c020343c000e2003803801c1c90030312149620103990761201805080a11001000086004009622001c240490000102c4a95a4540700505061090240c0782581d50801e00c4503400d00400300d50076070054002400401400d607098540070020016180e06a07800400280400c12102e003c40103402c002c0c00542c000114550789150615400382060b82 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 279227940 1250 279226690 279226699
    0x61b021f02130b090a080f010b0f0f0102120c010e070e060306070504080303010b030a020c100b0a09090c050d050a0b04030f0e0a12110a0f03050a020406081507030c030f1811 76
    0x28016010000350b04821502c420b8015500d402c0b0f1070001900390740ca43c3d08504602d204030007400120351015001031450281c150303004000380d90320b00b040c444160704100c1d890b40075a00900404a6669900c1e00401a25107640c00006102060b4003000b400d2040c150720207480068070700103105543c03900f400001d8101d00c031414484e2070580b801101c2038890005210b517448000c0d0110010710ba01d00290112840f0050b00700036191140c0c00c4005000042101c440d003240070308440c44001c5240c80d41c030f108510044d0381000b0545401460711003045110060804111083e002d410007400c00a610150708502862003a2220300b6080842c040c010145031481c001e0030703c0740441d08420011070400d02c10b0210f01c0b940040070807a0101c03110380400d201201c80c1e404190402002031000050050210310240458421202401b940c2c1d41d88002546d45c000d400c07885c6840e08190303000f069010740a588204090301c0607040c04942d0329020800d40040310301d52120280141c1510300484100b0484201201020b0b80496 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 279229190 1250 279227940 279227947
    0x30b060d0f03080709030c090e010b01021b1212070507150f0c230f0307020f0307060f0f021c08011d010311011d150c0607090605090409061b021f02 65
    0x1141d4458001e26000040e05103d400e2000c1566039200c1d030603a9000d1600b00344411602507a4821501c024502d04680c04d038a5440c15001d403025605c040348044191030140d00c8100e14100349820001115a6096244e071103103e40074040c2c900514450260182c180642d025120721803400700086036040182c140142081181c80c00303103c196070400d640c0078220b80c00c58440d01c104100390038030601406d8001741c2c0d00014880d0030684035800c440000100941d92003581c010b4407601d500700a2658804141c080c1c0e0022401030183c0d6100c4c18806c0c3d9050416040510446101e0a030003a091040031817240640400200c0301c00060041482280c0c91f405d0700c2042c80290a243d6255448203100032018108407410802ca2580b041030002710010180302803d03004080061120010440c24281e034000004d4484ca406400005418140500c0c002421960700d6250146070400620411005080d091811100d142da21141e02c0c00c0030100d008040400703801d035002003440101980c100a030030540c4c24503400004d401003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 279230440 1250 279229190 279229193
    0x607020609151017010b0d080c0705010e0f060309030d18030906020307150b0d0203070f1703040602070302040b0a0e0414070b04180e0102070206030a09021801050d12091502010501030b060d 83
    0x10082c40c411142100c0140c0305001c4e0807001e80d0301500a526030168804580440002480a0140100b0341e1050030421518a00e070380c0c500644040d220007440c0d1f41d020000012052441c104880103550050080c025245000440d071084400c0f038101a101103050007124103c801095040780524000c0c0030103000842c00c0105a5440c2c11540140880107299291079111090198a42005d4940d481e136006083c0c8010300d803100040c01c2e0b9007160b84191100500541c400d8803817604c0200c1100c0958407664060105a400c5070203000180c1403041c0410341020a181001900098448600340264802c0c62110404030041400c94541140c0f5000b8103800760f0100300401104032012045840e04e8200300d40420a40c50501c049402401401c1001e9000b203000400c00004682c254050070040e072080350400080e41ca00c5031180c81d4034500740601904030910329200300200d080c0e40e0001505030b0341e5142c1141081d46803203080001540c4d8120b1240980c1d1224010300800c8103001038154011015955441a6840d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 279231690 1250 279230440 279230461
    0x10506010c080724091a06010903020307090b010903080a0e0f09070f1b1a1e160305060a030c0611061e040212010e0106060509040506031b10050408060702060915 71
    0xf003050007030607181400c0380b541e241181c844000d2031841016034200044517081c103100341000c107082041407100103c0d40004040b0b60040d180c0c03c2c1034a40280c020001c60307040c40010f0004004148030780d81032083c813000002c0010300100044c82c0e00c00390b83e9500301c100240c01e428041031b80d00180c4134a12500b0b40700208440980e01c00f5090504491616215124007828010f00302c513648103242c05800040409102c0d19034030703001d0340418000d41c503040301c1603d41c0c130342d016211410072404d5922a440c519210146964a40309400003600040018072244856a0303982d41c409050f515640000c3c0030407a615046100b41000384085070340320650040e00140492000d620000b00d04000780001c0c032840700c1c0003a111404409501031900180080001c00046403902c2000e0104d800c2030302821700c600d04140002c0c0250401150911000d5210780154002c66048020062142290580c000420205000020b0381c020b0030082c003030189120b50080c0089040c01c080c454141104110844481c4844009000e04100d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 279232940 1250 279231690 279231697
    0xb0f0f0a1802060301030c03120c0c0e06010219060b040e0c0607062c0a120203090102060a020a02030c0102030a05011d0705071b03051c0306080708030d0c0c020d05060603010506010c08 81
    0x5406100040c000006207140340c0070208948080c1d00702002000200410040c07843c100252030080e00500c1c5803800c58003044a2620a1400c0100154050542005520031b0420050b40110050058401050000c40e05007088000404240c901c00d1301e4a4014503035003414071982d10692250030180140c40d4010002c120f0501c1000c1d0b0050440c0d640d130401c04540441d0035000e0b40c4520090300d5400440000a02455030381004210540c0d125042c0140704a125000000303c3c0c110b40010f03005806603980350714444000b50406030009040d0b01082040418406003840110320901c4000d030b00041d994108010540e8091480d038042d0b00012007032040c010056001410780314100e600000340d22000010a10b909a0000d50b5480248180303e800c0c011600c1b202030007140c425612255804010482e0388200c1c1d95030b43d064503c80c42440b0b400070031603865184044d4000706074840032400c203804160f00f540c2c00b03c5d1044100410503940f9401440c00c2c41450701e400e0042c260040d00919041000425641381c0f552280b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 279234190 1250 279232940 279232951
    0xb01030204080705101b0302010905010f05070f12020c01110c2112040204020405040e10050603011815200403030905060304110409050a0510090606050604030b0c0d0906020f070b0f0f 80
    0x860b040b41c5840014446c1d0119030041101400701c00e0310314090714001c0c1c06050000d0086502d5424280004240301440c0710321807060f2010742e91a0154140441c0513142c01a06507141001641c0802010340c6100c0e003401070702102486000b0182d85c511610b40024203080941e04296003410108000300821141c0b801520042c1001c8800840541c9461000800a20032030f482660020300b850480708000d003011840001030b10001600b0310450791130204042c202c0d8582e410304150540074042010108040020b0403400c42c000a40001d40c40506640020200e0946c8030f134115682d0380020f0a20815911104400050002f5111a41141060b540d0700c1c028225011182d40101c0d03485000300140031042011b548001c0e00241601d501091024071040a0280444281c5410303041240000311401c00c9000c0f1001c1341e402c84d1041103075071200e040205460740a002c0030402c0c41e441c0d29010b00407e8542c03008001c2c101180103234a0b5070b68203030310b041400c0020080400911541c0c40d030070040720000d2101a80d0307000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 279235440 1250 279234190 279234199
    0x4150908070b040e090304051003020301090b04090203120d061e050102070803090109150c060504060204170f06060103090c0b040905010e0c18060307090b040b040e0c070c12150504150b01030204080705 88
    0x41e41c5041060f403031030082360300156001c464040b4811251382c0641c0214180e42c050b0030305010014100f414401a80d031006030007501503110101001401c8a050003410b010614660040b03650350b40c9410030012640012580c0b1540994090104019038040105d00d004002c188099400c4c0303a034001c0083c0010030340d0b204400811540c145d00015451040c0321034080160302c900100b0090a081c1046c800030b406c180264061400314010b00c1d0070174070001609034220503200b002080103546e80401140600b4034205d0446201024010118000c90300c0c40140c8040c000d0944002003541c50700f140002d4886010708507000c40c07102003204031f154141c60800d096030b9520943d1390359900c0d2528035048402c900154000c488050f0b012802050310b140e010001d1045400d40071030001c058484030303c46200380c4648203005110007030031401007140b02c03100d1032148501c50054001c00d00c0c04030005104004c4d0b94045070103c960448229800c07040349158440c170004880c080c6001c5050034181042155510b000d40202e5115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 279236690 1250 279235440 279235469
    0x506090f06060a050c1e010b0a081209030f060906070f0807051b1009080705070506270406050414090f03030106200a080a08071202070f02210304150908070b04 70
    0x3e5030700403022030b80d402c0008021151074203501900c84081d510802511400e55003800800480344c40c0c220380100c1039034404001b5001c02c282d80041320440c0c0d8007041c1155054001e030040005001402e00551307108606083c0604070720705d004c00c8010301a865a0009406002211040c441310f03a6209003506d041d00da10030340080c3e150311041c0c009480d285502c280c2c100082c2c00c1c1140901044900701c080c0003030324803480803100d80c00d490380304018550203050079403000c04e802036030789084000c1841d0340303622010030140001545c5900c40d80843c00f0350305056424460030480d5421321000e08001c2194110428107180914155418544010071381000084030705840017806102e242156421300490300d0041e8040681555900002401382c42281c088520802141c41c41d00f094820078881c1c02250308195128034084200c680780c0d402c2120b004070607402580e1041444412224001e0100003c0000c0e1125a28030090300c05c040600070082602904002020381054504200301c160f02e4058500342d45401030032084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 279237940 1250 279236690 279236707
    0x307020a05010501060e180c07170c030d0204051206191a06040f0608070306050d0605150a08010203060a14060904110c1515040b030d030c05040b030c0c010506090f0606 74
    0x1401800c035101030201c0d40b0b050000240c2d144c12611091115400b51558911160b4141d041d809a0324100c0f0100c0d0006400c00a030700028031180c1d84c803201042c442c540c060502c1c140350704c4d01e80703950408034000094075400103050100b490300c00320001080800200405171454181c401d41440702c1d07038101403003016444905591403a84822940034642e00003038a6181c461b139442100101900c09881400d006c140034002007914036110f80501002d9074030182c4500d4220b00030f03503110001404005c100502c50414040380a18a55904c006103004003070090001d038403403c0031010490500700c2d41d4405001d0600c2c045903514183c03503903020b4a0000c1811240081c841035160440c8805200d1810300396107038001c0700380c2e2056886411502c03501843d000703032649210344280b209100c11a5110070810381c0c1039000d00f4450000d144280c0000f00244843e2030040c4c04d00d030740d40c0b4820b03031260170503110b01c0c8068001051170040e10509200c1c00d42c3c0720350121010080ba06080c0f050340e0b061100503141c140681d000007240300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 279239190 1250 279237940 279237943
    0x1c03060b0327070515070c060c05030a0c1104050a0605040e03040302090612030915030a2007060b040204081204030b0a05010b0d02070206091c050607050f160f060e250e0408030702 79
    0x60081001510103170710030700c0d20000d9805035413011108a51405c443d00e800b085603841754940d01c0d020340e40100103515200c00c2d02c1007500c04141c070403c121035000c00015000102d40315401041c2c042d145409020418078107040c00c00c41503c039502514801c41e402444100701581c0d0782c1c84016046503058402400e002c8824010354118401d0a42058004c1e041140440300c16007200000d600c19280d0f950301f0440303054040001c5100504580781e030711070340c031082c064240426201c1c0d01030241d214004000500d00347c1e455008074104414140d100f511828007040820a202030f200c0c0d0540d004640030020417483d0b0604031081400d000c0c46100619440d400300303400b07085441e150216103032032100402110031045902c15500002c440b02c1421660340c0140c6020400c030601501c00e036500960714401e00703820311111518103107200c0000c10041c0c51284940c480c03140820307800c1c490907106403101009002d6003a843c2146405003e220a80c0e041074510b41d000070010300244100c0b90741c105502c0501c00eaa00d4590300801c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 279240440 1250 279239190 279239203
    0x702160501031a101e0503010b07031d100f0315120b0a02040e0a0614030d050406110a02130219050403030203090409061b0806031213150c051c03060b0327 68
    0x203402042c0302c0b0130822842d40020b0071500307041c03202001411000482104507020700081c410041e1001c400d2200c82d001074041c121440e40d6000300354048114500000010702d1b0309401c0c02c010808110200c41c0e40000c2039041c0203c03110741c00c0020348142c0992811220000344180e0450207000c1641000c00305001e000c141e01158001e069004246ca82400c0100d82c0c01e000300518464050220203000120380c06003070103d591000345446841e0b450030546040c034251202c180b42c40d00102e842c00340003051801aa21040040b8402169610060701c03881a00026103200f0041e0382c50b41c05010b030501041000903400011160001016100820808105c0ca4800041c00002001c1c1100c25011680741d500d450b07020101520403101203044404140c0024048038151040800c244001c11214030284215850722841c010502c145241010303c0c9136258a030396050142e654940b1019468001415082503071500034003025000902e8003900c1c60406500d1030007003180f03c0c02c412070b0741038602030610714030300051101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 279241690 1250 279240440 279240491
    0x170408030915040501060f080c090114041e14060d08190537030204030b010e1308030907151d010c0203030d0f0212100b030403050c0c1017070216050103 67
    0x30301c0710b24181860030501a001034052036002c3c504840380043d00100019589101c64806046100182d08107011865031441102c0b0366900140c4400c03141140c605010a0081480348034000003411a02c828100d41181c400a0f000f240b01c0c03400800711501250841048030004100140c4078030541d8514002076880d40244403c3c24800b003c008112054140c049494555400000d600d9002450502009a049010f140030141c034031702e02100144503c0540c1200d10340c110481c079122492250b0143d40380d8440303034011154120607401c602000c000e88050149105102001400d00030401c0b01e01c00b4542034644684180070341003012200e84c86066442c140304683e00346440303030f400740405c0c260ba003220406076004140001000c0349140004540110992324036040d1b0388080da0107480c1da200d5403021540c1d81c101c1c02c69400b0034022140707621141d5844010b10034221090342c69013428444c0000c94852003980080241041d500901c20480703030001c0026105c02515024200041e0888488a00740c5095618024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 279242940 1250 279241690 279241723
    0x7091a22181a10080610050105180d1a01061d01032f04170d05032404020d05090c01020d0e010f050d0612050f0a080720040507110705011704080309 65
    0x18914440582c800203039100303c00940c1610b61a0350f80326401662004111903070144805000c0c02403110b58811702c006c09041c42c1421000100e81004800036060302449041241c0e0140150080c2440011a034905801855281820400c480500b003200d202800001111410159550201c040c1c03994113010100c1c903160701c4840c2101101100600c41c02c164418040d0000d064650901550f40340f6000600002007000c03560780b6400e544440b040f510054003001c0d01c03501c250f864216a2811611284040e00b100c101200000c249130400c1c180e994204491703441c100d81190031014222040ca41c00102d603840b400710030710780401c200c800e06030116990300948a4021807a81000c2c00007900321080084901030500483c16100e40d2900c8036199a51042c59080084c10381c5018403804020031b403800c1180c04140e61005802801901000005040316021640100400e0030031481102c202d00c02c00410303000d04800c0c20100d040300c1717840140003c1c5110051000300118800400036000c3c200c00e10510204111002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 279244190 1250 279242940 279242963
    0x306090303021e18090606040312020307050a050703031710060e0f041b0e1f08060406080a0b0a06080d0822050706080901050a1a0f040e07091a2218 65
    0x2d90415181d1210444a401c0f13820340559000a107000b0500c14080c2c50002c011600d0715140d9641d1054801070040e1140560105200d450085002408100902441540500543ca00b10320703018021010203407140b070b50307a0904001c004107c28040b000400f075a2050404c039541d03425100001b01280d040241e00c0743c00c82d08011440c9412001a0361000d035042698940c604c8030001c000620028010030760000740ae01c2200b41c50640c079940214406a007115026002040194a992046190122507078089030f104c080b050030041140007501c01d02c6c1c00b80140d0000380c040c00d040303000010080840686410741925040107a041a40034ac4001c4d50551544101174070906a6100809007000b136040350811a0741d42003800007031420950f4826888072102d1700c06440d003100e200742c0611008100068003103070499610407184004603001c01c1404c004040609003c0f40ac2c9104251402d211928250030900900f4210100e0600c0010b20200c0060301400074400607015811001d0741301c5444850401030525100007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 279245440 1250 279244190 279244237
    0x31212010302040b0f0306160207030210051b030c0a0822060c03110106030f1203090b0112020a0504020708030c070c09290d030e2103130e07080103020a030609030302 73
    0x20a0034100d82c0215401c01a611400b018410340c3c0121095180c0c0c07607081000041c0e5024038104280c010b8040f00c0c41241c81250b00c030342c00300d00c0b104443d28150001c924086104a041205005018030348104400614207240180c4210381da03a0b00e0444005002c203c000c115101c110a5403101c22411a0000c4007040509564400243c45156039100a0700002d004070249803000030140188400c603580150011407440316512080d26401d4060011010591182c4511022031801482c19001c2c04008041040c20b05251041200c20724150b0301241c05203005000c12004225024140c0341c1c0903900940d4681e40d03070310b0392605140074501c43c0c1060b5036191810203494a141c004051548500200003840020080c8100030400700c02e5492100400098110040d1481401c021060742481c40d06441d0450344001103007803950031504401e074642440d00c0034034420850601e88401c12034109401b8100000c0d6541560042842910203010242c483d503200c40a0700c0401d8880d5044030018440707803208540c1074244 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 279246690 1250 279245440 279245467
    0x20d020703020d081b0a0c020307031211011e051815101d0703020a05121504110a0c0f0206070204090c050a060302092803120c0c09050702030901030b0312 68
    0x980c010310641c240c01d40303160f0284c0b41a90181040082200d0b201140038072141d40356102d40c41e01c400700401c2010040c0180c03400c00078030024520032081581c884040d080002c03c1c1c3c010701440c0084980c10b0110a00d41c80d00c0c50f80a00c0341ca000718120106903681e840000d11286550307503010b00d400d031041c4082402c061071351500d040d008001030410504d000360340311001d0300811500111020040303113000210300b074507001313500504108800d8180203040600780440d90ba10590b040b61800391304050b605070150185014800c00441f0100910807030708120180500603c400480c440080c4030408a041140641d41c503541a00d9100d50300500501c0007000710f180190300c507002d1344142806070180d90404914540640284c554509000d0321100c42c452200c165000350a0008549618034208100044082007c02c114500c5c5c100d44c0b03403200405800305d450200c2c505c40565200803100c901e81014444119030120455183d60303800d01e00401c0000454002a081c03c000705400404d207407000440d400940c52 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 279247940 1250 279246690 279246697
    0x150609060c03031f0510030c0e041817030702060411030709020c03130501050408100f090210021e070509010b07050f0d030b0103060b03040305072d0309051903080a0e060d020d02 78
    0x200c139415294090181c080846240d0103020f510100308203002c242c4d0381c400e40c80303800300c001d0318640321714403110203c045001c85a1490b500200c00c129107020074240b0041003104e000008001c1c11407881c0d440c203060005e44689010300010130b60025204041e079981c0d41081000042c000c1c10744219038507041c042d040341d96540441c03d0000030320011000010950f0051080d141201c12500103800c280d90315042e0107008141020503400101d64030a91040503071100c1d07498501c41d24454000b02140c02c0f00b90600c0c009170701100704c03414086c0d1240000384090344802c0701c054111030890800c035440c0e040e01c1c030b01a0b003840400c4200404a03c030385441c01c5d50b034507416001101707640000c0e01e04007d0f0a07203a00034140b992200b150b01802040e000c010050000e000000444c031b004401030105140c0040e24208081500d048200a0f0002140c1103000d000c54a01084149402d9841c070aa1480d00c0c0d14580c0c41000e140a0400c064003803202d0300e4020200303a283c840c215401810072103030465031290b05001070300c001d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 279249190 1250 279247940 279247951
    0xa081c140d0516110304050d020a0317040e0a0c0c0f050c091614040e0411030f03030a0f0b03010c0c060506041409100e0601180507030605270601050a0503150609060c0303 75
    0x1403c1c90b990406050056807460088035101016501d414148018441c00c11140720081741c1081400c4c0000000c40d03140304540a683e41d25841c02c03980d503444c2c002814404c0e00050500c2c100d0724a4007180c1c40c1d03c1504614850811580000704412059980c1055404d00e01989040e58004580f10300b041b01d185a042841107101d2880e44070b0701030030100d11194000902480c0503401100e03002d000450080f504240900781c18540090481c1e509500d1882d0050858000340c81111320b180c3c9031503604805402c207001c0e42515040540003000303b00b0300b181c401809185c40700c0000c0c142c941c1e1100400c0003030f212074001000307498080d140d00c00c150504031111580c54800141a6135003615210a03250101c00106c0d40b5070403102804288080d403117a141000340202006000c1106240d916000061540c603080d585c119004100e82c2c08480005d500408441a4200105001c0c10040e040140000c80340d000803c0d20f4100f075220b070b8680a0f90000701c022410074819141411381c084004a000c404195002004501c40c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 279250440 1250 279249190 279249211
    0x50613030807050406020a0807081b07090c0f0e090603010e0703140609010b0a0603020a021f020a111f0b2b1b06091403010902130b0108060a081c140d05 67
    0xc2e0344007102140d260265000e401d005030014400a130100380c0580140404074003911401d450f0034806030f101c51441c100c2c0062507103160000c0d1020000b02c80e03244241d10380240c2c2d906000e08900e0000b2030003400d1f42c00a8031001d01c103120b444081492900c09511030458410001c0440d1b1125450781801c81e108002090401ca1601c00c0c600010281441802035042d400e2025281d0002c9505180301130340a50000030700001188160b4881da0785206802c500b44020100b0b074500141d0310f4042ca84000c1c0000741c1e00d201c00038558085071030a10403454039180c45016541c1d00e6000548540b8807c005105c80302464180d0100c0d1000788a10100c01c07000400c0c051240344100c0d042c4000110403640741c24a01c405100e42808a5a4660100041c0c120480f00101c4404000e0000a0301e08003940012100f10302200890038290350b03101c1c406110358100a4050700080115000340c03c0d02d01d403c0720369a44200040041c6003c1c040c00b0a0f030850980030b08955400305400c01300c400e0315a0701c00390303080009060869248010303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 279251690 1250 279250440 279250457
    0xc050403061506020c090705121914010602060c0903160f08060f01050d02040906090218090c0301020412110109090504260a020607030c170118050601050a0210110705061303 76
    0x2c6544803403200086580c3c80e0040c1100050403002c000f03a640c030003400c02040c04410003018000b04440800c003031189010701110103803010220491805c0382c10903034080180011400040c852150001019940f2034400b858007a582c0000740d01080c00c0c48008614883d05115520000c144d0f8003618000005031100e01c002c8455907a40c0440c8100c3d180400c0c40b406411161480400c805420181c0042d111103000d010007241c102d1480d4045030300d07002d0210311007005a0280090110180c82840b405500100c101c00942c2401d05141100342c400c0e106000c0240701c3d1501e42079148250f4018051784005002070b10b0100490f2901d03046c82d64003542c403480585203202d00b092100203100001c2c000e9a282180741e40c020101d5542e9428140c00801480b9080c03004e0100714110348010b90401d40b12140070b0400700d80480718442050341d0440603120080d0955040c020203120311100141c0c005500d8091085100f40441d09040500c180c1c941c0d4452400050b01c0c5004140411580b90320201e901c500891283d0361b00c040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 279252940 1250 279251690 279251711
    0x5010b0403050d170a052d070801050d110909010e190c0e01030f0210120c090918121b0212031201050603060a0b07060e010e0d140307050f030a0608010c05040306 71
    0x2201594441340d006404040c80c08940c0e40d00c0f141c0e01142d40030381e450481740348a07021040d000355001d107a0900c151210358000c003000070722070340905a24014402a60141d06031001c07995115641e84d95000d255010b05c800100003086001c0940001160110302c0e03064401a41c0c001d6040581c10066803429201560410000601100604103090480350404020501406913908110b80843d010041030200040020545110702580c406c0100240340f6840305044141340040b118143d86800c03150f000e414100105940c0032842107080340c1c20354a8175241a11054152304101c1038803240710301c400b0717400c44200c0c1800c0b41c82d44d41c00401070004039828082100680c0c1d0f264104032807071008880440c1c215240000c00c101c080c4100e00a410490711590010030f07500c910780c550500b10f4600350500307452644080f00e2058803d809c408108810305074031300b8007881d40c50885005049442011060035101000000154840303c0c036074041c60191101c48028040c0d103441100c020f00d260480c0c001981d22524000c0f4641 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 279254190 1250 279252940 279252947
    0x1206010609140a1203030b090c09031b0d02060a210c1701050f060f1c2711011409030703050105010f17060c0a09080d0903030e060705070302060f0d05010b0403050d 72
    0x541000c00800c8452100d080000c1084c90039603941d0304401345501c54555240d96640d49951600c40d141100c0415100d605007810545886031008106401c504e155406415a450300c4124035199601502d0080d0b1701c02d01080201c1d0141046440015030159001069a00213000d8021000321502507607010102c09102c218600014020b1190307990150b40030000840303c0c1421400381164054480700c86060295102c00090440707414183c038401959504002c0e19051030041d80f415014044284501080a070303596040c80c0e8141d031011031790502c4000c1e11020703c41000d14007121164a00581502e860581d03c3c941a40a000300b8003031079444240010010400c260103a004802c0765481e10018006034030350000424860340030300b42c104100494114041844c0c0400c02130f2145080c0d05503134010b141851420028000d011501c48544205810440315010910004104042d26012a8425511125891102c0140c4502c0744041102c030b00f41000020302409032009003017102d010300d00b541e6a1640030320044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 279255440 1250 279254190 279254219
    0x303040312140a0f0e0f0705040c020d121a04090b24010c12020c03030a02070f0905090a020f01021c08040b010501050f030c030720010b041b02030a050702030c1206010609 75
    0x151921040b040041c00801181d000002518210480061020400310016040407014240300005601010f410003030390620b84113840e00001c00b48060010069100d01c000c091280c1800c10a01180d01c50381d42c0d18030303d0000141440c3c0385100a00400c4030301840d103040040c0550860b43d0f50340007500c80b10903d0382d440d803c40d1040030b003c10503512a01a0030710396598610481e40f00d4110b5085101e035100e03032141c030b0b2410002050b403042140c00400f007103480c282040403280324603002050454203007000d01000d41303000a4103a80a60b03040750141200c07032003040103c2c6004000300200c00061728181e214000c00350883c420500030b40c00350100f51656070702c03580195202c3c03003408c6240301e03413080420001d00b000300b65074060b581000142c903200c807620003d20a0903001010305210801965550300c0d4901c100c0c6014422103408600011918503413580d50384003c0d4590054203108400d10000290010441d98207000343c2d40790240041035103900d02e400c5180241c0c1e840c0309010740c002003030b0722510201d40000114182c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 279256690 1250 279255440 279255461
    0x50d06170c011b0308040507030b240409020609040e0a0602040906030302060604050903041203141c0c090f05010c030509030a03050c15100605280f030b01080105031914030c0303040312 81
    0x120f0f09102c4903540407620204020816200c1e409904008800600300c101c00b00d0040c800d0120420313558400f07031401071070441001a01c1d4825407400040d100142c030344400b910b0109c242220b0020341803641c2d001c000d00740548070200410952001a01082c0514554000001d0324043c0d400c83d040c50762064180401c980c02940c581d0503e61050000704030508040b00000c2c1250300c00e142c020040392151050802d02d0308040c101d80c3c02d0314800d80d80024511114440d049429103240f40c40c000c0c6624002440c18808100c1c010203040013030541001003814080d404981c90341802a08a0780020715605008106030042403401e0b02900800700621034081100d0500e42c0100040504280d20304d00d440340035542503028801c0c45020004c042842c80c0030136014842c1104184054803100c009039240940101140c0a00200e00d0601003480011300240c0c500081070000b40c14241c0c80d0051013141070034540040303401d400d81942ca902c4009910381c80c40380d02001950003144070ba11614010400244002d080c0e8244510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 279257940 1250 279256690 279256727
    0xe0102190f1713060e0a0506070804030e0315011802040b0414031203010311091905071d180a0203130804031203051b1206011806080402090109060608070e01050d06170c01 75
    0x6400030564a42c0190760b5217024a0031140c5441550384e5032810325604a4282d400b02d015002044181904a5400c0c40c603010110042e001c00300c0c3c2d603100c0015018040c020310750008903040300307007644400c40d90449010b801025403c42d2143d035182824420880c035005424000c0c01482d40400120280348180c1e816207521030288103040e007804040c0804000001c110300019041c81400308241b0745e0500c1024050b890364ad987c1c1100308843e00200709480704680e00b041c0507604003000c5100d0f50b158160900e80042d008000541c0e01d0700c8801c4210000010b500c0d01400c9900001000410083c0d20505805465540c1d01c06000d01d60380e03120034900c09544e07412442c2c1050300401050503000300c6104c0c540d501c850305040a000648042d01c0c00c081c820170640100d80800d03ca2010321065117422a5406d005142c1c940c010300c070050400c84000e0020030050680360074401c802d1540522a07000303c058680380e01881d034040000070350302c1060301c0a602088040255500039120481e445502c9400034a0390303108011f2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 279259190 1250 279257940 279257971
    0x40e0a0c08010317070812040b060a05090903040909080d050720030a080402010309061d0718020c0d050a03021908011706010807060e04021209010b0307080703020307090e0102190f17 80
    0x5028136907590194100701c500705810094103016680c3c210100703028070b0294070000100d143c117200703018508203140c100341c0c807a59542c802c1242e0031100200f200e040e60b043c400003003180c0070203103010501d40c01654102e02c031190400c003c1040560f0300c28030484c00c040424403240c1030001400b03441502ca1142400f044009855880001d016501940000c14447d1296000140c61314540c140f403800f080000d00d100b05039811132030041002c8880b041c82a94500c0450360300b1850100000320640d0303200c00101e44038080c4500030507000030080c001c6c3e0503035040c0710140e20001c2c2d00210349030005013002000d000301240031b400c4070030f000c020120029a450603628490000c00c0360505284c02030b0307900b00000300010703441a002c11103001007035200544a40070f0400300e000403884500d5442018240100c40d001100681e008031700400c00345c2c2d80007501200300c80760f0120015030b0400000e191030192140700c26801c5040004c0d403070700440a03480f164810045d141690b4140802d100e00301036049a038000c0e910003205842c0207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 279260440 1250 279259190 279259223
    0x161a04054c0b010801050a1205190303050106090b071101080a02070503070516170316150c0908060c0a02030d0b0d0f1b0e04021c02010e0303040e0a0c080103 69
    0x4120100030351064041c1c001504074449109000410800440454070038030800c0510141240500211894242000d0403d5070500000c220b80489a20030b1295603135a810000c400c1c0441401a050340384042801d85011803041c0c01d001d4003a00080c462100000c199580000301143d0b2001a600e00682c0031803540300c4401050011600004090550324801c0d900700100d0000034020030050075158441c002801c2441d0140100d88203c500a602c013070402001144290138050021080b501c0898540c031214204036124123110030010b590024124009140075002c130002e640142c00c00c0103c4803d134007222051b40d41c4003080c05141c05a490300802503481803015130140c0089400c032860705100a42070321003a81250f200d0400385e084464060b600e01d4420001400054111114103000e03141e040002440c9040c2680071902d0b0301c68a440b03002d410300290b02410b003103a21400e0410704540e03006044984543c1c50303050500451006a07a40301c0c1051800c1441041280518940d904a90b0001101080509403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 279261690 1250 279260440 279260473
    0x5060907140a0c141e0606010f0f080408090d0b04060b010e013c08010303110616120e010203010b13140d12030b06070f050f01090b06060a0c0503161a0405 68
    0xf1071401c445a80c200142c0311071001c02003002103801582c0703108011840081107002820040e003d441c03203042052420400255035040100040b05408500d07019015a640341000c005a0152440f010341c010240c003036070424010310011182c05035004090030040b4803d4040195615820b230040b650100304d6174101100e01d407610841c454601c01c2e10070765510511080200803001d01607440040c002146e06030f0014400c0c180d000304400c1520843d00c0045c102c40c10301c071010b1006031320004010000c00400d40043d81c41095039412050045204c50003e44d100d5843c0e81420703120340c10414058840b51000c1c940001c00050b156800c000110000d011407800c1400780d1188120080d1400010090503101e2219100c5510b40400038940c45000d100c441411a10f2032030a142021600081c01d0329503810a10b0308030100310811401074210740300700d6600d41d441c4e2500310251403a8003140000b4100e4000812a201b41c0c013002081c034a10a446407010080143c651400010607100a540242680d80b01141410100c140e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 279262940 1250 279261690 279261707
    0x7030f090c0b0a02121b1006080606040c0e030601180b09040c0515071703060a1502280204110702192111130c0206060a03021305040218040605060907140a 68
    0x310340b041d140040700d021504038099206e04040342c0341c80ca1482c4401c2e1142014408900f500c44054030074030a8901e0916407564032003010304007610555603058116850b030700070300204040140150589046603503d81903120440001100041041c0c10421500c0c11450410300f024480c50b8410100380105042406020300c078440c222500303511110812000022600c0d100084204036805031071140d0700e1070544148004840954811021414440c950300c415a030041404003240300701307455904011151209005140c40384000107134001d4500058803401c03241a000030102140280c0d209848541e01440101c10071005110390741c618060741c0c0d000e00c6455180f10f00002c41c3ca0080303581e1002d0701244400624066910726150100507078075014202c00c01c0e018094190300401c11101500d013145940c0215090580d00030084060039a03550000d8219521012906030140140300140d4280c0350070702d404002442c0030348030940b0030350500c0c0010324610b2180e40010103000c2440d01c0c29041100c400c4041d2240741 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 279264190 1250 279262940 279262957
    0x60910021e16050f0303090d08070c170417060603010e03040e0f100504020c010b03010f0e0c01080a06171f1a040c030e01020a02031201050a0602070b0a230307030f090c0b 75
    0x41034030b40390703002c12010880c03002d02c0080035000c2d55490400700e0100e894000501035610500132154208a80650001e0018051340d80020495081c2c1d403404807c1c082d2441650011a1084015051038010100000e001e6114404c280c5c02001038840603005a950b07401207104080740b440002d030004004d0b4075100c0307c484d0002e5059005904850b20b036000642680c1110282221682d541c84040c034107481c017400389a01000c3e03220400c1004031400c1c0e0a00d52070b0180aa0064103100d804004108140310940c8203000510311040c04200681c00f5a003016201c00d00420300f0516500703201c1d004102e0032010310038052907854003403200310005824801d00000d4003449152806040d0340300c01040e040c103028001040c54540c6035010310f035280140d084c04440a281a0401406030546074010b004150300042e049042c0c44e00c603850291200c40f8040c040b107400404044083d105200d40a040200c00c0400015602810f2251001c2c4801040c03141d60400712040c4c520040c158410400c000c00c406c9030480000c2001d00b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 279265440 1250 279264190 279264217
    0x601060f03090b070f0e0a14011d19080f010e0a0303091a0106080108151b031b0a0c03080a0c093b040209070503130b06061605060910021e 61
    0x2407035a0f844101607500100c4501020a1805d06040116a4400400b041d0400102d845103002410001c03600360242080c6851414031102004102c0e05c1d00002c491210600d0004000c2400801100d05007410340426104120851060302403018280344103015560158a039103009001182d00c50b10304902034110a01c060700c2d1801490400840805042d003628017815242c2c030780360030951408a80d00d25101180c0040f000e80c0c0c6514090111203204011080251944a181540c60392a42d41e44000181e0300310640843c84c041c001480e03d41075401201040125000342c0f01e0440d0350380c550b441c882c140c40c12540070034005001801c1c14010440702e0903004026084d0b01008200100c1aa20502c81f160744140903141c008070b40c04104400c40c5000f07010260b1020552801500394146145c04580082c500314005110300e8440001603a151180340580d0400d4610383c01120f203945250903d56110482540c070400c45010381c0721400b1800342540202c07000001c4412a0701e0072402da00300c2c103481031f400c0300c5100c0000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 279266690 1250 279265440 279265451
    0x60c0a08071b271e0c0f050703021504020a080d080f010e0903120414010906020705070501090e1305210c2803051308012a0c2d050115080606030109050601060f03 71
    0x21490103201030983c04404c940001084020710300081c00540c400d0703000038100042004140c00203640030440c400d42220f00e42c615811a1074510000f0740501d9160480342c00ea21171340b00b03007a50243d401003e0740c0c020310301e588150301241d07280d00c1d10044529088900d2500c6038403c000b0689040c042900e4584e005000d8002907802c0c0030710116030707800c2d10712448080d1111a0080341f10014030900740143d400914003401d06042c4146480c1d40ca100300d140042012414060f0142e8420501c8001c1c880b4842d2071402950101102220003400002c54102c50f410310715500c43e44c1c02c83c3c00008007055003440d000600c0f0781d80c14107000d1070780e400316400da10a0501250405202c0d01c0021303108400d000d40041410182e0b0f04500300b0458860301c19a80c111300442a00300500c0207560404030380700c0301105c104987c480b0070500000e85000c1c8090030540300cad400000c0030303503180140c0c8209001c44003400c0000d0302c415038280d03103543d141c030300c02c05003a9102c464000c1c003e9080300004014650140c04540c640340100c0c10041795 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 279267940 1250 279266690 279266711
    0x6030c0910030201030e0303010e04030c110d0305030114040501080c04090f0b070801080f1f020c0102091201060501120b0a0501030b150a05090f0d03080a0b060c0a08071b27 76
    0x400d4081a1007211003155440c0c0c0c24021581c00d80641c203c1aa0031400079829903251545030403002c403003d000a810700120f4081c20302440503d4001040c04000a072041141000700e02c0c0c000c01c207a100b44035444c60350081403400c880910381401a01d0494040c06c00404036444103800b040300134000014100c3e02d10703006114110008803140b8140e48100601d4503a01074561502080d10309041c1c4101c4900d40c0b60700003044883d01030001c000090101d20b406075005860b0740c0300d682c18500901c156000c4e01d40c051000703c458000d40700705401c84070684800784e0342e8203031b003030b0036817207139900340c8044440d02c44d8891001001404154031a50040000039030083c001d10740040200c28000c1e03141d01c00092800041d200241100315810702001a51070aa8140d0307142407041c5031900c0040072040007421030312072651506034101d0f5503510007090780c181c086014180c480b86082841c1150756544070b40d1040304c1100b8811803141400b02c58510314000c4440c1035802141c080060110762070071440c8100d105054035a262180103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 279269190 1250 279267940 279267949
    0x1090b0109050709062a2307031103010b0d0204020f040b0d02070606050105040b120c1317010606140403060506060d0606030507080a1b03050612011118090105011706030c 75
    0x18001e0401c11000140c90521600c0142058607681121040c40500300000001140810814494481c5001100c0d0803100340c2c5418141e0510310700072603041190301c100c510f02d541c50100c0d549085030b01c04c002c80308040b41118149400e03550010109039001d80c0d0070500c1c1c0301508064004002032041141c0107031030680c6840d404212a004030070368851140d0b0108001e02040308a104a00c054a8242807040c1054502081c55a0300e22400c09070300074850741200030441c03c88040081e9101c404c0c80400e10462240c8982d05a4091100b41c00320982ca582040d50000d4aa800f070b040c2c005154504815840c500390854603071102800d8041c000a402c07040030089606142140e1082d80b0243c8101e9038081861b041c29000104a400090130800340c292078031500c0100301202454100f20340016003004200b5544100c0001c017400ca841e4101140c550030001001d444001d0600180b050001c0a46007400e40c02078002840a0b80c4400d0113040d002c55032120080c1c0b03842d0340e500425540040014111004e204510300800d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 279270440 1250 279269190 279269213
    0x90212070b0c01050a06121b031401021c150b07050a1a1509191503060e0105010f08010b060f030c1b0c010e010c021c0305070b09060a060816170109 65
    0x603020210214890b0880030080c0070740b0350040d244c00010311400b824a140915800008070b0010440c40d20300314a60100380024040f40d000316000000782061007a82c0c55124042e6100000210751421845400240b821451041c0160061042c0b07030845401c1c2000034550103075100c007509841034850400c80b1400500c8558070015540c104c0482e190060800407100040e00808031880742c824150501001684220005840401011044041513030300d80d203a6484401040f1360809401e50703040c0f512541658074150880c9048408510100003166515443e0b00d00700d42040c280c003a0300c00020040900c424407401c0c05590080002c4519070301d840c1480c0e017001500743c20002000e000d0340012038400e08640c0c2101081d440320000382005020140e456001034a050410401b1250060700300d2541e0007414859025200c4041e4006011380c00c60038191202a0340303440c21a00200746074103003000070450010204146407102118210300090303608240d5081d01241c0642c0f00b504c0316660354003a2002260810440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 279271690 1250 279270440 279270449
    0x40905120d020702011706010c0b0612030c0a030e090f010308030c040503031b070902040f0509070e03060a09150e0d11161d0a060305061602011d060f0a050903090409021207 76
    0x50f542e40c498800034240340b481002e11802c1c00e846800700f04007641c010b58030548840c0e004603050080ea64580004403240c0038114018036a2201180042013205c0024800c03007031500a0b1540c40c84440a02d0070401c2040080360300c1c40c81c80054000401c009050900a16085000000c42500302074507000400d00c4c54101d801c00c911a100f0700008007076110b005000a0700648000207040d45807505100c14001840820301c605030150010070000390400388103001e00840140007d0580b1128103121182402134a520b00050700c80e018500303254800315016105107410305071414003400c0d4100030040c080d40e82003500086090306001e01300105000f030003103da10f0000751243d61465814000fa1200c11805114001d15001c103c4c0c1c5004024400303c0d40000e1040d40c09680d48403010fa030700d816010124050040c3d0300c402201403556500c180f40e000c0c0c01044440c4958050800d0613610366074908040182d68054400a51a0300204489813840c185500014003032400580200002200829a0352038a812580f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 279272940 1250 279271690 279271717
    0x4170304111527030322050603010f0603230f1504050901020c0c030102280c02100906020c0a050907270807081c05030f0415050106080a15080c04090512 67
    0x41e0b459043d000c1c0303642e0500315054141500c0589042c0d9010036a68410894a282005e1840e207104d00c01c00001c049060141070050b28030358982d6514102201c10b20951701912010030b0070030f03104211042640306170410354100c01d00340e000c80e0f07100c1c0d5003d21040d030b102611040205a0710788001e445c03a01d480c021140212502d0000507614001d0150180c104420782c40c800703100e0707401001600220b601e04002900085280c3d035214038019400c02c02030320707801010900203401c0142ca4007a00c1210350403800781c10031a0504d4003175032a036007210010006880210b00a031580056880c0c0400e00c00b0f40300d4620035400100130702c4144581a524609040c40500325804440d039030340000301c01c4c0b1280405200e50400d41c410882e00700950800441d001d042804014504002c1406c00c40004060286000100341c89140c0c16104005550b1101802800707040d04659010409040141e0f4200002810018408036003048001e400861000801c100180403d0350003510303113120303074841041c203416000c0080004080b80b08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 279274190 1250 279272940 279272947
    0x9020f04180b04140f0f120a05130602100f091203050c12040506100e01030302070b030402150c0a0303111c0b010c051b04060e0601020d030c03060b04060c0c0e041703041115 76
    0xc40980750000c0a0003212040d080780d410300f22040800240d00f8180344400f501380c0e440e0002140120394902400c0181c900e42b60884c1c0000405a80200703030324840064010b014030581483c8041801901d078243d000500105030034500781c05079842036100301d400141c0f102d01c42c0e10b80110040c000303280e1581079600351190f0b0400014410741703c1d00410500000d00881c1c14645072076155840103511102548030b400540c1c0b0b00040080c04542d01c0444041d0518081c1081948880015503000d50b10b524a4038203d01080c50000314180d1104020140c8603a141c2015210700c401103280700340d60103844407466043c18840303413540c640c0020b10240040c0d0441d021180c3c00c00c01c0942400b0030081a60804d6002d003418003920800c0c4112643c1c00300700203848e009141404501041400d108a00405195000c1000305001007804241c1c036601c08803076403019000354403180b00c4544640703610050003401d8070b0084c0300c80d0213208004200d1040001a41c0c0c064044c40300300310501c6000c0b0101c1e180000d21440703000740030b0002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 279275440 1250 279274190 279274223
    0xf0224060a060c020102030417030f0a050c0601171b0609030601060f0216030b01033009031403030f042315090f1605060f040906060c02100309020f04180b04 69
    0x341c0091000b0001c9282c50820f0104540010f5103c1c4124000c51000341000402d05002c4070341042124061401d40e08015598032050100810a40118504a01d01d028031000010300000c24100e0340780a4041d0780161400c0c205041504803c8582d0018036900800d05001260071395605114250090015464940d44240c10300402410315a642c030380e151040321410010300104004014083c15a5031040504610703400c88200442e481d8102c010910f01ca0803400110543c2651240d21a021a840b4415403d10103040e401340d15207034002100d107580c6840c2118009800301e00001c01a00e80b0000801030340c007204036001c0d44c01c1d08044d200e0400805091152040c0804041d0802545000c200810080c1c0300500c1c1101141500700c03820b2140e148500004144000526909003c58006188411007040015580d14015006400d1440203903c0742150030702201c0310500900a168603241d0060007a0010781c3c101007004000c0c99481c0340c0304460003030850303c103000035401c4000078003903400313940108110075a8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 279276690 1250 279275440 279275449
    0x909150f0b03010b030f0703020c0604060b0a052e05040306052809030e01030506130905060103050f060f0c0a0c02090a0e0709060b070b040515070f0207060e0f010f022406 75
    0x100c0d4001c0295070010001004207810070803d89402c40318804126000340c035149000c601070701074064814000e00840080c002081500c2d44290b12a03075042d18200d290070340e58000c2103913030700a40706002103200c0c2c00003000081201c6030144240c841c03054200f450401c0d840751140c80488504540d071b01c0ca440c50011003500740712512001440903440514041c44201070564005011300d85442c4034038141521640415299030341c11b00903240748224044104009503c505040d13540e48001e10040c0c49034007800300c2c902d08640b40407594500c118040c004285885c1c81d89101c08466510142d4900d007007207250821200140c0d1003510301c90180b100210042450030510119504003007480c0d00600515240100401a02d20003909840c2c0e00c5401441e05065035a95007411800d0004074209031403d00d80700c0041107803698018102608401065080b91011610303003200795042c1d1050b4121540c004030801c0104081e600c99401c003002c011151066842d00c800105044860455494055140b951500200402400e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 279277940 1250 279276690 279276719
    0x60806030c1c1101051603020c18070936090c050a0807030308150402030106081e010608040f05010e030a0c05011406060702090403030e030d0b01030b030705130c090915 74
    0x204846400d004519411100204007260100403c21848545041c03401d80c029820380e805102114110780b54801c0a141c02500e418880e02e030b180c4908c10003054007a16100344410b052158505840f040c0c0f00c1070400b144481403601d01c07038498003007188104070006003c40380c50501e90078201403503002c502e0000924000f10290301d1a00b00b103000d1280240c0030003031404006545001c50b0340509200110b91610700c0c0003080240d00ca5800f50b0098000800051301e1540200607030306c615040015007040481040420007000003e103e00c40020300264080380206603482140e0411301d100d540000780c555401d07402c083c1140c0044500d803001c0b50150103182c0a01a00b0300902e40b010003441105111481c1c250002000c40c0a06140607009a440100050402d0702039403101c010b41480038102c0b41c41e0b4180f402c170f81002e012180d135038900090078103510b80020b040010390502640c50080816202d402044296002007402031502d6041009802c00000e1108091154031801c00e00c8002c0c07200e030203080c184901e22101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 279279190 1250 279277940 279277963
    0x420108071107060c030504030206030103030f2d0e0609042c0f060a0b15040e0a140402010804060507031112010f06020a1208042f09092a03031306080603 67
    0x216007070240d80e4071007000c514002034901c9410101e101d5051820121114021500000e410500c004008814182c000341d180a1076421540c6100306030207407003060310300900128a440c0c1403103222403180d42d040e809400c10071000403000d0001c9081140703044c001810399110a15150b140902d40f000c000301a407000481001d4100e000d00184410940b0600895441c2d4004001c0c440045e6584611b1807103948040701c4009208100c0030594440e600c0c2d92001e45030300d03401d0310410754041c58a508046001d09a10341c1c3c5100301c2d0140c4456040784ea441c1c641b10040c0800504907001c050741c480d40c01d100c3d084000c001d4841c6000200d0a0200e035030402e038808040c040705403c04400c0d54090080b40c0c0005a2a801d020411280c614002d4156106c900d480780c2d9564195852424842e10480d40e000e084054107601c894948044403002ca6031f85814100740d403102c002c2560f00f26020051340190040020700c403104010803201800b142c5c13074000140d40003240704c89580c200c100010b0480e4107106042c5002c000c1c142c8002d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 279280440 1250 279279190 279279197
    0x3070605150f031c03060f0602070810050103020303030f04111c060b0a03050709020c01020415030c0e15090405060f03010e03031005011b060b0d080c07230942010807 73
    0x40c1910b001994580083d00d03c001c940240001011016109070000c0c2d0050041d0402c0303030703885c50311a100a51140054002c00380c85109481c8501180800c0d4001c00d8101ca07000781c061841c544880e68030302d828140c0280141c90241c003040400006464906d445e82c0304640c0d0081c80359141d1010f191040c00d40746d0308028988034141040d4203201083c00030400350700300e401c0c28000681e20480c11811031f002e805658000842032190040044180e90581c11100e594000d82c1e441c0a80760170400c04000c541000741c008800108001d00600f96241403e92000e904070700010080e80303100c80c0c0100040d0940769110a010b00b190404010311800300e078050b4242e00500300908084c001900118281001c4018114014281540ba500d0040090f12440060f483c00c0e90030038402c13940c480e02c1d810343d60740d40e007001d01c28148940b8040c10b1103c4004043c00324100742d042e00400d034424a490f0a0003000c4a42c0001c03400300040c21204031100600c2e071160302402200d180f80c0b021041c3d4401032800240c10a039000f0300071003d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 279281690 1250 279280440 279280459
    0x13090803060909010605041107050607022a0102160605090907020a080f0a0c0c090519050c0f0f040b030115030c020a0209160c0f2001170f04080c0307060515 69
    0x519550192907004109840d0520b4558805840a0260605d540400e420615083c200901e03001c5040090100c00d001d1021114242c640000c101d90390070000054044420070513041070030703d03600704c2c40c807448151051044403a031440400b01101c8140381ea5008401041c0b0028107000380303080100310b59512400900241c284e2080c01e0b2100d1452380300380030091444c02c400044504e075507405080c036508c20b580c04c1102101e6103500c40362144002c000c03d90300070a64031703401e4056000460440c00740318800c4080d080c90304d060801e0440b13800107a4000320b0725011502000e00000c034000420f4000345009001c1d0f10602d0030703041c07140b0202030116807007004070100f19008221000090f07100c4105464200c04003200c180f00100c039400089401814003480189041d04402c60b02040c4505100107440c203824078203e41400b0b00344a03005580040c046515011052184e100040f05c199890144907801401800e1071440d0a81041c2031034110361003440300301c3c0c0303031951007061010940c0b84891540c002d0106403940d021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 279282940 1250 279281690 279281693
    0xa02040317040f03060203100806040501092105041a090312130e0c1210051215180d0e04091a0702071a0d05060d020a081509030a05030112050a0c0909021309 69
    0xf40c44030070f002c0903180340d40000120384841d0000f00301400034888901a10703820b041528140e406001c44890581e440c0418000d08800b050300c800da0003100c03481c00e45500340780514080401141c00c801c0c3d0000082034106105c4505591010701c66080000c1440741e08590310003035815808283e04c50b9030000c50320180d6660402c10007003500740c21542024540042c107012a80d1300758900d580203000b07402c4240c01c40c04644d10358102c6880050b001c0020194224002c4050740d80412124908051010000321a40700c0c1c07052490003401914030010001c00500007054a1545443e0020040c0a51030440d00c00c0c507400e070401071695410300c041005410100c4411860424040440160380180840409901d5840c0041001940d810007022196640070301005c0615030341d0900551140311b86800d4070070070200c91001580d04031010040b1003001d4203d03101c00f8210303400c0c40182c110200070310030300300e5180c4584a41440410350307000750103004021012000c94540d106205020b615100000b06003034103420040181c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 279284190 1250 279282940 279282959
    0x60e09160522060503120726030606130807030b01080d03050106050d0c09031a010303080705070308150105070b090f101103040609150f0b090903071205030601020a0b0a0204031704 79
    0x6240c034540803881184a04003840410042246610060b0702d03102e0101c42c1030b10140800d024144981c018510781d0ba104000c0e00d0650081017230403524604407041000000e095203401000f81410304040b182c2c0e150456202d5001502d403030170765042605c0b050500e900411001c1020080c10104007903500d02401254501880034101c1c1c000e5501d09580c103500d0743c1100d1841440f94003607100560b001501800b07820380481c11880480001e000a030001128003001442442c09401124201a4540d880440b280c1e95025030354a1a01d0080401d41040010800c941c081003c100d4034900911607800600911a10015010302d1f21140c115240d15032802c2201250f9000e00d44401d480d402504030401055012146c50b00c0c01400451484502049140c44541069060302d584103000008080e5288031081d00c9030a1000d83e02e01a64400a0903226885411a4860b00c01c0c0095904940180120303110070220350707261080c81c101121100d0400781c0c0400d040050003003501c200201180b0541305185014100240d12 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 279285440 1250 279284190 279284209
    0x120f02070512030c12040914100e040602120a0f05070c1a0a1b0806030d0e090a0905011d0a1707050d0c051501080606190605120a0e01060e091605 64
    0x78403803480b203020045000c00a00440d6180602c50302950980441c06a002c001d941040c001e550b5060704c0c2400444014201d0008180101c1005c083c8600291038002c070441c0400005000b1240c0ca034084c8180c000349030407203401c1809549906004100040000e4441c0b0032640020650010001c11a240f1804201501801a4459071000c20300c2c529507a102d0b03050b009825041288803801d0041c00081d041c166211840c580981c0f821410385100880c0a401202c400501c00701030745d40948250302144041006074802404903118000105000c005000106404404c1e680e0030026078100e07a80f141e08108558000000225076403201e241004042e840740e42c1d0303032460f032190300041c0b003c2c4469010074408208001000b00304004003c194640c3c407260900c2c0c0365076003980d0241c01900803128282c4401882064803054808a40d940d9003410810392200e0140306014120f40c541030754954007149034031b80c01c1c0101c0d40640548404625076041500032185448072040006036103c18005080c032441e65141c603003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 279286690 1250 279285440 279285449
    0x109140a0b2d031b071a04030c0302060a0209011407020d0b130203070e04050312101e05120a08090105070c090f14071e05030603010e0105160e19030303020f04030c0909120f0207 78
    0x14161500b240e441d05100d000790107060b03072090250550800c001c140d40000c0965006102f0703826140561103000e0714006038000d611655021840010f424100c0002e10000b8101035800205040c2e002901030315210451103080e128603a0603c47c480c0c441056041c00c00c980801011420402045898261981c94580c00384c065040d60200f582c802140e04094400d410001503c5110750110807844200c9c0c50b6148a4028071070176000b410208480360080801050f0b81030780302e4001905501c1c02803441c00454050b40212003c4400341c001502c041440050b500c030700101103004100025a00319031324a5130005000081201040207280801d14444025a0f0042010505542007442e00c0e500c410000138090501c1681002d010761034681004044400c01d242c00d03a51490640b100100580c1d20f4046c814450342c2c40039640321800301e01c101000000c0c482e03401401a501079065040c2016182d6542d481030a1440d4050340ca0503403034403840000d00450420b003048440d254108648045031600000e900c4803c04e10a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 279287940 1250 279286690 279286741
    0x6030f060605120121060e03030402010905061c0c0909090c030606360f020705060610110c06090d0804090b04050a0203061c02010905031204030501050f060109140a0b2d03 75
    0x200c07030032281c09400b245c1080e994001400d0100c0c101074200709035a030300103c03416400160746200000d15800d0007c2100d5080055226005460340e902880d1006072130101c1088041000200000440203050b00c80c0d424618402d07800d00b003400d86035050080c00e440c000e030007000000c45400c4d0108c91421021210a814100502001c804800c030b20000d613004000000c1c048140c94000180c04040000112700c2502c9000c040b95509440003205000316103124442d030503203085a101120940c102d1030160f02504424500030003c2c00040103568640344903410960000f0b2000f61111000742141c6080e028082e840705000c070085040d85000000961140c8601c00600256040c010856045d17900c10140300f00a0718024089485008800000ca2030943c4903210070741d030039480c0c00080384910009241082c01048169254800c1ca401c0c21800d10011032010006c5038000800c0d4800959011014042c000040e0b12015142c580b10302460000c8448485000304071000c00d0400070012840b4540851848116502c2d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 279289190 1250 279287940 279287969
    0x60f0d05071b0503120c030907050d0f120f081b03070c0c09050c04061416080a02011e24050a06030b150c010e15010303090603020a0302090a06030f0606051201 70
    0x3074256200300300542000c1c4100044600c8006000f0300000601c5c14245540030030300c1c0c40c1c0d80ca076812140e500041c0e5491003141c0007207004201501c1c02400f42e080e5903000340116480c100389a56800ac25041410710840840c082c64000400e06402070320556108811586024003e00c2c601c00e40c08844c4001004a81030003c4c0b15117420600040ca407821b40607052040003040346090909500e02d507600300b803040900048e4010380c6000402600c1c803d40b00c0d44201048c10306007070042582d85440b1600580021740440d90f84481d491f4503018000182c480c8062004000a803690a40034120000030f17001042d50031200d035a00c81005241c41c1c0c01d001d201260140c1c6800504102c130440082c1d6103031200c01c070404201d41d0121344003547d002d0640c4a000340300d81a0080b0740c61000c4004007102034031002d200241c0031130300c006400c22029003e03030014250045540380051034001442c0014880d5003281d0440000a641c0e0960405491058840c132009010581400c0c0d042c0001201c1402c0c1608050059255415055 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 279290440 1250 279289190 279289201
    0x6010906030c030b032b110303011403120720100206010b09040b030703050105101d04030503040c1e03020306100f17150a09121e0e01021e06010e0105060f0d05 70
    0x242e01c92030107014005d0a5409443c02810302509902c440c4600b50b01000d018a00f0f410440d0150082c0190b00c12000d02071740c150380c40c01c0b10050094240d00c142d1601030081441c0880a0060700000f45450351040081c01e41d001d04140c030b45841c2564848416004400901000c88140d400040c1d4904442242501c11340d80c1c0c1ea01400304001d0026030500c0d60305131050840200400006401c90b5101d0ba0303800035130b0000642c0d2034507190b04001c0700d620000040c0168601240110748920b008551060154502601466440196100039186104103807880044043d040c421890b0900015810401480304400d0790350812151000c0046584204442d140080039040c800707540c180003484c0d0344401300b0000c010700d20740600514060125a1021a403c80c3c42c1c00700500010700604501c800d581c0e0941c900811440401c4003030f0b03141039010543d01d05611800018061024020f108542e2480d01a8003514003549084e003c92000903041e00300510890042c001440041103902c20341d110881414000302c0c864645 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 279291690 1250 279290440 279290447
    0x1b0d0210020f0a06020c0d0306050d1115031806060406230a030611130803031612090507120501050109060602030a051c06030c06120507080112021809060103030f0806010906030c 78
    0x2e090002038900951a5860602c41d00d03030301408140040350103441c95800030b62000c0307003228420f01030301d54010028400b00d0085440c2c03200c0c05204000242079442220f00f02c0340300941c50f0304205d4103104840c110305649101080c0604c100c9400000070381e02404030f181071003900c1041c52000d5061060b00e43c1d81c0c00c11707074559513105c6071035500440e08064100a05c004414001e12943c1c000c8102200c02000860b000650040010489200300e6404034581d00c80558803500b03d41105004400402043d112008000491010b102e003d006240080c0500645182d07441c0c19400d580b01648000b4485181000800100790080704442600c03120b0303c0d080b60f07508900c48d0340d003a00341c40a03000c0c808004d290141c04000c004809a0050a8a840fa100c100003000450484010f9400480b1201e0008003c0340c0100410040c0541d8032840f103200038a1030004568001007a04c003600100d0324a0f036203522010040040c1908180b110704884c00c149050710841c039003000040c01c02d284c98814481055920002c03104079a10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 279292940 1250 279291690 279291703
    0x1e07050f0112020a0c03090f0b16240c0e030102030c0f0c0304030b040f20010c08090301091524140105030a18032a1a070c02090c0403051b0d021002 65
    0x10390b8811500da41c0e81800c000c001c00e031480002c60208810100100301c50301807008210032075071882155480c2011091200b10500ca24240031106011612096003d100d0031507100310050700d071340d0400034642541000003000d010602100070f010764410801e01c03c0b40c100d41401c4540040090190380c0d51071018050f40c41c50361145034005000e8144440600c020800750380c00c5580200c0c003d84c0c4140707a14040f0b11562490030310586050740441c810301e80c0784000981c032001502403c50002c000260b4009142c54003600e0291142ca800300c00350b66003501c0d60303031051461981d0401480c1100e40807000c508007800411440e40c03142100e410f200780880040c6550840c3c0e042241424444003c58a6003c03a618015050200041c46014810040080001c4414901c2c03c4400415048903c420f2034001e800000002203501600e504100003888540402685071551101e01400305023000507030319803950624500348024034a4407000c0c4000c980045010343d8900441d58510761f011503100740c190206150591030001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 279294190 1250 279292940 279292967
    0xc280306021602060d0608060709270f1d0f011107080c0705060a030c09050108070f03050a06051002160b1201150c02090a1d060717100810060501021e07050f01 70
    0x500045c0c42110f0700d10a400c6081144c2c0074904440b03550710b8101058807000000d0280101d040c24010280c2d801c0206000c04ad49405a034000004040c4058030b003420a070342d0500202c0c0301b2000392000c1c00c0d40140c0200040070f03501003c031000b0001c4c1c4120890b031a00078816103070b002e803410001240039100038609010b0b0b01c004110060045030343d084038a00180c00381c9804001c41d00401c103044400030340c55016142c602d11660703446d6612485621940b805500400c00603145034010b0743d40d2070000c1050784902c6600c2074040022340080442126011354841c000d03450760031003607000c0da0510244000b01c00822415041d500e254410b611076001c3c000044901d890f010f0b078041d501034036403014004001d00b1380e0302800c007a07000076403030740c0003071f01080c40b2595101019101d02c2c00191380b494804001c4c100400429070080da01d0110b50906036540c550040c900324080d5040308050303a4900b010400b96070100100c1d62680d240649550745030703c4070f0031615100e0a9900c20103000300c09841141c209c50381318600791040303034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 279295440 1250 279294190 279294199
    0x309050607080d140f06040605211006031406100e0c071401052505040315020304020114030103082104050d050c0c0603160311120412050f07050c280306021602 70
    0x400d0007500300c1c4c0d0202ca007a03c04040da0710711500800c200d402c06000300e0044c2d40c00507064603840d100c5604004102201400261018043c041a12903403403c107008420085026841403200840d81105082c2008005807101050000b054810824540111682030f8002000c207000360b260380007400c00403465a11000340c11840d520f04000c01a0101c146226010035180c044150410200c528505070b81ca40310350b02014040b00d08259117800321070721540040d44d0151040c5060090f5903551222440d442d00300b07030411103c8030800724604900c400701424411061022407980c1407581400e8980d140c4480000503140d0400070006086094040d0401c460f00030301c840a0003aa94a1a2080c0c00e90b00351052804170300006418020040d241c003041038103031202011000a04001c984460382c4050b43c000e5981c1521090040500c11503074000c9546c0c0161115600a1000e000b48520050801040016410105100810320404000b0400c161030501064a03441900103a545000d008100700c0c40100240083d0700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 279296690 1250 279295440 279295451
    0x307120f060f14071407030e0d0501020f0418051003151d0f010e060a0504032c101106070207080d03051b04030503040911210703110c01150e040309050607080d 70
    0xa160300f02050b207200d0001540c0d0050406000b06464841d4819000c0c080d00254407203140540c43d1601c0131070260440d1103900018a0417a219080b0402d50304554014510359110018509070590140241e0390f0250180880d04409411503032000450005103801120081c1d554070700b003500c02c0350742603010751000c20348044800f200c0050506030701819202030540b52601400000c00c0080b82e0034044c05000d142c3c0341e210340c035513401e8440807a000029140040c0980504404020182e5210011800840440c0d9500d201400d81140003d80c6405805000d503070455001040822020780045030700318044c4443e15021804c1e885185041c0c05220302c00c0c0d002c0c400c5081c00a000010402c001008cc0126254130b14180080c2041d0409840103009906164021881001121003048007051205602c441d10f42000900c03000c1030401c0d4a40c0360004180b01c011695100901107c500c3c884034900001e04040301c0d04003c5281580e0010050f001504c10035010311000320f030f20000c002c05902500c2000c00c0743e1108002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 279297940 1250 279296690 279296711
    0x606050a1e0b090913030306050405071e09050f041a15040305070905040c050907020a0c180f020f070b09070312021b120a020609040902061c05060307120f060f 70
    0x4902920080038110103040c801c00100c40440b10141d91024030014860191552090303100c1081c60a044003c42c2011b60b108800304465555114081c040e0b14195144058414401d289045222400d9030b4103091000d10401044695109030721640054820388021030743c090500c40e16101c02036407000c40d075407000114240101458440028004680c0542c00716000142d07201c940900320384017590003a04401880c141440b4500f080404a6004805441191801b9406031074400598000b80c0100c13000700081d510f00040c400143c0605140c000c109c2c4821468982d45009960306e9100d0307034400421039144400000c200100038481040215088510b0074124a807040d002511081101c5281000c0041605140c0f150306100030410380316203802c4c00030079502c1195005c1119540000d04620341c41501d54020100580710180900583c0070b5090b81d490620313091000e54000d91318001d150502a85c400201080342c812a10f0400880a400c600c0500c0c01100508101d0007910143c0401c0b480079050000060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 279299190 1250 279297940 279297959
    0x21e070b06030c0907090b031009020d0e060601090b1b0c100e0301051303020d18080706020102090405010608060306150103110a0c020a0603110d05130506270304061b0606050a 77
    0x91180707800301c0c251444000c07800c0400c44403803c2039030007a001500c804030034007215140324011901300c0c1ca0400c1d01d4890365a24841c61069a00c042c0c03c4030b030596121016801c0c80740c020000c403034001c282428201d030780c98245007103030b1120f02074111150745502d440452560303261802e00a00c05441c501500170020000b070b804e0085e00845405030b049000b580b0302030016011910701042400340d642c1c9540503000d070300c0261100310398400b1121892036541030848000a001141040303054000c2c406600056110042c00080104485059103c1e03010b0045400070400903903408180c0c06d900140141d01d011501c1031071001217008004900a0300750100b40000d01ca988140c0044c03003401603074802c81d0040c18007034030b0300c504509460920045101741c01d01489040c1c0d41c0e0b111500410743c420303014052900321400c40c0c0c482070328200094a5021101d03030450200b0700d80c11036110440e540d1244040c015031405203040c100920308030042c0144c40c110441c3d00002810800715410200041800138001c1212584030072541 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 279300440 1250 279299190 279299213
    0x8160609140f0316030f09050a060306060201050903090109060c030201090c3002100c150603030801060f0908030f0315030d021c090f051212030903032e09021e07 71
    0x341540b00e0b40c141c00c1e50000d000012500524616002c3c041400c1942d6002e45840000a050409001485102081d151111409a4000e00b110340e804a103040c900100a03084410142c007400407508100f00303480d500e903004464101114640d00c1c10300c1c9208102c0c01c0882c01010b64102c010000c405240d4001030030100c0d0100802d600051400c0f003000400e10f208880f004019041e0000d42003840d203004000420702420382d11441c14050501c0c40e03020211a9070b01800c441c41e50f0000c4000c40e40040062055036441052401c5080090074403002c0c8a00341074001daa2401481c402c6c1c6a42c10703001000503960b2051590802c240140070b0110307101c40d88076442c080e44a14448414041d41104a1800e20300b103403107a540070084402d143d0fa07d0341c940e810181440007003d2040c034003020030711400140c03003190a14000194071881e0304034040e40d200e0605401c911a0981141c0002d00d00e21810301d2550500d5014210704d901311824034000683c2c600180301c583d40343c114500c400b8403014402041c1c03c3c052042d2407060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 279301690 1250 279300440 279300473
    0xf09041502180907050307080c0d0b0909071e060c11060d0e0a1203020f040e04050309090702060103020907031407030b28050405010509010617070c0b0414010e1908160609 75
    0x607030403e9a60b102044809001c00c0b500c140018104002003031484400e40020124030b92050300c0861700c1c1ca1400c0c0802c006610a07580310844c6c0c0e006c00001c2100d80700000603094009501c1005001d02c6141030802480000388013000f400d000c1c1070a601000d55a1041c00300c0d15200c100100500401103104016516282500c90035502c10b1103101c0840075140c803034400c030380020410552142c01c0c01d080c8000203030a85801003040340d0522040111a5a5030382d00c02d4600e203d40303419070040c6199030442c41403203146240034041c902410300304003504510042042c140740e0b10501526001420008040010302c01e083c1c2c0c80305041c1401c079000f0703c1000460103c01c40101380c0f141944d0510250743d0316028000b440030f0074850840000c40b0702400540748060a60059000582803a000c20b841d0501c2d00c421011540a072001c03950941d200b606074082030030031b02801d148142e801001d015504109140081c07100a01d01c0020440700340021a0700d458410141c0c0c81c07051903004101004090a50301d0401c1c1460b148410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 279302940 1250 279301690 279301699
    0x70810060203040b040905100308040e07021902010c02042c010209030111070302190c08030d06061e08010501120608030d020702011202071709040f0509011a0f0f0904150218 76
    0x280861640c0c0008111421a201000182d02e407038036140300c030745c000c1c000600b1a40c42c82c280804000701252841d40a84003a0901381c1d07000c140e46c00d201d44043c0ca800310014948500c241c2501c00340001d43e030408241c0461a4040d03801003080300c554488040c0010806420b000d90107240d1b020300d411100154081c0c008450f054000b0400f0411702112010307240071300d210003001a80a044a0700510b40208913408580c1e1042c859403282540301d0800c5401c0d0f41022000342c1b00650703509c10410110b075002c12208244085041d0980042e12041002000b69005008080c1800018500184c03140403941c41f030340c01440c0d642c080ea52162000300d0304201a5000f12030903400200d1540010207071030958400c450300c00d527114421036503409009148040703035044503005c03560060799004d420308542058000c541c40740b0441800042c5400703041a02c43d03c861490b46416000b074001d6962a840d030340340e24043c03944000088485003044e9540e4508011407419401c200146c0350b001082c0030340e06802005640b8445030f0202c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 279304190 1250 279302940 279302971
    0x190f0512060d02130f0c110319020f030a121d0709020a0215010305010e120c06010e06010e0409240606090b0d0e07030c08120f0304021002030405031f05060d200d02090708 75
    0x20706c11610b0000b00145a030081d04100400d190940246403100c3c1c2060280c010f88501c1440c034025181585c104095800100701d150070120038500d00c900c104c202200180000d01d904141c1c00070140e80d503c4041c01803e14282d40040c4403181703640200082e40d0300440c6401103296640e10791410b00e02034040b054089025108000c200c01845034070705c01f5101da42d032400f0001c00c616860024440c0c8130307041c041c000c60f044c400201e50329805a200ca000d440d01c02030044400000c80000c2d1500c900890884030003407068603151a90600445e64000600700071a580328074810b881e141c0c3d09080360001c2c92484402e410714840d4007000400c0001a581c030000311504682038980c2c044041d0920740c1e55111b812040d25080c90108005001846c2c5901114100c440c10300c11642480d0312000480d00d0452816070020f08280000070340512100d50707005143d4000c0059402983c00b04556450201a283e07040e44051a40d242a05e40324054680c1c100d81e4a40075001001501c02d07060000c1d02428040050f80d0480326103030201e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 279305440 1250 279304190 279304211
    0x171b040902091303050708070b060f0a060c02042304050703121e050a020106080624030f0a02090c1207050c060702120f0d02040b03010b190f0512060d02130f 69
    0x610844280540107082442e03280c0c2d404071145042103508004400b8400e0510044001c42d0000e8040c045841c440c0c50b10003180d05145d8100700b0001d181000382440350a080b1010b2101e107a100c92030890300e940c10b070b5003c01e801c40300c2400b92401450001c03021500c00f00c4070080006000300081c0358000c4902640c1403c24252485500300c1e044c96414a541c48800d0701140d40203201072103100201000e1006100001d111500e5104141c2414000e9404101a00045040030401c404095100d10020000c03070040c00303400d101480041d15041d000002030b1003a030203100025940c0e0381340d074200e641c03000c8200789203945450821000b40c2280c1114101e01183c3c8109030001d4901e5000088070021100c00e07031001c50031f116514001e201c0c55807048102110140d02070100082c4204050040d501070801c1c240c8c05a2102c0d207040e0401c2840a00750744400030407005c00500880150840c040703803000300c100c2c000200340ba9158000704400c14401d50b8000e400c5104803a0045201d0110f51060b0040c0e040c42d82c0c28031100450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 279306690 1250 279305440 279305449
    0xa05090d05150f0121020303090d03030b01020c030f0d030c09150309140607080118090b0108030306090c0f03010504090c050310050a050a061a0705070807080d350402040204171b 78
    0x90190481c1c6200d50410350984080030704a017404603100030f04a0f460035040d4070100b0348015030303000c044020a440b14000c42035582c042c0200220454250b006044440c4040200c5030340c0c9100f05011414991707200c003035115031407140c108031002d40800030442c020004081d030f00034010b002c00c48003034a01c0d03011388030824180c50020603001e01a040c030740e5440b1402d0342810840000c1e40f58150181c1c0f0406c3c3e588200348000380910164500030070303205024503102d24001c1c05011040d81d0040c0900000d501c104040c102182c0d181d81580d055800640300050b005410380303058110002d02d07802090381071113802134000c1c4034405608040d01c16400902c082c40580c8030b9002500039a686401448411f030101100941c80301031046c0506000350150046903a0141ea8800c0c2c030f41003100c0c90308100750941040710b488064a400007080007400b14005202c0b18401e6032407500620b00380a0440b800303000210f8402082c00d540c2c1e260156005401c19024604048821400640c0d860021020081104807c0c010803510fa180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 279307940 1250 279306690 279306721
    0xf0b040507080c060a050a4a03011b1b060f020304030306050418060b060d06080f0d080f040b04030e0307090204060207080705090619030614041103061b0a05090d0515 73
    0x31031b91034003400c0045214041e24041d01c0d0540c942c640b0010247d4010060715041c1c1a40d916100c0804084051403181c00000700c0c0c8220340382468003036070400791301c1d00301c2c40e41400c812050310041d441c011208502504000c100c2040340500a01250b080100c171a003002c06550045000d68841d860030042240c0d504280003d807080c12922041c0402c1d140300e10800b2620359007125540c080020140d51808c801c3d1809403003107408980090320154000316075002c1c0600100f00d8148002242d00700000b062400c0680c46000b00c10090000b0250b042030004181098004c0a00d21640b101c01402d6824031911081d80718025003107841a03100511803000c001139842c0e0082030410586001419040d10350f981c2c00c00f0320940c00203038040d110101e200c0140010204045100c0c0014a040c40c0350b01c18114106402c02c0398241d00c1c0303500c41902c40d800002c00c0c401c2c940445400425010600720a85840d40f050035001e48642c010a001d07030b074020b00b550f040c0c5420071601150402c0c1c404000e4440341c602d40c0311041d0940340041c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 279309190 1250 279307940 279307957
    0x13c120c080c071b08010603020a0902030f0106111c050c24040201110316060b0a090203090619060503070e0109050705040b250f060b0405150306040f0f0b040507080c06 74
    0x60052001c00d0009040c036005282940c05004024104c0c4441148090709185035802290140d5542c071341401145010329181d40100987c1030250709500301088103408102c0c0620401c0d090007143c0f180c22044050a000da80360f001c0501d40111504104040301034070070762191081044da0b020390140c0040580403941340001d4845150454406a6115401929042d0150362048c68912041c052031052440d40c0003440080c41c400ca50125115074181c1c00c0c40f18030150754118040950050080000e02c0900080312a804002921028010300019541a00034600c9400140e054001e200c8013080c0100d0440115040302c604401c00c210560b144101100d150003540903400900208010200c088070084245011541c3c1801e4218010421a515800b00c1318021004860079619841c4a00413803406200c0c2da035008140a1030b000354030080c400020345070700c002480140200300c04513a510501108040c540e02440c1d1140c042c1126040038200569620303801c0c4070703044461286925080d01c0c0d06200c016903c400303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 279310440 1250 279309190 279309197
    0xb04090506010b031e10030203010f0504020315041b030f020a0602010c080703020c0114040f0209010f05010903080f04120c1a070f0602031b0406032003090a02013c120c 74
    0x1d90030310714040100c1c4e01c0034141c030311002d60341c8001052000c60903040318098806654000d00341885c5106160030b45040d030440e201501e01c0d010811001d601c010070348007501d8101030808055a5140e280841007000c1c0021001c1c0000e0b00d00070302004028204003d80280c5000300c0b1000300b45a51500100c4c00d803412103001d103000810040219103114001e40150449543c848008604040102080d8000c403504403001d460030503c541c0c2000540c2884030343d9902409404108450340c03030030b00002808180d85440000c0c040080064200000da84042c180c030050001d07103101150340300c078609004140c0034490007004c00c00c11004805224000d80d1104036604654400c0840138490a6500c030740b402074000030840b881411850319501d408030b00c62402030026100703a4030f00040c20a0140301c011b80e05000d0141c41151000c0c100f0603c100131800140740078116909180840da59888410400f0141250a508000c2c480b9800241446515000b8031258203110b00e0b5520f0b144011440c00950940d0665003142011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 279311690 1250 279310440 279310453
    0x1a06040e04050c041802090f0601020d05070201090b030106230a02190321021305040213090b060f13030210020a020a0e0c0c1b01030b151c0b1c060b040905 68
    0x9864640c00081c0d2140c050400c2c2c1c3c103001a0000441c0994207003e100c0741034400b05001d114118500362a100c0d4000000070071174503003450080c0010750b81d403070124401000c0c448081215011a881048180041d040880c03100341c595948020180008a081c80a1401c581030019600561411242034a900c0100c44d8018a0340d4803ca000d454405c12007610140c080080c500c840d106c0075564a5189054000c1d0240c0c0140da4080804074030312107442030341205224900400050045004e0710801c0c1003a03950a88001581c1808100010032034407444e49689055500442d204041c100800921402c42e802038516040c050001d007c103d07121084040000c0d44510584014040083c1c540360b03841d80580b4210303141d89080d40b64240ca40c0b810f540403100410188030040d101029580c54061040e0120007a202030030810940900c0c2006030040e40800d04200e810f500d40e03131510700e03181d40140c01c141101602058541001d481d80c28507070342e6001826110f1500f005040200d504240c810307907a807150000040e246 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 279312940 1250 279311690 279311699
    0xa05070b160827040605060909100e07020d020106090c2c030102070b2220010201110414010e0931060507110d050f0a0c06090503030a0c031a0604 64
    0x155082820400d400d01400344a0000040b400001400c5186a0510f464900a0085440198058040403150207a800e25000f0407031030b00c68205a80348088100c030a81030b40e80e90300703210881c00c4940f640418071181103a414005900d0700412103440c1e0108503070003440030316114180c040540b4407104000d000504400c810f00d43d048403141c01091a02007540c00a0408801080080d003680c0003103005440304844101480404088080603a4113a0810b0301c80c00c8414a02e529903003c9030035400074001c080c04195280f804941c1c401c0d070007024900e10f4881d21549032134a5200e10740f042c104008440740480d00c084861407503032411010081c03054102c85010b000c030300c58180e120580000411113144290320004480000100c40d8050f85110ba044c81d6509600c415501c4e03141403411b40005a0300317092010800880c0c51280c1241c08480250046041900d00c05071035244c200000c180011018103030740004018403076220111342150885c46010340d4107000e4601301c1400040e1069481c0d0440341c1c041010481000f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 279314190 1250 279312940 279312959
    0x501050412020103060b0f25051504140601030803040b100f0515071514070c0b07110a0c0602070f0f05030303071b050105010806040218090703021903050f0c0a080a0507 74
    0x1051403040c134002c20441c4c0d4980308181d8682008000d020541c07030100b42c0031511107070128001c401e0480a06103c00d954016192a901d608010190070020f84100300010103018a40160078a8401e241003240c0156942c1d0038040110f400940301101e0341d60100002c6000c031000c0f840c4441c2030b203c440039607260883c82c000400078036840d030810840880c24103101003408204043c0c480103050002d854081500026a49000b0490b000105040c09002c1d40c0051800441c01149625600c54500d0810680f007920401c0107030316000b0600c2c00100b8081403940c0100d00350758041000c008072014001009070864403000c038040c0d098528000e0542541c01880020b0600f0721820310150410038200000c1a4512a5100c041c25204240c00a60141e442a0284411400d100d11445541c1c20807ca5104503404c045102070341b9260541300c0039100e1809142281c07214040320508800450340141250701c0e80e80d044c02c4060b15688114250303445000c070703140005100324000c144e040007560310001400c030302c906110503035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 279315440 1250 279314190 279314219
    0x160305070201060e04150b0105120f070915020c0907110619060305070e0106081b0d0c0e030a0c05120f1002070804150810050f0d060f021603051c050105010504 70
    0x8030210740d02c07060300103a8402507205182c0140d014100101d1782a6241080c4015550f030401c0950401008020140860707418081c080e42220204000c1d03c510b0312000c104441485807500280c9440040000d00e5001e9a00050450b21048065981540a0f81c40206c141c2d5a9180710480c900f05400c0000003402101220100710104446100001427032070312a01ca461500c0d4075500324001d0740e2000401880595000290103521070204044078105198030600c007440f40c0100f024079641d082d200c081d02240b40c2e0040d030341100949005021200c40b54035a007404040c0c04210710030300b805a45440c101240d0400c02003100c403080c0310f0a400510928110f52070b460001e50101e034040e10740c1d04062101283d207011156592401ca17096948202060074215203030704041a00390310880c441d21980b50010034540314181c028000c42c1e00203900007640041c2240042c068494003403983d0701c8043d4012800109038101e005480b8031240c00d030003c06c5081d8101400c03400c407482805900d0200e08184010403000d564007001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 279316546 1106 279315440 279315451
    0x709050901110711030c2d040209030c09070908030409061502010b01080a090807020303040617090303060d0b0a15080303010515030f060d02030f030a0807030501060305160305 77
    0x100405203e4254028250003019480b191603940a014031040c1940c050404540c02d17203800440c04040701c132001c41446000c80520810038500f040d2080d01c400200c058020044001c100c1d003041708034100100340c10204401c103c00400c101d4010f1014200600d81c4440c041001820aa01c0c1c0c4450707541d0758000011a890300c2e2550001e60380c0890800c2d0400e01816001031030036100e04090002d4403c0d000061b416100005001410951014180241856031503d00c05c2c1500c2c2c004d2180e441c1e02c81601d110740d1020236003840d18041003c18401a0300129103640006064200d505017010b45041640824070710f0300048010401801d10390866000500c250449034036500c0d240d500400c070b446001c0c103018013030003030b1644032802c40d24100444140020340c0d070304894850005000003400ca400454031040068108400010644d00034098103004000070505030303d84a400b850200e0041c50300405 = true := by decide +kernel

theorem cover : BRFrame.Cov 279136690 279316546 := by
  have h0 := BRFrame.cov_init 279136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 279136690 ≤ n) (h2 : n < 279316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
