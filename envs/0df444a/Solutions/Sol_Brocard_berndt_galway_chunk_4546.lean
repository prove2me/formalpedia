-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4546
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:58:17.878849+00:00
-- url     : https://prove2.me/submissions/e82d7314-02aa-4dc7-885e-9ee6a5efc0ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 817446043 ≤ n < 817625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 817447293 1250 817446043 817446053
    0x6030f031806080130060c02030c0c09090d1b05060406051e1909020d0803090d17010e010302090703020c1606022e090314041e090b330304 61
    0x401498500d00d9404560000c40c00502c02c215050490300c0c41000c082d02c0035151211040041c40101034410101460300c12503006c40c0c42c0d80a80100942d158000c2c5590f204c40c401c102e03040c21441d1180d0303402160020148009282c0000f00013012041034505030107100c1d03015441030000340680354060328602c91081440203222569001e50300034107851000c0c02113240d0752240b01c62040c004554202150043c07245450090850360415003c80707100070000007007200c1030740e1184615002a504c0e162603078810701c05c041600e40c202082110355209117951092940c5040b00c8081010740c1400f000780145131850104210314001d4040d9211b0403400000c0e1590004c2118100002190034480d820040c420313941d1000c90035140810140481120521640c03088021881050182406050413810045001d0070b07040000880c0e00a0005880e80c4800a02081e65a013100d1604005c1500b00d0000f84c0d00d4004a00d400d651400d50b076002c1403160445040134840c011002c0d426440442d100c80d20300000010400c02002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 817448543 1250 817447293 817447307
    0x7030f150908031602010e060103170f03010f170708070b160b0708041104060608041106070804060c020a0501090b12090f01060b0918040f2a06030902030606040c0e0402070606030f03 80
    0x40130034410003100303d40718004030700307036602c40381c076034036590002c20041c000b1404a80300703590a003201804940c60a0964000d9085030340c001d074840203041c040307110203000030300242d0011549411610014804a81001080d41d01c40c0054401c041d14002c0019140300030b800d001c40c141c40c20303d400c680316900520708031a000e000004210340464265442e24080007651903e88034603402d50302c0e1a501c03401d0710b9440d599940c2540000c83c05080d4080000d104076000140154000c101910541d13403481c5290202d841800703000340c0f039900305505000ca115801d00900580d08180c0f19600c0b84000b280d15162290190642043c1c1d181c0d200851079400e0031004a004003ca1008214142c1d09481c0e0f440004001c0d48801070b04203060700c000b41349403849981341001ca642584d84002040c2c458002d281000c0456100280100035540a07030f011a0f203840c55374082d841c003031050a51000003a1014440040500c0008108100c0c5100340751055501054040a0114903840200074584c0102d90704003900c02414090300b12 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 817449793 1250 817448543 817448551
    0x408030a15150e041d100515030304061e02010507050d05100503060c04030c0f05010e06180306040b0a05091513050102070c0306050612070311120c0d06060602010b060c07030f15090803 81
    0x66045c80f4a100c60705141d101010003421008019150340501050307601c000e0107000c2d088022800a940340c410f41682c0030b000400044c8815280e10642e02000c510b64201410403205110a5900d800c080200d034581003421549104001c1400080550381c110800c885071510360800381d0184520400c00039041c502e000107000384c0340240d102d800080d6581e186201c904405004240c0014000c142d41c200a09059019001b04112035141404010058010a01d03140c4210780c16600c0b40d81010034009060543d00c205904025082d0181480c204100221145941c018029000c91a42060b080060003029410b441c1072641c00b90403400002d64a0404502a220543e242445021003400d0b40d4201000041c3c840200c80d441802200c2d40354841c010001ca8006e11074008119015000c1030b00071507a601e0074114001885054002885410520000c9c01c403600701c10414010f1a04110740110f0440004680e4112507018035080d5a0201501d0130740c00704da10202450b640c1d01d0500d4080c408011400d000344d442 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 817451043 1250 817449793 817449799
    0x91f0e10060f0504020a14070c140d051c03060305060906041101080f0f0c04051f0f0c0b13051f02040e0a0203060108151c0302011d03030408030a15150e 67
    0x21a1444030090003201c0e0184a07408400007039540030880c608042c1c000d0a5110641e00746030700c0d01f0171081128205a07003c0e810842d8292040702e42442243c0d118035418603000c1066a04840c4c41d25030341d4419a40d2008103814212940d5261a045081c0d48030b504a00007541c0d001e002d0319942c0c14815180f5680d074100340d80460390040600c0c20b00ba4154030a4100c0d0b4410800075035a00110f490724101000c18030700140144440702c0b010007000c80e894480744440e850b00d00b50300301d40713507080903002c10010301ca40440d040200810070114001c0c40480d48070b0b80001c0e0031034082e11403804082030902c4d02900d040f03551115001c43d0b001c02407100c048031007550b01801c00c44d840c40300e101c03100340e80740303090b010407440700311615808118600c01040c101c50411052034446c2c500600306950701491501d042c800100b02900c12030050391508078581041d00000c050341c0e1810a848001e500b14141a6504229808020101420959140c54035000f624203d0a050000d180411001c8a00d4040c150020041c8841d0403005d40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 817452293 1250 817451043 817451053
    0xb030a05070810150b090a0e09060a1a0d0813120c1703040f03110a030c0b040f0e010614031e01030f120f02030d020904060e010b03160203030c030708091f0e 69
    0x1010b08840d00410928001800b24215842e003000700b4007131141c06c02801150041e040c1c06000c0f404030820b080c990b00820501000304142d24081a0010568480110100e072030822800300d00700c00e460300c41502c0c0c4007a5208011989840c0e414234103e00703103000b66105003109807511058030244007400440e0029180800030001d80100311362003c5540e8400e9110304000c1c800095800c0010684007840107904800080410700000c1d62790303ca9400030300494000b1254600002010840c0c1800c0d2100c00c0c00502c2806941201585810b80140041c0500c01c1d0b041d01c0300d40c000000a6511288190108054103040c0c409846541c5a00b00386c1d083d0060004102c0b1003041c00305c0201d40342c0340180e1610601202d594011440c1c4080021000301a40040c0d080541240d1070321b001088900c01c003003100e07000c0c00c1c40380340700c3d034403854440c240e03841110100f03c01005540040080c400c1030f840800c220381d03000d040c0f42000f054039103030143c14a19000380c0c44d010014415881100084c0300c640fa4001039036040c480403c441c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 817453543 1250 817452293 817452313
    0xd0512120a090506131b09021b0c03100209030a14060a0b0d0b0714040909080705121314062502040506030c031b011116061202030c0a120b030a050708 66
    0x150884149400c0606141e001308009040048010920000c8512400000104158a841203041c2003600e81007401080d0300410b5100c0c01113545540b034407000030000018281c0c03485a001003074655075620200d504041e0001404052510104880041e0643c000440c401c11600104d100b5111340d0b0070f0700e1400b95142043d504541600c7c2203081e401140350803404100981c0c1340c100c41076a0845c81d804580822882c14000050b0300e0351248a0f60a950b07008030001592030005107041030a148088603c813900f5a42802058480020610b01400391030024410301c03414002c0000003042030081d0b17120895200c01a0100106a5021250100f92144260b8081c0015200e160402d621a16800e11285d010390000088403070b400c0c01401c0034070300c1c5032040c1045c00980384400f10301420100c074126220402c44100100300220744d4401d1420030311030340ca00b40c21400c5080a1f19881c8852082030302683c10060304910344c0348000032551001484041c0202100c02400b4546400703600d0b4907030351250140c0360060340414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 817454793 1250 817453543 817453561
    0x30908030c010f060b0403050d0e1201090809130c080c070303090c061206080303160324031a0105032b0210020d090b01170715021002040b1206030a0309050f0d051212 73
    0x1c2e50503654820b01909e4680113040d01100d140900011040d0300c101d42d4094109248000e12550540501401d601561580c01e141803000c171807038120354415070303519020351042055404143c1540004100c200d2698800b580d0400300c018142408c0090702c00f46401c400001e120f5044076908103410941c541c207120705a9901305d00c0352240421180141841d5442d1400032010b0b00c01d60210301c0111003888080d883d4181615507400d4103000b40c000b20754843d100e248007024003030404207035401404c003180200900203101d90540565682d03800115501070041c5800ca10a83c0240900043c50040010454440e81c21204200140000c44400d44521644100200719000c45250b2100d59210b048014516246030800b00155003441c07002002c114001d110801e50400641d0000308010020300c003409865002050781600c5903e400742080c0c3c4264060040b0342c0020b80c2050340e040c00c80d82c0849603014030440c1d61000c9440ea43d0924030041a5008040c4904800034002d070181041900d22070f003a000e0755443c4500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 817456043 1250 817454793 817454797
    0x2100b01050906280503060102160b12071b0302011a040b0604300606030210180618120605070e2d060d051015091a07030908030c010f060b 61
    0x82a0005504100b40c1200e400c01d2002010111907540c9007614042d0315030200043c0f0303101c1c03194a00001e070300042800095030381004030641d40d600401400510f03a1070201032070130702d11a400405c8540c500e15400104103034021303c0003103041554440110301c02069490002d0003071500311408801c080290480068605140c42144030b481e40c064003580c549801d0403c001050465100c7c1d2000e0707100000c0c010850b108408801d030b0b2450303100d40030108600f421071041000301202800b1600400082405003403103040e400c500c003401c990301824884268101c00800c8181c04d0f03002e40100b1402c2e0400b07519242041110741c40b0910444190791743c002c0c0c0c5d260319400c000d00f180f164051003a9440f181c0e0301d0703044c000e890b201c00b100c04840010242443d05d211040d61078240c2d0300441e60100041d007404403c003d04844a000443c0700742080c54080041c87c00c0c0020000700390b513281c44680c09090040307010717801c01d800744d1020300203000c0c2c42007203035140c2403e404864082c0141808030b90119082080000d011508282 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 817457293 1250 817456043 817456061
    0xf1b0915050d0e1903050c0d2d14041d01050102031c24081b0306070507060504021915091a0a03020a0e0a140414090606360103030210 59
    0x1036958034003800507844101501c0c02018240c400d0003030002803140300304d5824840540074401c1d19080c2c3c68180d51000e40b820003001c0447d400074400300680005804041c801010700350980b8046808161005400c00c4070f2003808402c41e41200c41001402241c480c125031030407400c0380034100d030010a50ba2600c0c01280c80b0b02800c1000c10501e600041e65500c00701840d08007400c0c00307080c01e014113110130f40c4401e1226807105130741c8400e18a800028410301e50b240120800942c00c4c0068000b040b150500f43c4008040384140c400c090f001554501c081000c55031401140307801a818801040503050311100c601d298202040ca000307001c2024108001908032144420204407540d58003c10b0518140d440140c1c040c1d480071081c501081f06d40f02c0700103001e41d51510a00301500003400303a0301404030104180800c60310040c0c141202c52205100300242c80400145043d8081130940785000d1495903880c0c486d4007910090f100281224201800084d00d401c601003250480780283d08031060211104202421989844 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 817458543 1250 817457293 817457297
    0x50d11040b1206240a0e0301060306140907050918070b030705030618040312020a05130b040519052119030c020a0e0708060f0a050607081b03131203030f1b0915 70
    0x40c4d140711a400356400b6000b000b102e81000c0a600541c3e01c0000d0843c0d2058100301c1d0000c4e80c074482c40010341c9540c03c00e0396102000c03c2c02032a00703900780341c005a80140000e24500c20b0104c0000c24051241052000000514603044034648030f0800c40000f4200342c00480d001da00480d004a4a9201041d42109443c0210740503224900c000114840d01c10296200030030207014010204040d1079210423180340c21000380011072103d51143c2c00c1004004038650b03205180e83ca450850107003402942c0c2d41e1f5100da40030a400712900c11480344050409070600f0f80040009074407942d8002c620041c50b821900c50795141d072085415096064031902840d401d4a401c0d181c0000049015000030303c503040480d65240304000082802c44205c1d40c0d032000460030380c08480c1c12202c82001041c1c100c02c9010700c0f20602c0300290208061070629540c0c102041040d8090300c20501d180308246460780500d0b00030307440000c0312100e0300706c01d0022a403100010713000446414140c1c00018000400051050039091440039640d0303613a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 817459793 1250 817458543 817458589
    0x1d250f2607060e1c0203031308070503010c1e0c0c0f05040f050c0315130c20070e0a090219030b04050c030f07260d08010305191101050d11040b1206 65
    0x80804d102c1115003400b0441c81141c41980c0300c001503903040001d0001c2c1c8461505004602d03062070700d090309140741580054001e078105014891220380198088484200240e5940c2003c0c2203120304581103002c2c4040a4004030044c04080343c04d40c406140e040c262902540c042c00484980280c130700450303004440d5400c60810a002180010000c0d000e8410241c030002e00c441c021106040c000d10480d00d10505000200d000070760481080e00000d45140c070039405c1c04001c0c201e56482c081440000500007001d00c075019546014080443d52440c100114030035030f0b070a01906264583c9019042c812040c0d0b010341342803182c40005012032500181002c0748402c1c150146c4040c07440e02a00c40d81040d01c42d000000d1100c400c00c000c0000b040200f10040c04901d081c0d032006110751550401c072342412140207403441c543c2059101d80f800304480c01d480c144242e0b400c1c6000c60f55800c0e030001e003100a002489910f02ca40000240020309403c450015009c4400e9220500c101c0b9200c6400b0403d080011b4950300301e030100c0c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 817461043 1250 817459793 817459817
    0x40923010519180f02030a020a0905030d0203030711120d0207021c050d0e0117070c030906020102121b072a05040b0d0f03050d050c030a1d250f260706 66
    0x240c2c004141c0102403c55010a6811004d031442050341c00c11100c1d1808542e0105107400741d203078418607101c02000284c002d4888840c081d00e0003074481c4030040c640401d00c11003454040030b5131303410841542042626019030742c031031980c5407054010707502c101802d0b031007040004090042040d00e103803200e0f5025442001011201003130704003030380c243d458068001e050204402d141e1031071076a45020244a1980c45c0d542010b8a43c0030f18024050301b445402134021607105020202100945c05103898108242d0099101084100211003900344100380c03004001c8816403507880c40302104081581c400a0902e85007a03e000d49071000d01080350000d010341e660080301303076040501140c0c200a02a210314040e2801034604010b00380c07039800340d0340305540c04481c03540000100b00c403038080380c400c8c089900c50b0501001c1d00740e4030305110680e42d211000e04105c1d449079a0100c5a02d04c200c1c450260004000c445100d032500c0780d446110450b0b030303040607529203035244550398406800100850b0391019242c0d0313612003211700c8072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 817462293 1250 817461043 817461059
    0xd020c0111010222030204050c190305040c120b010e18250f03030e0f060304321510090203070f0c0611070b060f040c020c01110102040923010519 64
    0x4140107030401d981d5420805144220004807111000341003908940c90f0461840c8180001c4130030040c286c010303d500a200e01214628602c0948010300d20074074000c1190b440e1410445d82075441544041c2440f01c0740350640b41084410240305048030710401168480d9500c601c5948034010710071145184982158003003100140c803a1840d02d1038820300304010358450341c84262019143c04241c005401062030220424020b140098184600c9802500c005e81141001e64600c407807920507483d03600e000300c000049400c2058200c010300440f61902021101d00b20b260840c41581d8010a8a59540000b5954000f05102c4d0042c02268041c150700e40d920781d0b02d02d4201e41c08540c00040840120358964546201004224801010341070003801040c4496660070321070100490020308214a6000380c1c108540f41c4252900401c0d141c400c4482801c0600b02e4401e424000350080c07185811982c00e0516080307a03900c103c4c0d09a00c4d800f55544071032000051603600c82c02005280c24410103001c0f0300b01003404043c00500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 817463543 1250 817462293 817462307
    0x10621120801350708060a11070f08070609020a0f0e090303040c0b0a1b0b060f1005030a0b0a120f0210031e09020d060515030c0114030c0c210a0806030d020c01 70
    0x4549954040d83d0503621407031950501030700394020748045c0c0c00103061101c01400c07441640a004891200580340820070355460f998102309100203030505002007292001e119560304074006107a030050440034100d4464910380c6401d40c682c01a00032034003240c0c0000700013140c00002c07280155040700c81c1d42e860360307d482d62007070032580204410003c204500d08a008296802c2800b0000913200780e0451100345407210510450b158600c483c9da01c180400c1d1184600660000f0403a500b005d4510b0b00030650480342c101007410b1750782c140d000e1120010144140b5090002407507a440340da83c404c41320041744881c0e03a182202507805100b0303000b503810110b01044418203019401a103849201906030001c41d0601d403501d104807070b0121445190b8080c03c42c0d01c1401c41c981440b542e10056401d0070840c51a905442404590340001012004200030000e0388005102d001c00404121a00c40c03480042c8035509500c00f8030382d9401009220f00854020030214589103004110344001444650040c140c01c0003581c0115290 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 817464793 1250 817463543 817463609
    0x241915080a0c05010e06131a07052d070f05210312070311120c09061207050c070f1503050c13120c06020a03090e0405010621120801 58
    0x508050000010003510034060140064000e402100300d0a15180c00900516003050029100d040c04010103100001c00780310a5003076500108904008001560201c4880d04c01c3d20b0001d48544110100200c02802b81c214000c69240c00081c4040700c0d0b00b154035055a50841e6000360344603c40752280c2400141000da46041d900002400700e02c480c68008011503084d03070301200d40300c0c03628075800040203c0701d03416000e0082e544c584039150500d0003184000f01c031022000508484d0800d0400995101c00707075207490984005090f50000750300e032410f1402e006407103035004440300d034803d001310a000244480c11210b00401c8070816004907180b181c13000001c80061000901d162100b02d0240658602c05000755400300261082402c045200503807802c0890603c0180c3c0d011004550051940c40006540120101c046a5000c0d050700302c5521945000d074090a03090b003240c112981000c40003d4400c00d072106580c0d050b0302607408045501d010240c22180c0580034002c0102c6090141c2c41010f104070850951010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 817466043 1250 817464793 817464821
    0xb06030a08070302060702061006120b0a1d040b010515070609140f100e010b06160f050a06020316031413061d06100e070e1219052419 59
    0x10341505580d898405030000c0ca416401a84403c0401070703040d0f01041269005001003828405440c40c1c20703402840b400f40403850702e00303290322211342d04070360348802c102600681030303450b294014003500c601d00009038481180c081c2e0f034000d56500006614186031003c010494001500300f0300c0d00b941500c03032070b010703005503082198401e44003900703c1c44001040c091030b1040401c48001e0302e4890380c01c4420400fa0b440d00030b0681501d0345000c041d092143d5903213086a003401d03240040c1440480e02405c004000d545d65020182150046014010400000754021489889036502e55850307090022022000c0303c1c1105482d00000b90381f600401c018051920641046510404003c074000da803000c030f500c603902c2081090800aa0050b400e1003900c0010085620207481804c03920b148900e00818000c0ca800c5100d00703001d018203101b4074451404001030200c00c0c08643c003148500b00b20b201524010741e41c1e40d1384a00034056541c3c0480a42403900c1d958074210b004221101c18204147e1803460380d20001c000350400c080b6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 817467293 1250 817466043 817466053
    0xb191a0607031b080406021203060a060f050418020415020309100e040914030d2f030c1611040e0102040308090f06070f140c0a030f170d0204090f0f020c07030b0603 72
    0x24842078000006800144101340d130b1622030380307020030180c6000181e24900580074800e10801007a6200d8081d071400702ca00c2850800965804403c050b107581c480c9800c01084500c21220000400c04950000c0c000c89108501103021800c5844c0c0490300d034000c03d42800d0f0310424a00d1030080c524440c44500c155000018000103116846039502c6403000740a0324200442d410101c1c1c1950309514610a00e403424540f030000200102c0c400c041103414818441021802240100100d03103c0f140840554105809204800040d0340c0741d8201007a40034100348015103d20300b00102c8001c03081d01030094504032035010340c1c842e00b406141020060b10307403011840c46030000024026040801c10042c81010083d00840d1108690381190350014140128407124500030500e40d1020000190081c00d20801c071070b0004030008000512050f0300c0c0851145082c2000c00c14008140490050030765401121000c0c4800b20404caa043e01d010b16000768024107201c40b9150b0060a002c00c0410092080e0b030380d110320000c06881d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 817468543 1250 817467293 817467317
    0x1908160519030c1103070513020a030b120312090f030904090215030708040b09010501030305031f0b03270115061d0d061e0e03250f0b191a060703 64
    0x955003812503209900081c00400e03c2c0e800d0181007601a01c2c50101580076080c21401d0401060f181d0441180f90312040c4e070b001800c00764080c070a52240e02c00328401403441d9030240c4c40104555807608064109041500004003003203000500054010413100c00301c0145042107102c0c010071005080b0b04a00383d800603810b40c403904c16046290000c40c4510159143c042c92030500f414042400b9100629860440c0e03d80401800401d402009586e40141d642e040c203540041000c0001d03100030401d5216290210010050001509818000c0d00943c1840400021400344450499080c0d4401145c000c00b241580c0d00140011031007104102982517030030020b04082d080d01e00109650340c810351019034805903582008207009140c5a41003071001600310003401084a15400710740c0328440c4130412800d400d1240c03441c590340d4420110422180340c01c041c540c68540c000d82440d42590344211403010128048540801e4520018440c0020f0403181c1642c1d0304900c6200c03001d0050a5110450550921030300100070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 817469793 1250 817468543 817468573
    0x501050c070b030a051008010c05041a120106050c0d020a080a030914070f03020901090c0e0609030705041109011815050a0c02120f0607031112041a090f19081605 71
    0x443c042c241d01440084c0e1803a11b02101c0c104041141c11400b40f50741020114241a540700080c0e40c1510588280c0f01410504001070028070b210302220340c00919421000001c50b95081405084040000ca00351184081e04070402c0fa2076034a600c2c2e00406232034041c4907106103580310350301c141070b801c2c0f145a1410110103080d05c400d01c0c01000741c1c403003201d00894283c2032013141441d0241c40d004080e400780c00d0040c42c0d210040640001c4400141e80d00aa101103500c0147d960f003002070038003c020141c4108250a5001210422984491070281c0482c4405200702d6854010300000c0f400c64501e81c4040702508800c0c10304880179170010b0081010810904071003c0507039501480349440e2600d0200504100104c6e64481d800d00c41c0c0201120706061a0040142c90701024000719480d0106030540000c4030340c1c403890209410b04d820100d1800c03000080c010400e40c01e600095a0b10000c000da4201d400c0d02085903152842c60402c1c0000074640502030200a90f02c146000c0c0f0221001c0c410420b80d451460380c0341c84 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 817471043 1250 817469793 817469797
    0x60b03060906190b0906040b310c0c02010219031701061d0f130209150f0d06050d030e04050907030203100b150f0a0f0507020d081209160501050c070b 66
    0x1100300c25412002c107000f0703540f800740c00090210008001c1800008025000100038080c000e003c9401251070381d003c0355a40c5c0e1380d04520404400040020340c1c62002040310389101032024590500c1941c0ba100301607003814050800c1206555050f802496412916044070b9401c802ca500c044040c0030709010b00b407204082050000f17000e0500d98cc0c1c2e0083e00194240b09200c10b00300d454041e0b000301b00c1c43c1c40b52503483d00c692200c10390303609a004025a542d01c0040100c0c06040d01a01880100d50011a0610103140c50500508141ca0a00001d00c092074480302000b011644902c001804204020f0000d8854142034000a038401810b105544010ba50707600800d0810407640341000004d595401d0b80b00d518607150414034500502e0b42c0c081c40c104020b42d907a01c2c160b8840c05000e4414003281c0d580404070b90b84600122241543e000c0c00ca002a035019243c10032403908440c4269284151400028100700f01c001034020060203100601d4121a10301001034403245d0111110060740d0182c00700201d02400d40b500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 817472293 1250 817471043 817471051
    0x30f0e0318152503030b1509060a020f0607091509120b0403200303061206042003030403150f050a090c0509191a01140f0a050a050405030d030c0e030d1209060b0306 72
    0x411403c801e41e2516004044440d5880000d2050342440425041600303554165441e00c2010345000307a0350780705203400b80e15194812843d0232080c8245020803d495a1094003c0101c8004200080b98006960f20a890b01951401000e41c8050000c207000d0200b84404001a0054000c0c1041c081a00700d40d505148840c01e010003803c0141c0c4000240005810688000d4102c842c0c00c60187c03200313040c00c0c1c0e6440d252204024076403516a031904000328050b03030140119002140d1201c2c81c06600510004e41101400c0c50424404810b0715000c00610015114010b410f0031139070048010901c9400c00d420443d11041c09041c1410200d0740b502e400c0c90000762441341e00900c02035624038000505501d00010b100400d0600ea0052942060040320103010000066402c000c065090481e12603020310f030226202d004a602240d4188a0014a00100b40e01a0300c06510354a450b5503000c6082c3c1c084060640c1c400c03d0071002000100a11064500700c0d2407540240111407056202181c0d51520400007403034154103407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 817473543 1250 817472293 817472347
    0x60b0616060921020a0209041a09010e07051509131508030309060108011404060e1203010e062d01080606090a0602030d15030b010302010f0c05010c030f0e031815 71
    0xa5080042c042411440c000390b08400000003d80c0818a900944440c0100c1009000b007030320170302040400c440307a200d50112140b400c9201c505890400c42c5607021301582c3d040c214240c00b5800d001310341c500700401c514800e0120031040a1408030343e03c0a101d544240b08840030f84d20b50b80c4540d440c150462800006008100c0700000b1926410421210350414506034045d000ba85c1c0b605031081e06006a44034640d900c07a0300148001000040d65611500741064144c045000760400400400c00409005d0b001e070240c00259925448296440c540c0d01c802010b004004401d14001c03a616481980b24549459001c240074060a040240400120301c09819035044400541c00101c1c903000c21820350310400c00d21020b51803900007807d02e0f5407a01c03c00248180030203810013291003040c0c203150740503030182034629a005008001558103094020028060305881c1210036042c0301282c03420140020940314074141840c0ca07881012940e20030094440b800280380d0880c00f000f40256061480262a1110086100707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 817474793 1250 817473543 817473551
    0x30f051602060a0501050913030318030c03081e010b0d1503062004030f06020702191502120c12090d05030a02010f0b03011a0f030c03011a01090608090a060b061606 72
    0x200c000e800e2880040000b07094034a440300401190b60307502c80c01c03178201c00000103a07941c1500e103040807030107094075104070005203a07009104070806510911004400e800380d56030382900d454070450800c001c01c4c0c80079040c1586c01d46d680180400c10b40e180091052800701700d07000950910003498401180f005600c180d460715a00e03200b041c142c00b01c0001c0c0c00c50007580d00c4501e503c0e0070306650303400480003202c0d0805040d0316030103d80c0038215141c0300d1108a10100c5400301d51040f83e510405809211660401c030b03001030186620a20511480d001918002038105000e0708001aa441101015800c017008442c0d000941c408004040740c010310051686d07103115400400c0301307485410a00c069400d1030720080d010341e140580b0398400180402d200c18440030b0846481e940f200181780020715140d82c1c4d02c0d00c1603241d4070b04000340c403941141d800302c505002030030303200c10100c1c2d03564580c180d48041c400c54244910303801c0504140c3c00901e01d0f5105c007450b020000c082030304000310b1184800b900c2c1e23130200046400d1652 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 817476043 1250 817474793 817474831
    0xb091932060907051204020a0302120604030201291005040b120114060f070221010e0c10050405030613031806050a021204060e120705060f192d030f05 66
    0x15060a00c0e8071000030707942c008460601500003440d0340310ba07650014410402c24089811940c54818079070046030018034400480d800c106e040c1c0c0c1c07540e00036038044000d98607100c0c85010014120300034101141b00381300c5521075045c02809001c955001080b400d02004005c10004c1034404808c0054490480140404446581840c98044101c8034005450b07100304814080343c1d900d6010231040f40e1407168140c81800b440007020000c01800c2155100c5030945508080008860080c0050204c1081d80129107050a45d240c01c00b090f80c10b8400c80c0205501a007040d0000f9110070102400006044e209241601003070070046280d0f42440080d400c01c1d80050030004500100603410842c401801e160090481e20703246c42c000010708542e952860341ca006003402d01d0201d4081009100c50001000041c10050792051a24034024480d40150700303841e02da100300b0004034461342c45034864050b10100108041c0801c1d1500ca0003407615080780301a10201501c600c50b08028100b14000c180c040d40904e6251480007603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 817477293 1250 817476043 817476131
    0xc03070501050601050708030a0c0c0c06030c02011a09041e0204021303112d040204082e090201050a0e1906052109120c0a0828030b0919 60
    0x5805001e843c100300046c440391001c01d411204403608440b10004c0081d081c5070420081d00c1c3c00f44d0101002c3c00c003070300c540350015100750160408002d0000700c3d4005c11400e8400f200380b0240501d081d501c280c006100d04005400609480d51010b480141025842140c0c052580020140d0f4000019400c400c110910208200040e15560404007042103030b020300f8000b043d40d03801213443c8500f0a85042c0980b1510a0009a140e5504131806042c4003803d442d00da01090007688181c210f1281416107007421100c0a09a1a041d889440c0c100760b4140d44e400d01c1e0001c4010300b04c540c1c2010f48003556000309810351100d0f03002981c0e284c00b0000d0001d07884441c0c079034102c2e4a45000038810070b0304118503154030f982040280701c000302d05640e1501c01420425218200c0d07505082c03030449040c00007001240e000500040111080d0340c0c0402d030b41c000c0c403d60210311400840860950380c0524000740c02440480c0416a050300c0b1001617005592815030000720032283d0002c00d60266082d035412006c0c000030b0015585145 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 817478543 1250 817477293 817477301
    0x2101a0901080a02030c0f060d060f0503060624090f130c1103070c1205120d02030402130c120e010b151206030604020a03290403170a060b0d0207020d06020c03070501 73
    0x1401d0010340b803d1451a00401d840c1d07a8010720aa100d411084078040305507481e4016500b2040b540c2c803080040d99258140c4010f03c00550003040c0c46417003088000303003c51406e14110000c0c0096090f501030110401010384442e40c00a49945502c46824000442c80b0380b5043d01c1c1c100040d01070200425080d21003000940020611490117410b50420006600131400400c504070455078072081c4902240214140ad50810001600c11090008001030801e101c1c95160040c60099008403454013107074400100074000c8902c07900c210780100300450400412459207030b2000c0c0c0c1342d0809400125468110701e0003d50001c942d0007610b800c008000c030b900c160248400828943c8110300780c000705101e0505400090302d0b14000d2000410b030680c5d00002d03038444054481860101c0e5016139400384c2d030f07080524014002c403038414000c402860207040014569480c1e4005c0204444070861040d152042e41c1c1c141d03c01a40c4220000d0745c00071248080f210004003035100401d07002001c1001b1f1900d802c0d007450320343d00399 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 817479793 1250 817478543 817478549
    0xd02091504081513080705060910021327021c0e010b1503070c05061312021c030c091a27010e100c0203060c03010906120c09050702101a0901 62
    0xd400740301c1402405000a000d04034100d000c00c0303403002642d60b03030503420301070404800080000c00b01040c16403c02c40000782030750107008400e099400000c3d005803044c00700d003d4002da05240786080c000030440e019422034114005480c5030701100f80a9080a10202668800b100c02d18140419401201180c84107204d1a960400250024000b00d41d54400044003170380304030f542d01008000000454249806003109040e8503a0250031707624645010003011040326203800090710220008103000200c1c42c030101e1131100c1c4101c0341407880c0340000081e20407001850a0704807071042c130964520116803c920410344442c2c07444020b0741c4507583c8601e000300c84500d4050f0b0b034820310a0b80e101d0049a001da80c1204040001c404150b4860452045901b01220341d10414100070f0b41500801c01070041c040d00b180e00841c10b84019000500000380d648456442c1c190319500301070301c0d40d5501d00c0140205d074410b8001139002240351043350340d01c91110003007404844000010b03034800702c402208980e55090032602c075401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 817481043 1250 817479793 817479829
    0xc02100e0a0809060307091505030414061621060b040801140403051213060c080a05150307050405180706021f140a0f020f0c0312010e090d0509150d0209 67
    0x8048182d5034484003800340440c030a10906010002407036181c0b1414a5000030060109620b040b028603a1019203076600546042d03c03140368606080c0700410000403040d00a0360400c14101034090410400c13200f0351401c1c405648610042650584001c80c64003507080900300031503005030340340d1922001a084a0356007131201940c14000d0100070100e50014192901c150340d082c4000d126949500e251000d4401205000342014079140c45944220382c00040b42e445014203820810494442090030811126032848460389a07029000034842814070350041d81d040b100f00007186186c0d800c8440d1581c203101c1c40d50050f90040c1d0040201e407010010b4042e042504c0c404943c400c22600d11807614103607000c14014a404001c980391020901c0301a050ba0484086414500c0144c1e02ca07004031048a0f1264020481c000c6602c0e480c0380082000d51941c410b181c081c06016004000d4002c604800b510701c1d400032004150300125100c2003403400321031301c5c0003010b42079542d15005a0b102020801c00000710440d0030f034900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 817482293 1250 817481043 817481053
    0x140405040308010e0c070609080a090e160e1206010b0a18050d081e0a200f0c2803060603030215060109060c05070f030f0b09030702011b020d060c02100e 67
    0xc0400d40060300507055804440200c141581c034414426914450102d009008514142807502809a00009002c0d690101d80d96451b0b041c0c3d95070341c1c503003102c00d0607611024a039400c1d000d6440600c0c06102000e020360405400ca940425214652904142099000000703003000098005006a4040e5404c40798081e0051203807512400c5c8400f04100350001c3d00000d01d030602c00a0182661007004500c1039810207050000c55071000041001071035240904011000c1500c01401d440813450301140100000c9480d80043c41750806035000c008401d5030012414034886044414410401403002004000e180911004682c0307915510b002484c1100c0f12101728880d210410030b10845030b0f4068000802c88010b481e180101007501d041c4103042c00480d500408802031150000403c0181c1d5102e034090b04e0340030340fa8003071560341c0f1000b540c4d48a206103100240002e54001c050841c03401c05440c001e1000d4000f03002050b6451040d550601120300031a40f80d80940e1000d82a41c4015056001c2c4012000b0341d500980 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 817483543 1250 817482293 817482301
    0x3060c071e11060d020d0516030c17130c0306060305010c0905090613052724010b030c07030c060212010f0501050a0815030a051203071404050616150c020106140405 72
    0x81d1203542e0207a0214411980020800c240c409a0b8064074002c01594408001d02e0a1400760503800f01004405900400d09003110b52903094081c2e110259550b0900c84080425a0380007610403034082c0d4508105c0d00c2d034848080c0400440c005100d084041c0d803040000080c507074062440034004010950066100e84541d03410451240c5805075902d6030300800a00115a0382c850716000e580c64444c0b181114103509011411900450002604988908218100d003c40343c25082c01c0c4040c5540c24056080032007000c1000c11750360b00fa40781c02060414002d1130035024950301070b554241a030f030203502d440d0020030170799005026410700704175142d00a20007405c20610742800d844c030243c41124018548001000902c04040c40c07a02d0502010503247d5002c4262603c200c0d20001d1082150000c0d00c54000158058020303038041082e540071901a5580109181d041c1030300001c214000214104049907555880307000b00d07250b443d240c0a0021140e4080e000421201c0c01c040c094100c80b91801403181c86581000240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 817484793 1250 817483543 817483553
    0xe10020a0308221a0114011e1202070f1101030e151312050409050609041e0609020603090c130b0d020111030f210702120405061803060c071e 62
    0x28610380341d410309051005035038820072403441c2d0005001c21008203010840707110400c61000310207011607990a11000c1d19907201d42d542000030303a280341031501180d50184150000303001c4403074100c000b600c00d00d031524007007400d118140280c0e0020401250640741001240e0200110903a060090400a1808001c1580d10315402941c8032800c1604080104544c0f000c5803020f4020b0070b4680c01550009020041c83e40b4810008000342c0c41480380140079898000031910b01d191000d0201c0c002c44d0400c002c80c3c514442d00108160944040300704441c081d80d034070340700d100503210003001d10b20554101000e400d800000d00c0c1805903ccd0650780c0441100d9281c41c0f84202e007590fa060152800a8084c038003403800540702c80035645103100348480c00310401341c0442c1c454401c19469255429120008403048450b450325142680d40d6070f075184000d80460300910003440b2a04003c00500800c2840c0410781012483d0341020904001041e100000310000014500d0280045002c059418582c0b41070551800a8181c440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 817486043 1250 817484793 817484803
    0x21080301060c0206040503191b08100f0f05150102010605030a0206180a0315020904060e1306050903040b0c01090c0501170f0a09020915100201020a090b0a03150e06010e1002 76
    0x1803542401804000b40096489220a81300581401b0707040782c0605816842c030843e40000c003001210b82c2500c41056a5004001007107040c21621100b0091070030b03407a42c0291501805050f884080c610341d42d10000c950340001c0b4011140110a504854410500150002401c0d039010380c1020303001c2e600081c001d40041c0c9a000c110344043d100c031611004d10710080000165900e005a0028204080030380071038a012142d6070050040f620120707070402c0100d58030901c100281c0d00403503509284590016002e00483d180303800856010802c0c0060b02d14003501c903400749145030060900e540303403607554000303480c100f040c40401c03040580400d003009200d40424600408e04824003c080c8200004224080344040d0703429001a11a00d034014240116460f16444080f06000351410b0300d4403c10f500f4454044050040c0700b2101007402c0381e03903413a1400b82440c80c40c0001e50321044404040580d6682e21711075038032085486038043c181c900f441e12500c1c00c18400060010718002003040c465a40031003502e0940b03400040b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 817487293 1250 817486043 817486049
    0x12030f051005122a0d0209242b031808100c0503060303070807030318050c0102070504050603071e03050609030310050102010b130f110f041a0306010212030a200421080301 75
    0x2580c00140100c0171550905035844002c1d00301c140c0700103208001546401e800d40900d08400100307503020a0300f08224074000541c14091130071280c4540d8071110301c02240800c0c0010301a0500040c0712031584245d40864400d41e110184d0398102403940030209900d03000e0b8400e191194a0701c0c50550400c42c0000b40c0300c1c42041c0000742000000143c800405001c0d4210388024012442c2402c0f40400c1410f0168551a043d600f00b8014000d0803000300d1503282502c240350052201400503c0d01504040c03e42c181d001013000701c4e00328040308d14000000180100b01c05071062030340780e002d9901d0b81440c1c0c5030070700c0d04409034003e98156410000c000c00e40c1d0b2504a40d43d06c070b0070503522000c0f65583c400c0070b03104010007420512000c21440090810310048148000f0401c540b900310070000070f00a1081d00700036a02040e10414010303000000b6910810410310b003d960030142210001031036118015819903030003020204035945100225042000003407100c01c084074001c090145010100443d03a540d000d13448140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 817488543 1250 817487293 817487353
    0x9060411040909140111191e0905040506180105150702060703110f06040807080306060d110a2303060105030613050424050403020c1e040e01050402190b0712030f05100512 75
    0x11f11010804c1c0700303e00340616032a200c0c10381c0900360340000000b8a4406103014103806542400045103447c1040e580c01150098101d982d1002070742408108800d411840c204004a1441440000056a100320062007603511a4a801110403d2a40b0b501e0803c0c900700425800c43d084042080040b030948800c407501303107900c0000f031030380c0c0d58411001a1807030041100b00b8042d1440d0208000c0080b40b92001400704540350744071203c0f0280040482102207210f0460852015014008604154055000307160004e000904600c200e0600404000441b4004c40c1c044d149603044040c04039298403071458190305040341c06014407048c50039441c081c1d580e1501d05401070107026007010000410138009582c0003151801030062020401300c901c403d000e00010740d0305901c0b6221242842c0700c208060010305c41140c0d8240040382c202280c80e120000c5036001219007105042c4c4420b40c1c7c0007864160300c59503204078800c02c40390712003a080506001d6100d00b83d52030411151710030082c022001c1c00040900110b9410750f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 817489793 1250 817488543 817488577
    0xa1a0906070c1206090618020307090207231f0b0607021002031c0605030606061315090302150a120c0c1b030507150f020a0c0509060411040909140111 66
    0x60700d010184030401d80d0051042c030840d503e038001040040d41124090078007660302440054100b4070f038250070400078000258182e0003076408004854503500540417542c080c164600084081c1c00d4152a05800d00030000c656070003008804500c00c075504801c0d01000444201008292540008500617109640703020b8403c00f401104550300b144208112004481c1032f40e40c00103005038542c00c820181c242340c002d0030711074001c020005000307042103002c0d00c41090810f07003030400d107511b410b407121011850040d40d2402c1005a00d004405038490406851110f00c41e03000440c1c0e146030016000f882808544e030364140319800c0486100e80184d0041d900b0311a10b400c010000c91410700e83d01c83c07580d04801d6500c0200b0078011800001844810101d0301ca6140d0451b80b69081001c6203001300302d8179042c18420060990103851000e100b5800d104110a0784102f0283c8001820341c00200035007059040b9a01002015843c2c1d0103883c204001281e00700019a00e000080c400c1c800c401c16581903900581040d084030a01c030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 817491043 1250 817489793 817489807
    0xc0906080c131a070c0e100e220803041a0f010b0903010f0e1c1416020f040e031c02041406130e07080a0c020c0907180503070e0103020a1a0906 63
    0x1c0900b8210082c40300c0a801001d09a440c001520540c01210701662040c08080300003c038149000045846500310142c071a02c52420309400072901e40c400f40186446210f01c00d81c0d01c0344c0c68003240f50701c00041e000d422101c0d104d00e064a80310401e0314040b1041c48402d1120014800c00c00003202055054448600395961221410000f00303004052140e5003007803240c02d00a5111040301e004c100c000b42094100300490202c4840e1a003a12054824070241140c110200010408480d1252118400e9480100b11040310a41000040e003503640002d0318800a4000280a54081e0182034088903955400402036081030b1514000d189030040c8122145d0003468001b4000007000303180d01300d41e4044c0030f0314040061607060828004061082c01c40d04821843d142c20035044000380000f6080d000310100810702c2e4040d940d140c030202c414449807a0760528818034048041203d81e4207100e417002034a501c400b110340c191314500400424004079030103162040c07800c0d501c01004003201400c40381c011b0816100c1b2555400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 817492293 1250 817491043 817491067
    0x30d080901180c0501030b0d11040b150307030f15030b06090a090b09062d0402010e0301060914040c05061303380a0e011e09082b0c0906080c 62
    0x1d0880b50049294a99491a01c104481d0040000940d042070740c041009a81003001d000c007401c240f55001c0c150f20100904001c0a280c9504110303200080940050401c0d00003000200c450f40040c0c4002010940301d540b135101990841c4190001d030500d04d02c400103404e1564881507010300c4003800850141c82048006122003041e80c0011320f921741e105489030300074502000300c02d407100426120100c003150881010300c030341c220149c0071500d801e41c40100400c4985455005541c0404030007005a0155204c9000013151005031140c00d4032402070382d00200311032616184c100034250080c2c000d184259014000c80c006e00e0075940100c3c00740e0390304c0800c50b0121800200034104502d90020b000d68509030078090b800040070203514a60103a40c030b40380c0a111103020b4841003800c2e109010051112048004076900707002c0d40703642080032000c2c0949010b52400011081d500740c1804071002020103282220746244418580b0f01c90400e14901ca0324140518505004000b020864080c0c4410054500441c130051101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 817493543 1250 817492293 817492301
    0xf05041e031209090c08040b06060304050f070906141f0c0507030506190b0a0506030a0902012a0b0c0408060a0b040b041a030706080c0a200f07090f0b030d080901 71
    0x582220070070254460707500000f4032102443c0038420f107560501e0814000c0078010600e0501072a03208050313500e1507071100140306160f000200705840c6446081c0124690210901c80c0d900030b8141c07080040b50043c00d01601100d01c5403007000c128018a0349819400310000d140705001c000032864070b002e00200082c0e0a0980c98608145c102500340d024047c1840309405002c58041c1403038100b0402030000032104d1040040080c5584991900140e04000040c1106042d40c41140c0c010702c141000402c240400c5007911454030241c500220321003100106400344040240c6583c2e22188260201e464181070902e00c540f100e2016000f5103101303481e040d000f00e50b40e6490700326889064010308100302e41c00d0b1110002801c0301010600d24081d00443c0c90212b660381c8504c0980d8450421100c4140c900300d4200b000b01c1e15940503503010b0140c1845440b4015441d0014040f10038003c524030003d01000c0d080562800864031002a004080c80c0b0740380d580541500c0102e000d444000b968100081030707546210502d4050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 817494793 1250 817493543 817493549
    0x20c121513080c0606041802010e10090906120b090706020c0f041d010615051e0f04030506150a0f03211101180b06060406050304060b04060909030f0f0f05041e 70
    0x48030b000c0340f0010340120028540744180070889051140010f0403180300750034681400701a0000358801000c0e50f075410f00380e4061819600d940b4102803881c0ea1400c130f100171940d00390005035588200111b52000d1149001207240c1003107907400030f06040b9203000f0000c0d55444a0080c00d5014960792080c0c508076030380e250300c044c0c08419010002e203000b02c0c08001481c000c0846002e44442c0d0801c407a540b0780341902c603d0545110418030910706000d41d9505e00d0101140d0030440028400140c100401b0000910500116008403500c331143c00392501c01004000080c3c1598010005c5210102420008115029139402c110403a0141c1400154100d001c200d44100155046103015070030203103050a9185031b070030b0488915021b90120b611684a440070030200303214a103e20400030b80184080303030105400f54481c9659110082000070407580da41081c505031441d0640590100b01110580c0318555001040500008468030304200594140e800c080c1850280340540c0f92203c0740054909003180409841d140030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 817496043 1250 817494793 817494803
    0x30f0309080412030801081209060309120a17060301200c0c040507090302120c0d12020c031f0e0601150e0f0d050a1707030f110a0209010b0a020c121513 67
    0xb0b01c9450340c2d000040d250390118110002020300000003142503010503070302c40b6030980100151034001c14004011880d000500000c000b4010041800d02600074200106044203490311a412143e09249a440b1000c07801410b09000343d0514030a560f508640340701d0980448454501d65441c1ca001d08003903481c0100440e10142c0141c902001d00800580103d5000100c1e403088808039814030081480d5900d6101c040c5002d41c01010b000e400034000f07880c005050101d241148112a558401000060b141c000d56121000c5d12404c2c010080100c1c031424003030b00301c0c43c0449030700030015545490a01d00c1e4128a541d500d104014211150310401e40c1c07102e40c0241c05d80801002c4131003659007420b200e6205d150606085545444060380e540b00790b0b0004040c5c0756a1034241c0c403880102101030302c1c10f881010b8040300700c0065018410907000181d07995800107000e4aa0301d01660307200d850612019140504101d03009105a80320321b164030040388d00007550300903109003da2034041511814403040341c4003181900104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 817497293 1250 817496043 817496047
    0x50108040b1f26210f070605010b030a0605040c080f0c0705060115080f010b030a020f041502010912030b0a030f0206090d080306100c0213050c090a0b0909011a030103030f030908 78
    0x90f4203408001800c81c60f8000341c403000060043da907a016911064400189100211404001d1403481c1d0302c00941070350710030300d04c3e0b45213000d800e60740d00000c490b826046a82c41d5a0003006001402109203d01c8006c1e005c252020001e4244050b0050041d940081c1080c80b80340b144030014503d000400c0603901c200d94420100c80f905d50711000c1e4040102d2044030007100140703012000950182081d03080c203049400d0340c01c15902d15240e6900300406580442510246030508000001e25550b03040c00041c0f10310302550000804524520300301c8999030b04030509004250400f0041409a039a1019000c03c82e42e108030b4980a0720003e10200f02c8034041e0502407540305108041c03107018000c0500046102e550304484c3d900300d46021031429520101d0361903010350041e2028a815110306650ba003c1134001c0c14074403105080001c00c1e0001500d075003441d00803140d1400003050114080c1040c20546000d4040d00c0c00e030540c554400e08030320045010510000d000c210009840a14460180d800130041c0e80c1c104010f07507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 817498543 1250 817497293 817497299
    0x803270706080618060d0f0606050a0e1b0415030216060c0c05070807060f050327150a1a0d06020405040609021c050405030316210509070807050108040b1f 68
    0x10340241003ca6100d40500511300f0481c944032254600d840c410a802803044010344105d80798401000c2d10240211005656144017055640c1c0b14844200180400400d4000900d480038000c0a0041c0990140356500c50601c0144940d40074808908500340007031030016150104a880d16490700050100588801d1a001e810540350342d03c040034204450041048900c441d64a48215507a017940d4070034240000c42d50070180c074125126100450700100d09102020204d09081c02940c44100b5080841c00154403a00741e0100304840180c01c942d1100c40c030002003082c4907800007148000368054900074442c84c0b40c25850010044654150740180c2400713041040200c0d160035030200290300c00c0042d400d0ba03001b84c81e00c40b00e8012036401843d114a501c400654115201c1201c0e89100318603c10581c81401100c00801d0910308005000b42c0e07402e03411001c0030605080140489041101030740240c00c46030000c820510450f40c000312600d4101d94442c0c00490b4580e80c105000c9200c000e01c40b80d06c60400000d503000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 817499793 1250 817498543 817498547
    0xd0f06020c0307030906050f0315030a0b07030f060e13030f050d02072603280b060f03010e06010215070e1f021024030204020c01180f05060c0301030803270706 70
    0xf406099100c2d4461038a02521410191003a000343c000c816070a6008100140b0ba40d01009a62000e10201a088130005142b640d03560740304103421103410000a913210715100014145015900003071480030401d94650a1005404d900302039210005400c0c0540c2c00942c4030740611410440740e00c43c040070811502e82c0c11901c3d00d88c44040702030303039030300101030350341d40042100c8001404032401550801d5200c05401d1420740741c03140f2403440c003040482c51607582c07034045040d44070040140395084400f0203031541c1c0e60400032841d400113800f500345811940103c0d04514100d401102090b08408c49003071800540046500141c2090307030701802c05a015002041d4083c085030000744403507002000f04810300401d94900c1c241e1240c42c0c0044e11440100f5200714042002d402d156008040c1028840300204503c1122450701c00000486d0008454a001d10341084007848821b2041540014200035a10b03e95459616a048180406800703400618030405000384203000d05601580038030740007800da072107540d901c90300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 817501043 1250 817499793 817499797
    0x31903020d0815061c0608120316030207080a0c171612031109150f030408040f090212044101150506030f040602091507020102190b060d0f06020c03 65
    0x340c8004907001801041d44600121410418100054500f034103041d00001c1d200500f8001c015100e008540e686c0300400c0301c84c4103201c0720800300419000300c1daa13420922400d0780440c1149107000c0c10180b06000107000641e0b54002c8413038001e254030300359049500c00e060000011142d240301c00002400003440e03846080e0000d9499044601503a103603c07031060107080c10f8055400b040c031120712001040002e114140340c1000c0c0c80e00900c9a0f10413941c181f5103214450300c1a540140d505446220020600300106110382c68044060038410700150b05002080c003074a6144400540000c10440401e1122601a4040c0d0040c0c4801c40c1e0300c0208251101072100643c2c0340b402c0c1c828200700796509140c8901c004000ca44070100031900050030807881d40d030b100984a140e03100e024004550a607000c201c0c80d05203540b45000d0307202004030010780ea961120b43c3e1001900d803581c031428403444103d0306c0d0800c1012410034800207a00880654551004403890700d08120202034171340008140a00c00300c0c021113034000c0000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 817502293 1250 817501043 817501063
    0x6170a0b03070e061305010e070f171302150f0409050c210106030e0f07260d1e0309050d030b040b04060306051e0f0109020906040803070b060103180507120203190302 73
    0x1000403c05175880d003076409403a82401104801400400400d03109442030140b100c1440080c94450903922611550380d9a100c400c1c0e411060403800c801d0b202055207015150b40da1143c3e03241c000c480c5040158041b030141801107104c0d22084540d030300700094014220808542c2141411400c110141501202e00b100c82c110a004220000740f401200321440f050010324907942c00c400200a00d0715600c2d09507805a800c00d441409050041e048031a0b07820a5010040420518400d44a6000c10100158165601080a14010101030070f00e1303610b101190000c14260815010340c038000c00e00b10581c1c80401c5c05000a00c1c0d0b1160010318240d0008240800c550003a4069030309c80b01e980e484030010b40d20758030640c0030079503114001c0006907004100b6042c0c01d031b004007900721001d00906d05041d55210803a0442c2c0000d9401e840f40b26a1100b0400c0304d682c144105101281c08083c080c0807002142c4a40342c0c1c50189000c1d00c0403200191a80d00305541e0204003812030001a0702500702141c520340790081d00c400d8400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 817503543 1250 817502293 817502299
    0x70803040c0e0a061208031b030a0c0e0109060f0807031104031a0c03190e070f030b060111030a05040e2a07200d0f03170c07020f04020406170a0b03070e06 68
    0x14080b4010f0b0300d06000d000c04840405035143c60b400742c291100c00c240e600103011612024600c2c0030b43c4900381c05c010061481040032800c006480b00344010302030403a200c40400e0b0b50402a01201c00d100403500148240700c06903a074500101c15503980381040d801000c4001800c3d020300c001150000c10403003e10720250384690301d0514900702da241e04540711018042501c0840110f403001c00d05040410890780419000c00d6114111162180c1d640000c101c1e4017801e8000381c82540f0100c0400250b941c201c4800111074036040015850644031140041c070a000324000e0a880a0810300031034030b40f04100302101c4010b400c003070310540c2c13820110200010f603a01c00030381100e40c9061001401c440207a81403a0091381d2070082c00300600c410540e40c1e054a8003102840403001d21070011000d40c00e13201110030307c600c1494403c5a007651810b8900400030040001d00d880b07031286004200521005e40c0c41003080315091008c0e900550961521140180545400b2034140d80510a40500003496001c0d01c07042801007000b6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 817504793 1250 817503543 817503569
    0x16060c14010b0432060d0b040c0312030902091302031f0209060c010501150305010302031018050d0906021203190e150a090201030e0a0506061c0c080726070515070803040c 75
    0x207902c9099003e0303400c882031075008031058807a0007c1001032107543d038040c0c4100030440d034203512503541c0120101417107040c40002e030399003140b5000c5007082c01001c2d03080408590381c220300c000da542c00a6070b40c0c2000348441c0007865002001203401500358050301d00a00c00204000d072a4110481000d0003460248140c901c94060b4085c9511003902034031030306042c0c0c0e4000c0c000c0d103284a04000c002c400b070084600051009804050f0160110b40305000c45e032031881c603664800540d1403419070003e10b0b018000c06001c0c1130001c01c2040c8400d148079070540c40014620728001050070552520110308001994040d000d03002c03101800c100d481502a03003d01e80080c0701344ca04000000448000303a0f9a04140000101907900c0074003c900c1d40e2401c008030f003050f43c0030900380001038605566070b40a60580c6511840896002c07900501230b00c10b12030034011aa00130040075844048450082a603209004e10605001da21407602c6aa0484d031008222181c0b103400105050b82c0341040d06c0d16156151007403082060b42c00803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 817506043 1250 817504793 817504871
    0x110f0a090b0304030f05030429090f010e030d091e080a14090f0d02040f39021b0d1a071101060f0504050a140403020a0516060c14010b04 60
    0x141c00603a401590541d80e20203030840403200960b07060384094001e0365441c4481c0d022500d1384980100b100301042040d0501d401a060030458a03117040c498424081d001d90510b83e11400c803000c004141c4003110f000742404903010015081583c26140341c12244081c0c0c0c0c00e01e80111041c07107211801000007400c25034468010703a81140a540090103841e16a40d4490b00361114590240ba08800d141d00d0540010000240740b20000d100d007084540c088078114514080000303180d1070340000303042181495040021910a0920b40c00003d440d200d000d051400c0310b405000300d003091511050005568140d0100142c00c1c0d4015440310130038840c00440d130402c00201c003100c5510007010306004000c21503060306084000c0d50704080800004d0240144440381d074170f27902d2603113062108402001500440c00ba4001d071012000301d00b442400c0c000395803600c92441c0b14440080103030b00e511403010003009400828260803100d43c000000e000d0031607881e900760300a040815100c448854800c25200c1c584a01c2c0101810382d170 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 817507293 1250 817506043 817506059
    0x81306021b010510151803110a1502010e0105010b0309030901110f06101502010e0318040b09070c0b0a05070c02010c060e01050c03010f060306051f0908240f150f0301110f0a09 77
    0x2120848041d0316480b002c00030000039404234440c01c4404030040401d903030b290311621910740d02c440b07001071040141e4540126920381c64084c458070703000d0309600c0340d490300d10b29010700016a6407142040b0703e070400c10b2000c0030500c803045c280000d0110304a860706403140b81c00c0c500908581c1c00b81e5070251030803a101581244044074014800c943c18840010048c0d0f003440b4031000081d40303032540c0220060f00b142d11403905a1080d541e000202d48101c595460300d840806041c1000a8480c40040640d03159a282c07005008205400c125400b0600703609181c28043e02c00c586c80e01002030200c0200c00000da41c20070f01400780d5810410061f40c1030391441c001012155a660704102c0a42c7c0d107c0c032a1030707085981e040360036002405520030081502240d0800c40c1610b642c1d80011032402200102031101006108404100140c1c0015029086050412200018200320380425000407041c00d48600c00c3c84e50320f040080c2914290008081c0c1050100141d41328074411052030380a6220042d4180054001400410380740 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 817508543 1250 817507293 817507307
    0x1e050f06010e01030506010509090103120813030801051306031e060b0612130204020c06070206060310140f0916030503091f020a0807080405060f090907081306021b01051015 76
    0xc0142d4444210002601c01500103000140c5510304000e800c20815441e81c82c0c0d40c1c1e005008511400d19406100d4404a00502500024101010580c07001c000540401d81c40f291640c1903c1d81183c1817041c14080b0b29001c001000640c3c802403404107001c0103100d200e545c07030370100034035800350100f84484415042040301c1441200088040d0355450004242d14200c00d4200d40c28851020f0001490301c205101c2c61440c043c0c007215010010781c8210100011401c05000c84034400f010a94280036060340440e00b82c1c4808030040600080d000313040000b41a101081190003500b000d42c00d0f40d4115152070703040c03490722903110380c400901451481c50300010b0460b01c182c02003003091055002c2c00c80c005c42503654280c282e0142001341c50006090001080c01c2d41d802d80108009005206d10315580c280c54030a001c02e03440c00030000e0050041c07010400c00602c0d17220904c255030b541e2207500147c0d220311001d0365200d00c000b000e030301c1c901c0ca40ca8001001001440c1c03a90510581d111910484031052500008860390 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 817509793 1250 817508543 817508551
    0x6020321091207060e03040f0314031201050d030309201203040b07030c0f05060f01060f1d0f03070e041b080309011d031e0124081209030a061e050f 65
    0x40d40700321424410031490070b010784129071003801d02003690810305008600e5900690000c9151640725441007040016124140d41c113214440041c1d801c05c40c0d0309808042d079a405100d00c0e405009002100d80c101403290348100f002540c42400310840005c000f5052402c1840c0e0300103240541610607000202420000c01d0f54102d909200401d0714181190354111010040072000300c5490640061910000320148592840750282ea2a15181989071000c010280c0b00c8a03440300080c403145440040c168610041195031140301036038407001484910300400d2500740350758000c070204035242c0140310800c034000c00ca4060255454882c0e101a50301c0e440d1498492048000d454085103005001d004c4c10200d010340021a02c0307004090741c4860348001e030922050305c4142410120380e55580c0c2c402c28040f1302e03078201a0416081e2616a0805400c2040265440c1d1102104004402c004180384880e942c003041850402944410140000004000c0b4803202141400014181c82e0030000060203108442e103006e032003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 817511043 1250 817509793 817509811
    0x311010e2802150f040305010c021c08241203180109050a120f080403060219120e030f031b2b0203040201171504091a0603070b0a052206020321 63
    0x1030002080c1e5540f12a4003080101c4202c103030922000000c10400c0c80303610740304200303a005000c1409142500550b69101a031010041c405504c0502403080c180304c02d4141110304402060682c0044032000a040300317804444000d03c1d200c0010b805071458200301441071290000e880303905805448404000d61881a80164501008042444400f00d03c0c01d100380843c0f140144130081c0742c43d0b140c1d11210140c2e80b0641d881c01d0703483c01081e10328591540c02032a030310058040042c2000b000a062450a03224030035041000d00201001c008980301d4060b159513030104804204142c0c1d44d034400c2140840310211107441c1d41c3c10006c102d4081000031030060007203078491039059403042c1c0d40520200c60984100005040c840364072124805a5410740c84034407070918498000c01c210700040c1c07000900c600001c0c6008140d2400f0b0380001e03504005011840d825140d194005041541c1c0303480c400c0030202c0307800c846c1852079810f8a00f00c0200085907900407000301119021440703401000200d541803401400c03000c2d64180c070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 817512293 1250 817511043 817511059
    0xc0219050c13110f0a09051005090a05040605030304140a08150907090515060d0f05010902070b1024030b18041401050403090510050904020c0705090a050f040f0311010e2802 76
    0x78216a03070600030301e00420542848a08551548041608c1d154415103080200d0000220340080c0e191400800b0b009041c100d0701071125508090210781c4070f01541c4030300c001980e500c21f480700c519078034801404040c1c0061011910341081e500725284007807806461030084c1340110400420800e0b0240501c174800c502805c1000404131400c0c061004a6102c2040880c210b0303900c40400e4401040c5004460003024451000760301c07615142080c0c82d682c90003400325240e5895082c0f00708407070601003100300c5410030700300d68054460503101c2094000e0550031800f241c0c8030400b0000e400b4590422180c2c0b500039800b41d400d81c200119801c0d0180d00303d520503540074000c070700303032803410403292078000054810035038240340c01c0d414611a000464183c0e00606182040d0750002d00d000d00c01e5060100d200d513481303009010180014141010700506603c00584040d2001581004000900d400354100c0c0b095182400000c2020407415028161034181c40581c62a031000108004146420240605d800454004000803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 817513543 1250 817512293 817512307
    0x305041d010518060a12030512070e01031d0a0201031e0204080312160e090c0405040f0902010206060904080f031503060703060303080915240d050706020705010c0f060c0219050c1311 80
    0x40801b041100700b141000010410b030104450750002040c001c0300e0544030542001500000941a28603e6a081d1340007905010040255000000c1500c2203540a00b400903402007076400002d00d140c00c0c442d00d201e01c1d5000040c0090400d0002009207007134203054982c1d10154a1700b9420703044035031504401e18001800d1100200d030626015440540001c01c8904c414075241d074440c0482c003604c0660407881d43d22a599104c02065503014080c044c0d00c084100d0358200c2c5403409580c0c0d503456008881212030388001c04400903080f00c80c0f10320504d15504d4010100c401c03d00d007180300103018000900080700010144008603800240010300300e040e00201c401620300c15507800700e10f05030300c07007542200d103401100303004071060702da113070a8404898580280c02a040c3c0c40c2c105080a0715001d05544005d040064601e80031010440150003c159207510403404200b0f414182c90480c540303501ca140740e80a05452030440300400c1000650700c1d4032080c05490846007000400c211004860019030f4001c0c03190403c000003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 817514793 1250 817513543 817513559
    0xc170a030f0207081605041406060703030c02101e0606080606090f0307030812070306080a11011d04110405010210020307021c1e0f030f09021005070305041d010518060a 74
    0xe840744503560301c1298005640e039070001d45020030442d0041403134088440c050142e41814051001c0c074035910011140700782408000f00c0c010f0f106000014080584d14444251142d00c244a207501030324603a04140412a0040741204103596410038401516140500014206016620980c400c03c4000c14040c00e102e06613051124512030161516450701980e200400021a03003805802d9140c20240c0c90601031500d11000b60407114207403c407100a034000c2400d00001080442c1024600c6020700c2c024144d101c0c602c1400c0d002a05d030820003a405410414a010185103140c050300c1202c03001d074215400036110212031170807803009468880040c0c001c81130b54005404003600c280600c1c0d2261a240f0b11139a141d0490751031030402024048005198a200c0a10303840d07150140740d41c1d0440107030040010544030390000d00c0d4017004201010901c040850f241c03041c0343c0128152000cd1420303c20780355400d0103103d0100c08e10300b0240a0b4034818003020051541c021841d07106244103c2e80940400b081e6801c0c03001c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 817516043 1250 817514793 817514807
    0x16032906090316090b01200d0f03021204050c0a06030629040305060702060a05090d0926030c010c0f08040b010306050612011401080c030a030912030513120c170a03 72
    0x720341c1c15104440c2c40c1400451400403c0008208103100020360350301c540300040c400e0844504804a084280c80c00c2e1503000000308000b02c41c541241060560f80d80b2010303042c3d003e400740c1181000c8803581c03407041200f40319011134000d0f501d040441d004410700c0e4441d0801e0b42220704600500c02102c680d002e401488203603144000c1d0340050310030121802c0c140d40c0d6032050702d41103088401000503003040003401841400341c00b035160060341560242041c200303460310003840301046200e42049034102e4a845466106041c0c0e000358141030480580b0390b0f507000c0040240c0a80480c900e0b450000d40d4560a90802c140700d052407900903030340700c5050700460b4038503200c08011700405444150720114485e003e808070f01d401d108081d404002c040a1140c151301d440555410060030034109800790b0840300e003100c0000c0e40b041c1070009031344142d422000450041e08044905009405100580200c141000704046003101001d1110f28820b115544403180c0700d441462060004c90040e00c0107074450480c4c400028001c442c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 817517293 1250 817516043 817516057
    0xf050301090c1809020c0d05090102030a300207050c0603060d060c050f0706050403020705041e0e0a020301060308180a0e0412111c0e03070501020706050c1516032906 73
    0x42d02d0490b0f44110380f001c4101d01c0a5510100969a0020f68440000000d001880076000981491400c0c00800c03000030b9264442d6402e03040411036540310200400c02072404000c5c41c00b0303010040991121914140c0c000a5115070030a840749c0c41050135034061490601c084030303c108000362030706510b0b000580d160b2000d03055a84020701030145c248030620304030131003002038070ba003602a41d804103142c103260502038180b0660340c101c00e0082d4208003c0000641109442950300401c1510000ba00d43c042c0001a043c1200044002d605500342800082032290210150001c4040505810100d0075031108000d950fa80b00c0c8a0052a0700c0c01100040c08070745120000707030301a00c403401c0803804050041d49503418025004140c0345402d030180d05c4001440c4c3d0110291002c11000e40040070142d0030000081d40d680082e108080c05c01c83d001841d42e0005500380060001c1900e20300b503101c4030f0b040c03640c07601c554400c1a020711000a481c1080300e001201c00d40340180c280301000712030b13020781691307080500400382d1005e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 817518543 1250 817517293 817517297
    0x4150e040510050c07060e0c1e012d1412160e0315010915030804030b0402150a080f061806040c05090d0c0906080607021c1e080708070f050301090c 65
    0x55564011881c602a030f601c00c6900c00d90140da12011881c01b48200da03000320031848154050b02918807144c9400901c00030200940c00c0b143d081140c1c1c4c000407501c014164042c509070511a680703210400506900c1040400f006454004041002c04c0c2c0004490040560011680380d0102c00b044410380b1881402d006100c0398a48020203000e85400300e41340c81e03c2c50003410101d003031100041107080c1766803003400858664401400429446e584895280e0302407070001a000454150100e021076940c1c90f40400074072046611103855102d81400900040c1d4110f17161200c900342d050000d0761514204803070480030b881d400b80b840b50a88507401804004c2c030341c500d0a4000c0c4001006005490340c0d4498540d00664851002c0c01c010608082c04072081e6a020341c05050381e50310010500600903004a503c1c480c0c10842401c03024160304e9901d080701c1e074178240c94481c1c084041c400c000c00da05035030000c0e100b849441c40e6120f603e4a600d038003400300e4840c141071940700700054051005002c0264680c000a01042d840c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 817519793 1250 817518543 817518553
    0x609020409120c1e03021e01091b030528171c0f0c050a230d0e010509011103060d080306031606020618030a2a17090a0504150e0405 58
    0x69480755002c02c0901146030100d50400d10500c2000350324481d55000c0d14040b06000c0030100305a901a5540ca814122200c0442c10103400e0030602c00b00f540f012a105802080103503591401300074402020b103450000361940d01400012500d010807080e21400210350f16001d044102c4190b49544000794030702e00c08140d400d24200041c1d28a2901c100141a00704001440090a490300a81c05000c0720b0b0322810601c203100c014005d400038039400803246682e0707980c0301210b08560401e00030802081c0c0314580090b13150301d00e0602c09800320f00f015030110b44100d10b00002008101514040c20740c86020031504142c0c480385402420f03000a9650002d5904844003900b1102516041c0c0440d80d20f0300c003550440001a48490200701b848600700001c50101c0345070401840c541103480500034000d9010408500740f4082c0d0080c50a11001c41c040b1340c180072a0003d4508849020004041e034165203d06c010b18419102200041010300d01407043e4050064410f03030515005181452611f06d440008001303581c02c2c000c0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 817521043 1250 817519793 817519811
    0x50403020a140c0f10080f09030702040c1d04050108071205190f1a070e040b0f180a14190e0304032001030609053601060f08010b01080405030706090204 67
    0x100e21980701c2000d1040301503d03500e004a01444042c1e40f8002e40c051103120418103c0a015802856051300700940c1420a0050b907510704600d45180300d2034030004e401610340304420180075070000c40c0c0e030b00043c0380c00440c0341401c100404000c251107007800342001c160003030081004100580400c8119a80c0300364103403506c0825481c0b12500e16040000c05480d1403200ca640102008800e040218034507107051641440390802e96402042c46807800c40e01c50180d5a5001c40c0d0700344d42e841250451036404010a081140104c458440001e03040507503040c1040f80c2480300c070075013520180403c58860140003072801d20103000040b2010141c400c4640201c0320340010000880421107a1000b564083c074011407113141c0110340000142156032952040888e0792134142030048243d51210020600205600346040d00e80010703646d4030180c1c0646203000060740c078050001514081c0303034404200302d0340044000c00c4800a25801036030380003002c8500070130035001006a8000520160300038503030140068000198244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 817522293 1250 817521043 817521053
    0x3070f320a0c0f0c140118050d0f06091202010605060408060f0c04050a090501030b0c03060306181c1d010203070b040b0c091018141305091203010b04090e1f050403020a 74
    0x264070801601d0a4081600500174440c40641e000312120742840e03e90040c98518420240702c452034000c1e08c2c41150101e10040500c03184613500602150088010011a0f03024078001d0540030701543e800700135500b40800000ca600d0f14505543c100d0701d4190242129a441c0d1a50342074580c0000c3c000004072070107004c007154a840d010b031280b000d40f0078024005020b5045003032403e141b40c40202203044842c004c00c108006070f203002c10f1094201182500300c061110140241c181132821541800031030301c1d0071660000d20158403807108490400c000c14038009051440004903102e2141c05005407010b2034105c04074000400c606401544948242138850030320002800007100760a03107801c001c1c009410110003001e6074404e41e0091004040c424a82e50000c0c00c41c0340403544400c0b4180748180155500d10000d05480000c0c081d551032004914240784d901c2da1507051076005074026002c2d4500140c5014040701005e400020b070041c00004284c85484800440008100a40001013046086005146101000135 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 817523543 1250 817522293 817522313
    0x70f140403140304140402090f0f031515010e030706020706050c030c2406031f11160f1a060a1721032406030708040c0b03070f320a0c 59
    0x82c00c00805150f40b00c0c54074588414460314028480d21492040103d4010741c0e50300c0442c172420390426650118400d800000190400607045074440c006d0040400300b08440300340200c482413a5500340c0b07480442d0034001c001c4c50b546103910301804000d43d20521003070040c203019101415500d1103042c102d034a0b00c800c858003d03082004c00228104a4480a40e551004100045003154811400d800070440c0c000c1501070001d602450480907044540d84000e07403010140e0400c100e402c0503200c8410099100e9441c5000480001c4009007031310302c1ca103980d021a400840341403d0b6401083c0042032411030605000240c51000704000ca20000c4c0e11806d4407070340315003c00d0048041081c080110841e10b0b450400d14446115882c500c12110001018443d101141d075a0000d986e0440c04070b1500500d40e50b130703510b0454840c2c10709400c284a40400030040000c82580310400ca948044c03d503980c004410803002c21800e01c07564680d0503120700400d40341c104207001c80e00030150446000e1440c040c072080ba03081c0c80e044a00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 817524793 1250 817523543 817523573
    0x50d050f0f0313051909050606220317030717182d0f070315021b0a03030b090402090402130f0c020307060509060103031d060904020d02030a0e0303070f140403 70
    0x25003021820050700c80d2244460b00c0100001d440102c202203410b0400d000201d400c3c02130108040da40c7d400300d80c0903200d00c0155900300c010129200e07203024811011840d1440b442c07004440d1246121000300c80e0801c071005486c003a44850304c5507600104003640c3c0120b4500010040c40381c0350b10102c071408500b14100448007500042c074a1050350781d0026441140407103408100000385600c00340080e8800c0030006044011a500301a070803081c800401c8003503020b072096000440030003407480400c0401e40d401103203c120251080d18100030728190502801040101202c0283d8404e45540015026081815100e01000c903c84030000b80108490000c004a42042030035200603840880d4800400c41d00d44034054012080d00007c10140d032450b039000313040441080c040116950302d0f202c104459202c805c00c0da4a0440028803d41d120302404130958000e400468000078190b0909140f000c0010010080f0b074003940e441d41d20100100603400703080d1000100700714449241c480030031000000c203015190801007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 817526043 1250 817524793 817524823
    0x100f180b040c0c0507080303071b021203030408040f09090b070c0309080d0f1706060306100c06020d09060c0806010f030c140412030f1d1507060f05070201060b090a050d050f 76
    0x24620f9541005480d0070565045441365610400034003003102d41002402c1e895460300350703041801150303d10101c2d80c103841c060b001101503c8040309020030403501801410940d8600100181c00681da0300404064500c3c0d0300c00609041514000b10718001d10541c1c1442e060342c02070038101d0410340c0d2a5040da01e801c1500f041324000400391003000e0b070015800801e09a51140c0c1c116442014100880042c0440c4000340609100d412031080c6054028000c07c3c2c0d400074250405011502c80032200030f5240500b5641c80102c40301880c0c243c28406490240c14458000c500c180d40b5260140d01d040410340c0113013103c0b4010424840c024640004d400c0c1d03880003d0020700708031045103081080c0b0b03260152181c1c111101c3c1d90140040c54200034188a020040050f1030401116451400c90f251581d04a1070b11900034050314035410110400d91111032a0009070240d40160b0003000075507520004118180240200260300c030755201e608202c20f1801d0302e48502c506000d402502c855034045a40c0f640750560184203130b01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 817527293 1250 817526043 817526057
    0x40b03061207170f1b090907091118010203030702060106030b0307030206030103050309041b0e040c03141005010f0905061c1103040c1a070302250902070503040806100f180b040c 78
    0x240e403030f0040c084070800312a0341c0c004002c10b280d282c520080070300400d601c45009a00c188005151030000b00000002441c81070020461245c985135101840c0c2e0020b407176403120342e4840b502c1110360351000003200e03c43d0180341d01a1100d80d00380701045010700b41d0041c2d1140e0510a81001101507038035000194000d501c107100443d07a90301c4032014041500e00d00300304d10706000140c8002d000140d4119519440149048a001a883c149421305600900d1120b2100c47c44420b1031040002e20380c440d00f8400180c9000b6240c1c4c401c1ca8600110449144046000b41a08003405000d0210b4850f113401300d103c05501d8400f8040b500c0c00d05481901640d800455003038540c5111124200592083c4401100d401c3c900d04a2861428a264602a46d9410b280003440802c030760001030455020740d1003521101404101c80705555407021420310b03940e280c00038042c0c00002c2c01071501081d08140503400d01400c6449011100706968038088518200c071b14140c61140b1001e8880045882c2a96144104000c0302c1c040d40b290b070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 817528543 1250 817527293 817527329
    0x51515041802040605090408160f0c121b060c0312110a1701061419020703020907051b01060303140a02011503151b0e21070807081011040b03061207 65
    0x4020303100245d115500500514083c0300124000c001120b0010306001c0b031203134050050b031a100d03000b16405403014218103400480400c0581078120340e201c2e042c1c0140c034014010030f164400008104030601c42c003008208400220000680202c5100581d501483c800140c82001c1d01d1281e50140d00115110300050800c2a9241200181c00c0103140902082c0c60540d1600d44030540344203480c4a1104480d048a405004500b060b0344200100c0025550190245115061a0390094199000503040c00041101d081d640810040148521005c0701d4056031941000800d098201c0c580e913220b07818041c115520b0b00140079191107507414200c002c510407160f040b940c4407503003251400c4a0600740c1208440410428142c45654050801761071408110350091340c8851001415102d084408803040f01c6c0d0080c1400020000c0c0b001c1280320899030b0704000c0d950162080d842a00440e040c0510b406c000010a01c402c0c0321488240f400b17541c0c080d034003402008180381c1444640e803800c8416400b804041014011030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 817529793 1250 817528543 817528549
    0x1120203120c160e10050607060b0a09150504090506040b180109050309010f030b0a0e07052203050606240a0909140601181a07051c021605060304051515041802 70
    0x103001c000e0042ea100c3c05c08458010b0810380a11a0a10880c80450000c0500000340e00c031000e0301c035004001502c2141d45400f000054450f90751424550000c004001490b420305000b420b000c254000081c0c91182d640c0da960151400025244120500029811404049091081102590042c4000c54403980f608000405100017548004201418129500e1280d122012a9415140030b102d80146940c1d0301d5000301c882d0700520801c04601c4408250380c5d04045a410511402c0d42d004a003512200d0355600305012001c004803070b048140220507031014900c15540000750101e04010715000c1480c0d40c0d15036049041d40d10030725580001c45880310900000d90782003030448000d040b06501080d040d92404425641c0040015041e0840801c0003590302e0802c80c042c820042e005621141200d4144c041460007955102846140002c0c24440d94000c50285040d50540e03204580c06802030810a08410500381c0740e0001801400180d4000e81c02d0003043c1da9140102c00c1d48510f90444007086c03d14038010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 817531043 1250 817529793 817529833
    0x30c04020c031341040e01020903010204030303150e0f0f040c0e190c0e0f040e1e06040b13020f040c09151110060e01032310050f0601080601020601120203120c 70
    0x61050464202c018241c8464504541322034440c0701258000350101403105050301902c40c0007109585540700140200416070590b010a0104030b41c5424010700c0c07a2111860002c0f8141602c11400c0e002c1044001640c1c1401c0d42c000c141d203c1d2003014203200280d52035011000c290070594007035104102c250104100310005201b0076590001d03038608401e4070088133010900c03210640308214086d9072511031601d00c0000030014849100500400a4801e5181141c950344a00b0300369000c9411101e2035020a0042220b0b4099900260b0010f00c1300c801b0178542002c11004020783c01d100020720121480c001070032a4001014003a4800c50380345e0700514880d4004180c18034000743c0ca503084a5103000c400b4020035401c0c044032815654800000522010350b0184034000a0400005112902c0781200620003a040da80040f8001c0d62121142c200c00d032140401581c1c1081c049510380d00585c040700040248580b0030120280c6103001030191019081504102c611517031001522910691151710400042c0540c104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 817532293 1250 817531043 817531109
    0x20d170a1d09040c120302030903030d0603020307080c060d0c0c0501150f08061608130804030507092a0818010203011e0e070e150909092a030c04020c0313 68
    0x2e100b0b4034501e40750340d9002c0c082400c2d0146002d03040c44101d2600405008200301c6080c90b100130b0440b5100c45403418668050903150000700e020707026144000400003c009a81d02c5620001803409003000001e40350640140040d609040412015030340910200e4000e20490b0804008000c98080450500100d40c000c40c2d0a640402c1182d401003040148242100442d800004018545051113444104002c03520502ca01805420900c1c001070001c108200000d40714102c0d4001002408009860071900d410400b083c0380c803002f40940e41b05194480341c490210203500c00c28151056501e041c81000d0310b82283c0098101030b00c06103605442043c01002090017500034000144c401800d031a007110300130854408107109501070440301081c502d903e50748038143c9e1054400602030756114039004e5009691030035284a6203044042034001a5901441d00300d071090b01803000740c024080d1078004024440207504c0700021144500003802844441a18200260010481c0142842020000148841050404030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 817533543 1250 817532293 817532299
    0x5090117030304080a0903021f02060a024b1e21060621060f0411090112021b150601080f070509030a15020403110d030c020d170a1d 58
    0x619914803203000104036544181d2003450142c642d41107400603184564507800080d4042c4001000f0760385148004000280c4d0f100c158221026901c0d41d40b004003c0b40b113000220314102204400121803881c0300c4082e43c02c40d641032210040001310b410088905d96000321191412904000b6090a03501000752506441401c2d08007000d00d03141e28840b20814070002542d46038080036600300000c90680d2a4804d8900060650075601d0b1841c50480341d440040404075611403040840c50807103801c84c1410702c20a8002d11001111170f10304034011006484441084601750a1039400b080700342d40d000b032807404415000400c040100386007640c1203403481da80708000b05040d0412050104103d541407011400680240880c11b017555620600350202c1d0901d1001d51001e400031140b0610705c1c0700c862441d40104226405400204054244134042090800d40788070054000b9144200400c090300d02611804000b40c4204214907484540e100e90f0340e669000320304900c0102d5000c800c8032541501810f4a000c4100f011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 817534793 1250 817533543 817533569
    0x1006121a0a0f0812041d0702150403030204060323180a050f070e07110307120225060f030219080c07061505010e060a021e0a1406090715080105010e18040c050901 71
    0x249030001864003542e417010011b030580b004a10f0140c0280701c90207030000404000310719480c1c14100035000e0f40c0184501d0000a16028103000302d0004a442010340f010050003031601a103d844080104c00244004041c07a80200c40a07040020000c00c0004104101c0b8006070007a54034040c1e100c0039508000303025100340801c3c0c440700c4c0485003004c000c503101660b0000c110642c5858901d0220b14249144101041010f2040049000045100214070440c0c03d20b5485500101003010b0440c140d00072500345c0c40078403602603110b001d03c9000d014051f903c0b440a0a20504100300e50b1101c600ba0f5824280080300305101d6401840b05d564400c00c42d80e281c1c2070589403c1e15008680400a681d045160003000143c8030040c42e025803410141700c405a069000800d4a600c01400c420540c1c64031001d8808044a2141d82d10000b012201d0070894207040810f525440350320703840c01005440000601d102140d0042407500300d950240100420700d4001ca008200300054641040244901040107800844401c049 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 817536043 1250 817534793 817534799
    0xe07080c040903050d140f06101b050a02091905010501050711011409060a110f2b02031b060a0e0c1018050a0e040303051006121a0a0f081204 62
    0x100052810340348105880014001103035040c21102c0d0300407540d82528a03410900c5004c81880c01c41c10084c00b0b100010350398070268503140204000078a072088982d01003070015202003071741c041c040d110880b100e02405c02d0310f107415040d900054400a0481e074002003480903503001034001207a4891140908008e00b0401c6c500790b007a841d542c1c0711900f03004083d41008140724501050101c90415611061800340c17420743c8580c00d0300d00240000101c1602070440344100c0b0503985900800041030010040d100c2314115900b010092135103501e000700d031030143c1944420003015540c8210040c1e10201070003044090f00440c1002070581c41907402c0d40a03410000d51001080a45a5980300d000f5000011039003041c0020040d2200d0701015610183e024961104042000154484050185600c00c0b84642d6040015954121611200e40030301e0280e6400218a500d5101c25450150300c0848821703908051030210903055000640120801c0d082010f000d048070104114480c42004070398070468a440b54603003041c1c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 817537293 1250 817536043 817536059
    0x31b0302090a0c0905040e010e2104050904140a060506030d0201060303050324060408060f091212270717030306090601031805070b120705070f021306080f010507030e07 74
    0x30020308a0407502d076a440301d072003c40c0e0240107203000420700070340140184644400c0140c020192202c0d0b000c0a4000c00b5040c0b280440c8034040744080010020a0b50b051a050500380414039400610407a01001c581c040c00910705402c02c5040d002a105082c00314051520790285800d0080b000841c509583c10a0b0062000940045c2034130342c0641200320050b0b07505c0d101c40d40e101c0d003038488070101600600d00081c04500c004002c11002d22a50b9603194241d150b41316010304540d1903030700c021031031035400041c000f882180814111464100101c0b4100c8010380c106a0350050800c40f0b0700c0d1581010f035204000c20003800c0b000d001c0c004007081a041c065425460a40041050008020041410159906540d48000c41a0150040c880350804100d525494682d04d1543c1c50358003248901e601d01d5000800a0042c502c03e000712015164424111554a90542c0c00d2000c4442d0800349818441e80310039010075040810000c0000042c00d0000102c0c150400d0b560203002c9038000115081690490300042c80848 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 817538543 1250 817537293 817537309
    0x30907060806190e0603010c1106281a0f030102090d151509051e040f03031e1a040f060b0406230c010e301b0f07031b0302 54
    0x35001d09042650382d82c1d8a0008003071001e8460b101d00c903250034002c045040c0010701c80b0703070f8400d0000781e0080000c410b07901415910f50503284a01d518a6000c4400103004500b20021103035850020680242e06182002419042d80d03a950300c41000030751001e54003280303807500711407804660314158021850400c000011601c0700640c03200c05042080715040d200704622543e401240e190020403441c00c1020f85945001c40a05002d0711044040c280030000300c1d14406480c2c00c01c90107580d000340e0000e5a10300e81c1d074080d0081d084150900a000020050481c002c1c810b50090200c02e00d048c50710310160107031200401c012140783c080742c84001ca01c1d04038140120720840c011134082d11810300300303a4402c1e103022401240000c2c680c12500860340c00812050454141500042c60b5810201c090314071141e408080c071424120410b40c5a00002240300b400181d01134079000600084034007125000510709036410091900d00794102c810781c03550108100b0014018420189501020044101c3c9110b51442c0c000503e20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 817539793 1250 817538543 817538549
    0x20c160b0a020d03060b090d0f060216030807030c0e010c03020f030a0309060f0c2007030614010801050f09030301052e11060708010b070602030901090f0302070609080c030709020310030f0606060f0302030907 91
    0x100441d08003681800032032800320400d268840c03401e563360b15051150451a04002a040340400d942501085281e4040d008040542d0169643c8a900340c603030707000440e180c0118400035402d45c0a0361110030400201440108401031041d100810710401c946412001c883c00942c2250081c3d1412100702107072580700030185011a0800410300c0b005400c04581d03410600b095200a00c960f00c2c01d510124120341c0000300c00e0488030b800000308000d54400702c84c42e00b65001100c80c0c01450b002000140710b20314104d80d9013450601991302072413002040d144200c2c601c884041c0407001150400e440c0040340d440820480d40e0050b0075203411011545012000d500b6801a044018582d50700400000c0090000f54002d05a050704076030030b0069003241d403c0203511180940038001c006040040041900000010a00d09500002c0c0043c4a403505d0700810000940000d0600c4001d00c10347d0100001144142c1700010b912805510700089452614102800e0100301c00b0034502070600600410001a80120326030f411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 817541043 1250 817539793 817539799
    0x61008150a1e060602150f0601140a02120c030c0c0607031d040902041a01032007020909150901020a1706060702090705040510030e1203060a09020c160b0a020d03060b09 74
    0x500102d51090340d8612002e840d28400305468414006822a80020800c1c0d545c000030800241c00c1c0c84188100c04104411585540404c0c109a80f580009540000030314004000348140e407140200da03d140d45a035805113080000c5a840400e8504040c0c00600035402840300844030a032810100d0b950180c01c100e842c003c0c02e40a10f1036108841c040e51155005802100c0d801002008850309482c10781c0307002d0035118007090019141c040c80c11025407604400c69032080c1044071403030501d40e083d800c02820718402403503007481d801890500d08800c200c140351107003d0007a032000540c45010034907008142558802c0d8150441c88003405103c141d413501411500f503030fa010b0b5484201e654400f80c0560315481365501c03d80e0005448050814a15416482590500d6144042d80c4490031041e542a90341d02090702e410303601011014080001094603802400700c0c20040e01507800c041112411f514450600350b1029071004000281701c141c555051043e089810700d1801d08000b002e090410845075401005c0d0a42c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 817542293 1250 817541043 817541051
    0x31e04051002070605070e0a080a080c070801090b040605071701030303022119050c042103111e0d0305040302030a031e06081509010b060a08060607020909061008150a 73
    0x20a10006106205440c85000300565440c1154507241d0002c01d0308641c56030001c3e10a080850151910415040c102d0700c1071001808611a5504d46084940c8144004400e61281c50000030f411030082c01440c100d50b000381203003500e915190801609540000700610104003100030644009804c001c2404d0650f03805240c016240c601080150502a00742c002c0d90203004aa8006c0060031071204045141c103418140c02400640c8501141000600841c041ca801800505000c0d4030229404000dc10300b0a000307151032948500140c0360b00b4101003016400000955804030810042d200c100220308003ca010301d4108018038140c1c40080d00ca004034051b050030182c4034001401e095550105100b44c14200901c20400030360350b030317045030754810705400c03481283c41d07042001603e60302040c8a59592058040c043e0307480c0ca1035596040f544100d004042e1030340300009200341e00140c0c4400d261688141032803c014241030601032903440c850139003980001c0c2c81d80e0107000c0c500d21444500710210b42000300504085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 817543543 1250 817542293 817542301
    0x603030f0507262713021e0306062106010f022e0b0402040b04030b0112030c0b100e0a0e010e3c031606060b0930191403031e 55
    0x1000c0b520401009a03d04405a028020002030b9003000001e4a401201c95000d030161405900c010f9007e90b0360081011110f0f011414030284041c002140e000400410140c0360544280400010740e0024000715641c1e0845400c006680d6040219604810701c0741c001091032200e00d10b04516944130002c0080c00540f81c00c040b0700c8071145603810002200c1e100410554859481d25003090158010b844165a194082400098500b00d80c030210340c3c0706501035441e41000825a160403903295005032410340c0210300400300017603071900111141e00030544a1008610f60703c1044d0b5540c00d40748100111031441c0c0003001403071440c070b9408071502c200d0440b403809011001c410184605210310070b40422101030000141803042103180810f40c40340c562241e10100300c925118506079101340184002c417030700403280054846640b41d400100400c0c0c0c404581d8079119840754408450f0500c1031884409004c40c02063b0310008000c0112031940580c02490011400c5d032510700206a01900401a4201d0141001001c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 817544793 1250 817543543 817543613
    0x9090a0513062a171e01140a0906170f0705100804061d03070b0a1e0e0c060c010605010305010b090315040c1d0a05070f0e1306050405040302010603030f0507 69
    0x80da80c50860301e02181d51529040d14040e01c810ba4907040244103c1c4d40c0b1000503014070048810441c2988403203d4040c0311707828030b089034240320f0350800742c030f5841020504001907200c0a03000c0c0801504040c0c04030b600c000a0590464030b40091104801c80700e8028a50900c1152114030120240101600d003d00c0c141e00d45040c010700420f44034007484202d407448410000000c900000804809115900d11100380c1d40c0c0e4004801114244008000782d090140c4400f051280c2540060b002035480b0400e641c14040e100d40042c1e09584481c6901040d651215400c00003582c140c850380e801040d0403610030340380c180342c0400207032a1045402d14452416500010078188010311003040d02074101c19407103001354068110b428480e6030341110b60002031414400000c8806102e11036894040f070103a1650100310300880104122040000c070070f10595580d0758800500782e6031780d02a60f4001c3d07001b500002052411402c0c018551000a81b092081c010100318502c0060000320300f05010320200031284140450030015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 817546043 1250 817544793 817544831
    0xa030f20180d030810090905072c04060b0f04150b0a020f0a030504090e0d0c060b01031104030f02010305012304020d020708070b06010e010f021b0a0f060509090a051306 74
    0x100716000b04103815100b0805410074500c40c051440307070561000450380c1d9100202540e90040c0010125003114501300b041142c401c2103010060b0404406281a42c10100c010711a103c0485040e620143c40304030810103402d2000180c440c41b1410b980034041c1000d03130000810140c070980f051104103480000c0300003c2c64400e200007500035840f1000d0300c8100c015428000d050f40c0082c043c4103a52482c01c6007915058600040301c0040c02c0080d26150351041c56074031004018403240381d44134141511580c10010140c0c044000b400514482c8400c0c1882c0d002030300004044a0058201c80001c0c10100820307034025404c504001c040201c00c540159844450b40141d0020340241c007000be1000002080d02e90801c5451041217200c0c04007a41c030010710000820045a00804082507035025030440a403c2040c8201241c4404002002030031340100f0541c1c0d9041420007403c075500030b10001c0e0000c6880451441e02034200c40c0c0012190b0414015400c280075510342c00d5220303101c02010141c1c0d03181102c09038454401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 817547293 1250 817546043 817546087
    0x60c020c1f050f04060e030c0a06021e21040801060e0702030f0f0d0e0102181f0309020a03140f0c1f0c0204091b0302010305180c130e030d020a030f20 66
    0x8030f00c0d1500d60310140a0007030002c07540340b03c4c868000c4080010b1241803a824185c22207280d0f03402031492110035803080c200e02c0442c0e50080e00502031020788a450f402c000307100781580710070034440d50744d140e00d091082401c550240c1c1107030781140300000a1200c42e40c0c1c00810707100d41001402c1314aa840407030f4811003940d4451a5010205142080b99102c09a84103501820010310f00c802c0c040d1103216203a0070040520480214641d4180d00c0205000c1d21314465031008121510150501e02101e4981d2910100c0b6041e60030559065845001c0c4c0c41d641d60401e0003d10001201a83c0c81c88115112141341e13282401035144803010081c1600b40790f020340d500c1d6006044003e4201d0400c41080d070007058602c441e031a1900041e80424145404234400d04502e032404202c00c2c401402909818250300300300f1031009504d200c0c3d44c503401d403a84145090080c00348024440c02051400061b034440c00010007400381c50b80741c0406204207290a810808242904104c0c00e0318517090076138990760395100a0401010002c00c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 817548543 1250 817547293 817547317
    0x206032203030204050103050609040309180f11041707030b040b070203270a0f030b070f0c060f090c290c10060803040f080303040c050126090604060c020c1f05 70
    0x61401000d0503010f50090041e210280e80500c00b03640c403201400006d1b82c09a03002000100d84d01d01c00c0000c1003030003000c0c80b01907a4401001c207400058051003025110700e2020051a1a00060100a801407010501011141e44000303080002d20b507441e80c0d030310b03039000030000f61468181c0c40c0000c20780b62007881160028a2000b0200c910042d03c00c034484c2404180801c1c15005941080300400d1002c4603105032000c50358060101c4129a4030550f048481e8043c0c07903080e80a00448018a40001e44640503c1c20030105820f00080da0005504103005015142c1d400784400011625246510741d40c008504004030810f80c944581d80c1031701d000c505281034071050307a039401310780f91241c0414050400b200900880d048012034002041d03c5940301038682c801581c005040102c8180100801e5014a602502c000c0b1232110030005206c41e40d20140c1c11460455540031903400c030340100030400c450380c81000514515803008240407414800402e1300301d42200480031001c2c1c3c3c0c0c0c144151045200e0340407a4402031000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 817549793 1250 817548543 817548601
    0x1f3f05010c0815061e040b0408010c02070501050304121409030d051308010e070e040201050409050f06010f09050f010c23030304170f030109050405010f020a0c1505010e04020603 78
    0x1810028000c0881d03a910310009038010001c41c0b140c43c1c01103165800100c0c010f03d620b2030111851410124a1880c490508a510050000145d02c52a200280005290300c40020070800c440140003800c043c20340d00000c0c113028040c410b010114280e0078000148413500d00705040200c40f0000c03035010f1402841092585031048000b00a480760748800903118946124255801c0140c5801c80c00e8242c0700304162102e91030340800303c100140c000c2030070700c00d808c1401810310519190300c0300551310586108460340401310f51001e041c80300381d5a1000d0f100b42d49803590301d0183c0740c0703a041100050061060105840c10041030360700010a1000c2500074410701c503030001c40c0e034200c5864903204a0b140d030011107083c2c501151410103c144400710f842120050381100608618607030030700101d00c00416007c4c0042c0d03010742d681d103c4100b1040251000b4000c446040e16a805041954070700000e081707282410340356145040500400051840c0398035260095070440e41c0c10b840ea078841c0c08440d01c41c10b01030000c081c2c83c03101e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 817551043 1250 817549793 817549919
    0x40608120d0b0306041a070513060302031e06033c0604031b0b0c160c080601050f030307020913051006060917031603030b01030905030f031f 62
    0x400e10040405154404080c44160340440401d500c2c0e503002c8401421403c034049400c00d007500312501c5180d0040007810058240000984441507018898002c4030200e0790010921025440344002c0802203400030741c0b4000740d46002c1e0003181d1030303040c4906162100301c1407000349061048800c00340c0d0150450920000c074010100d2030001e6940b58160742c1a8085102c0000145081107074441c8280f80b2600022100c000361213481c2c1060040d8460824800340c41786c1001000006045501442e0082038084001c16980d41020200030500d1440401144240d00030080b840060f2100c143c02036001d52001d1002054000c01e0511030708000c810640e4549007890010082039198100c40e684066440180c503402d00905c018203155134901c030b014500a0356070b4001c4900d0001074820f0300000d400600c10316001c540d66650f981c82510b541c2100d00003160344d10000c802c00148a40a01410249130307480d0300c0541031545481c0ca890842e1080c440702c03030380d600103203050404819001420040da0340b001881608912403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 817552293 1250 817551043 817551073
    0x30313020111011806060509071e1404050d0506070305090705030705041802061902010c031406220c08040203241f031217071806050d060803070507090f020a0c020f040608 75
    0x147e015151150000a020a0205104a42c03211320001d00c0f00812414a090100542e90f90303d6031501601c60030740402012403907484032502d040e00c8038444c02c000c0c00103052402c0085d040d17403001070801c0c80c2c030b52050104100c6581c1c0007403140201c40054600203000300390518628442c030030f4071030060f400200015482075040c035403480307104410190b0307402004469900300c1c0403000d6882122148901c1c0c1101000f05440349814840200038026404280c02900c880560f0303141034a107040801c0e408110b0410420042d41000d00089000d00d1040d494040280c000340015207400c2c0300585080242e80e98512041a002d000d04441d90165801520604500c1c1c11101c000740061a5200440c1081001001144526008d601d2190091695040d030b900a02d04080040344c5941044154800c1036131589000140c1c014240000c00800e805000600b180b2070610400e0360941d152983d180302e81500c10403003c2e4440d640502910100c0e50304884030200d01000a000034003030511900042c0c4035000d04518070201c40e07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 817553543 1250 817552293 817552301
    0xa050601030b0718060503060f09070306050109090606080c130f0927020603130606120f031d060403030e010e0306070917030c15061c031709030313020111011806 71
    0x80c41080e0b50046556418421514041000303e00584010320b41000e110442c080d8006d1544584068040c1d8030000c1ca0000142d03010710141c3d80c01c4082951100c00307015559009640310040c0101c000148030302403420301c00404110008124494032800810400000c90240b41514001d11b1542002d8640c1c0b602c8100c508010046031104a1002e00100c255020058424502400903500101a281103548400002040540c8040100e5449950340c02c0464000c200c20403d41505000c0c00010102c20468034001e41101303441c1441003000b01121504141650b10a0101c805882c0e0506d000c01d200b440100050302c0c00b8142071719071075060203510704110750607902c805801304507900009070382e0504034682049034a911400301ca5615641100e04040115000260180d41000c2d020b4220f07910f0340e0410001c0b03a6001c90304078041f800107030001410114880c81d010903d82000100001e1482d60a041c00904040107010100905100e054220000903080a501880803c1c0051010f00e0001c051898244010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 817554793 1250 817553543 817553549
    0x60901020a031a09040b13061802041103040b16030e01020c0a0c0b0702060f0c070b0a020309040f0614010309080915072108132102010c140a0c15020405030a050601 72
    0x303140c10b6044000300c440f0303506990000b0000d03140c14265103440d21110b202e07040c001c0812a0801101e110703000014030391312a01d1000c9880052240b03104510f481003000f920714503031560703403000c41c11301c14080810b15056400d07400c00300000780203401032041201540580301008581c201944080380c41400c0b06d2000c0707000c2012611131141c080000d1780f00d0907000c80034001c03502c01030b4000a0a000140d1080c03102030062003400c01c601c003150040760759401d020304a513000b204050016000070400000500f0305000e03070301d017215248205110301030400a0040c100031541003860304040e140d0259506005d10034046a144410242c115280d040f1814032151607640319840132544d81c640c20f4031400c00d500b00c2c0c40101c4120f002c59900c089030317604c440d00050078100c00340350181c4064015a11517003841090310300d1b1105e1108981c00100f0380354000c3da006003900c081c2d1180f4a1130443c041118508081e4010717900c0104a900c000042c98623107028800c5802401360b40c01c07594262054400c81300a0140004000d812 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 817556043 1250 817554793 817554797
    0x7150c0b0f09060109061401050309070803040f0e10061d19060c0312110a270f0305010f110a030e01061706091015030308090c130615050705030306040504080c060901020a 75
    0x99030b82c0c3e50100d00b00c41c0e0347e224600451311004440020303988520700554000034a80304035901561220102419544280d018400a1400c031a08001c60182d105150f079100c8034200072032280d2450048098081000c5c01040c40c040000351800e401240e0b501c030100d0003914010b07050788262030348410000c1d00032000c2007000d40c041522126000c1400c8018012034104503034091456003401e0380b20400750740742c418010076440d076070b1483c59588420a485449081c001c020828280015502d0b500b4041d00715000780c0b41d801c1e803050a201d142c11400d600c45007207072508a000d20340080c01000f5000136a00400c1c407504820003250210281444050000500601585003a400c2e60311000038101e03c1412520000130702d412640c0e403403504101207402800210f030301500c61000e481c0c554000ca80000c505201d40c4007030803c41707980c0700c40900c5094035110031000703004002c0c1001c80c50074140391141c0d956400000c1519100300c3e2900b000600b0023a03042c0030b035039038098450101c2c2c9140c00c094803064040d40080300c074080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 817557293 1250 817556043 817556053
    0xd121b0f110f07030b091e030304031d0a050f36010602150415141e01050d111e030d05070203011b050a030c030216030810050a0807150c0b0f09 63
    0x6104071020855054207622580141451442d650741c00c1140c06009000782464080c0b0103656241c20310004244480d05c01400146079240761030301d40a89182060318030501850001e001c1000b2603141c0d1840c20f010b03a04101d5840030281e59420001e81408421031091084040b411548840e030710728a003603100541258003840000342c0e2200403c036601d07115805146503044c0035001040201e04e58002e1400c20400310040030407600c0722a4400f81032010191404900c80da0810184107002071542d034198050641110b0030780414103582c07101c40c0c048160b9803402d8443c2591511041100342e030700090203003010000c2c0941d50710040e0b0f40c0c8081c2298111a100f0b80c025400d140c499016103080c40001d0300502101d44490b400c01c215641d00b00d005044044081082c1039003000658910200c0c0d50398401507520070341d1017408920b440c14580c100a405036000300d0141d40301c25014010650041542021f60b07000c08001d40e02020700d4072007111800f02e111005001d8001100900890f1314280b000b1a1289500c003048134 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 817558543 1250 817557293 817557317
    0x1003050604060e191e0e030901080108390301060b13050406050d06090f0c0b0c120304121b170702120f100c26010e0106020f0d121b0f 59
    0xf20742d100044814804072003010442c94244121075200c201540b0080300008015000e40c01c410085550705000c03a07955500116a040c465a0310003061809011004064007404000e00314440c544403001a0010510250004044140b410703011080031042d130090007030044950321140c2107150782c802c0402031002c14002d02c1c00302e241d00b05401200200d6030041c02800e080901501d5040c010440d00800300c0360011488030220101e107400d0707100e602800210601c0c41c0d45d140d405c0c0758107141544030020b03e4003c0c0740070303c10800414912060110314601900b0b01406000c4000b041c9055035a407200010031401c1485c50030f201091010001d090030078804d0365045003100c50405007543d030741600d8105100c550b000c0c00098800f160300d03030000703c1541c4982c18a8041600f40e16103189849004940305c81c40051001c00400c0381c0c099076800b56004100500140c50300b4026800c1490b1180400c00201c0140585008a0f1041c1001c95020001d0360541c5100844840700ca01c00042c035001d02c102d120030004131400111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 817559793 1250 817558543 817558559
    0x20d1a0a1409060d05031201140111061302012d0c0606080303130809010905040e010506010206070804120e0a05190f1d15150310030201090609060813020f100305060406 74
    0x3070103440400070594242680c0304001c01070f0000307100d01d048500340020701c40710026403060a5801e02a0460440000c0f03e410000001081d041c4155130803411a44036800703100c00e0030420680501c0326902843c20080039412420240c0703811a2002d40744064000841e41000c015901801340311186104030300504c5181d5480e68195a00c0c0025281c3c00c6c0310000d440606000a043c000c0140344500060603c01a504d503070707100203411120344422400580c0d44a4080000d1580d043c466260722480b41e05140d9a00d041586541180a12058104082c00a5070345481704aa580420701001000010440c07500c09600c2207000b41012854860000510703480303000458503104540a0929090780c0505806460796164200390540d2403200005402c1140e510310400003141c01d5009610030030160121445851651000410130341c40c0783e1005082114100f000d209080e4840740441e00a8003031b8400d400114102d000080007294800c440603448401c108070018540d416400040c4542003c44080160a90328008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 817561043 1250 817559793 817559819
    0x41a0c040605090d0501060914190c1e0e1c1401051605160602041e06082412160f120503030f1b03010b030a0c1107060c06020d1a0a 58
    0x504008202c0910148195003070481452104034002c3c000400c009951b00e19490440314440e000b02e40b00e10001c002c00498407039600c1048020340e45500d08000d0900c512034000c00c0030720401030100c07000d02d20500011080c2d01c218444c03564880e0007810040b00c00c0702d194105044640914040340c45401400100c40c0c602c0703044c45801e00c00c0325420b101d43c4035034840caa0b04403007130791044040c007a2100119030940c0c0801c90610291002d400d070349802410060541c00e80302160f485d04c1c8c0c0b200041105550400c4086c41c44e18401c2508200b1004110026400041c006a18031541c215a0851807040e500304090684802c101a0119107013580390030402c1d40c0761030305c11225401407900500142c0c0100041150311a5400d003072a404480f02100c0c1c110750f03c11148400080e402a403081c45120130100510415041521074800540d44500701180b9041e107282d11140c0b0b601a03403289074103008070070441c1c8084c800c181e0111000200c1090040080c80d4001c1301054404500800c2c2ca800707040d4202d07004c160011074ad10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 817562293 1250 817561043 817561049
    0x10903030206130320031309020711090613050f0106090602030301030b010b090a0306090f031b02090604020d1103010e09070806090309102c090c0405090a0209010302090306041a0c04 80
    0x400ba00302a075503c000148180340d2038008804000b40121011500c90401c3d54420a917905e500c099695561071040300b841344001ca402020800e032042008800081c0d940186881d440010707900c4007090303503a03030000483c2c0960042c0c880c480981807400300024013030500d0f040c03810f8030a40d03140c1c0c440c1903403070740802c83e9640400d01004080320308400045c011220140098014400000c008c0b090300303070312542c85030141c41001500701c41c40b8014000c600105504008022206148120000c000c0b06a68000407181c18010300898001d40d4002294103080c442c50304884c25a010941d000e41da2940d4030955078240c0c0404550444280c001d034000801c1003480440d0080c01000ca00004600344042e81d410016001d0000b09a1418803d00b491080d0443c0c91251000704403803040c504100c42c100e42d44081c410032490040481818580c208018002030f0f51f1108043d8100444940c01030b11a0b2040d40160000d00c9040c40c81507152003543d04000c10005620032102c0c40c0c500c00106c0e022191a0028030312020301440c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 817563543 1250 817562293 817562297
    0x90302030f2a040e031c05150d0311030912070305010b0301050c0304120537050a05040303031a0a2903070e090a1d0d030612321902030c01090303 64
    0x10080030002c10358090b0610900300d0081001a03204584002285158050942403044104c101d00d4006201194403815a208044480b50204e404036100051280800180e0050902243d001a003503001d5040003600d00f4040080e2900044205c8104016541c01d0395100458466080490b141d94508043c00740351b0140c070b60f03450114103540b940d0f96020020b0b11949250802c001040c41003c8040c0c08074103080102c03d05e4a000d40c03440b80d42d81d000d1100d0491440e092003007800010800e000c1d07000e9200c0111070460b80c2520740004e00002684071030300c10b54048902640d0007510f0480210348140b10b128442a06282a4050002803903004042d0301e880c0002c880f880003042c0109600811070508810310360b03124408820028a0700c0c070740c0360a045070302c1d0710020902c510b520808942030050342500c1100302420a034901c280362440030740d4a441506240e10910b80c03502140703c40b0400030007450030812043c1c3c1350500139100019101580005407100d000d4040e8800e00c64600d105400d0350050740c0350390660f80c0507 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 817564793 1250 817563543 817563583
    0x306010c05010b030706020c090a09022b0f080406170603070b0f07050d170708090d0c080d0c0810080f0303011e0308180117090d0813021c1214180a0e07090302030f 72
    0x720003111202ca03041480b0740c1c2c2c0e80c0c01482030dc0000c403804d1180c00340303130b101d407080c42c0d212420b1a00c010103c1d440200d12902c048010030610445940010f03035003040301c01c1e002ca0346650b0301040409008600900900804512071310000035040c0341c02c00520310344100b0240d6103100540e40d03d2003c40d07a980d806c1d103403051560400741050b50005d1240414210541c01074881c00d18224032400118110340d60251f800c00018128428014805000c160142c010604c1600801e00d41521075456922440103118070f012401d0401070070100340d0780050089000b180c00001442c0c403030030505144404800c0300c081040c006852001054030002043c6800c070f01507058a070007014003140181303054a02c0c01001c0c2414a0341c800720011000186d44101c1c1c400c50020f00144074140041d40c3c1d18003400c0751400340b9031400600484a0351240401000c1003510001d0940c0c50351b143d01c0466140205000c14420303003040c803203007414404000007603030051a8401124030070b504850605910003000c0342c550b6901d1030354001d81142 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 817566043 1250 817564793 817564819
    0x30309050405130f0f0b1506340c0807050604060f030b040209041d011107050d08040606030605010602031c0b0127120b0702210306010c05010b030706020c090a0902 72
    0xc140e2040c2e510070485641d001c3d03001c405490350095603022600c01c03100071181c00548000c1115003880b0a810a00d010301034000680302c400012181d02031485903ca040c43c030741c646081e214000000135109074009260310901c441c00743c1005c5d80101d1042c004d030006442080390010b810b00305081203c0071a102c664604006080041040f409040102251584980c0a01603d41245d695103d058611562014500c2d0038103032840c00142500c0724000c01c1e0b10152402d00c03207030022610120b02590703003806520300407010360741e503160850041c2500c3d04040e121034508030001c55400c1c0c00200070f2540142c091141940740524000d07410569070542606400150841c0c1d03603000e00d1050280c5940700e0901c00c03050340e02c0c854444d51708035a400d1121200703a64521b802428009034a4040c404014030b100b455654003800070300322607026030074800909410f0402200d84508030a01c03000b94024085580700030183e8031140d559100c001d60b20f4180c0501c2d07900c1003440e070340450034101e03a9102c0c1c5040304c4e602074407100054403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 817567293 1250 817566043 817566049
    0x1302030702010b0604120b0a020f0403030f2d02061807050607060e0a06020301050a151706010c0f08130e01261603081b030c0a0803060301090c09020c1603030905 71
    0x1000d000035040d9074031402c08611540d00c080252018020550b01544058200c0c20f145020540207080c07101070a1042006550b104580030440b02130b039800d41800741d0400c1c4500c1088815010011006d0401c07450030070540e0700d040d2500180d00100c81a81c1c200c2d0325035114414120001c4402403c00340e110f034403201e81005a070070715030041c0103482c1c01068006a880c001d604c94134200007614804a600c17590000c0140142d14000d2096400741014402004901d075000b00e02038403041c2017108041030541c4400014009a2107100040d0810380d07c903c1c1c202c0380c1d00151802955030740203261240d07030074003a08001141d01e10036601410b048070030600c0755140d8402d540d410913013546502e80c1046020702959040030000807200b0306990045d0b00ca0501d140d51030a0305403034420520000c00c0c170f5024982081102c0c0c207864400003806260640c000e406aa600e03201c82d40060700500311101d00074a41114160000b40d01e40c001c0c0c4c050001194014242c400c08003018907410701040c0c00c1e000080101c0d02c80c14090003182 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 817568543 1250 817567293 817567297
    0x3e0c0306010524070c05041d1027150f020c120a020f070b180a14040e100e0a0506060103110f0703140d0903120510030b060301060506030f040506090303061302 70
    0x800c07403008078020442e52030740c4500f5548040e0095854041c03100d000c00050900c0d21500c800440c0c5401c559940c9580d468810742c03074003205001d4080701d58680c010704813401d0202d26140301c4401d1300e02211255803200d01d841b20701600c1003a11848840e01e0220048081811802107407880b0550001500d103410f011890505e254000c00c241c001103200b9a4031005134070a0401c40b10010304110034800b130300c58800010715020304050781000c500803898900e0410a80c1c10300180c050003040c6c1181c0118108040f0b01155182640c1c89219124042c1881c020106410020940c104828040d8080e21880c1c0d503070300700540540750b000403922180082081080c1d5000d0210001d02a21403003894944a285001e1440c64825004a41c42009840da21510103040580049000d140031544800c140140d01d00f1101d00d0407044507510002e0040283301c00024482d6900794400c0c00901001001a9120305003c0340c3d81c00b0448044408503140c0c0b02d1440803400451002007621b2080320010941c0527000107524581000c0c2d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 817569793 1250 817568543 817568569
    0x7050903030403171b0f0f070e0a0c02010e03040b0417010b012309030d21050f16050702030a0809193506040303150501080123013e0c03060105 63
    0x4c3d01e002d00040c1001c0c0e03040c506a005030b5115000400700250011034450500208050320212035000780000c1159a1407211030a40c0714181800c006211040d20500340d0240ca078030700240c3e60724000010041030681c1e80d500a4170030b40d030400e864022a5480380c0446802c071040d6203902400f003000440c0c01001840c910f61505400f01307090b1241810081418082850305200e000c106004c10010300d0108116215510041d1030001150024040c0c0e0504032500c09500e040170700f40f5652100044005034429000b14100c4441e103601504660303110f81903040c95103490b0000a180d52082d2071540380d07a10906a0081040260f801c100207100b903a402c058860788400b50541416001c509001140c1c000d00d14003802400e10440c0281c40110300c003210f458040149203c1504014103100201e4018027005521041c4110f0400080c0129520400080c0044e124034504200008a803c03441d603101c044170300c507820f8030b000d851860072901d1030501074401260384801401d40700d290554400c00040001e45881c1e030480a071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 817571043 1250 817569793 817569833
    0x7091404180b0c0c03031014010c020904030e06130b030702121c0518010216020102071e050904051c020312010b070305121510031b0801060212090a21030807050903030403 75
    0x391503000c21109056400c21640e0743c0400700744100400c50360600c41c01d0310230203450903e003a550841c45640040c103023800241014081084018241d0b0680d1030300011900a44044200f001e0045c0e540c12101400e0350044407610010b0044c0d92a000032143c8600070358842946428294643c840160001030050500415807169000d0a24002c012540c089c4000c1c8041c2e49607a00c80021101980006480d01000e60300c81a0710b010f03804141c0c00000000c07000b55041e180100c0f00d840701d030344960030200e1426091040c414100c60406e4401d54440d034001004040c0c1c00040303100c2000356a83c607001d594082c058860040d01148042041001000d1040306055002101004005c3d403060242c1c0420f409844881c40381010070381d0b980c804144000a403071400d00504440ca070003503940d0b0600034000c0d10703401c200510040d031403804035007450176a4071040414080c0c85101c202c4840115190399031088560014000d0f40030072101c01c0411000f92140c01110001c402c003900551800b469a5101c280c294a40b1a49503c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 817572293 1250 817571043 817571047
    0x813060f02030a02030604060e060a09050a2c0f060c0702040902040f051003060605090403050a0f03140a06090e0105010303091202130e010204081b0a0302040c0c0b07091404180b0c 79
    0x81800e1000d1805a410f00c40016124903040080c001110f45581003200300750030041c1000441d90340c150444042d5640380402085079122810503a01030043e0780310490501d20b03440306a8105003480641c1510303040000301224000d01800700c9160310350f0310070b846039150324504100c00000360510360018035a00340701610004071030040761610000c8500a441c1f00d440c40e0756104040051200310b010f0100541070031a8015180d040940e000313006803090388200800d020214170090170840c00b80e800720b2004e080040e40c40249151400040c4003c04140c002d4108107480e0450b04499900144903803410382e075064403131204003410010080350074404c107103049a0184894a10030b0210060b4001d45c401011860b00140c3c886003801402c506212030b01245951894042140c0005903585028a03800c5940541d0005482e0168803011134610780b42e40742c05000c2c852007005001e40c13580e000c0e00b140101c4a200815500184a0303c0030003050740c4480550036a8005003020300c501060007001010341051a0f062094 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 817573543 1250 817572293 817572311
    0x30212030d0e1b031207112409011209050c090a110c011a2d04060914040c050a0e0f07030603020a0801020c120f0a0e15160c050103020406081306 64
    0x12007910100200b0314141d4210004040b0107003141900c0094400046020781140c00010340040380c58060410b0207002010304400c0d5001c6512040c4210392900f203141c071312584088203800f10302c04660080341603a0001d2110200400506601d1240e04411a84000980341103665002009010803000c5c003561a010f690386004842c814041e8001c2880031000d000104541039900300552451000b550240cbc0104504016080c1d024001d1182008010351803d50045240c0010049801002c45410280b81e292030100e000350200d41c02e0252501c1184500d9409088075201c905000fa810b24510031440d800445001089400c1050a5020380c000c0445c5800a045556600040ca92400550100100d658009001c1c1c1d9002c0041c024000880410b00d0b00c1c6180c4600e45050140c0c1c2e11980340d050041068041d1980301c25501d5a0904412240c00c0e04041d8455094088800a004000c41d0840350302c00e280381c001416500900903201100c5407034541e00320300d60b00c3c100d14508284480e030003215802c1d07940e8220 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 817574793 1250 817573543 817573567
    0xe1518091009140d0503160f141620010c0b040f0f030c0309090203011d040309091e0501080a02101d0604090f15030b071d03030c06040302060c040f03021203 69
    0x840032943c0240301928900c08401c004500340f0340084c0d001c8082220030410812a421761070074080300040d19251066410304902d204456410140081003040b03040054011140c025000404580074052840780c250114103d410107103000c40c101081d80400e01c00c4081c1ba01280e05010a5a4024090b0a02910244299642e59401c41d00c10801314007141881c12035200385640030303c85201502551070210314550406056401c4a505d0907582082c0e19100c0c1e001604052107659401c2c0140038442040c402d0036451038070b001818490084100c1072500e84000001c40070000114100d2864000e451340e0301d14080c1400807900001030700c1103150000c5140c0000c2e403250300c7c0e00006000805000d403001441d03403000007814050702c50300000e0441c600504042400400e45558039242c10840d64103020040ca01c40190340d4029414815119900d4040400d84462040001c0703030316442107100e542680c01c50394460304c61180500490244410546102d48144014180300c4c4980c0301280301241200c0c1440318669038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 817576043 1250 817574793 817574801
    0x120c071805071b050303040206031f090b1003052703040b180f010c031e0c020307140f0a0f0b090111031303030e03030f03190e160e15180910 62
    0x1044812960310000c002c02d03658009046001400d10248600c60404107444469580c003018001034420500080030408207014291003804600f0380403a46800580e80d184420000c008503500c4a009011100303c48139642e11a100341845840e01c0c0703001c2e0419100c02001d0304400c1ea5034403408201880100301c0402c2d10381c0144050030318800129840101081d0a1050089002102c0c1805045c0f01090300c140300001e4201801c401c0764010318060203c4044000422541d03002c1c111170282d0035000d844004034900020710000c40c80301205030342c45000141450203000c0410050b1046110491040005121030807001004041d40101407519448240c00000c2c034a0555000000403048071080314810002c040e000070a100ca625811030140d42400707007605140880e44401051006030810880c9888d01c0c800c4030b68000c5252950700d00849a503a00c191040140030031080c001c00305046924070009152000e1010051101c0c1c0e00603024620601c840c034401e0700311410241c92100c141c0190300314035000440900c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 817577293 1250 817576043 817576079
    0xf160c15050304050a020d020a050d2d0305040b070203032106010201061e1e09020a020618010605010c110d02040e031c0204050a060c0f1208070f020105010305120c07 73
    0x494204580c9000101100350282005050a01005004000104801007205002c0c2034060b00c2421000c9402d01c0000c803021000e0708110f0b80002110f11aa003070010030340540c3c081785d0f011844190b01c7c1092064079100d60760046001000a0410001441012020380160800031b20113801c40c0d0070802555241a0150701003034072850040d00505c1000b420b50703424000d100090400400b400c100649000020443ea0b08500500002c100741500141d40036181000302d00080102240440d200c680700b00009442d0841554800c500040042d90420f0400d818460f142c11100e05031031303480c10980315036034105190001c0300c2d032329030302015a140f2800561954020300900040d0f180c05903a8805d20030f000148010809410540c0f42031043c0720600c2a0b85590361520152411820710314250707401442e142c4511028968010303c907102580860100d9500071441c64080c142e10340340c01607a9118120201d089907001d00c0060811b5204c001c0000d50541540c00410202d0048002d0b90304554603143ca984030123100203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 817578543 1250 817577293 817577303
    0x9360601052b03030e012904020f120c0a02150c1819031101020d0816140d09060b150c0706140d09080301050a1707090b1c11040609021606020f16 64
    0x1121740400028280f02e820003410045c001002030345070f16421142c10340d01c9407500c50f0182d940060904c400c03e1036030b029900003101000d100c9815262980c2d44e000c0c1500410902000f512640f150803200812000c40c46d4860070365618124100a5804441031540b0011034003d81c03c195194a001c42004c0841c072248055400342d261007081e140c88800080c9091004c00440081092507000d0088031082c500340300e810701c029882c200c0b8002103c050640240c0c4559580705034074078a0001154104400d94204482451003242c0082c0581002c440081c0240f0030444d080724243c108620900c0218040c2e591903400d80341003600541050441c66401040704d10720a0286d0b5400d9001c40100410314040c05a07101809805212001d0f80c00c901400d150358020500a094182e41c549400015a032900d043d01400c07007042000181b1607041c2418000e00c5008000b0b0a07a000304d09002c0049020750743e60003140c0864105080068203c503940d01c9400c029000300242a880307100800c0ba04e441006401140c1c0100c50080c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 817579793 1250 817578543 817578551
    0x9051207150306140904020a0f030b100e0705221e050a0902070302120307120203010311100203041a03040501111207091509050402070c030209360601052b0303 70
    0x74a034070705816031a0011000c06080c51020301a004510a619050761816038403000a511a03100160310505542c1213903410f451000d20000500c07819280c8580126400c00b00381100603245c10a0011200c401c072885408502c0c20441410140c003041d5600c29000c03401003401d501350351220b516014a80c0c200400010700c80f010a010b1241d441d0002c01d0400038002000214584403031a58003a448480920707100b0300c0041c0200008030818010599502c0b5001c100740c0440d600c0d03850f458200d68a00440c100640100c42141d0445080c0e4000000c44003a02c074801640e141d141c0240c0c200c9640743e8002842240d20303540381c0b1174074041c06910301c010b40021544003980030345514001d00000c3c0b00303690b158401200f034804490b1401c0c0454101700080c00743c1d8025100580d868045007081840c001c000d0740000d420a8500d8100601d25080d02803a20750006d0400900702103542c0980d5a80c2c0424805180190319041840104191302e010340c244c54031028000d1141014240150b2088454116444190042911 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 817581043 1250 817579793 817579799
    0x2411030a09050f03090a0e0a020904060603021914031b071e050f030403120c05011b0203090a14030706031d06010b040e01150806061e07060219170a050709051207 71
    0x30301c5002d4140c10740d50f00841c1040e8451000030740701c58003889610380e6020100045603421265404aa08402c801b62040c8105652074800800a45c4a00841904030403491116120f031403154107030a4010544400711400c584440d603056080c01591102d807801d5540400803480003410010010042c450340659503032590485040003070803c05c000c40f018019420400080c00018640c901c204075020541c030308003071030440600d0603078010042c082c0c28074104981511080c2e44036500000402c24420b064954a010550392850500c418850305406c40c0e151b00644018000c8030300c2540918681500b405600c074900392080c0c0724504000c0c0c203030001d04070800006428803803500c690009500500800b00703001498016214020303c5100060301d82413007094000f48030f02d00841039018500160706d030146415901c01541c5003500096008010189181010b8500c24461600401008140710450300100000f503494510705001001c1c0144102c2c00d10001b9080807900383c44690a5104005540c001402e010b41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 817582293 1250 817581043 817581053
    0x51c0e1006081203040f0f020301091101020705030a0f12091e030215040e16210e0c10121509050c03040203010b150f1b0303040503040603182411030a09 67
    0x2240c020070010382c044003030030f25012a00d10840390311513008110050080300a00e02000601e000e000065455820401071400f4445480c003a881781c08026022100b80301ea442040c1922100408400707402c0888508528010034808901d0600401540c80d01640050712107140c2c568440c0700e01035110702c4c450303440d00034421410f140864009441400b4a103904151400011120000d0014010581e6900000764508854015580e0391110310312001321034a040d0b6103882d100c0c010402c0c0c210743e072080d01c24001152042e040089200141c441c1940e60000c01c400c3c5a0a20301c081c0c20058101d000307040d800000003d00c00c41c02d02c45c050007841081c460503640d0030180105425600d91140242c8981c056441c82000c401010044231641410a04026104d041449100d801600c0061029180740800010082040b501200400a40e10151010030591000d8040c10501c0100464020584d070400c40306400c0400003280b842c603010803008404070b6021524000003456420544c1c0380d4406079150a105c5040007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 817583543 1250 817582293 817582301
    0x1e020c061501180302010c0317090c15070c0e1b0d0c08100b0315040b0a060f09080609030d020f0705010c11010f0b03030f1614100b01030219051c0e10 66
    0x40000d20704182415010f04880c4503003c40c0d8030009040c0907625a000f0200b40c0104547e401e100c456203405502071074140200c5880710301102240b44038030310144038107100807590307815035010a0300041c46c50032140c11303d155030030088000740c02400d9602d0101c0b418030101c802e8500902076080b0a0b04c010480c80f141050281c6002e4002d40380c103160f210354000c280015a101c805030382d03101d06c1f1706c1d90480404c1038050100b00105080d0a5603a08106010700124001e5001760100c100341c42c1c160b845258280d80c1e0030000d1380328041941e101d40517400400c400b007004d203007580281a518100c040791501c0c0152a90f62103003110312481e80070003c070340d500c0a003071034800c000e00c40d003201c00c1e042000910116030541c0c0000c0c5c9901c100d1000d0103003060007003241101d01015546000079250300148654000390f542408a940e908203a0042913201d00b40300f2006121f512900903921018800d541c070480d0072a940d4416280c98120000c4c2482c4040141514400c00c4c405e8001ca140c02000710005e00f16150741032a03910166 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 817584793 1250 817583543 817583581
    0xd02180c0910230306010c0506100302090603030307080609180d02010c030605010201020a0801170a020319020f0103060302100c08162409020d0b060a0312051b0601060c061e020c06 79
    0x8802e44032400c3c0c6030400801e0368641c1c014103454005950303580300c0005071a20401040080c086100d608100244082c103080000d090703a0007100d61110035a0384400f010303540e1100300c88900c00114a070001c03a840e410455176054100011440642032007051980291032b125030610401e0060b03440d0380104e840c1c1030f05807040c440604000c1c070095207030041e22100a442c407070043c41503a0000c40d9884640590400512101d48025401001e84185103404030180e12051440d940c260701c65481511040e2144d070003846010103ca41c094810511800c0247e0b0030b4644110080059445001c10001c50038521282d800910081303200348218a0440000f1080101c038084105000c444989404600d0380540e544400c5d240216078450805001c3d07076220b82c00300701c281266a2000b44905070034000d8048054114001d4000702c9003850a105911032510f442170342c1c03806c00784101c6020480070301c2c00402150590700940520b98414169441000311480b01e50300303e0703100e44040700c4140c000005005c01d0302c1c20301c60f01c0201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 817586043 1250 817584793 817584797
    0x1305060112090b0f09071a090a030b010e0106030501080705010801030f051507050c060c28110a060f0c171f08030a0315061103090d03180e0615180d02180c0910 70
    0x10390418a1207d11807024040480c000040403510b041141e440103940d00145030b0001620f03001d540c0d105c805110201d03080c001e01c2c000c20f041000108800c800002c841c0129a0143c0d40e49620b64a56110703c0104a0140401e07070b90703405280070310925441c0d0b1031070f40c42c000c50840e80c81c19a6916010780003403d0003400741800000420400034500801c040c12030111a4110700c002208500000c0f100c16900000140c884401d64002d0b182c45c0403d03ca015440141071544402062020140c0c0e07030070495040e0700301803d80100d62880c43c007148005640c3d4840c652000700380c0750a014116140d08540b49144c001e8112440000e03107d02c014032081007007004440007411141804c001500d441c80104e600c0e4010115028041c0c1905002038041c148292440d00320740e654956080002d82d129030308113481c0c040803030300e0300e01a100d125580d0001e64034a40840300041828014056180303140320403c05235801c01c4500340e034050a00c1045500240001c2c55150080a400036034550f98120030b018007503c80c81030881304003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 817587293 1250 817586043 817586053
    0x70e010518100e061206090a1e05060109050c040f0e070f0f1b0c05040c0c02040c021906051509070e0a0f080607030e0f030403080301140409021305060112090b0f09 72
    0x40090502d240c49010f491041c0d0f04030496903500004290044102c0c020341e41131307209880a11494150101c1c1c20003045007e28060341c801904e200384e2000c0c10041c1c1d2801000e5610220041105003007c1e4806600040c041d040285020360340d10404440e600d83d90841e41c41341e8a05000d0006079034000c800c0150600090134018011114084003416507800100500d00820280e070904007082a0103012401030a002002001032264192000340302404006049000394540080003094500020b50754400d00c0c2d511250351603603041c9a5508016000c0584204070003000f10b800700d495544c488200038400d1810355502611440010100300c0340c2e10942d402150301d0030701c4c00c80a100c050000700e1026030140b40382c1008148c0e144240c203c00d1030907013518803c101d18000803902100300010440158101c0c2d62404480078010710640c2000104c1c0c0310000001e502520441c401c403860301c600d8000310760140050604000d002681c800300d105841c920345081301c10b81d0b203032001c10541d8011000d0003070700702c0f052000601d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 817588543 1250 817587293 817587301
    0x4140f030a050703030c02030120120f01140f0607020402030c03240d02100c050d0954050f371505040f0b0a080a11060318070e010518 59
    0x140d203c1a5500019003004941542c6070306544094010170825009c0408401d1200b000f8104145c0a800c145200b40c0050441004180c0d100c2103250158180d951100c0d18a100ca0960420040341424000010350000c00900074003025a885101652081080ca11030f02d64910300102680380003524000441102c44480140100c0e42d04c811007a180c0e01030f41512100000134001006542084004200030581c0c802c580e8958100303580006841d00f03c0d0071041001c1d6030154a4207400300901c090070300180c00740d01c0c480464034080302d1591140100715002c6002c040303d0312460321003001b502d00440d4500b0055005009008240000c00890300301c1d034000341196485081103134890443c003407040741ca044183c6d0700c81c208a0441011040071200512004004008031050404984050090440094850200718400081c01100032450317202e802d90105107070000740000e0040002540000e0f15200001044030345042c2803602c104942d001410b40c990040d9850f6140204200d444c12494000c110340710720141c180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 817589793 1250 817588543 817588553
    0x31703070c08030c0d0504062f0f0a09080d02030403290105040c05040e04050d03050106050309030a08071b060e0d03020405180c070b0115021009030e010818010204140f030a 76
    0x1a01c005034061125540c07929071200159140c0103050903a1641440d100602003004031a51001c0044211400c0384d400710310544a8100c1781c441c00810110020504001032420020704400800c00f060503800c100c0e1540381c9507000e071803800414095400c050307840041d00780b00f84030300400d155030300d01c8000c050302c081d041000d0030600c0c0845041c420740d40a191070b44011104540200e007a107000d8400c0d8408682989414144a560342c410403030340c000402d00e4040040b80e002e210300c0860b803061515000662400c08410400c80d00680000c0c0329104102d5008058500e808070340b5030718240240261004107a02000d49102400c2500340e0500009140c81004100680c0d224003507001071001c00d034007080c2c0c0c980c7d0341d22805414910640c2002000306010f00b0001c10241131406002c101541150300300c624500b684581c410445002c1c0d080600411035140119185601c511102035010030083c5208045c8000c500c40344d4260380190700040007641c00150200d6036070526042081c101e000480041520010135161 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 817591043 1250 817589793 817589807
    0x11a0405031e12160b0627090c100809010615091806031a0a11181c0c17060c0909010e04140709020d0f200d09170403170307 55
    0x20510101c030782c0402030124184140996114a0000c0076515640e004000c41c900000d4210282111059001c00c0403458504008404c0c1040a400c210032117075035500c0b802c4100700c414004011441c0c0e8030a0364440036294450f60710550030308825482e04d013124140030b121a07096a07196005100d407100d1101003100e00c2984207503010300b180c21011150440c45581c2c0e00c050090030094001400295200c0d01e076070713a08081e41044034400c085054041001085010400400384a941ca1102d8518101080703a20a8608180070013803400048600d03004545142e9102e80c846a110343c00f038040da9140280f04680d403541030100541c485a40d00700c40740340c45010400202034940601819081409080001d0300300030940e000c0340b0a80c8000011550065a10040c5102035400260b82c2241c0b1410890390704400c800728082c0564000c503010b410900e114412320f180700250000c600c1441078945031003001010601e620701200b051000c0c007400d0382d0b446041d414800518032481181c918410420820410b1541e40500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 817592293 1250 817591043 817591063
    0x1050a111005071701060201020403170c1f0e070803040f06030e0a080d050103020a091404080306031f0b03120a0f05070212060f011e050a140316060206011a040503 72
    0x381500c255091410452600c80c0070624066414608018809000d802400c4010340b2100b210b4400850707a00c03003070224240d00807840000e10700b00c1118030071560403882c10040c04d6500140400c50780142e07982e410704036072560516a0042d0160b6105503c840403442407191001910100c801145403518203440440070403032030b00c41c003800c240d80ca030084014440f09115203000960025a16610740f0f080b111031744010070302840300328496011038200003580400c86c01a8868209654520031942d40d40d0340b2000c940f039100408aa41c507008000c1400d0901c4981c1c003105d45082d4030a14006006140c1900f80351802d030a80f1940c0c50000401d100800d16030798445148001d010092402a89401551000c02c910449286001c0200d009800030020044804c2d100320b03040398032508070240ca01d0744112a24403120b0702e83c020250010100d0710140140e40c0020800786980c0340180480d40a01003445000c2c02c01c40740c03038100e000181c015000400c6091650001e00f0500314112548031700e003d18000c0040d50f2039000403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 817593543 1250 817592293 817592297
    0x60302090612150c0a0f0c050d0c060609020c01050103020a06030b061630030506011404140d050f0a05010b041802090612030c03040602212703070612051501050a 71
    0x51101c000c0703014440750740c82d0010403a09820a003080d1002d80706a170403131039101d0001210780a1342c004091040250312601600000600001c40f0b80388001c5450350154541980d1a5490303c0d40051910b1452006100046d84d4500001e0554114070420103417403450383c0310804160034100224220350795142241ca82c400d918045d1002009540381c02081c01c40035400020008003130350b4440c055031407442072880346c0c5481aa4101f14655030034005540d40f408a10b10720900290074802400302d040c2100c0c081d00280c2001b003002d00c0d40d8400341e59051412882e010851041d4215194560410409000302c0d090001c04940034410011150304242c140c0c160150b001c0c0c8030740314074000b003034207501c42c01006080401002d041d40e41d078103c5901056a2070f070103485075000510070628100d075250504100c4091141c5a070000d035280015041d040c001c1f03c1200401c2d6407105a05003400b60155504014079001031102d51102036003035001c802443c0459170020b00f21303d0703100c0c10030704480c2c243c0c0c1c1d000e01259101d031900c3c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 817594793 1250 817593543 817593559
    0x12010911030c09220803070507061d0304090b0307030501020a030219030506060306010516050105071d090103081b12041806080c03060601051606091a07050c071a190804150603020906 80
    0x3c0703c03031380c0361108a00b0006030900e00700200f441041d590100090000303a02a001c00d001e07484c41c00b9802054410504010a0709400500051108040c0e9421040882c0c400604444c0c01c0380d1030b500c42c1da08903030000b894500443d500003124442e110b13840c04100c171540c1c401d0170108083d2a21034007150146c1700041402c2d040000000d05103189101c1c10004104950304040200407503c0d1410f4090050f4000c9604407007e009010202d8003189041c0810f14140c0354024420350500d00001910804000d10741404001805103120340c0c0341080000c0041e00091580e07561885d2140454580e45044840c2da410004a5030810b000c01a000e4a0004074150000f0003032912540d64488071803910b610801696008111604004014040c4452800c4110b0040004034030801c0e1a1120207080d207680c4a011004100350308220410007064003070f1038810880c00d064202440c508081981039041c5044920348280104030400d090005001d41411202d980380710515007040502d00310b070001000c1201c0200010300c910a2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 817596043 1250 817594793 817594831
    0x90303070c06050a142a070f12091527050d15020d1406190303080f0417030a0e010b06090105221d15150a03051512010911030c09 57
    0x200707501c10170b074007402c80b854425075090072440c1e035139045003006290001215003000004102400c00440340c5e4981e00484a8030f1140c2d099071120122502d20003060240300044074005601c4d114a044a02c0c1400c095885648544c40a4041050300070710010b0799403d441060030a215944503440c0751700c49240c1040b01d4801402440218201920880c6030900c45030b42071100688208100c904003d018001c21148074406902070b03940c0710100d0406110107030000c0d1048000c105195510f16505800ca4064642104c0110310680041c40c940d1003a100700302c03410f07030340c0010201105007845084111a0b040358580e02e00003110000800074024018000820403856a64405100e44400401d000300f020329038000080070b00c2c410705002d1038000c070b40c813192080548080c034117540303081e1410035042800805c5045c14100714020840041c0307001031070b003010030400c4203804945586100d204074803a440940041140141ca14107006c1da000040390241c000e0f17001e17001c005406c0d52055520303540400d400302c1c50440d00c50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 817597293 1250 817596043 817596061
    0x308010b030a0e0304120323090603180316110a03170a050c0601121a0c0304120302070516080d03150330030b040c020307120e190b12090303070c0605 66
    0xa03119207007030f00c500c0005000210b10400507055050b0f00d000382c4503081e401101d2028400741c1100300504441c0c021080011034024a004405582c100c852186050f94070100d20800760318642c020001e41030b07032034684945017003000101415500c01640560b0300112003803850741c0e486410003a04004840d180c02c0440e0009000d44203000369025070003510115011540d6945111401d455944400d5940c4002d000781c0f8000c020625070114010b1b450600070502e96603c3d5101c5071341038240a070003001056000c004000205330200070004fd25524100791001e601e20b42102c0d28649044c220440c0141070405041c0b42d945540c610303080b0304036a00082c2040c103191134142003801b4240100c034101074145e031385d1a40000d41a8158070524103c40182d6040041100d00c0c0300503070396170040820040041042a44003031006104140443c0046405454003160207415044c403400c40c03540382c0290114031408101c1c400e5001c0d61149568001071101d02071403450602a40c0108144003800001e407071152248080740000f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 817598543 1250 817597293 817597301
    0xe060111010906054816050c09071b11010302310f03050c0123042705010501050a0c0c09050a0b040e0316020f04060503190605010e040308010b030a 65
    0x1500680204100360301e603e000c400030a0103840a044045d100781040307102101143ca020620328410003c0070103da0181d001c41c00c00104202070000340b200901001c5800100c2c20890b1018602c00e501a00710610000248021828020030460402c02e4101e00f1107031103184880b034620501d40003148030000302d030114010f0b006446aa2507000c8110307030b0410b101c0302c0805140d2603404082d208a002172550341d55040000c03801c2d070300340c00050519049101c0b14001903014100603e0b101001e500040c94542e118100000d003a0045d901c04200300e078542c2d0982e010002c12481198030780e82800c1040281b5410840000c00500a6401003001c3c0f2120382c0314182881000e0f08401c00074510014240b020349042002c0002074400102c2d030710300950500180185128001c01550305201c02040362500c480d0264003003146004003030100942055641c107010440d83c81c1489030164018021b800c0308200c0d03000d03280480803070300142d016410280e9002c0601c00065030110310036045552800400b40c0304d0300c0b0301040f04018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 817599793 1250 817598543 817598567
    0x9020301020c0304240212031305071e0608010509100e04060e010911030f01060b090103020f04090207030804050f031c0b011b0b0703180c05010809242e0e0601 70
    0x34400490002084511341181821050700e02c14405c503c1e0b03441c2c08080e80e03101c14107005200442010320001d02c06061412400c07400c24062005c68411940e12103608016000c055500c55890304c0c02c810034440389030840c222038018101039421343d030710b4685008415007411f0035001c5e0403488080354002c82c081c480c084c1c004d403642c400c449008000c21b242c80e10308148654283d4055a000c0d0055122602100c0d906104900454a648018619180e5000300460003580001c1c0b80c0a0581d50a00c004a000c0c44540b02500c00c4034400c0d10703080c00382d04003410198501140702d40c00d02c0c5503600c20044880c50004c0034242c0112540507100100b042c2a4280060750740402081c04043c2c01a84208814184164001d00d2070190240d620100f101a01104041508100d6880040e140c69403402c010000340d40b1407042280d104403580706a42051441c0c425140041100c3c0c210705690005400c14030462426100f9025050000912000050704c504030f20384500d1903603441980130200544001038080d0f4020409441d203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 817601043 1250 817599793 817599817
    0x604050607410a020f2206080102030714131e030803040b0f0610020604020d0c0e0c0406030c03021206040c03201902031c0e120a120f0204180902030102 67
    0x500110707014401484488501c0700b89103030191111400041e800401d0b444040e94010f0120781041ca00c040500c10314807840345024401079603010f0703440690980740c42a14060f000c143d0015a4904120f4801403240ea00b00701e0030060401308000051a81c1c640c800620f040b1505664107082684419804080c062415400a812990000704020802a4080c5102e00c10322140b40f900303900352a080d061050b40d40b550060324015901110100300546000e4100b40180c5104040101441d611141500e481e1241039a240e80000e0010a0500c074041e00b5018a9042c007010380f81c11810492100d0040000c840c1c080c0280b40200da84000c0c030b80150344650048540c0c107050b010141d8141340304a0314811300d5030102c100310440300c420f00e503040712091002c411120b44843d41d04101e0311102c20205107100803d083d0130b01c000c3d07922965094040d1403412001409032201a500c5800034194098402c00c16140090340c5070151a1041205228140c82400d1652124540d0f240002e10114540b002c00d00900c0341c0418041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 817602293 1250 817601043 817601093
    0xa1a06090c180316030320030c07030204021c060602370807020a090606050c0106050a060818190b1509071d0105210603100c0905090619171603020604050607 69
    0x2c01d00d904007d88054001344003a003040155109003003540c90303000d0395a07041c0d03854100c00b104001600e8187c025018580d140d050150100c05000e01000480306660b200e1805038119103659030700041c90500005d864403008000440c04504506006010820b001004002d544003140e5482592100007018002e88211041040b0b80341d103480d0040d01540000c0a8865950b00344000880c00e4109800d0300c2c0121a520307218145503407101103d85010790072101803c4035030320402d00451250700c60070800e10303699800340c42c0100d4541010410040a000e065080e28000c0c401d5030184645994403107100e42d404484035a400b00b201002d180101c3c1c541c485e00c2800f00030150020030200e880951f04658074080c0c030b422400c9400c0204038901020175104904140030208290312410007150403d03e030015845600102665030b1285a5455051352200c0c41d007100a2005104180042c440c500b00980f410380404680c004010341d1071680001c141d8491070080e0f03409920302107494420000103569101c440c1c407030045414 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 817603543 1250 817602293 817602299
    0x110d0c03080a230108010c0c0507032409030e0406060e03070e100e25020a0c09020d0908031306060f180c0908070b2a19030e030a1a06090c180316 64
    0x1403c040c2082c06500215480e100340d05000ca07001d280d6180c49a41d100340a0154945182c40d03420352904158514002900d003043c1c81d0b10094024846c2900e2184241c60f8500c40d048214107010407a8100d401c21400c0c0200f84c0c0005102d950005a0401152244495844141c2d511387c400d0344421505c1d0b011580c0501c54005210fa00c05440c00c000c03189410301d0030f164500c0d10040804a0359404800000303094040e02c2c59040c0813a408940040003206028800420081519500e100310b56200b1542061401e158440706400c00c141e90046034000c1040314508440903040450a04860300119a018040e40d0350301070260040e8011130007100105111010390380515513840d80380d0321075442810b000481102c2c5452600000420f4241c220b00340a00400400209000b003080c2c040b0040c02070000d8080c440c03d6803c88041fa6000c000415a082c8615000c449203904401c240c150400d001d030146200b400f41504009400040c84140c9665080034103410b001d0170035420109060848030f504542000d46560008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 817604793 1250 817603543 817603601
    0x1c030219020f011109010807051e07030305091618200a05040602010f0207110d05010b040204120b1506030f07050906030a020405100c0c1412060f0403110d0c03080a 72
    0x10b2490a0031070081c0804441d540b0b280c440c9118100855000c00d075942c020644591055000d005209189240e002c0005c210a1500304036420008040740046d4a0b00100030351100e0a001114400e1003001c007080440d403c041c0c0da0039000ba46220428005966802608580c2c0c601d01c00d0307894020310101010742d540c43c0c00c6e040144154424003c040156081ca801034403645024802c42d02056041904203881d03c045c001040107001a03600305583e65034903080c0d400d070306907901d10041c0020f10006501c1501c195071441d280040302d02c010f0456101000100e0070341d0041e00c030401140d0340040003002101d510707a1511030a5a1501030b800903d600000080101320f012661640240241e64048030340da00b081d401c54204480d99050810002c100d400503100811000380d040c291101c001c04001d202584214a83c0c604a1400c002110032070558108042403006242c0c014548082000502001d40744030b20807848050300000340c03000004d0800442c0300000340c85058030740c0140506241c01d41560160416a02c007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 817606043 1250 817604793 817604803
    0x207180e10090515090601050d1709100302091318080708040e040809040509030a120213090f02070309051e2202031e0a140604020918040602030f060a03051c03021902 73
    0x740c4d1012200c0c0c01041c0c0502c00003503070904031080105020000c550550340c0062828842c00d2030f00105c60188001c3c14695a4114101c039020620f603001a10740b1094000c00c0805d8100c2c40c010004c940c83d2010b40d01646080068420606402024540c2d0310a01482e00c0d8105224030b41c02900c00c1311f00c3c4010300080044440080c00380380302c1101c0030310030703911585201a01c0b480f50408040100d2120f5100d0b540d00219900903083c4070300d803050203600080e80c2c0c81c6802e0541d64070040d044c0b00b01d540010b0030420142c10103609800b412043e21012001d00003c500842009030400c0c58034031070120101c0c2c05d0407822541c80500c1b46031000c020300b59241d0402100713400403840e00540b0050640036141c0080c2049000b80b203402c0710110002071140d0350f9101e50003404000e51081400d50380003942040c45804800d89800d50a000b144107000040e0780b450b1020b8601094080500f81c548103200d01c90080010910009880c081912410403071900040c102c901507000303216040c140c95000d16514111040c0315000b050b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 817607293 1250 817606043 817606063
    0xc0309090c0d060f080a12030e2b050405060711060d060914091f0506030703120815041401030201030b0a090c0903030201050f01032a0e010f03120207180e100905 71
    0x31007408002d440350720010340c10b4058000d842061b40001040030100c1c40038003182c0d44443c0f66003030019a8041000450307040041c40e42c01c0c8000c1452105c92801040c541c80c42d0f82200745d00501c1c0040c2001d0911000905a1081403005020008450620b035038669900d0300f01d030361503c641c1d1410031001e42c0c1d0702110000340481e4064001c4000302080082d604031804125500a5500216020342c04a40100900014607004d890260584141400400060140b5503100462b20580c1c0307030741c0d81500c0c0c0441090018482119000d004a0901801250821031f06940e40c2c1034070382c24240400e401d440e210118155583c6980031000c29400e14664503840d64011075a68280e9010b0381c0280060380c2d4468500c4841c1d1000c2c0b1000303140031401ea2450200101c01700d1102406040b210a18104540d03501c1d1021a440003a0807020f64450611400c00c2042944040c11030900074a0003d420b01502c0c100c00d11000c406d40c00003075801141c48043c03c5101100500282200d010704103001c0188580508100303a8404840c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 817608543 1250 817607293 817607317
    0x60f030405030c0118110d03050306041107050105040309080d05040503070608220b06180408040b21040b01061b05150702071a030109061703030a020702010c02041b080c0a090b0c0309090c 82
    0x2029500e020b05101fa1440891a0551505491910b0b80403e02004144034402e58014034400c6c80990000740080c09410b0296000b5510a03140c18141081ea0b4104000c40b13541c02c0c2400310400c001c00441d18046140b200700d42c824100044940c0c0c8044192590010340c4040071441c201c02524407042192143c070440c01010269004240d0720300007031907451800c0302601d02412a840034842045065a420001c202ca0040010305250140708401480c0b68030070240e401325003008029006211540e80f0011240303071519003ea0a100021640c0c48580d01c0340000c02e0ba084015500d400003884060003082450f004004010302c83c0e203460005c110502c40b680083c02109005402c2c000001130500c89120802a426001c81c0a58607648491300b40d40000c1d800500708a040c400d0104840001d83d4580c4120744d032021060740c142c650449140001814400300420980d8611800d015040103207920280031001e0744d907040070407a910700110210744e2035401001c01d81036001c41c9030007c00401d1522000a00043c241c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 817609793 1250 817608543 817608563
    0x3180115050307090b061213030318020f0f030c030f07080106060c030210230114033c01060902040b1c02040b0d1e05070f020f070302060f030405030c0118 68
    0x41000300359159003510416516a102030030500c6210800d41c40b550303c1ca280240414900a01c3d420000c080500131500400301d02c409440d40d006140e054007840d8070400702e551550721801081c1d030001c3c0ba015034100b003090058080e0341c1d0a004c10b44040100119100d0014210340d1270003011642c0302d5441505000781c000a50a16800080c0c02e8001d02901b85d0b4190326801404103d241c0030480784c0102364030521442d0801284150145044007400040c0c080c08444c0140001c04038004103251504241c143c4142c03442c03005a02900c2c000202602c000310400060034200c0002d0312054100303024125580107594120301c00500019880c803a0001800903480c0c48040441c5c4c036014802c0c040c128002c6200d40d83d00d40c2c90405c0303003005019880d402010141710300140d49a0690011800000302c0d6800c860b1500810302c04004c00302e51580411030701c9040303a45140100300035401c55011402078010200003000c0382c24080081400c110040c01030340c9520000341c1c020080c0b140c1d144001c20860080342c60907140007010b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 817611043 1250 817609793 817609811
    0xc0e040f090311031e0c03090a06080f10030c050f0409120201150f1d0601020a060e0714060316031104031b050103112803020c03130e160e06070c0b031801 68
    0x8001d454170f80c40707400c0d4030006800c04c0305101c1185603c8090031040b5400100a04e5050341e4440c19083c020307000660380d5040d2413905945c4a583c0c40005054158580d003200381c104000b446000c4c008003901d1013501c0881544070740801290180c08000e100a00d0f9060b00340380c51603200c0d4154081403d00096034004200c2c01d0383c1e2840aa94420513000743d0440381400c0407207408401d06000c8460f00000103204a0b14074018036210602244d024401c051071a4102c0f001c01c02c01091000079013280c2031400c4450500e141420380b82684505012031405041c1900e03040c0c0d4201d60b5405000741c44c000c60b00401404810504002c0c402c154142902886012910301541c540401401209541882103135880c549503400e000f003401640001c80ba207515082680801410032000024005030a5109800e01c0d00390a440c20034131600b800780c0d001840c00301000d01845140d681140d1000c840c500403132065940c556034111508081c00d4044050b000410407002c004180404007003410050030407049800020411088 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 817612293 1250 817611043 817611077
    0xf0f020f1c0b07050c030309010609050604020c07090c09030209070306051323040c0b0a0c0c080f0a06090f1709030d08010b04051509030a080c0705030606130c0e040f0903 75
    0x100c06440710310007541124000007800c1400e8150700031010f420024105481841e019145520864803410b281e515620104004a0315004180e017203c1d08503015420b1111041d03400340d881c10300f03203d00c1c240d25481d1035850b030070305006130f22000142d9000741c203a100324070380f081016025003030611541303008001e2a000229020324a21a08040c86440301d01600020f07000140300c508004050002c1d40e55030303001e1000041c005455401070560740f0079a210020003460f242025a2605000c0c0d1200c07800d030b000302c80c0c00d4003001d038046401c48480c1e80c0300390700085081d050308011040544c50340c0010003140034207140f010000050400303807002c8034040b41210802010146d007151441c10a05c103c400144080c8800d204c0d42c03820120780045511841015800d140c8041e002034600702c649242030b601c6190001d821001c820701884581d014200581c010800350510f41e011580710300c4a4041811195582d0b000b100c00203200d1700008550140c01002070100c00301910b9044010003071074808802090440c509078080781c1d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 817613543 1250 817612293 817612309
    0xc030302120910050901030b040c0903140303040506060607110604180f0c1b08090a0e091c050d09030c02090c031504050408250f0b15031f180f0f020f 66
    0x80d2010f0700da10440714129405507001c1d000b84203058145611079841140300c1d211849004070041b82640e812403224611300703000c2c4485201c0c10501410707410400420010400000b030a6410044c260740a56540d2030909001d08001401803905074000400240041d841c0c94400c600700c0c20900d0804104510030100079900101c540d54040e00011800500c411820070407240103045c4628051001d1910340a0004002003c1507035541001c80040100700c03e001080b04104003002c0354002c0498030340200c1c24441c1014085004030703220f80c01020b40701d104a404040c8210041c07005160301402514041c205900000050303001243c4400312180c000c03410039036916150141d07902540d040014140303080054070000100765a00891800f0904081c030310500001c840d0080311748910b004e4529030075203050001c448140140201607640c440c2d4084c3c21040030341d4110800402c0f10080812000034424101e803034400c400794041001810309650710080400384070804103d0034916200300c0c3d54220070702c03800041000e15 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 817614793 1250 817613543 817613557
    0x9051e010b0a020c062209020a0f110604150914010c0e010e0d0b0a020c030a080703050a2315150408070f0f14030705090a0c0306050306160305060f0d0c03030212 71
    0x1139020040c50540707414008010220252154069003001405030180c40e08907a007584801c1c8415400503094100796404031009076104018a40125241102c000742a030701e140180000c1c0c44a03000e441d4810a18005a0201d41c0181d0b00c5049413103407800700c920441c000e100300b240e95404903000c0108240d5a61140401350003150000302004c102110030340321448400300007005845d40b25401c00c142001e605007000644940941e0b0f645900841c54a840700505440c4043d08a0040d00d04082411039411640b5450048a94110703403103258903034520b0006110303440215121a003201c3d05001319200440044010003e40340c1c070300119034040d6520022242501000c1c86454100c95602106100b800b5003181000d459800080c1111b0446483d14002203280005031010300d40150349100e00b112081e09806410000d0200301d019007000e2a00b142003481c44240203d00d6030425590b607000441c00d40c1c41c0181c01d2600d22014042d04462901071601049003443c0d800240d025100313100c098401c441802089a0745 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 817616043 1250 817614793 817614797
    0x6110312040605060a0923090f15010315090209010303030c090f080703061a0f130f020a030b120604030f0f0207120b04170702151804090c0512030f190909051e010b0a 73
    0x41c0c7c900700a04001401070031000aa01900c5000c0d0703480071042000290140d0400d06a0040b54510720700815903000000041400c40c0c103190303001c0b0240c0d80c0e20301c6460440f034043c20040380001c50000221841ba443e07410018403541c1203030002c51411000203001098034400e4004100f021108410002241c101d09401da40c13020f0548141c0708070303040140b4901000d4039881d00120b80110284100313411b1384c0140c92810b0003e681e40f103221829140c2140e01c3d034400c48081014100741c4c10300e40c5000341304c900781d401c0481c14403403003030000203a41e44200119001031408100d00341c45000145000d45e032039602a41c3c240c611050210406070341165010880c0c01880d0b00500a48070300344a8024103c80303401031502410511074180b505211522280580580c070341c400c00d01502207034204000c02c10900614034002c0c0040d070090100414040c0641c0441e4101022002090500284120221402d201c6908100c0465042c030341030003174144002421074071200260710b03601c1c0d445c0c1e04ea5610105074002e0400c80c01c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 817617293 1250 817616043 817616081
    0x203060f060901090806010b03060a120c090b0f040914061602060f15102a080409051314010209030705060c030a0327080c1207050706110312040605060a09 68
    0x2140746000002002d1042c010b043c4140c101d0f42d2140c500c0d08003a02640051180640041000b240e03143c00714000c400b0380440f00100b651310b030b82501e401c1030002aa005179140e0a5980949903c907079940f0211004240b0014001c1c0300c803511918010000329088400d5800c0b520815001c0f07403101540c401c1301442540c0c02d0b4010301080d0740c0c4000314841480c01400c108405810400034090b42d0311500c4030008558120748a04080010101c401a44068141041400918503039511000102c0c0002120111400b03003c1c0410039440c0c3e401160604107001400601295401605400d0b00c2010340160284020442c02d0310407203a99a41405a076109d014881c1c54250010040009418000c1e444244174003000c100810160501c0840d21040030106907080c4c3e105400031928076405002005858241c0c00d01c146140d0805165640700d5580704020f0180c1418042ca44c40c01d038032500d6041060f078008103e165610140d50800341010001003105844542c000c141a5602090109150080790b8056040740c40c012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 817618543 1250 817617293 817617319
    0xb04150506030f0709031403120a020a020307020d1a010e1503060c07080a0c0c17070f140d03020a0b10050f0411030a1d01020315030f070b0301060c060b1002011b03020306 75
    0x1100f00800100504244809080040b010034034008207039043c8000e140003141e0b00c44000d41482802e0b40e0042c24450280e0040041a0407141d0120648a6041c5d0541c1c24403200d050f5850100031041505a0041800e11501e00015084201c00c00203401044054011001e4010307000034552140b0003151942503000d001c2140e000001c60860042c40c1d00402854444900d403416554105075807080d600c4480000e000c081008010740703090029800034620107450f5108149461401d00140b40c10b0807001c4e1180300c809001c00c043c0740c0244400b24500c1e60011484c101858012220400e0502d02d01859025426600d4146060300b070920800c640302c840100c00a0039980e03004010f2001d004451040c0685119404109140c0305013400554000d108021003070841d510f0700018140303041d041d03081d03614031607008440400c20300c0380b400101c9040d03c00900d46000b5100c0c203810320802501821104076000000036010280540e4103500c0324980c070034400b6448031000100e10003107060b8001603c54030f500c044204111 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 817619793 1250 817618543 817618561
    0x303050c0a14060702010e07080d1112030106020a0b090604260706020c0609160f06051315170703060506031914040b0403090e040b0f19020d0b0415050603 68
    0x350248892400c100c8400e100560303074244a00010b50454500d640c4450b090100b459020b02a030310b81400d811004100031403034003807416982e000c03d041070024480c035243c1c40310141c0401d000ba1070030707c00c08051859603540d40d640d00a40e6540b03948402e039102c804000c040340400c20081641801103401c1070102b039040c9882d0340100f085406410090925107030800c103c0c00081d01c10300141214000003000b5180c140b1f8421221410701403c0404181000386e40d8200784a00c06480c8002400d072078080c03401940314040b88040189459498100800000400131040300055020041d45601c01c01201801d41ca506c50780c0341601510780314080c556000b1010300000d1a035170300f1021981b8028500070000314102c001c80000f0ba03991401a90165a103c03014000c000070316401400c468014240425150580d241c2500d552604080181901c0e5421441c9404118208503011040d1510449980c003155210304500325003000b04a440b01241c081c0f4140601085c028120414910480d4409844a86155500da101e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 817621043 1250 817619793 817619797
    0x30b0a1107122f1b01120b03161203020706030605061c0605150a090e041101030518010f0e071e0e0408070501021206010e1e061b0d030912030207020a030305 69
    0x1010402072028034664500340408081c880c001d180c107015035454030080040301d052500300074004030300000300074403200c13030340d90007041103413025080500040d079103c0120000b800c001082c0c1022840612200012849403040502da548540c860b800b03c1d5119540c584041d001e42d010361040c681e0102c400c1c04685103a0001400314801d490070403000190b0103498134005070036500c0d00000b9950844000c40e074401d00a4000001402034030719004005505d2415540d0700721525031005407103040640300c801260782540318a1403006c0c58844003000780170282d112070700000141a01100302c003052042800c0050b107d44071082403486034100001c040c0410b810944401e48000d005042103817042e604002100100d0303030a2015110b80030510306240c505007031a000040141803c0740c2c0507440761039502080100c2d10200c01000c102440141c03000e0781c13a000a00150030b0031010040d04000c41d800f5001e00800011790581c460903e480c401c44001044980303403c001c500324020340e80c000f5004a0f4544040c40840d00641c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 817622293 1250 817621043 817621073
    0xe0a0818040902220609090c0617010e18030c0a050d031103040b1b0d1404020f041401090b01051b0105090f4c0501140612010504020f040e01030c030b0a1107 69
    0x501241701a51b030074640007101d50302213041d201c01c0a441024416140d002030481342602491035040300c41e5050800c040300b05030b006088103940d407850900400c90b050003032042d590103140000589240706480c0c1802500c5600e00040580000e01c0e0640c4022080e20400961380036035001131014045a4a40b441e580d001412000c0071010070506121011001d0000d0181309a03869500310340007124145403040c0001d030302019140074821420200d00d0004100400d8203141158510700c3d01055407240c010050354a44941440081c840b0300680c0011914841500b2507402a00c076101182d03541c0d109000140d0325000641913588800210b003107003002d00d500f030300c1580102800e14515000620102401421010148408000039a1319000108203d281c224882c41e100c00007540c1c0249800ca01203240f558a1505000d000c0c4142c0d400b14068049400c01410b480c007409040d032031403086503104d0404010903249032108803081c00700b0b0780000d008641d650041e04240074041c401a800c0622607a0340c041070341c070351342 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 817623543 1250 817622293 817622359
    0xc050c043602120a0303110c03180609060c01090506060301020c100c050f030114090a06080a0f08090303040e0f0601090e011401120c09090f0615050705010e0a0818040902 75
    0x20003244050f903141040c41d00705403400c400400e4641110310f0080c0640340e01401c2d850f0082800d100c1c0704083d50020044880f4212600520380c410a4002c0c002403403401b9240406170400000701e60b603058640b05601c07072820700f801030040b00c0c0d20369a00300816080c0e2040420f0f904140d0081c0343c40b10318042440d00410300b07101c01802c20134140f002210005101e034000741d215251400a1306003445160404440c0c03103800c03000302c4406112003424042c2840d0b445c004560020300d11224910034106200501c000d559608600500b03a035034940d40c9040c50440704e0310990310060041a004003040296020340c00620441e030b4402d03e0003c2c581c0c40c003003140b5603038801f21102c0c07030601003840a414016100c604c00c8403030801c81c0342c03910407001d42400c4806044491003549102c180b4607000302800104011420306008003000d18145640745030301d00d1300710b02524034407803009103501c6414404d00c100f002e800050644e13600b10003d0340010010900800c4140e4008200280d00000d00482c0c00d03898150088e40381075884410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 817624793 1250 817623543 817623641
    0x1229151507020a05060c0a200f0108012d0803180a060503090705121f0c020f070807050d14030d050105012607050f09120304030c230d020406090c0c050c04 68
    0x5525000c1c0c090b80115035800c00042448d540e83d501d86007200e0100200740b402c4c80c00714450340c106041080d41410500d810140c80008105441250801a010f1000303810a8000e480d01e03070740310006030440c00e0761a180f41c1d8410248000007164040c0700301c054912401a11005000d441d26081c10b2102000b072100700f0305010f000c0c074186240580648103042c41c00540300ca40019001f94403120003810003042e0300d01200031ba0010a410842c4000014800c410f42e001200e880f0b00e520b802d460400c04030584d0341480000f034000802d5820000d80e45a00181c12600c0c02e032110710907241500000d0400c221101c5070310765003d88030f2000c2100b49104a0292001140c80f080403440c0c800c820000070720f1808031042406c01903000003000c1c0104507881500c040100309080d08000e6000c0c100d116480c4e4034910864840c000c0d1001d8840505556594002a000f03201c541030811044010399001440b4062807e400d584501c2100081c4e0740c1424140b08040030145030150000c00100b01c1c0c5816645100700010303d01d0300e00c080e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 817625899 1106 817624793 817624813
    0xa0e060304152f0c07230a06030501060207300312020f0304060b0f03061b04090f0b01110c030d050714071502161229151507020a05060c 60
    0x88100e2201050039489480c00204040d0380751187d0041c0700310000900c040d056809281611440c0c0e00340c42510362210900310703000340a80d0400104010300c080c40004003c0054a41c40e009210b45040344072580018850300507a044405a20704100000003444100611445009400e03401600c03000340e080e000d41d001039240e0700010091001080c02540d41803c002c0048116000307049101b10800101c4188148140203061041e4014080f0782650600d41c03001c0c3e0005001c04400000900400c1e200100c244205c1d050707001154115a0301040500d0020314100a000c4440544100601035210103c01e04009282401140322480c080110480038000340f0014071440508940100345c0c640310140054100440000d00517250807850309000c14014504003020302400d032070108403104820301e032420b08506614490322000a61000600000b0007075418520003810344000b05a041d200c1c0b80403 = true := by decide +kernel

theorem cover : BRFrame.Cov 817446043 817625899 := by
  have h0 := BRFrame.cov_init 817446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 817446043 ≤ n) (h2 : n < 817625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
