-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3991
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:15:32.627725+00:00
-- url     : https://prove2.me/submissions/68063dca-0b79-4c7d-9f45-3aa844b62c89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 717625899 ≤ n < 717805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 717627149 1250 717625899 717625927
    0x50d0215010504060f06122c30071b261615030e07081e06150409080f03040605161e180305070f0f0f060f0806010e090901050604050106021204052103 66
    0x7a6124200403034520754864069038040c013400f42d008988120300c0e4030280e01d5504114000340074651081203941d0f4020034845810b9010951a0032950002c1075030043d11040d07400c100e070003413354035400c002000c150118000015081c10300e4018003942e4641c80e4011044d0a0080e007148004122850480b08919a10116961141c00c03280c04c0748400307a03d54640099100000030014050b00317440e0038541300c411903042000024440c030b031000c8940c4441031042c5525100120051481540262004111880c100344140d00d542d1200c080e01c010b003c400d6030504400045120403e40003846818031072109a41c4e07541c020f01000c0740e50f1005003244115080030902010750b0f80404111141e266070184803c0c0c8a0fa510046031a4a0041c500003a08010342c009a0b644540c507030580240c818105420649036450200b9803a000c02c803180009a074444c0d0500519080c00c0c40750750f0040c03c251002d0243c104560000000c0341c4200d21030721b441901c80105c0b40b102101f01c01c0303450040080e075200b16541c440a10b22014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 717628399 1250 717627149 717627221
    0x130902130e040c09180c0e0601021f0902180103030e0d02220902040e0a03080f150901080d0809031e0c010204090e070e130c0b0313050d0215010504060f0612 69
    0x11a901c1c20402c141c0740e50168810803412059201c0c0e0246006c50920070b400d00b5010005004074118400c084004418002da94180f4850740076201700416501c8040c010700014851302d201450f28084241c0041003c640d00480c0007040c800119200203800d4800c1c00094081d00300910005078400074500704024510081d030180080c607202707036824801060000c0907151911007200004d0041040f031800582006810503020383d1004007031840000340c0c55190080703110881c1c01d030040342c5260300003c64488042d800c840b01b81c0e0300c08a24070083d807502c07905488086212040000407505081c010406d000004002c2d010789003d806802010005480c1c0b040209645480341c1c8900e0480fa000c2d44045002c400c0001d5a081308a40c11041d00410302c0d14041c0700301c3c40355000602100c002c1e01341c05a880c0015500723004034103500c94554028280781d038910201c044610390603808148120301e803280800c600500401c0705800c45050b4101070200400181072a40504220414141b1500340341091041d000e0601c1408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 717629649 1250 717628399 717628409
    0x9040b0303131d06061e0c0105010620070810090305040305010c050316110c09041103101a01110a080c031b0d090501110c150702030a140f03130902130e040c 69
    0x3e00125241d038000703400f5504068a941e50000c40411100405001182c031303600b01c800c0d41c0d840251418031240a4142107034020382021000500c50f03c83c0b40c00000701211505038100c07250028040e45850b11052903070714884810861003841c2c0301d03103240080c1360080054400454001d0b0081c407403c2900718000f400c1e07038000c48201d482821900385541555100707502c08011000712900601c0c55102d450100485550010b01c2113034207040f540c0e0074802646007803220a445481d070307030000b26450750241c03000e1043e85400710045040102d80c0c00d8404000e1400569403007020780180c00c5d04e84c3e61500000e51400c1d442a9860405025115000c00c103c00000042c40b03c5156060365403001450384440044520300c24500b1000e920354000c03400307040c3c1854824002c0070070720950341100b0b02d00281c82d40481c0c00d15a84200c00c0d10819000030342d480d02b0080c02e11a0418007183c2e14044c0d031405c04040c19200f5040c8450064a0009074041074a41035070200380e0140d0080c0c40041c854100d00c1c64245400c8500d901c440c0a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 717630899 1250 717629649 717629669
    0x120070f081e0607020a17071e02090105010e0906091f0605041802071113062303070e0f0c030a1104030f020301110c030a05160c06020708060609190209040b030313 72
    0x415090b0341d1011a041c0e000f50580d6010b001c11400c0ca856000651011582c200d003803c104204600005810303040e0a580078465040341e00800310140100000008160301c29130502944494103111542c4103404298000320840d000d00d0103032540800c20b10154038500c20384011903080c80020440541210150003122081412501e400302c124401401341e024441c40100750722074042d0501c2c030629048615030081c601c1c0c0c6d2000509140e480500103248400c0540c401d1015545207907105907410188265005040503200c00b00b01340c202080322040d403100007045040180c0e000300104500042c107030040c290480988000d1a107031501c1c0e043c81030340c5208880080348a58a0b14001038042c180004c141c4081d107038000c2c05141004000001a90b0981c092082800504154400b42d000611251030f00405030010350300a200d170908000340e10785072030b00203415248158000d45c100041c8280c01030200d0b0183c414a540543c5583c01c000c0403034054034403000c0040e49400701240d4a91901c100b603150a0490f500c5001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 717632149 1250 717630899 717630943
    0x3080d060911040b09030f0105130501060509040302120a17010b1c0515010507021c0b04030f02150a0c020c03060711010f09020904022b08040e09010b0120070f08 71
    0xe4001102c0d00ca00b51400c1e4602d0a100400c00081413a018146100001c0c1c241c45040e03120200312400c40782c01716110001040c50340401018400d00f4400c81c2e02030b0000b518800510b0800ba2400303541e0b00120000e1070301d210f90001d6085541440307107042d0b482a40503013803d80000c0d6110400c182d110b03040401d03100752802c42c00b40c0d000d00c2e48003203004d40e6001d00c00344020340c00c0141460700116071079804202c0990304140da054281000007440c1c050881803d0050556403090300b0030740b400402024840c8501421035001911b0b03000ca042e04070303c41980040704054001416800c00ca016820140c100110039414044d01e070401000b150440200061044002c008200b4602c0210781007003143d58105002e03402c4155600001c0040c1030544075110b20b13403203003400082058140602079080180b5050201c411300740c042400c2048090590003c0d40001c1000d00078072031403c05000082134024070107007548070380895642105150344207008160103002080c2c818242151030f5404103945069110411000c298040707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 717633399 1250 717632149 717632159
    0x1060c0605090c0f060c0313080a03030e12030a09150510090c1407060c0c14070303090b2133030c060a17070e0907030c09090e030d230103080d06 64
    0x201d086080a0b1005040b50608004e54081c40a50f03004000c0005141c4403c200c0a2800284240448000c0201c8801084d2501441c81c00030190303140851209095405141074101e900c2c00032003646d41c848075000300044d800c801c1d0704012014091b00d10300400c07503a10300320a00841603134503003182c4255818140709000c20000b04600702d81c025141000301407032520a00492001401d250000c0d00b40c14080e1821074001d0340143c48030700b403030001301c03aa410340340c2d01c202810410150081121802050f0034a646424690240442d070006c0710000c01499100c042580000d09404031040034064005103030343c0b00e07402404008a200321070111808401d10a2194508210607481d0201c1150884c450b070340e031030802520f4130f0369821940103c090060360a0010001c030f21103082d21001d0f030a511400c040d9901080c024800030014200204c00d4000c100b416050024a0030700d5035002045621014200708002821100c55281d105202c0c20001c0b1a00e1070302081c00004140b080100240000003000003040145586d14 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 717634649 1250 717633399 717633403
    0xa0806120c131d070b0a0e0405061c0309180e0709050402100804050322091803050901260103050102221202060d0905070801061a040317030c1201060c060509 69
    0x200c101d0541c003800414008000c402d20b0703005004081d000010f03070fa4608035592155401c2c500d0070340104a5094001c1003500c02c440c1d22105400f400700056900308940d0500c10301283e41c0b5008112242441290710004c041014030500d161001085400d408a10000e00c44c40f04502901940d1803084041c070076820040380d00700c02031042c540190fa0061a440c03404801002c10385540200500981c0c3c10700043c0a86002d500350039081e404100c00d500031401e1154141461481121001c26507602c0303a1005480d1000026082070032554681000d01780422a00e0b4906982340b10300c003000e0a240440650000000308214054028043c1c14881b11600440000d0440c0c1d40319420403184280b07120740403072040725405418614020904210050700c045500221078580b240781c04216800103c0300d1f1740d2414100710310740d001c000c866680f4070100030300d603c5c29186888440490f044040c1c1030a00e01d40000c007203004441d0700c8044a40041003c40419034961303484002414820455400741c0300e590801002030504040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 717635899 1250 717634649 717634663
    0x80c0f0f1e061302190305010507090e0702030702100305060f13060311010c110402090d051b01081608010e0601020a020a0b04031704030f06050903041e03140607050319020d020a080612 81
    0x220f0202e80032041078003048049003005044955205500c075010000c03070401c0c011740344295895146c0780c040300d240c01c090100880e001450b01e01150003d000210040e40d60510702550308549240c0031605844140c00101011400307540301e9070100e00e0003411605a02c007034020b8400c41c0c0c01000c10f0407404401100542d2062034404000b0322030f00d19050440450300e4254060b1440680c00f13085540a100c8551fa41860b0002c2c0041d40d0050988030000002e40b9079118981551001010000044201a880b0041e1a015040c00385000305000c0000007080c42c2d2080161552051300104030301441c070760300c1e0001603690303010380004c2d03901040341410050b04510840451742103941c403011485c0744140c0c640b512001020b001d0031008a900040000090680c065918196550440760a4108882ca1490014481c00a10321615115088002003226154004003a654480049880c0f1006808000b900744000e210f21625045694030120f13954800170f41c40210740d8450740080d1242c4c00014220900a40d44001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 717637149 1250 717635899 717635911
    0x20901050d020a0201060902182b030804080705071e050d0201050304021e0a0603020a0e0a030308130606030503030a06051c0210110309060c01020c061b07080c0f0f1e06 74
    0x6000c01000c1d034400240d0380140316910340b610000805a89030480a001d0740e0002203650074902010b800b07040c16240000c104032103418a00141d42700031003800307050844100500c81c00340c2403003150000503042c02085800c981d400e41d8840c05540e001501c60a1101c0304000a01112809150703d8a000c01d041c2000e145d00c020b10b5805031030b1581141e580f83d003081240389409151401406105540010383c0e281c3c0a0041c018000c251005621000c1c0000001c1000140703860003449007000c11070400120703400071b59080e009440c014a403219440036040800280020354801007051100204108480c03150f54040c20035900200e03142c42807417115080420a082842002075448001c60131100b1041e802160b04140050b5010162410030080600049003600041400d03840c90350005100c510a410502055038411482d40000440010405450b4218000d1030001409003100103840003101404003e150361100307070311048070401c0203550030047d111504042200c00701e0072000f09000c0300d118003180d107a10440b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 717638399 1250 717637149 717637157
    0x91214060709060f090e0a0515220c140a030b033c240702120412060506060f0717190e13060e04020616050303040317010f0b2205060a09090c03020901 66
    0x2447c0c6501c01d42c002d10020740017071030340340c1410300800e020307116042d40415a030380e1208072407142e9280071040e0f01034030b072484190300401c0b00303130700c038103883c4200400584803118228070b07000900391702c0c09002c01d00d800e0941255800c3c4174801c3c83d080c0307007400b9214000300420803506408520380e408095026a01c08800d52080e481032220140d44101031440c0740701b5544a1034510440e4520361400780d050900384c0c0709400544a01c0c0c1c0c000c0308141440410b00403a40c00503030980383d00c2c1c40c0c0071814900c01164054a0001001201565428840e800303810081e00d11443c1c070200c400d24030001961000d0180c00e645e0241c6802507074505000c00503107086104070011150310302e02d800301c84d9840790308101c581d50200d0b80e0010040d0304503c00d10003154040015500c070341c1c0f01303403203480342204030800f01010400705a04c1071018145a03c001c0c841404020709803010398580c2496541450421007120000c0d4125801060b007048011500002c0f072940120700100303e4141080c00c020084500c0011400d80c0300303807103c1342c0c086 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 717639649 1250 717638399 717638401
    0x4120c0902120a093813150903230c1c0f0c0819081008061003021c08030718080105010b0a0f23070b06010f091214060709060f090e 58
    0x301e078a4201c00708007071040c08645050030420003941c0c1c0b401c43d001006402d20020509001c01c844040f9070b241d800076021a14008203500e140c1e100300102c03008014100c40991141c4081c4201802801c8003a040301a1695031000c1c000d400344240485e411020003544bc034032941d240b50b03404078151121816280740035600e128004400740c1050382c03c0284490b01301d0300b109080013071401c8000d007403454900c0540c06650b515400c1c01c140c400ca205c8610306412482e0150003200a1040e580701018040b0101d0b581070358024950030340d910540c11300008245c0081d004072030000c00c100515502000350700c041d6000700322003440c40783c64280c050300701c400034000d03224144030401c80d60a20500418000800006030b141c014103410b150300d00014aa0950401808000c00c00700f103e1041104010040750b02030428a00608480503800d401480d220705482205002c0d690408180248400704002010040313907542164514100110018024401c503c07c2000054039131001801d013038800c041400846104022501076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 717640899 1250 717639649 717639661
    0x2004171f0903080601110601091806020a082e1a070c0308030703060e0105100302070f0f1506090c080c0a0504080102160506060a080a03120b09090a060507020a02150d0b0604120c090212 81
    0x2000d011852b0001042c07050001c5000883d00d00061403044801d560750082401c0521404000c00a80d40414825448106010161104a00c00c0c1000c680b80300010142d62440b5003c03524841c8900280a0514140c0c801c0c013009000280e070003103029079665501000301c01e5680210f001c40c00020b00805a0107084c1e02d901c900302c1480382d000b51103030b07030300501c4400c2e82d560b02c3c2d58440c195201516401c503010b00c28207055944440403031007042c0041c0030084e010b1040450500004011000040c2101c4002034041081081c451049050b100a490881d008661303841426206644034a41d1a1088890b4802d02c0700140450401602c20030495071010000c10b05110300b543c5c181d4030180001d51001c0d01c140d44052001c8035544030160340b402240224081c201c12a05c0e41030040c2640d100070181e10640d400b96484800503220f16203076542d42098524115155040d40903a00082c0c494000d05c0c0d903002a0118011800700c8c2528008103205d4855401c44260680d526145400da000740f022a0300303400c20100c00500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 717642149 1250 717640899 717640901
    0x906030305070f03090f0e010810270516060503041205091011030d05070c02190b040e04080f0406052d0409020304030e19092004171f090308060111060109 68
    0x920300b48641881e403a1700d0b031200d00007908244141c0c800c070505440c41c001000407100605c80244280986071062262002581d8400341030f407400350f02c1003652070b51188840c040c0a03040c0127403205030074800740401c0320b5580c600c80280240c006440546200c50150040104d580c001c80441ea2103c0029143c1c21042c3c60074007040c2c8100c400c0304a64200350108211b013140082c2d0703602c2140d01c00c02c41903c80021501d6a80140180000d08000034000420402414001c4a000c80e040d0f404440c409400c08015644134a401e2481e401b078010b21075035514012501298940d0020003904042c0c4940003403d0000442c201202c50018010b4000c4100d1001084280241011900110b61180c020300f0710154104580300810110000c030680140d002c0107001007484403a145000d081d541959031294400c1d00620f01501201074491403280c51141d6401c0c800303040c0c4003003090203041070710b0101c0c442030400411701e440c0307540c0a45443e070022000a4240d800290096014010b07140108003900c1c01020142c1c20103004030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 717643399 1250 717642149 717642173
    0x1060804050c09010308070b1005060f0a020106031b0806070f050a03020c151801060b03090c2103120709080307030905130914070503012a080402150a020d09090603030507 75
    0x294440c007a101450045483c1d04071454001c500ca1000e0681e034880500f8216481800682900e4010310110340c10015507942c48142d800c0070206803051942c0352040d900590050140b580020100c0d00400e00000031124110080030881d14440c09031411992014412104042071229660200d2170031300c100d8480e10b00c2613015103080c00020045511a10003000c011038402400c40b44030441030955a0b940f1b101030028000d0b01d00402d25050300500b181085402c2a40b80c0e030311901c0860244090344001041034440c00f8a0300d10300c58040c41965030700c013101d1240400780082201c05070003003028100000b465200c00000c070341440d60180e80d944451403c0c45c0400c602d40b500c4050354032001d80c56a20100100f155100b0001c1c5010b103070801407803218540405c1c142503480f80898096040454a4400481c8404451701c8000f0f1040d4613007180c440e0380794800900c0b4a0074101c02c070200701c80c004c50840c3e0040e400080a4007140340c6a111011800d41c1c0d030020307505039582408010005001488408001040c0345504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 717644649 1250 717643399 717643403
    0x40303021b0406030633060c0204050a060b070605061e0102151015020c03060a0b1e03280209010e190f09050f03040f210b0403020f012f070b01060804 66
    0x42038140c0c0d00d8541d070041d11041e00320b08184c040549514a0a46c00030340790340003660100c03101445c10380c0c0b90000c0640622148200a03000d1600e42000803030024803a80288003401e00c10760034545a85103410650000e0030102c036500e014902203400368800d40802e00c41401d80300d005034020302d1002900029408980e801600e08441c1000e607280c0800c41d440410301c1034584400356801400401e0801302054941440540000041440c10035164826200d4404502c0d0600c0e010240d81c01403040040440e10b00110b001002910400003d8081031341000d0a4102040b18001c503841404c598131042c100790184420b40c2d91460443d5055022403001d80b0540120550760b459040c0083c41c00c04c2c644a250800614402d605100e400001e402c3c4059100c502904020300200c11002c401001460040240700d4220310b8050100110b403c0040c003012300c03c0002201507207038040240000340340c0584540112291400c4600d24140d01000c01850522010650f010650032041d100110307440c080c41660403071000303401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 717645899 1250 717644649 717644651
    0x70e030a08070f0c080d0203090a1502030403021909050403200d0e010c210305180f10380a05031513020307120507180b090a050723190203040303021b04 67
    0x10005e2190420300400036030320f820303401960745e4000100400641c0d28850300303d44003020304a000d058045078000142d038140c036415a014114007020301d0341e06010300010f83c060707000c65050a0801c410183c1c03200084140070301c0e095500801403103107042d00d0f4842c00e40c02a10f500240c540302c2070141075807041c02c2e24984a03005034030400c40820343c0d00b148040c0f4128021044042390302c40e01400902509031010003142e0440c28083e103d4160301c008d13200c4c2c4070f60704104044040c3d6181c040250a00100d816001040344102075190500e042518016241d00001031440d4401c030f103901c80000d400d041c0426000d8514a000303106030344076510f03051280c0c0c203c0103550041e41c01d0711403180c0c041400c0080244150000f0b01840084c06032030301d400703507036403000e00c030028103d0209007480165411610b801a40d241c00600a241c04240c56070303036040850f5404190142260150400349640c04901a46402048010b4032800301c1d240c1011b400710241e030ba0348114400100142e020402c050202444032003042d44198000384 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 717647149 1250 717645899 717645923
    0x120702011e1437090b061e060f0f0a090501020616230c0303040302100c0c05030d0c23030a0f02040f09050405100c17090f340b03070e030a08070f 64
    0x20081e4403030044410f2a4111540c3d40000003c0c0300c034010700a03074849011140c00412148660000540b5600d0402241c0a040d01181d040790920345401551100507200000d039072109160f4400a03c00c082c1441000c1c0540140030100741d210308103442d109480076840d140c0c0c1008c00c0c00c3c4003c5000a01c0c0790000c41c45420300c01d12981441b108188000e40c010381c06507005245448001151004880b660005802400349602140c00000d2011051368501101c4010004411105803800c0d10f6403c007031010010140c0e80c6e51403508600030480c024500803402d08030304119401060002c00c0483c81103000f20204980151800c0089020f140c02007644035100740c00f62155070080c20035110035101209411030203d0048188004200e040201c5144e00080b588001c013184043c02883c1510b80d44000d51401c1181e0300e03101142041040b017080c2d0300c0716000324840b607040c01d69100c40840040c0c00564951000031081c036082210b038680000c0c508210b54004907064508869a524481c012043e940c00f00c6000400136 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 717648399 1250 717647149 717647221
    0x92907111b0402090405070908010e03040303140306010c050f10050f0106051c0b060f07110904021309110a0e0906010b0406050906071407140f030313120503120702011e14 75
    0x2c01346c01e005600c1900c0d4040e955043c020801d007036030200c51503c000c55206100420200f64482c54003d160b90243e103c1e25907036118000100d50302c0c18509005406845640c80b022484040001c12007038481004a003041151590f403074020803180b082c07040300000350b414480300507180c0944841040e1184600800203103106803a021030440e40102140043d02107020550b9811300000ca102941d0250003101c090106260550000740384514600341500c0c010341e245200b000700a03103860350032030300030000f07003500f44c0642d6440c541d0440150480c0c80007654007500d0000650203000300213413070a0b44d00988031a03080155040500603d600001c505a0340002090b40354460050b092100700041c1034501d400000c040304035010700005080c255651030082e40101302d044004100701c1c40600c1941c903a04040788441c840d506065195009100d00c030004143d884051002d0160158040b803001428007600790344404c2130003080c00488448030368010342d01d407605001601452168280b00500300c031421310204004c52803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 717649649 1250 717648399 717648401
    0xa05092509060e091308030702190804060207050d03020a110a090f0b030c06090f0904020414100e0601030c02031e190512010905190906092907111b04020904 69
    0x500000011540c018000e0103003d40c0514490300d10310302601ca07141e032800c0c10b01c0c6150380b085a060300a0400c11001c004182c0040c400e10001c494980a240080318811141c100401c0c035074064801d03100584518080040e050524214514582d50141c02800720b071649500d0b6650321018072449039500400c1c4800105a06000d8031030304540b60380325100003540303007440c006052415030800340e19881601c09210002041e17031b8000b1860035035003040d1031952054459101107400f030b004000e50f104080c0241d8040000b4000d5481420f41129845003944109444c0d1030015001c84032115203150050b0000c01c80500c520048014100c01101010111403605901e1040402c9600000035441d0000341e00141043e014410540a1409018140010045818a00400c411008101286065203922000310f0310038006a075101c81c00d241d4100200e050342c520300c003c0680e1520208402c1d0110480d210000c551954410344100c1c14280068000384401200290b1001540a0010a075a841a02044019455126 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 717650899 1250 717649649 717649711
    0x209031e01020703030e0115170c1f0f1404050418050615010806030106050d1b080d090303020d110606151312020a080a030e060d0209090408130e04020a0509 69
    0x3081000503140c001c03d140c002c080c1c801509041d001ca0303043c40340d041c00c0c2d0001031041d4400c0300c0920f00088103600115107824100308601140542c4200c8181582145481144c03051030b0303e00451b66900411030356110143c5000d650415001406102480248407604095108441c6440e0803501944031241c1907a40510b000000c84050030350b03903080c165180841d6003129090b81c101d00e0460080c4085030805020400481c01001c01030203000f000f84040106070004083c1d003010700012010741d40c403012564400f500b02d40461100b2030061080c903001d07419051241105414040c2034101820003600d441040152850300725100200c2c44404110700b80d011030b2038034a03400060080002262503100d070703401048080e48803680004001d405c0b101c240d10000e07510400c0e001c43d01c2c2c0708561040e00d035091412010020301902000780c0c2c20207004024042404001d90150003004810b20300001c1e49034031604150081e10050754000e412101c085018009850208592a449070000f1101c81c400c403c0403c0810b05601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 717652149 1250 717650899 717650953
    0x11010519020313051503043f08130f1104181b06140f130902070f021c0302030d050403020a050d0c020a06171812040e0f0106030b010f03020903 63
    0x2c40024119526540c0c00b201400a00381101c401003031858250880016100050000b418003045e4442071013005103507480c00c141e4003000600040c140e008c80b0007004185004442c54000708031078000240542072107464100100d5030110000c4480c01245e940c140300090324085880c3c0c096180c241c43d085915941c02004421400b45801c0412100e02a405040c14419500007104004030302e100301695605860449032041c0412406550b034504c44e404881d81850903070031802c181d9000280c00400d00600740820113201d0300844205d0030415503400070060540b10b030900200035030001d002c190490403c55100030f61180c06401522198400c035582e00f41403411012482000c905c0740c1559009500300101410081d140600b802c03140403000142c041400b450061644041544100d0261048001071000308207800050307101c5512207441e88012607138108100d4103400d00f5249440001101f40c440d015943c0b4443c2f0684440c440304030601c1084029500251a480d010b118030000407401c50400c90982520b90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 717653399 1250 717652149 717652153
    0x806031e03040312020c0901150c0c08030d1b1d0a050301020705071d010e15180106024b0304050d12020c010c0308191506030b09090a0b041101051902 66
    0x2900f51328003400502010f200840c02c40d405683d80390120b80786e00400606460741d012404000c0e01c01e540007154414000d50004011000148000400d580d001015044080c2d2060003400140102d584c4101c00724031048003140054400312110030180c04446004041e85409081000c1135500d640201e42603a1152038222104d40c40503d081240b461441c08009080501d140c030405994500244da02e41c000c4054800d0031010580d0401d400e0a03a104845584e12000c4012092440e6942d1700e0b011351503140000e4400e1050b03100140e20f074998548114121100d107031a0340702c0c2082d840040e04040c2c11a45682c10a207640c4020000400c05699124001c1c0031b0a2280030704840c21820b1590003800c0c050700480d110306002c2900408030001303070018402c1d0341c021840104000340514600c00b4001500181241c600400100b0101003103607070381030b0401c0100c1c01c2c05032201c006988500c0096990b800f1242ca000d0900c5072406c0204000074482516910aa130052606906102010b00c0d1400540b0400417214090b03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 717654649 1250 717653399 717653407
    0x1110c0303040b010e0c1e09100206010f1208190522140301050405060703180f050a030305070503091f0608100b10030e0307080307031112041109070e010806031e03 72
    0x3218824099000d024840f10580701742c10000c1d0010b0380d078081d0264952002142184103c4000000000d0361784035a0000d003070450b00c000445010f92218004c1c0240c030311424400b203000ca2218480c01c1e04440d560f0344008041d00e0428010303a01c682d5201000003000411030100420b11500421000350181340c00780c0c035401c075030b4036281c0340012180c0c40d4980c0b4414000c1e41400100300215401003a80303a844041070802207050902c2594100282c078010782d000f00300b052070008060074040c00083c80b0320030078404d440c01c1009031184501034030030340011038540e0310581c0080c40d0388011843e040310b042c1900520340c00108645071250703038484c1040003443c24001625500c0c3c0300981680b500c160500d8000226080800c041404207841c280c03240718403900034000d4440000070404c154881c1d80142100714900c000b040d16812040f01c0e195011005480568014007000c050441c0c0d86031642640303019160a4445e140304035130701c50064070021401403440d5410300406110a1480d030542d200b0b0760f009840701d0061951 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 717655899 1250 717654649 717654653
    0x180f1b10030c020a0201080406020f040e06040f06080601060c0f150509070b040b370203120601030501060512150402030c0a1b020a0e090c2e0e090a0e01110c030304 72
    0x32444002940d800c141c10030000c0540241c000c82c41c1003d058082c81d000d4455039540c00c0110103885070189408007584006000904602c1c048000390064000725030920201c50b0040c210302c240e0b42103002701116038001313000400109000e0841d04286600c40c2031000c003108010f17203e0064032540c95034685003003500e800420007403000c244602c03c080c2030381080d014141424001c00b07400302d000320b41820a00480c021508485114035000e440019010820744d1004454045002500c0781c0203003410b151040c403a1000300391198040d0144505032111a86d5007400c005840c40e07284a15034020b001c60311304a099500c210f01c640c03a00d0000710f108845030141d051350b800403140000c0910049076141c4103000d807039515000040e13846680c0c00048902507002c596440c1c940f01da011b414406c25080c142e0303014070800300500b0b00d5a100c101d10200e452001c10f00801c1c8a050540c2528044401901c0590204041001812039482903200405482c40c10f00000741c003903018841e00840d503201c0c0000311013035031005c010001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 717657149 1250 717655899 717655909
    0x12050703091a091e070b0a02030403031704030e012006041101170f01050607240b1008040f02370801180c12170304061505030109020306180f1b 63
    0x40d09800c450900070441c5043c00e0159141da160b00c00724444d0800c0c04000640070034041041d440a4000d201c5c0c15541c0b4489608040d41d03a920911044002c144074440036200c11f4a4081b03c070b84207036010384842c1002c03c00c82d401103811042020040c0550181c0e000e8400c908001000040d102e00d104850b4450350180060001d40f024005884044012054104224015001705c85050458605035441500c0341c05a01d0000c1d41098280d00f400d503075010105101c80038941d50341140010040544050000b88000365040700c141d0003c440107803060311030040020041c145014529113240002084070620384111b00780100c4103050310084d100601d80e20b00c040c0007802080c41420f040c00071061244d224081070741d0310483c2084803840f60107141c5002420000c140801c41e00c0316a151061401c64580d0780c50540350000003051000149590344c075415402140030300b014030800c00c50b160002c0c010400c6603103851045000580c600a0004507010b64502c2885c44002004001250b40755050780c1d0f00540c00d2081400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 717658399 1250 717657149 717657173
    0x1060e04020c0a0b2d0a0b0108060d02011107090c02150f1012080405090a1b0306050d020609030a05030c100509070501050304063b2a0607031205070309 67
    0x30300c92441000302640200000902c030f4a00340e4055400300c0d9036a15040700328401041c00e00190810000300310b403c07004000343c619142c8182c1e51907000f080480500401141d040c1030071954a50483d44000406000d580a00016010031000c001240c41c499218200d410980d0807000c420350140e07003c1480600701403601d10340603501003280d40d5059994039000c52030b2007010143d031240c0d8440e10403901c00c150621081c501102c0180c00060883c42c1c4a040c244004030080403a08100c030710798103079024500f42c0c49100c1d00604049900041040100c0c2074a03408001a035406100c01c4e03a4140328003241c00c00010424030141140a075042d0240c6521300f920b5620300143e0740c006245241d6034100390000e02040e038005c000c2d2500320380c0015000805801840c821f000d400e46400940e125550541c00d103d07201c06031030711181c020010707004c00d440c0c0104140c104042e0b81400d011382200d213080030501c082c8003410141c0103888824024a810700c440340d520382d09441100e00903501000020340321828101407218a6500f8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 717659649 1250 717658399 717658427
    0x40e090d08010b0c0114130203061807060e010c061d070b030408071e0b0a050106020f070f060e13050a020a0906020c010903021c1403090f060f0316030e0f060106 71
    0x28141800e140c410090a100050043c0f282034507012810000c00c240035840b8000d5038065581501485c1000202082281254030080388a8460800020420b031901da60104d0212901001018008d007010000d0711583e82807008941003281c4500c058022039964040e00d102c014034403000080600712a00600e040116a400010740c1600c104184000110350fa811074192030b400c255801c0074032410200c0000e001e0407030240a0f0201070380c5d100380f25070f030051603226074100d17400d940890f10000c00813000a611a14a4404d80c0c403040c900d00b40400045000700408200303000005c2c20b0301072500f82c5800d070100320780c03081c0e5442901c164040f070190780d01d6400c0b00424020308203600041c00c00119180000345482c6142c00001d0040004d10404010401c203070080045860707000030802d02c1d40d006a060269a03801004800c0c1c400c1ca0f07038418006007800e080f0219501c2000b035107001d80c51591000e2858584426400206082542e03807200840e15103c1484543c41d000c5000f00030300980d51400b40c0060144000c0302070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 717660899 1250 717659649 717659653
    0x2715060109120309050d0c031a06030607020d020a060e0705060703090e0c042909040c0e150a08040605091912081819110d0b1803030712090c0308040902040e09 70
    0xba00c2c000c00e8220415604036601144c2880d0b0f0f1071303501c0ca0f08140d104c40750340c0001e000c016844e45005101616455070340c4212000d400b01c3d69180e45880049030b03501451900032000d40c225440410204005400081c00d46c50003d00715012503985002080c00e9a0141c3ea090740000c018001c00d02810003002c00e619000406107455908041c14444000d0310700d0101058880488006038500000c04c2100054511012009204024540281c40090100c06003200554030510840c644a003004001000366081004503603205403540e680c6a0b45c0d07400501c0017401c030300d29511900f200081c0304481c05026090f1301c1d100301c880c10220261500040d00800d07020b0315000604d001800c08510340a0000f907070f60007080888420081502d05420403d540081d0308521640204c42d10407408140003420481c28081c41590000c0044007540c4000c2640700d02040c2e4a010000c0d05a0f1030510001d445600840010741c000d80d000d4103039a559a645103006d50281d0300c1161040d8004c0313001c0000e039104094185e44222030b100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 717662149 1250 717660899 717660929
    0xe0f01060f021216030212160b0c0c15040303140c070b10050112150e010e16020118170d0504120e010915080c0403170403150c02062715060109 63
    0x1480503050091000c1d52800036035141c04107083c5413080103c2c0c4031f01401507401c17030703170300c021010001802d600401c1d01a5030844544012072480c0c10014101c549401d40c0380d000d4501c41e600c86840764032140b4064010780415455128000c0040101d84580b030080300316111040e42e5092502d4501c4103040001c1412107010300d83c05040289903004210820302125940d0000313051501c440309080c00d00b0740c54214034240203070080042100c0c0c40082c2c034240900001c1600380d0228001d6402203081e2042c2280412440c12041010b00001d8068540c08038520501c00015050080003481c80342102c41c202c13000c0e80c00003010f00c0108842d50b044021400461000e103800400ca601741202c2469914100d0800020030a8440020742800e40c4c1704261009903510223090344141881d85920384490304640401d80303045107880310101050541d44a002d281c2c045030b0700502900c0c0d95121126801840c01c031800300d1a000515000d400c4428140f0040061004101c840e00d8079040641c00186800d0352a000540c02e024000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 717663399 1250 717662149 717662173
    0x90f0103140c0c011e0b091f0e0c0c150708060a0f0317040f080c0f0109050904260408060f0702070602070e0405120309010b121f0f02040e0f01060f02 66
    0x304501c0d50206011801076600e480701039110740182402d035200f01c520a102c2038200c0100030706801440f11170104982d01b80c000d0b1a41d0fa01d0104006e0752465042c5040c02c44030017040132440d00c0c014542d0141840000034102281000074a040c40c0d07540c5240c0c80b04409040801c0342a5030012103440c0c00c1501982c8a40f5a02e04242c800341902d052070201802c003030804000c0300080c10381101103c2c0545500144080182e503a40c0c2255a50702c0f03d2140c462240c0c160400002e415480781c04d410040f180024440d1000f80c40311303100c408407141544140050550001152450a103918000b40014020100140308503c3d0581d03410100910280c0340d00b0440d000000108103803503001645109440c1003a1090030f0503191858100c0c580094061402103501000c4204407000c241948812800101561284046a03a03000c800c2d44850340301142e5280c20f003c40e0201d40355801c1950280303400740340526005141a488031000c641d61407084805c0d2040780740000040c8102c5500800340a0001a00e0004003000e44000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 717664649 1250 717663399 717663431
    0x3040807061116140c0604032423060d0803011205070801230c0c0a03030e06060f0102060c0a17010305030306150702011704080706151505070503030720070b090f0103 73
    0x2480c0900415001c43c10110300b0340782030000c125041700080440fa038955891402110030000e40b22401e0391a4600522940c12000c03900840807500385529428211a24240180d0702e001c0000c0c2c02283c100e40c2c00681440003404910085010304030440490b4024030203843c2c0345280034032542114140380d05080ca00c42c118032010950042142c2090290a2150f07a8401100e0160282030a111006d100d100301d14814150580d00480201c1445016a82260f54280070f00050800d411001c500692201c000134040c6200030024085265a03490702c50580c600c49100c0c2c03034194500303070020340f215007000041c8011440c28200f5003250209651003a800d1039411b80001e071100c00c007a41c806685007400c800040410041900700c44d0081c0d0711290401c07207503100d00300c4140038444502606906481410104000f9402042a540c0e030382e5100004624513640c4403401c6501d800e03441030441c0400d40e0340e29034031034898040c84040301508545140301e8036002c2000c01c05c004098000d0044d0b050601c0c10400000510031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 717665899 1250 717664649 717664687
    0x61704142a04061e0e0c0705010203070914120706051b01021803060f19090206071515050303070b220b131505070804030305040302071a03100b04121b0902030408070611 74
    0x1e4245400d21940d150122041ba520501000801a501c00010003500d80d07004000303a41030341c12044801d0170040480d001c0c08454008070b110710b0341c0d59004580402000c3d2156005056005840d001203034003086400041c0c0c00c1e40c00507141e00c194000c600044c680c29080820900781d0050b4070307002c112050704180d0b18110340a258039050300c0080d5241e003042015911070100700c07060300f44d010441c11045442c0c902944002c09031012201d490032280c0d540000c90f854004280c0b541c041d080450f07031342d0035160002c118030700c0d21201e8909511001c2009904012408100d9654800c1040780c0251844010520f01010b03203113000c0303801440c000d10300300a0102c0301d1f52118490b644142d0608000400d5184ea0405070320381a00356101c0780b40b800c0c80d4000804003504403000b031406041504942c00500d502e6155040450060b809800500c800f285003000c0825401004441040d4040c2c00940301181c60300080400d076803040328140c6003c130b0001000b00400c10309105800c207445c0480030301c40c20031300303081e103034520301e2a03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 717667149 1250 717665899 717665909
    0xf0513031d030c150304021003020901090e06130e030a08010f0608190f05010b07031803030c02100c05070635070c05150109050907061704142a04061e 66
    0x407801c440c40710315850420a01802803c02002c40c0303581c00030080c0d500c1544c2e004a504900030340c10f40d03100c00c0429000740259102a5416112050308505000300f11303c4444000305440e0740010003d501d02d020024510034581d8040b0804040e41ea038824075a03024142c02c0040e0300c240c1c003100641c101048065846912240c0005069081f4141c00c2040c03005000504490500094147d00d0800005039004800e402000814801d88858070f251000300f0f40070718880310320702c0042c010907401c052290041c50301141c03103d04800c40d41020600000c498942c00d19010058000340c0205408a03024038600d842d200d5101c0c400ca041c0084d144220b08120240003000c4d501a001000340004481d2850030030900388103c4113400f60700d5150b21255a50b960050703003d40320584034802c082c080c40c0c002081291185040340180d08101026840d40d86455450b80680c03689007013003035403d024040e4401b85002008000d0b5148081202d0701500b84000101080211000c980c400f0031002c2440d880000114014998001103072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 717668399 1250 717667149 717667187
    0x3041a03061302160c0f06170f01060e060f04060e0a120507050f1309080406171b0307050c06070c031e020604060e0a1502041e060e0f0406050d03030f051303 69
    0x2445a005241c2a04c2000754020107260440d10042904c004408990342101d030f156407402c03010348001800e074a008405440c6c18404400c1d00005004a40c040e2074030042c01700380500000d2412203810b0b900141c40c1c0086d0000c02c0081c19030028120249084c2190a0180100c12204540389a003583d81c01e680b8111442007a0160510442501a80d501c040a401d90b0100d80c40c803c0c40820351a00d401c04640d881406120085281c3c000003840c90082d0202c1240f14800300580c140c2801c0f0740b0b440c2400d0540001308650100101003007082942c990030b214260042d2041d03100c001c0d603000d085c94040c154440c02c00a08182104d00003001c07043c194001040340c2c000307070880300010f50899407076109402c00c102150040d01203a4440c0c1c840c0c1c00700f010340d07005004481c0a03449000185540c000029400103030740c4074003c00514444003030201072803d10907403500080d00030b1002505a50b6800400d5021900843c164040781c0e5500740020b00100358020301e603020f0075008004001200c26540034200c40140d0096483c1a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 717669649 1250 717668399 717668407
    0x90203070e012a0605060301050a14010b1c0207300f0503040f0501020307081e0106052b11090103140903040b0a230406030b031b15160503041a03061302 67
    0x700d004111141d402c2501e043d01e0f0f208072441400d140300a498180e40a134000d40c60000000c042c8459071182d084085240301c5000504d1b4070700454440c103a0041d018156185c0c81524071480e15003050310040c99414032441d00c000a820728030b03155284100d099906000110019480800b0055101d400a48112000d0401c2a10b0b0b84580c2400030200c816043c00610702d40c400400d01c6043c5070802d0400e48110306220140a0504802c0d80c9590021000e2041401148040c010b0340900c00c5441a48201c1c42910810340c191036200340140c4042c1c54207903045011031540003a008009507031600a080c3d40b200701070040402400c280c0b000c540e680c07255200c1d100c47d901d004618440160310864020280b20702071018140c0c80090b07c2c200d402e03603901604c50302c2d020902c0c0c441c412130507060100f101100350320015160b0540c0c4692400388020094074080c102101c410810200e40b414004406030172009000344011038413103080402107102d00d046e40180c0000300405000300720180d60b07035004140c03100405240160301c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 717670899 1250 717669649 717669677
    0x70e1905060d1806091e0305030f190c09050f1f0c0c0e010803032403061b2a0d020601030f03030209010e0d0f060501061d060a05040308030903090901090203070e01 72
    0x240340040d02c0010b40d6141c1c45a6109101c120307000340c401c2038006d02d13080150301c2040150440880c2c1200008000ca1014000220010b04986030654403141024040199240141d0314408441000c1c50381c9022800e0790783d0502603403d1224a094650700103460078040022207800b0b8404000c00c0000040420803070007220300070000c0c0000304030001c06610301c10822a5031079a00c3c1640b650022140050140d106001c0760041c52802c0d8404006820040c01a20a50b222001c4041c6d04640780b0900c01181d5a08000c600b15054040040000d01c0480100c0031015010031103225080c00007140c090f00865200703c0050020038002211a00300581c5802d0059403a88040c0c016915540000c954580c001c800058800c2030191014032844c0f4244107107003c0045030307268102a24142c2e10780001d03c503480fa20548013101402d05000804040d03400781000c50400703903290344000741d42d4012a443e003010b40002c11542060f00b000440305016000180c020750551038030400080c07030703810700d041054100001310b0800c400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 717672149 1250 717670899 717670901
    0xa0f09080309030304140d05030f0405090c190f050c16290a051608041508070f020d030f06050a0b04030314070818040608010e1b0d02010906080903090301090605070e1905060d 77
    0x7e901c0c0c1e80031040e203454141d012610359030380d0050300c105030098240200245c0c02c009001c0845441c1c020b0700402604981d2a02400c44043c40314542003401d12504010040c28450100440c0e01100d104840c80c050403418240480c07030a540480205220051b400640c4001c000c03288203a400654881c5000e603100c0d00c40080c4018400685c88000d48200d100041c0801c0160510141a00c505080d4a80c44065100d8102c1240c40c2d0031a2541d583c0142c006907e101c4000348642c1020301c44100300c00e808110310b03840d6400210003031407d80c041c161032240000c08104140d009410b0050000920b640381d41000e1b540d03203c40d40c1d288610428000d102208503442e09a5545903400103001d86884002005000180c00d40c43c0e030344a0100600300c40b00a9602d61000061603e600220901c0340c0c1030b51307141d00c09403400500b82e5507524060403544150105020200c1161424071824003020300995020074030742440c017000340500b204501a00d000e14164648504a03005d100b0100c0111a001c0c0c400319174804030740300e80c03030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 717673399 1250 717672149 717672169
    0x1140706060e07110f071502010f1802031204120f03230d14060f060703021903080f060607170903010f060902030105010305090d0f180504020a0f0908030903030414 72
    0x10002031605a010621101d18480d0500c2030801341c0781c4c1101004510b00060703a03404a6224100280d00441007440020881405c8075014201400085156103d0b0500c8606507410043d155400e00c06002040c0158a030410690101107115201c080c0b0f40303824104452703107d860564002c0d0140018600810415115550b0006505d22004000341c0001020b01541041e43c00410500482d908007050b80c43e2484100e480f0f01d00545005000602c1c101c580000d200c0d0540080909800790b000d403013102c03050600c0134119101c405100782c1c2c0d0503c0524107614110451880035001e540100c1e82404204001440141a41f01c04400c070311000d0746401e85d20000034007400520448110b45402c0c03250020750008c0e01d03005035058440988090020f40e03280d8480c0f594812003003c8081c005180c00c014411020301600095800045410010303619680760ba0100302a030f44503400a000040b01c03030241012071940301140001400714000a0344c81c1c0903041001a960340207500500101035084925000190303a88403881c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 717674649 1250 717673399 717673403
    0x10f1d0d17030703050105011103040b040504051b1206030114090a031107052e0804020d08090d0209040b1005060c030403110303190c050709060f03111216081009030e011407 76
    0x701d40d4901d01194000c019100a100349404140180503d0082c907a004c001e55003138900c00101d0f1402c2c64030349801c02000d044040c2c0403c0000d21541000c41240207014000c290081100021102904000d42032608542a01150003a101c030410184854410041443c4441b10f805143c241049003541003418100004d07a4007541d400075440c3d81e0700c3da44082c04203040610311250141c0b5036242044c800305940110081720300a52040c4154081400244004007030701090380083d12451821507160301080d8900010f8900782e4030550203004004e00c00500b0481000940026510141403d03051400c4503624000c80c08010000200d8414500c0780340c8040041c0c03100300f29201811848003030b0207200034088959511058902d4094001e000c1041503403801985e04031440149282e002c0703461520741c8108104041d00407a8809000d404452504c0f00401000c0c4ca0701003581a50781040380350480796842c0c458150043d81c401d6007408900c801080d08030140303079000c0d502802c101015550700e0800d40741c035214003400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 717675899 1250 717674649 717674693
    0x203150106180b03060d170d020706020318121801111207030906020c01170a1508010b032107020409080705010f0b0a09090210030f15080309010f1d0d 66
    0x1e0440d40c005240941860301c050342500b40c94a860071104144800c8a505810021410500c00050074180f801200c00c001c881a003800e210032030603a031042e42d1102c40241ea00755000703c00d1141c600804410000f60310300c042c000381400500c004080c0740601076208101d40c0c048940e07040c030220364000c10f6210760150850781902d85071810f051146025810030281540000c12111011580d2800055241c09043d4140c640303c00301203a0b81c16071805914020070306007226032124010040e0280f188804c0000d000e074031001160241840c41818908000380b000914440700c2c0807124038489103070404481805405403000300322030300b003418400f000788181c20005000d50329107080c02014060560054030424402c41c0c2030013455940301000003c0d81d840d0340c400b07907108004483d042c541c0d9000b030b40045240000d91001080000c0031407200c2d41c0016603548a400b481d080012100c80b55079100d80c849070712601e02c0c200458030710860102d10b440c07160614461030050584460200602160500710000d000c0e020358 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 717677149 1250 717675899 717675901
    0x30501020c03030a1b08010e1b0a020705130204030b0f0603070b03090a031b081c0b060705061005040603171608071a0601020327060f040815060411030103020d020315 73
    0x401c0d541d941c0308407138114003189820340c050034042d4450b0078035003000381a40e0380c800164240006079003005c002514181c02010411030070b6072184412000341c40c40540a8015084283c07a02e018407400c800c0b0446114401441080248005041800b070a604102005144a03869136100b0100c0c0c070b001c02d035410080c89014040204458a040001c14040d0548a9581d90200c0340b4105001007080c0701d034107130042000c00d0a00080c40c2c0312404881481c20a105400b01040005014010903000c0c2e001c043d040e2410340115082140e280c01c13124991000342002e81c0c0401203a851521110096246486021311040300022580d02905d503050503043c504c0d8006810550303911040c50b00803040d4045480840e8051001c0000900ca5030010065078001d02080e041c0c006003200541204000d110058480c80c0c2c480f000f40800000440424060030241c40740300000c040740807403240c503640c4005000341421305c200c0c00d010320303d1103c440a02c282ea0440341c1c16268115130202500c0000d0810960006101005107404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 717678399 1250 717677149 717677167
    0x180910080c0901030215070203160602011a0a150804030522030302010c020a0b011401020a151d0705010c1e060504050d0e030a020a030227010e010f0e160509040603050102 75
    0x540129101001140c150307405050900c1003101c8240b00195004854403000c5c0022110302d0020020644010182e0340500d4000b220450305e02c0544e04020f0040c1c0d5280200c0320400291200c140d180ca9045558600c0249014007408501c1ea0070860070b41040000004502014003803025500c0d640100d41021000000c0c3c41d0320720400d10302d24032040d0019030800c6828842240041000f00d000c54210040080c268209424840b001100c1038070709045104000d56000800e025014036800304c9101c11000c01c1000c0065100440c8680c92240c0080f6900030080070800c903a00076484000050340140e940300c04600040400048da0f04504d0090107c0341802c0c1040108040420300e03840b511000e1b140c08040c218648181a51291300c24002074120480b698240701518122007454035400c2c011040310000700031840521011700007a4040301906603250014490081c1c83c00c0b014001e052030042e01c103010b251201134400d00001c0b100444092200010f43c40c3c8030b580f6940c01610195400800a6640703600c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 717679649 1250 717678399 717678421
    0x3051b041107061d01050405101103040b04080a0507021f0915090e0a022104120c0b010b070203031c0603030f11060714090d0c03060608010207050a170d090b0402150301080709021809 80
    0x1018149c000030349011a107642101545060b24040c40d009000c140c80740d80d42d580c1d040d100c0d03480f41c0401c1c03080c06800d1001c000140e0701d543c08118407015540c0c103070700012041c3e01c02402d000b001d030300040c1042c04c1d0b02e10380e08035113035000c29a40112214500c1585181e19540141e800a200340401d13410080da40c1d043d50200107480780c0f2200d02a034440c0700d01d030803505100141202e80c112052001490384038090300410001038950040e000103400103090c0d84c5400403000700c0e0a0030820108481e8201501d400c410014142c100580c0c040c440420308000e00903216410446481c2c40303000b0521400d00c8004203005160b00183c206944071501c001d4007103c0c00e298a030502118440aa2100710366082c28250045a40d800c18001c1c0c640e25030703014005000c6002e16541d1400340310030f00c031040e0103460800c0c4510000c01001d8059050220301480c02c510160401d401844103c80c0b00464485500904000400410704005a048215a80000d00586440051080e0300703030b0b03c0d50350030003e6100c5041800e00c5103c2c0c3d45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 717680899 1250 717679649 717679663
    0x81e090312070e03030403080c01060e1e0114010e120705030706050d2f1e1215121b0a090204060f0210111c0209030703051b041107061d01050405 64
    0x62219080442c1e52500c40454030a484a44620b425810502c002c10000e4005c902030000740c4500c034008600c05071101020340282c0c50813100080c209241d41c200d0314080031031622890141096207192507031200c6900018106c403840503c0030340903002481206030040ea060003094080d1400a082c1c480d00f0313664031002007440d00a8000c00802618081450180541145e500341ea03007030000a0540055541c203066001304e0300403e00c407121030100c004816030f556401c81c00070519024060008082410038107420511000c9156140b07000b220144d03040d408615000401e030106080b14140100d4540d4808003044c00009140e0200c02d0490012901003541034000742c9132556201d45500f1124130021138554403060760078484888907403040070004082e0580000c5140c9504d1942d198001d403800b408980400c1c9045110380c001e0740d840d0014a152110251030040203840c60800321020320003a0104a00b01e4003034400d03e94000c0c1401d540707405078042e0020b52101421200c503079000030030044c03900f4140140c40b148 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 717682149 1250 717680899 717680917
    0x6140403020904020301330807051e031006090f0506120a081602040501170640080a030b040b1801091d0a080a03150b0702041e060b18010915081e0903 66
    0x11f00a8000c501c18200141030030890f540204070905010f072032008106103d580c0050030f038040c0034042c282e5540c00d6043c0150801083c00c00700c00240107501821002c11900040c104501c104094058540c042000288440030580c0000450f44c0e21550403529050b0758180000094216040500002c3c000001c0702460300c030000f40000307840d007075030360000554402441504d080800d001003c03800f10076402e190072111000c3c00381017a116034034074094540003415081404100b00003a20786490404a0600380648240d1803429251001885460101c036141d0483c14014180220b9954a01006c0e13000308000040c042030140c010740d0400780040c240302c0c2c4076034001c860100120b8208140641d860f00303820031000803500380031040c3e4100500c50b4200806031105618259900321010124040d00545126031130007804c540540c141e0f1185101021203071441e1640409051050030740c420440c0500000005402860600c3c0140d2584c0c0e448480207210500305d00d800348a004414100006110008000e0000d90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 717683399 1250 717682149 717682241
    0xf010311041a041a12180c0409051b0103022506090206030f01150207060e0d020a030501050a06030218060d14190602090130090503091201140106140403020904020301 73
    0x200f40040e40c20301d10310541d00c4000146036032600103644201c41d514900c240080c008161511f204680000905440341c50703c00b0360b40354000381c140d092440120342800702c54240c282400d5050840355402e20042c5455001c12001039000581c0460410010340e01c04584250300a00407034032070600ca944496912424040d0000301c039030b0611803058080c0002220022110591f440b0110703c0d4085080c070412083c1002c080780c018503040404400140700303010740b030b10a000e0300308000b80f042d1441c01000f001750a90340e04854200c0d050340500c10180c842d03400c0a078000d504089080303880b10254500768507140680000021103079500d0b0140c1d040050940003855180401d9231201400070188518500c4c101c080b540000c010f400c601050880000b180d0041d404040c080c10030741c4c2c2442d0801006c00c181a03001c180da240c1695580300380b50219500c10342114003400d81c40c1b40c45d42081510b62003401052089001c0a1310404030240001c00b15074094110b1041807500001528074448080b000c00000107150020403000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 717684649 1250 717683399 717683429
    0x1110020a0c03201b0102100606080601021608100504020d06021c05161d03070317040603060e0108070302010c020f06070312110f0d0207110d030c03020d0306050f010311041a04 77
    0x1510f40302254061541c28200981085049041441300116040710a6410b600500c410000da40e0344510a04c0300900c0d031a250302609281860009007064020100303c12018000300782808a118001012645444215800509038446000042865002000c01403800e400015461441a1184802c4456801ca1a1309000079201c1c0740b503120708240b103001408002664400c5a014030600100c154042c2100581600c500036240e840c0d580d4010f8504040d03080100c0300047c10096958140309800c0144840c01c031a4685504094030203403500c1e02c0c1e1001030b0420404124001c29550b850b84c005140c080c00520036981c40071149000f0f00034403019043d280320a0b1400d88c0420001c075440d0110b4042007034401d6a02c1ca402d55020050f4001d400001d02501d0b030031070900d00202c150b110014400e00c0709000f510b984c4540300441c50020716100008610408144c00c18901304101c0c2c035400381c40b10b400740b03003401c001c140d24441000158030303409141e1007032240c00c5020200340e245990000c0248160758180301d510b045 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 717685899 1250 717684649 717684677
    0x9050105010507120e0604051314090f1e1c02060601030b0f0109050d050a021512011a040902070311160501110d0c02091e0406020c010506010c0203030a1110020a0c03 73
    0x14501500c3d0024000d4400307003524120480c8180080c90711700400070003c0c0d04054581003c9510400da2104140c08555166081d0744100c0301035810991111510f4010807012868002882d02c0340c82a50038681010020641442c03035010500400080303018a004004250341c1a14009680750340c1640c00502180c600840303070005051a00b00c07031001d00e4040c0c5440c1025441c01d030920002440e400803c2e68140140c2101d13500680c0c0e00d20b2540940402908002d0b01e500e40000340d8441d1103c184e0040c610600400b4140042d14500400e45049a822003401038403110b0908064544c00304c0512148558080d128107040c004c00f100754640c0550300d00780d8410700002e604090b800e13a10900941003001141d1040d1859005292a0243c00d0740005505030000007180a100c0001d1103007810b40c0d084421980105010200c50380922035658030546c2480c0120740482c580c0c01098491044c1d843c11401c014518080e0100344c901000f6a44462405001c1150f44841041c00100031064025080340022502c2d000008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 717687149 1250 717685899 717685907
    0xa0e0109062f0301150203070b010b1c0209010c080c1e1606050408060a0b0316060c12210f06030b040c1d1005010309060b0415060e1008040b100b040306060905010501 73
    0x180d6044040e50742da241d85d0030144862481c0f005e03202110218801000004002510090010700a0803c6150280c03030b01d40541c41140031101d501075100c02184184031210b10390381d02c003101c4050150020714441e43d038541001050b04000b0340c2d40c10760400e00002c4d01c40140c4c403600040d802d00081c00c0c01d2212503260b602c42000300d40703d00c00c0d8811f109041d404007010540c40104e81c2d11100300d098000341140c3e45801541803d00b0070350030300d92006010078000b45812040c0500d004410404406914104038403400e007000e648048005038111b020002d503119450b8007581c2d80c03984000d016541081c80200c8915003840c003810107403041d00901001d441d8074145054030f02c0e440c880e00c60065960310300b8003100b1428140110010003402400361030301d982303658408119481c2d501c104040e41419402c9520441c2c20800007410304040900042d005a4425400a801a40c000000b81e0020b40c000038074081515900d441d40707a41461038008a501c403000040000401406600c11011920001014003da80c0c0c1e482c0191 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 717688399 1250 717687149 717687221
    0x30d0c1a0903130b070c06360b0f0c070519090903090b030c07110108070c0605040606090c020706030608070f0e06010309151406150906030a0e010906 66
    0xe00c003080030901840492880580103600811880450342055040c84411100b5450369100440078900018400c0c240074601c81780790003806482c104484d41c00000f14200e0b05503080c8182000908640c1c12508509182808a0000820b00312042617100e92008070300701259030000308000014030440c8000503060810300e5061450303842c3c1134134040c3e00030700e4400048054a11072070128204401180c4c0424501e85c0d000285000c0ca07116890f01d40c4682081c500795030410742d408003003410320180404100e0003e60040982740c02c541e1240010450380c496261880c007802143d048090180d0400209211199000889404403440342c1d5062088580d1390103456102d454a008403100e1481c1840d06001d01c80c45500c030740f500000c040c900058561119220180074500d025030030764019417140140890100000d0210713800c000101c48030303c0c10106080f510300c0030f44a10304607680500000b00010340b401002d0351004400c40e103071074000d000e03180844c94010010064a0709058842c14502811001001c07140405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 717689649 1250 717688399 717688403
    0x70e04050a1a1f05030a0b090f0105040e0c0907030e07261504020f0d02010e100801092a0305270a02090a0b0906010810030c030b090c12070504052e05030d0c 69
    0x210002c2c469101d811615640010241e540c1340c1d8030f40e80060030075122202030323a02c2000350101006803941001e08010a44000e140001003d9005064000950340c0e1070b030500e50025440c4c18001600c420008006c0e042c1038241e4044c0e04890460303844441290000004550070384402c40c01e84000c404c15034142c04201d403041e0741c042d421501c013040c4190305007003191071007103018014100009019100710001d1405240d5801c0c0d03000042410004009550880c002d0100300310f840340050b25001685810381d650018000340b0101010780320408503d94007480070000f40c5080b980038107842c1d1246800140340c2d4410090b07004a015004c0d40001540c803800c43d20030442e207110b006000c00e10325160400111713401c1c00c0c06040400c09401d0800000001100302212500452080000d407030f0503e8a00c10103810400d0000e90356028498240041403100804528802a0384e4211000111a115600040140307803c604101881032070003030400758061210310b200d50071258201c0480d03130100c410040031103203c4c1c130754100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 717690899 1250 717689649 717689689
    0x2060403090b090604090219020f0d0e09071107030302070303081e04022b050105010314070b0712050d020d0e06070914040504020f0d121206030c0e070e04050a1a 71
    0x80c0b044071482c00060401e803500030310b49410151a80365050480c0d0010290110700039045411800e41a01441310520103070302000500300c7c01952034000b5120100c1340340403034418a00440003d50450042400c4418040504c04486540e070300c92501039602c0c0a103010035404aa0642d0004104565034070410151150000700740e11182c9550742401484403d50134590106a48001c95005a290040011940e18003810010502d07502d10f05110080c1000609480c80680004c001030100c1070354141215521179104c5a03034100c0703113001f010468641c06805c007140c0900b4000103000303540360195000112070140384026140c0301d84a80c0340541da41d10300c1c1d101d018481c850800c0707103180605c3c06511081c0d00030300240000214600b483d00182d92030302c1e28141160f23400910b006480580da132090840a480805403010411941943c4507004d02c01d20521503003e0151441d0000781d83c031131003031282e490404030192080c03219048c14580b1101402400041e02c4600c240080240c0d424906141514000092121 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 717692149 1250 717690899 717690917
    0x80c130303050a0c0203101a04060e06011d1003050103060b0301091709360906060a0512100e0304080c0d020906010302130e04050606100f1e09091103070f02060403 72
    0x6001d9800303803c031a0302030702805105103200015840901000c25a54a1114001143c542e000c1d50b980e260071549030458007561526a06201c0703403001402145c0c00040c2400c160b14100d500752404103108840307041e0b544e040a0b10310b0711000f0581d0941c01a034142c901c1350344280000b01d81c1c00141070890b07501000141c00c4030a80300a130300360141c4440003803581d0302000d011071210744420600c0348003d181070529107140c00130100341e0744c404109814210360030002910143c11ba07402c0040c0003c4000c134003401898032940144616441c020420444c07031600c50040071050200d624642c2c01580c60341c10612441c1201d000c0c80c0c0160815143c0b4201c1114102d500900f0140d540e2500300c0110001e4010400140e49880d02d6403020801080703042d901da110ba4455401000d1905c0e107142031040399561302403208284240c4d080720302c0500d60050380781030700c0010556040c04030140882045071801130942c0300d41141b074940022825070b207004c9c4008510403144d5881d009101c80710140200da5560040350301a0000b15904 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 717693399 1250 717692149 717692153
    0x306060f01110f010504050a1118160507020d150c0f0c140f031305030709050c0a0c2306090c0d031e0309080a181e03030509131b080c1303 61
    0x2942d40b004900300c039000c841d4020200300116084500c00d88007580d40354000e00a8608000032003145042c40d00040e201224103071444010f400d0001c9019000c60044c2804c0d00c00c13804c0e902c1c840c030705545225800420307140a0f500c0c2828144a00b101541d4050041742c1400d0060f00042e0249000d0340085180c0d965864042005807103030b0382818020b03603400b2000d02030417441104040042000c0c120190300d40350340854941c5000708045c98a03495a0220042d5400d103420048070201e0030080c1c3d4090340c0103050a200315940340c946132444070a0319040c0c040855201c56600403201c40010b0743e500c80c0040c0e404490f00b22220750300300300b240d84000b0303c0240060300f202c4880c5000c1600141d0011110080e007404100040e0607500c000c00741d00311071020800102d1010f00c00400c0d640078132620006103000d00d101d2003400701105054102380958000030741441000681f51840d511140030705440013181c050100f018030201c080409069034807614260008500401081c0142480d804440800c44c4180104000034515 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 717694649 1250 717693399 717693407
    0x10203060d030c0f08040b1206010305150603070c1e03020f030c0c011407060c0e01030b0a030312020703050708030a020a0f030507080114120105190c0923030708030a0c02010e0306060f01 82
    0xc010104c0307059448110301c030700059000000d40040e1050081140d115010103000d41e09220006001c2410981030005000c009512108002c00d100803c1d292140c1e41e40c0d07400c00c1500d005041c141c0040c414100001903c0e042140140011500c0e8420b030301b038407000704500e81801d580c0c0c0240a0a9000c5400802c0201160344c001c1d00d40c44410700036141454180131603034903403070116500b0352907400100350003408440c955a41441154410b000c2201c1c25491203017503072001030030251a04003084009600250f90800d1600600944211652000c0c8180d0340e86810485100690000000e401c0441d11000072401254045c1c02682e1007204940d8503401585e1138440c02d03804010840a034550060110810007030102400c3c001d42d131040c0101030f40170b80c4c0342c469542242c0854089142c010100002c0c00802e2001c0c944c8103a49010b000100b9074a0000c0400000000e82845580da020f40301612000a00c0d00c50301d0380242e071801c1194000d0300c2d0064140705120a0685505045031034650014458200d050307a9070107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 717695899 1250 717694649 717694667
    0x708030c0a121a040e030705060a0203180106090204030620030a09020d08070c08060c0c1209030316050a150615032c1c1e0c020d0f031e02010203060d03 67
    0xe42c0303010100781140309078107402c84501103040120302e042c0c4244603215081c00e0007807111130300d5110011450140796441e215141c4001520080d840e6400001190246014104131031514040c00700030420795545081074002544507100481e0781030b040004480c0b804840b200421007180c500c00b0094596a030b812072100041c4403a07642280c1c02012001004013140b00c0e08042c01d086c900c11466240441c1c00c0402c05481c0410060405505020400c521b0050207004140016110b0000d0070442c2c8910748c26000034154000c0c00001e428003001c20040c14248030000407030483c10760150744054100c980d58000c2100341d91042c001c0c80c0c0c0814251101c200c06511a0f0700807d806070719011070600c01d80c1144024500c81c41c00541090042d80410603107007508603206200300711034042d410301d041031310500151034038034a205442803000e0181801c50b40d0150f4442180d00f807105c03680024108a0f8a040f480d001d49040c02c443c06d1441d151104c5104030a040303005200f10b0340110001000c2d0b622181c8650303012101280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 717697149 1250 717695899 717695917
    0x109060e04033002120a060918060902030709020a090f3002010c2003010515010915030204081002030114092e0e0f040525091a10030204060306050301020708030c 71
    0x43c022000012440d052000d00400188203140300349034101000001d003906c807aa0404540385182140039456690b90310390105100d40e02080c0400d041c50b00d4000a03041c45031503030215080d5800069a040500e134800c1c0c3c80420707a48480202e4414640780c52910988004188880340c0340f88915242c50300306006450141c0703185105261580054680e6510603e07506100c03441d45108010702401e04031a031500380105507101c00d280e118080a21244000202008042e00c0b410400c08148600466031500ca90103c401500d4070004840ca030f6001504108002e6009200b0900034108001c004403a40ca0300005543c05803040807906100014040c0c0b41c800303003e010104400415241d02c8000038140200e54500307101d04540001c85407280ba1034101a424201c0d00d01c0851175050a618052000700000031014080e5640c1410004100fa11000714200c00c181c1c09103c030f948100d0400c6030140c0194150000d0041e07407100e40c1c05000e1243d5410605080c0d0042d4030000b010507806000088000300840702801841c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 717698399 1250 717697149 717697217
    0x100c052109120d0902150c011808040e1e070f080601020d0e0f0105090a0f03140303071b060e06091e030a0c060c0306320a060c1b0f0902030109060e0403 67
    0x100045c0d00240d01500248001c07035160802080740d1004c02030a00c10300301e03261011040e05424269a80d00c1100d54404c5000720100014120041600744a6140e440184800d2101c115985070500071806803e02d000501c1c4400014881c05c0003420f1035101148640041e0b07843d84445404103d100200580c81008002c050704209091000084690b94410070000620034990300c0c0d024a400c6007801c2c0c03521308103e038072000d4070b41c800c0082c003401c55841000403006550908029a00e5085403624401610362021076089600c110300c24003140c1c6034082034a140c0a00041c0441284180d1407011035142d000e082040d40c0410740c1403650202040854010700c030355901d54900051656181c0078039030190745100d560341110345000742040e102004080e0700550300f00411556840c100789405001000c00c0b120300e030010014580c01141703e403229040843e91002e03005d614441820356440f00c40707050007500240300d03905840f418a000024081c000004c03940c0102d4040d84c640c0c20284205100003c00b04032291050480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 717699649 1250 717698399 717698411
    0x9070e060d09030801090f09020d030804060204030c08010e3c0f0613111509010e03010605090109141302010e01051b0105040f1416050f03100c052109120d 68
    0x20001071141d22000343c4642c8489259504107211281140d442c209900a482c1c034064013035016903600d005081d5056490700e0500c017595110b14081c8081d0040c0c0c4d03c0100104c0c0f000d03102007881501900300d029240e00d03c1c0c0032501901b0301195010410714100244200c098442c24070b154403815500e0240e43c60348024401c48040c5144005840d25040c0304982c0f80c0c1c00c00100101d008104039400000d4a9030040484142d405448a03540190452184034503032810700c81d9004807403045407000e400010041900601901a56a4401500010302400b02041d000f9455040024442032001703402d0700225a0180d503800c20300300c43d140041d81d90b80d01c82d04403a00182801c03450380e56050300034007885100304e00c100303200e18880303d05140c40c485414203003100c0c2a40f074001417a13540d06d80f110a5142d03407c5403c1100e40c080c01860007000b080c1403580000c011405541003111045c852508003000300b140d0420031000a540c0d0240d59450040c101c410303240344078603800c00562250154580740c00b400354480f10003000120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 717700899 1250 717699649 717699667
    0x70b06190e01231c151406010c03111b0114130909020d0c030312061d04030509060c0303010e0f180312060a0e0709090b03032d0f0d0609051509070e06 66
    0x100d0007043c0904e50407018070900c054204100010b16042007002200240720794103980040e216001c100070141410801440010f8080c113104018090b940e000000a039220b02d0000d5189000b004140f2000720302140600c0c0d00785850301c1e845403c441b07003505203000440c400f90601c400440074081207201a640304084480050116007403000010045119443e101d4003400311203002c500796209541f000d00301482c0d1460401031081e0144070700e80c0c4070f50b1524000c0d5a603c1598006403650081b41c2032003650f4400800041080c0040b904a940210300c8685d0f901c5903a40c404602042c00f503c0c815003209030350018001000d056244a50307064000200a0010704c440b501c41e5410541050100c0f940400100303540420840300c1b0280c4541d0340724910980144d85011580341041104c0040700550380030a8400c19941e964107416603040c0c403030f40a22030103141d5642c828654618040c00d460b020b5124440d182c10007207024403090b40503000d00c818026103000b4160f60b54075401d549041c0403401c030b02c0e0009010420300711 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 717702149 1250 717700899 717700909
    0x60609010e1201090203010c0c030f0c0602040f0603150905131514070806040e192409050d020f03180d051c0c030e0609010212030c0708070b06190e0123 67
    0x11050b4040001524450764010182920310501c162014840751004a40200303a200001680d030784901e04004d50142c0e290301e0200c000b4801c41d8000e2100d1001c1c0301000c1421030b403541144100103185205d111059880e1941305d011030340165159588a141d030420750f0300140c0d101081c8070a100014600107804d884285e80032462000844204001a1081d0100005480c2c507100d00c10085250100401d008a4013141600089154100180c07540c9580034111030014031500c4000100451807200340644100e52800340d0703413118801242800340c042c0071403035900c221001055401c04840b0a003600d47c201390340003d1010b0403600c400d09079640e00410040c0d4124103000a403002c1500c040f42e40e070a041c07020324100180241403880d4aa8410303a400c0199505d142c5c1d00040c031b071000d880a0240980e0380e4841c040f00c9402441010001000c1450209141080c0140004114072885069401701d0f2020b00f4859800341881b250301071803030704110180c01803100d11008032504241079040f298020711840d030a80015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 717703399 1250 717702149 717702169
    0x17070f090f1d0c0f0d0c030e0c01020d110c030109030203070b1b090609010c0614010f050904050303040b3c0f04150b040b090907030c0b0705030712140c06010e1b03060609010e 77
    0x1c1100b525546c4940400c0d41c544958a010b00c1a04041c3c8003000c41000000d4035603d45401d028100f161120f15480d8500d01070044a00b610001002088043c4041c680691030390016202900c1490342c2030000365809916051415400150031101e5203440b020a00308465034211982044c1001034040c03400002452130320401c0c1c10610501700c8210b09600d0100400800748841d0410380c050142d140520001800000c2501d0300680c0c0002c0b8120941c0c0c90304401e807215882c0e55982c4034000d01001d0702d03412000c540000351500d0640418603509640e21600c0e49607240d08280c0300200400d107440e0000f0412030296001c485154802800030425602c00d0b0300244003144252020070003078000711020000c00c240169a40000c10200d44003d003089450f840d00b1741c41340217455010301800c1040410101180c8140e210401c150101800076032901c000f40d42c001e0b520300c1c09003c0d4000c9110030801141c2850041d5200c414401000b0b006a8655a51042440203c1e00100c0f0100c2c10720249800001c815501d0380924 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 717704649 1250 717703399 717703417
    0x2a160210092d05010c030e060d09020a060807020105070801080d1206181d0a020d111f050702030f2e06050d1401060501140a0c0317070f090f1d0c0f 65
    0x1d0a02c00d00c100302100c90500b143c1d0301050600c0750031000a80002d40107943c1c803001c000304840c5240c40380c02c14002d40e00509241d080081d0701200c006004544c041e004003216000d4003080c0c3c000c001981d54810103940c2502d0070b020324001544000901600103104036800d0110550584001c2501c030341e03a00403026010100140206110348400301300c8034503801d13600028900d002950080c950900d0030b070003151406c078134424090301d45000c0303c8000d000f5031150900c0c10000038940c14080c02d2541c0c440c80c018004d4001c00030484c4603005452003042d401c000003491010340c86000540c105040031030720780d0031218654000d29020494969034001040e43c0e41d6a2115009409602c0c1516002180594242102c8143d0811414071810681140d50b07484407105440140c440c500309440d200704142000e98102c1e522040703108004207a5001c1000507503000d6100301c950034141c1c8500034203d03140d165082040f807217805403000074811842c22045071606034800c81e4004032030b86840ca207010214502c2400c00c0e4801c0040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 717705899 1250 717704649 717704699
    0x4060c091a09012c0118030b100302040b1e060c12040602060106181d0402040b0901090f06121505180708011506020d0f030f0609052a16021009 63
    0x10341c0c03102e560840076440c09603603219005048800402015260764001c0c0c2020790410039002d840381c05400ca130404d40030182d9003003449034140e898503019550400741980001c9028a007041d028040764109200d021517514000c3d401120000e07028420301050390040d00c081e65083c81400d0303a05a64104c000014009803180d54007405841d1b0508c0300240901c9140c064680603500860401c0088890401c00c00c0750302402d4075007003200f6840d42d0000a0180ca040703043c40368803040340000050f55186d82d5109003010380c004da40501c4216680c41004140c51080e040140c500321b504445241c141c01184d00c265408540a411109015003c1007410b241040c01c0d04055441d80d955410702604102015071341004140500c02091900045034000340b14100a051590515454003c0390fa050f5105070000b070041d01902d03000300958a009080a022340064800c3d0744407000d000b1003140c60004c2150304440d060350070800c41900050441e03003800300c55050b80c1200d23001c205c003003440232502070100401083c1011016807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 717707149 1250 717705899 717705907
    0xf0315010e040c06020d09030305071109090a020a0b07020904021203120a0b0901141f02030c0102120a060501050c031b160305011d1b0d110a0b03040605150904060c091a 74
    0x80c14407800f10b072a400c00d805652182501d8428140e0000c0c1020540b0b5052a0454460140d807130170311040100440540d83c000141c0c800c00421020000d03880e00400e000301c80000a803a615106c2c00820702c01c10a01a4004140c100000d025042030701e410700c0d516400f00122413500c20110303000480c0803420b4500604098413240d8107401d030300d42049190b014296107451480040e1401d00040c0c507641c0c85100740c6480482c003050258401d8024800e0312085401e85d0003d550340c205980b0040e64840c1c04484018a05103072407000724240d44160140e402071a004001146003480045400e250351860f10f03111b4901e4407491041e0b400e014562010f10009500ca00000f0039407207c01f00c402180320444c041c40307400b1503000040c8924a0040340c89100e0400405a4125013030f0384180c14814840c03000202c03003503040b4100c0000020840031030030045104034003d460403c255155854964110840a00c100e9407125040700400c021a0455000407204030310b42c00c10a1742196580500c000d0700054030300b500144c000201d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 717708399 1250 717707149 717707153
    0x70612060e0f07081305120d0608060103030f05130f0b180906031011190e03100e030301060807050c01110c010e0c0d0305160818040e010b0307050f0315010e04 70
    0x1000d44005426407542401940c5048070340c0002c8044010407540801007101c0205071154100200080e4481d000000d07104011201a0707810300542c004c903e02c1403900d241010006114402240941c1030703030351594489180c240c00810403a02074000d0314414408101090340081c0641000c09464000d12003000340c0f90300da9021070000c0c03864072442d0020a00840c800010000c0583e0040365040641500c00310006400a0700514050319000e14442030b540c3c81314480828a03a80d40001103041e289008408440050301d0ba20340500980701c1000084646900c14001408600d00900c01c5e15170007485440c0c11420990800c0c08242502e41d001c8202c0c0307a1410008007681414000c1c007450120005140c010102d800d10708010034002440404050304120004c01c1c190740c054003081c10298a5500710740400c1c1c5a04030004100145e02081c0c4003d4812490907941005c2080c040c092010900e200402510055160005100160b0b5100f00c40391b605010301501050000c440a054034041c008010500119280c28 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 717709649 1250 717708399 717708401
    0x9100b030a1b051303080a020703050102120414190b0703110732030d020703031503060b010207061106060f121f05010b030f0114061209060604110a230705070612 71
    0x121428200300501088802d15101c3d0400086040b06d130b004010958807900c0110032402c0c0101900002d04550001842d81c00b44145160802e011b24000d078008240c10015000c59542e0342003003000404103188606080003c00d8120b2904c1d42d0290183c280441e101250050340c00c001c0e840883c00300c50702c0d80d00100c89440c51a580004421941d552001c2c603c44418107080c60b0741d07a008419200c0d205940006160080600c80c0e0000c4862403815511442c200783c40740340007000740080040990052140071070000380a80319100c0c450805000742d0240c00a41c071400e00744980c48101c2c0e0b80c1541c000715880c54100003064200001c012159204076444144000308640005591301a4081e819400040c414415881c4252204030f04450300e2302c44044c480013401000c10a1402044c0380880005400c00400001d50004901c1ca03101e00c3d0222402c108019000d01803400f103008808403c1d000030490258240010142146c04040e402c00311185410100700b40e90b0302c0d00d41a01ba401070030000f07580402041c00369481d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 717710899 1250 717709649 717709691
    0x3143a020c130c12021303060b04020904050c190509010e010804050c06030709140f010207060528090315090b01050609150a03020c101404020108130f0302010203220b0609100b030a 79
    0x404410752034441a4001c160b4006c180340800381c1856a5600310800d280e07201d81c105e80c8800c00c094810b201d03a00d005c3e460110395422807806040c2038124501010714140c881c0003168821241612445413442c8040011250000e005104641e18481d42034050610340c4d502c0c000d1441081566601f044550400401c2d400c0c540c22822901c1c054600c00c04005650fa07004150581591143e250094940c0b40011560300450320711702d990407881400003a1044501c3e40240c00340c00756400b03101411075882407d103d00e41256204540078118850041c018012450034200800d08108010207240940100c503281c4441030344500480d83c0800da0004032000001000c4c002d0707100408000301c08100c1041103c2d0b100000038001400241013020303040c00542080d0404c079140070741c03941001b18010b207124107140180c000e5106031080c00a4900300780d51041b641e41c0030440008001c0c0d210350344449640350041400401400035244810604404202180780030208c07000c2c1d07219010308003020404107280044401c44400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 717712149 1250 717710899 717710927
    0xe15030a0b0105030108121e1309050c0c0a020f01031e091707080405010e0a031b03230309040f3306110d0c06020c0703143a020c130c 59
    0xf001d00040000f8130f00400d2540542d0850707502d160f69910604800320030394400b0202004010b40104400c40d240e07268210036405c0c2e135221036003003100e511400c600f42050b0148261340c0b05550b011448041c01820a00300e6016001c006040201d009c00110240c65103900c2294111102d141e5075030052300c24400e503040e10705000d050b02512285802c0890304d5809240c421405031506000b2054a24607040c0c444035031403001148c000d181030031200040386ca114640e08440c0b0042c0c414050759600348000c070342105500d0901740f29020041d481c012410045c000030700140c1c40c100544035554294041824413054800a5000c21401124003030601004108505420b50301f00e081004803144480c641002d00141480781a012428420303501c0300c443c81c244c00644120808a8044d00a021001081102640d07014410300c07106001c0e01c0d00b1a46032907001151940040d000703818404140c83d845103074407151941c0d244140152054071000003c00c00890310a003c40d500500459644200169086501011010b1010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 717713399 1250 717712149 717712157
    0xa0c050304080a0e0609040c02010f0c110c090c0409050906041a010f172d011d030304020909010f020a050d1b08191d0319050307080103060207030e15030a0b01 70
    0x41880e0b2101680390290f00d01070014000c1c515401c403013030369032001555a03001e4010414440c0000340740c0e0080c0a044030350300d0300c0c81c0c950801c610140700c40d010300090788011030707280010502224102e04000401d04040d0207400340e16410400407038400c0f11750140d180b090003410020216810640b9040310301c03820001d42d0484107204d00005010121400700e82a0803600700e8520801c152400c1c0c1c034180d0410704800c0b44001d195448a6035941c03080c0a40c5c014420f1164011700800044034a5004801410b1b8020540001c03a00200001001071410030303844e58101450703400000344007000708030400481e84542000404111b010403126151880390003001d042d0440c211203403a600d45051005010700d81c01420740900b03d0b880c241e45817494041d50303120070407950803980c1e541089100303060004d480742e102c0d4813903800e90020300c1c2074161414040c0049074001d200d195a8260b9aa20310740f00e803c000c1d000301801f1810012240d10042080c1d6418441c110f114000c0c10800b81e480c00c005641c0d0003110a0201114180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 717714649 1250 717713399 717713401
    0x3070506010f12030e010e09010f170312180f0304061206080a020310110c1504050d0215070302091518120a080304140a0206070302070f0608190c21050a0c0503 70
    0xa40b51194030070f0b800a41c0b50070021288000c1c1401610325946402c58160031181800000601c8401c009006086801d02c6520200404180141175281c1c400c05010000807034122010460040180c00c46004e0a04107000352042c0c1901c0e075150b54103561055100d800054001c040d0b200407114144201001898a500203020907010b960110792584c103040c040b07070000395403076012044030600d650484a90080000a507100c0713600c0400c4540b40c054040d10190340c1e9104940341c03544203c0c00003a000c0c410708640400c80c40c0c82e644005084029500c004205a0007542c1c50301004034030030418000d0090404044403003003105110313205100c45a541210400c20b2a800200241d01041080c01142d070807541011521b04120950b4241d60300e088140c0000030340040c40014140c0c280759000c1221019150703e0b09025801b195500d03c115071100059648441e400d0145a0100c6444003540c040d092842c80d9080628003030308603002c11002100400c4070100d031a6107c10400103401940d206d48504400f103410801d0031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 717715899 1250 717714649 717714659
    0xa030201020604061104090207140c0301090b010e131a1605030606091302040b12040308100b0306010c03090f08010e0c041a1c2906010905061c1d03070506010f 70
    0xe0b40344042c1018205654459600401e0b4812a04540103040d811506543c2c0358006d00c1c1545170740c40c04229008841c05001c0310707100d840c0340600414120a4014407040216400c5c02100c2c428a02e000d044810090701b0b4160050010f445101015072401c50a00402014a0045002d54021140d9200300040200c104104481561044103603403003c8800e4a03103001c100c0e48600000000e10130b5400a1200c41000300d04800034000c50004141301c0c0340f00e65078484181c0c03076401c45041c0d0303062507008045460206100060055114818908202e402460400792035079444924140100311900036a4150b5114a003070940d802c82004144040b85003a50f081090a80181712208510482c0031441c0c0702d07442807210106030140461508040036003018000000c2c0c1d40c080849500219452161038542804600242c3c00c0d40c016a0f01104503035000d8001c500d0401d6008801900000401201000382c0d84c0314490344c1f5035081a440202655010b200440e80c41e1050b05081c0e2400c0016446203800301410201485 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 717717149 1250 717715899 717715903
    0x1812020f0d03090804081005190b0306040303020c01140f01052b03050c0f060f0f01060c031e030608100e19050c04020a1223070f0503041b0f170105060a03020102 71
    0x19014a0b8a80024002c0c020310b070130120f0f44200d41c80740006104240d180b1000341d4031580820301400303254404010850302218100144c4004070304203a810f81181000901080c001d8000f001501c2da00c00001a00d4004091401800602036954010000c01d07071006000905009160b2a6004081c4040f44070302d105000703102c183c00802c41001010030801164002c0743e1001042081e141840350002d581480c0f03490740d82e50b041e440040b28107550070a929400091558022a00400302640541da4a10032100505c903c0101d240d46d82c55110815607250800585180300344a50811140c0740000450903070440000c65241c001988101d003098021003c610002400000e07070468459420340300907031200084081603910100e400d0402004a00381040c40c41c40207441440761283e04034510301109903071950300040755013082c079010510219000b0030209000c1542045402401e45841c103442d8901d80e290004824810000c0d030180e100d20190015001c0c055500b0f004540c2e1156090fa2403612007032a64000035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 717718399 1250 717717149 717717163
    0x509010b0703090305031912020f1608040807060c0203060630010209040906021908011a0c010b0301150e06030a0c09020306030a021c020405060a140108090a061812020f 74
    0x35455800000c1c0d22001c0500800c040c0b4000d6400c48140c9840f0b003c0c01d0405501043c014070510009403245409041c400154401e4505828441d01120704280e002c1681d503102490003c0156104003040c070000600300400c2004c000502842d030707101c0100070803d00c1414540f01004e000c4520950914484402d0b0600c4600d900401111802140059081c5000482e00a1040010342e582003428591000b051010580082803a080b03c00c000c00643c0362403d0003120822002e0089242c0990f440640c030704800d0803000904160505003000080c014034980000c3c0c05c40c0c5a59000e1459400c0c40320f07003040b480c100345400703582c8044250040c11908046a4440842642900070301c043c0702c1c0c3c00b1010485681303040002c0354040303502800b01d44c20703c00318044013a1030b0311094408920070307420700c000070304282803070749070182211700e4800d90300c421202e02001910588801015200540f0400c10b500020540c41d001e201d03000c1126042000601d10b00b81005141024107000034015907100c10032504200328009100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 717719649 1250 717718399 717718409
    0x8010c020319170705221a0901090f0f080d090b09010c030309020a06110d0905060a0f0c1a060f092a04080f010e010c020712020d1a100618050901 64
    0x714001d4030020310306581c0f402005022400c2d01603504100304480c4d800000420b460007103804e070040c1580b402d0801c2101018613003d0381c0500c03596021140c151001c03034009030001940504110300d00c251070b83d0065050b001240c0c4418504a40c0d0001082513600078401000600382d1403030044400c0d0b050240c448076500c00d00c2c0d01203041000010966051521960001c000316900810619801c9c0c0e58410050841e1521203002516000c1c10440c10105401148110304803030014020b5405d0803464401a100c68040307405c09802d214005100e0380000e088900c1038105a07010b9008001141000c0c0c00b440a0416540069130046060500b800091130807160301c50755002c03d080c0d24074440040d1180802c01801540e2001c0840e21803681c6c0c1040c0c13000190001640811440000c00040d080d42c4001c90b0754010b54070804444100701c8401c1c5000d414000a18880b0340d020302d1490365081050f02c540283d81c441203581d1901c14a0410051103c5603100518218004000114103071140c2000f0003d0340d030407418820303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 717720899 1250 717719649 717719677
    0xe130201051b0a03030b03100e0a060e0f060702031c020702090609190c02030408060601020a0b0106080a090f03051305040b060a030203250c15050103031220040603140108010c0203 79
    0x14112240450700000000d80b64000607222030103080d240140281207407014445c803a009164248803140130903c0b6248440e09c2c02c00061107155101c0d2030307000091642034000328007406169030403228002c080103041d00503900c1ea4000c550380c0311102142c8120982090031840801d004101180142e43c41d0f6481d140c00841c225001c0c1015111040310102c115403002200082c2424580420903c40c2c010024204030b4a0b044141e5125a90300c0004a03181d125520008101620110042c82000d21400c0950740c003002d00000050f40313017110703192000c5140d20b80300c040300050780024408200d400c81c0410400202820b0f241480002202e20000d13502e07015114850041513404000034518090342d0504d84240803040b10140004211000c00a0200b400104292940c4010301e40b40b05102d0820b10600e4101da4040e0f603600628480440d041015141b070b810701c10811203000440e00001c1d0750b140b00410040403180c41c001600c140031001c440707407001b05900001c3e250745000a011001c1d42c000c41110100401c2c250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 717722149 1250 717720899 717720907
    0x7050d060c0e030d1d0901082a06190f03060b16051603050606030f06040f11120106270e0a030c0201050417060a140402010c080d0f0e160e13020105 65
    0x1c400c0382c40c042c0c880c58142d410301c03a4804201c10303d41c0010b141c44140b40d000100c06441d0541c10184141c1a40a203d10046035000710000c0c1f40801808e00d4040d00d1000d0303034220010b00382d501c40000714a0340265800b45200b5051100350a801600142c80e0036941045d400e05100345032420303000300341c680540b0111450703000c2060741030001c204042c400c4488a408886040348403603124180540d59039030440e80319000b8400d40900c1da0841d41c0009659201d243d004c500d62103041a25a035500a000d240340300550069100d142d4042c16502c2030054201800091191340b5031407240094080e1034500078071044040383e150481c0110394580c00310307200004030b8150a114822510920048840744546c3d442881a0000354004623030310240414000e0040110070001e0114030407615800100910070350b40240452000e10214000824200146c4185030260b1400100e148140c04e1240a5030b440c2080a40c4641000b0030b1003604800130032034079000c1e01e08003a580c41245071400e46404086c0740403202070b050110102d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 717723399 1250 717722149 717722171
    0x602010b1e13230109020406030c090b03010b1303020d11030714091506040305070609030309170d0809010b060414030d050c030d09020402070206070b040b0f15120c12030307080907050d06 82
    0x300c990060f1145024030400d03603076880c0d010000350080c0c092800001c1c18030640b203c00e988242001c0e8203440e400303551240303940d2800b91003e545a03c2002c103070300c001850800c00809684e803150001072050140441d40801d0030804101400c05200b50003440d0750103c0b16154209984401c0d828a82c80314290f807076010212050030010b8458010341e0b0008103030344a0b0f1400442e1181d4804108003c40348680c8900f0700d480d80790b000f02c1d0b40c01214440100e581754000e00d0841040c03881100b0094000d100740d00001240040c080c040f0b00b0f5030380980c1000183c1500c0002c6000380f800c04000ea400040001d24080d402d20403920040e984a00c01c0303407940d00d5000d03140e80910040d5030390b690465180580c010302290b0b0b01e4181d458510100f02c4100e800751200c20b14000050840c2640342036861251440079401288010008108803100400e607440d084180709099034540c00340c88014041040c0c240210003140c403490144401044080010a006529080180104082c1e00c900d040e0030003c0380c0c440c0c2c0102c1d040c0d180c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 717724649 1250 717723399 717723431
    0x501110c06030603150403020f010f0203040317060f0415060206010504021303170d0501030b0906090d141612020708300c100c030506030c031b0609060f03010602010b1e13 75
    0x1000e05c0300d82c1c2408001c207020815800040e01511009048001e1102082d1006100c0413404100c0300a4040b49041920b12013400d004006903500000040c0303d00030090b80c0301c2c0420304542c1d6610000c0200503032410300380200303501040030a0041004070350943c60861905401c41a49486100c01001c0900c008015003201040c1c81c10b85c0d1407100d0b900400c1009607540d0400d03150710b02c81a0783e080f80d540141c0b00450b0700c1500124141d403481c1c0c0c0d0f94a03a041d194019140c8041244d100d0307503142c0c43c0601007d074200c0c00500407005442d04003803d80e005108050a080713405003441172400c200c40c0030001200007110000f410310740300001041084026601e0f0030303a801a0a003440d40340d19014002030300e00b4207580c4a4035010b81c050350141e10180d0440c0d94506010b01450340d2080001400b40042c604031080b003d0a20b0980010401503601914042c00c0a07008444080650000e800000250351a80207a0906003031039000034040130201000b049040b1748042c00320b07550000320000c4000241d1244031900c2c0e042c10b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 717725899 1250 717724649 717724663
    0x414042a020a080c0d0809150106081503010e030d0c1e080c090301050a062402070b0c0304120b0114091603050a060f0e01030606090501180207030207151106010501110c06030603 78
    0x207941c0c070344d14122001e940352070788403030400d91010800d001e0104040d8580041c4c0c00080b00c50100200f12070340d003045000d0b140c1d010010000c40f546003403134820100f180c400303002e9103030282000e0f8000c0d074503500d0b00610b00040e2643d01c1c3c100010000c8040181c5145100402c0059214920b42000c8443c0e8440c1344c0d00e0499445030300c101c40e403d0740c01e04040c0301541c9010342c000c10807a03440d96285601c84008907400c16900c000507500f040160301156041c014401c0c604010602c11070880100c0f840d2a9540414080b0710b04403074400d0b65100c1c500c9004004800714440c45040740001100d402c0e030300e440c003160b13100040d51000c01c11b007007050780d141e00080b90382665912400c050084203030b400c280305036943c60018114109001c12102182030450020b60303060f00b8003c05050f59509a0b01c940c4c03180c2840043c80094014080941c110b10031640d001641d1501c0d005045c1e142182076850081d080f03032440000c0c0c0340c1340069000ac1d04020022644642c8100b0100f02d5004d00141190280c1d0789440d10800645443c4c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 717727149 1250 717725899 717725903
    0x12060213050d0c09020307180308030405070501050906042c100f060f0801060804020f041803020f012d110406050d0b0d0b0105060c01060819140a0206030c0d1508030414042a020a 78
    0x1700c0308c001000b40100200950700ca1440344086807a05521480115024001e00d498160131800502061295203002c480d44194420361901e0201c0340510002c4541602c04140c030b210075001a918018010a405d0101d140090007080c1043c500c03c104c0520000c00e000d905108500810411201150856a4010342d41d040240014418002e4820124051043c8101c9001c200e01511030102442c4110b0018001d4450560383c21100402c2c4940e1200c50300c200ea40301c0084c00e0b0034a40c0da00d07401d1018100200c003400280c202a51099280e51002c50300504a5080b413090b20300c180c0323501c0d4015000a284e0745840e03042d075800b40c0b00c26403540094028207000d0089130704a0055809990500b0740080c1803022004099809180c14104041c1320480180c0c880c000307500040d401c0340d410000035107685803440c001c084c552002c100018035084040307e400384403045a00401c4098200280400c0319039001c800810000c2000c450070802c01c20051100302801340249402070180c4049207144045e01e00901151900d1a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 717728399 1250 717727149 717727187
    0x903010e0f0303010501090e04020306040b0c0c060708011703030f0109110d02070f0323091009080f0a0201140a05220506041d01170309040506040612060213050d0c09020307 76
    0xc0e65036010a4a030f8000740500c07400511045800140c8040028200c0e0045c1c1e0060041c0c60592035640396101d10032401048412030071403c0200401c140c004014080c4619995a03844900794100304071688842c0b100008546140c0c024800c0c44903d400a051690449828403030008038500e000078041101d002d40044403500c035102140c0041071007580301628030580d129a803100c0344030210b40c40554030351128890003692884d05015030a00d50800e4000c14102d100340c0d04102017100c2d95103001700e15224446281a002e82c210b00b100742e00315600403a02d05482150101c84230305044050a00400501806240440d034000014040083d2100844501c01800700500384590310360b01c847d000500b4200ca01103131410142e081000148801d410401c4001000c20303d0061403400342c155041001030540640000e6001c0d5440c200000c1c014005a51030319042e10400300927031602c4080540141881c410780c0210301402a1403049400611030800400540c1d4403504016100d807110b0000b102d0a0300c050b001030b5800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 717729649 1250 717728399 717728413
    0x240102071215180c090b0607150903020d0207050117130501050702070f05061312051c02160e16121803090e0601030c140d090b130b0f0403050f0903010e 67
    0x20001c1000080c00090b0003101c24040119a46400154404a80406031201d500b0345000d0110191a80089a0604006100604082240e00d581307000c0e0200c0910030103190365030204070b000c0503018003000d002031119002800c0c0305458000080c021803140004c40318901c41880008041110000302c1c01103030382d04040200614581220702075070b0b940d801d01031032800003024107002403149424012940d503e10001000d0131240d180800a0380113500c103107400c450074007401c4c0003041407034100030004940c112070390300a2041e080640000a0060450b4000541c6005680d04003c80c0300111030040701d1644003882d20f00024103c61300c40c9030040600050b2201c0004402180005050b400140c107001e65041c0d07440803500307483d54001501243c501c004541d02155103250804c400400000213046800003044003c00e00907001e03a0741610501c1c00721903011412102000351802e0180d506295580b01c4682b02c2c0500082c2400d4a01506c5400750b041f041c540043d001440b206107441c203400031010b425200c1c044a0369 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 717730899 1250 717729649 717729653
    0x21030406030e160810110c0610050f0604030b070c0201050c01060311120d080c0a020a050604060f0b01081b090a150306031b06230906070804080c0103052401020712 72
    0x1d02401c0c0b840c42041e2040e07846904606104100080458018000400b018500140704074081e110304020104440740610902d0140c0005008192054240a00e8500c081d420002008110503403800c00a018034401e00050000403003180300e5603042000c81c10140100021440100c4061140040444855090a0000042001c480310000284a08a4507034075112015041c00303a0b5585401c02d0710000032015404902c20401d0303200102580649841516006e070791646a452030940305407001c0340c60543c0c5000d4102c011a061007103964403c000d207417091860400900b80718050f103004100107610440042d1303011050703403600d0100004100d41240080d80d44548038015008007401e2100340c0b414003a0380f0300d06c1202c4140c0070024003510350035120210780c800c4044200202420f098501100000100600043c95560078042c00405116428171a03940c0c0c1003a200d981803260481d403040c10305050005010700068480340c2c1090005420302c000a415400c440100c0c602400da510612950340d5402403082 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 717732149 1250 717730899 717730901
    0xf090c08061516142b0c08040b0c06150303030108100e1509010504030207151205041403220819020d030905090a09050f0a240204031e050d0306050a052103040603 71
    0xa1001c0030a0b0984d28072005d18031034103210703d030840059201400a1215201058003607036084e4510390184104600349a201c82c0c410705070707501614424820b507108504129442c03c05194a0095002c00e501031070075545000221035850a82c03601d070f115500d4496000f114182010000c050388800e041141041604020356694003c041c19a030550041c010f080700810b80c8071b1848055000078603d80d50b20740c640075043d007243c402010050000c8900181c410740d0000c1c103a1382000130f0080c1c504918818040c030b107030b09041d042200c12145c3c003c2485410081c0c4512031101510003061100e40c0646605008118500c0c0031a154800c5400481d880051001800125520741e8000d030a4030b07100c1c1c0115110085074030801581e1b801480d000030200c426060041c428490482d00e6426403901e050005410641c41c0d550f0030070141d120243d1050200c41d01c4aa41c0c0502500700701c2c010300d040d901d05003007110074100741c00720342d1122282c01990302079500302040d010143c200d5011820b0b40c12480d03086e40d803646d0311454010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 717733399 1250 717732149 717732173
    0x3050c010f0302360a06020309010309031803080301061806020d05070206090405010f090b06040b0d0c170a14150f04110d0e0309040b120616091203090f090c08061516 73
    0x2140c2104040c1c1303076241420490740031026a00b05070001c6003010b8050300114050059228210100a015801100032081395400e0f48080e5108050140e00ca6040c900001d2600720a40e4040c240d041906000304400c0f03402241d074400c401d83ca80342c40d5903114628008600c10744640440c07150841d250000020f803002c9030074101d6050faa42e5110038030131f840b90401040a04d0156001e0300d50808000c2002d0310307270764059070302210705641c0038200340c003140324440c40206881d24116111480d0a80b0340c2812440c00c1c22540c1c40340d50080381e03010038414003422003000c15814101c25801074050350f03a50303a800d611450010300f52454698041000d0000741c5810814540b6600498040c500650400c20310511038a407101030300541c0b592100081617503503611240d83e41003c1764100c401d401e204c1100b20100301400f0260540c445180292035480407940b42607903800340708940350b0180c0c5400c2c0c50180c1c0c20140c030364001200f5030021000c55441c100281c80c000140304034890002c0709a0044940d035200340c00c002130481c0304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 717734649 1250 717733399 717733477
    0xb0f06030d0503040c0e061f02010c030e030c060f180601030b0f06090421050408030a020c040f050c030f04020d0b07021e342c070804110d0303110301090e1603050c010f0302 76
    0xc0c051540e4892030b640c0d0345d01801c10780fd80c07142c00c450b00191003102ca1803441948102e0900040c1c14540404480d24244031007a041035508035080020400090040518290084000d40302c0055520303050304d0b022848001003520311542c0b03560340c4e8001d8869110301c0664002d0b01510042d01e640315a06440655500221800c182c050340c208403000300e01c0c0040c0d202e80b51040307810441c01455669203a02c49441c242004100701d91000c22054181c010500c0e018007548600b040c0d07001448031019007140c6580001c0440c42088143d84064280360921142102280c030300c4d000c9201c200c401c188000840000142548c100d2895550040c5100040440c81c0d0003d480d40079032480140390544951004071a66281103802801e10001000040c59904003054a0007005010303203400999101042200e085a500a9001d070800946407210b5021204e0b040c411540c0c00c180c200c50403a20b892440ea80d1541b10218503036494144a010040305245d03e0003901103803141d4403c40c0350100c00c1c114a15840c2c2c11001540c0c51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 717735899 1250 717734649 717734651
    0xb06010903051c090e06031c050f0304030507150c021f0b030d0f090e1b0a03090c08010e07051e0d141014131119030b0f06030d0503040c0e061f02010c03 67
    0x700007041d910f08517000d070040343c01070041c0c100180381603e0704c120604058042010003404000c00e40484541c0c3e4040e50003548a82d035559070f030314004e0815000105036001c0201c08586003440504010380c002411700c4076080000031010281181140e800001c1c4402140c498042c02801581c000f410b034400b0118060482c5901e40184054403030696031620202142c0c0380c415100c916080e29031030006203010704002c560900d0040f440c0311107651100d034044900d07440a01980e440b1850640d4060051044202410095880c800c500c50001d20074074040000155260141c585132a101c4180a1480c4840214003501c03012148a40140c110000041c400c400201c0d003074202e40030118401d6a00c0c89241c03c4c141d81c0154801158003081020004070011980048a200b04007000c0000012504c89d2014070075090054880a00d15001c01894200300c40d03c42d829080040c09c0081000003540e59240c0f07001c0d214119001c00459842c2008500190102c078108c06ca03000d01e40d00068a902d40c150400440843c0d10340d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 717737149 1250 717735899 717735917
    0xc0207060f050301063b030d0201020a080f06030a020607050610050109180c052208010b0105040b04031103010f2a050310060309050a0f03050a0e090705070b06010903051c 75
    0x10044800028160490000450820040011a01c079011b4650580340042400014502e001054118821411041d00708111034007001d000900c0d00740031107211100360780001d5140c03a015800007005010010621105048001c0c003140f1551001c101c00c2c00e0842d07025104c5a6668014140ba039601c1c03400322501c400040d072080001c40e15502c601450000c8403079280c01c20301982c200100360809051849048800c10a050200c5849001030190038410b440f4890840948a41000384103425a100076241a0510900300410003039040a40100d404481c0c101455200c1070b462400000e014021498451054a0610b01c1c1405404200d003880e1a0398054511840e0003004d0300340303003aa190701084944820b8000d602104000c082e02941080529522600580d8200c4000d41e803080c19820b21076506030000b41e0701103010910399400854078950b65408540c0300b84035180c004401040c41c070034508010302d0030102001046003640907121150145600009580c0a42e20350301130f414041042c01440c80019501da9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 717738399 1250 717737149 717737159
    0xc0a031e0e150304061113060908030f1207090f0f05090a0905060a1a0d030819140402061602030a060b03010f020301052116080618030c060f10080604060c0207 70
    0x206003201d401c00c02828400510382c1a8941d40019000140180c0e00c0a4480c00c18101040f00386004120307294061481042040c10002e0040c031500041c0c1115000b54030800c007101031000402c2c291102c030301c1440101c488a07503075207a0845030010740d54070400d12941601e00101d40300040030000c40036240180c441d072f030f0280d6a8114003002c0d00c164000c0a00180c0014001c1102c1d104030b81c0122101044000c1250510039030407003ca144090a0f640c00d400040e004803e00169080d44910200b40e07004010b4188404000320040220610b400382000744221000204131594004032600182c6a580042c151426000181410000b40c1100100c0620a501e02500c018000d0340520070789041c4d9030f018014074103c1901200c0040040c1c20452290103d108030078240d04440300c6903440d98041c03c4014003419450800c0d030254007004109002d4a00f45420600c2040f5014100081165210340c1d60502c4c1425521400740c4819110401d80060060380030741c2042005008085c1c1002c0d410200d01c0d4200d0303040e140d5076 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 717739649 1250 717738399 717738407
    0x15080c03100902030a110705010b01020609120f1305030a1104051b040b07030e120c1c0b0a0c030b10031a04090b0f0903090a120203010e010c0203040303140c0a031e 72
    0x1200d42281d00e03500d50300140191101d40d030146038441c6110a000448924003e10b00509421066044800da03444000140790f65034140701ca00c1d040717850040245480304655510280900070365030b04860000b000306200135254940c0011100800001d0255002c03c270a03403d09400105110903803c1c012420a004160071a40c6890107800b03600c940ca0055050070304060400050307512414083e820000c500c1d15000003551401003104601201c18020f0101c190f0082c184040e0202400302c54044115200c0a040483d0005602c0ca50140020074006016520300406400400c1c4070014a40c0020042681000c02609544020000120841d4090590150804010640e96440320041c070007440800400c808900641000e41c020100c0c80c00d1728206080180031942c41901a40144202241ca181140650400f80300e00200150302038004c1c1710600b00c500003c2c5d540d01c11480000c0401c008958404401050306058910f003500400544002800310705006103150004008071000d00940d200d103041c01409 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 717740899 1250 717739649 717739651
    0x60b0a050a0302130603080c0604120518211c0305060409170f09130b040e0105060307060e0303041d010f0603091a1e090f01060911090409081315080c03 67
    0x704404161811542800000001c1940310035186484d082e010000031001c4015111141901008040511f05801c040004007110040d94050040c2001421080b0240846501485905a50070107220301400e0851801c0e071203116071006a4021061421549500c140c060340304402c25540900c01ca494000401003250075513800100741000090414055103143c030050100308101c00211420024124041050302e11001d003042190b90340c50b104000c0c503107041e11a036511484a074000b0809807800308080795864075140210800c0c8101b5010240b0745039000c02c02c88001d80f40d0500c1402c005948003581d101014000e00030003401d50300054000c14407034800d102d481103151b0021004d0314400e503080c04000750324a02424003581c601c04150b484403031005054013140584c03900c0c3c005000030710120f24000e0031284d142e084000d8141c2814015180f812800341601c0d059001100d00107024000752402111074032403500116000b651011001951004000e0411500001511400001ea84044c030140721480 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 717742149 1250 717740899 717740909
    0x80a0b030316230d02031c0b030d05161407032a0b1c050f010f090e1b030307020d0b0609250e0102030904020409062c150f060307020604060b0a 63
    0x81003407007003021846040d401c00151024040800310f00031a141003e04084109182c04c0142c0d00001c0d00c01e01c0b2816a1843c6516200007d40800c007922195000a0311501149283c004018000c11108444031607604e15102e104c1d442913006203000400e0035a6074403084144410344442d2480405031281c204c464550341d03072082a00b080c4d12450360038035604600a03002000d000b0307580001c23040c032482c0d0442140315540c0144854000002150f140c6416001c9020903500182e180c14200f00c081c1490315400284640a2003482000c172046031031182c042869800f4441c0041e61000511590b80240035450703218a00500307068070074000e260b0700e030358242d0142d99100e0100a0003440c460101d9456521030484c140d2401014810b4902e8400e80800090698002d0f80009015507600c0340b080013008031410100441d04a410800d0348c404100f015105500340300201980f004140342c40d41d010541c2d65010f0202a504001422151203080000c0c00030341d02c0c03104a400704e0f001c4d460311360a5441d0707203491849801112 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 717743399 1250 717742149 717742177
    0x30209040905061905060d03080403201c030b1008040f0b01060816020d090303050705013305041b050c0f010507050a02010c02060609011205030d33060c0b2203080a0b0303 75
    0x1f1300341c0e030446803050001c00981c100400c03442c500440c410a005001030405029008120f000030030381c083c0030403490400d08003050600d07104030411261541c1451001001032410004103d94a0b410300c2091001c1103a8020101100030703001040d40c0ba00b08254038040c998880140d070011110100c2607a0307410b007810003040450030303a00c1c0804c0021321950080003a18820800480d40c0c0800348800d00a5030051040054650200d10111283c03503100e214a500501b411141403109260411030b41401c614050490010004001001051400100100500034020704001c0141d841c2410004042c0c2d007107011628015402c102e0441d10f4107100042136402100001e1012040b64600781e44100c00c00c1442c0002c41e0340c0c0c00305000c0c4011400c0144584410610400c0103034210601d40c1c0801c450460507440d9034000182044030a200c090380c84500440b21950004800200e0f44800380502001042c440074052001106441902007541c0840d40500401c0c0b8040240100080b60302019144c0c0280341c3e40c0e04c505 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 717744649 1250 717743399 717743419
    0x4180b0a0e040f0b07020c030f160506030705070f051e03090310020a0c0611030703051006050a0f110102030423070503060a09030e0a0e0108070614091003020904090506190506 77
    0x400350400c840e82c2c0080c4203007810031000a0b1551403200c074660440b44034002d42c000c4007000d6010706040c00008811400704000c0c040800483c104030b5100b84d543d0084a0141001100155515001c0d104442c205900407504d0303806004a4035119640380f403184200c41d9840350b21018102c000000005440c0358040084c09130007610007010811000350003032850042000030b44821000890f00510071034250790540d4600c155280340c030143c0542034072000781c1070231480d00596600304442a44182514081ca446161503210100000c01c21030300c1d48420030b003051441d40b0010601080000c0c45038140b80306103c0c40c545550064280329110f843e40c41a10a480d010f4202c0700001d40b1045290b440792044501c00c1c141240108500c5002c40c58001441d0881d00640e4500c1c1c00504c1407040c00c010b060020304182c64806210b02000c2c11a13110f90107480e1000b4020102c050401102a0180d01a03844180018208004249943c1003850340e07800140d444881200c016007281c1c04c031000324080c080c41184003030320540d02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 717745899 1250 717744649 717744659
    0x70f0b0d050a021b070e070906172d190c020a0308190501260a0206070b09071e1d01030b0112050c03060f160e0a06110c030f010204180b0a 61
    0x34081c010201c1c1c91080d400c200c2040c62a8983c02c0c030004102880d001021000d0410300300d03425410f0051320311818010304003410400c460344202503824824032081c4007a003645821454941e2400e000308a504004a44c156080d40e44154110701403140800c400c2c69a031000d40034040d00200c0d8481080702c07006030018141030010074000e2940540000540d42c80010b658002041c4804465084c0c10011960300003540790118290405000800c6040000c06030128060550000780c0310311615100170580480c610004800307110920016004216600854002400400c01d0620311461406141603500e900111f00c403248005c1507a89060301d13800800b41000e40d08007041d4800070284c0e00d90803262440340e018401002d4805100450185288510304103050802c82076162002510f004803c081002c074507020903150f56840c04803800c544207030038418010402d094005080182d40ea100c0d0750584200f0410310081d480540c014130880340760100018441c0311020703200c0140d03034200c2c00e0103a2000c002102840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 717747149 1250 717745899 717745901
    0xe01090b030c040c05090a0b090a180e0106080f0d02060f011403120703030f0f02070b0a18050304030f03092403151707080c0105090a090504020303090a080c03070f0b0d 74
    0x2004100c000d088a15501c4004005400c1e25100b01c4100001080424450058101800319001804244d04040d0a140100d0702150b1041c0c5180b1600c060082c0d000c2d100014000268000e640c5001203d00a0040a40f10300303101d40c1d40d40c03000c3708102e0b0030b100728840314490f81e2011640314022210300003464940d034030303018030854200115000141d160240309401c02c28046000010200e46200380c41c0411011a000704e41c4c4211640e0b003a40f1406503004014540025011083c0305521040c0d49000185591034159403500c5103440080003002448001f9021090292035007084052074405c0d6601101a43c660381d56040a5410024050f45805c81322440d12004d40130303410110b42101c3d0b1650151400c2d0f69641c1c1481030201404004c40d103600001c9003800070f90307014052480160400c0c00c0440c9440b460340c010a0710a540c41c460030030301d2030756400880c04540d03050044030744d00d400c018826001144c580760b015840c0c2d9038001a441c844d00c00c4044c0012440100400c010490b035200709500d0810f948201c03260 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 717748399 1250 717747149 717747161
    0x20c150703060b0d050712020304020d14010f021b0d020a03021903050f07031d0301050c040504091505070203040806061f1206170718020910050f0c10140604060e0109 73
    0x1109154a8080c040f0b003612143d0f01a1003003244801c404a80341c00d103040b02030600030070000d40c1c103000d41c010010400540c5483c59509880e80d8807401c20306650f010703601414010902c0700c00702d00302c050000034030081e2034940301c05484200480c502907408002c41290243e035619141c034002800350300041c1c0b81340c0076181d4802c41b43c0d180354042c3c1881c0d0701d41002c0c25a81d198950100d0b500300c001c22200d00c85d218074080c041401d0b03200b20200394000c212034140244030f8103141c0220b10585102e56221842c180030840f0300d0324481c00428030004c09114604103014065102e40107400f0348640340c03190b1070000b034580c40c0c00181c014005078a9020300d612890b200c64211440b18044a0303030806591100c0c4001080d940016003043c4019540015020b02401c144800d5184c40c51160b504a003d030040c0585400c0382d0b104c2c942c00307000c1e8129041c440d5444081c5640c042c1c0074001c42840817038501401e42e0781444050650455501c440c0059043c801d695218000c000445516001b8071045515503801480030001e1b65102c1c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 717749649 1250 717748399 717748411
    0xd0b01030f081201061106091f0f0633020a0b0a0903110709020d0c0c05070b070516030501050a060504021206011110090c050a0510020307020607150905060402030c04020c15 76
    0x28600d0a43c007041c4010310102c00703070301010014420700c0309000c070050280055504004000050f100340420040d4482001a0f011048510190f45210001c81099180d20080060024140c5145084c8600c40003000083d02ca0010b0704010b1100109d03100c001d480801d8028010354416030100d00c03a21000240b500500c1c4100003102480300800814a070300314104400d40091482080240e039908200d840c0c04151420401202c0c00e0121608070f500010b240802da000c162603103c40c031140c0790313003a03401c046140c0180c61480c0c41391707100206c5020007446010b412040c807403048010103115940d582e000380422442030b908506015410b910201c0c5c03540d0310444220800440f55001c0300c100406101d418030032039261020444810303101c203001700003a04002209400a1a0440d150618180109000b9480f445204c0c0001e2040000246038002c020200d5901d131041b0244035010000c1c1404bc0c43c040e5a10315050b101684244580c101d61807641c502402202e100040138030242405070808015001c5c03d260145c59 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 717750899 1250 717749649 717749663
    0x80a0f06020702060d2d0c0207051504120305070303050105010c020f040c031b0c0c1d1602190308071409180a14070804110108150f01140c16050d0b01030f 68
    0x41840b0708a0207005044280c24042400c0d81d0969400d00050740c12014169646c50790741c02c19185a0325550041140403c8500075290341e90000d0306072810031000d04c5141c2200034040c1d00c00701c4100502d503021005e000d13010700c81e460402c16071340c91b0b0006540c00d181c00180203501a4226081c5a00382c14541c01105c0c2405031814041900c0001501c42c80b10b408889204000065040c00c410702800203100706440105440601101030b50f01c1c01e6500088000e004180c600d8000c0803908514483e03100300b000d880b00c1c107401c1800200c001900d02d801001e000095603881d0001c4c44000d00b0f16155070b6110101c40c240d0000070021000f8107040b000d081c000100003000c0d1000956240170b99800c500c0110701c1d50703105528540c0c2c1e0020a113000c1c9000c038082031501c0000741c10005030404000c044600750300b04040080040300e02050041c00c610040750154070400d0b00c5900f0700f1012440f1544448006107003c0c1c585210390050003202d07126401c0c804c8040c2b808802034031603a0814010000f203540002c0c58503000d405801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 717752149 1250 717750899 717750907
    0x7030e030102030a02121b161703010608011706070207120201090909050102090102060f090a0f1103100c1116090510081b090601030e0c151c0c0306080a0f0602070206 73
    0x80d007281c004440080c1c0c6607170001104880c0070050403030030f07910000600844106001c00700002e600d901410401c160000c5004600d44148a04811a41d04048011900e42d17503942e12032000901c3d0700340a1044c0200c0d25407002000190b008040f801d01d2040c02c0c0c80e80142140380ca000b00d641030080c00c6005c280c0c148011207130042404581b50180c00e000307034000c00016903642100000249800f100416030174480c5510410301180351001b242d804501074103c000444010010300b4040081580310001550510032040700c0e0341c1950040c5c01c111855030706078850511015010282c2919030016060350440303040900d0b803d204480d40c540c00341343c10040222101c07038a070b07488014242c035040c030307a107003903400c0c4075000d103030b4034014a0084010369100c0420318052204a065a00c5a9600c941d2003208510a0507001100520b100160058030710800340c0f5000e414400c5643c1403240000c140d620694030020f4100080887c184600140c100003003a03110300c0c10112542580c035108000d41200c0c5080b64003607030400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 717753399 1250 717752149 717752177
    0x1206041a06211003030809032506110304050604110f181302030a03090807091427100608060f01080d030209041d030904151805060d12110d0206010f09020703 69
    0x762075140308240e0f04084907546421424003a0031440f0003444601c05a00070010401c2850f07102030340c13420b108244041d18140c00314510307100000e445c2c550036044840b42c011041105100000031181c1c0903600401d0042051241d102c2404000034500c3c2c45240c11480e040c8448543c9030380c402c1070035804100c0c1c80041044011540c000f0b41030010781002580000c425500074440c58406010000040c1900c0d40c0030410501c140210310340f440f10060501580081803900304183d40400b004207800702c03054200b41d07405520842e070740c0d000914660003a002c0350311887c0005002e04c20301420048c1170701e1455004119000c0d00c070304110043d510000a094001e42c89041a030f06490700c144d80481086d010502960300c4400314414003085a1900300c0d01c088240103000200580019105114003026010b0b4001ca40ca5036040d01191808000240c000d244074921440d412039175074051301240105a14005a034444640c5641c00c0f03940d444280551203400340401c40800091610707a00500540340b10741080c00c6801c81d55 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 717754649 1250 717753399 717753457
    0x3070803040b070b0106030615120b09190f020306060412030918050f1315090f0507060302040e0a0623031e0c10020321090a080f1206041a06 62
    0x760b403060815200105000003001a1030745124050010f41c81c041085030b1030542c001420502c0c80c0740300e906221149681d4002c0d402290001c10311004060021441410b14220941c4c6040e50125407202103860481084003800c0710b40200c82c002d1000814090074181450940d01c00c41072901404c0381481030241001070716082c4940800c8010640ea90700290314609803104a00c40c6e00000d20003c14001180075110000346403140704007086000410000b100d41d55441c011118045640000c1c2c024030803120b00140c00c5074140c0042040d80e5800050b40400c1c1c8407080c0300f0003524454050102a58400c841c1c5416403040290702c49110304000b021606240d101070540c1e41007101d0034009a0300c90308400000425418040c803218428a038510065150405820385e02050f00422074807040304800020109244280402c02820002c1d00070210079510743c4409c1602d01c032603000755120940032103a07400042107841c052080030711551100c0c899090100c88034040040303a42c00032003103420014070120212451707240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 717755899 1250 717754649 717754657
    0x60702181008060406090b01081c140412050a060617070306020a0e18060a0602030c06180f03030c0706050c09060313080c0d050c0106080606100c11100e09010e06010e09040203070803 80
    0x580000400381b019050a02c1ca80c071050300080404c2d4064040c512004085a0041080054900d05105841902000c502c0d2500c2258003e120706a0801135100500c640400c0e000d0100b0b04c5000300700403665980a001290100340c100d07051054011980c1000419403a8009118208482c50103c0c00c9154110000e40d80c810340440d8110101c80203005c108090030240030003006414540011030808041e140815038800c001460000c041420006102c00441c0070070a050351200c044050381d07200d02d0042104180358001c4202611a0360078a00031440c1810b01c1d20807550710180c00f034800751271542c82e01d05070100390110303c4040f00c4a030820401ca07407086034180b02c00001c0300e4059036003035038590402103005c1c291492074109a0f01351708040d0500c03030103581e41200301d80000b4050400001d200c4140c240340040f5003112941e139401038424100d0341815544103202c848901c04c201d5801ea9240d07224240b80a451104942d9103000c1400a0010b0303e051030301c0d41d903a40d0b10a01c01001c07116011b498450490440d08 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 717757149 1250 717755899 717755903
    0xb1813020a02011103090c01030b030c0303030115030c1b030813050613021509010816050d140402190609090207110a0902120a0515040207060b19050f0607021810080604 74
    0x6800329000e481c559080c010340c200440745100080c11400c5c4200400c1e107568600c00380b07034189035882c00010307d2a182804000c1e0b001e50020140c90301e96030b40e26446030211604109081c000391800000e820300c7c0340206056000b16021420f9003054511b00d40c0e0640d0020303005041c6031ba1480d000343c01c03a000100c1c104240c0b4840d0604900c1c401e041c084da403050083c1c4802c124050300c041d0001f4044005640d0344090020b80c0200705003494040342003009000d07070750762045400070458141828404002142240e007500e000c1ca20980d95101070340005418400d040d81c1c140103102c0040d210103810000c50490b500507201540c055002c030451119214002901e070340c0c0c91390002c2300254000c41e484100c0107190324040c3d8030047d00f42c0c0a01051500403c1e508421094048d040c1c491035000c1072260612445038400d02d070100000d001483c0d060341c440d4251506c00700310f210310362040b54682c44500c0c50b41041816900d810358080d0110032940c44840e0380d114400001010b80090000c802000501050200f01c26402070b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 717758399 1250 717757149 717757151
    0x60a0c02100e161409040f032703021c050c0f04140f0109140103150c09091d0f01020c0705060702011b0f0204060b03132607051c030908040b1813 64
    0x30643c24804244400541e0141804080b01e540c00c1815843c1e00f6802680141c0c490f01c1d1250307424aa1505444606080c0b0110b0628a440c0d8880c6030351902c203402d9201600e0085400d190b80104051004140400000d4005d10326040700d500200581804c0d403121803440c1d0010004a50b80752074041c0d44080803400c491604502442000401007201207100b003140d900512143c41400750304503217070401c1c00303d170804e00b202d11651345c0c114086a1030701ca007407014054284d091090042c1d5001081104010403d92660030441c0140d06241465680c14030885040710f2168000d0021185003e04000c040d0b080130302e00b603040c42030007003002c0c1101c070440c0d1030303202900c0c8079212000c2000c035240184000c4034a03540204080034401c0091150b81c00000b0600c0b5000f580c080100c99040b50700a95900900701a1200b003416048003007920401c00c080840c2c084000d01103d070000c800c45a07090000c4007680c00a20001c0d01495003003005100a4409200620401c0318007000358103450071250101b2000c1200f003002900c51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 717759649 1250 717758399 717758413
    0x121d0f190b071b080c01020d12090b01060806120123090f0105010f090c03020406050f031e0c0d0e0c010c120e060d0e10060302060f1e030c070c0e09060a0c02100e 71
    0xa48840311000c000d003804c1001030050441410020f980c1e8040301d011001480311541c0c0042c1c0e684001e4200d070803490790000c82c2c2e0000f5651000064500d1500740d90343e510822148070070f11400d0005200302c28568898001c0a10203042d40101225407000c003415440c002e01416412140000003401614001d0040054a400b040e160080120840300058031840030140108810805254040c0c2078a5540c3e10b141185566500c91b11a86c0c0d1400300a14032070b0b49042148810014120060009001500c4d50030b041402201c40c0b0301c800d19250080c50407011b0120703114801540c0401d502c0d041c014607800160400d04020343c0c2050000b40c440d044001a04411030301e91070704402c401002d0110420440c2131150070f000c901c3c115400180d86000710084e0010801d0007142c00b101000d440c40307005450040f4410034650340d041c10501c50f0401d9100c50015104281b90290002e00a0882d4050300d00c50b4054601078803842e240c188014000e4040d1a140d40d0071841000e04200382d0760b5061060403080c8015200070a86 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 717760899 1250 717759649 717759683
    0x13030906030203071202091c06020901030609060812090a09060b03010617070c110310060902040e13030806010e010e031f0b0102030a12051e04121d0f190b07 69
    0x108a54005004040c010f0041c00740541c2c1220300c607502c00340001c2015865030f650801007038a41150081d04041c840c009010a004d014075035000301060300d800e80e014400d840d00d84030002d080c0e800520808180742d01400c1c1d00d041146500000c4d01140300001c0001c007111760369805a0068440503000383d82d001e03000100406c121500000c1610001c00e444070f180d4080c1c03400700b42c00b50800800c1440540441d24002d513484c1960340034003180d9010340001008110b40b680340c00c4007000a42180c01214030a0280d48042042035460302040c101c10756140c1da40001c0d60303851030300448044140c40c50041c140800c00030a820155000c0c010507004003181d4102086d0350901d2030703c0005903408a580716065400c00c2080b01c0f0101e9000200c141c0c01842c155000c5881d840e01d80354a00c11036060000c00200d040344609000070003a0780d49100b80d94450a0303603032000c020100031202d01650980b5660540c08070820452000c0d90822145c0403000010400704900c110b40d680c01100420303071000004450036042c40802e208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 717762149 1250 717760899 717760907
    0x60605040b01030501050306061009081f140105031e0102041d0402010f030501080c060f0d02041d06030102040b19140c0a020118030b28090f29070c02010203121303 72
    0x1401c2440d050005515042c040b948800c000b40000d40038540d5908010440344c0104445001400c040e002c5a00c00c007103882d05000030920641c22485018282038503107405513100800309059900050203424641d49101a0304541f10545216000554007480300140c0d00d401a482c6220035a410341110f02549028400104184d0110ba03001050600e000c0051003206000503460040c0c582c20303280103550301c10b81c04c50581c440c02065a07040241d400018007007002d808038620782e01c81d42180d000401407600c4403c201801d03070040e030241940e801010b002c120038411403240702d460001401d060509600c50144241507460b03000c0705201d10180d100e04148400c41d41e020b48107560110820780030440160850380c0c1d032100904068107903428040001031501622103000e841d8020a500700104000074005450b0801e80740442d4001900c01c0249000104035180340d40b4020070f00c4000440c0e03c0d50003a0786004050355000b1030000164118801403108281e14110f00145500404d8211149152503080d494020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 717763399 1250 717762149 717762161
    0x110a0602120a050f130602250302070b09150904020c1e0708070e27300703020a0b10030b010f0509010b070b070e011205040b06010e040603020609090c1606060504 71
    0x10340d070390f8640340811020090842030f4640082001554080026290a001c8040c5c02144886404141c40310001101000f10003d02401d40b80310b50241d8401a41d91101045503004001d51203400021110301c802c0300c260420b005054a56000b000142882e800507102840c00d10785510b203c000308490400303121181002c000c020300400110000f00261410b0060000251102901c6001e442c003003c0c1040381c001042c1c0748069000764001d4100c5007074881500300403034480030b4800b1400302212203002c02343c4000301c0c1d5030448a1076601500103000c40c0e4081d640300000a24010410174441b142100080001407904020034000d190000d20050105d0600013001a03400040e804410303451420080900000c68052150b50302c10301d00c1c10b0801200a0704030069031344807003a01e025036055140100700020044203c81846c0940020383e500705000b4005000c0c0421240103010286d8042c0050080710541c0c500301803800e44c00b0352440c00f0f8a007042603603120124071010140086811544131402486281018460070b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 717764649 1250 717763399 717763411
    0x15190f0c1404050105070b060a0e04200d031e020111040306201e03060a120b16021603110607080406090911040e01181d1605030609030901050a110a060212 68
    0x5075181524200021303205105000300100226649000210503036211f0380000700411030700c0c0c20080207189c28a07003400602402c0505c40c200c00350410000c0605e00308810101c80b19945900c80422408160501600c140f038a92a00342c119903c541c50a483d070420b0a016100a51041e000802c80042500c1074807103540c0d01404106411900307004d12030444880c42d003e039110800304840b50b550394036103601007000d150b00341c0c1011451100b0b10300310782c00300024400203a2042c1d1290355404512041d40000300d884841e50030210751100d4034240c1c14030106822840c106045800180b42d80d2801015035591802d036000f607400040855041e900820582c842c6015611103c0100740005240900344501070000c2041030040c4102c2c22080a19403c171142c840d48075035425244d2100f0203140e80d05802c42580d0f40c60403802807848507c0754043c0052039050020b151800b40000b080511300300f28185004503110327004000c02808220030804011228181840400201401211302680c1c6090170004c0100100000c0c005c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 717765899 1250 717764649 717764687
    0x301181b0f0809062503060b040f0305010b030f1e0a05071d09030715020f1201030c05012a121202030a0c08010b09010207030b0c070203030c010515030f15190f0c 71
    0x200070481d075100004d06007070910700d041d1644200b070005c0b040740102441c0d0810a40228005004203102c10070745150011203100344002d2151740b040c0c000f40350310f9403c503514144e915400b281004400601d0011390b01820940c0a08503420140d00c1e485880c500500d0b58019180070b581021070342c03a80001e62580c02d61060704007000f1490f20303034141d641e544403940c1616050801580400c0074640a0151001c903540c268041c0365225055850b401d00c0803a2070040e10a45012070b05400c4c40c00000c840380800c440420200c0e44030003a0741c110b1074644d0b052052807803506000708021504082c002030300c20710240d03001d21881c50b800202d900a824014140003c1a0490f038008102440390b41542d03a40000c522054030340c020740d5078085072039041c00d07891580940030f0002d526000110b1600c811400552101c0c0c0715030b01c0d60302d12078500f030807030401c2c940c98442c5038014040c950000140034a9048c200001d0642248407511002c2c0c0e585044006602299001200c1009551b00c5842003c8010f40c400741c81e6041c5e41c58011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 717767149 1250 717765899 717765901
    0x42301060903030806091e070f0201051b0f030406021b070e06060423150c03120708130b04030c1a0f0703061d0c040308030903030f13080301181b0f080906 68
    0x3c1c083e00000004100038443c03006180094404032000e450707148500c0f07810704144c206041c186005829000d110560400640c640030000b4801d0241444d0f40b082100340c50080c1c1d01d480030300307081c03441c56510081c8143c07007841d001c0102e0034040d040d50602c2e0078440b001070080c000300c0d03041c0075082440481c00742c16684904414041400a0400b0a4402e1045000c000c60008241c1c10716021528214070301c95000084140800c44c40d1080304040010900707001070160003d61075480900036640341d00705558003032070b80044d0f4210100240c0320100164200e070003810081a010000d82d40c0010250603c491302042c40010340611000b201700e0b14026030080c4c5541420f00100c1e05140e1290204290000f000038090f013941c000c0750756180440d08aa010316007166080c1d54a2078881410742d9282e000b95012080007090f4400a03103043e40707034194400b1260740402c02c940381d41d280c030040760008440f12600c100002e60305c41100c0074200308451a0f000455007622040e48480000201030a6058005c00032062508080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 717768399 1250 717767149 717767153
    0x1006030506090a020c120a02071403010612140a081c0b04090b13030903080a0302040806011a04050607151401080c0303090d020d14060703020304061803210b042301060903 75
    0x441c0c5030780d1003d00d0300340050725521103000081c500720310019400142c1c0030020350407214640c0424403009403503902003820018804041418201d500a1040180e42c68101c0588000501811589408140700504452550202d615020007507444142041017948410458034911600d600501c40300d00000ca40070080c1d4003460f184c1d10b1100200914030b050307000c500e503003502c00c00d130203020000d02441c2c000c820991541c407407020280081d840f50043c221180315182c000100030448043e000046051044070504003880c00c014001075030000c010485015441030161030b00308070944180062080c00304041005540f40030340c007609212035880300c1400307900100306000315603c4031402a140c90341d0640f00740302b51074098240354502d0090366841a0540c0215010f10100395030613005140501d00a502c1004000c001d52401c1515040c8860000c1c00f2803802100307006030307442c0245014900e40f10220701241862418001604890301031503590440340849180d900b800c00310585a80c09810340d8241559003508507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 717769649 1250 717768399 717768409
    0x6180e040c0b0a1b1a010e0702120904020f0d051914010513020f03100e070906200102090a0b0301140402091309031233121514040b1006030506 63
    0xa01411018031400901c103c0c810348500c1008408220310070b60f124a810840c5000d501410a00484a41c00081e01c1c00100721100e46090090154000303030000e000045a40b50f81080c0c6422400585600c15400c0c400409043c0c0054024640d08180c550300040600d0704282d0700314070350468541e01444a00c0c0c0f46450104803000c20400e13040d00c1d0100c552070142d041411062029100313600006110100100c240140105003402400982c5c5c858040c807100c0b580e60802c00c03114480f81d840f0b903a001079401109101c072036140f40444460001c1040c005490201c0c4400440c1030b4464a03803000c07502c0c55001004011166503200c0550078024101c8043d49001d50100005408241c2c180500610660341d641480405006460f018158000c140d41030040900a507000704011482c01000c540390402001008500c0302e420b01e20a081d1109000c0340c5042c90f0365600c41180348880c0f000d80c44d100c01e6940300c644020407030050b940c9100e548a9603003460613150840003404828ae4642c417000c103050400703081c0a900d1743e0b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 717770899 1250 717769649 717769673
    0x30c0703140d020f030103050f06070c031803050f0706110706211e0203010501120603052d03030c0705100b0604120f021003021815092806180e04 64
    0x180340c41c05a145140110304214803407031005001403440080e2600b80114048003170760403640a03609486030450403c3d04141c407a082141c0410000c2d02d0080c1b038000003409123054001c0b8440c0362280300240c07a141ea40e59442d1200b241950059903002c240c081080d10390190566007140303010710141c01040e24041c4040c020889065408940704403480f0796003c00b0f4440e52040944846c9018148002928150540029402806480d00007070304025006843c500c5401003070116944140103104c1d0501c3c2014840303800020108081901d81c05032041c1e0070752002007024500a9200d00ba030f140d501d84030b900e040c600d0512100e880000082c01c108001605654400564040300e0040080701c036100b409107003c41000101120096002c0b450f504034902160b41175014000001a800010041d40c00c08800c120b400e107408092000b10b03a104001d40740b8203051003096000c3c00b039211003045148901440880204011a82001e0001800340b110007074111aa0409840189104c40400f1914181602c1d40309503410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 717772149 1250 717770899 717770903
    0x10c05070918080a09090605040209102109050106080f0d14090f030a0309030201030608010b0a03020f0604080714010f0e030309040b03031309021e0a201c02061b030c07 74
    0xd911884620120070300807410303101661243c04150b45162481c809050a1010300803a85160b14008000c42c85043c47c0c404c03140e40304001040c134074400d80c4004040300d007000c036840c418000300c8800801a100c0480c0d8041e455455100d003001046150801800c40e140804e00ca80c01c003019032011461100c81c5030000c41c1c0e07503801710003030400c0c40d580c1141401103500010115003203074040c418102800b0516a103d08202c0a591003641d06003c01c540d114107860030780349524442603228207c06401c000600d800045903e5800d00a040907042540d00d0031010f081c400b032980024685903c18004810365030303000300605080c2c1c4190400c0c5018810020102e581c030700880c10400d00666a50000d942e050364104262240c0c003071090400191107403101e401030040d412182c040c022482c0742124011411449c0000d80d8005801c9035203941040241c040550703c0740d1540304260005010305154040d145203402001080d030242a001032649003860f1040300c0d08030000c4903900756490000d2003804181c0701424203d07160b141e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 717773399 1250 717772149 717772151
    0x60305011407050f190c020d060c1103130506090a09020f1803060433020417100c08060904060908072d052e050916080a080403020d0303091a15010c050709 68
    0x44100e4101386d03000100c011000c2c0d03101b0711034503c0c1c0040220326000890000080d07600d0315440050610202d07641d00440011080d225181a400e115900b000d0010b42900b9400800440e80d03d995031606400301d0348001e0ba201b02d00d10000491201e0b03820342c030400501c1c644003078005203020715003a11aa006402c101040d0403810054002400440c2100c0b200911800c0e00140c0840d503031039071070302038440307100b08000c0404050040101c003200002d001d01ca83c40f11400d41d40c444001b03554903c400c11890181c0200110740741952005200045a0044090840648542c0c250020010088100c607401c5901c040044402d029101d0700c00005903000c101c0800c00c2040309203c0c180110100003400b640e0118440c51070595140c50300700076420200103002d40040c1032181030760700780c0d640b2001c0d055118090309201604a000400081006041080d55403803040e009207000540c03000903aa403411204500e414030212101b00000b8002c542401d0440942220001d0138110540301030360751801d803146044d200b407003005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 717774649 1250 717773399 717773437
    0x306070302070203030c0115170106030b010509071209081b0303040c0308030915090c04150e060d021318020901082b1709030a080708010303020c22060305011407050f 73
    0x1510200260b9420814400084c02008082380720b1045115a40c4589072446016910799000f03014188034000581350000e898168503800c203c2403040001d40903100c0410003a014101e229480850b02c610142d151003031310300035034542000e06000c0d0390b50304031140410741c2e030010028480003600c11084c20703007120741c00400700340c80341d0310704204e641810094030119103480c8101d810041d2904000c070351540d07002802c5404000c400042031101c0340d81a213034010181c0800008001c96910300d04400b10118407840201080700b81207a0380c5185064489503502c06403c8140b4800c1c1e0011480e10110b40c07030140140700300070a80d0304125030400349030340304500300d0000c00003112040c40f54440c030a110b4200c041c0c1002811504c14140801007990303d0780007008200004000d0380225142d24410320f45141242d8150b4020320340b00b141d0804210038440410036035030b501c0700640150100209203000e004010340c02640001848022a540c02c01c520b50000c2074001000f0f0204810440443e1080a607011080380050030510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 717775899 1250 717774649 717774653
    0x312090f10052d0d0509011a030717120a0e040c031e021b071206050f0705070605180610060207152316060507020c09160e0609040e0a03090f05030607030207 69
    0x3503c244803400072401c80d00042c10804d481c8071904500e000b8038080000b04410710340d407503d6400c1d01403615002a0305400040040080300100520760f491311a05070305440c403e40400c44c5081c8154403030041c100c04648000702b002501e1820340324901507424241414011128019011041042400c102100c000d50101368800d070800751030304643d16450a0000c540ca01e1f91074040010001d800841c084510300d00b000f000548114a140441d03014a00580f6854105200d560303c0ca0050007006013440040b00211079402e800013810040d15011302213040e16001d060741088002170408000c0d4000710000500c036000d02003d580e00480c80c2c50305010008081850f05c4181944c5061446200c3d04d80040070301984200c42404007070340c8a50f000f0301254003110019220798081c441860b00032110603807012601285415540e004c1c41801c0c00c0400300808051800c141e240c0084c007114910f00390700b6a0382d440314603a00101908914503801405150401c0001507213440d0010742c0c0c49100030007400416802113400c01c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 717777149 1250 717775899 717775957
    0xa020102040e0901061e0e040821010b040915150c030912030315050d2a08160314030f0f0706020f12090601060f08041b050312090f1005 60
    0xd844040d42c03800b45400c0c01e071012800f0307001c0750180464018000200000143e5010302d020110f80c2c0b03a900c1c144042d0f5550312a009190402e42200c0c918400d80d9a0b220a03003001304034044c0c0a068400141c0c2c0d165400c005403a01201d41180e0015100ca03d045000c2c0701581c100040e50600406e00e1800118451a038901116801c020f0b0b40035085c090040c001300402c01d1b4040c2c02400d0202000e56030345100950703c03030030071a9246020f20003820001c050805180b68401c1051100b503034100d8441010600c0e0f50700c0700c0040c60304010217031907180c802e6045001d2003009900060352301d1800c441401141441c040030003201140c8035080401e5405400003c0140030400741d90140e944400f07031060001d03298500d90925000d807842c111000c0c240782c085d0b1800030030f000d400303200b070b15020110581c2c8401042c0c0d621354440b1202e032100b0714001c0f80c8100b0424006441c0c0c1c2e04214001414010500090315581505c0c24071a003400b00907610352244000304020045150300005545c0b940b100d11090001030000ca1400300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 717778399 1250 717777149 717777157
    0x11030415180f1515121704030b06041d030c01050f0907030b0711070b0c0f070504050c0706020c10150608090715080a0941070b0f160c060e090705030106050a020102 72
    0x9950703260810300298001c0001d818403d81e502908990008806c003010800242c45a0f000091840c903655003c541582499880103100c411024406418611304501c1245150400040180140c0d101d400704103d100a0181c496000305e511001421010304580e02c03070aa02c080101040204401100303096200d8204000d114001e0015074106036840c0321500060740c68594143e051a02440740000c00a0385042c50311034184036001600340341d82814003c2d542c10010b0b41c001d0011103039034801c3c40700c8000540d40c0ba200c3da0075074401c85400540030f42e1600c1d1010340312400080c000c2849410100d810000e9844241c00a4080c04283c541240c03d40e40c0e0070100c1005100710580606030350490501c011110300360300c40c140940032214203403900c1e4490343d800304804614141540743c5a90000c4d8000c10204003520060540042424095820800e2404c200308848094600c1074480f0054003004212060700151594a010f4082c0d8801aa903d0301c00009000c910041c0300f00010090000303480c020f418403c3d8159 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 717779649 1250 717778399 717778421
    0x81902090406140424120f0203030d150e06030604061d0a0c090b040204030203070b070206040e0405030904060806060a03120905190e0610020706050d11030415180f15 73
    0x42021a48500e040a04100c00200c1980207900d0801c40311085070082d8580d941751440c15000c20710017418085401d0205c848400200c92013480703403a030200142d5051002e881e0504052100044001948020444a84403035000031a0041501c0c103100c05528086140d40d4460740000b40450b660303140c45a0b1501076110b03038090700307842d003d50b1440c1c80400401d50810b508407103002c40184450200f40b02008128462407000035410352107108104020305a00000d8240c0314001024641000d5440d00d403103c0914088030b00304c865030030004080f040d901c1c05104a10140030a4030040480d883c040f00803812081c6940000b038909030041540c410907038803500151000d02400b4040d101041040084032030f49583c17a000e4007001c00034000c0020281d0030301d5028050243c00c10360040030030700d2802e04190751a41c4440300301c030708464503600440d00302c0c074105005501481c8100c0034400d40e64221020002155824002079040313400c2901410301080c08049070003001a00a480740640e9120a814080282401100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 717780899 1250 717779649 717779651
    0x6090f05040c290f070f03021f0e060103060c170901020d050106030b1c0602040b181e010207140a0b071a061c021e09010e01081002030c1b0c0a080a02130603030819020904 75
    0x10142010390100b40d0000450b04118a548280d101d82741200a5882502403c00789502040040022502c0da4210094554030380c00e0180461300f583c40000c9000d44110740000d1260340018a440640005102e240c0c0102507070b1604000441c284030001d0911f20803500c8050040c0d4120303a10070180011035040307800506a081001d60303580044001c0a0440104071001031142101d0542c1e0030001c1645400e200640c003051b4040d0860a00703240c0e1f00601c921016403026040203001c00080b5201900400410650f400342c460400c8090031441c0849600c80b00810080c06090081000c2d048000c2a88500c110254105e03000c2d04080e042c0c0e03903900100c1c1f54803061983c1c004850000051054503004200d41611024001d449185541c040b042c001d80c401641e80f08901031003041101c0a40d401000d0220300d5846400a4a00340d15100c000a880c03080150000300094112820701070071450040b2804802052201040c00010716549020384090401442e8400b5085460400100d07034004d541166032414000300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 717782149 1250 717780899 717780923
    0x1e0912060f0106051e070311071806080304120f03022112060d030e0f13050408120109051509040f15020910020f0c1012060303090311060c0703110406090f05040c290f07 74
    0x801c1c416541030400780c02b440516007280890589404000c4400703850510b0224000c0217500d41d544180501d11540560450188080f410040c040081c2c5254054a52046064881c518904241d40142c0080c00c160711034400c0c1c0c861100000d130000052154120100e5031146040511004141c0d55642c8151101242c2c1c5482c007000b08100866018205002281e28040d14a0380c8560049049900664800c4500310010025101501c0c0154200d5806440340e414480c08944990744c0d41412550081840c49003a004184685c103410143c020004407000c610061500001c0180417274cc580c008102e00c0e074000e04000880840701805045503440240c41d44404000190b9241002420b08550740000c0f10300e2215990b1780d420074580398041d07518440d4803501030907200d451b594800001c25210030031507030003507103601001480450764410b80050100e40300001c200f51805291980545500c0c3d0802c0480f180c04541c010034282c2882103691415030803c50095559042d00c141c2c0f1020b0088503801040c42e041c1c50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 717783399 1250 717782149 717782159
    0x15050c041a12011d06090a0b0301150509070c081c061d160822020f030312010f0501050304080d0b0a030c090209090c0a02031e0912060f0106051e07031107 68
    0x2034020401078090254181c2d00d070742c0f50f00b00c01510300c126008070000b1442500204040d0b28018080903080803401d04001603248030340d0b0129003903450f8203032400c04d0031180c44c000b003040f4100765a031340b0fa00846600e40b5041c1c8603010359500405000341d103400c0b810018100400c6070004042d41c004006030501208002280010122503000c2c500101e030421008c8540341905072a050043c180103026902c503040d618400e03401d641070031040a03441c0000740d0b884200c0030390403200398030148001c1500905401c08040c10b917040a026030103100340c55002c0c3d81007103420010080460304443c26a114121507078000b040c0d00c02d055000500708030b030315000034051900360b49000a00c000c00f90f000b04440701e01502c03099096564800d111b00c684c040d800c045001f6800c204003290411544440480001112810180c01c001e0864046010ba444401607403140e98028002e019105100918150040c625440c1031854103482d40f4a0b036100181c14143c1072064100401c50a00700760040c400c400c24082d0000c01c680300c3d69520 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 717784649 1250 717783399 717783449
    0x50c101a1201020913151d04060c0914011b140c0901080d080f040804091508100603110402070204110f09090a0b0d0f03020a0b0f1f0806060625030206070306090915050c04 75
    0x8d4604070703940c0c0e00d0324480d00d50481c003d00c1e6010495a086e01d005902c001100c00644005000c884014140a0201040800a1465035441b00d02d91443c3d00103018060400c41400210001078014402039402240210f41d100d512035019680002010506c0d0381d140c42da454001458021a00301181c0b1314204000e100003510400d018508642103442101c105040d4404900c0898000d800040c080c0701420007001440d08080d0010700500d44050700c0068202d00c11540045103800456140000c071900041c0d400c0741d490408403054120184240c10404040da0100080c0b1031551010001c050549441040041c1802409024803140d003110354030100d4a410807284a00110840c1e4400c5d00c58400c61880d03501603071644540c4152090031b00202203075116801003000c0c607005180000d4021680410510108080300e245460741442034009002074140088081d09462041c0c2109074840d20703042d1520082204414440c1c91500c00c05400203139500c0d207005841d0640304503004013180c03001842c509409130460f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 717785899 1250 717784649 717784651
    0xa021e090424090207170c01151d1b0f0f0c060123090613090506010512030403031205062b06110a120c02010e0d120e031207050c101a1201020913151d 66
    0xc00e420030400760350ac031004030201c0c002c4103070901100c0c014200014013070840741d074501d00c90a4880814a04068440503401400c0d030150080c2e0400140120f458041450104003803405130865141c034000c00c281c041c500c2d847e041c20141910344650045000f00715103440701e51521039100c2c0d01820a01c06203815003403080ea520000e20330709029042c025101000e01802006841c10b4a40c1a036410340c00c0b44283c0c5044000c1d02000e02090b5100062031394014180100005503650050203420328501c101c643d00b424021140700e003940a201880800069a019038480e1014040c500e1a810008480c0840d0408030300400011042017228451059050303a065000000d000d03241c03802410078800c01c50411801503c0740502000c40542103c900080356031a0300440250210940c820125020b040169403c4401d4030002c0706551980c00554040031824286000c0c1303440740000c08070003545004a11008038081d4400c542541c0d500310354a04201c255203600400481c002c00050710341b109210000e401000003658 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 717787149 1250 717785899 717785921
    0x10c0c090c090506250c050405160e03010603020904060c090509010902120c0a0806010c080c0102031006031a0f01110f0a1b060c0503040303080a021e090424090207170c01 75
    0x101d0028006407900e0003c04455100c8a04603e80740004200720001c140210058411146e200400001181607241c0707103d01c901c074800e000004c05c81050025006010a100c001d034050207079041a6007480542c41d1407000c281c016511060024100015800450b07001c0a15017200ba80b04c2c81640000032010b0300c5802504c84001d5200342e415058442c040049818450045070b8030106d01d0000001d241980110000c000700307400b40c6817207450b00030000d00203801ca074011280950302581e003140602607542d05206024084400011440354080c44400082c003100c0c0f9006c006041150481c40d02151900900c86c0502040c070b85000c8410038003281c90051140001c020310800c81c84501400040c415215540c03441c10203030060065450641103072000c42e40c41c1c0000303090040140d000c118188030409000d1000c1000c0075180019500c1d246004104400c2d00c800d904549056018200c0d440b01071541907070050100e8001e40c3c1c1c01030b519012840c00d9551480c0e15810030884d4407000c07580d074080c11019044960340348 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 717788399 1250 717787149 717787157
    0x14160507060f090f030609020d08070627030e040509010e100504112b020607020d0b090709020c1b010908060c0408010612030813020f1003090c090c05070809010c0c090c 74
    0x200d070040c01100e403603c1500c1580c60100982d801000401c04c59807183ca140380c00907050513002c8050b40c89045403030740013940440720a0743e00d0001d4040c001740e108440c4d400b441e80c00840898011141c03402050410f1038410341c0d1107103a541c0003041004034250f01c00c52000d4034040943d101c845007000e10b90001c0808440549150200540760300c400c0c6400c460460792039075001d03030403000300e100c811140c440400034501c12a0042020008170015030f55000d4081c0040f4419881c0e1400351070303c19002030809a040e4800000700b40144100003003050040b50341d074601c2401132031041e4074100b0b41c401250982c8082d8003d00c0c69004100602984c03400600040c025185008002d21440d90348100b1240c11340c000d100c01400140e482c00110300d600c100d8411610540d4001015140d443d40003c002624460090341d1500100396900c2c0b0071f10400000f251183c00078040036004111004c0c41004c058910310920324018240342c000104800943e0281401400540c2c0010384046c403291607040c0d01d801002078204a802203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 717789649 1250 717788399 717788417
    0x206130f14211218030f07030c0b0405100b03010516050d060e0708090f0604080a03050405010621030e090601020601030201110f06130201021507050d0c020c1f080705040b0a1416050706 81
    0x94010302003c0d4401c025800542c46d100320101d103803903680c000d80b4040302042807a102c450040740840003200c0c040d0f4020000707081c0c0e0110541d5100c00b00e640126441e4041c3e410803041011203210b1448003800c40d1118103000380c0c4e484c0404200002841d103504020003010340c03041400349444d48003071124440c0d54503008403400000280d103c20340d00c01c0d0071100106224001c00c0005882403007908140c1d00284101d001040e110384030f0b410084820312441404890351014004001032551003900e020103035006590703081c1d0750b040200000352911b50501010f410701400108102d0340c0007080000644103e40d6200381d41081c02c2280d440b84c18a8248081a40180308191800740d0942d04072000601a00107901d40720700c4c102c070040e03032400a8500400041c05502500081d8012500c40f0309240b08a81c80d515001801c6031041c00010f01000c5000d005241005420300082c4543c00e40c090844041c06142e003004001d28a29090000041c0b0135814015260140c51050b54104400001c0c414162141c03600c0304020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 717790899 1250 717789649 717789661
    0xe060f0601020d2d0c0501060b03070e0a0528030507150908010507020607031e06090603020907090806071d031606030501050415140a030818010206130f142112 70
    0x2000c081080f4008550f013800384000484021555103ea80300390500b0200c2900c0c51541702d850840b0019800444809000401c005840e43d0040e18400040c200700d48000c0618100400b04d036200082c0c003002c00c4000703965007216441c1954141084019903000040300d10240c1c903401d002030f0890742e040b1750b800450700e000b0001c188001c06010b014400c3d0703026801031596135030f40e990490103803914400c80c0c110001c0c101d04c0881845454000c2401030000b81c00d02150842c0355105004450718005c0c0035000b00002404107001c40341c00451109e410541e40d20f002800203000d8078030306372248a05502198144944881100b0981428101c48100d4003ea1002c010303503a42c40081c0000d031649100000c4406608030310a002074450b0b202208001000a060754151a84a640300740350ba5001e610740031041164480404001d60b030401503d517108148481c032881d5505160340c2c41c050300962290080801001a081e840c0c2100300300961890320f001c100301400b00d515040f07480030f815440400448099a000000584 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 717792149 1250 717790899 717790907
    0x1220010f050a052a130e0411060a050d0b06091201050a06170c01051c02070503040f05032a0f04050a020409050c030106020307120c080403062405090106050a030e060f0601020d 77
    0x8460800414a000d44d06840e10b2951001c00e10401506400d110038001c41c00030780c01c406000c802501c0c4096044c1302c2d03424a414081d81010703800d184580b20350010403c0c03100c5540c1c41000d075445940310041c0480c90381900c0c1c000955500403031000c0b0b504120714034212005a036054000d64003801d015502040f281b502c1d1103c1e5a014000381000c01c03aa80d10104c075100865128100600340380d048011071352440202d4054070000d0303038000c01003503829500116003445180c05040f03a90700100030441c000e2400d801040c4c8405541061812003404803003a14040c03003026110040142d81d81c00004000300000e01c0c1c81111500290094060401901d141c400014105c1885000300ca0681700c1980046041884503034440a0200400140310304114200080740700240040c809003001c0d41c0b140c140804c1c00b004080f0120000c9207070401400c0e5181001a00b002292a0880d520381950700078a04035030b0340c040d907941c02d8010342408841e50f02c2d40d105000400c004100f9684a041c01171009a0a0380e05a01545e1001c407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 717793399 1250 717792149 717792151
    0x230105040203030f0c15130201120507020601211a240d0f1a010b0d0e0309010e01180b0304380601030c0c120207090513030c1220010f050a05 62
    0x303405520400c400d00d5100c10410140944411140031900720106c086a4141d03013000681d00070003040d4017400008215a00310351310100d0925410410021403400480095030307040c06124090060448001000c48072100848000305a500080359060b25004030005840b8610f04480b4030740c200044a00701d00400c402c1c12580c1a55040c010416507049805455070044070442103811503141c110984c807018134825283c5058002d01c000d14035552038040c01e984e00d1003030300c450040c40302042c1c1040082644603038000200901008003881d001d04032080825003804100015040034103200f4011041000b00420015001480c001c210b50f44c12298800f20313040388820350000c481e03409460061001411749d5100c1c2e403110f00903c400d46880049044243c6a441900e55420688401a0403103030341130000c00000e025041d00148200110504903409032001041c80401c54002810316600e140401281d6100b074003401c4c0e00032680b011b03000c0e0781d8101a074590700801203a48000c2c400c2e0f003002c000880d042c203107101d19 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 717794649 1250 717793399 717793403
    0x7060c080702091812070201030c09030305030f1918060b0102010510090f0917120c030105060a0318080f030f0f0c0f0a0210020a0908060a050103030f11030d0923010504 74
    0xd41080410360030403c80e810001c00300301d42c0803400c084480500104109a02055507000310340b0f60b42d03624a000040c244c621562001e0280490110200002a031050480354800d4000d0214605505c4040c040c8403044412401514100e0500390010502225648006145c0380b041004000b094582c000681c00e94030102c84404003194112800c12903422260010720304058201c42c00101213040345d691511100031000c01d411a8503000c10240b900f803000003005504101149802c600755850200019800e1040a42d13075010541c443c1c03807030150b0a0351400c001403100e0340039450940b141c4d0b0080c5205a1900101c4501049a02c05004500c3c0c21890000e4607010f010100460b40c580b1940714038046c07036076000340c2a56046100d00000131808405a2006e84420502540d41c0c2411920740070049140c20710240c00c202103c8e181800410019400440c0031a00c07804c00d003000904440c0002d41070341507010701207c903c10f00382401c1c0020104034200d1103507103200707002407851b28007009003001071801c9650490f80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 717795899 1250 717794649 717794663
    0x201060f050a061809060e0a05060a031e0201111014070e010e0103020f1303050d03060801181103031201080616031e11090a0b07120f0c0305030403050c01051807060c 73
    0x403d02034248101c5200540911035030038250415035600c501c0003100c020350300640050b82042c0c240001b01c2c1c000e00880d6041442110b04000050641c0c41d03d840c420107203419502c0750307104159624116401010441c2c070706620760b4143e42c00f1900790400740019185401f0007074001c1c6111800550218020340600c14081010b949034107c00441d040150000d42c051110544184800e0040c000b03844140340c07003171015500c914007a21341c0131103020026040e12207a410900699041c01c861121802011415600784e0f40c0010b80c4003d02099500480e08510680007000c228281c0040085119100000d030980100040444c03682c10759102102282199a0481e14105080e000412820501e1494001d80c401c1c0d015605120b1820360000700041c2400159841a02070b1140420800e06000c0840144120444c071810b00c00c0500100c2e01d80180342c0300e610396004090007000320208050500c01d90503210821882e400810050030511341110031101400c001c1e11144c4a840004500765100d050440105640410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 717797149 1250 717795899 717795919
    0x3010603090305040509090f060c09060d0f0e16150e0102030a0831060501051c0609050312040f020a050303181e0303070804060305090303060108060d02030a1b060201060f05 76
    0x4044025001d141d80642c00c0250a0101141075914020310b0b070b024040003070045c0004540a05501c1c10400010800d08603e1010700040a190f1141c10850f00c00790082d000025440300102144801400d00140080c0c131b5110f000d5070843c0c0d4441000d032403416552141541c00c000ca81410080311420459845c2d940142c2090181401c090b0103071703541c290081e074a0481c98078402d507085400500c14040405100b0008441106101846068810240036150640b200261400700fa200310743c0f11180040d00410055441c1d0b110414804280252070b011500f806400304641064204180c6130140340d88107a04c220000c40c030002c1c8520700001150324215800ba41c145440c5c0b10074041045c21450503110740c01e1030040500740c2c455a5010300040522170700c40c000d420f488605241c1e0050481c0c800070004101c644c81081809000da820507000c0d58403200440d01504080b40d24808281002400c100081407a403514a56051009035411488180c170080d500030000241c0c4d45030350415072131a0703200707444e00500c00d09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 717798399 1250 717797149 717797159
    0xc08010f091a04030314100e150604030213110315010e0d050c19050306010b1312050606060f090d12181203080c0403051005010302130c140912031605011409030301 72
    0x9000c2c994410300a0a0002d0700d01d1090035400c0d10400101c5a281c5014001001403110040481c440d0b03401c0011071102d00407031034510b804a480c81c46103010291040c01c1e10001002c0090003600194040b0f507055140540b0307402d10f080389400080140d000305020602201c240726081c244804001c903600d070130800800b0798128040c14001000300c20000c1000d00c0c4c080d0100420030f43c4042001c03e00030810441c205036222002d40038550b21007034940044008904d440380c01000300b480020155008102201c85550f2003400c1c03040203049100301e02e40719403c01c12000e02d038814056038015100c10100152924183da420a002e10807156440b4042c2014500314940383d00d012900c9004500e44c89803021028603c1c00e40c80b45c0300d0701d00d0b01c000206034000058643d0010320840c28280c0c0d0040307648182010078080250f40c48005070441240000040d071080307011403008070b213590742012b801d4103420180989a542e000c034442400e0a820380141170355203608202d00340083c080341c60440e5104018807001746040d81d00f40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 717799649 1250 717798399 717798443
    0x40f06020903010f1e06120b010e07090810060302031608120a1106091b150d0b19030320070b04030602031e09160611120f070f0c08010f09 61
    0x1d0000e40d400d903588001c0300d2805440b0344550382c0b00d84c3c0195420f04640c005085150180c0314580c100c0c1d810051480641c80018100250311ba040d1a4445505441c5d507845e0300003120b04154607402501184502190940c0800140c2e121070140c034021383c00d49803200704000700c01c1c150009510440c2071a80c00614200d20201070700c07000d0400100303507140054140050143c036618040081d241d0040c1900321400300140311010280006c040801500c107080880d007070401007842030048115181c0c0141d11480e680e54107135108140c0c118480c0341c203001d408503035842c0d043c0106005c12000b803110900300d800b0340504201d00e001560f10b081306e900101d01864903046a940002a41000d00b40b41a10f11000d00d20307071040d10602d0040d5209070741c000c008104a100c0c41d11240120000c82d40110b0a0040c000003c1200d0740700030445465240c2c0054103c0c1c2e503007418070341854070b034421950054014110b02c0100e0081180e000041c90031140310f00f0080c481e4800c0d0000b003004482c14850000c002076450050607805142e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 717800899 1250 717799649 717799657
    0x70507020415052107092a0e0907090e01240f050d18030810081213182009030c0114070218060a0603060317030c0d020a050406090e040f0602 62
    0x6158000d41c1c10f569040410354010354183d00c400005004a00b1105480c4100140d0000307001e40c8409010300302182d86103201c9404400c4140c1c061600142070382035814019440c022424201900f80881071924410040042036203000e9007410396900340000607108135403a0129422290345801c0d145401e2492010350b41c0340c80200420341400400d01181e07001900d40c8c49040b80d5120780803c1c50011022503c1c0c0100104801020300b8000005602d00303003d0070400160419842d00c1001e07605907070b040e00c101031070502c2c0880d03071206e405441ca00c407040608800c0754008542d1088040780103007948004210600701c900540c00c20b0394050340243e002d038049600c076041a008991221018925140258004c41d40e05100003140381c80381c40b20001401624200884081c2c020101403508204003070655454074444000b2a40c04080c0c03401c0400820300c3c3c850620102c55284403402c5003150f0b240b805403c068000d4020384902c0d004500298000940c6e03140c80302241d40304a602c0912a542050b41e940ca550080d08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 717802149 1250 717800899 717800921
    0x1e0516020a0507090c2105010317120a0e0115140a06080c030c031b0a02210708041404060f0f1a09010e041a04090f02100306081e160308210705070204 66
    0x5406e14140c049500503400482207401da44801044070343c11800c00604c503c103002e00b40c03001c9450070822090004a038505294100c4103032400407a03074040103488140545501c075400c8d080f805070380f5000101c02041031100f64200307100303880c1c0840290741ca200650b40c0e4002115a56502d01c0b0030400925038104942c02075901170b00c4076812200b88000080c2180302500030b0f081c046e0159103c080e030b410414228040725074419200034105031030324591703540352a114002c1e442030b043c480003a09555103181e03031107401000181800c00300360509180d803003040c03c410660724070400c0c07049007034810a0050503020750100c0e04100c1040c2c40d0348180100340014000240807c60040301c8160702d881d5184800c0c3e6481c0a1421801d004d44101c10701c40c2c586004125800e82c600c820b010a05181c54020801d035600403501c40080b2516000c01034600d03c1647d13509080110100755007041030031000003c0104400b840181c4404041c0d041e1014611b1046a00e1030002030080e06c101010400a00420380145025000511411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 717803399 1250 717802149 717802157
    0x20d021803010209030a0b100b0408010b03012a031829090106050a1205011d1e0a17252009040302210d060303050a18050a1502011e0516020a0507090c 66
    0x41c1d0349c1a41d00b1050300160031251a0365119660390129290900444ac2d20240302070000142c45484010b0700c0301b2003140e8003400141511010b00c7c1511030550741c8001d846540110005070b4880c0f8008030280b04100c080e0b00903071880c2020f80880d0f00c00754144074410070f865001e0710080302070b810603105116541240404450540d00c86070111803a0341074100050307210030322000a082c000d5140d20a0b8948050840400c01c107030303005019407408030340c185491034a00380d580e03202240e41b04041c04500c000348908000c1703101012081d44a040c1001401d05160302d14089030414440d1407a1540100503c1000603a0040c0050f44038580003070041d50070f0403945100d83c5802032640e14100c0b41340d40410944179103600a902284000c60340d00c032026000300f50304001c030801c2c200300500542001e0026216035100e020b0480c8428401d031801008034003d6000004c00d69500421814051001b031760300001c1c0c05d0844800c03100d440030700f0404000b1400010303c0700c2d802c3d5004e005401d0840c1403000d500014852106108204 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 717804649 1250 717803399 717803431
    0x2030d09051c11030f01050717090304060e0105121f0b0723010905250e010e070c02060403080714010b060903031b0703080a09030b0c03090d031e020d021803010209030a0b 75
    0x256005c01080810301041400480e1303a140c00e41c2c01030103940c80c0c00d1611225000400800842c0341010040b201540d045085c01d07680391a2450048400b40508a00c100d0501543c2040c403994580080c40c0b244035107000c0c0c01206d0f900b521000511201c0c003640c18014220201d40000040d00c01c05004001c48000b044000007503414100d440d41440c100e40d00040740c0300d86103c5000401658a480d0311540a4154a00403102d01c1d4501800042c0040c1c000304068100329a135a480c10441d40e1f01c0e0203c600464004605036120649814042c072a401000c8451031198a004032440e040c1c2007007001d490040d03900801444c10000c035524400300e01404051682c001c0c0c02101000301c000b800041c05440308003a103681d0104013604624000310b1041c400380155604060500801c807600780e00003141c656070b1015290228040c14115004c030981c40494611184190000c94140000380c025806803c408008400341540c0c000c05005050803446055100750309504040c0001020030201c2c41d956800045000b071300001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 717805755 1106 717804649 717804683
    0x151b160819020d060528271b0815090a111306090c11060a060b0712090b13060e090907150306031e02030d09051c 50
    0x80c0d1200304039a000b10f446401d01e401e10b10f40d01c400140f0040c00c16520300c6034281003210140c1c41d54072103c942c0d084100110b000360603c0c2440c02e18034161843d0442000000c000d0b05160607696500d02d440318078403845002a00030020300c00000a07000b11b81501949aa4040001d00000708582c07120002c4408126103001540d0105001c8840c0c0150710110b04201c40076248a60090600360310b050780c400c900503044000e50540d20400c00503103085580340c90940003122824007485001440034414140000d0401d581208107182e6804c104000340d0365012200b00c3c41c2c0c04281c41c1100c500c0e0030300c401c10503160018001c0b07032252002c0b00d0312101d52800d12591a50303907205200b18070202e5601034120f0b00d498021351200700555045a0240361030144480a620070060404040707000740b0030651400c0e842803142180f04d05450009081c50750144403614070403000c40301804252151421301e100060 = true := by decide +kernel

theorem cover : BRFrame.Cov 717625899 717805755 := by
  have h0 := BRFrame.cov_init 717625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 717625899 ≤ n) (h2 : n < 717805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
