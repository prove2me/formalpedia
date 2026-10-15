-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4894
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:04:42.274131+00:00
-- url     : https://prove2.me/submissions/a51abafb-e823-4ddd-9d18-10e1fbb7ddce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 880035971 ≤ n < 880215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 880037221 1250 880035971 880036007
    0x40501030f11010e19050307090c1d310c020d0509010e0409050d0c0c12200f040204080106050102070519060c031b11031902011407030311070b01051c02030706 70
    0x6694141075542d070019100c51814045c10003082800e182c145800c0032541d40c0403207070007820300c0c905440179504a44001060405581442c08a50001000a2035200030b411407402001c400b000400c031241070711010150501a0010910800324404412a5105002d07220b9400045082c80050344942c40380a0540502000800c0401c10580300d0f11020b0078220052081d0780451124001d1a003040725600c4004020300d12502103045085070380d1551501c0000700b000c014540355825002134581c0d80c43e00e0000c400254060300443d121601e03440203030300038003203802900d01611814100080e5841c00d49504416103840d6102c10301441c3c9404015100240106411814090360940380d242141d0030442440383c0718018010202c1d04a54402450700b44180400c0c0c44016a9840c001030000d0303608204a0700302000c0c1003034295035520140c1011001003a000b4103203c5417210001c0c0c0101485401c031921816070b402145d108440481c1c0c0440f00d034455143c01c000039003681103c142004410300824401c02c100351074030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 880038471 1250 880037221 880037237
    0x51b03040513091a0603060c3702010e031c02090a031a040c32120703050307030e090f2a0703020610050102010606080a050c0c120315040501030f1101 66
    0x400041d400018a9020700b0760140e40340c1c0c8032010f11001c10500c030743c18042000302c1d0206060000c007103500c0f00c80050510b05910000214040e080c4136442c0e070715400743e02d07048010b00741501c070302c000d014070503503100260340190308000c0341a6485001000f158200c500c0e5011000f07203c10440a500040d40042401c00d60081e1402030001c0030071041e0048a0070a50b800345414010703c0c052510405512690300404002e62500c2c1843d01d10035030100c0d05218603440b02c03400e88505d0304040002004800701c009451194090703484000308008000028014091090b01e480c448c3c010004188014031000300d841c04404080c040105100c03a05095001403d5641178061840321a82800c4c1d81c1200d0b406805c00f100103900c42030401905407004101c110140c00248000d0200700e1500f107004100d10001b07019000d4465541e80413800d08401003045034490801c034400c0c0c0b505070801080301c1c046034104407910310a41d99a8241241c4c0d914003849801e0590b070340404100101c281c81e4440141d00860007028505002d450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 880039721 1250 880038471 880038479
    0x6050f0337060e012301030905011d03030a0b0904051c0332070206090330010b04080f030f030408070303381e1c060203070c12090303051b0304 63
    0xd4095414040421040454100e1400d03108541c15601688400300031001c080d1840a017200c0111362000c40b5900f440e010524151604080d0300620035110102c403c0c149044e10181c11800c044003861044120508c10841150903a052008905080f074001b0410b41080d046204400007480300d900f00d003803552500040030240d4031401451540320300800a08203440300729001c0c04d0029010156448405407010340600e00384142c4082c1d8038010600b072107403c404c01ca145480d00d4200c000602e58103021075502003449507540c0d185410150721602861085008842c100180118001308803200c45c1074040c01280345550355211164503403c81d43c8210105621007501b500092800c40803100f0b8015400101c00c6180901d003004a08082021005400386001c848046201140032021090403003040c1d031000c001445409600c1d805d01c50b006001010244040306004141d5071240d00c8001c894400d6005011915444005a4040040d880002c0000c0c8041150540c4078a5280e50440700c032600c642100e04150711 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 880040971 1250 880039721 880039801
    0xb0c010e0d031a150412080c06072d050406030506060c0a0b07270605160b070206060f030313091509060312091a04050607231606050f03 60
    0x1a94010800083d11110100c0b0341d8546403d4a024625003195103e5100b10034107007018150060340300711015801c00d01c040d0420300615008650f01c3c9200d003416600d8500d010f40010b0302c1a0000c008070025107141a10700c8140c42160704102c0d940d290a620313a14103041c43c02c074048010b058001d1046810003820701c005802031200300420070040740f283d0f0140d100e515040100910300e0b0358041000b600d034016081c40c1070103442c11040440540314a49840f6aa0710b82010310441e52880550005107900e9408080140055020034a140030304402c4814486454180b010036660b4011054215000300c4000001c0210313000580c048a009010142100401079807400710004036107035a84152032401d85501044246a80b004814003d0180001c1d801407584c10b01e02c011100c2d0066018560151000003011001d2080424068101d80340e07010744d1100020303401400544034000342248010659540c403002ca1007034044d0b03050f00c503016038190042d8210380d9200c4204490340380003c0f41503440c0607050401454400707 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 880042221 1250 880040971 880040983
    0x21050a02060a0b1f030903112a0a050d06020a08060d1a04140708030c10060317090105070804061d1c0308041b060914010e090123130f0e0d090b0c010e 66
    0x1140b85c40c00034040c0d00034100a403601c451648d23020001c2d080980a484191504411248000e0788401401c4010050344042241a15250005684003404022800410155400802c08051203564040382600c4000900020600c07010000300360412015400095541e00c44619038410f02030458100b1864528421505150301c50300b15100c079402c00642001c8010781005910880321007800100076491a68407989920080c00d0840e000d40300000504130516803141c41594a4140c220480981d00d99a569002d0b2902460300b021803032030b17181549440601e280090310040c04001c00c41c00311400c4000707658110340c0780c180184111580c0329248180880300c403035003803044007038082c03900e68859050600d4601780014200c41902d03410001c0c660451209911034030f08650445000c031445940b42603040328240e10740c110b080346442c0c012c40882003032401c290468100224640c2c4940081207030f0342c021503103c0e03122030713084e0400703004604508000c100e084c032038170002d00a00041c03030000038591807201c280c242089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 880043471 1250 880042221 880042279
    0x62a0b07050a0201050612060417220302190b030a180c120302060a050c120613050702071d0402060f0a09090507021c03020903070b0901031821050a02060a0b 69
    0x903001081204502d5024400d01d40c00400c121895021540c0714100103a542c81c0051006101d120700c28035101401c406542034440034448201c1c0c0c0c039548e040c1d00c0c940485401c410712042c4e2040154184a243d03c202900440f01a118010402d40c03459507600c1c900c40c007a01c2d204100014500c40b21102e200420140c1c2d182001420b884880c00d40d160740c05040c000d2410034081c00c8902c00d60b18210034841440c801d00f00322180720411a400e101c0c2503840c80002100d02c1c0da1202e000c1005402e00c0b08101c01d1643c045440c005a410034281440081c80840355400c1d50001200c0094000310300300001d81243c80e18030080c0441e0a498030745024020380398440007094810031740320080540d000d5500c00041e108008014810300c1281e00d0304500f01041200017036030303e0045204180508e4070010398031303607564841d0300100511134805100b40c03a06149844e0a40c19503d100c2005070200b004000100c40752840344048803c4c000b41c0c0d03401411a5212034546900504040407a030b5440148203000e2100c00c140002995811 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 880044721 1250 880043471 880043477
    0xa09180804080610081c03110c030d1b11060a0506060405100201090b0c07030f080406150b0918060a030b10090c020d08100605070b04080c030f0414010306062a0b07 72
    0x5818a413010700f0100e0300c190026821500400c01501203504280030001c403400041c034011401c079810800100b442d1040d44800310713890200040c03140340810541c2200501e01303101006030b200000303032007411224500c1c58000c41041d0f400c004041000311126400c03a83e0844030040c141807910703644d20002061400143d00480150351590841c906104d00c0c002c14a5100c140d0700481860954581e074014000000744003290b0501400c0004117041c4209580300500005601c10390000031501c0d00340700072840c1c0182c403031a40b089205410442107500403150130b601402000d002d4220242c1140d0b10015860341c02030250300040c01030100001c040035140603240e41d10649801800d20913030b000d400103020240003000c00342e0300b41c62070740c040113640c1d441303012103c0e41608a40320b19031944942c5401400380c031461500c1c41c1c00c0c7c4802f0410704980a1008000d20845014216900190b540c0c030005400b85c411500c12030003c51200e070007050791001c02110889a41c4540008280c030441c981da15010841d205450700400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 880045971 1250 880044721 880044733
    0x9040b0316060806041401031412040f08060a0e12030408090d080a0e0906010807050f12011e0807060c080a0e0307060305090f070b0f2203030201020a0f0e0a0918080408 74
    0x140e039004030030150803444c152410701c03417459401182e00c10124107100003403090703081041103000744000b40100a0131300702c0c210303900e80c0c4e07150340d942c01451907031050283c01218054440841c0c0c600038144078070250720001074054032881e101003545a0103030304018810b581d441e904100f00020f80e4dc032071902401340781c410660292161f001000041c03051409043d114003642014050204a81e000400d596010000c0c1c13820681d50142d070341480c04103000c1c000500400550740800840c05c1100860007190f0748610080076040b0031340e00c24003265140141d225200c0400e942d800c02c40c02140d6a080107140c405001e04022408a0900020038900748581e88040c00195650b801d015000f0814440103049540b40c400901003142040d903c40e0043c4180450081d00840015403440f58441605107040c07981400c4c1c901054055503420003a020f5401b030b00c030100000d007040902e001454040c1810045064014041600460070480ca54006200d9100b00d45029800c980c40c0c503000407861401080a4a040d1000d440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 880047221 1250 880045971 880045979
    0x30c15040e0f070306090b0102061609090218030c030712020d0f151a12030d180804091b08090a060905030906070c090c02071a03060d230705220209040b0316 69
    0x4031171a5400012480307040c44a4010541c1e4001030042e00500141c070f17511203094941d8070640d058406640500b50b1036002003125081440f19a0329145803200075000c1d00c503102040002c140d120784903030040104201084c0e282102504040c0079603001780344580c10904e41e41d0f200d9164041c03401d0b16000e04005d450b071604501045583d10341da0340e16039140103480091104960000013516802051520750440d0b5440e2034460094482c2c0500800e1aa00f0002507941c850703d075021903000d000d44407641312801722206590141d040c8500561403084007010081c0c08401c4959a40c813000e46035500d030940d41ca2100380140809a0f075880020304986100c3c040c1450803902e081c40000c00da9030700e00001c1084d034100c400200014100060110651010803158aa495403954002090858101e001a0640d80320303090300407910420024000c0109245400c13034603010b603100200004982403807003410400b00c00c101114001502600a0300301000d00070000b040031218240130918061100c0ba042007030040d0244100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 880048471 1250 880047221 880047227
    0x1a12010504050f0f0c010e0f0405010e100b1603050a090905070c0b090c090105011116180b0f100c0501110a05032502030f0a200f01060e06030c15040e0f07 68
    0xd944062820090030380c2c0301c44450b013261038110920080341072080e035586100c0d895440c12510040418000c20401080d41c42c1d00100340c0307074642201da141d540360804a000c241c102c40071040d40c511000019504105204a0394100d860341c201c00d0000c0c0501c00080404104888107010703191041c2c0380b50781c49801100440c00d0075180c1d144080c1c05503203903030412040c44146407581010f66040d030701c0a007007858103c201c001e040c928000700003103d140d01c0c00100c2d00100d0340410403107a0040d0500c60840600c810034241c0100b01d1000e1803129010b034040c2c0d0440720007004500038004410598020341c000590645034448a02042c3c0c0450007400006034000308128410b0001c030411069030414a40704030116a1840340a5580c1c4070b141119a010070021a5030201248030b10948a800700d400c06200c040031110000c160361340e1510442c142d400e0350030202c002c42d443c6c1e01c0c5107900f0321038000100200030700f070711850921071300a000c50100071071b0b282e0401020411141c00324034a401110b0b009104041868214002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 880049721 1250 880048471 880048483
    0x5040207140109080c150f0c31051513030308090a020d08070303180f201207050f06070b0109200703020f1b010503070f032c011512061a1201050405 65
    0x100d04900003400d024258020071f42c10307644140300505981e66441144095091504040746c100390329000c0381507071000c2c1418000b03000204d45040e16802e402003401c014454480c0503d000a0311100d61035182040400c0c45140d2243d0888450403e5643cde4180326008192070202101041d2040c0d040025003070205545442510715140c40001c1d219140c034116540d02c20f03000070800000c2d100718060b03541409d8881814104c4248a50014152042d0741480304109032504018821103100f5400d804043c10541070103000ca800c603a503c072542005a078203000f0908018403003854400d1501035804442c0c207440c420680104201d0380244c000b4042018400091454030b60804e4001a418112105007031290341c108068940240040c01c20320807034589000d00314010100325a800c3d520a0340c614285440302a00751103602025080c02c02800b4108680070b42e41199503040c40740290b04803698000c840030071180d40c0450039a0301c6c1441d401c2c070b24094020004030690b240548030034240e5518000e01042100400c20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 880050971 1250 880049721 880049743
    0x200c010e0f100c1a1e07032702030d021222090603150c051204080705010e120409180c063c02010e12030a0b0a1206060609120c05040207140109080c 65
    0x3c4d030152400480e40034050f80e99550031031079807007000b0106d080d450003074208040b6129207410140c003400e041e5101148070391034400141e000e80a0400031000e43c510110705559204243d8501c01d02d09800e014107004002107088a00c0d14244802c80d020803450f07000e0080e00300440c00b47c080d26080f21a4017403a5021a0a800c0742482404400c00642400401c4d4030000d0781d0054004100ca500c4078440d0070018050407005000c003649000f20b00342050600040070103042600c4800ba0708210301c2d5805c0c0078481c0781a15511000d4203034141d170403081010b18407400d00c007444036001c03084200f0403c4080031a05a07840c009201d09480b07800201c584011240c0c2403059407010b280d601d0040020740d100011030340d158072018040070081901e40358441d10585590010034028044014001c0180c540c41c108a0000e00d4140281070005140100003c0c03c0c0c0341851b0380c00c03c2141c2064680c05150300e0001004029441120200c4586255003410003c82600b0300c1103100950041c1d01d00d5548018030b9118605003405010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 880052221 1250 880050971 880051013
    0x513061a091c03090611031309020a021b09040807170309030405040f0902010c02040507260105090709030b1611030a0305011503150e07031119200c010e0f100c 70
    0x3900b004030754852440001c0f22030318100111900c0340c040441e8254400d07100142d114146103040000c0c070040c80c0c3e000300f40610701682034a000c0d6124a030129030020420100c41d909c03c15a80c0803a011827103510060a045108e0200e8202c4031a8245020704240c004940403822600080b07010821030500b8090500d2107900c1010400a1180350341c00a011601c40c007130082d01450f0b443e00014440c81c000c4400101c1e030002e035410040d82050124082c1c203440f801340181401031000001040f10140608001d009990340403a245075a03a45502101a150780c203680d0340c1c801c1019401401494500c180014540b0202ca51740200b1158102401030100742e0003038403100f0400d8a400d6608050b056160800c0d816503419041d8103410361915001100a442d1030090780103000390000d1413400c5041c1488a00d114880c0c10b4490803504618101c0e65035421102d60341d2440160060200450158881d1514160310b420080c810070944272000d01045081840f08104d4020844142200d0188032508000c0c00032122460 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 880053471 1250 880052221 880052269
    0x1a04030f051f05190914030f0d0b060c3007050a0605010e06031902190e15061c0c110714030115030c03080714030715051f0513061a09 59
    0x103404640344c0e02032046200100b50359550782810000100045a020b02605007129243d140402032000c0b20b910000c10020050700c1c00e000310002d4100007065980030461840680340c891400400e8003d00c105150106ea010103c400e03c0f0300c1c010003603001501115000310000c1034107401c03510b00f00c02180c7c4c06030010403001030510100140d075a00029a22058419440c0000b00f0341610320209096980c1e40740c4090400348034000c04070303024201c820ba0034812001082940031001e1540248842031040b0403540800602c458803007002c00010750080e8061406500c0c148040c0300d464032809083c01c140344c200b0810040302088540f50b40c5024000c041c08013102040750f044c06880c59544c10110f882c0c40c07000400e841004175009050040401081100d03101c40c4081c0c0b40e40d46454034041c65260100c0c51100c0c0782c10316010201d06031403241c0d0f00038407041c240d001c24418014142420010046405071040a459271903000104203c00c2070402c0d02d0148d800c182d107c03030701c0707050356002c00c02c4d0b52901c0e80d000c22051103ca = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 880054721 1250 880053471 880053481
    0x140402030c010f02101a1302040f0b090d050105090f251719030203041503051501030509010f020c0606091f050103020901090902210c131a04030f051f05 67
    0x41207009886800342080c2d940303080038a106a04103c00d041c2802080c6291000c0058040da1502190703501910440c0c641c0c0750035031204105000c034090750140c25910ba044580501c10300c2c0c06040105940d860090000315030b82aa41d48150a41d5011502064560402c080180c03226004114030b41d0560703060200c04403a02e6142c160329807807100c03074070030710400c411110207132540342e08188418103070f801c150902c0c0f180d50415801c000c1d540341d00502c03171744401c1420100900c8036203200b0b10459000d450b11819005012010800442c0901006003c1e4404c40d50b80e00030f442010301061000781122048074020b01028a804420041e49020050a06450007914164640c88225407031400040e56024200142c58114420048580c4015504041c002900c002918880407500c0303074006c10144a04280d9a1f659610b507000414070303004200c1072140704000901c0500500544400c4a003004c0c1004510780e0800c0c0d640d40340c589200521800680303581d04000400c40c2d80aa001040006140c0306500a01041c100703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 880055971 1250 880054721 880054723
    0x908180a051c060216020a171204030f030809030d0f0b130903020604140a0c1e050f0d110d060c05040e070201050636012c070203040b070c08060406050a14040203 71
    0x2c281c0000c058580c0007603145801d00f140f0b42c48020301a009040d0040c043c1e04d94015080c01c00036160318403414460503511000e404910301c115003e4070f60200c0768220724078566405803052038011300300d41600d0005002c081c5c0d4100301440f8460881580e500e000c200002c0d0801880b09050510558880050414150344003180d00021070540095006040c20402101403080c40d0511090542c0200844c1d805000090343d442950494024071007070400c2a21a03540d10b40c100305065032011802a0022040d081810108404200145505034060030740003205019540c1d0f901101c0809925801080020509110714041850416032103500741c00200030b41d080000014011224180304085540c40790902e000300e40c800e485110700312002000c000d81e4656159a14200d4005041001e03d104555842c044078500d8100d0044500409558029600c0c0509000d546807480d0720802e01540c150511000014842c04100310080c8594042c000c002010b0030000102030a44480c0d421104134102003500b80805071394 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 880057221 1250 880055971 880056019
    0x11030c06070b0c09030321060d0b0109110405040609060e011a04122405011d0c0301060c14150406180201020c01030c0e1e01020d02030a0c0204020702040908180a05 72
    0x142103101007a0702e40d64528440d0f11449083c0100780c1500001c50078420f00031565a801c0060000490b9600c2c25665040910038003004441d8054009054040100803844242c4d002c0a1004549081540b0380b584820200301aa43d0aa1004180c10340c2c0314010020542d0442c0081e02500d25112600c2c000414100314611600503405010703c2c58950950210800400045c000032005c2140c441c3c600b541c20301e407041c4000300030034820f00f4074401d09640c160f00da01c7c0d01e42100034030800c210b0241500b142d080c002c0441d80706808040484040301840010700b48030504018880e0005040f40e80a030152a15141a03800c1d600e27080324209000300d540c490700005070780210b045074a2403400e10f0006174949005034200c81c41d0301044412074100814025401a10881d40b11440c2942001e8088855141003418100c1e170703e00c2400c80001c000780310400035030018a407540090144600052011840d04401e44840c06a9803001c3c00c0c0780b00c418048000450a4140a024000142011600031051483c0754880303c00c3c100d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 880058471 1250 880057221 880057223
    0x8222001080103202106011502160e040201020f100b04060501050c37030c05120304020102060106050309030d18110121020702040609240806040c030305130503010c050711030c0607 79
    0x2405142c28030041c5e0f111003045010880c240292101000300f03240082c0d458036420700031001d90101c06000702e4880c038000610030032603800c02c00e03909401a24100c014041024040d00490450180c030362115242c81007005640f030344030a031101c0020710800410401048800384c0e8040d40c14400240914030080b080821200400c80c0c403500e0310b5480d00061411400100c500c071074400c0000380504240003e040c0d100fa440c0120340d100740c00f02c0d015025003184212486c0030444009006a000f40014403040c0e204030059900718081c0c0e0112400c0608c6c0c00d26407020f40d03031702840c13200030314503502c413a00140107840b11a02c0b201c100a08010300000c1a00c030400001e0400100ba40a1241c0c00280d00343c00c540701c44e0702c640c9c01404201c030700308100e85200e008031001c004106640c1714180c1c45400d0100301c014021440714080d50348501d66042d032600e1582e05650300d41000507020320508031041c001076141c50a010304088409984d81b81130f91440c1e50b180c0000d513081c0084e01d160013540014035101e025200c00c02112411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 880059721 1250 880058471 880058513
    0xa080601211e02040b070308240d0305090a24082203050403050601060c03080f0f070e130e0705030d030e0a170408010207030815010f020d08222001080103 68
    0x2600304a1080c8016000c0c82c400084802e00c000340c00108110418090821135220b40d42c0c000d083e4556900000c13a151289a0702a000d904110000304c842c580f14a034120414880e040c11800c061071710000540201317503a0b110a010034002c42c80c0007586404050050040a128102000c5a0424480c8a41505050f4114600320000414024145405201900c004540c050111070141d80c40350f100901810b40e4030340071004201880e0218849446000300e0314031403610004014580e9a440808841800c0860080b5401440411803145101528000e44000104450007080341500d850285071500070308075942810103280401c20384640d140410303030143c89034104a40da0030700d204c154800e0207184215404401e1961000404e00304140e045241070784203030007000194241100400065031101c01d50f14200700141c2207000c40000160090000c1e40e00001c803c140c103c00e000c060340c14003103100e40e454070948000d100310480c440303650038043d8180c841507002c0c41d15407602d52455070366849031030400f0000115 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 880060971 1250 880059721 880059731
    0x209042a11030904020c030d0b10080403031505030312010312030204270e061f0603060e1b0417060a0606031407031e020a0f0908010b01050403020d080c120a08060121 73
    0x560341c0100191182480c004008565890031800d103d0381d01d07800050302e035a0841c141314800b41c00340340c4401d03152544541c41c1c903041c0680d41c46a904074010044c0c21903171680444150b202280c00d407400c0024000500c88504002125411b50501c240302c000404507103410140100018080302004c024207010104680c540248001503c0d44990060300d0f2241c541c0510740710b15001c100600d44a0b1800c1022a4210a14040c159844020441c00d551950041d0b000550817400814401c0408c2101400590b0440840300e050075102c11a510511a6010f00b018450b0300070020704c0900c0d1010301c0b440c002801281003c1211792141580344409000082000042c1540d0384007880038000006022110500b01c51005c55440301400c001902d6026641c04480000d03200d80008503420f9014440c4400c4140140c4660303081c24a15400c20581040e00201221200c405101c02400e08200300300100040010321140b0392a08207001c001800c0e000001c1025041000b4258031183d01240030013031070895240020b002c07603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 880062221 1250 880060971 880060997
    0x50402030c0d0507030c050603070905010c050c060a050904140f1801060914071e0210020f0f0f043816120f0f030209030312060a030804090209042a 65
    0xc10402000381d100e0300000c52141920400c40003140c1c550030ba9202d0b804549546840b03505018843c003084807602e002c105075030030511082d03018041c0a000c0d00d109408440340070407903202050050f001101d180b404903501240100982c03901d805007016400c0200007540700c5107000f6500040c00030020b0b00f080e03070481490300c0b002c10300e00083d04141c7c05410141400d1100070b101c0403084025030404c5468900140152003030708a01c03060010304400f6101c031540100301c1c03100e00075900c2c0b0080d44a031152503c520740030880d00103c142c414001c0d0013205208040c242c0c840349022005000903141d01903500101c0b002000116408200001100c103103861030b100d8545480c035460645500a00369040500302d99001c0a407401e1456204881d082411543e0340e07101c1030140c41c6403003076099004041c2d0066054001380141d484011018102c254807103001400b1700346055481c2c84a920940c0036412904405400181c840f00d2401c2c640a8040078205091981001c000c1d1480c5940c41050812044010418a440209 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 880063471 1250 880062221 880062223
    0xa020103021315021e0c0919021b060a1404030804061512061505010201180807050c130e010c090303170c090414062107090209041e020307081005100305040203 70
    0x3030003a051003c0c0d0002d80750401c24000e56101e08901176844102c010b601469811040420140c01c5100003804150b0b540d12025000143d54400b03000900c00c0e48c2c0d0030300a50740001006c40580403062401c40c080e01640c10903508040985042ea542e0301e1201400105010000b84d00102465010760007110005100d804a5544083c900041d4031009608458400ca1414407903142e0100408040d451903446a196454005900380ca4000030f06119840c051114880401c210340c008140040c0715409480c184d41000300006c0c1d00020084029030100e40d10b02a030780d001c103001d100e04a01c030003040c245520142e245030b03002415411540603003040c40c1c40d00e20100381e0104075070090302c1c801030000301305025120404e0640454070704100c40e4940301d214805881708030103a04808a81a051141002e44010f030708040300343c0084d5108284541d040307507030794400c500304940c141500c0c54103869107440503a880c20300340001004410081d0480540030019081000143e80b030300d0b04501c0d000c4403428041407980e5240002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 880064721 1250 880063471 880063507
    0xc021c03060302090f06120d0905040908070204060f08061b04060e01110d030e010b041a0d030c050307080414010f21061212080f0903030417090a15090602010e0a02010302 75
    0xf500508858140003c00341c06011146c071429080e1580e40d444080340d640140c0d203000c2e0108172808500c151078141325500301a085661100d01074050145400c080d03601203011522980d1000d50201c182c608240700d4207000703012664012095804459043c01f80841c8543d0600c142d100312828001285020415a40038039406041112024161199201c1120f0040c020b0509400a014107519046e042001403901e0320460f1135601e1019078100182e1904401c0c825038458080c01941402a020035210015004100400c0903501c02e01d01c4e03548580ca00b0141c45503943c2d40f031100e1414402282c030400706455101e0178600d051034881c0014102c26240040305401041503030082e800540e10300da400e0f000d03c0302404c1d503100210320315622241a40d0718040a5240c80506850a4020b0b07041000400d0104104000510341c55420041c40c51400d109580015607031205680030040d0101080e822001507900451510300800142c00280700e1800007035240c6032180349004000b0b040c99408170300600d020748613001c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 880065971 1250 880064721 880064723
    0x1c170a0e0d360302090903070501060303121d0c041a0406090b0114040e04081e070311010e0309032503080d0b19241125090c021c030603 60
    0x1661400601071200500c4800c09011503403000102e469141c51001210351108540c55140000c2451107040d5070030400d4800000e0411401c0d84410b01040e404038000b0302c1000c004500c20384803180c0c101d0b0400311040a50719010b003108041c1c1d400c00080020a04045003011030320700100da0000d01711070602c3d42c004001e00000005034215150001c0030031840901d900c4081c0c4003e090300c03421034840085800d03c0c0385110300d0080c01044050071001c9000600d00300040c00e186070005c00d907926100b04140c1d4201c43c9410203d0207400117001c524034820031200078492100d0000d00300d0040c41c03405500340042a9158003408a1f03042c4403409040c09403201c0c05070078400c809550300c08041c0307668140c6a18001d02070701461501034420b5020090b01441f9010000c0000220355461000314001c948104100c02079140304500d044c10321030340b0803041e40c0402c0203200c0010304003242c0d040c4940034406d08100841a601d035030042d030003582c44c002c44c00e0392442d0000f0741202d200c0346d10f1890b50301e903c280c131100f1000350991b540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 880067221 1250 880065971 880065973
    0x60a080106270b010507030509041b200d0e010e0d02210c0f0112051f0f0e0a1116080d140a0e0a1119030b0c030103051c170a0e 56
    0x10010610401c00c40b56100a02c02001808101002e01c016050803140705100321404107104020110000e4003940252815100c010030003d0641e585d2556036003809000c0803001c002502c801c603005a10040702803034081a1421500421b842c0100500c082d2004038a030003003a0601c0b81030409031002c1d650300e414035070003280c2c0075000000c1c0482d0b10950710080001c0010b400e5183c0600184107407941010070002068610594580c2283c014020707001d001090090501c41d0b460350a06e241180d0f95208001090003040c5010800e0300030b91034050314030304c0364002030402c42e505400d20080300340514820054500c01c2074603030484204a1800d142225046c4254004103400508007044881103030b4050145034454000503a0030b100031180b4400a44d1120303203d150050103480b40c0c4680e040c81d0300786010242182c4030070b02600c1400c1901e98076052001402111554401e1400100601c20480c00f0700074030080140802c42d840d8020113048016001c0d4030800121044011400002540701d11503801003c14204040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 880068471 1250 880067221 880067231
    0xa05010612030914131d012a0504050a050f0102030408060a050115023007080f0c16080c010804231506100813060213080a03082d060a0801 61
    0x1000c6801c0c031400150041214650001070480103020322204e07801d401001210103080e803145007002403c01c42c1300d52101d0f42d0b6140214a4120b424861941d48500c10b0b040e403000d81404074040340341210440d445504100d0140010050303500c542c488881503d00403a54400171504550040346180039507481920148641e005015107080c00c3d50069060381c0c3c04817a801401d00d10030f0020790341c034018941540142d0504c0c41c0c1d100914001e00d01400304203c51240801d180180946030f142032a0400000d03041c0d610000a0081d0310030384100862082d40296120710700e503451a019503180c440900302c5005062051805c001010000b031640c0d102041c810505006038541c88110b1043ea8901026110340a0400b000c5c002c110075103070070981d50000410b5a03903144004e54a10350b46858103100041c084881d80d80034004109207401082040001c0c0081000501d003c41c00b5080c010441400501f030205a0301e01505242d114040310100044501e00500800c1920f482c0c1c000450a20f10655101c00010351900c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 880069721 1250 880068471 880068479
    0x9020d110a090e060d0809090603120408030408060906130f0305070204020409021305061c090203030403021f0206010f0509010b07020a090e030d1b02060f04031205010b0304031b05030a050c0a050106 87
    0xa000d034041d07031420b81038908240d6555052004484405030003415000087c4403c0c0468500b01c0308180d40300d04080c05462680b003408904d0300c965082034102c0b40e80c5410111f07042c8607810b01049000d07804441c81009203217901b0309000386101c10001d190081d080042107501c0b981854022000c8801c0154090011561160b482c9a0310009400c102d10108110f038a084e00010b041c6001001d84629070b072010541503844a8125001000b000500c0301240c05000500002000d6541c075800c0c4070f040c2c2c9120001031305d031841d0070400a00346501604890f00d882c103009402d1110340c40301c5481605403403000d400280d948040e80000b03000c0c0901503001c640100d040c14040f101c5400080054031590a0a80061041204400068442d102604498001a403003200091a8802e944610941250180c1040042085062013450a4900907000341700000c0002041c0001c144c0c1c006140c600d440708004550040e000256182520f034411100d109040003000b00d00042500302c103100e0603c4055110b4002c01c07017641c0d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 880070971 1250 880069721 880069727
    0x5190207150e0306070f0816020a05030708071a041203022203060b1e030c01200d0306030b0f190f0e0102070b0a1103070807051303051605090c090102030409020d110a 73
    0xb0030041540a0b0040d903000c5000700d4041ca1014000c0c0c030f403a481b4884941d9030443c0b4840082078180c41007007144208200c400c08200140006d01c1c500b4007a017520343d900c50807030800b00f603a10000286000140c40d2102040080b036500042c881c84240e05140141e0344005030f400c09000025000001044a8400c6c0c40010801c00503501c452a0510165105100319000c0982801c0c11900c240845030540c000303119240c044e41c404c241e9105007644a900c088031408100099519202c00114850042036070b0710402d0007030280440c5090b5000c8518005040240361407030014038105250501c184070076071030b1131080028203400c0e0450008082c40c44021074507150170f420301c141790301029039800902a10b0441ca40741c0740412001124880c280e6926000c0311901c541004039860392002c4005030860f58142c45c04800100180305000d6100380840d01c100405041c1820802c1e50f000151001c022403800b00b01d2a20280d03008410b90742291485200142c031000345904940180c0020900010703a81400240094801e070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 880072221 1250 880070971 880070987
    0x203071502070c2106060503032803090f0506061f0c0308060a080a0809040605030109121409090a02071209060e090c1b0601030c060207260c031e100c0519020715 71
    0x2002d8038003482451f541e007050544a2145402808c2c0c1128881c0d01440c02040503510001070203a41d1400091003016601e6110101e8001c1004036410381000382444910320f403040b4812040c4445211400402050702d902400c0f106070030f44002e05110801d4009051980c96251a5008141d00d43c1a206c2c050028a042d81076a44000c6517540300b146030a401280c1410140300c1c500e416075002040034020744d800320b41a10b0140c0120b11140b0362000400001c0015215070900343e0150601c510301507100c2d07549292013070720420303400313107000420940d04020801940e1110704280f0b03860058400114503251600c15241700d1181c50720840e803900c1c80a460340075150300022298101c1c3e00031003131002c60a032200c00482e25001140f040d50042080f41c600007520202c40e01180b03407015000d1046031403401621001c07909185c160300d048514440c485001d0389029609100b80069503129034420005040550710141c090b0291310803404165580044401c141402001044040c082e0803c030407000e41c1400c600100800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 880073471 1250 880072221 880072223
    0xc15090512060105090c030c130b0301030519020303030a0c12050103110307090c02100c030f1e2a030237030f0c021c0c0c030813060203071502070c21 66
    0x101d0901c4072040e54100441c0c114142c44008240340441d490701800d42842e900003a10940d0204000c11000d884243d0401c6420b00404140110f15140d40c90350030300c1401c0c40c078600c0c03d02c807180303400c440c022005039808400c99a1182000000003040d51a000c8110b0341086003017210214680362400100900c008400008005201101181c80c650b454460032401d81c0e4406240202680c482d4202400000c0c464010070313401966071400149541b0760444110a07903a840079035a640260b04030b2000f030016454001c680d207400b155298403000d4884100c0005940c4030b43c0c0700c860304140d40895455800315010b401c0050110040064a40340d0b500d130700c880d9400500d00d1a0804c0070030303e400c15080e03e03110b0350301402030b035441c00d60050128480070120500b14003000c1e110440070451025504d01c0001c0d5a059038401650003880c029484126825843d410000190003020640d0720500000e00011002d04071205d080303992180168407003505103448441400c1d240c02a00c074140001c81610715183d002400d8003109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 880074721 1250 880073471 880073479
    0x1205120c12160203180111150612160b090d0507031a15010215060105041d0a0608030c07120609020405090f0714060a0507081308070e01051503040f0c150905 69
    0x54aa142d041107030706403244001405604103000c020142107030200d16800c0b01206041141a80050518031f074100201c05e44a410300304805002d10480d07051174000801d03000c060400405180000c600602c040c4607441c400c09615030b00020302c1d00c00c2d580303522803081c091550000c110b443c000d48900e005140d040c0148010058107524900182254a400036081600c41040c0c01508403040d201350554001000109401c2c14004e0401002407110141115500d80d50341c560064611030030810391282c203969681c0e000514030340c0103026820010030081210800c035500d0681400d10f404451421101501c10f141029500c17525100801c8560034000c18624031a002c0c15060302c034140d40751082010188060211290000006c0c00200c00e4580104002c0654031300031011641000211351010007042c1c070981003043c1c1a00070003010020702d8102a00d503405404201c0701d030010b80351400c01c8405c1500000b80301406901c0040c95034000e0001e44a40d481c09070580c02094141c1209055014005030824401c42c2d004d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 880075971 1250 880074721 880074757
    0xe091005040b04060f0b0a0603090c090507020d08071704030e0111010e0309100903020a140a140d021302130905101215150e0a1b08131205120c 63
    0xa40801485003611459001d4042c081c5502c0320784804c0018060786102041c926503178500c041a039034810b04100000d290340e90303003c0307403501c1d1910b4600071900d601c2c2d00070100e50703041405015007140c0116011300441101e142ca4286951402000c840c0410307480a045484070341d50081c401410350040991641e0344003a2514075081c114400100e00301d0341416403848558006000040d85803802202d403011401840c81d018154507100e030000740d02d5804541c01105440902c0010030701d079060050420000301609090018555a84008110000040b0800910441301810b0450316082d2a5050320044940c0e11001d8001075140c5d882c0c20010507090343c1d0011400a817a03070014062504103d408507440c0d0140c080200340d00790240b0200503049007000110380c491950000308003000c85801d150b101e40c04040b800f041218681d60798040c1c0c4440d0751840c0041004101c10000302408009402c4805a4407180214009070300c410300322024052100d0b90500100382406212440c10720101405080c011092283d039 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 880077221 1250 880075971 880075993
    0x30a0b030a050d05030c07050601090504020f100207030809061207030b121902041d0303040f0b070906020d0f1808031806091507020315040b07020114060d110f0a0e09 73
    0x3076a401c1842000300315a11203941402c400d44124081c0d50001c203040c00c0242004940c1d66981d00b4040240c000141c01c507581d0041000b507103010840603901d03230002d442d02c030152a0354010094894450380405440c2c040c0016484286846d81c0d4120b810b404d000b02c00034401c40c203048400501605900e05521700c0348000c06c10201030000301081c50400390900951400c01d14001c0d07424403000c1e01410940c0100044440e5055008046c180015032103144610392002901d4098034190040c5940079280d0400c0080046041c005941c0005187c0342010705d030300305511a865641b404903401d11030000030b030480d0342d204580099280c00002c003400840b940e8031644c1a2070403400091180310f00841c002e82c1c1e0b02a14121005031310b400108010220300b0b00140965040c016032082c01e0700204800e03541180c0b10030410040121243d070a104460f4008a4018043c00c44c2c1841c0c400100300c030b41c0c040300140010340ba8600f034801d29651100c0c013102d9550050903104e40c2956901d8100d11000c0104c0d502085070082c481112 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 880078471 1250 880077221 880077223
    0x2d0907090b0406030e071a0a14040b07030804060603020a290f030105010c030c0f0b0108060f06012708060103080c06090f1b010201020d060e09120909060d050a0606060302030a0b03 79
    0x142541c40094000d42054900b40080b00038113882078181c00c030b5004070313003010440c4c4a501c041c01055014000c0900c0d07450390320800c010310004005c040344103280414030062000d405400700300e44409815290144640e161420328600800c107e500003540300700c10110000d886c081140b540f03a1001000c03160585090b01700702c0a04a684a01c003c0e01c0416001080180300b01e41c0513004d4210014003a181c012151443ca540d0b00d5691b00440800b6292aa03c090041041c41002c0102d280d1101c0c00030007180301801c04e140007a120049007128200046800752444d0f00921030348881c180100312540c21200c45581d02d0a20070002d51060b10041c006004a8002800c070781c000050068600d100d0800510241c040d90142c080c04541044d03800e0304654007044440c03034419840c0180c0d0301814003c18046a24103103010039918042e54607401d100a210b003403000c080c040d0b6556a401da130042c1c0590740d81000038a14540346042900203c2c00610642c0b0384540401c00c26819406548100710020301000640140360800d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 880079721 1250 880078471 880078487
    0x1030f02041520060a0209040e010b0102072607090b0f1504090518010510090e0a15090305090d080304030e0109030b180c10180501050c0d0e2d0907 65
    0x50362002c140d25810410aa2041c3c41500582d034080c0c1c1100407081954818508049043d50342c103041c00e0700401d4081d0a0b00d8248101003c912040000b040040c3c413050020b91140b960f0700c030700e0002c0003840055000580040303001151080b132540640344025218120300c030081c0740f1000c810340121314000d05001c180c10303d1a201c00e0a804202d00d01340c10319142c0f00c003100103404020601d00e8410500c124070498854240260350080f15942d29540030642044058801c850081214921a5004402d030b98040307446c2c00f0103c810481c05885c0450881c035a030805850314030440070219081004600350038140311010000c1c41c000d41c4255113040003800c01078011906040c0a0101414100b04503010803a101c8150345078850b148980d1007684c06241880f0009803011191030760380e001091a028a080020000c0300e11040545401d0a0440c00c10f40d0704034030140c1e6241c9031001c3d0b070280500e200b02031440f0f079034000c06a0f0410b424012803441c0040480b0f100e95241000358400c0b400341c42d02d000400c0300d450041c030315 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 880080971 1250 880079721 880079729
    0x30f010f0b16050115060806151603181208250b0c0d0b090a06031e0804170109060501031a090d0f0c021807020f12045001030f0204 58
    0x3106081c000200ca01402079045207008407200e640c1c481d10500c0c2d0032400140e081c02060947c40b8002c00d4a064024024040044140f4141031002004950b440e40000f0701168580342d010329200600902c60418040003100316080400620040c1c1c040e20708101400c2d004090382c1c803420744101e10740402c4151503400018615002441100301c20001604240620080d0001741508030b00400c41c5144100410008241a100e00702e1040c1c40c0d01040c130a012100b440c0d0710100003408040fa50811441d250b011070b5000f6030003004452296032842c1c0191040035040404501d400035404c1201e540e403490550200090240700801082420002452000300410200c40d9080c1940ba00b803d28000120221007840c10050304907407000c210183d40721103900c0c00c40150f1140e03c0540060040c0c03200300c0921494000c1ea054075500141c003c0000f840300c0e02c000c0007000c0506201c0e82c40c1c80740b08000108620909130003106548001c07008901d210221440e2095110042d132000c0e202080030340039198134241a84100d000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 880082221 1250 880080971 880080989
    0x301030201080712020706050f06190b03010b031b0319050a021e03060d0807050c033a1b060b01030b040b030a1103190c031704212402030f010f 63
    0x1c0ca0b55010f541d2454124201180046c45d001030b981d1f684045410541c4c1525900e1018010172850382002c0b42500350300d40c158491884071901c0c01c021404280703c14094520000c02c044007043d85241003a060001400958480a4880c9403031048041e9524014000031107807410b01d0003141072002c0f01d00c01c45a0300c05144880e00411108004d015800d680b01518843d044a50000e2907400302d031a040103402e043e4816000707803814452103c109494801c40e480c100180a440c00c245000b860b000388100c00d4443c1d4507514400e4038242074601992466040c40350000540b2022080f00704100b5558058014820240c90400c9100382c0c24050004a40f0121281901030f44501c00300004200c4000e03c4400d2440c008088070301c0e03403422600c041070525464504988406560600b40f04200e41d4100013420b010041085505103898402e04040200075968550251905d110130340d8140310b601207804030b0185c0d212111101890700010014025407003114501c04a2521400108038040152028411645035417 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 880083471 1250 880082221 880082237
    0x302160305030a0c09050904170415080a0c05030c160512030a0203040515010b0702090a2301030c06021212130602030c04090b04061a13050a23040c08130c030503030108010203010602070b0301030201 87
    0x40d460327180188517101c080d2a5120244800660000d030544c801d0120486550b81c1c1c0504c1c2070840c0c03c041a21003858400d02880f030b060040102d514241c0060307440b102c10750364000034030700c0032820151305000d014040c0f8540c1090000800c4400e01080e00118001e40c8a582103403a100e881000d400c144a0080c041c100d10500104002005490003200180d002200d1190000d0004e079600006100d034100c2034240c40c0140341d40401001403101074035844004142c64000340400c201c40a015400511a501e44075030072400240104449544200d951104194440e204541d01c3c100000c05880030f0f0803a114200f042c0d420161105c0003420540a8001100c3d00c8100d4000400700d070390300781c5245c0e0b000008240301c1041d41d450005141c2d0707544802c2c4001000521040044000401c1001090200001c0060f020390b00b0819908001a400f400381580103400429450309103085103403244a408460340003405511010002040fa084194001c40c12240035800f2070b0030346955606d1400c403c0c00244000790201d9251 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 880084721 1250 880083471 880083473
    0xc030b0f0108040c1a0913091406010b0904050411031209100207031a09031608090103050601030b1003110d1508070f08074b080a05100c0302160305030a0c09050904 72
    0x41c6045070211704040103850f00341110803001c10358500d010700d00c12014a0311500c000c0c1c24032000c0036504003032442140140c5044d44c1010030f088a03910582103c1360207550740e80c000800b800308403070380754200c0b200c0101a02d405103100c41500025400c124012071144802a1103410031a000040c840112603118442048030340c4200c100550400004055039000d000400c049940c18100101c8103054500c60102252031715085400101203640041040c0d0506142c8000800240d07110324011000000c07a103008201a521044110100d0040c0409180d006040c098841c0c2010281c102e80703c181c500b448200c400080c1d466000c00c01c0107445108440454222210074004102c402050f14080180245040e08011032441240310415100403c1e84148016100120000c100900c0910080c10320a00030560300c400c6444945d2100c10500715901070b165541c61090f4528041c1d01070300c11150044080000080007400e0113007803903204441d0304480328603201403100241c4c01211a8810b42d40c028005284170740c5c031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 880085971 1250 880084721 880084739
    0x30f0103210210021e0a0306080105060105040513050a0f0914100b06030a051302060c1e0f280803010f08060601020d0801060e03070b0f090102011d25090c030b0f0108040c 75
    0x3520318056024054241c617038510004002414500701a9400048440c0b0b0410342782d003195000b4106a0411070200300c00c200c140d071000d00d44101904654000a00c42d111401e412004014035007840400c5400c10714070707a0078082c031014129072075004001900d0300411487d0011003101c1020000a9008600348042030b07014003103502982d4000b00003031702028103500f2500003622540101c050a0103035880010882104000f0614444810f54148010460031180000083d114811142c0d043c1e1201c0c0300300004111318900700c0078508204e0f0460075603540c82d40c41c0d19204007010002d000d624007500c217010202d0515440050307109006000e55544403400d07400c0c4501110301008000c00709030315116000c408207940c80420b0003060031019010b0400d030340300d0703e6500190030f41d0020012180340c8074a81e14403043d989800310380e0111450800c1c0d1a41410782c110320342c04c000032240340c0084030890f181400c40460580c26611034940803008454410030820b06800440d150402141d0061601100799800c01c41c800c0b13 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 880087221 1250 880085971 880085977
    0x408071e0315141008150720011107030207150810050607060b030f06060f0a08030d230901050114031b010f0c05060405070f1a160314030f010321021002 67
    0x2031400b4001c2070b0b001e100e1014406006043d5074044840710126400c000300442042540e001046901e9071000618000384040d00c2c6d05404220384182c95400c103130f440e4000000307511008242008042c850b441c1c04c91810001c1d9035004501412420107003441201000e01e00400440d403040c81102e48604c54241400244001e40d088900304698031034075220420040d175020f201003001c2c010001d004080c6031402904000c000604010b9081c026a60441c080c081030700d010003141c43c4883c400c60081541c00a04201220042c40035201e0b00d020b104079014031001071419040b503412500508080807001d501c1d4020103848130302c101040c00d42a031050601082d80c1d405600e840c41c80314601e05084034924020b444941c28110b040740c0440d1503400c2410144544001c80340d45c0c1020704440003402030072140d0103c98210a100c1c2030a007104000d040e0b0007540400d4411440c16035008400c0d58040d4a906241c200301c52446400c0c003080340c040a007101a80203480d81030034003c5441c03180354018400c1c01440c03400c01000754 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 880088471 1250 880087221 880087253
    0x5190f05040905090a02091e0f040816083708060109080307030c1a070207270e0c030d050307200319211104030204050a1508030408071e03 61
    0x60511000801046600c01c0f64480d08100c00070300a105240d104001c10410010441c0303030040002001002ca18013418011540188100c03401071003600c50b401c20094034055081000701011030030400c0400c01107404090070f50301c034101403e07106400c4c2c4000c48444243c01c08461200e07001c000858400c0071441b658020360049c006040c0300c10550340310a1160f0031a4030401c000c4d804180a414200208144103480d03070395200c81c2054103002400c09400007511403540b8440c3d840084c1c41c0b402c94020b00e10a486510b2202a0407200400101016131412910781d5480794001d4441c1c022011044805c5014004803882900f0540d1842800b84045a040c4180980b0408242c0c0324842404030700030141c86800291032805c915251410141300c808050084400101c02040106003402c1c40300008940c00c400b40c9041c0c03503046401144139505d492200d17005001800200703002001e02c000c00a0b03400d0020000f44240e51045d0180c5131819164085540c0070803406c01d5040403200008400c2003c1540a244c0300c1c510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 880089721 1250 880088471 880088477
    0x1003021e010c060e15060a050a03241401140301060f090f0905010203040615090b130e0307170d0e190303020c0708070609171b0112060806040c06020d05190f 69
    0x482d07840d44000c070f0364a0810700c003aa0344982c1e00318511850b4554411382c45602190814401403c00011074418482c03840024120107081c2c8022034480c80b00f28083d50100b0b184c100422a0152610207411154800e100e01014402d080313010304060304040c000c44040d074404400322803d0b40e1600756501c008040610030f070001d00f0340d030340c030031800281c000c2c00110f010b00e0140001090b10846803014091802d640d501c1129071340d103004902c4006440303004c0c83c00035440d4020000030b0903003200c2d4260350540c46114401031101c0380c075401c400901c001c8500540042c001c481002c110414040091594506200d5042610585842003220009100341c00406800802400b50b40071956a40800392800f0880d80101c0d000c1400010180208000b540418500c0b440800c010034010810340e580c80007080802c03814504011031020b403046020000e41111000700f031303440221505403415043c0101140f01600500005014007284506560b1003407055502400c19044804051440360340e05807400003c0e00078013400c3c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 880090971 1250 880089721 880089737
    0xc0b0f0709180e06090a0b0c07110402070c0305010c090302030a02090a060b0a0f020d091d100807260a050304230405160905061819120c0801051003021e01 68
    0x602d04148500a101c50244000440d00c40c00d031280060620b503000300041100c0c0d0004100c02d0101d0460541c26421010720250140c0d0381d0014100340c803400d181d45030b0b15a0483d000048032410840c5100f2454201c80c0604001c00c01c0d01020a401c0b65550300501c4003035455800301d443c101c050b140000103580c1008170104001400d55640340084200e4004600110204416802e40c6000310b0b01400007040d641400c1c42c00051031810403c1500440c0c0700d4a9511a9a16042c000070303807900d00d90700c0b415014001c800c0c101c45c81190b071003035907805901d000c80000321502c94504003c0c0e00700f1000540c40b05400d9000c2c014604203800c000941c00b208c003094580c001d22008049403505640c80d1752043c2405902d402c821f51125544030100a071039500b40e5440680a0f0b84200300d040389080600e5564101c120040b01c08000840110001c02c40905e120740000d4fd0319840008030b0800c01032201e0004044500c1600240400c3e43c0c6d121802a5007800c51201a4001400f90050900c0c400810345008290805061400b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 880092221 1250 880090971 880090979
    0xc150c0705011b0b130302060c03070912050115091d0705150d0207060903091d07080a200a0801180509030708071407090c030b030f030403032316120c0b0f0709 70
    0x351103c1034a80c001c51790f007000081e2082c5641030020030351008130411850702e90704003070a0003091480c0c1071040741c03405402c0035400030802000303400c10a416054880fa443c00c854484076100010310030054801d080300c0360310440025001d40410342c03130704030741d4020100260320b4869016480e055102c0e40441e009580d08100000024042d44100c00c4400d000359180f0414500b400003032440c0803004240d00c541758042c4c80030040c4499000480d20b80c804031070403020071f054404d60390340300c607000c00c0c48030500c2d05407000304016805030f5100c04450704072581100069001c2552044170f104a6909440c50483d0741c00030030040e004156480700810301948500121039041510640060801a4940001c40c03400e441318855480340782c2c507000c3d80b88148005c81c05042030418904900e07940e442203120007030034014000001c1840102c0024610560080c25424550b280020050840c2d100c06124040718900118800a0850307441008075042056006c400b049040c1c940341790115056100400180820600381c2c8045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 880093471 1250 880092221 880092233
    0x4060807260307030203120601020c102001050f04021c0c141503090105251e05190c03080a050f060904061803050904060e060604060f0203070807050c150c0705011b 72
    0x440e042c1e01175030146443e02e03240d000c56220001c010b0712145c115800038064150503960140080118103040c1003030a503404980c1c04000410102440b418525440e1604100b030b84150b81a032180b081d482207507194660f000592441049452105014001510b400070512042d0500d0b40144080c410080c040c500e000e0124038004115403044030b044041c5d944035002c0c00b269400c40c403600030014a41851203502c00340308010040192130070100c400d01e918035565000c0c84050062044550102401030034001c441c5012030040c00211074480b048000515241c000b5849014620415001d01740b5001404101c3e00d401041043e00840980140d4540d56118494410300301e48900200b6881d120b0340f0789948070100c02080100301d074842d074021340a0891010030060f00d0703910042102c0903105c1d1810100c01c80d6034003d40c220300d1401221001080348000048190500c14009219002c2c00411138564080d02c2e0b1343d4180350316074080e40c280943d01e98080c40d802e115560048a0300c0c501940080b491790b6100040717807206 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 880094721 1250 880093471 880093477
    0x503150d020a0b1201051f0e120f0f06090606100507140607090305011416050a020118030305090d02012c120708070c140f1011010606020304050102010b040608072603 73
    0x14554000954184070110b051368080c010301c0200d0b1880e550002c0141e0303d1910800c0800722504000007030001366030035074844580913000d2400320201e681c1a1000f8410580d1000d078a01003045502c1a03600182c403101001440304d20445014141010040d5081d000f9a12500468402c580174034010410100f000b00c100b210500c40c1910356a145d114506e5030030140d084441034081c803a44900d46008000f0441e031031000c4001c611a05240896580b072017a0350481c010041c0001c000c01a1030003290071b005140e8190010343c0600441010340e5658610080c09900301d816880c1e200044d00b51041c1e0070340301d100d42d410000318030140b00415a1000c04d0b00d04103403629944883e008440c40000801c8000500100107404030141c031031444056403002d0302c100050f10601d0022403403845040d074010b010f04168840c62031492a580304100900c05680c5400010b900c90b00b06000c2e441c015843c0001c3e60580b441c007030051004480d0300d10f014214450038901c407400c80180c18400c5690212405c440610244410002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 880095971 1250 880094721 880094729
    0x5030721090e0405030304080c030721030e060717180f0318030a030c080a03110d050109230a0e0a020a0f050f010311090906281706070503150d020a 65
    0x3808812194001010300180c44507045495155146800c01000850010440380c001c1e4000c6082d5482d005000500340c518491014000c00c241040504a582010270b031402c0c2c0444901600c05000483d800401c05540b1582240c0e01800030741d80034a9030100440600800f5080a148581200311511700c0c82014a000611608052680c0c000540c101f42036030b4402d440d07888039000710050315000c40c07251401056460b40110151a14400007071610585002c0d47c08140d060116801c91900d91501201c03074401460240b043c1d4089905080c01088404400007401e440315401d001e040c4070545400080c440200000d44501d4400d1065120b5080503945c2c0616900c02880d058181c4a203642c01c200500c0070b01c0c0395402066052500308034000380a50840c005442c411407042e42c045451303a035268000381d1075011000d9042d03280e80c0004a0300031700c0b030030240000e000ea076450b4000042400d4955501565035000b202c040c0c00107103062020030540c0e40c1501003011810b41c02003030390302c03a00c81640003d10030360141d40c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 880097221 1250 880095971 880096013
    0x5060f0312070c170d03020c07032009060603071b0c360504121b0b0a0207060e0309010804020d030903061e0f0e0705040207081b0a0b0c160f050307 65
    0x6140010800b0348143d0030064400520311015080080010720b0381d52100e2084035003803580201c1c82907000c00341040000c000b142c02c0070034000c48180405645841d0aa419140f83c0111800703800188241055400c507400303100345644107072001940c2d10811091031840401107c00c1c85582c000041c18410005041d00540d01c0301054100d44141d03400a030310600da1000e083c4c0800b41c240000c00021400c4d034005094a02035504002c58048102c0320000603800c0202002403000b2540e90a02071400d403da4084c05034a441503200f048002c0140624565030300541061f01e000500500004006050032140b840c1c02c070703101341840000f16840340d4942c0292a5a44c0d940004041e240d15212042c0e849401001c450742142c1204102d48043c00030030079280d04281c05800d006640000c0d000d000c0000a200300d03422450105e240b082110445030700d007074454105c080e00756100b10b000000f15108540324400c070b5103410003030803040015561341d41d03481c051900703850710644d0180018409a4041030002c0c4154038401e840786 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 880098471 1250 880097221 880097227
    0x3080414120a061b0309050304090509010b100f0932011202370f1b1505090111120a09061409070501021c09140f060c01020d05010e06010206040605060f0312 69
    0x1904000c4030704c00c030154a108044c200314060011078004011a010b84110345c2011869503140111540508801040c20b500141134200c0c0c0440c140d03102e0101a0b003004155164015251741d40d108041885141c0d91102d100078403606100c080101c507007003100c110001810122110303512908420202d8102050040f90341c03940072145481c10316524860303045003002c0804505a24500341c8010689030080d10400140f050346809039085003140b40e0071540c09940140e140c01e4540c80310413030b100a000c0030b480091082d03091000600540c1c4088042d40c042030718040482407140d41d010000390245c03100304020b81d105941c5104c40494040801e4103075200d503080ca0002d041c0940b0741000245484501d564890307109121003d1210125400030070300080741c00002c00d1044d004140c00000d1303010500441469400b07000080c581141c0103040d00a040291584001002103a81c3c80e0003003942400c0890380c26005800500000300000c0031366101b6034102102501034991000500c0100340303840340075014034600103008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 880099721 1250 880098471 880098491
    0x16080901022505011820041427030408070f0b1e0f0405090f040201021005090d0c150c09150e010c06020a030b1903060e0a030c022103040603050105041503080414120a06 74
    0x4148000303840d84007640c0400c1101e81c11222041400e0f006401b0079401d20150801c7c5c1c00036044289c05c0032180c4003c1342501c2d80d03650780c1c44103240c0d078480078450141800451417001406805000c00d81d8005500443c5008022044006115559000d18000c000000007808049019201c00d01064402e0740e8080b915007007400c2c075000280c5800d181681c09200d1500381000c12a4800001c5580d080c8908a81032144171014145031448000b000d40e10380915852074051503030346081e40100004100c682d030010007884040034880c205d610603810400c090114580030072120008466600402c844000c91500240c1001c0900c00241c103481801e100e01c151a50928091007404402d100f90b0441d412488020029103c16a40181c0811840304002c0e1040c600022540c0840c040c00c1c80340160001039009407942c450301c5070005002442d085c02001e010354a0445600782e0920b103500c5800c10740c0d03001181c190515240c01c1094404045018400d604441c14084041e00c031141000240c2c0f1903441041c001c1482c0c400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 880100971 1250 880099721 880099763
    0xe091507030218030105010b0d02070303020d020a09060f0c0201021c050d091b1706070806060d050f0f0a020a2109023304060509090a02090306160809010225050118 72
    0xf50031064031036450007004010440c0100103c0380c00143ca0303100982c03945510708059000307000f0032258612039400007071500340f07507580034182c1c0c420ba0b03205484d442c3e102a008101180d03c0070b440030000f809a0b0052191115400721054400c002c4d616134680030f40b400321031604010680b04501da00b04d548005690010100b00106840c14024081010446142d40105144203640f010054441002c1c06a00c4c0042042034a07140d017101c8488042d01c0051109081040d6001c503a104111109545141c4210103ea10b4079110b0080b6009000207990360741400e41c0007101c0c0b003150b06c08003268818952f034a461000050720780c64007052056071509411500480102c001092141080c801e00c0b4a124081005001068009080e45da8180c000e4a0305240c659850359000001e00c580740425a0504c61142003000303d04007405942d450b14016912001039460b8001120700340c0c05500a82e202e50140441900503444d00c1c10711015046004000101d035000c01c1c100c0c00282220664401c1c0c0b02841025140024812 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 880102221 1250 880100971 880101007
    0xa0302011b0c080702100c0b04080c0d030b1e1c0b0912190e04020d06141219020d21020f0118020a0e100e0106030c180506040e0915070302 61
    0x1c600340410586040c0e918425980714940c0028440c4229a0003000000d1250005840040c1e21501c0000e41c0d0506050000054200c0c1c1117084003440380c908006c1c88503100313004006e40d01e2005841d181010707035104082c441041e03a41360400d4010307902d24040c0d000d14404d043e11015031806500001d0300350405000080c00e20000304d2108014103000c22490f502480c03850450741c02100c1520f405120f004c0810001340c00b07441030100d85600203003000383c04101103405081c1c1c0c6007450021075007020241204000d044d220201d07440d600d42c42c1e162002c014005428030784c1044944c0b41c0b150109a64038204a807404412090108107a00140d10100742000e81c00350034482c16100580401c41c00499030100c2c0d00140c014807190140440400060021500e0482501100c030040c20301d0340c0354084207685070207000300141a040c00349000074240601d41c48070304030844200c0e400d40321701410311854035041030000c01c900d2a0180c088841c500c541804664160880d4050b6401490690340c0540d44014803400240144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 880103471 1250 880102221 880102271
    0x40b040f1b0611070308030f1b19201207141903200309060f270f0402130e0916140a06050a0221091309020312160609020f030a030201 59
    0x44d10004060021400b90400d0325401066100203403030071f59600140008203099507031048506540030a04040b4650b0051034260100c841c0e54803c01d420070741664811401040c40900c6115030000f059130b810010039030f80240401d030701816410328a800071404140c50030a2030724100c2035142040052500700b65024000680e102c000f144003164640b1207203503840d241e11074103920b2446044d002401c0b0410420201c10b84038400829106003040e030743e8141140e161a080301150074030841400c200d20030186000e209961300002407003003174416581007480002a5080c081c003506224420301c101d0203004c5440081c200b0241200c03200702c08050800c04103100d10720a06411820a00c101400700d0030302e503a4009821106010081689000d031515100c8104a038400d000c4655046600e8600b540b20f800500c0c4c100f003c415100380c0031200110b0350b020300c03d152801120820481c201050700d00201240e440e40085900d140000c04801c02201300788000b924000011001301c000d42d46414000600807070a4010342c81007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 880104721 1250 880103471 880103473
    0x150b18040c050c070509060a030213200a0503040f0303060b0301090609110705060f040311012d200c010213030f021306050d02011d0301050c0d05011a03040b040f1b0611 74
    0x204207042c0f0080e44070403140c02064001c038000c1001403280c0da10f4007024402150054846403501344900364a6000d084032101e003c2c00e50300c01041c10300007420078200301d91610303000380d845c2c030304540720340d610300110910400042d030401d919484003280701d0a4000045009107007114001510798602000102540c6040002d842130003000c1c011000402d50100301c49078060b4100c02840c82c19270300d0340b4096400c11005001c5c54000d61803c945030103045100c1400b0320015009110003014040c1582c000425251079001e0410520960004085c1c0b202d110402b0f040d10814207000903040004100743c1c0c002d03000081d84103841141d00c03840320034290b041028845c040036103009014000b00b4249004039030802c55501c0002e04110020f0601d4128400f0841d841c40c4a40c4020000e0126040a01d1075030b1154000d4907041800c14034040000801045040741030003040c140303e03045411990f40b0349401254140c018003e40d07020003090041c400150043c40d40c0254a48101a074020b620304024004161818001c1d001c2c0803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 880105971 1250 880104721 880104727
    0xb040f15141c03030c030e03130602070b0304081b0f12040302090610090b0c0316081c0c080103030f11010903210506181f0b0403200a0603150b18040c05 67
    0x2500b001d80c065422042e00b40c00c0100300f6240b401c5045000b441201c0d18103926010200c0c0706050038140a141030304032240d950172510b400b920b070aa68803143c801500c0003000d915040005000c1c0d10800c1e410440c07001480820b96040d1404c01603554284000540c0501c400e120000c0d0500852030414440340e00f1910a0f902000012628100500007221a01981140d0a00415086041801002100d620044507101904004c03030a181500098005019660564980288192040c9002d00c1103034018031407940d40003156440c5450a82e0442030301d4081100f0030482002020648809004440b00107120355200745100d1441400b40c442003000c082e22046031800c00c400d00c01c0540d2604120100000010f400300c0382c2d42c0743c0191411503150070301031021011918220014019203050042c1044902484204241410620044100021003951268019000b95083c0a10f078030a9120520010788480f080e054140c0300c5079540c82d150414a11903421140d00491f1054a091a01440c001121241881d0342 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 880107221 1250 880105971 880105999
    0x1906061803110a0801020c0a0506070c2004090b1302130e030304140f0d030b0306010e0405101a0402070c03020f040203060117040204140a02030403090f050a0303030b040f1514 77
    0xa0030a024840904200090600c030401a070b6207541800091071408021946d50400c0800192515198181610940102c00019003103d00440158120756030081d42400460707900155810b0700c02407956140c0d04165034040310790010305a801d41600442e801105104603000c81d01c100000410b0344418110614102070041c056142c001003580e0f00540c0c402140440c0c0c83c601030019152464040365a40c043c4591945c0b140600d40544c0704282c0d49c00c05034151442c680c0c84810701c488108040d2001419980454184440384e00c260f4001080c002d00d07c0c0c10b040f0003201d044c0c00102a6004401c083c0c441c07000c400010402c600e0080f804903098002030340c05508501d040720002c0c1945d80200322200040c080f500004003155166804030011240a4004000710300700104000000e40048800310045840d202c00490b1141100030540100d46009140400d01400c5980c1100074081020203682c2054498401030840703407460080340100401008041040761421f07072603040d8206141ca80e503014500c0504132035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 880108471 1250 880107221 880107257
    0x1a0c1201060c0b25050304060b0303041e290703181403010e060c04050613090204321c060b090112031e0c06050402031501090c121803030e030c06190606 67
    0x1c1c003100440c0c05e0064891307595041c440c025200d181c9890f507042c0000140807408400b159880002d624000012400040e261040450707910346025a070700780e01c00c29400c50541003d81030000d2440300d1182c50300701e2103000d640c9c40005c0e00f40903d4128500342c02d1181403000c40f50a003442003840110300000102980d04090070389146900c11030244034081c11001072514900d40c04489210700400200d02d045646680c1c445031040d48419640c00c81c41d00252081c1c91036403c841e084541c0124000080800402140000e801c241d41c051003501254010707207600039802d03590794040000d4006e001c0c1c0030041000c070100d441c00811845004904180000c1c05013a03407000564000c80c0c030032103d6400240001d0544071800003a141000b810400d508071600e200010030a1681c50b00302800f5410f20307448680e900798244420605a448015001d5a01f00d4007031005030109100b600110081d14040c000e0700c1c9007c440710701d56800c1c40310480c0c0a03012401608400b006000c60340c455140204443e240644014240c80029 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 880109721 1250 880108471 880108531
    0x8010b0a12110102150f060f030604200d02150c010b0a030b040303020a050d0c0e03240f100b03070306050a0b4006020606090a091a0c1201060c0b 64
    0xd403000ca600b620b18070003a4000c0081d204a615480e8070212240340c1180180182c1d60100c4005002c0c04c04020161a1414001645800303141c0c008030154202000030440035007a84000235851340080642c1c895005030320380008040c0f0a10303608480301e03501e00c0141510727800c0d91f6407218024058008802c041001c0748100d044241c00607418500581e03a202420000c83c0d40c0d000e40400303a08094030702280b440c0640d410600e07c000c074040030f82c00d480381018203050881c4070720700b504805040b980c080c1000581c01c00384c00c0300d0309500c1660f420b003c522642e01e58841c942c0d40e41045030040046545c80c1418880703132511011100080500812003403070240e20742240e41c0c5c9284900c10054480c4807032100d0b070005520b0840c9101000e1207403052489200c1d5100d000a5984506075145400381a880c004214411120701440068a800c00d0050038000459601c2c800065001072420003003d4041c0f1008111b1150503403014020525903032008080006402c0c49103914501500000c20800c2d840c3e03505284000660300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 880110971 1250 880109721 880109723
    0x30807080702010306030215120f010b070f1a040f06060b0f07080904110a0207180c09061b08031003060b0d0308070c08040513050709060201060506090f010e130608010b0a12 76
    0x100d5a2a907500d0310060700a00380980000b076110703400000322a20742c0c1240740541079408994421200d140c40703500c1d400031050020300800300305000801040c00031542907854655011720442200e414212031001001000c00140e074225404d40513602c00000780012401848003410a0f0740d043c618102e04580308046602c1017140041108001149030540e0396596441800580746160540f50b0356050300400948a040900410640b40000203030641010000e1041514200a41d100d00101a04002060f0751840300321002400c3d00013001000701c0007810002c09540543d0118004a11203419403900c0300a1b03a141800f968010754011610307c0c0801d52004086401460b03905103e26071380e21a05214002c3e01c60398000e903401c80005103e0801d2a115a403000d03129030721035603030142d51984520b800c0303080e40c02ca4800d459100350305010382040d034540b05004d4a0f8241e0705040c504040c540860100304451280242c80a00e0350341c94404001c01c42080c0103000f4451001c403443c80c406800d1002c00d400d070003040c400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 880112221 1250 880110971 880110983
    0x51b0a051b090f090307020d0b2202062b0606030c0809060709170a0506041a011a0d0c0309020d0609170c03040b030403050909040b04020a0e090d180f0e0619030807 72
    0x208840110174130459803810340148c2086500d034040d00b40400b04c01003d03101214242e004220303c1d0000c43e000402d00c0780c00c0d64020801c2d890800e004500d900f44281c40269820428580e0031071042030314841c400c100007411551800302d014002c040c0b01400005c0700606c00310b46908240b042002c0182e210449006480d03000c9415015640c03810501464180c16450041c41c52013a1000c1c40280514900c03250242e40010049440680c0c036200c802c1941085070300c0315080004140560801100b00d034000d01000c414901d00000d04c03d50580000d041070740001010b0b50855500c041000074000d501c040d1140035038420384500e02d800c4290381003580d40d104500c00ea818400021000c0380405102d4021942c038264020b0481c40c060070641132007807000300305503404c911498005000141c1c1803403c40b9000e10030101c181c058003803503900c20310503030300e0100326451031001c0000c0c00d6012079400e288840460152045c000ca0011910f03000c01804214400d44c8103403844c456021f4010000500381e50104c3d100541e100d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 880113471 1250 880112221 880112251
    0x1009083409150609150c050c0d1506090b060f070c050a08030a02011b0509010c1103060c041703091c061401030b1906030b06010f051b0a051b09 63
    0xc031040040310300c804010a00ca480030301000409070219003290b46002180381c1c80342041070303880c101903404510038810101581c65407446040e40c00d019010448486005809440b190a410790026a0110440208840d00c2400c0320b4502001211440b85101501c503802041202d00b5044000031402e004980d043d1100c0d4900040080c00c0100314240c4100805002e4240d4020310f072524580398071307030f044442c41800541c82c000e4803a000f40030004007101544001e48a107843c002000e0011100120510001e580b10b120142502c2c080d03486c201f0115101c1ca0307030706000c030f0340341c0e414540c490f4000080c02c402e0101c02e41c02807090354102d5852180c5d4500c6c40000e510740a200c0c8555140c89000340140b5000f4034228000340c000081400044e000040c8600307001c0c810b025008828150f101c00b2207140f0300026040b81c0a84d00041c0d065401007010700c01060381810314038149501c3c4c1100d00c114540400c09100b0641003000d401003080020803607603190b0385101d400f000d00940c1030b1011a0360103500801c3d0b04210f200706 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 880114721 1250 880113471 880113523
    0xc150106023007081c0b0105040312020102071202010c0215040503030a0b0a120317060603040b0f09150103060b010e0901180c0c05030a03090b0a090302030712030e06010f05100908 79
    0x1c098200150102107440e82c0c3c5522050400e03002070780100050303405680f50384c071100d000100240325142075680e050311500e0803c0d04580740c1914290489000c9400e40d03500b00158030100c3c06992044240d6409580046020010800d000742090f100c445020702841d04a0140070004e20044180c0b54041041e0720000341e12a0803600182d10719001d58416155041052038034014164410f24103c5043c0215990228589415003800b030f0912007110081c0c40e200d01075020403220410103102d01d4103c0c815404840c1c0300d40b503011001d1112502a4412115165540264440e03560080b20400c00120210385818580d894103a900e84813480c0403030303660129551140d4900d901406111007a15007508902201d849040c03141d00500105074146082d030300360f02400e0024005a8550140400c92a810f0b40030354204039807a5604103005101d4100c0070140354032100c40c100c154004005c1c642c000c0400c4c00b40621044e10340700a000b003021940d030504040260607041840280030002d40e10000c0c40017074004080c03070001c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 880115971 1250 880114721 880114783
    0x5030307380c03071d030d0804020a0b0c010f06060512010905040203030d0f02030712020c07061b0227070302090f1c080a11070e0103050606090a0603060507050c15010602 75
    0x6160070032050074880109000040341c160028510400082e181c40a44011048041806074440c455803541a40164040494544a0200035070401e102a0203400c03c5a2030340c0514000360004182003a860395650040c43c01c5203900c4c090803004015a051161030403161200d4a01d0b1040705000c0c801d5900d41300c80108084cd01c04108582241e0800300b020000721076105010300c0603610595100001a0b0f007004a0803181c0e58500c2142d01c51802c0c403004180c4c552030020b00703441450382085a0803c4100c0300d01d118001d44c8440200d141049800804030781e03a0509104074010800d0050034600405106029000d5180c864803610144e0410455200383c650b1400007006804441c03000c1c004049440101d5100c1a40d50080c1155204000e905c0607034128548038072140703541c01800d2001074059409200402c0d9242021621660440d00c8800e0101d00310351680c07510310954605407034000010f500000c25801c01d4005205200008600192000d030b15403414000a64540d406216110003405803038000c451a0343d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 880117221 1250 880115971 880116053
    0xc02100203041e08010b030f0d03410f040203060a020702030c1305010f0506070b0a110c12030103140102070b01210b04050d0f092306072003010605030307 68
    0x1103195840b50b03e035018454100c8000790b240f183c0d0300380f0341c00c05007600700a06e4003107003a202403413040d0010411003081040440140901220004140ca107508601e40da08000c081c12903443d00146114540307005051204903a40c600080000c0c50403280c0405020040c1d0700401d000b0781040d009040940c80e4846400081d082c02c0044c5411079001415a0031280304064035002127048030394070705055111913524005d020700352184001c01041c40c25600001951074003aa403100d54442d1040000500b80314049004500c3d1600ea8002801e0b4020301100420400409d411042c0c0c580e0b1001d40298203000480c2e60300c0703010800600818100b44c408103e20409103142c601c200d2101d1b600041c00c1034803420282017542e10394014060001c002500e543e88203084030301855101c000c6408900c200c000c0b49412500c0313201b0482000ca000c030f43c0201d080224001090040801e00309941803c81f0b0700c41003c000200b0542103e4440d07104501981080c806280442c00d031082c204840c1d04c0360261f00e490909400d60005840c0c0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 880118471 1250 880117221 880117229
    0x3020d031a0918060c09030c1e060301030506100b0c061303140a1e111905240727030803090106030c0308190e150703020c03100b01030f020a0c0210020304 68
    0x1880c2c503010801500b03002d280e045034100e490b00c2640c840da01c0d01700350030142e8070138044c2441d01a0720080303000d1610b007054840b03c90444821201e401c00c1343c0459001a00da40d100f0780c8203407603e43c41581030010382458044604010000b44000e103103803044081c00310ba20b0f9100140846d0302d520307070500c0600906010b000c19034090f40500c9102036860401c81d4001d0541150100c5000010015000c0c0205150048550003010480307200240324040d00c40c101801c4003c002c031402c6446000714454981d54000510880303c501e4007400812200345455030b802410484101c001d00782000401c00c011120202005102040c1c9400c10b0f0300e10750702e035600d0308560302605aa900007064445800c00000a001d945d00c047c040558102e48062050302c5680e80403501154291034984d80700310240c0440340e86000e403100401e0103a203c0c1c010340350165a8000000c0c2000d40b45601c24501c5500e9401d0719030030350791502c01c86801d020254421400c2880900c8014840e90402d0340083c00303a41c203d545021003a0007081a20020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 880119721 1250 880118471 880118479
    0x70f081506040f032906150c0a060b120a12120b060403030c170403080a0507021207080303060a1d0705130e0411180f060f280f050d03020d031a 63
    0xe00d42d101950243c3c000b40d48001d68410003400510180d42c8101049240c1c00c2050252482ca00c0d103d050810400712510002d4400c10079040018405c1003c05010f12003040780241d174006814001d210502600b60380e41d494030001a044210034000241310a0064400d01c00c851401c101c40d4052070300c41c1c8c4010034580c0e60280d8030800114000040652200644070007034803c5805001e00c0018510001486c012800003e02190052042005162040000e048400d0000b00101d0721201002a19410425140c001420340d4000104002550600030500c42c01040c1700850b080d1001403104404111420241805041140006415038546103a0948401420020360043c00e50b08041c900481035814204401d07000d80d107800c65030b010035140145032511820010700d40e4000b90390b445081164403844540901e0780100c1240b0340c134052014005501540d40d15400c050038421b420312817015400c110943c81103200d94240465a800240e000c1396800c0340c96030505010071049076191604014003c003107511904 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 880120971 1250 880119721 880119727
    0x906160e12060105150c0a0206071e211d09101d01080106210f02031009080c07080a0201410a0905060a0e06161202150c03070f081506 59
    0xc6210003154580c1200c004030b0320b003c103e00040c5c401202c6401038403a4800e0540200d078045026040407402400010b01c40d44850400b865003030121603055000000c1a1000f04c0203010264549009250000403440d85041c001103503120040da40303500440340c0d0040c600402620000c907010b0a148a0308038040c01e42c5d03c1d180010348008038186a00c003442441203411941c00c008001840602c900a403a8141c908000802c0c1c8030107003610798110f598004001280c141c49160201c00b00c41e00c0300d215210301144144c0c4a5540d49461b000103504e44035664110f00010b411518500300181e130030908040510400007544012081d6205030124020044450250b0001c00107141c503034000b00c400000c0606400580b966900340b51560103100c0130303000d9161580086a40d0b01403041441c5401c4005c0c1a050b40d035008002c020360f0b619a00c8441e0448150110405030b0f10a445007800f1100030b064045d8401c0200281e0b908514200b80001d00700c103109000c80050011000c04140b10540300312400448280c00303484140c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 880122221 1250 880120971 880120999
    0x10303020d02160303080c0a11160311060901081918110924062d0417010905060f09010902031c030e071d060d0b1303030f050906160e 59
    0x500e03000309190050050003a041d009402e01c60f1000458207a940641e211030701039459881d25461703075000c9511241401080084800c00d01810000c8003400401e090b0541c00c59483e501d8451010020b003292548611014807220700e10341d038842d15595001d201c3e01c4101d00f0003011280400014542d4480840320100d607a18160180038001144000000b0151101c0c02d1950b234403c0c44440c0c03221b03908120140080c0e80e818003c141c0c0340c100003401c2c0d5000d841626485202d051800c1c004803104030905803403640800f041c00c00030044505100204002030800921282600da034440c1d4135843c0c02040e80c400d5144490128514031000d44c0b02c00403966015089646600340c034074420f080c2401c80902000042d09000c2c1d240c444a00100c7e00c0703c121001000e09075a4a420125400181100101200e030010200880c6601203000201400d000b0340e6801c0c0781e14005115410000e0a0700c0002c595101203904242c144207184800140850303001c000942070610018140504a0f20019100d002d2907001303a49080060f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 880123471 1250 880122221 880122223
    0x906061312120e15030901060b04080a0606050d11010302130306020c060f01050d05060c0a050909040f15061409040302030d1103100f080319020109020d0501090302101e1802030601030302 82
    0x541c86800b42041880d01d99030340b0740864551000f030090302e4214007594005001042000082c5030010356a030008200d00b504c448503130344140c2051b03110b10f20642c0420148030030f102c8281705d02800383c2025901c103a0a103045484400c1082c1019140038101540003640066020088104070003540d40b00320103560b100c0304160384543d40e2009940000303d081d4203100000c0c051421740c1380005410b921034080c2c147d9a448a08544141d0090b224010500804200b00c03500c5680311010144181d00c156900004d00065040806202d10a2040344110a2070501e0a01103080e050b40b0f500f1000038100d0310000c0d190394505d0124254010340746a40c11290512040445880c28080918841d41205991382486070743c5038100303c070070744240c412810140c00401001c60400800c6480400754642d900020032814125800b02c0c2c121030b404d0310265201e9648846510400d58140140490181c0e5168140714003c0400105d4164412811001004e2641c4104081142054540c2c010856400070203803a403941c1c2d00c0c10f001e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 880124721 1250 880123471 880123499
    0x1030b011806170d27030602030618011514031902090315010f142707030b13020304110a150309030c0204060f0810090308040209190e030a020d020f0c09060613 70
    0x2440100305c0f01c4404143c502101410080190040c0240c19034451031603d480c030003540064009500868071200c03882618420a400c24000c0c04018807100e00000c600d0300042040c48031400c510000b607400c1081c840501c192071404141d0141070b400040c0e4030510580082d25006500e0004840240030400000e85900c2c0060140125210814403c05101a0904001175441c9110b0b04070491101032224007207125030461b8640c4d0207003003410300092031030b48000014a0b816002120360205900042080200000035201c100d2028058440e401580c0c03c2a8940b500b18031500180c100b0140e44980ca102458400c00d85c045d280364000c2e10402c001512518185c2d00141140141400c52103518600314042d50248228840b0a0f0140c0d901e910315110382d82046038080020f003c11540c41109640700700c0850305031181c0a42104801300465443c0b11034000a81000300402c90041903411503401c0e8190000c1c0411540c00b254000c50707004401d5500c079400100c42e400750700c041c0d0414604001340481e076085020302e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 880125971 1250 880124721 880124743
    0x10f0c0e03010c080c07080304020a080609030304060f0b010e060d1503050c18040803060915030f0c040c02030c060a0e0106081e010b0603040203030703030915090c030209060901030b01180617 84
    0x2807046042070396060b00c4600381641c1402c0c150710100a11b8010a0310036025640107071004007101e2000e640c075101a071a0410a0b41c150b54141c0000040c0020060315114180f540c03c2d640ca002e210300502d510000e00500382203c8501d004c4d1800240c075100070f141075840601c40d81041c810814106441e41031090303850042c028402c1c0103d4190044d00112252804001d01c990745c000201c505c0c503599402804181038014002400e140c82000c030055036542c0502c404000e05144800134a1a1052501040142d48140f42c010007075400410810000365000710703a490344198584404195018800d40c85401010f8a07882600c0a00400a03100074281400e10b4200b00780c00794600a00102404c80c0c100120362109a9000391f00d40d00400a020009000b078010081c0a401035800d1401d1148903041c0000343e5041d014202c51a4580c1e100900841c90b0020304250803440680d5103040380e60555070350762075144042c000c000c80d55041d41c0c0070f415100c0e0130360070a01c098107004c0209041901c4007010103548a0b14a10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 880127221 1250 880125971 880125973
    0x61203020a1b08030403080a0e220c0305060d0818060307080708060307060e0f19080106030b0f070207030314040b0d05150f010e190902030c040e07090e040201050c010f0c0e03 77
    0x440c1c0300e03007070450102c82c80940c1c50450240d40342510315a50160b130b684c0994100c0091010f005014003682c1e5a18001301c00710981c0d480194403140b41100c0d02c0b0103c500c043c10442c02d0500e00418000e458680110b05100598807488043c0d966254002e0485280d0301c0081c0e855101030000700f0003039666408018a4042c0516480d828004c0e02c0d03010030152666224000c0d040000d680300030f804200c0c0307002541001e030340030094103600b2038080c2100510b00554958110081a0f9100e25003041005095194250b01c07041c640303035414281c10510802503d42506100103420455800a151071507880582104e0041c080c0e520840c1e034945c503407451000541001c8a00e03134501400d11410010b54200703c92514055081655000031a0690304108441c21000b1480700c9068010301ea400302c2c074084244002e500690080c60b01c2502e403407500e12084803a0500400c41d004200798031070100300b040c043c94903190304241d090070201e44401c4020440d900402d00c1c80c00600105d403c19180360700c200c1e00070711900d42c0c9005c103030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 880128471 1250 880127221 880127243
    0x270c0f0e0d200a0914310c0f1d161106070c020f031c0305090718051012110f0f04020d06032a0e062e1704081606061203020a 55
    0x282038408640c0000240c0451071718090002c6c50311809130715120a120660140f0b00c0441190a8680b03100b154034510440b03401d88180000d100500694910000800314001c0b000e403291040c0e056102401c03009090410b10040d0a81c420b07400c14000e03500a950049010202d880794038105500030086000000c09030301a04201003041c2325400e0206020720500760700000c580804201d01d00441c0180002400807805018a0304007062101403100807210b022200d50002c942400e006040c610781c80c130282e208107040f40a4a80c14000940c000020030360001040b54903000c00d40e00c400109001c8443c104d001d940c418400a207510007802c913680f0280543e03019500d809444007440e4032050a100b46441c3c4004580f01e404400c10440740003400d5282c0c0900040d002002107016040707000d00f45011182920480320011401648055021402e800807a0303030320b0341d211028101078640c1d000c1c600c190408c0c02e203089034002c80030051180c587c02c10030050684480442c0c501c10f03942802500c6028a89086500c00303061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 880129721 1250 880128471 880128479
    0x20a0b040b0a0f0605010c030c062c0601050109180207080405131a030606032505040504030503090115030b04030c020f132004080d0c0c090501270c0f0e0d200a 70
    0x41c81a130058600c10b860726942040243c9007504c2c0428040b20071079078561141150172985011150031403200f1841000016842003aa004a04040c016013015041224008041040c8200743d400c0d001c02041140c00140c2d1526142403004e8644925000f0a80280300d11203980352596080d80130190034148060100300700c1e17014501301078484509031401f0398035500c100c0000250500213600500003c4d050070181281c542c1e100082019035204a070b06401140010007040302080c800c4c01a821110071811140700300a0030f6070744000c0d941d1130217000a0100194004208110b481c1c0030030714128410001c2420b24415458042c08000d011200500c0050050407056900d03c01d01c0c00741940c0994010001414440b020ba500071907200c090110140c030012500807000944076440e1044a000c1c2c0211305011a4032081e1040300100341c01c950210031800d901d04030004502c65840b00b02c9503641e107042d1600104403070000c0300003002014003030409004880303a0202c3c0010344810040001c41c5040643e1440c1c0490350b9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 880130971 1250 880129721 880129751
    0x9060f040306050f040b060609040f0e06040201080c0c120912070803031506040b040e06150a03050f07020d0e06032a0403032343170a120903020a0b040b0a 68
    0x44e01d000782078511b0040400d83d14500b00c1d001c0e02d00c0382070140c4000f403000060540c11007038030000070854100b0b4202c50144025540d02c815807079405102c08840c1440c107906a62140c2d550034a4500c0740e0300c0d0000214000301d05544040d103400c6116115012142c80a86800304140c80e5401910b030781d4128990622481d416061a2040d1400c4030000e064581c1002d103880341d14002180000c04d280d43c05118030701e0100040740c4c510064540724840340d80000b424508102d459910580150a41c0155800700c100d48080c0d03a4800b00800006500b921020303120340307400c22085903100c040c178583c1c4856049a1000116195100044c1040720301035600d00420210f440b400c400c07801d54043d50100214010803410344461402c540d241c0070320000d0690141b1440407540840e100d81d004031281c10007490030481d80300900c22000d070b0302402d81c0e4903132030f072146000800d100182070a00d000e442c051126859042c2542814020f01200e01c2103a00080d0140c0326103082e1814510300b00048540400745413400c64a4080110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 880132221 1250 880130971 880131001
    0x1603060816092d0c020a0b0a1b0806062b020c250503060406090c0f030302010b011e0c02010c08130b030a320901060807090e06151c060209060f04030605 67
    0x445021003144501d08072a69005444480740b81301c15445114000c400168100e50703400c0c807811300a94002855804423410419190700280d04c002080401002c0c4161740e681c00c400c07a00100e00d49140800c400080c2400e5860b080d5141c12046076592002c518042c010001040c100307103008922002c03205056184003400c0540e8010b00409800d0780c0241e0000340051328940c0002901c40c094446500c04603a201401d041000554000f100140d45039a03003a4032551b0004000b1840c0f2200a2803104040712401c00201900e108030070203410090345140d4101840404012907801c055880f040e488410385507200c8000c1d0b07038015250560003a1904a08051041142d1481e5442e44081c415a46050150f450300c50126180608102165582c44c440090260400c01c0701c0c800030011044040b42103c90181c50310b0038804020050090071507801040e09042c1d88005018504404503c005000903c640c14400b00038010589010b4100e140007c54100c00d14994001c1c10440e40306000c144081d40e40c04510810001d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 880133471 1250 880132221 880132271
    0x120216050603101703040506340210050a0e06070605180f03040e041415060a090603050c060c030c060c0301051f0206161403040c2c160306081609 64
    0xc03c001d40030b0140d001c410b00c1c03800600142c54205c07820607842c0d0700015007940c09100769220400700380c0c5500a1400b00945c1c208010214415007035440c0c2e43c1500840c030395400141d6150700f00b007000a003100e41c45000e55030402c0031100103840940c5540440c43d180740141310599400401078044100b001d10294006821a04441c00b5400307181003d00e401180c960040d80900201d8030315001005a485000042080941c001048644022141000b2081c056114525046610560b003413480034404944001920755100805482c1031356282d43c00d03441d050840c0615480401280030300c00a0102900c49a009503068840c11035089030031a00511000050310364002e515405078200000040d030803851004080f502c02b9407420060741c0070443e03520030505940111402c60344548503940601c66140401044800a03c404446c0e200c80140d82000490039403000382806520481d410284240f14400d41151000b444c80208940e850081c3c10300304280341e1042d020340d82e511480c5c030100f10307050b041e00c66401e0048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 880134721 1250 880133471 880133491
    0x40e060d0c140105120415060909020a150323060f04020703020c0f120d051e03060102060109020f0f0301091a1c060e071a0a090905040c21120216050603 67
    0x420701c1c01d1442c208103542140860b040c4142403004c00212142c2c1c2040b148113078803038400d801c05003604c40380c1d080c03c43c1d000382c0055400e20704d09100800141c403284401011780303580e00402e0b0650340059204502034030a00700070410501940100703445424180a4481c002e20048480001c01303615082444201d006494001d00180e126014100b501d050051100b4041c090190501ca0a40103c40c46246022241e801020020344005843c0e14040110815080b05500b0075400c9461402c1a0b00001e540c1c2c84103024012203107130f001a030300e15203010410032174a1021031201c6060b129039580072208010081400c054100d0b1407482e0081e02907291000c13040100f01e207881c1c0b24203002c01c00341e15036200a004030001c80b50a807041d540b0100f855125007041d00c0485408220306513882008540c010040300b401c1e80100c65443c100000c0c0710020305040d8507001501c81c02181d5041d8610311035120082080c94441c090203000c42e00c4050308500e980883d051051002000b4a40c0380d135561071f0280301161104803907084c11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 880135971 1250 880134721 880134743
    0x30504080f090d140706090f031a09030d050c0d05100f060e120a0503040501110304060f05160b18010e0a0b0c0a090b1c0606110d180911040e060d 64
    0x307a403400101416685401802c462841c02d902d80d20410040c9090300200c4c455030108008024455011001102602c01c00e0103034101c3d44d1640d5034015078a4000e41e2815001e495903070014462600c104140c460300b07155800c00748030303034108030040d000c103a40000c540303003a801d0400c40080c0305a1040d20f8580104d0310003d0600c00c02501d450801c07986100f030160302e05da00c000b90082c6a070f200001001483c40c0603010314051a5224940300000d0003a68a0560703110054209000c1000080c6c0c01c104020003448490604694442c4c21219800f0010303681403000300b280322000140141070140000a143c00000d10f0002c00030b0941c085402e03035980401c0a0010032800501c40024802e001d610043c244603812801c011740c9090f11049031040a4000d1425581c1c44e01040d15200041c00a6010300801031527942850b2540d1156072913115100c0c008000e0540c18000105030380503c40c1d4030b500900300281500c0d9001c0140c82c21b1030b581100254801d1040074000142400421000d24003e041c40b004598490350f40d280c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 880137221 1250 880135971 880135987
    0x3030209010302090d140c0a0320010c06020c0f070909020d021e060408060906010501080f1b0c0f0a050f0c011b030e060f0705010c110318030f2b03050408 68
    0x80d5110165040c1090303001d000c00c030300640700c4000c501c00c0c19109449240480080c080c505140031158544140718502e2007200b00003080240c2d0280c1c0c01603450380c0d10011451403440040c0c940c0300300c1f8000140700510009100082e03100106a51501c220343c5000d507000381b641c83e4070b201c096035100f5074041e6010f074a61030500018546a80d00300140308600c03400c41180b040c6117000807e80e0f005680400d0640d000401000030002c0b0a120b914090a400d003850103040c18106010490700b01c0c002c064800b40d140140d980329540c40d0314000e89413006038190440b0301d10300380200300742e8480c2072421003100e0510842c044004060310101d032400140360183d41d055190320940a801c2d56401c5190400d07411f015500412001540b60134000b46000e007100ba088564481c0c0718a0030030b003103a0791078030074008026450111040c100008001c80c1c045075020b141444c0d072803000c034000a062001e0040c800201744034000600c00c40b14468002e54080800000d60409101c03955a000d0b02500c10403a0300805000f820050b03c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 880138471 1250 880137221 880137227
    0x603050114061b030c070314190605040203100509070303021501060e060d0b060403060218040501240e10020703031206050609060708071a1008160510021207030e010813030c03 77
    0x80389424a15581c0f111002c0c0e811021030075940880c3c251081500862801d00900c2013600e20350b0b00150000004004051210b4000d40303080714040c0340148043d4441011809650b4100300302403803120021002c00840c00c01e41c4000395a0b0381c2512044025009840795154404901c5041074100c910315147c104540c0016401c2103440e5011201c1200d580365100c08800840d11484060009184102001680c0e10b00748090b1101854044401a1066042100500603207200780c000000141007103400c0e0b075102c01c0c141010307540c0e000701c0403029410180301c0384c404084035800241003003200c0c0030b902c070440f00c503c11811501c107541c003034004da64000008100021450801c0c0300105446c074010303585542030243c55070b80d02d09080400c50308910301c10144c0040c0b02040782002501c10040217080018801200500c20141146800f072041d1841207510501102c2d07542e009110009a007001e0482556030740703d00d4540075000310503503001d80c1c3c0001c035000005100b074400e82500b01d000541648034041894940c2e0360403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 880139721 1250 880138471 880138477
    0x30f0c030916140103110a09050f150c060708010e04050d080406110c0a0203060709030f060f0207051009051b0d061515080402130510141801140a060305011406 70
    0x4025584240b1441c414201406000507014150b040300c1c100036066604001000d40d4141804040d1440007042004042508010b1200850740107403071302207582c05542c00241c0340d0700103100c5203552a840003503038055801d004a10544181440d88405489913261032610700c14038411200103000354040d013003846a482c0511300f8980d11921078038011071800d020700c0c954980c5812000e404042c0fa80603584003421032405220541c0d00840d80e1510500742860b6480344840c2004589001c3c04031959140300420100c210b80407203a400d60800c0466108002d0b001c0034000500c03c0c400c05441c1800b9070800243d68004081001070103100013420b0351012212074650000a00480c0c202407098861054002241ca030b0b5600003054a60180c2c50751400780c54540184008040b202e18074000ca103240c14104500b01c50342c00c140c1c805a89003170071001c4009a18001059240480602124100092400000b4051141c010044402600f915080c00642e5a000194142c40c0203004052001070021580c40755800c180c009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 880140971 1250 880139721 880139731
    0x30a060f1a090a030c12020a090e100902040e060709151b11010c0212070e0a0203070212160204020d020901110c060d09020f0a030b2a04231e0f06030f0c03 68
    0x4200f6070781c1c03035890068486165200000d0704514000c440213600e0414100001807010807000e00015521460180c0c030348039841c0444096541d2104181c081d510346600241141c0c00c1d007421203880f402c2105014018014a102e15a40044d0003039050402c03602c100c60141c5200072140c446040503001399642c1081d0b07451484d403a8100040d0038440ca0140c0c0d0b40030203a17020dc2d209e1401800322103060403c030740c854000041c9201421401001481503c0d64005400311282003076601242e10344000e5803144091100c12080030b0340c01400070900002821b0964020703c541e98090701e88002030010780c41b505443d00f14208200340d10003014400304d40801502d4002c06815880104204030310b06502000800106660308151001024a01005003070741a51844e0b4032841907180c01d04c42c0701401e550b5020040c2c800c40c060039910394000c15a540144c0501540c50720400c20007411040905141c51211404045003810188249036011480c14213040c00000c41e8055a0802c280d49181e5882400d520300380d600240c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 880142221 1250 880140971 880140979
    0x3130501140d090818031207122001151e15020c04050f09010b0a0b03070509062107020106090204030506040f051e01050915010e1305030d060605030a060f1a09 70
    0x810761200711140c0c0719041c403113440b40c2412030700c80355020180c400301e4149200c098000d9101d4a8000903000380241660300482d40140c80c407061185c84039084070f0316444035402d035981c4520354244054641043d04403e0b8049110f5540096040d6035168140c48004040e03103560720006500c006000b00810318601009041980c01201c1d50541c0d030401040c1101c0d41102d003094600e08503414441c81d44000e0180c0403110b0021950507000d242001414280f034800071708031174180b103800142400b86890703104c280c440c1c014424110a80a11f00e0000036910510116032440c015407a00c40d021901404900c2030790160390300100103008940c6c550340e0368000c02200f00c4041c2c5d4a07116102c01110140680e0781c1070224281d140f400400c2a08011592a2a100340088800168441c0800501ca031198411105a0002641c08100100381171810080e04501c0341c80c003c900b0541c101440881c885801400070b40c06a010418100001a958900c01d8686880e40c0140058503a4180c03101c060039803070b50090148900010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 880143471 1250 880142221 880142227
    0x11512020c15011a0304030503070c050a080f1b030c0d0c06060b03191802010f0305060a051002030c0f01142a0a03230610050c031b06180313050114 65
    0x1685482d01d0400031000500d0091940180900301410000c15403407078010070854214246590058814000100124100b008204040003406002c0090700080b41d0080141d50395000c11425407040d907881603038200840309136a4013103450140000204d40000210707c3c094908800c10f004119200b2628100039074456445900104854040710019802401b40030034881d03000b15034040758030a4034000b011115421050501110150740c0140f000c9441e030040d4a00007a66a4a560009020102d150006074200500490001000d50000020143d0740314100849d60024001a245402d03640756044644929004101051882d41445441c2d4405188456a00316000c0d0005250b12182c10040c10b420000f901c5000101d1502003480009070a502806001919072508102050000d000c040011082090018603184180c000344240d50000d5403106841c4000181a041540d070781c44103881078100029804003c851200c1c00008031442d0604520300c0c4001e0318580b1006440c600c0c919100c20601c14020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 880144721 1250 880143471 880143487
    0x8060a0f090e16060903380a09150b0307080606030312131703160302130e070302090a091d071d04020f060307031e0e060103061104080a030903060f020301151202 71
    0x1c100f401130100350340c466034160f185081481080226925a480c00d171042a040084442030713598103038040c54038104012207a1981603a50005000f095005002000c02c0c101160341009160004565090100d00b1214030a0312040c8a903200d00c41030f81c1165060f4020010702074a4444441e810354040e0b4612140c080500d20742c3c6650440d0002c0d807400d500070110020420280e20700f00566038140d0f030840e280844c14004880d80ba0100350000f4040d456044041d0400100c40c0c3c0c0c8250100e030600a405030440c107540343d03142460005403800c0f820140d105e50003030303800c0442002d0000342501200d20041305092240c0444444860a00c4043e00690308014072030b000e40c0c1e04c2d4403160002c1d40a21020742c1c0c0050101301c40300f00c10300640076000c9200015811701e258080050300001d001030640e600300f00001480304845281c01002d11a40d40028803c0c05035a68080074550441c2503403017280d001e06802e20284076040740c22412440240103101c807410143d4141d0820604c20a1802524403480c04018581268 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 880145971 1250 880144721 880144753
    0xa030b040c090617030a08060a0902070b0405010b1f1107090501060509091503070302062203080c06250c050a05012903010207050a030804080d0603030c0308060a0f090e 74
    0x400c4805894512003454200400314403441000000c1044c480c40408500309545299100d1148035444070400030351743c0104009070b6a0501d0b840050240d120119929112894500c11640040750250390070b501e02005441c0758100303840c41c0d005000440043c083c0882c5200c60076101d00070b034003805549a10544001152403840c911805000e000240c64468450900404001a00e03100a100c0a144142004618020b860005900003940e5040710100c2e00ca60300c0200380200307400c02007180c0c0300406110800005003c4000014104041c016090704c2c501e03682c25400039181c0200c101048085150001100c260a208000482e0164890b500b69000040706891f25425101e0405500c00e100051040c2044c00070104400801c421406800a43c14001692281500c0d1100c0d240c01509008044d0001400c2042d154105c9222070340c0c1e200c0400c1150f440342070042010401007000c4000c900e900c0081805482e28604060840c0d0110314080d50582c1002d548101030418500c203040d491144268226036245 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 880147221 1250 880145971 880145993
    0x1802150a032414240d0b040606090303021005090607080a02090a03050d11011512051c05070b010b03091b010e090f0f0c03090a030e1c03030608070501050c0303150a03 73
    0x70410400070410f080122054a0b1801c1404151007032069110710300f0b54009540a400299011070100d6848003c82c51740d003005000c0004205600c50314080f400301d178003a04400038000762806079013210755002c081a203100444001344e910541544c0301c1000220054850b6100c030b0741c00704101e203015081c092182c0c04200b09071f60b01d400443d00e40d04642c080c46812a40580101403294404000780042c040d41c0c160300d420074046001700340c01405a00d4100b014040208087c1001d00490b0041848038130800000800580043c8000c4801904810000413140500000c1c0c0703024412801c0034282c2040158a021000486002c0d0503060000000c420010340d41c1b034041080c8642c100e0a60825a440c6c0100002d941260060609403085400d1060010000d07000807010140d6a06040007e15400507a0014000021f0030b0202c0d5483c0c03d424030610101139051b00032001703c1d0340103411510356688400042d40c681c015504038540541c0700384005252002540b444805044014081c02c40503a200c0d02c07000c041d40e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 880148471 1250 880147221 880147271
    0x10512040507180207113d020d0c08121f0e040b0f16080601030609110903070b0306010e190f17060901060605040e04170d090201031802150a03 63
    0x780002c03030200000e203803014600c41d008000c00d404502c2e0a00561b110b40b0140c13503000c0060301680181c12162044134400440303603c40020800d00401c6040c1d10b492440040c00070499100044c080c1d100403c60007806201c10744201a4031044690078203034140000f16150000034803c12500b085140004840c090811400c0e001c1e1500300c903040c03110310303081c00c15903d40c000c044c0c80500c6c503001403010807004004c5202c802c0240403903480c000142d52110401200a0301640c0c101d1648185012068451500319000501100c102501a00c021642d100c080c40c003a030004948060209102c9610482c00e85801400c0c01c09444814a4258001ea115451352031400e005802c810001f00303016845208040c3c041040e5540f0441840c003d00c00d603400c3c42c0c8014294012449283d01c1c9a01e8a0041030402211b0034618a100e410051066126541034241c0405803c03a0f18003030b80800d10f01182c000d803a1401d0401d03a00490b40141422240c170040d00540e490340d030320128041081544e50729130540f0f14560041c2c1c101c3d4003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 880149721 1250 880148471 880148473
    0x403150f0e03090a0b03060603010605030a091a0108060703330807140a170705060c0f0111040f140901060e060d05010306020d0f05040b06040b04061e1508150603060105120405 77
    0x280c00c582043c041104c41079000414888028000c1005035030f100000c0f241911b0180c500a516600c07403035006009810707482d500503d5805800b00d000855035100021504a843c61030841c0d0454840c103130b0a40803110303144082000d074a808800d1a588120010040350100781c003181000320559920b01403400d0000b10303080baa41443c1040762001561070080e100d407015107201810800340b02d55609145940d07095510486002301c6003c10030500d400c40034450081200da00c0002440311101505c05080d9546c03250158100001d180319011491200e21900e150314110080d241d08001d908194040d0740310320445003030a60143c81041503540481041c000d1500841c41000d0258880d20b51030002016100310040d4140f201d403803d02040040ac0c0d5031902c0c180c02410607140008d00644084c0070030040c10700d642107042d01080f130300801c0c41070740440d124544c125500028845d8030649500c0040f101c44505941220541c0900b19017560280b0700000110303080b081c1414103d1408001c0419807040c084125030075906 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 880150971 1250 880149721 880149727
    0x210304090e0606030d080a0c0c0b07030f0e1506060c01060b0c1f020f0a0305090123150102060103080d0213270507080613051305060c0307091a0403150f0e03 69
    0x2500c5000c015a6410903002c4000d0510b60621710300003004501c00030140d656007510303950b03e500700c10700540d00d0080458202d1803000817483c214034060068035041c8454a1074520b000507400300c0400c0070900743c40302e20420740d1a12964451a0420645030018112601c5039560b9810000e80e00104100501d0b69880120140060450a012104403128420f60200f003190040210707840003501030007110741d204418140041d031626188506401400622454242020a020b019003885100911284144100030038600d005803424012a218402888002c184a00c03d00c2500e10750b82054000d0010840e03150f20b000e0070280d0300c241e400d00c00c54400e0040503103400058660710b081c12545c042c1039880140c60810b030b02c440c105071002c28507483d0b0b01c012104c2d80d40e648201084c010402d10404290700b40e0000104d91031070034814200720907548151118408103c07050b50010b00b107500c1ea0b80e01101c00c2400800305040c01c0c550303100c2c41c0c4014149081e5046440d41c07140046050081c41c82030000c45a242001151 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 880152221 1250 880150971 880150991
    0x130e01051c0215190810030b010e13060c0c0611181e0901120219060f050c0a060501090204050901060c121b0f030518010c0807021005070b0a14010b07020a0521030409 73
    0x100045e0060700940e02900155400c1c40400d4220200504641103607142c05050398032603e0070381d8500c3e1000d00c020445ca08002800c1c4245a2000b105200580103010801014071082115545442803194481580c0c803021200c401c2e034540a4802000011040c13400000001020005117108c0b200342c210089014018000c00154103142116105490f145062044a41d080c0303040640300780c440460038401c0082c0042c1055000c00c046c4100c111460348103405008550311191914081d41060003080d01541c0140b000140d40c9109030a0341a0941d000300307030034405040c1d46104841900c1c0c408480e28a2a03000707504030001840c4105901c1001d4041d40e501034580040c02e00090107903071075400303da0410084100410124581c001103480303ca5044904140c0349183d414240c82d203001d007800c06000640080d00700041c10303d0300d41020090880061002015a881d41d41c0c40801d400f618101940261026a060025040c14161358181e603440c00004d402542e107040d0511318540c4580c0101d40c3e03054491100361 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 880153471 1250 880152221 880152227
    0x403050307110c0306010b03090102361906030203180d0e03010606030b0105041203020c0907090905060603010605090d020f130605180f04080d0b04060b130e01051c021519 75
    0x910290000c102038420b0740015030011385d48801c103004540780d00d5000008200110025030440c0c40042901c0f000410086603003010442c0b110124808180098144c0007824052402110304480d055040b200009042d0600e44128002e400090040c40980202c3c0100314446404203d00d9035150b01941d2102c0d950303000c400602d42502c03026030000d4149810000045510b83c0c004060b202550f02d40003618800c1d49003410b0803407404e034015070160b03004a8038400781303c2c04584c031035120310640780404402d20143c0c4810f02400850b2209104080004005218208044c90160303e41e14070a40014041c403c0130000c0c5002601c0e1003a10502d0034038080d03031100d0420140c1000e0360001c011420b840c1413110030b8502641c803a0a4503100401c018040100011046c0c804225580700b8080c000029004000441d2940d0101c101030340a01c0400746100407809001411040340c008803416220040d04065500c1c1e110040b2501092200784102e03403000702a4406404114070b03901422000d0a07001d0690407203150b1160103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 880154721 1250 880153471 880153487
    0x6071202030c0a0503040c031a0a05010b03010f03060c140301260106030308061009031a0129090d032c01140f16030c051005101d01030b040311060403050307 69
    0x444509030060080100841c10b0100740c03070780c00303000b41030040d6030340d031030b40b80460000045800090942c0c2c41c805c1388540c604000d1103114400d503080c50301001146d803101007105160100340b007442c5038040fa44209000148554000882c912101d0406842810350076200c181d05804c240c00c01944180d40700c0c103a04031000254100c0d041034202d68020012641903403001003a055005150600442000c010031101e00d204480a0300156000b21b045003541075100d6480f1701d044e00078800c12001c01200030b02d41000c000d000e0080144003141d80e11043c035011048040c814910f515140a406101a41107129524140850685003102d9444420300700982860009024254201d0141860a030203105044e4501040011920103105e44e100c0d07071601e4896032030100d60b50721340c0200017009070180c0350800403d4a201d800680c0240ca00c00324000100f40c0381e91190348140c0543c40001c40c03807c0c403600100081188002c82d140c0150107883c004074400008410070345014410f03507003100001c200004020381e42d40e101c103413 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 880155971 1250 880154721 880154747
    0x70c0b031e0f0601050304081303051b10092607080106090c181202040b060d051803460c020108074506020609071517091009050607 58
    0x48440509102e045000d2402e0018201d80c148640040800c051003101429a601d4480ca51540c0e24141d4481c5801511008400382c0c00640c1010130b480c940c402d01e800018130146040943e12092018035100031160705244044015044c00403000fa040412031080c080540501403031000402d0152030090003100303c0f070050721008100714180508080310341005400c0000c4030880480d8118044032800000c004005240d01207601110005601030448500c0e00207502c100020201803507040d10f400442603da11a0404030321180140d801c50700c40c20034183c50f08580c5141c0e44103ca0440084040142103012401e01c03101c400700c4c0210715404210342c0e1010784558052003903c0c1040c2c0311568100f081e4010620b10000140422840c518044100f903194070b988640480501c0056045649030340182d00d070b03a004d807218405070040c0304012030301c0c468488000c0602d8159660301f03060b10380380b80b07080c4840d054042c0103030261740980784992501208601603050303c0d6001c0c0d4007400850401c540094030b0034a000d10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 880157221 1250 880155971 880156021
    0x5130e1f1214030904090f060b030102030903070f0c03020603070c1515030809010315260607050915040b040b030609071d15090402070503032d180102070c0b03 70
    0x601803080c4500401241811035001800041c040c00000b00503045002d444030075a041407816040c5400e0214030701c10303800e036113019000400005444c00c040c10b0070b03880708442100b525401008030100281d0350b1302000b1070b41400b070149a10074907200d50000d90254400d075640400100c41400759800d1009410806a4841e001502000380392400f8640c00c0c0c41c2c07156807002512108001c07070007440f964004c0d040300138401145c0074020b618503140c0e10411004140b00c0150000500000c40006031280300191180c01204561a02e80c100903c0b442000b00061b01d03a01c01600d1140d0902c00010030019910242c40074240510344542c6915004040c0310b010540113181008100040d0f55104480651030633000c10060150750030325003e50506075241161207071102d000d402520025003201030003c003201442c0202080704c02c3c0a91221310650f0981b1000c0802411518495400c011600c0081c1e88812608501e10040000d41000c0c0151074114082d00b0a902c030002c02c080000401c0207941c00032203803410f4186110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 880158471 1250 880157221 880157281
    0x50d020a09022b05270309040e01062102060f0319050c251a06190e090d0815010f030914070e0604230406110309070513020306010e040c05130e 63
    0x1203010001400c4e14665003c010080c1030721046024400c07907c0c0600302410074019813802d03082c414000c2ca0f041c4104002d0303000c4003543c049035124210380790301c3d0160020300c910700b8180046490a0554809081c0708075901d0101c00c84000c0181c80c0c061a0300c54400c021400b526400c0d4141c035103402d4001940c800403c896005690310000c0c070ba00c1c9441c03d00390b003000301041c050b60750071000c0351406804902d10002c81e048024002a0003103041c11161241402a00307031035289104000940d4229820f07194010780c2c40c02281d1208181d4454041c1c503000c40041d15010501035126111030800103c0d002000d1500d80080300d043c091480b1140c611a081581901c042168000c180101703091071500f00c800084900e800008203040c03210700d400c0890300046020509541e401c0840720f6039680e4185209840c002c4422001e52002d10080d4401e481c42520f06843d10741d034110304070007044018042c91414074240501400440100102030022070090800c0f502501a00d01301825003012030030050b8136507411480c40e8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 880159721 1250 880158471 880158481
    0xe01150f020d0309320c090106050703030c0203070204020f1801050f070b040c0e010602060702011113030201030504061d0d030b0409030f0807032414120601050d020a09022b05 77
    0x1558102d41d1100d8640001c640107285000d2124102100d03070480b030920f844440c05085003a51070000780c184002022142c6181d00c40b030510190003002d00c203420204006020034004240250805003103503000780f05992502203540d00040481e00040010b284000020400032550a03050241600c03014007400c04030304002544c0044006417080b480010072000044021400f045103440c600710280c0b001b0010080f80b5a100d840080d175a0b1011210000190308041d114007041090200304c400b02e1802d12419140e650a40e0010760161070050012580140d442c01001d07118485004061860010303040905130640d40d8050081c25074889072403840c4600e1a002c58180082e1704819040080c2d070362030801040b2980d40b00010f50050007246030402d550b00d00d40c400300b515240e2000207031007a54441002008030b4480e56060010007020f02d44540301c284e1000d401400b0902e05040ca6100c110300c01012140340d10384842d5004282d0700b1098203101804032000601c40081d1400002024129815400308040c2c130704 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 880160971 1250 880159721 880159723
    0x15040e0a1a01031e0e07080f010c080114010507110f1f030c030506030703061e051003150212150f1804020a15020606040b0f1008040203100b010504031101020102040f0e01150f02 78
    0x14012104c81d031aa034450b050072010b9410310003600101a42c1c070a6494020204640e80c0c060031601c25144000f070f102c240086400e10041c60101055141a9200707424060941e4031340d401c1e15442c0141c01d038025104140b5840d695941c00c021008904003020705c0f0703103154101e6006810390b81511130100a1508200411a060710001552001c13070341c106201140080c0044c0a5128010900200016030384c201820800c5070040076020f01c0460741b01d41a84626001c15541c0c980481c004c1c4402010f410f9171850104201b9164200d207120842030080c00036400f0040308001a45440d800382020320320750b011000704015884d24800d280024000c080503000c01d0340280c40025100e220003454644141e540e410501c0090f120b07005580c0c0304d00c80190005071040c2d400d43c006452020200c0c0c0491185c130800c014502d500c000b0b80244010644103071152420701d0f0640c0c0d24002c11119922847e41190340c24800000c1d100040c541c14801444047c014040d50350400c401c61405086001480c2c00748900b0101031071010794 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 880162221 1250 880160971 880161011
    0xc0d020f07052d0d0605041a1611031306080109110424090308070303020327120912070b030106021204051c050106080d02030d0f0501120215040e0a1a0103 68
    0x407603040840707408041403550f03242c82e102c4100c006070800b44000da135408200050340308500980c01504c03841099012540c06c1400700200300c2d40d1800c006400d80740f020b0400d00900100c4102005e03a81074a00740414403c20b81c88166640c2d12080000381d410b80100100401441103046070020202d50518060600052078a0546000c080f06041c004115000c1030b55071144038810040e507480034000e82d07191080d04000f4060b400503546003082c922010b031244290000010047d40030305610000d4007814461032100034058206104664001d58480c11004c03024400f0320050001c0d0119107100ad4413541401c00092074403d000148441c141c03400c02c020b2080d59959582c5ca00040086803a05105014514115016210075401140b162007031040c180300701600413010b82054a548442002141000d24800301610801c1c0300b03c60841185030540d80c00340c18415028000a007054502a01d060b40d204481103800a0446117006103960351103500541c01e8130620f24042845091a0600a41c2ea41180304401c1c80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 880163471 1250 880162221 880162249
    0xc0509040f140c1008150f030607030903020f030d05040314040b0409020702060d0c2a0b0c0304081b070302091e060f0d0c26030418021e0c0d020f0705 66
    0x2100350180c034954800f00700900e90240050144000705401420161594506452480000241d54500d080908110400c0c0c5204030380100200b9240d00d540005070000d148400065046010f11000058880b204100512000c5040900001c131071925050043c42641e0740e42ca104001c0004020402c416201d40003541c00f0703281c02100061351400c440c40007911600c108010b50303602a0a105105641d15003180d081c2c00300a03071000e60407001072051901d80c92040c0d0a00e000070007130354120010501a114940243d80d00c10300c680c907401e10b0611003203050240c040041c8004d034603551100c4414400c505081c04c0c0503030881c00f4a92000c91004e05100c036500c9038240140843e008042c80c4a02c40041c0d1384080304800c0b210340003801d1180c0b803512680d4140841400f8020560010401002d4680c0160300000f1201211903515a6030106d00e01940b0003c081e41c005c1000800300701030039042202140ea0030b00100070882c03100c0000c00780c01c0320000000c2d042c174290300c0240b4040d4011002c10045900c840512020603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 880164721 1250 880163471 880163483
    0x80c030f0604110408101509090f120e0a080607120b102312041101050705030a0c0203100c110c09070f180e090d09141c0c0504020a09030c0509040f 65
    0xf001c2c90076407100c054000c50788140c080b0300c10f840c0301c0741c0c4103041548640c0c5d0501c0240c05030f0f040c0b280c452030403000f0b591600d040200a4500b1090700000301e650980504900e0081c1e180c03102800380d210f0001416410103070001c0019070000c800b07008682c4c0d00203d01e110b400c1c030110f41c1800401141c100140081d048403001a0030f1069402e034441c1240e4481e4141556110004202c50701c4d0b41207180e0140800004440c21207400208410f150b03071540c0981c082e0707184079038824000c40c64000310010031540d203016400708903054491700040c07400f0f0ba0790710b001d040380c103482ca0307600e03684031800341400c0e00d2401c00c00c0c17803000303010700112000e2004007603021607001a0f00b21a400e120701021070301c40d00b030200203000e40d0041d0011800c0c0c200f40044c00d43c001c41c080c090a54070740c0d00c0c202510b8580f01130784680b048151003030358055070600881034091900c018000b00c0701c1c000c4000304c070b1455541011609070b0f4000c240703020005d4481c90042c002c100c0042010700c080c0c0030070741d8030811a20341552081c0c621804010003802c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 880165971 1250 880164721 880164731
    0xf08011a2b1226010b1611040524090108030a030905030408010905030306090115050403020f030a062a030e1203040f1209091b0906050f0904050f010501080c030f0604 73
    0x400007000e0340e480c0540b035005041404600319068010442e000c074a207124940c422548445001c140403400f0301e416601c1400c402c51400d0072030801144214019201218005c11408000c0e0350b0340d0341d83c86200d114141201c291005001d82c098a405091030a44c41c041c0708060780e1006004003440042034445081160400048450307150074680e2450060380d00c940b0a541c01d294101c0104038022000d10f008860954003106966220302000d074003d001c80c3d8512001842c1030100300090f1601c030325030004e8840c01906840300c004280c0c840c50140d03681900c040e940040c8415000c0c1c42c00c0d6984000008490301c5240400106240582c0e80b9120005120443c000a2000c40402c1c1848004458814410380c00142c1400010740b061010303001e100c0521546008501d40480360301310f04038004030001401c0c62595110703103c034108881541c0c55041283d5070f0500030005d1000349915140c600c6014010424081c4a803600d40c501400100f41e240000c2010f81084000d0050100d00c030203400c5100e4001904943c041a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 880167221 1250 880165971 880166029
    0x12090504150b1305060d02040312020715050a030608030c07050307050f1e0414010603050402010806041407110106050a0f030c081603060e0c0405151806030d030b0307050402040f08011a 81
    0x40c80d00c2c0c135005958001d80000c1c003c0401407580e802401201d108560b2040112000082030b40c941caa5440380307513807491449041081041c8900b00410b60712205060001d401602c031078400d80340d60444070110505a00164052255103420060314006140c2190548107820f91100030840081c0380641c241d824940c1d000c0007075071550303a41d042444030f469141c00451031903030b42d41c5005000e13007809d8034241d000c9102003000c1080750419005131111102c0601182d5407a4540300421584c884401d4640e000c41e5580e200c011600e55501c10101c4001c00b02c020440c2030a40c110300700311452880703691110302d0fa944120804407240c185140d10714200e035080340c000a80d004084102e40d0401010020300340e817280ca840208100176005152a02d40a08181c1d03a080031310952500456803d0b41c1510665419400f0308025003070b0b0343c440e402064250710301034280c802180c0d65001003000c0c2d80040e04048441c4500d0001407010301000d1190200d0305148036006403103279404401003203410003900030328035002c080650410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 880168471 1250 880167221 880167247
    0xf0a0503040809151314100804050f06150a0b0903061b13060815040524040e1005090607021b0607060b15040602070501050c100903180312090504150b 66
    0x911402c0c0050298200700f4201200800b440c5d00451030342282e0414840045100003aa0500c4200c0032405040054480c40029058602c004024000c072011312071480013160030807050015902032400c542c113118051118100308400600785400c2210007101c01d12400703030359903000034401d500140c110740003502c0040110354505551240c40400d01050f03100b00e1001502c7d981c071071080761007000758400340c0d40d000071804104010794805403041a404507845522f140081074080644410280003800000d10428010201d8184040c040800400c560390300204244000140941b562240c0c251028003440741c58004c164028400c900030580c01aa40490b11208014032079100042c080c40003043c041500c540b40d180c0c2d0003039074403e024500c0140224400041e440d40241d058400451a05024001508000c0c429000605641c10160100b0515102c0090395034210400d01000d1401045881b40b00749031460080c0002e842da60145010b18500000320503d0328480c89040c040c0d5452907422641d032106000c1803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 880169721 1250 880168471 880168477
    0x30607051e13060e040903080c0904020d05010b031008070e0c07170d0e100606140309190b16080603061f09110304020a05190311011205040f0213020f0a05030408 71
    0x144200340009009840500c2d5580440111100d540e0781d207214130030400920082e10380b41c6d00000c1c040b888130b43c0030031a104000400745c00c1004002d0f000508083c0c1480552083d0741c0c0a038040403074408000144288074050610705000380c89900000d200c02c515082149615440040a401403041c1c08a003035010000e58030041c4110382003207501951103d0600500d14010304000c50b1402d507600c1800080c00850003640103d00444003141c4030000b922022220b2007405620080901125001d451680c0743c00400c03400584800300e014900468280c9001c20004003080303508a02101888031344810032242c0d5400103481c591010b2490b0f84580c0a40b03810f40103500c2c565513504000c25050a0204480c045843e40014500c510300850307501c403a007540c0d0300a2107620500648441100c03c031208040c0b02203074010407003184160061500d2410340c001103200408445095508484426280d035107141985002c0c501d0041d6601e072941c046150040812184a251080c456520248440880010144050704003a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 880170971 1250 880169721 880169767
    0x50d110a031a0f070f0e0d021c0b010806130f03050d0b101812020a030b0705070f0c030203100506010e10020f03071208090d09050904020f100e010e060903060705 71
    0x10740b188501e000150b840d80c00100c64920040780c1110010703203428865002043d5101c81a2a6082d8644244040c02a0000d841c841aa0420081203102c144ca00701600c2c04000709010340301c000342c0355060100f041e0510748003405c0b1000c0340d01040c84c3c0341d01080c00704016645e103a0b0b250800c2a92a603603002d48402601114206c0d9a105070162140c0e042c0542001e91441c841d1783d0103400b0300d025610341031000c80041c850800030790040c40c0d00c20140000742d450404507401808501300306003046211380c4c5032a50405256411620500e6050040003181020402c03d048080e00305810f110030b28010000a10340c0c600042403a100e0058940e26003038650003841140c01d9080c1000039259900040d0524010044241c0d0300c81c0005004040000c0e24100c0114281c0841c03511507032698581031404007000603950015006a81c841e044107034080705661520240c403e1a03107540c40b070918911648001411380307030013844840c0c05004204494074060f07401084e001d0f8016450300300652140940b0740740700c4040c10b80c104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 880172221 1250 880170971 880170983
    0x306060f0414041506122a120f030e0108040b0402090a0603080c031206010915030b0a170a0c12052d0d0905090a020c100c0329130501050d110a03 64
    0xb80800e014a0420701c491880d01c0c1d00050000f195196420104104110b90141c102d86000504e85a4403242c100c2c158040c00c0b03094071fa803079030741c0d118852141107883c449001c90380a03006282000406400c5031200b981c040007401e00684a02d03107900c0d02c1e8201100140003e10032481ca00c00140c1d4030405a000750003a5420107503a649518200020039980d90203002d40d8440000581c000900e25842848050192200201c000303d81500d0f800c41079024000c16040c440d44003600180201d0041d6041e02c600c040d080744e00c0001c0c0700d1002d140c14203401c90341c801d0304000c40c031901d2100760001003400003410441301802c161540c003007050400c0c1011408540c841c0c454143c2d01500e0241d001c030b5a8001106000e6910841e0758100301e07161400c07000c00320b00c100702425466411424442c842496580d0155038140c5040c100440c1985c2d00341c81c41400000700c051801d8081d0088004220795080030b40c074040055900b8007081289504250010380d4035111107200500c500520a60031410f521860000c03c0259403109d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 880173471 1250 880172221 880172261
    0x260f131b030b04050c04020304020618030a140607110d020a08030901090b010e0708060904020108160e0402030a02120a02040b2a10020406020f150c07170f070312050103020306060f04 80
    0x202d8070440c0300c80250750540321403080325507210391460584212405550300030141c0d440c003000c0b8810544c1c036220074201a075040c025903100c2c80101f17044c2d5104c840b040e035582c809000c880c504510054190074021208038a00c2d8890101c0400311500050800b080c1500402a19125075440b0b00d0079001d0101d17400c0003440020130b0000003d40316850020385000d01c4c5c041e152080c0c1a0384250a0108038901203034017900207400d0001081500c4280c2840c0c1451042a2a0910748071241c8400318040c1d03030081d00e61241a5500060003440301701003011a9410140400044d40341c07030714150100d40140100d603120b80c2c0207603208408a007a085915030201003e8030503010380700c01c1d0716602c0c1104002d4201d4802c1d4800340c00784076184030216001094070740304145280103198841d2240207030910160032210085601e22444806e841c60014048040c081200151400a0341d440389881c008081000d62074940c41ca017402c00005000681d00070410551040042c5c40d40c10b40660504001805007070314242d0701031400010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 880174721 1250 880173471 880173473
    0x110f1e04030c080f16031202010e0a0b090106061e05090d3c0c03290a060f080a0c090506132f1201151e260f131b03 51
    0x11106000c54003907806803013840c1c941020440c1c0303825882000d01e040c00d140c00d40034400206400e002c6081503420f88000948000040001c0e464009582c0b01520000c0c0d0306010403942d44424064007001d02001e00e013030101e11045100009414804001d944240603006c1049201520344600c04100b99400c14001000752000740058111442a01c1720f1000c031b02c142543c0300814400402c802d00f1008c0c1d004404001062440c6c071191030307100b40e0303090410f030850740d44c1e612250748030320701c00d480d8021508020001400c500d001410000094254040010340c0c0010444601103144c0a5031030003102d850b42d50100c1da5507582d0000a07401300f41806005440d41ca843c80c994007a0381800100d12a600c440c0c802e291a40100c075044035801d0061020024495521000511040164a2a05040c00324600f002c2d140c800c0742c5404115110442e62036000022010713011400d080110030020750001841d00c0344503c00d41010480e1044609008007406025103045080030100083c2c01c0071030310100798800ca880005501d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 880175971 1250 880174721 880174733
    0xc03080a140304080706090615030c05210d030504170414010908030412170f040305060a0510140105130807090207060e0601050f130e03030a02190201110f1e0403 71
    0x100c44031000000d04040d064a039040141002c42e07015036040070390342d800c02e00f2641c0d5038400307805000d004541450315002c0c0900340c52058074940b40554410070700540b44a04100900040403020007040d08004030300c5120110000d0081107800141440b031901150b1692a400c0034170604c040f0b0041d107440040c00003000244403000f0442045400b5090340c40c10045643d9088681ea68091406108103014149400000194170030048001c0705450510075810000010306a1f040c6800c580c0c402e0703401e50800010001c215100f40b16456000140c03202208c0e000e0f00340040154104d00707018281d070500c14000b404040c0c0d02084800000240076850031505901d40390030b881806034200b080d0031a00a42803482240e085040880d46506940340070748100b600849910800000483d542c1c07090400d0340d07542600941c05282030005500c41da02c40320015030388841e00d02c2c038018141081c24882e021649020030741803c0c525520100c4e0811011030242c81c2d00c80c0ba00c0c0c291401041d03106500800c1d82200040c8c00020010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 880177221 1250 880175971 880175977
    0x13050a080706020c01380d0501090807121e08190903030b0102070f03051c050412080301060905040b1503060a0519092409320105120a031b050a0c0308 66
    0x8807110080c400c07011a00d50011081250206e440f10100001c441070308038040d1506010540b10b0300601005280185407212404c4880142003500c51070000240c080a200c003006404042c08030b503180a01d44440350500780503106540e6190f080400495402040c140741200c101d000d04420701760b4040084213a585800b60060480860032405401000d10028244900b8100316046940000150055960004a14800410152281c4d0070301006000206016061001000650307100f00e0322555294101000580001c2c200d6201d5842141402148005612141c144e07071a83d0380b40d4031400c2d8807503c40c5000122044416000541c0003600054060940040801d200c13040b00e90882c030070008003015100609100e40c030885490709210629800b0000181b90f58424040102280c0c1202c100311281d617201698200300c1100381c18808682c1c80107115502d41403050606030182e900080003051095600500640c181c0125404811106600d020a201e0107001c80e000155004401c843c62030b4581c640b0040d85c0d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 880178471 1250 880177221 880177237
    0x8031009180206040e061f2c010507030e01110a0309170303040201140a140a0f09080303010609030602031b031311090106090e0417030717090304050913050a08070602 73
    0x1a080111103a00c4550034150512040d801801e80f0385030a040812070702c050750015141c5900f04250b8100c0005020308005041404001d5603901d00e15841140c09801e1541c1842040400600418141000030f03a0460b0403104140d9240c1040c03c00907800c207005032244080100005120302803001341d402095840301d414410364180c060b592013040b94035130949a9078002224000d01003070903861401c0300031041070040c0c403520010303203800081480c01c1750505c00142c1280c40b2040104040485e54240356821400410141901800860942d0303d0400010251180c0340700181c030041d40003003c203540700310801000340360983c03100d25030f603407400c081e0302006894045807025101c140d0b04503d07070313800c07844d001d40701c2412500d50359030300c041540c04c00f18050041d690280085600e2103000c0640c500242c5440040c51180089031134400b03859074800c3d00040c4a400091110007150410003080c0841c4ea0341da6202030308000340c9000240111450f1410610305030010070085d241d035002090790300400500d41c00a03c0300e2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 880179721 1250 880178471 880178489
    0x210e010c120311130e0a020c070b030406090203010911132703050d06080601170102070203030301090c030e0a03051b010612140f010203191a010f1d1f08060a0b07021903080310 77
    0x17554034680341404900403c4104007a1360001801041001c0a15000d590842c0c010400002c000010f0390003c1c2c2110ba00400440b100070041e078003141e4615003006142036450358140e09118002080c8010341102d4030603460a0011600381002c501030520035402d482c458605624200444c0c1c0e19050640c0d42c81009100f1100500a403500e14420702006000355100c442e4040c00540c00d50342004981d00c0034000c01c4c0c3d1090101a80c412000b01d00078020402491560700035140c5079500c1550308180104a036000c0c0380c240241e07040103010881d00d01d000101c0031456400c008040030648581c0b524a04011020003080700135030000c000c2c000141c1c03401d00c64a0841ca8001410450030462800807040c510110412601141c42040c0c20420680502c06d00400c00720816240c8082d0764220000a40000c3c241c00c1030006c001159400a4029401c85e503000e400002c200d844039040b51601c80c20480310321600b90020301071201c030420014403114502003200510f90240c4015224901165032981100183c842c41c648 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 880180971 1250 880179721 880179749
    0x609050a0b100503011a071509020918190302150a020c0c010f080a050406060b0711040507090308040306020f04090207080c06060f130e0309030604210e010c12031113 73
    0x18a05400c40c00d4404080f601d036503003540e1900c02c02d00700f0804100080000070a0800c5103000181e04a41d0400408001d9a80058140c03400e0050150980c002000c588400c492508140c0b440000003580c40c8649101c080c58452030103051600f281007500780b5145002c00140842481006056034020304800c000501c11100c02c1c50482004541d401c00381941e130008101854013041c42d0f0442600080d038000d000f6100401c56903910001d8030001c1e80070304400e0703550b001c01c031240250502d014011207411400c01d00c0e113204100d00310380b90540f02e80700c0c510008046681c002151100c04c0400401ea900601c45400115112a42403c01308100d6101707607400c4440d406000e0000d10740b890710350740c4000b030124050b00f01014108070f5880107004040089460f0043c1c8802d0001e10511b5404001845c400d03071103400b94a50324502400307282040c3d0344569041060103240c020010b01a64080a01c94400d03070414051701c60021440c0068004015501c0c041602807000118802100540060103003154085580280 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 880182221 1250 880180971 880180991
    0x7062d020315011d150a09140a060507110a03080c0d0201140a090c030821071d01030b01110706110c090408041a1c0b010807081005040507120609050a 66
    0x8224401161034105a0156500394011544142c4924114500ca014100705028880d00002d403ea50740c83d85518090300e001a500706920f910080d2400101560148040308a19000000703100d0031031030144030108000450100103010b10404082e500c454090a946882c1da00c03400c0059441c1e00142464001e0710443c400f4104903481403052400030030007804000d4440e120109004050800803100356070108900d10044042034080c0028129071060b8600700c1ca0082503a80c84200054009100d00140407840c1d41c058068007490f00f00b22502035007460b002a041c4140401a500f001c1c4c00c40d08620755200798880031074a280c001c074601300c01000400442e0f00103a9a00200300481804030703801402c10809220401c00c0c8031518040d4640035104007800f501703103011a100b05924103412540e0544007622071211030040d50b00003004035080030300c034640b0030414508400c021003032090300d10419000700d0b52000002c00d01c6101d80e0818051551040e03081c0003096032500e00030060b04040d110390035410300e0150501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 880183471 1250 880182221 880182311
    0x2090619030f051e150112050c090415030c051c1a060a0f0b0702130e060a0903031824020f0c0303060312030f0c030702071a0d06050618060c01020706 66
    0xc0c5203c0c6540085404a030f0b1103114004405c031250031854184025848030b07141c0101d075805290312807401d6600180c4c59034080e40402040e20303290640d5030740c04443c07100c0c14808038100180000030358074103480510000f8100e005003c020b2900c0c0c803010300b0f000d01092564910b988801e1160380160011110090400c3d11901d41c1040c0010501c11842c50880c1000342d0300040c2448941170b8104a10100e00040b4a5481369002e800c140c000c42d40c5150782c81e900e213082010590580305080360030340c0030304002030b17034803107a9442c20101d040e03101d46039401b200c03001c11240030920349404030394032403020402c0741d0340b620000304540750b40380c00c242c54142c401d0260100201030790f103038502901d104840f402c140b002d09071203280d4400166403018004000314002c0c43c20101d9034400f541442c10f038003021048803c0c2d41ea4003050641044071110342240788640010041008144018041d11a1107001100c005070f03141036200da980e00903c191400140010704001c6024014181c000c901c0400c0303040145220314090401000c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 880184721 1250 880183471 880183501
    0xe1009110a1413171e1509010c050307030f15090b090c280903050a08220311010e0d0b01030f021002030a050a032d0b0f0312040902090619030f05 64
    0x81d07081510714000c00c201c400703408020850320441c19130551340d01075201601d881005030318006041003580700903d006107080e51b0482c01644211104003c001e81300304400000d107584000341c8400100740d01c4406011006402c5c0c0e001000707000500e0008016290b6820060020f0603d55a5092042070048002200008610704662051465034202c06000c1088407624010750f848009160421000c1400480003803401c000c05a03c0358000c00c0b040340c03550141d40903080941ca00e00030600d50f00d00300c0c860400005000c10a4146a10f1090826005542d40040418034207800e0a001900300c41c1074200010034403070402c1d242c0020900940701009d045141da041a40d59209560078640080e00412030f043c2c0e0345100f42d10000c07880c80d1203070346100c00c06549100740d0751400412002100e0390f03544101c010f4007032030009a1081c1d9400309501500c0e00200d0409114007a000c1e80c41101306d4141c00203118402a45c800b011200403841007100e0340c4960903640c03402002001950140b0300034034500f0780800c480d640502d2403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 880185971 1250 880184721 880184737
    0x151514070b06060c03040f0e04121d040c1713050111040b09041107060e07150e0306040803060a051201061a07150b0303130e06030705010f0203040e1009110a14 70
    0x107081107a01d03000c2c24890b00f0b07808144c907004603001c1400003145400d2415401002001d0040d17a1044a00709403c040070140b05151007101802030340d19408c0031115207428108040c01d4104c0d0001900c6103640f005443c103021449140140f0740760581040045442d071500c001102c1e001d80000c0000b4100340340900001e1144c2c4c0500d181d020350034004025149082e0b0000c920080f07070b0600706410401c0c01ea682d80162128010000816004403505101c20004100c103c0750010340c0b8500000004c803404003103500d601e80a000030380001c10000000c2d016440c5c1041030001008050140d0b0101c00408016500915560040d8980300c0e1a04401c4620310303038524140d0710700039000100f07a10b4080311102c1070801404001d440c680c0500080c841403015007100c10140c0d00401d00c4500c1c1000707920740101003604101b0300c0d0700aa818000b400d40c2034031100340c0c0042610180d40044901c160a900d80114992030032181d030b44103001c814204102d5901030b64000020f01221507268503945a1300354222140d000034018180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 880187221 1250 880185971 880185983
    0x1c21060f09020703020a1e1a0115030e010e03031617010b160203070b04090f0605040c09121406071e09142e020604030f02030a0206070f020115151407 66
    0x40203001c10030581c0d00801c8281e200e40100c07034003c2c00342c1c1d44450700ca03c12600c4859102c06805140303014405440308140381c907104582c8001c8a98102654038142d0510100748800b0175541d0326018080d008258401c0f450005800c048035124a45100101140c10502901e540007940c50a01c030140000a44840340c1a02e40000c451030903c0e014640322012500b142100341c0c0c1c1840340020006190024000400142858070000300e801602c0c102c443c800d5403040da000a004503e414480001140d1000c201c80a680c005064007428150600b425400306800b201091881d0007940e081c41540741d04448109a205100d19440d051503100700b00913035514445214a80000100310748000d8149041d2950100080c419004a03080c2c0c500440841802401d030880c080140c5d100e0340520040c580c1000c814000308106100461810801202c003e480350805010030702800045400c2c0b0915600079000004645000c1c080300c011103994041c941610781c0300304103260208403030704040e114020851048588d0300350052 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 880188471 1250 880187221 880187249
    0x80306031e07091a091f0b04050a12230105060f0619081003050a0501020703030b0901150e0f100807080c0a080c160212010c08060d0302100b031c2106 66
    0x20f00b540c400f0f0610803000444c031801c0c004c0c21600340d660b1010f082d07010712a441c45a8039001100304c0b8489030741e445900003110110007400200041d40d1000080c030241c9101c806100404d01d9540703800c1c001c244005480300d1128030220101901c501c01503008a00c6094100c42e14a064940e8005024480c403c0d00b601c0d8880d800420348184045005018480e008080d02030526000c561b2521801c1c207280d10224111840d9400140745410b00d40d250080740903443d0100d0f0701d09501e51404d0b0039050601c5407210340d0410b021101c43c0303803400c81d1386c0d503911070034015001703804840034103417405000308000c03000c58215000c110344001203141554042c1c2519000710342c41d02c0703258940c6c544400480041c4c003c503189024081d100111000182c03141d03c2101020310130f420010981030182000034205c00c0c3c00802c6140942039207410100441d40c00500b43d2061106002c0000e02c1031665004a418140c188101d840316080b03126460946175801104031807003070980004040e4503608030389107000b95035081c860489024005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 880189721 1250 880188471 880188479
    0x31e0f060d1103101a0616140a060e1c02030c0322030210050d0b01170105060a11070b1e120117070e0a050a0b03010506011b0519080306031e07 63
    0x41001c8580380186540700100e4251030000740b81c198004e4840740403949405120307a08030000507880510309022a401070801008010405138549041d4010f044042c80559180e944030081c03000c51a01b40e00f01c0b50034840b101507000e2140c8d440050f81c01d5032100c11518603074030104910101c1a034480002c03540c080c1d464402944407400702031844402800b544400000d000006903035800d11180800071641760345841c2c1405011f0340d8120b442c0d80781601e05100703000d0f100c54482e98284414a0541f0021203001d0b443d00d0210404580324200705941583d2841181404100c000c0460302600c0d5001d91041304d2100000c1c1851f680c1040c2c044c180810103580040001840918214803449540600c2801292942c0e070361180a08400e54080d215800b159070f42d201400072114003805020072283c0190000d015a040035070009100c10020501d280c0800524281c0201300b01c8140103c0b1000c0d54001c41c500603465883c103100200d5401690441d10a104900d0140c824a1981303003c1400d0554550281c0b01c01850 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 880190971 1250 880189721 880189729
    0x2011d0a050f030304091d0d0c0b0406240b130b040e01050d29061503041218081507030506270a09020910090c020c0306061215010308031e0f06 63
    0x7606035090341800217003c0400c00019511803c50032078400b104030312442a40325981030030940c16090b850300f002000030103035001c10201007410f0340003a4004230002d6616000040036214403809030b1042081d003000da400246402d07000018003074007041c000f00707914020780d20402c00071948524803403100e003001400010056031a21580e141e11580c0602d441d204001d035010003520501c0000160898040c410030305200440c10a01d90780700c1c0180f230030441645582001c0e181d982030100ca58800c401041019948440758004c0c0050000080070b5200c2150000341c10070b00c0c41102030100300c0b180c50000e40b9003030005805280510103607441d103500d07000c141c480b05000c0c8c003044500074004000d442c01584940d11400182c840703600686c4620781c44100d20326401d04024140c0151258100080115400400c4420343781e6000304800e80c00480c119200d00c484c02816401c0b5050040151014840c942070100000521545000840c89a500c85440c1061502a00f8040c29030038016100700d000241e10341d00185103820 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 880192221 1250 880190971 880190989
    0x19061b020f06031b570705040e03090907091a0d02130b03041502040617090a0c0b0a02010f050705180f03070b070605091b010815150702011d0a05 64
    0x90b04c44010781e1030309001203403841c0d40c40100d940e4000c0540c66a6030303a100701e112040144d02141c1a8000c0d0625000407020f4141130b1a020707240c00e54591003c0d410140c08030410282e4000d0030094414020885980581030b2030750070079520071b070007480c0c106c1c0041c000078411100c140079034006030070461601c00c1084604c4000d0304807072090404594200411501101e214813100300030b11800807119583d181ca40b0300780d8040c10f1000f100e9002d050041c00180b040940103011a10b4001298544101a03038030303048002d1601002c404094a500607182001c120366144400520b85501e0b01e030024030030329180c010080c049803411111040090014021014005d07034581c28004290401802c00c1e010320030f00c4001900f0044640d000f0075003540005110b40402080d40182e41c0e20008030750103008140c2e0b403078a03802d00e1402c40b00c410b603040201c08400030303119030070741500d1030405880505035800c40014411000f0b8154888502a0b02090f43c000300a004041e034206c248006900203048a13505034600020b001c0029 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 880193471 1250 880192221 880192231
    0x6080702070b1308010f050f0c0a05070602040905010f0f0609090e2401060e09061819090809120f0c060d110f040906080d080705090a030219061b020f0603 68
    0x401003800c002810544038000c1c03c14288842501120b5a00d0a100d007421a01e1708a00b0808007070034081048104012480302c140c1c0b220300b07050442ea031040006000c480500c50100000e103501e1000c640401e0707440043c1c0c04030703050b100700301551940562210001000380303a052041c000000c001c20400e0200840030380104404134000d03000c4452103401000700003a980c0205415407481d4000e00010800c255004c2140d00720408207540c41010342c1030410108a0442c00c90301151507550108000c1001e02d6034034a003425455100310760070401c1c9002c500c0c0407143c13540075441c1c2610034445c1f00807070070700071501246080b40e100002000f040204085030034404540c00c41c60310fa190b01d0b9502c6141c401501040002031405460300c42c0029a5582000f00302011500143c010a0056001858020a00741c10a20042c0c0000d81c82c10225101c40c03003800011301c05015604000e4225000561700f030f03411814030048400352030442e07c0d07400c0215499660041c814149460181d4448a01d07404a2071318200700c00255080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 880194721 1250 880193471 880193473
    0x30f0a0204090807060c02060a110f120615070b0906070306120201080601090f060c0512091507061805100c18061805300106050a030b1905090706020106051906080702 73
    0x241300752515401ca9407440c00381e00140e0041070420010110910504013908035400c6980c4c1000c0616234131011038020414440c02e5505200d02058266607001d00c0d00d00c0e42080d05842c60b540b85402c1c946403114400c16148400c09110340c00110707020500900805043d00d8107850076400e201b241d80c0044a0410024081d581848111180480c0c520801d00080300078000548400b540e450762850003074039099424000072841c0105001098043e03076544940c0c0c01540035050043c0d04c804080c10880000c20160001e0b0040c201035688880c03c000c1c010520700c08006803803c00300f0600304041016120a00d00002d0708015001401050180070300504048111680900800e040705803980d011074410300c7c0300350402d10110f04580c92220003414402581c8800540381c8024402c00e0326003000314100d2800303070200416039101c200001e2205c1d0b548142c04000c1440d020000e1210b070a10161080d01d40340385000d400019401d0810100781e5092203840020300c080c00035050200145480d4044400706c0d4060101011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 880195971 1250 880194721 880194727
    0x120105180a0f1506020f060610091208190c02010e10020705150c0a110307150807030f09050601030602090a0504050606070201081003170d050f1303030209031614040506030f0a02040908 81
    0x3490030801515805007095400400440841b43c0e405c0d07282080042599124514943e5185074007640700d4044012074035240f45e0390701c6c001c44a00d4600782c4c034003640010081590a004415403666031050360340d60703298000c0c1c0716224803401c00028404100901d002c41c00c00b5a00500c4104590304000364042c0c8030b1546941710f035040c00450000142002c820042c1a6404131420088540318a41408028014070410080c0001c20680d0800a000b501d401810b08090641d02c0414020340a0550017160000e07074404151030071580c582ca0584002d401c4203040d00e00800d01c0039000301d8035091510400e40212801000c1030304102c3d4507401140c001100070705404030751250700030000009143c1508180e08102d102c810503241c141b15441d0208948009000081584c0008140105280c0da0031041c07101981521f0050396588600c4040b03440c00030526034658218815100000d066588507080c41500d0f1000c560601458a4a40415a41c3c1c0e01c0c003107004401d0340010315040f00500d8141e021250f41c41c801c030312140c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 880197221 1250 880195971 880195991
    0x5091e010c08040306020d0c0207030c1206060819030905010e130510080303090607080a060620030f0a0903060e0136060f0b0114271c08120105180a0f 66
    0x102c503401030b40c0101e83c2150040b83d2490001d94a008102048501d44001c00007245181c89081000b92140b081034032071040411058280324064100101038841c000460710b0900c244641264140c0c007125060b40043c0310b8020208441d88950054001510024808210540300c004401c1c010000601054040225042c001a81d100c090018501c01c0c45140040d000c00d1401c00301c0506030000040103c4000c0303140071810300c44e01d500321046010780030250300c00590580320001420f142d4030a00309109102480443c1c0c4104040c0c0c445034003015240318000c1401004c40d054405c50aa48480b52405603603510040904008601120700410f4a825807c1c641c41d8041e550700c1c0c0d5422144510003101003a501c1e00c0045d1381c1940c2000c00c032407040d54a40120b07031428480c000b40380d4a4280900410304c005000e11a0202d0300c0c0e59654001c90f0072010341200c1d01030003689290035035031580540c1c8900c1404c200c0c82e000007440c2c03405c039528030b03103981d1241781c117000c0780c1d035480c011030000d00b4415011100565070b241114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 880198471 1250 880197221 880197233
    0x2040b0922141902041a1c06081f0e0c2e0527150a02070f080313091a01030b18090120030907050910030f0b0f0705091e010c 55
    0x8002c94100008544a0341000c07858106821082400345450a00410003044020440c00307106845030660200140c49020322070161100d002ca20b81a41745c86030074488085004000450503241e60303c60004022901c0a4034a4000d00342c41d030709401c11886030800302c120b1419050500304044901441e4080c90102025508a01c5000300059001000070700c0101d03c0001d1452881c11a0940c010400300c80303105c45618000003100050b250034012a611004241d00b22014020400d12026140014203114815120f140195594010b0b000c8842c6403a42c0303078800544284036124030010203c00584211207241c0301e200560160181c03c0103103070014034803d101402080031130315141c0681c405c0d0700080b800655000721041c9074040c031055080c07001d0b010028400740304000221181296010303500c810742580c03644891034480d04190700c0500484070084280c0100070700400d04c28440c0d40300780b80d41d40c9a0b454801c0708072664021440fa0541011441d0420034412075070810300c500c8402c05240002c040e5001d6500e80c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 880199721 1250 880198471 880198481
    0x5070306050907030c050306060a29070615060c05032b0504030e09070207050d0b0c04120c0e130f0311030f0c0c09061804200604030f030f0302040b0922 67
    0x6040b00d0341010b2020300800c05d02030503960007030104400a00c410f06041c4009000e150041c42002d0181444820300040603612040080e1091100c40607584c0328003d5041800243c911540c0500d000c5d40140f00c08114903020f004c1c0c2140d940d40040086080c281034541084ea40008507402c9540c0c4008543d5940c400022400360794841c612941e00c844c000302075207090090360703040940805d0035508506810711260b1640c855100000b41c0002002c3c0264036400c420710396510468108400c601c003240401b1060050307410900084940d8a42e00d4455540ca07440c04440380d02808900030495000451004003280c450724815203064500426a80f500122054800c036941c00340c1020480c0c0d82001c41d00c18618500480016032190080d101c44200c0020300d854018040c500610090003c41c0e94550380c10b1400300c0f00d0b030340300381010040c1c2190b1313030742d030303c038108000d694801d05070480c0059540c800303a03030721a4864002d03034007180c0078841c2c150f003050054420410300c0c0d0b0403220305074150001480c4800f000c512900413 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 880200971 1250 880199721 880199731
    0x9130903050a0f0509031b1315141005091002160807030c09092f040203010311090a090b07031a13140702070b032d0a050601020d020a0f0803040507030605 68
    0x7485554801d80040940400d5201007030b50306108040c05000c0711501e000c9007412021000745640d405a41032400080c1040e40220010059980741c80c5800842d0b526541885083d02c002291002e5584800d20400810707800c03115103400098801c8c03021041c0f13824400c8905a2080c09030055488020011480450581c1b4640c81026036521864040090248004158001d0010340c3d00c2488040410b0711118410052525154420003510a1600c4100c000c031a11000102000b0700540d40d035696424004940010380080070b1180b181900465201200d0340310384c9a590b41c2c04aaa07010360380e5a01016401066680001c010384400d04511000954421415000011200200090218409141410041c0002c3c20b00c01954041c800c01d0141510041c1540e0b4405c03d01c88008000c8400e4900001196440650b8441d1203071000307042c00500041a08a1072081c2400c0e800c88000d810142000c07640c1d5004c2010103004015085100c4000c11102c5000b035a1142c0514110341c1d040b90303207070307203030001c446040b18 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 880202221 1250 880200971 880200977
    0x1203050c01180308270304060804080d0608240f01031b0b0d06090e12040905060111030d0c0e04090b041101020a0b04141212060d140102040e0105040e0105090d0509130903 75
    0x3004280e4915145041c00320366203800c030512070810817003011343e648180e004030070501070854005030810440c5401c840001480300001d01c4503d0750b5a68455440e003180d08070f491007400ca003070010b10041c42848001d1103000d24818600a03646181c45040b80c12020868082d0703400c00460011a1000b40d1100910200c4c0b850310b400180a4038000006003190b4551090400c00d4010a03042640900748005907002e880b0345100004103501c3e06401601c0b804540668481c080c0400303c0c0140084001d43c0c0305807003460580d11010302200d100c000b048112000540010040d0b0300e01d4000c07902280e0800d40e1007020241c103004660103c40f0b1611841445241103404441c804038000a0408000c001d12041c1280c004d8548014205004100292640a401846a805034a2a02c0440c00340603440003031540e02d41d0404002c43d500d545580e0104d0100809024090041e410724901100480052003502e00c2048610050305c6a440c81c3c00c41161650b212600b49903022844010a2066a0680c0710f01c40031988070391 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 880203471 1250 880202221 880202237
    0x190209100509100504150f180602100b0a05010c0b040807020a0e092e0e0a0b0c04050916211113090b09010305120c0a1505060a0902041203050c011803 66
    0x1c1c0c10450325010300d040321810091305100070040381c440d44100d100401110b09110100b4035001204840d6080e8000141d84003010f800300000d000758000c1094903c400c1d032501c080c0324100c003660a001140d4203a1068600013225040c415011600c5c150040382c200b0710412045192a10035000650010402c0d00b1029601d211001400a400c40404c5450100c4200344201c204c290107502c0400c004500d1910030020b520346030319114801d50814089041c80641c4a403010000e4101014203015580040c0141801514044040740d00d080340d01f40718480e052201d5030b442c540300c0d156001440c0d903025001090101d494481c1a404103252000c0b0141202c03003601c41a456156207800e000000b0355404107080390003024101c0c010300215501041c02108003900302c0e04160780310609505145030000030750f0b01a081c1171291280340c50382c0032180c2055020700300c02c03650f01c00540d03295038800e403c0b441540700e01c0400c103405400c4000080c1c0030304060201c0c00d8455000051002c403c015010040e5100b1408400040c101c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 880204721 1250 880203471 880203487
    0x603091a0901021c0c201516030b15040b0f070c03060b01031a0a150e04050103120801050618010c0305040e0f0f010b09060904091b0f0806070302030c031902091005 72
    0x3015400c072484d481c82409004040e0707048800b030011315100700115a0445072075080c2c078080000304140c405111100030554264a80702d502c084401d9610101003000030f08102c002e407080e15004032884c0c10750540da00d02c1481d252030581e032382036682d01c08003005460070000d111403030100710030488900045000746404140a49010001012a40ea0015161603543c020003190315680742d43c07150405032084591112a00000c668054516036480b095296000d8100400801003002286990032120b04644a001891f43c1b650100019401040e0750000030f2150184820141d40c42540d8640150b03001e414803d24190b280c4006071045c9400315060b074800711882c4107108102d10000c0701c07140106203852416042c0140040060450b1060115080c456925001c584050000c50711461500100c2c8651409000c3d44c0c40e400d03000710110344d110311042e501a00e000100054040e00840384150b0b05500c020b0700d160343c0d402208052001340c06044092a1b42400505440c3d210084240000300007610f8075030300c42d0301c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 880205971 1250 880204721 880204747
    0xf10020307110604031e0203030409090804150f0f0c0227060102060c090f0d0602120403020706140901211506031e0b030d0c080c0318040c0305010f0603091a090102 72
    0x91400070ba4041c10080000708045105142050a13400031604c2403200c8041600020349035000b40c1c0c000c0b101c25440c0107100801c00200900400440381d580c1290268891008001e5414040090b080e10101c1e00060034050300500c580740502c0900d100070040c6091148245c0801c41c001082c00d4920300d07004d50901840502e607010090264408000641107241004501c00314510540001615009641c2081032000300400e40d0162000002501c00d01100c1d0314082c01c0080d500c140f0340c410b5a000c60011403035100309403144802c440d21060107840f0031043c8221a0030100b00c4070710940240c070007039994100b1100d200100b0418240100403aa5010078146000079041c2d0816000055030f082107803620b00d01e52655280490381d07144100c242d0030004400c0d07244d410030440702c2c4a500d1a01d9001d0000045440036210343c0d511013a8188400e83d010000b149601c00181c3c1120001e010780c881d0000041d2003004070a102c1d401c04c69409104001e88811029490a1131039840c000b40d5206c46541d40229560083c1c0300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 880207221 1250 880205971 880205993
    0x506030102071e060f0f1418100f091709190e1306021207030e240f0408130806181501030b07021006030c030b070206010f030204021e07140d0c0b060603060f10020307 73
    0x20f11703049510762011000f2810303910041490050f0004ad1940c03520b505141c6140e001074643d582120202503101803100d461851030388920303041881414400107003000c00c150041c040e01901c4401040030030b19100c000c0446035202a41c4400c44c1c3c01c40d000c01140c0900c0c42d4600c03a690003010a5200412090040e45080e420162103c0d0034131050382c61001481605180b204040d50003c9040620861949907410f001c54541b113003914800881d4401c4100151450f80003030514805d8001041d2003504124055090380c40d00084041220230680c10f90040c4040380c2c004016540110b4140106c407840c45403080048191907040d8015107103100002010000c1c4242d030880036a0101240c4060318056051000c086442e000314040680150390224610755840c080703585100203202450030064448525240148220300120710906483c0962032054540900603000e041810b0390001b10600d85940700010702605410050902d5440094155582e01c11340701da181d1980007020035400345545d41740718104090500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 880208471 1250 880207221 880207231
    0x51006050d08090d030e060304080307020d14090906011b080705064006050a050402030106060e010905060d0212040305130608150103051f180506030102071e060f0f14 73
    0x21001c01040010501c1044a80c0c50400b00e6801d1407070502410f045821072000e20420382c000000000f8002800f8561f40a03500c500d145608690010302d901504541e4200f00b526510f01c070758024030020515152091700190702080c10703d003c4510308141e0b810303c801c550004405031a040400190001405818890036600041c06a420203000c4418881c0d441c20092240385000c030081803050000d58522510075621303580307403c66014056400c050509100034001a1403ca120b503281000004005000381140c03091000140c44081c6014501020311080d9403004d820285400d13803c0010542c644071807400980140e009039529500d4008130750384003941a5541c1c000406100103d010404626030a404d03403c0018800e21b000f0034517848060410f9040545591440c90040200390045502e1000240031110f82b0880030060006450355400e05080b4801c1120190200b080380700205120fa07101106044400d204080c0041c90450f0107030110205d030b050003407119200340c44000090b40d402c0e1a9141d07580007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 880209721 1250 880208471 880208479
    0x30e01112a0a0201110a06050f060906092802040b130512010203040b160c0c0e1f261618050a020c100507140409060303021c05071b05040905100605 65
    0x7030340464034040e80c500d4002030090401c4400582040c0740082484500b540c0c60f4016014040c600f4201070300d8160b91011501180107003008030004005240c40c1d203440d4000c1103500d10600e19880260400c1d01110450360064118540030840086c1101002c0010802c82500502d900c2000741860200682c0c520b0320001404130b68014400d000100da1120003017500400031444032030708090001d000ba40e418020207006440740c2108840012807491080c5201e1040d101500f1400300705c101401800c0c84442c050080d0b0510f9008003001e91200d00310004165040741c0c1c034604840b14100690f003444400c01d4580c1105100c0340162415281d160790500483e0b811680e107080543c10140c00503011559058514551002d0310744030404200100d014074048018154928000d46e9a5901c900344000600701c40e1004030300504c68034000564015441d00ca0700309a02a60380d03810314009a030340b41c0c28814952400c3d0a02c44241e449000106030382c0b54821800c2d650310880140006450342c1c001c04048071400c0e44440d0203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 880210971 1250 880209721 880209787
    0x50106030501050d050606240a020601031e1127090726031608040b1602030c0f2206180b030c0102340503150f070c03051801030e0111 59
    0x81e034081b6203a64050f4040d1000020760807a038030510150f07940400400001000010000740b165808283c06060380d000303200650185240d1038141172001c00007030340900102c0d20603509408078070745410b502c0c200f1407094180507104001020918103041065408440c0350307012100410540c01c080c441001c0d00d11080c1c0141103c18050041680c4034031074400f10064012202980c4800c000040301681c018022551416443d50b403440012508182c620b101170344607201d0810036055628051100c40b00021014000c3d550600c043c1240c102d0028000020110150307c6a5000c6240400d0401445100340d1003c80454003002560500d4140a0386210080c11904040c071030f40918050b020482c0003100707200b5449840c450082c440312600042e83c2d084250b00d4000d0520040076901c0c10103455006410b4180249040d40715801c0c05c0ea0f10f00c0e09418020040780c000e000c3d8008003001622641400001170501141c0d0358008842d1030708448841004541225011403417102d5503010143da01543e01451404c1c1348 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 880212221 1250 880210971 880210973
    0x3070c05060a060e070f11010e01150f05061605031e0a1214130309080d170703090203100b1807030617070b19180e0105100302070f02120c0d0501050106030501050d 72
    0x20301300c0b0014000c000b80907143c490040541e00c62200144900d4400c0001c0040e084001c0426001e401c00d4000c4142c50801e0bc140400c40740d924221800495000505091130000700240344007600300241d40c161503d02062115071aa480d8215480c40ca100d52003180c0d659a41c2410400341001c00e01521103214540ba01d40003c074070100401c1c842c7d8201100065444840074607160860724910680c012011901404050b0111250000d540300b0860f1a031848039017646d610240114101c0d0b10440700a50306034009010018019400d0b1321000f10301f04003610140341d104041404d00b07010f00054031034000182d0f81740010040b02500c0880181944503800c094466140b40c05d120300c0403405445104d0f2215613641d40d01d041564021342c09812220000411203610659032868001055024403a25018081ea9007800c40154131a108035021564000720660300d0815940034000a000d640102c1c28051203541c544d0311040d9030b03100c80c0ca0001c0d40306100102e0325604012000701034500680c0014007601302d9011200c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 880213471 1250 880212221 880212239
    0x30c0309020f010806040609110a0908060906040b130515090705031914010b0d03090906120305030a09030509030f01091112030a0e06130608040309050105090d06021b0303070c05060a06 81
    0x380000b607092074011150384489000a00400d4258080741d4854540600741a400d001d00c0050308a082e00742c1c9500408554501599464000888488450b500007900007030018240c04003c9402040041e080702480e40990b403034519000c0c01d0f0040011040e032000400400e20810081c1c00003902056010b0100440681040c03948070754010001001c030f1040590781101d441096100c46003111000345002091282800c001d05640030318040c0c14091820802d011170a2a6039214012000d949550b0300f40c695501c1082c060000c014980701142081020032a04185960400c0941884545040002288407413440e10208180704041b00754003030001c110b4540c0141c6000b00c190340d5035404600380701c0c006e6a908000a400da00c1810000b450490010b10302250f95544142c0a034403d612941780c41c1402510b6400540d004e0041c8072041d98003c0690156500080d9942c00ad002003600f044403540b03070541062170407070135070b0400c9801c5030000380306000721010301404128940c1c0007405d100c030820407e81011562 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 880214721 1250 880213471 880213489
    0x3041a03061f2003090d240203240301060308030712060503120a11150f0906090a0c14150d0e21270901061206050102030c0c0d03121b030c030902 64
    0x1070030b015140540c100c0100b40110703100103100a2242880500c40e24020644001c0c03a00303003942000307000d80318481f2244188200c9001c3c02d412104150910417a122500c03081710385207034054155480e2400000011040c2002e1800f9221035207401104811200c00c000403100c0c2503101511a03885101014040c4680c079080b01e41040181c82c02c0b6110080c1840c1039031604070701251030400103000c0020080141c04460940c1d014110000540d0340700e480c0d00811a0b500c03940101c02604046c1122401c1042d0304402458039001903025294450404241d0b1405160350407150003c04555140d000b894403180003800300002100490324603da2680480e04810118044d40b50f24418200c1600f00c40d140b80c41c0003110000c1610340080c17401c0725640e100c010003406050313001c8941080504118021a05600200035103008004890003007002c0201101084039010785644107a044c8846480020554440c0f405442c11110203a03200010114401d400202160a0144082c08042c900885440169580d84407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 880215827 1106 880214721 880214747
    0x30c060507030f0c030806040f1104081b0108071d0f03030304050d140a0203390606090a06032f0a2c04050d080903041a03061f 56
    0x40c0e860240404c001070120b00a200044c001e0706003580420244050740c4c070b0104044115004101c081d034455000030140c1c1e0800640e8042c0711021b0b4104202040d02031a09000ca490711140013000c140d41a0350b20300e407080140059140c036660b0f01d1f1500303901880007015603030b42e8102850301a98803440b081940c4089486064200784d42c4004000b524054012500030350b00d0300a01201010042181580d65145c00800c0440c640407100c1150b00040950303007590042805003041d0007000015030008140f1848103042c41d0085c000114110052200d019090001c0d204041000350501d4071214801c400a4000c4002200001e851041c2c54401003403003a50140305801e0003080040ca540c4180071207020307100b6400400741d111170521400c40aa404801001680d08094580814071105c0403081c00c10700d554100801400880e00c1c0940300c607404a440880d440d400c100f5000342c041d04100c06420 = true := by decide +kernel

theorem cover : BRFrame.Cov 880035971 880215827 := by
  have h0 := BRFrame.cov_init 880035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 880035971 ≤ n) (h2 : n < 880215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
