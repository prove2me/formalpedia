-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5143
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:53:38.584193+00:00
-- url     : https://prove2.me/submissions/a93680af-0113-44fd-99ab-9978c9d7dfbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 924820143 ≤ n < 925000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 924821393 1250 924820143 924820159
    0x30207180204081005091b0306191b05121501090b070206042d050f032509110301030309051e060306011101020a0c052a06030a0e01111819050f 63
    0x580b40e024681696146000386132a614001c01c0048032060250364100c1180c20303c00d0310280c01901c0000d40e500009001400c20295a10601110205c4c0e9032200000708444600d00c03d802c452042c010702a900300751a05c01c0d039040c10100007403600174903503041c1c801502c0503101c0b981034030706000d043c2419411051040380c002d403003004041210f00110480b02e603c4a11850400505e28940c03040c00032a0484ed84290701403100441c0810759a500850640c0c0404600c146081030308007100310110b05101e0b264072601e83c4a2520040240d03000301c40c40218144e0380a0349038031705035540d60000c6c8076280600c0c0522046105190815080c1450200019038010b80149841c40310188890422030032a4445100c03507000c1001c003081030b0204842405070b668401602d614079195080006c171442c0720040844c02c000e11035040040090f040f1a03040e4418808550b900000f080309140400112000798480c42441c81c011915600a4031246070401864540e0401c0405041c0304034034007020701000c48540d050003a885844 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 924822643 1250 924821393 924821399
    0x3020c150612010605060a260a0c11060603030f0702010309060e0d030b0105030f0703050907170d110c0f13092010181e0b03070822030207180204 64
    0x10400180220404144200480c0c0c10624204000c1c030840e810141c426034107200041003a6540c0006a822583c1c031424944840c118100c04a1610304284600e451128501410300410f40c55035400303c2c401301d0080d2601c203d91b40d1114155682c42c3d0040315020b81c55481080054000080c140281000920605010030303446425a0740d081950704e4044044002e81c800e4800b2964140c0c140242c242d281d0302828200c0c41c1d400c121201c4e50443c90010001403e050f125804121010010030100c8014180c2c0d0a01d4031b13408072552000303030320341750103180c00f4000548071003c1c65039898010401000c0000000c211840502d01907081c400c0c284140c4036044a007a03964a01c00000c96980c1342e017011485444502c0c1d1951513007174000c11840c0d1121001a50400104103080c881741080200b0b00d50503642940070350441200c4168245003184c2e5207800030301d032200002c001d0045180d00314143d00c0c05805110710703214802c1e464250720604641c41790300182c0103a1140b03c0030818002100b4050b9280c500f149409881c103a2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 924823893 1250 924822643 924822667
    0x70809060a021612230c030d0e0102070b030c030f060324010905070302031b03040f20030706030e070b09060d0606021b04050103020d140703020907090905100b04150302 74
    0x74290800541c1110840d0014480f10000003005885400c07081c0000c140151103180d142e81d0052007010740b14029540020009404001c203203d8900000d084900300c01d12800300401d42524100d4044c0944902c6c400811840700c400c00340c07485aa40241e4003030071503542c201030065a40024088940500407401030b0320703a1506402c10b14160380c2c03220107440c003254580300c5000d08682005007400f0805105100740040300104104102004242c1c540960b225141c80c10080e640342841000240060185034200319070072558001124428001c40507104616580c0da0164240e80241441c1c40c13240d000040d0a002c00e661000c0074050090000d08001e0070401c0250641048903501e8000a0244c0d01c850b114080c14146814214a0441c2c207540501c03041d40345030b02007451a0241000108a03a0741560300025041d42000544019038000b080e0042504003e000500b400c00d142c02001c2d091350400b000039000e4030b080300b00030044440c101c000c02e00e0140381c50304c05c000f40840c0310340400070503808104d0200054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 924825143 1250 924823893 924823897
    0x70204091205120903211b1207081b030723040306020408070812070609140a060501051513050d170d0501182903010209130504023307080906 62
    0x49582c90b1140d070348991200188841c00c00038212455030788200207615003030204640502818003e1082903d0710744403000f0701198000960081c240d020000b00d000c1032441290200e26000c0c69540d11480300e140c4071100f400380e412084218404e032110040000c18100c500c25a40300b8100c000110b00c50030008144410104a5403003035006460f0341d50082002d102d103450a2014900405120000708002d4400c0344940c80755000d403c60103002141d803020f6032000e1000071040320145003041c0b020350340e1032000c92410381c005081c02c2c0502d42c05040200761291118210000f02d8969a81d000d1500c0c046601c0c2a0400c200010a00000c64264401c0b2110142400b43c590140110701602c500101e103640c1406082a9845541d2080b061040e040080c45882d04000d03858104c00003001d8412403040c41d641202103030181c41007044194110280c0641c6441103580c9500040c00b85108446190500c0909600482ea0440e04016982c0e9581080c0c00e0400c0511340d5001420664420004075060450755800a8466 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 924826393 1250 924825143 924825173
    0xd0e030315040b010c0c14060705030d200c0a080702041118010f031116030e120601030204060909020901150c0606031103010f0e120c0106030f1a0705180607020409 72
    0x29074880d00e03100d80c1e01d0103008036010b105003840c0034001e5031800e4a840102110304c3c400c1c00d0601e001100c0c8001692107080440d0545604401101d5a50801c0810703800184501c180164101c000c01c021050305542c26000c440b00c2c0d0014900808144001d600ca4402590014000300e034450394815908514500c00c002070651289000660083c0c481030000140140398044045810546480000e02007804400c1c2581c0d6010b045004a00c1c50003d645820b03541080c1c40365000d0b5102c5038480c20100400000112181a00e2003950f0510180c0d0b501e03410381c02a40e40108000750300c41100b1005010301c1c181104554542c5c0790300d10302260028000d031140801c4a002e50402d1f58203590001e0507018508013401000d401e020355100810580703424501071034036408601e0455640c5200000c90b2800340f9025007000005d0740d009a508420030100f4982010200000401000ca411140c40000e0329a8003e401340e13010145003280080e1207540800c1001076951164104aa009568003210004607003030b10055541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 924827643 1250 924826393 924826411
    0x2001020111040e0a02220314030a08010e15040e21070f02090c0405061306020c0d1218080d0f020f010b03030f030a0219030213210b07110d031a040b0f060d0e0303 71
    0x111600f542004c4813108c4280b80665107942c001c0241000c40d642c8040020b044482e021000e050030380328500d0180b000c6c000080600c1d841410680c0b0128000b80200d1046800d0b1000542003500a0014270101094011752002030802980442c1100142c00d111071f0240c1d100d4010103881f032070a5118400900d10350080f103800030401000c010240b1050350100000d900c4500126a00e8280d014540e45825036000300c1d4860364204005600c40c4440c00381803860510150588000340c0b01410320134440205251281c2d15142d005110748240040c3c071b40018402c801d04c2070341c00740c06107140816840f01043d50fa84041e103088a9103a08200c1d2500030900f1952111118090343d40140e0744560700350125022a005030000e2100941482d80e02c1d885900c11001c1210285d400003540c0065560050b080d1000895102c0b484198051001d43e01050395140c7c2c00b289402201903100b000b140045070a1004444940e00071030780000781c40909450b03030702e000c101404c02003000400102e002c20f40380d0710703041c01c0d90010f9074800b607 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 924828893 1250 924827643 924827707
    0x4080a18120312022701110709090b010e0702060a0c0903020306150103060803040506040302040c050405310c0210090c121a070e1807020a0803042001020111040e0a02 73
    0x209540000700b00c1c28080d0f40103055080030020091104400030141e400700c90441c129092072080e03409091500c2040440f9402d945060f680d0700340c00030241156a1040b180b080444002041c41403818400b94010705090340142161750300e200e1414000d114504d1048107000e030500303002005a03002c0001500c50100c1c5182500b40c414028009002e58016800154498106000600141e1521002ea0302140c3c3c048401003000680480141d46a01c919000507070080c01c610403940707242412482c0c1b446941040c0c0202ca10050340c05400d8400c80d000c0c2e00c0b1810041e00920020010307040d0507088001c6c8240035a0349140081c0e0b441c0359400084606030710440d0610f0740c0c00310000d8040c0341e84001d1a0f0240c0541840803206e00c1480001c1d000c400c158901c80c040b45a848041020640b013044a503a0565001441c280d803820030741400280c421208010400000104015400340d510601078040040075034a801030805003000d140244408004041c00611a030a204000103800c10303d1120144241c1f81c00409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 924830143 1250 924828893 924828929
    0x1704140d020d0c03080a0906020403050f100b0906010c02150307121b0903031b06050f040203010c02070f053c1203030411090703090203122106060304080a18 69
    0x504100c01030a005065420200300c4540c841c0d00500708101c007540c1441c18240e15540d00c603000000b07200c42c0c40e010346058804107010080100c00229404848103010450300608422459642981c9040e18015004101c11000c41c9155001c1c00054101d6803000744180144512200f049603140c008850351000100903800d40c460300241c41c0700349890321640b1008480106245000a041b44140d4480242013040c080c182d14404011036400d1030340303650300c14424005410000030060260b041950181d100e9440c03e05181e818a0002034560210780788806000345c0240340104110244a0140200c042c8050450302541c1050300c14000ba04014540e140030b00100e140501800a41611250410170b185c2c42003040c4404900c4506900e4148013003211900c40703594444108501074040c00c3d00c0250103205e500307215002900400003514081e40004103103004034050507803004c6912020740d0001d030031240400200340482d08013402001400d2450400804142d464100004001c0e0b0592040422040b0f12002c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 924831393 1250 924830143 924830183
    0x9030828050a0f05361e0f0d02100e0c0f01050c010f050c0a03061a1806190941030f0d0503040b0703050105221e050a0f0c020d030c1704 60
    0x1004500c100c3d14607010710301481c00c012940c1c03041c480d1b030310310182210701c24038030101002007200d140c005032a01d0558820b052505406507079007628018503c03400f41040050401c0c030100081d40c05540c04014103e01c2051000c0b0010345031580075111007003095486001c503038406000f0340580d5004110605074190740c0c0402c0c40c0010704480d001d07000f1051030000c035074040211160700015101031807641e141d10707130007d584030340014403911901c020080701c1212010b032000b01941292419044910002440c0c03c1959400d154419000d0035034400482403c00400740000e04420604450200b44083c044031182401030340c07418641b100300c081d01800208000308100802c119074075165085102c0c0d0405005035410900052400194503402d070310002505420480e05924540105000110380d00164140c044001c004030060402201d03440101c5082400400c0d0f40401481803581240c40355014081348038080740d00b10042c2207000024810409019001e59103210424140344c0a45d10a40d13080015511040744 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 924832643 1250 924831393 924831451
    0x180b041212020c180c0d06080102030406140c070602090f120a1401090305271c030e0915060d0f1107021e0105030a020c011e09030828050a0f05 63
    0xa01e821074000c0702030702c40240c07100110306000913140c1d4402c0803117aa0f560744000050080e811040d5941d82032040002d4480c1c03042d0300943c0200c0c0160b0060081041c041c105201065081d14a40303910841042200e01003032561b40984a559401030040032003d25100c00101c844004d00c1440030030390044105003041281c83e0f058880408681c1c03000b4080d001a60b10007402c1030084611000b00c1c030244522011007181440c05005032520020207031a0400100000820140c0300c042e0100c02050103c18281c503145040c1b08034511a000410304c170103c4400d00001e203c0c1d80d0304092010340000d911900e45d03901d5100507019a84a903843c00c03028030780395517250041085010505103004201100303ea483d4070f090b648002103d501070b1821b03501580d5403c4448003240105031200034030300b400d1035000c0380301d50300b80710768008001d0140030ba640c400e05a12404403e2410703154840c41c107181100914401c3c00e490300d264101c2e962001d000100055508405208003040d44d03401c6a540c5100506483d0030f6041c1c1c150034407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 924833893 1250 924832643 924832673
    0x50901110f100203180109050c0a060305220c03170d050105010c022803080403080a18081b1c11131e050402150703020303060f04020a02060601180b0412 67
    0x41c00120071036003049840d03000c44089480e0182d000400108514030710324030500303882c84150003040180441e0401c2901e80d44600101c1d03200c3c445440c00040c00502c01c0c0580c5028102181602a02c8407141c2d0700c1020311005d0003001c1b02d242000d0040000495500c194600c0840001c45040f5a580030500c140c10407544140c1102d4107200c96140380d54003588505622150f1075103424403940000c3c517020003080c4103864603480107000c0d080c002030220422906101074402003141d500e400d99640c030685000b0092600c01c0c0280705065004050420064040e00346500101402801c4d020b0070400d04802031b02c0d20a0710302825200030072070001450007030400c0c02c00340050401000e002c11051550508000e004200c4407840c002c400d44030070208095550313201c10341d0105412150825070310ba20525000c1d44940048a81314800d624540c2e4402c0702e400d250007240c4d414201a40a0704180e520a001517661005001d024110001d10030b0000c20003108940080000d00700700d1101c031540400916040d8401c9540328 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 924835143 1250 924833893 924833927
    0x703060f0b030f0f0901020d06060c0c0509070c0803040318140f2b0212010c080906010b040f0306020d0b0301181712010b030c090a030b16020d0e06070204060e010303050901 76
    0x70812685030744a0f9800350704162110340c08106900d0340c5a0542c0640504e80a11500c580303070420000300e094102100c6607040b1311501100b551070790754500300308c00e5000840e200000f01e6040241b400000d40040d00a540c0680300f810200c822484e2001004146411504810741c0008c1018904d190303864901100f0607890000c60b20518250055030000c20b0084038400c61650140d68841c080f01156920b04002c1c10340c010100007001911340d4460700070070341401580d144050b07000c3e001c00490302000358021075060354807080491201c1880e6903500310003503120045070440281c0d242c1107800c072a9002c1c0202d032001e940c1c020304020040c0b41030500d0b40c401e04120503076106c8850b040104c01c0d9078a0030584200e044942d044016603c903900c40c4400c0400f8480c0f408150b40c052043d01011041040c1c08500c2409200d90070b803000100f5440a9050380d413400580c002801081111005481c41d103840801094090f101800c08903440755100850800103d00707070800c9001c1a8017203480915542d01c040ca040144000c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 924836393 1250 924835143 924835147
    0x1513050c040b0a03020c15161d0609040b0a260616030915050a060608010b1c0e030c0f010f1812030b12030a02100c030e1905150703060f0b 61
    0x1241800944201d00c10804554004102d0f040494060341c190b640d820601400d0394164055400045801801241c540d000c100a40c0300400314540b00d803600144010904000241841e064020001c00360000d40c003aa50003a01c82129800381d0b00d45a484600905040001d4550700f0802c0c281e030f2203164010f6103490807a50208003004512814443c1603160910725040015070401c4c1420f1000280300c00c209c08501d1f1905041c02d2050700c0d0a140d10007812100d01d07941d00c4040d80d0b00d62074007103858803c40e445000d00c80710001c0318464415a80c1d1090300d4807c82c3d00102ca1a01c148100041e003841f90030200302c56180d6403465607210013921805800d403281c00030346241400c2c80c0c160356a54a0381c02c00d03500a00415607100c542d0b0300907441d80c041e0909103000c0201265110b40756118029550f14002402002c818280055030135070324004d005050442000c0c0001d0156600281c80031441c40e00f2020041e101d41c4150740c440811604151810341c0211420769010444909042300780b9078103103031503004c1d00c0c0319002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 924837643 1250 924836393 924836401
    0xf030c0903060f0204150903030e0105271201110301170a0c0306020d020d1107060b0108060303120903121f080303070912031715010e060906190903050105151305 71
    0x100403020410780380d000400156401c20552580000e0080e034002c0b01808039811421070202d508000d104040303922940c0c45402030381410004481c2405a03074510508040d41c00620442c0242c425043c04041d07130094080d01c0030000700e480150130343d1300307811101c0500c0340d0010060207880c1200b101000703040500402424200e2301940d0b2401542000e00c07020b024580d0108441c602c440741d640454040310350418043c0202500d80d41540c49581c040b680483e400d92030702c8a02c00c10ba5001e800518170030036004000d135050544201c0740c3e1122900061101d00c0701e0004100311150148400d41150280701c0c4031080111401500c034040b002c2c1c19843e0429011580140104886190b11240d41e2040d94003144030b500c0d24905600d403d5690201a2648410705034a400c108003420151482030400800d00341d031050384180d1140c09104d4544115504075030000c50420640c5040100d0f0146102116400c0c40c0a0f440301d541c0340c82e41800c44205803810ba42480a8429000700740c40c2140e550080301000b482e080010f07080c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 924838893 1250 924837643 924837647
    0xf0f09051006150c1b03060e0c010f0f050d0906020f04051c230c0a080d0311130b03060d05061e09030a091a210402030715080106031802030a0302010c0f030c 69
    0xf040c942e04004000300c1151660803c107002040c0030800c0c10302d04540082c15203910344070000d0b02510500d94101c1c40380706407240c900c2d8461040b030740900055480300b0384941c010900c03c4585a00040e0860b803100c0d00c5204580000e15544020240c0d12030700c5000a48030383c00c010401943c3c5070040c03151080d6500f04134040c0c1c046510700300140c038a1005800d40c00000300d000e0302844d05100e40014071681c0820301100c00200030b00b0210b003070042007510b654200039903004442004240d001e4184d07a83c00c5802034000030300051300c4510046d03801010091010021042599070342d8074109045400000c03642d03903a00039501144120b61456000251100594144640000000d009410078801c9a01c8001d20080c08144070500e4001c46003803100550a040c00240c5e00801a408114161002c9010307114089000540608681070301d402c250003139944021503407030000100c0c050514501180a140f443c0b80301980140c0c0c04001150410b0310903000492020000c2c503024080403200c560700003e05050406c1d010380c80c4d13 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 924840143 1250 924838893 924838919
    0x1062102090c0a2a0204091202010b06131701020f13030b01050108010b03151207140906030115180209060a030507110f0a031b050d05070c0609121202010f0f09051006 73
    0x4138001441d01c07600c0c40c0e0705a8034803070340c00f802e480039421a280020840034840300850126200c010740d0024002e001e03405080c011144200140e2103000c1000031002d001c4c44000d1444440208a068005401c2c103008000c48002580f0060280000320b07603c8904000308801615100d0043c402424280740c19850050200024400246040b03051954088004055501c0061101d43e052850040703950a9032110103042500070047c1083e84940185c20014060f4501400b403004007440e280c040c0016103280129880d0340c1410741c0b180c0f4900d070303400b800304445580718580034110311043c59901003804e007481c40c030250a00e80854500c031410341025115442c56000002d000c2245641440c03d0581241d02a11010058400b0701d070080150255125103c08160700101502c0c08600545d000b15030030380e4810065821014521034a2040d00c0005102e90220b034800512036044042800003181c2050b900711480d044424001c2c0f2040344542d9aa003032010301508100650040e0700a1008000c1981001c00b400503107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 924841393 1250 924840143 924840167
    0x5070504180b01021608070503010506041a090910090c060318080f2a150a0b0306010b0a021f05100905040b060616080d05071209020a06080901062102090c0a 69
    0x159482d03202e6281e250b4402c00940115159200d5030803e82a10742e08503a407210081d01c80c0070f00c80d60909002c51414680b521480c06460000840c0e044512007920903c02c0d034640090202c5e542e401210002050405035000c2c02c07071464407400d1210782c124100003018080b511080911920750416120000001e014002203a01310440420b2850304c514400c44071890010a10081c2c80018804a419400203480000e01c01c0d08038070700c41807515042e41e4003200c28045442904c1c61b20752682c4240010844074040a00910100310b0504c182d410240202c4480368243d00300901621006680c0e20030000e914841203000f6014101904040c840340c20b0030b484859070f500010741054401c840000720780e018190300c7d49180c0d070019480070700c0980721072248121000034901100d5641c0070074500b45d0741121001e031a100d0140c140368002c180d0074215042500403141d2030002090104150740c1d4900c089100031402b4101450035084070002601c0c0200b500c140040c8200141085007081ca0a01624516540101d03520900c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 924842643 1250 924841393 924841439
    0x515011217090a05030304030c150519080c09030a050604150917030c09030d0504061e0f030509010b030714030f0d090312030b0907080f0c0313060504061b0906020105070504 76
    0x15a40d00b0800141082456400340b903252000003400401c0180c4a0441c900700d5101700720f60f058140c00b040c400d407018440e0441c03002e0080b410010303416420303008800e9190000b81403542141049010070101749442020305082e21030758001e000b00070401c466180c005070020b01c00e4009011098150741c0f9011320a0301241c02c0300b0300c1035010000408403180780c02501e68810006080b103103004003510300034103250f1143c060f200005a4250750360009100c941d1600d444d00d0780d5036035180251a2030a60480c02000040d09544039552240344d41d40035947c003000994044c006509100f05e115003036804151030310b070070750f107034a14070390444956240c1b42a003122030401200d410280b8000b024885c0c8a040b00100310258a0075445540300d0300380113200c2da01030080c0b8440c01030807005002586070000110f11a0000310703100101d00024000b1240014140d8201c1d40d0030074130451020030044000e11041100504020009002880840003009000e034240119900b220090038241e19150800b24104030700c1440c0304248034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 924843893 1250 924842643 924842647
    0x70518010c11030a03050a110d0c0204021e04061d0a0302030c0d080d0615030f0b030309120f0a050c1305090c040c050903070803041e0b090d050a06090515011217 71
    0x70078020921408420060020262000d003541480c020304660000c034802d00002c1c05e038190710291800c2c002140c8000c0412a15083c403c00240d07403c1002030750001401c1111901c0ca05501325200242d1340c0580007a00542e2035050040070010b500c810800c1d00c04c0d2580380b181208920400240c0c81c0032581c80000c0c032013030b1400f0078007841d1030811400c288680309482007010300c1c0c040c0001d1010010074569600160f01d41c1c003840240034460310a8141e4109a0301c1590580007080803a10a141c000543e104c60f0340740e07005498806003132a030203a041820325601515140c2005c44135002c6450031710401c03410230940e80404c00c094200140300d40da4030307802003604902695464418088890080c0c09070b8000c01c0e002402c562000e07480b01c03001508d98109204450078800000d4501d43e0000f00d03c2204010384500e0010030b810f1985402c1000419051050150b8240c02082c27581004503e2b40d004420085019000030482012404d818040e4800142c0c0044809003078101854001481d07201c07110462181514103075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 924845143 1250 924843893 924843917
    0x1b130b030a050706180b03092a0a0909060b03070609050d080d0e0f300d020708040608040c06080c0304060b0316080f010b060901051603050912030d0507051801 70
    0xa49044114070018040c1e1189080000388241d10041c10701e0000042815210b56558400200c0040d0000303507100341440c0c000305181d22010341d404511064224800f54035083c696100c0c008a400701125810544179a9164101101400042d02982205040581c001d00c0058980140249244903030b004243c4942c050b245100144540303c01914151400c1c8032080200d1050070202d96501e50b0b0001180f40c42e0f00900741c9141040c80c0c0d11380706810900130114000301c00c40420b40200c2080e88003400d491800b40d404c2c05000c0c0890000c001800150803117407a05001804c0a0074124030000c01341e8800c0042203004030800c41f05091103002c0d6074019a00030340c0803800a20003c0064108241c0c0180c030f1842115048000851040010b9184a4400c004c0000c000301008074061240300d2186c00e0740039010030700400195024054220780542d4107806031800d24101269800040e0f10b601351880001005d80c408181102e030481c20b0b2055035003041c400c0c1010f610b008807504003070340b20003030900301a4107100c0f0040c40f0fa = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 924846393 1250 924845143 924845149
    0x1080120190e04020a0c0512041a030402180106021b030304051305040f080a033305060a171305010b0a26100c05030417270102030919081b130b 63
    0x111902c40700100199200c251030b1030020b0005070180f605482a1003001c2d0103140da1189901290300740c8550006188003080407124941643c0d00141c0100c2e08100454600d111402580c15114082c03d265030140039080d04441078000c0742010300314064440c1d0410442001303d41e40708818084904040840421340d96110f0a0100e40003c1c2d41e000a81a20030024103000020b03859440b04009806401586183e11107420384d582680c610160304180c4e45411803c1805546081800b4107100200351800c02c00014210035403401c0c0d85402c0d0f40024503c200c2940301d00800c00f0a001e6490700c0300742030b202d2003507032480c0161440b421000b8941c1e441402d0280c242003045101e0500c44960b11000f9442c0600640200c1c201c020302981c000c03102500c840003108506e0b42801da1103022034032211060424000355900c40300490649508030440181988000c0159201d1915821000c0c12158058042045002d191800050038032580c0702c11016101c1160300c43d01b240360b442034418000c0362250303a40020811241404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 924847643 1250 924846393 924846407
    0xe06180109020915040f0506030303070c0f0606260d12110c06270a050c040510081603060b040e030d020a020102040f0b190503071e0212120108012019 66
    0x182d0002d030220300300f021300100030030b20000900043c1c408021440001c074402044600907605182e1503041000801d16592080105109890080f003409140e4001e99841c4030880340c043c1d20000400480344140c8102d0004050342e400e070411180b02901e40c543d20010020280307000142ea1056043c0c0d04d0307203017030b8403e1541801e0301d05054242c1c00305c6590f03061018002d41d110208012004c2e1443d01081c401f507040002040300080181c0c894010321045040030b04100c0030701f074010581e000c010b00c0b00c080001e0700322080181c160302d4210ba0185408982c2182801c1c41940c10201060780514100103489400c10b100100329021520819030058861441400407806445140c0c05440e07100c5d000700c1d0120380901c03418000c1030407445000d0101d1702070701380503c285c0702d41c00111884008038034080c5d5041005805148008446101481a80c044030b0401040d0441c0c0d8002c5801c0d10714196080005002c5004248039540240c2e940040041d008440244000140d1144540c200c1e042c0700c0259269203002d002c1c01e9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 924848893 1250 924847643 924847661
    0x3070b0a112a030d0626010912030e12180a0e070c2a0303020f0f0105060f060d0b120106050108090a2d0501090f030219020603011202060706150e0a0e061801 69
    0x103014405d107039849000080121b45100f0841c4030002480710402881814810403100d10b5112901c0982c22502c00026001010450340703c03803050080080790700803402020020039003484143d400d4500e03c0000320600c01d1138529500030128080f0203d003030090051b003160741a007060b5840146805546100c2a4024060f98a100031800d0700c440b08a0120805801241c1a2081c0441000312a4160310301c92102d800e86a003035442c2d41d04072006100b04540d0b030030100300600d113074041d00350003040d54110003011616848030102d5610280c3d40d94402800f076076a10101180e000081000100003152440d110340c801010602d0341501412040c1e04c030300b00084240c6210008041c0c1120007041015000c0c2090415900d4141084005009220005810542400506030050f4015104070301b540e003403030032107000405003803001d0b64006402e108410004a95016065840800000b405801850600c80084204011340440103281c108040010b0300900043e100f80d011420503016464020200070250041c89020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 924850143 1250 924848893 924848917
    0x4080105070203040317030c03070e0609090411030c041a01050304020109171c110a120201090b2d130b06280e01050105040602191403070b0a112a03 65
    0xc0c1040369241c2c020000c0e10849020340f4445102c00c561019086041c4812105c0741c141e004180089400580300749001d503000200030b094586000c02520010b00c43d404229411200c081c001000c3d2b031400c0c18103212003a9034138010341d000e009400180070f48040400b074081076941007000220014040da031060700940f0080c000051544003684c03070078000c1c503127941312408100200c0001084009655100d100b0040144080001a1058414036940c00c004260303018003a800b159243c480181c04a07600d241424041d0f04401a920301d00036103031245940c030300c00020203044401d01c0e6408020b0a040c140202802840c2d019032006250754075032340001c500c540b0b80780f0010010f40405a4450000910400903c00d035400d1a000514503070ba41c90044070341c0d104900a0a00581141c440c1c00b036a00d90803100e540e50a03202d2403c1c2a01d104440c02d10b24559001f00c801601c015290806101500310b032413194410307900000c0304441c58842d103d090b43e10b1491030346a0302030360317180c0072070461600e941d080c01540d01c40c200c4c43c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 924851393 1250 924850143 924850151
    0x914010c110d08030403120b0906060306130e070f0801051e01142e02060631090f080a0f090311060a02010e0f150a0507170a0f021303030e04060e0a0f02040801 70
    0x81e0a00510b0054031f101d06995407458150a100d040c0340c0000c40d14880c130401400c2520303664501e000d01401849446588507001d84600301070010490a1024074003810a4408844082d490190403a003981c00140c98400790040400010100e0301c000b0941505540c1000000384010034000c000c079008140341c0075003c07010789031a024038100401030307403903a0185911030b400c4a51780c3e104d05082000b100881300404c0d05c40700c0007455a0000040c0a0518420310384004400151b40040f900c03201080701900768100c0310640c00003858154250003440030080f100d41458800c10341e508541d42c02d030303604542400d4035124020104d491a4068402d41042410b03500031010358050f41c0703a25402541d80d41c64038486001074003c5000007498500e4a1141d94410310155990880e1300031490004511404094404d07204203403a0314041c40d030380c1081d000a00c0c182c5441080d00d404103265080080980f0841502684540d050200030829143d10b045001e8000a941d00c0000d128400001110300070300ca95806100e2950070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 924852643 1250 924851393 924851401
    0x60403031d2d0906090601030c0e09270111040b16170a020c01020133080a03080a0c020a0c090218090c0c19030207060513031b05010914010c110d0803 66
    0x2c0b44800c014a501480c2c110150040c4404200100304100e6403140c001d04c2c540001501c035882508150800c0302142048000c001d20b150104000040c210303817030601c40300004040c0d80c3c541f01400310802a480304030003c0044200143e4005c01030f104a118040e00064003181401c0210742401c06054100e9216080150402c0d03c201301d01d2450f000210081c000d801259150422540103004000040d080c00c40c1d1404038040406401e04030941c0d0f99149480030054090101c2c003008104011030302117010b52144001882e050b9100802d82c0d0066414004540003a0075020001c1c10302a021001d43e81c40b40400741e1a09405806203c0301e51140003180d5100300c0010034054858041801440712908120950312a030703020960311f042d0b02805000060042c0d1003003008001191103840640559000f480c03034622081c4d5261a040500001c0c018142000f00e04003400700050b60300072440c0c90050180c0c00c10310034800e102e60006010b2a100c194003802c031103160380c0c018440d680e4981c20102c00c1c5078003000346d948a0034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 924853893 1250 924852643 924852679
    0x7050405040e0703060f020406050d0e1c02010504060501060504230102190c260a200a03110108010503010e10110c0d08070e03060c0301030305090109080d0f0201110405060403031d 79
    0x14944c0f00594016140480c803455040d824001c0364142c502d1038440030320344244084490000d22660340001014058160002c1c50702418030304082d0b201c2c0d202d0f130002c55103040604112007260010380c42441845070802c800c02918029100e4428021a00f18120411040020050307044c1030015150740d401010060300c040802c1b0840f0040000d568080486840204c002400d800b240795203250710a0495001c18081c000080c10150f41003041500000100180915207002c49c0c02d600c0a0b1b001108c03600361207000c4100c42d507030250009d40103008c02c0300248140c80003942d0180d121800200032410241d1521214000300290404498024480004031101c41c0d11010000b480342d10155403400c002030081842400c83d250002d034042c014040380400074903691940e6001d03200d90f409004202d0500c49403040004003041c0c18040da011b07401c200e803144d02c00c54801724002401c54403443c04041503104103110a000d82e40310402038500f52a4941445004507a10303030700541d55200c81810340740d0300400c58021503007140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 924855143 1250 924853893 924853903
    0x10030c170a150509091f090c0b070b070806010e190f0905060a090c090b07030e03010911030d080103050a020f01050c030a0e100c02091f0b27010206010308070b07050405040e 76
    0xb16040d01880001515a810000724041c141d65004580d40300250b0160000b8000b44011603035a480c600000d00c1001c45c1d0b071900080e10a5074882d40d02010b000c038000c03041c006041c4107254403088915016960780340c418006016555010000c5029040701214207501400d41c81044019089015403180310721390711503000c0041e10049030054050301c0c1104c0300085162042c026016041e000751204c038034003410004540070b130307410406040e01001940c803408002c42e2801e2140322503e07405050140c050404032000d05180c07184025408041010780001040851070204074a040a0b5044070604100300c0c04000499040c01914140150b42c00009002141c890b000342040300c50303050aa6000d072407074030007007810341c2d8140d0104c030040d400080b00700009889440d8544160140036549900110b440e80f160a030102c2504142900c3d00c40b0400051044c80c5020719800500b42c040702440101450360460340e4001c0140140b910003801c541d1040301207418640900c0a0700c010709000380c01040460343c940151a92a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 924856393 1250 924855143 924855161
    0x140d0f0f02090a080609210412141b1c0303090b011d060a061d0411040f0518040c0b03060a0e04050d030c02060106050a140f0406090f05060910030c170a 67
    0x103103126460000b400302e00841c855209141c464050070607800c0340407c5545040400c0380c4a88800c000f00310215a000394120000959409120f54400380444403011516106984116254500d1391880f0703118a40d4610700c1001c04800121400071003199946401d40190503d620020185507006001051401c08a6200184134003041d19a900c981c0300c440a0140441990042c40d0005249100800b41c48411032a50501004080c0c8005003405802c240919140c1040d001801d08841510081240c0d1500c152800404405004400c0d21401c1a640b01030b6070800a10801181c0c81001c000a2020340c2c9004500e0001d00202504c0c10903032601d454400d07100d003007681d558000b0038071303003c42c1c04c04003480029918162151a11118941030f0909401d0741e10410100311a0071425040008400c03001041014000400c810b40b0782c5a101030074070f250315841c5085904024010842800300ba18195280e80f80f0050f076480e58280020103805003102210000c01c0b4080c188200c581c25814032130002d0f0513620000d02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 924857643 1250 924856393 924856399
    0x503031009020a0e0108070221092107030219262401051201020c0d0801170105160302070203030c0f0c031e07030821040c030b07080601140d0f0f0209 66
    0x2039120324030307501280107203440400040d500b0006030000d0350040c1e940603003102a60044440d1404648030640c20700c540c401107100941400b14072a80c1d1406c013550340e20000324202c00854103040b48003000355034070951840003a2142e5034a842c1d4a040c14516940da4018080192031401c044001c0e82c140070809000f429120002e2060b004d494015406c50f0f10240184002d61500e6400da910340002c2100f061495004050f255608100f407140c2e0403c20002c07103403902119200c02ea550f40c07400c0100c1c59044041c0e06081d4550b4186010170283e219042410741143d500d6090068595006001080c95801229140c80592082078001d405201c3c00290280e10410200c080314610078102280402d400d540e010682c20507403100400344001030201d0302400003411181c3c0c130900c60f81400c2e8080c032101501074400743e03180410485c060082c445d08036017172680003c1c0760409900740c0c14120002002840c0741c400c0c2d00d8945030085065180f0308003903003092b110320000318002d00076a0b40789007089001b03610a00090384 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 924858893 1250 924857643 924857671
    0x1b0602040e0f2202100210051303020d0903030207060f03091406100b0405010c020609010c20010f0e030616120606032903060f060a0b0706020316031e0905070909050303 74
    0x41c2d880e0140343d8a48045071092143e00c003007600358203124140003580045002e41c000d03000c0d4411603400c51322810344030310f0b09900d84446100c4182070180c281800c2c40c52610422001d00802c0c00400d0300064010b0480301503142a50a011007410f085009000d0b0032402000400703400b1040d042640300180503401011141500542155100da00a02c180325a114141c0480c0314010a4400342c54030202905d429070042c104580c04010326901d60160501200485203005119103454103075503440507640b00c68810a0030020180325282d4000303507031004014010303090403920046041e02c02d8441c0e0211510031030702c00020b010003519072001070b0240075a02240042d41104051141c048003895103242d140301c50103809444540c0351600400c00300c80c00104803a0b000a0145030024452942d8401408910302a4100680702d04055185a04d280c918844c002d04141c00c0903d0002103108013450040035410b03200700010504614600982044c52580c407220f00d0504c4d10030b802050200100c02544101e038a003881c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 924860143 1250 924858893 924858901
    0x105090706050c07050f060c010923013308060c04080c190b1e0412051902060313060e0706030c08070212040b0a170c1e0304080a1b0602040e0f 63
    0x11001d000c0d5515a620640c07001d2820040340c00d041b2075100012101812840c5403084002c074490070b4a5080d02e08884007a08210540704049444070a0017054000c03600921084c40382003410804055083c221901218583d0310420708060351401c00c500031b00705031043d54a91b02c0e022000300030603041403240140501500500698610b0091841d070a0707000440c0d5000c84080c280300d403080c061f400400d10240c030b112146040c98110702070000030380700800f44401d510449202c20300d006414601e00314030030742401c0090010000180c0d10b440c140e076882008141c081d62181c6150501001501c03620005200502480102049455158000e40c1c01c424181c1c44a405075260244100c3c0da9102800c490706050703409000503c044c0c0c0406005003204c055910f40841c0f00c40310001412150b0100340c42039810554005031032614400700311311b002d290817509441a41589010344540d0624400d031800c140410014240028410341070000a42401750040011512641c407440d8400441a0035039003046490f40080000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 924861393 1250 924860143 924860147
    0x702070b07051207080720040f0b0d1104181a0702070b0a03410a09030c020d03091203020d021912080411281703120405120304050105090706 62
    0x80c0e9016074007100030140d08031140d410f00d8150700f00b854111107011041007208007240d0500401c902d9481800901c41030303080004108001c4130840d0100c10545810320784e100c40c2d155262101c04500a80000981d400d4441c1080060010542c00000740700c0e41c103811034070030b041c41070368041103500000440000d040390300c03480002d076a50079862103602800d91080201360700d414404d4015078801340310402414a08280303140c0c40741d07851103118000b50241e05d002c51083c0c800350030700c40d04942014200e041007059184030f40b80100001c15900c0f02034000c05038092000101881401d00038010a44040320b04460801c0d031070001d40f1070720380346000e6005104a4401d0400380d034940d01d0042109900c1303030324040c404251400c02d03110301100400c151004650700b242480c403503c031903014907003086c0710712000414a4158416003001d0905a0004036001c5045117030031034400c0000040380c1600781004255011681d4602c0c04030710b000400161011b1640c1c002c0300b4030040080542105020b000c0d48001c1d42e0752942c40e4001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 924862643 1250 924861393 924861397
    0x1b011a0418080d1127040e03250506040302060f0f06060d15090e10060e0402090f0a110f030717090d0f1209030512150a0329040b0702070b 61
    0x9182008550759480c00040c0401009240c0400307102c4010032000c88441d29110342d50810b80c08840410b94034501041c01e4a002000b5140d40903040b139041082c0040c0303003c07956980c0134413440c5156180e0706880f007403170032070408104214565208003299010300d010300e0020344515099a1403040300d6500001718460101c0004114490200a00160f00f004010740080303000e003c003006000c440c460004d4020820072054021a000900c10350f0080c12501b12901e425012207001e584007a40000c00c0405100050fa1120310b6070b5080b41c030142c0d404030640c494105150061115448544050100084000f030710400311003d188600b40760784880100310306030140059208070440d03401d14140c00c403803540d001480c020201445c01001c54589490540c0b078002c0e1510884001c050140c01088001c1402d0307004c02e00ba0400282e00400c004901021090408041000b403422400003c010880031031100c0c0d94442900040340315140c54441c452641e00341410b226603210410360390680107002c0c0c81c8000c940f098003030017 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 924863893 1250 924862643 924862661
    0x2009040228110c01050d0209010315030309080d05120c0c030d0c09030b010801020a0c0b0711060f040b071d04270c0503060604270203161404060f0e0412051b011a04 72
    0x40d140d161641c10211035000b9130120340a40c0c182b50759007041c02c0810403511440e80196129880b401d403403501b4a1001c0348ae026146002404104003005545a80c03189441d003150081c0c80843c01c691265070910240703045004804010807102e191240700d00350303554415840012203000c2d480141860b40c9404000b405d07840b070075002c500810b00b90301902001982c440c4139168000c82514100c81ca000440803418104282a1081c40c020303290b82041c001480051b804031504010541880e42c800e5401c242091201007843c01040d210f55551289002c03d02c003101ca01c14490341e95550700c001039080701e1a1a03141009140101d9003c0c0c85403c000503200d05262040389003260001502d018040d031650320941e0f060b03038002c03000c0ba00b500600046c61074006584120401804c054503d840d04071461400380000c03910b0f290700180d42014446010005080c02410890b000303034100030340d0b144040c1ca061080d512031003614000020122140408042c040d0190b010f010940740c2c8940d817040000610f81048191142c0b19 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 924865143 1250 924863893 924863897
    0xf0a030b191104030615060816030203072a0302011401050d02040f0b040524060304020619030908160c0906080d0c141e102009040228110c01 62
    0x801c508401801c45804403060000000c0764001280c1c0340020b80b07803c680d108a9040391110104c02958103124041e20180040c1c1c40d040310385141c0004c00b60003009480d4288814140e0001c04240c1042c42090300e4640740c01d1400030072084501c0740d0741680743c66580e4a429070065291998088031200018101d50480320018413816044006408010041440304898144640da80d9030300004e98855002e01c5103c1c109144c041d01d54001c0c2480e0520b18154101074462123442c0c100100300c016500c035000d8444d50360001148134030711892080d082d0000c2407248000341c2054030205107403081505400f8500c0f001d038811612086010794440112d0150b070a28007482006070440b0404841040c4144614000079000d26840d150100d444114242040300b002c10004190308140c2216074200380420900207040243c0078104080e0341001042c6c103407200c03d40135071000e402e00028699520398454042c0c0385018103d2400d805140855100150341c0c0002c1410140802c0c0725004901039000c01181e0b8101b1340c1010b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 924866393 1250 924865143 924865163
    0x60b0409180605070806191d04052415010c0507140307211217071d04050c090a060c080405010309020414040b070305090106030c0302090a06230f0a03 66
    0x26810000740c400380340c0d0150108071000d5460007044150141900824107600c03805071a0408a00384030b10240000c114041d441d00040041003140e51004c0d01c01c0494600354051000b0380c5451074102d0610140c0006100d04200c014142d14103442400079580c0901410910641c4612520005403401c646c421070141560304206d000700410b0082030081020384000600f5200400d4841c200015001c0c90b82d020704010b9140c81031864204251940c1740407626201d4203100f10f91001541401d056418000c1442d000c04c00c11026844115000080d1b0042c09400204140719a26000303a4100303150b0811071240b403084169440000c1d07418000c1d0354003400182c204501ea407904d41458010343c0600148101283c00503036800503c002040d001c12041c1c0100d21a0071b500030389003407610004007540c0c00a890004182d240600c00c0001660b200480703c2101d5050300d40044543d41e802100c0d00030515544800c0e0900d0601c0d41e0124400099100c21401403021140708601d0f89154080c820403003000d010051006c014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 924867643 1250 924866393 924866399
    0x20c03030403150e0f0a03090f0e0a1d030705010f1406030616140a0302310603110d0204151701142e09140603101707030203120309010c03060b04 64
    0x21048003c80700010301c85000c0380c2d00040099243c80c2c42003401c0d040e100b5030070401d01082010b6010342c000e0b0040550b0000c0000860a100e40407208440280c4100207043d9a607003612a50740040500c10361a2141030240d0351a1660350410700d0181094049400d00149814890070000c46c604d4000d40c022000940203241d1544c542540d180540e400c02c1d800b20034041003e01c20020a4071080040c004001076607005611280d211811040e030b002d8080c08030051140d1410070034626003140c00318000b00c920070303d0040746e01c510041c0070484500c21408600300c4076000003408203c0340c2d1007882c003415100c1c980c0d548c0b0b11442085076880640c4035003801509101c29000d114941c00d46012840510300c1380e902d8041c11032038080d80708203000381c034069881400030850380c440c2084480401c007203243c0480c82c15101d00e45180340011000300c054801d40900b003500c202e00c641c40045118108060785c0907540c0a001c46000c1c680044010300715400890b01000d040d800c041041c508607200c1c0c000c140c1155162680b290810b41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 924868893 1250 924867643 924867653
    0x120a081603020a0f20030a0203031827040c060315091d011b09080c0f151312061d1b03030d060e0a11030709030204180b091c020c03030403 61
    0x1200e06410340c21846128004004550384601c6080503610515039040006000b044600380c941348004174030712903040070748604003584010084590312640303036800c560a00140400200c2140080c00320150340f06085641003141d9030040d071002d0165002d000c104d4041382d41d0360310840660303001c1c040d00145503a019030200941106a04000074029402d04c911640ca003864061900315004003144032610300400c0d94136200c3c13540001c6104082c0070940040e0400a0001c000302d0f6030344040e1031000e4020416104004503140c1d0030310645070f40c944050303e1401e034141d039801d1401e00c245c580360081d07421a103030151a91082898001c184e9000303c07080c01401c102080c410038820303000401d40c01786406002c10054044107031031611551002d00f0104050605c00e041004540048038000308a440080c4403c1051008641d0040c3d100c004480c1c1c11640442c2246105c102c4c501d501801d20700c0244080d1035281400340c80f40010802d8441e01c01400c0d828082510710940032a5a0303598002c00c141c054200300002e1020070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 924870143 1250 924868893 924868927
    0x2c0d09180204051f08130f080f13031514011409190c0903050636031306050a0e03060712090203033a0203070e0d030c021e120a08 57
    0x40d003406001030a1966440200e0301215481090081120503003c142403255001449190401c01507000b64580600c0d95958100d1030b044e0f240041c01c1c0d40750100703842c949104c41d03508a80003a4000783e140003295030399140c801c01500340a10344440e49402d0001600180d15440f82c454101d0707060411841c40392001a00f0f0021265010700030000c0c000842d40c640c40205068001c1e120004116580c0030303c3d15103141040350400c030014200c5003001e1103500840d1702d00140e906d8074a42c00740f894480890300c40d00d1807944a1640c401c04e1101c0030f021983d0040084e403203412901800383d4003480d4540201041c2c060040517250741c82241d980300429081c500062a9941c540d10040b011803014084903e13060480a202030b526421503100a010401c940009114402d41c0282810004a491040d4150300745aa0f01801d01000070030041d004108080b403000500d0310400d00f244800790043d00502c0913803900242041000c9141041071b00400c501e0446c1131229030700040c1c0300100c58200038804e00b003182242d0401044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 924871393 1250 924870143 924870179
    0x30f02061603050415110405040b0306091c02030403020a090209130e03030c090f060d05063d02030d0606030506181017031c05060f09090c061c2c0d09 66
    0x340e640c0742c440c0c411070120307121b9800c20445003403240f0b40300c6140200704405e94074180c0e4243e009400500c01d00850782000200329000c4403851460240d04108e00000701d01d18007460b440a5440310099000081c0c1c1982e5500400c20075200b0746503e031442c0302d121814403d40350040001c150f030380c1c000c0000400c2a0f00e1680580701c4060010006491301e4045000100c06821070001040d01030f980744180301c070501d88401003080000b01003038900c507847d421640c0104411003520030303003102d06080c8200b420394600c01d008072102c080c108070b0100989601c40c18014002e10003114918000e140c0c90000d00218920150642e20441010303000b480354034200391425840c441d0300140c0b00e10610060210124000c1c0a0b0039200d101c03401c0a50000e024901a070800c04010411218140500c3c0d40c10b040c00003825010900303880320380d8140c807919541c400c60012072013500c01e0038007036840306071a01040c801d444144403580c0d0250350805241120420405000507182e41075540d41102140801f0f40820071140002001584c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 924872643 1250 924871393 924871403
    0x1403041a060f0a0621020d050a0617030a050901110a0f030f090b030c0d09020a0b03060a0b070809040903091d0a0e01020a1b08090a090207020a06230903010605120307030f020616030504 81
    0x117262101c110000c0c1d81101000840d001d445d241045040002803090600030311052150318440700601c402191030f403241d880d15500f0000700054002070f40e4014005584200507000c115810301c866800e21401c070f8000c0c0030040f0700182c000580c4229580c80385400c0c500341c0d002026550315540701c82da080410341c0d208070100202c840d1101480405691501d2100d002481400c600c43d54034600001082002003207038109000088040c81008003058144050381c445007820340340006c0c003808038281a05c490016600c48020f00382288201c0c0358401e810725495004841a03071013440780306c850034100780c00c7c1e00484030310000207009000390300441074140604090741c0f4000c42000340f801c0c8880020511074882504003070b2000382c000032010111b04140140300010050780c50a6048501100b54a404801182e040540c80903030104400846980c00c3d8030040007050010541c80700e030102c88036065107a410001c41a804640e504109284250001c01c41621034000008510b40050118505400a00c4003620a0700c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 924873893 1250 924872643 924872687
    0x70b0a24062a05060901150e010b03060103090206210604061505030c2a0d1403060f19080606100c020a0512190804180b0616031403041a060f0a06 64
    0x1020039508080b4084190040c0e000d8051440c01d5188582500c45400c100101072040d88010031640c01c000c100c25054035001d15440e581d13a154040103c0c003a0142c003034041e50041c000030300411120f094025080c00841e07105255507144e5030707580810084860902c1409002084101d0a6490070b114170011903000034403034007003810302180c4c00c150002000075071012001080c62103031034449000100074a00c1c010380039160940e01c00c40c0c2e560441425000c054401da010b44070301c02400d5051382d507035081d82403081c4105401e1008a5071b1603a44030303075900701a5052030060000c08103050300c0902c14030f80580300744e80140c0070708125450a003d07c1091000c582420700180910752402e051001039444014405001d071a510351154149500e00000443c211400000c080c905504001d0070344400d0b081c0c40c240f071120541601658203509090f256581340d5925100c2040c2c0000401c420081e0306e10740004080ea90500406a0780d80320341c00e0040508600c10500d510441040f001c00c00c0500c02c0480c141968a602c00e003907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 924875143 1250 924873893 924873947
    0x5160c0c06050a0c05070e01171c030b0a05031f050124050304020609100e0102010c032c0304030f0f060f02030402061902010b060a120b01030501051e0312070b0a2406 73
    0x504004c1c047d00410380d400a5000100104000811a00941c451140240c5005440081401c00d0340a0540c0c10505140d11010022b03c02c1c0c0e0b40c84d03468001400043c060b42c41d45610b80a2a061060510f0802410300e850000040b50349514400804954a02e425540d00000b8107460140c513540c0000304100e9008404000c14500c945035410341d0014030640e078a2f041882c1900c140060300390344c2101a03031010145030800780d034140301d214148142e6003803951070b140c0c451100d1260342034158401c9800250a003403803052680c08110503a20008001405102c08008000d50705c043c2e20140d101c140d40117903010000780300c40b85041c08416030480c030301d991074000025441d8503040480d00e5500022040c00104d040b8000d00406c0b10b100380248441c030705013482d00b0041c541c1481d000603070141c042d010200e005500f141c00c13231005881c2040910404851400d4058445035a8900780211500449244108178109081c002542c07101c194440e01084001c0004070409003494003c5405854902003d03000c1c2d031140d0404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 924876393 1250 924875143 924875153
    0x605060c010203061f0f0507020307032a1406040509060d050708030703030513020105071b080106030602090f01020c0901090f0f0509250524070c0905160c0c06050a0c 73
    0x506004904000160b103a01c1e0402c2009420042007030300141e01003024a1034074505e540100b1041e07102d03e40f801c00903114800340c00401c2c0f0301401900b00400b4403414180d00902845041218003100404208850009480b4200305254a049002c615040300c0103000a21039072078100510b50380a0000740140b003d282d199203881c0d20308030260b802440030381c10000d0350030f0901d64036008071503203c00c0011441d64030048a0340028000d20420002610365082410380d101c90800b40c88281e001000040001d0001c80e4072410000025440504283c3c070903110240c100c0040e500101b00c151034994000c107410300301d0307180c1100000581101040b021030140c0c2c400c00000304205901c84e02d03004a4100f0020040409180c074641d1410149001421840407605410070059448014010400f20003426045100d00e40c80302c248081c2c02080c0d001450188003040110306041c0750303408107100e1200030711904107140e00e41c00143c884000310315001c0c0c522400306106000c603500500080140c040303946000a04a0515226 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 924877643 1250 924876393 924876397
    0x21906120e010e06241e01030b01180312030608010c08011505040801110c151902160b04060905100606051b07120506040308061c2d0602120a09080406030f060506 71
    0xf0810001400100015214018104901c05c3d5500b0b07601405401c1986005400c08540740d041c15041584a205501569125020924408174407910380034060b5180d123051101c1580780424040020700c1d042002071000014051100f202c0d4903900c60b200541d0070f0141e0920000300115144003880340404c00007444540c2442050f04005201201e6030315040394540c201d08040c8004201c0c03060b100100c050003114a2019960031030203424035001070340c2c1d00211200c100c008280a00c0a030469419408000c28480c02d42c0110803240d10072001d80d40950a8021050f0440340302c1d00a61001810601c4820311b400c1d044010025120f0285080b94482507a440e94000d0800c4c4210040b5040d80101d800c0c0810543c1060010780c00039000c90f40e214842c3d01d042841d40281c1807480000d04028130000304c11803602d0344c0c9450700c01601a5030340100d60a12880c2084806540030b0601d1000c0d0618000c00203006c400c4920900e200305520500480c6001d01e484030480180141411000340940d031501d0004640d520070740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 924878893 1250 924877643 924877651
    0xf0f0a06181505100203030703091b1203031b090e041707080d0510120b07030e010e0c12030a051b01020f04060903110114030612121303021906120e010e06 68
    0x7001158007000201c20104a2800740e22660081130700020450074250088240e940c040051300c0c00040c0c82c80702d41008003034450141d01c07030044107580480c080b51100d00d0500c40f200c894088d0f00d0a00080021460888003d5840290400001d0302c4250510419140805c0c1c1c6d90003a01683d404651070302d10034007810a682c00520b04490351500081d1010110f902800340c0c0d03511650145040e0065407074451001c202407410040140340100070800030318603038040e62102c03ea040a000c02040044003502c20159605480d500b12482401524814183d03104000115101159a6a6218208580004a10140030007105060103d540a00c12014030b003076410050401004195660342c82c241c91410b008203450710b0442c00c1130400054501043c42c2d410b040007101c0e00171809541503000010b003c80350505101c8404803101e40300b00700103042910b07902594188011b803402220011310400c040210f6030b090603413030302c40c190200f01441d540c403803201c02540c0080841c285460000c0b03550744686401740d040100440e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 924880143 1250 924878893 924878939
    0xb0d02070506010e010e16020d12331208070303020a140f1c0506030c010503060d060228020a0b010504051902030a1d010209090f070c02180103051002030f0f0a06 71
    0x1c010000c9090041b03005404c400062605001680304842c000e4071910302540f2141072050b21002c0c005002c41c1c6610005941001140604910004540e006007809003804d03d009240e8114030082151301d1309031005031130158058406403070326880c0e6600313601030b420030a0501c0c14040ea41034200401d200c84070081120814a00c12191303a07002810303071220395240d5404e8501e842031601c0204240b6440002d0088816074003401d0586e180d03980c0742c000171842a05e0003030003800940081400b085164511010024000d03d00c6000c8030030342c89040301280d44102941014041100d064010003c81c00c2a0f03100c6500324407040b416613443c0030750040400503a4803e6a90300c548070303035640b003581c90081c151340e2483ca0030f81480000d52803c0001000900146406042000259204c01c08502a20300912590070059030203845142e50170308829401c7c1e540c503c00d10043d1a94000e20b40d01d101c1c1200c0c24401c4912a488021000302c158550b840b000c08a090000c1c01d08080c241c0d01c00f408a101065220a00d602464031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 924881393 1250 924880143 924880169
    0xd1223090f0a03050d050a1e0e0102131701060e190b01020c10050a080c09210c03010e0303100b04150c050c09092d03031b0f0a030204170c0a0b0d0207050601 69
    0x10601c5e0341161802004030b0026071400f100c200d030f44049181404192100058085408000420302500910035410390800f0a00c4c0302d0000039601e00030010001c1c4040e641d02c006c001440c6e03610790f01c1c0070721201102c1144120001c6408500c2d4010580c0c81f08101420600c100d4420443c503102140d1200c44c4030300644007240021580c11209548403c50681c082b0040e40224140303c201c6010807801a0180e01680c001e01d0300d107131a50000384007040409444d000041c001d01c55200d40d6003070181c681e40141d0b0b10400e0b0070f55040000c100e00200d103048a00301c40d84001696245d000aa00440c0c0c8908120700440e00e070f0041c004071225503a2541d0106006d0301007500605040b44c00d02e43c8040c51118bc0e050002c0744654407401000c6c00c280c011041d0b03540825481082e43c0000a4848003000c036100d82c214882c201d801c0460718411150b07040d070103030041d607107110850100710b2126502d160755880a90801a80300c01c0da10820b002c0340142c80e010306020345000c0005801c0c02196034a16040250076002481c585810f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 924882643 1250 924881393 924881407
    0x730020a2301030908090d03020a0209040f1709060403060b0118081e0f2508030c15060d0b060f01050c0102030a0209030d050324010c05030c0d1223090f0a0305 70
    0x107164001e14200c0003d0800304081e00030b9656400d1180103503400da620540b00f603158174003403500922403a603400740d000300408002d18041c41c1200c80e0050b5180151200c016046003080c401c03e11604a0b2160207004284c01c3c00e19243d40c0d01c901c081c20f003980724203041001c0b204010001d000180c2c4a0405821014080d1001100e9842801c814004000d4580c3c050b51001e158003100010210348a0200003074032090b04c00018102200082d00b88465006019501c0005041500000c0100b105110380c180103ea480560302c8410403c001c99844e268050300d209081c10210383c46103001440c5c401000c40604007e4100004882c01d1400ca80088030014066a000580c42131300e0315050003404041480d40c20035a046040841440b4a40c00381750800b0f8540040704885a03809a001d6650442d03003d40c0941225591014100910340b248201d1903503001040140f46010322002c0280503419044200b00600e465201d502e00717040041d0b8002400b001024000c10380d08030707031303a2005216039080c042c041d4484d945d441d03007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 924883893 1250 924882643 924882689
    0x110904150c0f0503010b030601110d030c0e0a06051219090c05030606060c070905071b03020c0910060e130b030604050a031704020a03020d020f091003020307080730020a 74
    0x1590301502400c001450604034455a040801c0d80c5c15582802c1c0c0d26500ca40e15280181e4850f001c030404c0010603c00d20340d040030750030703456000300d50f0f4607500c5d80d81c00c40f80e1054a0140076401e20f042c081c440c0418003e01020721210b180c481c0060f8003107120440c503140e81c1e03a0070308540101d441c0c140003590000301e14003040c06581020080f0a0f000030007138518500d460741c080399050b114885070007000310a80c0c881c004208494070401c8920401c01c0c5201d0603201c5403001d4613019558408402d96140078030224400111ba001240350200c04580743c0342c803000308002e0340b801040400788450101084c030326510005018180c03001c001640c4030750b2007a402070480c0c4003a070601a01c101200d10580c5481201c00f810000180c4402c003010f0202c941c15600a51042000d1001400340c00b104500b0507000788680d400c020441842e0750141013100d0003036040d0b50703225031144c11094a42516000c0c0d00c042000807418040708a0400d90140700c00c544101002d244900994002244c00c0155032043d03540030030040309942a15 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 924885143 1250 924883893 924883901
    0x20c09191d161e03020d08040b0d0903020f120d110d0c030b010206090712080913050a0c0e1804030c030903061404021f231308060901180b06040911090415 68
    0x180c2c44140841d802004244250203a803503000090040705c4030100d0000700a100c07c15a4003a0400c0322543c4e4880200c0f000c414002d02000c50107600502c65403c0c076105001c404104066035007200f100b103c0c540911004854090050b0202007a13030b2010070003d039444120715205250611541c0e0b5004540c1c030105200081c503000015010300007640050703408110042c21b10b004807413407640c4031003050789a20071040022050040c1048041166041030100050410154003003c90a289034460000100e005004d00100358111640d94494040d044040780109000f100c0440700c81e4440e00d84031060640f03e540b48816035105000212404804c04180021480c0c8a80d5080e01c005c0c0c40d41c000c415109a000c001000c106501c3c000c4c2141c0b440e0400d0808a400c3c1c40421030303000380c20110401861a0392000c20350343c2d40c8002ca501058079460600a00720000134140c0a41445800000c3c0350000d86400c402c0000415078140b007111101a050010050303a00c4074041036200c2c41c0694a0040b14880040c1c40800b52 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 924886393 1250 924885143 924885149
    0x60510080907151103070b010503011112040b060409080706090b011a030604110f13030c09111b0c0907170106090807061209052506020c09191d16 64
    0x80031408081140310034000595904440703142d4080440748024500036161070890808035411400f0010305101444101c0c02d045040700c009500800241c50042005105070203614503180740500513901140200e01032061154000324005c1c4001000c507150340da07950190344104070403140540c035022520309000783c2c07103036450040c14444103994841c0c0b24100d0031442440300401c1103200e5982ca10364510701582e200103440011450751003940d500c1408600140010040d8802110019015840072468240a01072404080a56070f5558100220114038504a084540c03841005119207212500e803903440c0c901c40b5000b4001c40e110880c1a0078071800303401c180a01600880148108410208484003002607500c046500d586000d03046460304110001c05010070020150030f500c038800024000d81c40042c0140414860380c0403895000746d4501c420303a05e940014081c0382c6d108040600280401d0700301c46601107240da0348440024581210f0300480c030001c0079210041240d511651940c5074400b01c140e900405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 924887643 1250 924886393 924886397
    0x1060806060a17100b0406030618020702031f02070506040807020f0d0b221203062102090f09010917090111010509030906210403030c08010b03040f230102030a060510 73
    0x5060840000502101040721083c1c40c01086030000801d80c00c8403602000150204100655481c2d40d60407001300030341054080c200c01d103c0d007107000d0003101440b03200310ba002e154060090040340c0260121303038010001d00180120820b40800c07044000a0040c00036512442c4218081ca845440030b00620145004200c4c1140c0104141c801480c0421209407015602840044041049a03800d60710240300000d140402810784298810701110a601a0040300907075902c030380d81e143c0c00404620600800c0c0144040a9005012075001c149078202d030780e80440e0711107a41030000c15951440d40d81c203880d080c0400c10b040340b6481c006c80c180c125903030b006000d44002e02c000c01c0248880d043c100b118540b01c0c0324690302503205990025401144040080300d106100180e40544842441c1c80e060150140060b0f003801000030310640008100e04410400b035900882c2c114401c0d074051506640c2d614201050000703003550000c440960203584d18824001103101d40c41e0309901207001da14103024800b400c140400f0082c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 924888893 1250 924887643 924887647
    0x90c0c0605010b161101054312031505060304030801030b0108010903211d060a060f08060601030917180405060303090105160c0f090c0f020303071209080d0e060106080606 75
    0x8101d40d10040903542c00b900000040c101d00c412800580347d43c4505000e80050b03032403081034104180008920514080704040c0a030380e41c0c3c1a03800c0880301c940706440d0010102420b040700202e88a210307500038446074016005090000e03440d03400180c210381044078224001640c0000600401190556050060013801d00034801800310b03a0300502850180030140c4d0b408481e0701c05100f4910030a400200046034040c44401016041e08109030311524201d03940b440050400303000180d248802c0c4c0440003214074440180c81607858000045014103200c000c240ca07138100c50540d0360b00c0c081401004224040b10203030110110000d0905100661b4801030909102e0f400c05c0c464407003181d82100468000e00d5942d07051940048142c070304100c0014680d089051b4030003c0520118100389540c1c0000c20750780d456102e401c6000180013081b070f40d07440115204400100c900031505035801881c2c002c941020700c125151030400b90b440d14508100e175600c44240007594000300041005c0381e000806650044401c1d51514 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 924890143 1250 924888893 924888907
    0x48010f111204021801080f1504020a2606070c0203010608070b090613091109040506091b0a050f0a0512071b11030a06110c0d180e10090c0c0605010b 65
    0x1446001e404004004415070740005002c44d980c0c481c405003144000b24151046584a645955a0328800740c0d00080600c1194601c0e5003420390207242c28031550340148849401410300c00707415610580b4156404418903010003486580c507050026078800c000642e640d80d115189030040500751421a400004140c01c00003043c42000342e40c0088680b07a48080c1c42d03031a92540c4001b50980402d41039030004e609140751041880342100480000c0c03419090444050149440361403c0000320407003903554102c12004000b4403d01c8507940c001400f42c0c60340c581840303030424002603d02c1c4071991081d55110000340340014120035403030f17140c86550742008041c90b05c0c410588140c2c4200b20480280304020302074044090340c01c1690b9904001c4407018540c0b243c2d080c01400140301c0702c42510f4024601d005024018510006099031044600c1c2c81c100e2100b92001000300d1900c80b401e0b2942ca4050003000072340c0d039184400300d2501401c2c0100148820349a4410b00d011a15003000c6c001c0781d8043c0c225810400c0200041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 924891393 1250 924890143 924890171
    0x10f08010e0f040221060a05090d02070e0a140426120619231c030c110d021009260d12061e0503010501170348010f 51
    0x158040c00300b50301c0b0400c94035280000340301403540011680010b503480c044040c0340321022481a00036481c81805200e41e864461549480e80781d00c09031480147d00c59101000311034520300801303030003540340f1600040022103003201e10b10b41e46003144c00340e0300300052040c0e0450340c45070001c0310040e002010825605200140d90440c1c0360b540060400d0b0301c500c003c04402c203044600800d1902c01410b65598a808070780302d80701d0301262100d580029a2044190043c0100c10ba0400c4030440d0400390300d81d1f030364046d405050f514042d02810504003a500142038a01401c01600e805800000007903607a140c5107112841c00180c2c4120720b81003004603c460400f81061207441c030700011240c1500419080000e0341c1411262400d000b041241d10103a10409420a00c00010746000321201c1541c80640003070040780c2e00c4441030780b40002481000d010543c01006003210f40d07005c00c40c4080c0c42c070b8030480d45101e0312000e000c00c81035044180f038401c03059210f039184103500c82c48091040da111148000d40a102400b26030001e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 924892643 1250 924891393 924891419
    0xc081902090a0506091801110c0a0501320c042c16050a031a060432061b0309040c03020901260a0b0607020409030509031009020607020f06090a060e010f0801 69
    0x80c40c030303a1b0703c0c14260100c05150a401c001c5d00a0301e004407181d103c44912101e141c0c0d503096000117440075460901500c2d892040f00701c050100d40742070907414040c0350303065404040480c4001c02100103076005001c04504800140c1058807803000c0b484200c968003212002104110002a100188a0011003170710300301d80e60030500b61000000075040004541103e480314449001215a180c0e0784880005004101c0710f06858907444110400c030301401074039031008003408115206000d200c2d80101c080c8026800107849044880d0110303a9141a682440c8108003c6805e4800758406800400d4010850a8465074010803215604141c484090701417550819410300340300e8081d2100719a86d0312481aa202929103204507120280d025104200c1030280e410014a1038010031040c1e4400d0203140c0c0341c82c15500040c010b4a5220750010242d40c41c040480c0d003048a0544001c036030f1608000d043c484800640e4030303c041b12000f8a2035850307001814204800044c6005861440340b030074086240c00510410341d0b03c8203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 924893893 1250 924892643 924892651
    0x9061d160e09010e0627010506090619030b04060b041425020109230d080c0906090a0b070507060f1701091104030b01090606020d030b1003090c081902090a050609 71
    0x4058803140c403201c502e01e01601800c680100d2510858050081481c10000d4010030703000155a1103000c4c50103000b881d4269001551090b81c050900c5000c120315180c91403c007401c00c1852044114466a20ba880544003142110107807052581c60142076141c2c14107010f5021410945112540c07645846012240d004c0380b00f440d880303810109000c001c00002c0c000d501501d4403581188803105a10030840c01c03000745c40410701200880b0b01030898500a4140100500740c003070550409010306103a08030050001d0b5400c401c0013b90b20141a1400042001c880c8000380380b120b002d50050483d90b400d11002400041042c904030f03003008070f1070711084a0200241c1070035040d100e940e040410440705800315051140125040135000754905800007a0110860388000121405502528002001c83c1810380454210f81c0070f0079001041c014001450074441d0388808582807181805140380d03501c0702c0d0302529000e43e00320001c0e004070340315007044190328181c0c600304d41c0a005000184207600c0d200000c50410700000d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 924895143 1250 924893893 924893909
    0xb090603040b0a1d0604020f0d0c0b07031e050c010b2202131d090f0d050a081f090b211509011b030519050f0c09011209061d16 56
    0x210201d482d20741c1c203400c0030001300108141e1580369031448900c6900c601003600d04900c00c0084054442132402c0c0041c1c0200c41c5600840d19010b9540303090b01d28500b50780321110840030496286010b41c3d6010b40d62842903c0782d0700035662a51110350380c0481c2421500300303014280c81140c1c0d1a144a403034400c00c40a50a6000c50420056200c00002031420070181d0070307400c00c80e002c2004018240c240387c40354082d1340c0315401ea0412552110811000075496034141d409000009104010129929001e004015040860b14445051a604101040d54003050750b8028514080e00d90312071503a14034100700301040403061034402c14114403441850329990a150884840c242c1d1032080002c03440c01d800e6100c4648804582c4144c000142460030081c0180800c80f40d11081413085007055a0103070203442501c2c13040101b1140420141c50303c001115003500300e003070464100500b4110b102800e80036030240291003446103001045040d5419401302d1407107802034030b0300300c15882841e59500c031140030103050003191408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 924896393 1250 924895143 924895163
    0x907090b01030e12030f0c04031509030c02030f01150906080d0c03200c01120c090306180602040306050615160803040c091a01030b01090e0402120a12030b04060b09060304 75
    0x4500107801420380f8801c2c51a072401404e60081c1d804801078020f6114600c0b501402c1d10303c2d40d842007a42c4450050303000141850401d0300300ac0000c84240d502580b8000d00070300700129041c0f15580064540880c00140c2031107a51601c860b0314910103d0040300d8090a90032070203210180c100307088250f80360150b411100c2000641c0825006040c021390003181800400303120034168101031000641e40c3d0000a03507840c000790042085800c0540144912042c00109030340d03c40b400d500d140c81e60f401900080c0c010001401507610503000149003440100700451007041d0101d030a00d0901c0c10032017514440800d1182d030303010800c0b04280e80c0b000e07813842c12440c5510900c030310f0312502c82e0305208003801d0058010b0010246040f1700b12220308070b20004448071060136030741400380d00f4032113004445c0c1001c0c03845252044002040803038010310740851140c1c0c645910b44111a00307550b05403039111603c2114407540b004256244404e1195060901844000d405920201c6103407241c07503000714980e1310008001074600b56030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 924897643 1250 924896393 924896411
    0x50f180a0e0a060605030d0c032f01090b16020c0d2a031103010c091503050408071a010608010605120a02030414100f0b0a080d0507150c051908090709 66
    0x3141c1c0001c41191280302258a08040b5280c030030b00908131405154030a11030301802d41302d00c03803280040d0841da640c141e0b15a00601c12140d1010000c40c00241103207180c095188609081500920400000764000c0344031005034201380c007010124030b080d03102c16011500b00704508400d40e2a1001c50f030035a42d50010f40182800324280d030795440c042d0011280680c40030303011000010310031041d465007880c100c218020004103c0e0000244c0e201c0c0e119200703280c1035510307068500c0c0c101402039020b2035005001e12000c0b440c00c079040d602c200108408010028100f0f50f540018004564000f000c103003d000303079050944c540000414407140740032004042407007050300040001c0800510701305881c8607d45070700840310320a400c98208409084040e000070344580ca4072428034914604082c080d01141e00c1040580004543c8013011a9141c2c007181c8140d82031400310829410040c118843d01c58404140d940d45d54480c89e10480d89507088040c40b400104014941061045108000c40c1c10000c8a403054000520152 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 924898893 1250 924897643 924897661
    0xa15080a0905061009050604051504020c0309041107032c0d0213050403050d0c0c0c0308210a060603050603010b03120307031d010c02160308070213062706050f18 71
    0xd008400100b060050754240060241c001400400b40c0b90881e00030303c501c2e5031b2101070008a074412505051188010504c011040c1440d600821150003080250b80c50250301802040645000280d506c040c1072001582d0824103038403540102c1d0300c1000a6036918024910b2800c200b0140402c0703e4a8822581c2c0d010944c11581c0380c00c030b06210350002003401d020034901420013a000303400c00344162403487d003028681c10b100d43c030982c0603400366640900f08070615400d545601805411061041d441c203030b0b50a13a041a607403422203005128408088020036824100030f001003d8420203002540aa81407020705031040d9800316106d850100d6103417003c1c1d113965801c0f4044000e0217100d00d00d4240e144545840c1a44d540041d081100140d0854003225248010040f650010000e0340c4400b80c00700c80c0a004d020700501d440b0710300554003000100081031454440760810f0a0803103510078440c1d00140c0e424180303a04412802031800414040300c40580300311011011902c4261034682540c0d0070b54000700060308542e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 924900143 1250 924898893 924898901
    0x1812030706060e15150d1404050d170f27010c021b101d270c0a0207230603090d0e0405060d0201142506050f070e01051e0d02090f0a15080a 61
    0x1b43c2040f20910071020185000b0040c02410744080d102805240201c981c0d80e4003d6103400280c0b0141c13121161503a448211200300000080d28646a6403191613540540e02c55420004c0c3e140e17280f90780001140031000e00c2c042d1800c0010b2261410b83c9088881881c40d9039034510100216071071509040da4101c034a2200030349000080034406920480d0132405c2400c80e0b00c40200301c1c24014044800c0260b68460b40d008042c9400741140c02401a44861010300c4141007054054000030f809804010440030102c000a0503600211450540e9a02401480d54102c0e806810a000440c1c00d0328100200d040c41c00114150444090004e070511101100840200849408403280813404003405012040b400380001c407000f0000600782c3d001c03070074407010500b407909041c20503001d19440e8458a040c40d0300040159115003250408800390740390f4891080c4900003000050011603506400180e40c0d0482c1e00420130305000c0c120798180642ca21075414032070b01d40300310740c00301401d00b5070300f840c1000e50744081004000e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 924901393 1250 924900143 924900157
    0x151503060d140703200d1209080109031e0e030d0f09050a0608270715050d150503121c200a020c01110a0b0402061812030706060e1515 59
    0x2809804012541c40b880c08242881543e10a5800301310844005040d0142829040142c030b5100786804c40040008460703281600b02d8141e5400c1400c081951010510708507902801d050b0080307003c44c840040312034000e003818185807159080941c1d013504031601283c0c1c0c0703441d805510018002038071440072160740140700850042c50003d00c90800c0d6600c6400c0108104025100d0603e02403000e42d03180c07501c000141a139000894418004c0200a14109609012801400e00c8005020003002103812141041c00350003565844200c0d401201d0380303841d080c1032510413003900f0321a66074000d20048440d040e20100d140244811031401042041d00c10003880f030322900d026083c0c0e034145000951100440d401080b823047c0c10509807900421683c1090085490300c032000c1006008112034000038006240c4070001d0808108840040d82ca40010000030500d108200d085141c4154000315501c408c0202a0064002828a03251181164182910340076900116856414402d2026200c24000c0d2a4a02c0650b60302d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 924902643 1250 924901393 924901403
    0xf0f03110423042306060306121b030f0d0e04020306030c03071215110a0c0507090c111209010903080904090804290910030b0301230f151503060d 64
    0x60161502084010311001d50089008a090181c2d04c50038801c1d1a150820031a442004054140c1d50b000030003080d60b000170304850788854a21554040510204820705021400541c10103621080100b010f280c800c9034010b0100319404010386002d031940c41820107814810640300035891381c4030980000c0c1041440e011998061143c41c82c001100700004d06805074581c0208004242c02d84003160440681d14242d921960180b001c00101050510079034089419500031750984416a032034843c05401c0c0c504080d0200b0000b100f0700480c002c0f010060000c40140c0016400d054502203c100020300800564400580079820104030038a10f81c840da082a121075600588556035580c4410465108203030140d45020f13880071044000c0e0207814207004440403100c005004000d01781800308102c001c0c01d061030b800b503059503c9000c00310b501e103404c0040140ba11010b0302c042685290980d0829000da1000704490740f0210b480c1c07003080240d03c5e10182e060a44814003010780da00d03515040400c1d42c440c00a400101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 924903893 1250 924902643 924902669
    0x1c080c1608180a03080a0c1103030a0504031e0b06120708121911031b0f0d2105010e07030e1e160b07020f090702150c07120f0f031104 59
    0x400c20000400030075100c203030b0081c01c104014090081c0400e0315440e00000305081410802604083e005a00c41c041c00e81c460001e0281309064030300803034250b030015501000810000700c0c00740b08000b4051b1f03c11001568508443c01020b040d5103034000c0d02c24010780664000d009100e01c0302c3c2888011310489001d098040c0132207116003140485200154403418180d0702a005080c203a1125030701c921809540f480d800b80056085c015180302a00c2149103a0f03144c21101d202d1249041503031201403210040d191741507114900c6405110074128110201a40c0d003500c0365281c00014003c144065028a0b00541d482c507000a0b0b05549403802403400071404002031000c032031501e81c102d900c200050201e0110802e500035112a56803150045554062480000d52144008001000c41d041100342294000582c0c0304554201100030a0418007100c2500c00304c0e940240043c505040c404150881204c006d500e240180d070080f0020401482204000010010541c61b0306813150a60820800d0b28007038200d5403504a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 924905143 1250 924903893 924903937
    0x4020c030f0a090f0e090c1903020d0803010504110304030c060c05041d060102070b090102070311311d1009030e03030c240412030e15040b040302010501081c080c 71
    0x10748111428030409169035121240400c05e000030240c111b005818131001420794841040c1084007060004642c000784e42d42010001016aa43c10014084c403401041526030b42e505100071322060b19442e02170480041d40400038030001942c0134101540c2c1c2600040000764007500c5190881d100c1c4200d9001001c50340d035000c0b02014542e44840c48a00a80098007290700241e6603c82c03000150240c1c40300340c0c0c0541c014280030404516214001c4e50304140040c03520140300c1c820042000104054a842225541c0111100782e480e1201e11070142882402281c843d0002510380003d0754030030605045018583c0c07034003940780c201401a440201000c0009040d26144e000c410800c940d614070440850342c1464900742031074409103071007a4241c0580c1e00040101045c0c801c8501c103030702420800e0100c0c02c40344590500f6a5901c01500072140c01a8400c0307840c0a034904080c20001d00b511410380048190360812100600c19000309a00c0c1c403d40704075411b081c000d0390b0761095088030b980200b0080107007200402d1904 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 924906393 1250 924905143 924905147
    0x130302040c030b130e0703110613170f07120204090f0506160801050f0901050d0c0b04060905190f090c09090e0304150c260712022a06040504020c030f0a 67
    0x905015203069441c0b0911314581c003c40c0054400305440d0480b03c0d0014001800880c82080d0b03139424108015203143d01e8161203480da000407850307603488600da8050001c082c000305c0034107000302c051503040080106401d50a015210f01c0003408410024407540d0b07229100410406034824641c0a02d070480160f6666280010003128400d039440c401c0030004141c4000461603103450600b64020410241400c5c19582c280000e100078840c1840041c0d400b8440c0c0203000070440340301d0004001a1815560320002c5518120601c940e026069400b8030034210b54990034481d5105541d1002e0444101c0a40411403190b044400d4038000382ca904030f544124286004032020190001c0148200e0300c568070380a061502d07003081290010865100146042d551001407040340b03180003003480d04150031345105440c1800695404907140301803a12080544c00040303500b216600741c003002000300c160814150012380c81e4200094858440d03405001d00c595070206103030038640b03c108181d940c211030984045594010101c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 924907643 1250 924906393 924906401
    0xa0e010c020d0e120d0e060705010509030a090801020307021b010509040203010e0f0f070e191d090d03090510020705030702130911040b0603070305041b0617090a03020303010308130302040c03 84
    0x82c14000c6101a048180207040c20362aa80f2084561009854014900740c0c040302da44031070100712540f020090041a020500a2284e140038640c031400555a400360b4900181800d0301da54030920860f40f051080000a94000c180d020960404c070003c20085585c1c1e000595103809803a090a40261010001040d1481d80200320780c00745100c0300f08180341c3c0e996686030b626a05006ca030b25500291401c04105090b042036240070015101c0c1c60307900c541c000d40707d440255100e001d020b01603102c40b503100c0520150503814004c41c03510425502c1d040c8521201900c800ea51441c8001d8000051507001402a050000032f10540d07000550003030004d04102207148050015011906040d0750241c045943e0018a240912075010b5606010340001d0a684d1012400d41c0184070050055450301c1da9845005442c03404220141c003d40b0f42d5440b4648655000003542c505007000808075500d41c5d02410719000030a030000117403030440e9072000e289503440d6101e07410220040c0841d400250420300b410041c1d4081da0f00750300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 924908893 1250 924907643 924907663
    0x100f060f0f030302031b030d0f0519060b040b0c030c0105010f0812070c0530030d0e0307020916120f141f1517090f0f0d0f03050a0e010c02 61
    0x1059912041d190802109603418038880140980c3c020440503015840c46c244080f072107490b00050341e007025440501300085d60308a10307114460a07503660170004240035443c2402c0c54009400d00803c00d107030419840306141d105600540483c00d00120380c03220611410801c8035880c295040082c0080d517502da00321a00c0c807040f8000d41d00791380603101c80b0154003a4458103849540d50403c8884086525040078443c0c0b0603490a2074070784080b40c0501c100723481801c0c40f000581040410000710b5941403074888030b0b400c4840c1100500c0741600104105e501507541e006407190040210f01d00b40d2408041110700f40e41000081c00044020347c1888c018605400302030780641100e5010390f9043d5500d984106190240324100e00c01004c01075240a07042c0582d13181104141c40e004100c0c00c1c00e90420400d6001101803000450383c0b078041da8003480911110742028011501e086540d6801400708003052040a0b001004a054035820595100c0025003e40c1c0f50fa040780000d40001c80007041030030280c000007074540d010f00d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 924910143 1250 924908893 924908909
    0x5041404180c06110609030a03021606060612060b0c0a121808010501140603130809010c02090405210a0e012a030e09010f030302030702040b0d20030c121e100f06 71
    0x28006030f07500180403805d9482038400303801951804150a0b4250000d41120003540b0fa884161000740001520300e115040c007401d029100d4407000b45110004100ba2002d0750098491017000340103810342d00c500051180d03051503104132002c01001c001a421a18542110311008400140074800504500c06500c2141681c800400c45054a040c0c0020f22a291000303170303004001d03100c21280f4540850303260805044511014508240b0005464000642d805010b65003652983c101098418008041043c0300c03280001031485070b400c0014040c00a4640d05401e401a414040c05095007060079102020030301450307850209140d000d03070981c2402014902d15920190107000c240c5d0000c0303a00000d132043d2712300f01c03a89a4000d5203065195428080a0110315900a80240d054612000002c1202c141e0450f40b0a4090214120a844004151400c0c49484016025819003401e0b0718005401060a0183e00c0158092060020a003803029160600907407204001903d004460401c10036141c101408445200f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 924911393 1250 924910143 924910157
    0x10b07060b09070e04140403020c120c0d05031305090606220e090c010f2c0406050307061106010f0e0a090201022506020c0411120c0d09060204180c05041404180c06 72
    0x42186c0b01c81d56206a5025016030321805451809150500800c444800580e060765101d80052005c0340340300d001c44a08039001d80001c50310304000c10b44c40c012800244400c4804541a0402a005c07590903c542c0081d800c5003080503041c85410144890604000c180e9402c8070b0905103814a00c60751608402204180001d0a0f50f01c50001144105100c49030490302d144c0801c0c0074180c081c2c0c00c4c614240480c079250380103500c07504006050307501442804014003503a2111550b10242c104594102181600710801c2d2503100303241400011150b0304c8040c6d1100c0c2d44040050b0031501ea00040c2d1034480c82c008101ca0010004429941142c607200350002124529004c5406482d107050802c800d8609240588c1c429602c24400160781c40303031500041703402040c1c002610f0f1070705c010141c1940640e403102c0010307107500d5000107007000701154440511507403601d00c101c100300c00300c90f40c04004d2440c4030303600c2042c8102c10222407164607551950300c800004084601c0120b03902095142c64200050a4030131000420b800e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 924912643 1250 924911393 924911411
    0x703020a0b31050c0118050607050109030f02191e0b1f080609150c0f03010b0405090723130f0810051312050d1d0a050c0d0506010b07060b09070e04 65
    0x2111107201203c2d4414090044d501c040b0340116481005409803c0c40c42c2d003d03000015030ba440300c00007401d41e14051400452019100e050107407060024000e40000c6501480350b4071041d600300e02640255640c0300003c401584034080813441c1c030240008015102d0013042c0c007842541500400e5500c04800d06c803410048080d0303500b0300c1684424045940c0c1c001c94100c101a64034140001c1301d656400700c880500707071341050f24001d01c00000fa04260422418200c000400b8003480c0b6240b045d06034070104929141c144100d10702e00285200c155121404052040441c645001c0c502c003d02d00c0000e840054654420190b683e8550303a51043c03500d9116042510740000309030309103001c000f403600241c1c2000c0348640903040074130111600d600440304440081e58940318115000d61402045007049280c400a04486401d0306041d0300708048035001c07520941e15401d01300c000502c0407031541c1c11600c0c0d07440c10300d40302e840900741003001d44041101c2c107074040d2740e500400c150340383c0100141d084084142c81c20044124 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 924913893 1250 924912643 924912721
    0x50703020922060f06090b07030201110a08010f05092502011e090c06031118011b0317010b1e0306040b0402072301020702090c0703030b03010c090501021c050f0703020a0b 75
    0x107120f00070381740020384e2030405010b088984002072814910034400010350040301c14015205030448c0081400140d136810040004c4c001100e203000103440101c81c081014100042031001030640d0403180302202010b140321700c021074002e60080d10784041c0f141400c0c90b1445891842001040d08500440700700501d0240483c4442c460320900310006100e0100307900d04269000f070302001c0c0ba11000002d0410000ca003030200c40d00c4445419080c914800d85400c5841c5c00801811548044140c100d1070a41c00c0a20500c0c04030302405000c5107140070204545a62505c4100216025040c4110300c15000b5000107621000c11a0f480c8046502e10800c6185107400f0382603a602900307034483d8410196220350400085461456044020172501c0d1085c20000740000050002c41c2c2505c0c4402401404141c074076004000c1960140705e043e540300b011030900c0701080c07904400900309003e00a03184400d002c0105141c401c041c001c0014800702a049030700b42c1e241d880c2c4229801c0c0c00c00560703404154140c2c3e8082410405170 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 924915143 1250 924913893 924913919
    0x1201021309090c030206030a06052d010e03071e03080a0e030601060c0b06060f070c080c0f0306010f1a1c062d09051e180d02060f04020405070302092206 67
    0x83c2d12902c6012901d00e5a000c000ea2504090185503407141c1d690310010380c42ea00d048c024491032032101c08440e00c541da501800e0039140a105016814000d8042c0203129998010a1480c01e070f82039000d0070700003082c0215004c0301e071038030540005004400000719100c0082d00701010b0f52940004034101c41d41603032581401c854405011500402e08000200030880d0b62034101e0241c001042e040352aa4104020340c1c0782c8064180d8654014090398010054000050130400030f1243c1000080e402031121754075101d40102003540030f10031f16144a610038810b04542402108031041d220b4640144111458400301650040241e480341c4002c200ca1b60141c041104d485544a01070b2a402c130702494807040c5001d14200240000802225504c14a0110243c904880389540f50080386808070701d500701e000c412456460b20488502040665000e5070400121404404007182d10541c10390300402e880e140d002055000e4014190b490b648001c207102001e4445c1341e081e50140c01c810030510140045130395003005000e0300c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 924916393 1250 924915143 924915161
    0x603060605010f05030c160213050601080a090515041a0915060a0b0d05220b040c0f0f03140304120b04050d03060602030a0e1807090f0e280b1201021309 67
    0x20139010300000300d07403140100c081d1114003500b8a21540440b000d40c009040171140480c09403015559809228240d60b00a8001d0340c4200740307c0003000410a6510340642e1081d601000001100f12040043c0401c80c00004d154050500081441030314100a050141c880c0000e8801100440c1242e00040d04c0e4900107005604880f5040c150501d003000b0300900102034440201014845203c090894840318410a400c803101b90285010110701d0030140340c404810070155001c803400d03220039a41800030314801d00ca0780c800c50b03900150f1071203c02e09280c1140d00314042c4d540300c4500400d400c0d1950f01882001c520303083c456881481038400c00242d40c2001d8045400500030000168400d1108a500c140280060040940700800043c0240d00b80c100c203800a08013194104000780c4488001c0081120200c5900058503460003580010301d40102c03030381110402100c030705115506443c94402c58454a902119a80342c01030407405455904003003a0703010358411242075000b0503102800080000681c468200c103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 924917643 1250 924916393 924916397
    0x40624030c02061311010e12010c030f0209010f0c060e1902040b010201090b160207030602191d3601170c0a05090406052707052d040c020f0109060603060605010f 71
    0x90b010a68503105000c102c0038036001e0600610707d824070b4103603075012031400b00c040c800e80c008100c0e0421580010244c40080307440c80701c0d0724014405070308240e80142c000a00c2d11690301d0f190401040504001001c0c0007440b103210228091401e103024403103c507100c440900341c02510140540c4131034000480c00c850f1032510280c00480060701041c0c4800c3d082c8021800c5020310b10443d41c1d0f40340c4a448500c2241c0c841d854041c03800382c41390788050880790400f0028080c0031200030680024504040404d08000300c2c20090b0710b00295401b0400c28028410b40d41040710620704010420540e190b2000005524081d181c0c14414031409080014524260401d0300a0300c801804a41c6240c555030b49a5004c2c2c000942307010750358075080200480b0360f03801d24140c4180060503001000014030305000e000d0005941c142080841000c490f5100d0ba000200030908891801a140010500a00241241026a9400c50301e01650a1003a581c040c484650811804e484c000d0038100b008559a00040d218820220340100c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 924918893 1250 924917643 924917671
    0x3050c09090412031103010801090c05030d1209060f05090c1c050c060f040e040f0b013201090f0f030b0606091005072d060b0a0f030b06040624030c0206 67
    0xb000801d100c4030815480300505011440703a5401010405d160026004000141e66658410f000d0246040071100141010b0300504010304100718002d0000070061000301901d61191210002c010700b40d4003240500d0b220400c104050300b82001410b49030002c0045c0548181540c180e00d103a00700b0030a0500da001e5a2017001040008002400e118541e00490704145296800340700000d000100302c600e003403141d07100d0282a448821203241203040940180c1000740800100c0e00c1031445c10b2a260032000f00c00600c0c0912010110181004950ac4002600601d41d085610b03440010070400b0a081c1000303a074403c0f0441c1c1c81d16130b54002403048a020380e0050315400301c2c5140691104c03901401c020040d0b14007641c0a504501805113074170b50044072403401000a410f440d0140c006125141c4200c0021500c203c4034030502c2454007d00c40450310003800090090301c00c03440803400c26900e81c0c0c80030008000030b200c0e400b00070280188501c200d0255507010320110b0300746402005140d00c003140e418440d100030340910b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 924920143 1250 924918893 924918901
    0x10e030901121a210f010903141c0608010c030b090403080f0405010209040504320d2d030605010f03060b040e090c131a0603160f1b06020a03050c0909 66
    0x30b80600343c0800960404481c80d0102c90207615840c000c180c052240d143c04540d032003180c4458629000701e100803800c15074034105a500000c0d0f03016039a03602d904080c2c1c405545405009400e9aa520b0300116917115903403414100080212042d00002402605500c082100d541440c090040c11601190014005801e21002807220000700346001c0c0c1041c003070340c0014244410240031800700c0b0b1040c2c805581800d00c1c448078400542081d10307514500210301312216049441c001c0311340c0d5920540e00700e11040c04580f864100c0007520000d0752743d140d42445204030444880000d40070f0014282030165500050718000d400c01c045019000c0c10003181d100380f0011b0700c1c0a140c14150403010b58080c100f421540280f1003824115aa89100d5400c0c10360303d000006500c13040ea409003040308000c00c41d002d00481e001d00030002542d204081d00760040e600340c10990030208070b0b1402180c4a0075101d0480c00110003a00c00c04050283c82d40c084c1101824a40302080b9684620813089058051440c41d554010081c00000e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 924921393 1250 924920143 924920177
    0x510260d140c0f030409060902070b010302060307180f17070614090117070e09130503181f051e0f180f040f1505060304021804020d0b0117010e030901 66
    0x141040704400032080d818082142c1c2003604201d0183d010207950380c00401e003030200119501c070345c1e401051280c408500e0b04400ea5955502e680301480064071519001c0000b4144078021249254204480c1190380c0d61a070300d649404401000601903c0d0109a0030506444050380000d594403e0f94250b45071405c00041c400d00000b416404440003604228048074554018041803141e1402040c80342c8640030000b84410501100200052180510002d06900c1c1c00200b04007004596002c4400314170780c92039800040101d410794400c5409401400440d80c162400c0c658400b010b0800000715103c02c166a00f80c005414400f4020703044102070101040041d004c049480f800710501c44440504462401166100014110388841c2120310340d01da100d02c594107900080e00901c402401c400c461041c25800c0036008900c028002040304148980440b01060545d41d508942c482e02e154001c170503504075a101d1100c2281e100348907400401c60360a100054500b071801006890b03c401d01a900c405540c11603e400d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 924922643 1250 924921393 924921407
    0xc100902030a0b04030309081b0d0302190e120601030f051c0509040f141512070303050306090a020405040c090806070c03140d090c08031314030a0f150510260d 70
    0x105d0601d50340388418800100180c0107030441250b000c07a004020240255500d0034100d20704204020944100000c0380d4442e008140c03c400c05942d440c0c02c4000460f81008282c0000100c882c05245205a034000000c004144065401c803600c620103441341e49030000c41403001440c070102c03c0c00219200380811005401c0550140321703000d0004901148000700100c41800300d8005541c0e1765000549580c03915164142400901d04e82e42c0c12500034907006249d41c400800710b0001400302ca104d0b41e605000300340e11140300c0e01614064480100708202414240b800500341d440603100f105c08074098080010b80d828000d800150281d40c15840746580700c44400054a46640001545c0440700c0d0749984007c0031560085990780a41003000007035507102c09100209001001c16805204030100450407503155441c0420480002940140c042c000500d25241c01c680300b0400d09a4103200070320380400c00604501e125001e50488a000d011f0600e1100c0c8030401040c0311040580380c0710315034880307001501c4241c49850 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 924923893 1250 924922643 924922651
    0x23030c0d03051f0e1f0b030703200a03360b060d0f06022802100b0402270a0501320c03130e010611060411041b050c100902030a0b 57
    0x4243c251410140048031040c010744c0200e074052030010104200700c08450a920008251144401c441d1407030400b1480c02c1d48070060400081503111300c0901c8004170310015100158100c5803015456040d440c5004005241c4182014810043c0e03205020345610721001c00c454804107211241ea1040441d20b80040080000c0c0003950003800f07800032400030a40500d07052881600c1820f015a8400c002c10750b2100007051514054403062440a10050301900000c0e0480c100d5012280400c078040b407280000c000340691306d8841000c142e04100d03241c0c6546005940d01e84400101d88025189840394011181c0001060030284d013000f8808041c14240d545416403450442442c080b2480c1c07205c007050640c2150446002030f100000380020910a180d5200324130381c0035040a10b0174100040e00306501c2a6105c8001d880a00314504c000e13020021511603403c1303040401684444410f182c0101d1100030b2031340c2d1050103401050700800d034104116001900501480e1030b0001e000300b41c170031001c1e100c0003101d0344060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 924925143 1250 924923893 924923911
    0x618100c020114010602070f1503020f19030c03060b1b0703170d0e0303130822120501110702030a020907050c07090b090f0709090f0e0a23030c0d0305 66
    0x502001510421401500900d020036800494502216120003000c0c5506821580c155040f125041c000713115001c200038102c801103040b8072074001403260190001c3c800e034164a1030211000568444182201c042c52200340126a820005941810803c0f811107865024078180844108604030280041500b0000b001080809403051a5030720b82e52445490b04901d200503074144086515402007a04c0c4c0700303101101e0480300c003452852500c07c1c070481c02024001ca00502d1148042504284819910145a0084000160485070a031103401007910180382c01803c03942582881d8442e5074101440007518940c43d4080c001740b65200c0342d50700f007002e07051009040f5410000c0c203014500c04210104800c034010301c890800090701362001710600c2405000100040d12a13000d44040c084440e0340a20158111b840151000a201d00a038070448041c10b040d00c8900c1c030b144940c1e90120309010070500c088014000ca01000c00302d14074038440d15a161b01600041c2ca900b500094050717400c45000b50002c80d0712400f49 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 924926393 1250 924925143 924925153
    0x510150b210406140c190302031302100225080307110d061b0e0904020d11060c010f0609150b0a0507030908010e0f01050711190302070f081606050c0618 67
    0xc40a0024007808880548540e40c07110403071121009036210a640180c2100c49043c9407944030203800b0380040e012070b455001c041e800000108030000288a001c8070a0340240b203030040b01c3e04460300941e251805114062300c1503002c2c02240110201c403200c10216000f8502540c1004a29181c100c036880640c0700680d04682c104802c100000c800d8070410604245101514214070011040100382c03280c4080814050b1946109100142e40c070054041101c0b40d001041c0c0c900d410003500820704034040c001940c02c080d03080c048849844101d9411410a50781c040303e08000c01c1c0c280c1603c020700c03051948501d204080701080002c07206440b840003072101c94002c1c10030128055440010324212004010901c0c050381040b00c01c160401000c0c000c8071341052491600d0140c0c0003009404940b145606110021540314000b807560400d0b0007031100134020209810350207000343e07850080030b07190b145410713100ba0501305981010401d0340c0964280c404001d2400b00402081d5500d50b000040401110b600c24054450 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 924927643 1250 924926393 924926437
    0x2010e0f010c020606100e0405062214090c0a0608071e0203130611031215180910060f0b1606060803071e0308041205160305070510150b 60
    0x400c01108185030100c000004804008400090412902138103180c85210025292000245c0c82030f50714443c580308440010345502c400740040c135000301e42c440d650807180e0000b407050003100550b880a00704c21100c8a0f04031041eaa01d030700e51070300c540499030380300e41c01140c10406000c52482007020135444151410401504501e0025900b0348114910a0800690002810405100c85803180e54003c101d42c0c10256602c601003d181622030041d0a140300c03403078a0850003d180c0480761074070030b090040c002d8100003580d10406015180c43d0021242c090542c801e88801d0280e6010a103c0d003000c45503060041d02e050360900314040c440e6030055590b9480c1030398410b40c2c070010410500c43c900040c02510b00451f40c030103142c500f030882c05e000d480c4030229403594000201c006c250801d003595442076100707211809412240c802910300380038440c8511a215403080c1950100764100d40100328440c001c104650720700c07101c1590102960300c41e00c2c842130f42001e1400d0404c032400d5010050704000c1e5050300a030801c800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 924928893 1250 924927643 924927671
    0x7060908040b04150e060f090102070302061b070b0304020109090c0509030d020705120a050c01081305070305070504050f070c1202010e030c0706110d0f05090a051e0102070602011a100201 82
    0x2030740210b1580000010204501005428222800c02d060300701180c0c6540c610000401502650100c1d90a0110010765004141e100342700c1300000c0c56005080f144c450200b248164100c40110b00744500c184100100800c0394400304c0192032013181d0581d10000380e41d080400106c060042c40400d0024408103006805141d0303403d210050072413a65074001c00d14545408200400c00118122055082e003020710081c010920100f45001001c8080c00c2c0500c007520313003840008141c1e02c9801c0182150140007004810040c002c16188201c540885007400310391945191400f041c0e205032844004541c043c0381e001d00040341081004801500c600000a092841300e400a003160b03c0140001000d0300411024421250015100300c8900c42650040c240009051009020051a21a580280500407a1548040d510501444040c1c0406050320b80c0240114640340c811554084a00e80580115880419254814030440807104040030352104941849001d01200313011040ca4001155294208084008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 924930143 1250 924928893 924928897
    0x160501020a020f0d09050619021c090929090702031603021e01020c060c0310090e01090201080c180d020406081204061211091e0a06211b0507060908 65
    0x40660300034020f25020283e01c01c0c20681c3d032010207400d21220210610a5031038040640d07142c40032206482010001241040e4902541c1c0e101d41850008801d20000c4074503072020b90301085070034001060100d05108500030b00840c04004030580b0b0990201c2c00f1140c0e600d400c6000a170803440303500613030b0328141741c1440c8480841c1c0c1d070a5041d030150784246d40050004038010446c1ca4a00b007404021820220881ca106888203c0a0f2000343c10042c0440441d11016680c03011400904c040d140c108411501c1d103030b03c10f01030038003650141d0200c0c40d0400000c1000e00560115841c1d007600406402240010504008606002a8040c0e030401e61b1a1404194080100114003d011041506a84079031800790010502c242c14456141d40070304220203e141c669410707056a0030b013807048440200e084507030071710200300045041d0140c0c2c1c411350010340002d026070042c064000c0604810a6074143d00301c51031001c0141c0302101654803100401b0604a01002e00c074002400969100780004603040109807516000d82d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 924931393 1250 924930143 924930157
    0x18040609020715090809090c0c030301030c170c030d0c06021c270c031421030712060b07080f0d060608061002060f041b090501120606050307120816050102 68
    0x1030354001000c0d8140300b24080800c140c0c2c110580140103483c0320342e4070b0b031405008a810407402042c640e808180501342480a89403940162006c0341d4503582d403401d14942c50319035445200e028440c4283c2048024602058207001c1c01ca01500a02c51100305007022075410700c10940555049070700b80302101d03000e003a10640001c4d1305c0d09240041500051010a03a02d2080503400404410100040e11000901041e600701c084a170041003115444e81c3c03100b4290300700038103034450804080781e01c80c20740140c102c034074003440c041d0100c0d50b80c50110701c13807990f00403040740c4641c0a11150b5540c01d00880c030029100704000c3c000141c0740b82e811030500c643c000f0503905445150700142c011401c0300080012354106030384603a0080e00e60744014007503424202c82c500d0725490003078005003084c0c80103603040c1c1d294000424136000422510130704100641c1d550300c07417000030003100b141112800d040040001c0d00b4540015420300f6261520f4115500c0d12290342c41041d00d5001c0903820340742124079103d400100b8030a1000e00740b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 924932643 1250 924931393 924931409
    0x606091b0c0102070f1a042001030b030a0b04150c02061306021c02030f0a0603020105030a0c02030c0a0804050a08010e1e1f15050631080304170d030b0f0105180406 72
    0x2c2c1c4002c514000282d051b48104142500d030350601040301283e031041040b0200114442281007100250300128058070315411120f825114a0845130104459880350380e1141d4001c4003100d1000c17a0960001064600c00c0721740c6001a4410f0003c1754081c0c81c40c4005003801440740000501c0c14103e82c507451504400e190408a00755404401c1014034800d040301e6039400070603484108281c505603030011f03155010180103000c01c0d55540040c104114020000c48a040541004a860400503483c100b44030794054040c95005881140001034102814050000f440a14001600702c40030344030b0103007041c1455081200710f54031070314000c0d40c903050407804002c800492032007020a0401058420b099a2041640310500440d01041020006080000f405204410780e40300c4020315106036101028680194120400900000500040e606004060701e690f050703520055400c3c1442491080c5d044461440405421404400c61101c1380c1d0311850007802e00c1e018420003da00c06005401140849601d40c0010103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 924933893 1250 924932643 924932663
    0x503070504060e0a2d0b07020d03030b2805011707021e10110c0c09090706031805070b1b150414010f09050c040e160e04020d080a0c03030b01020606091b0c010207 71
    0x8030800c64045c0060408503205600c0d00d0065030100c0c0c0d007030007e0741c5c02408140d40d49003220b4480d41c07440020555101c020318039030101c1a000030b030390400c04a14855580800c1c80510f45800050440d00303864807841140e00603050a800d01064050707407030140c9034003181a01510301041d07a000300c42c0c81114014005011001d071240c3c00e0401440c60030703100c1c90348144518040000c21030101800203c0b001518107900d008505001e103070301a10400c11004900400f18010010003054031504040a13101c00c146c10450040d582d180c411840c0d88407019131040c2800c07894800c00040118003c0c2c844000d0402e4003400005100e030046e00c1e2442101c040742412105904420503080300ba15050042c86036000081000e803604804440180d04c1d001860300c151064050711b2380008080d59204866544000d401c1422135a8520f49403200510b42c1043e00307000c4003c00d1034081c61045c15440017403141d00c00c40000d030026155407220328508800400a0b41d0200c824442000541450300c000c0c000742c038120b803081c01840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 924935143 1250 924933893 924933959
    0x12040b0601121505130209030304030f020f090103120305270a05010c111e03070206041701050c030c12093c010e0703320c0108070503070504060e0a 65
    0x145028142d8000446190a0003107264002545161500885000700c07000c12000040c4840f0380007034043c45043d15414000070070000140700007201c0116880d842126000f05042d10a42080b01089083c000500035a490f4414018401e02a0303020035000014142e40d0001200c0001c84d802c10b841c1d00da402c9030340c660024580b1504000302402007610040180c20680c08004510503000d550b04045e0200300e040090f41845402005000c1c030882d982d44c0c3d0060201c0781c5d42c54641411000645540600740004d40c80c5c072001815a441d804150b078011140c042090780350617401c1c440e14008202c050021850740c0503414002040b013590710003c52482ca07610725080b10040007809100c0c81c0d41500e45002d0140c0e410405030000c00d4038045002000d036a480320015128000185200000e00094035010704000c10900740140705060010703980205010980c2c4601960361103090842e114002569914007040050105000b00d600450000d030840c20043c1812008980da079010003185488840541c1090001e85500303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 924936393 1250 924935143 924935147
    0xc02100b010e100507080712020304060f03050408070b0907090f0903120e0c01052d2203110d0501020d051005150408060c1b010603030906020709050603060403110312040b0601 77
    0x940380c0400d00304a8107040b01e4001007091222000d00e03610030800d000034900c00700700203082584c114a804c0207200311800225500070750760740d00c00e00902c0d02066002400b0011144a805400d120369440f0000a003899034640d5461685100078044020600a9200c046040204c41c451003802400902020494070000d04015040e85181e070140d00016043c45900103640e803002405482c0f01401307281c919502e06d075a40c0d065025210900201c1d10701c0301d100c0681d030008508200544507403504909002c0d91003004001040700c03c603480c84000c01403040b500100d015440e010402044560048001500e081078036111242242c030202c03104a140394006906120a0030511021241c1c0703000c2c1e8601e1490a401c1c0001242d90790002410320040074000510040a00b85090002c0795140340c3c2c0d4000c0c003160380c0b40d19025009803420301402e00140f10f00c1c20f000410503400c0c0070701802104050f000c3c100030f0720780b0744046800c50900d81042c1d109120400c4192404066000c040340300e1401079081d554a0704047c000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 924937643 1250 924936393 924936401
    0xc0c062f03010b03010501050c0a0605040809280302040213080106031415010b030c030a09300c0f020411070c171504050d0c03260a1b0903240c0210 65
    0xc81000d180284010301c59848a04120b0703040d1131090a059441da910311b48040d20f48450070310018026400c040030b00c010088002c010704100181251103045624076242c81000321500d8181c0085205d01300c1d01c0810142c10254002e1610042104003031012a848200d207074203407a60740c3e1044403031380310360140c00c40d800c40c0c14042c0c0d0016a1400b02058081c1d4500b4050317410501024024000100002000c142c1c641043c1d4848440240d01103041e80f07800c05501007000a0032031541c0c0e091500c0d981c3e0a02d50300403034825031310120002d90128980810001d00d40912005044604160351844000c120f90004076002d65092002010440341c08a1840512400203047c5a14000b010011000705000d010009a02160850300142d1a2900344c001c21010308045407010403a2459698024a0400b030b050304d107244c655150701c20400c004050100b11002604403141070102107440000440301301e014070014940a070f202540805407005441c60410001e212022a00d420081c50302503809040440e9280f011401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 924938893 1250 924937643 924937721
    0x3091a0d0b04020c06010905060409140d02010606020c10080405071a1e03040807020f0a15020f01060b07030207150c06062d0f0902090d0525080a11040c0c06 69
    0x5015400c0c1500341941c80d40c1d45038180145041c7c01d4941000031840d0325245d01c106d03880b5400c094612031050308030010ba43c07198130161062005509140300820aa0f0002074125245900a002e100d0340c1201e0f803c08580c451130182c0102c9540c080c1140001c0c08855202080c40742041c103c0f801c60340d4000f1890380d200350150508490a021000b8000c100114401301c00340c0748125015518003488100342e00c00510051455007207480d807121254400342007960700240c0c0f01c8070740440303c1c02080019107415140907280200040100141d000c0c8006104c006000140d454005140b402c0150400e200d60381c5882c183c3d2a5a00003d039082e2000d000c59209402d02e1070500c01b8881d000e580c05c1e041c1800e015240000b40031500442c07441030b07000252071001c0e80300c21a00c4507400b60440c05403580201c82c910680c201120010041e00802003904020a03d80e6010981086143d40324aa054104c174410081c000988211400c41c030a00500301408000300b1054024058400c003d412000410002d8402c2009a845011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 924940143 1250 924938893 924938899
    0x204051602070906051f0c06110d060f1a071b030b1005010804030e0103020a120207050105062103090f0f090907150216030609080c03210606032203091a0d0b 69
    0x11350b04104949819078030415510310343c0e140a10038505a102a10040315001d402881c1a250882c200c4500902c44c0241250300e00f058028417200d07540340c0201404031524052820310503881c800c0d020800d000c01004100140c0b14009010f10190485080d40c400321007a8816162062450304118030102070929081c080e2009007005c2c8940d00300750303e0080590711120f850701d0501d036000603c00e486d00e010342c0a210f080900c880080d542d506962800e140039000940d1012301807158003101c16200c2071520340c64180c10303d91400441c144054002040b445040d11942c864000c8040034005c0c000740c4860750103900c00e842e00da00030400d07207160143d081d120440e440340940454008840203140071001550b44000c9070780021001c81c00509900b0490110f105500d850001440b001442c1d01c441c0740390b8120340007400604e510300645e60351442c0910001e4802180d0642080c82c1080905400c8000c003d40700300325601130710f0312140044d10303007020042c2c07403115038012862820049250885034800c0d02540b02c11510503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 924941393 1250 924940143 924940151
    0x501020903060a0911220c17060f090f040f1a161b03080901021317211b0a0605070c050606040603030f0f03020f07080322030503130f02040516020709 66
    0xd91a000d00c1c07a0743d01d40110740b15440b1000c226504001d00b544407041e4001402c1c0030032004000400103008401c0d030723500421141c60381600252188c5030141c60904a0a000b400048841d607940b05c514038550700082088a4420002c44d82c1c0d000300f840005404240d110504000445040c907030a0146400fa080042104106101c08802c2c0143c01850341c03070460650504021459868174048140079000d80200410705e2805808001100b03600c1c600185d00100e1048281c1e9004030b07c180211140c140140003003c0061403c100b07405461111a5400100360840b2080c2c0d5807900c80f0b5a129010b83e0419910140000e90304940d000c148402032050981045080741d0800859144d9030b001360010349410111030501c4660300d130094056000341c0440b4210811542175036a103c030549032800b5030b6041074586410400e0089455954089492945000c0c1e80e0980c949604542c0d500007541140c0820003011a2403003038205035000144c40f01d0160b01d016181380d203200c12170041c0300c1c0c00c000d140114540c0040449410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 924942643 1250 924941393 924941411
    0xe07050303090f1c030203131e030314070b04062c070e0c0409020d050106110c011718150a0b0306040c2c070207180b0603010b090312070501020903060a 67
    0x402c46031021819100310036050840b0000807200c0b07854121820708a07801d1a0100f042603400720080c690703e001c0101042030592241411400c408139000c8070805204002010310100340075841d0701c448040c07400352041c90600c03103543c1c11884a00a07074040700d0749ca03262040000d08900a40340c1100100001044a68500103aa5000d40d41c107801e1088a03c01a0710030003007004440135104a6001e0181c500341990344002c90641000102400d205250001c1c180d051780d6001d036000071480d29107040050303682690708114601491030345074010344403900440d2200b44000d2407800500c16801d070058815034103a180d1034842d901c0b10644040c400154800d07007010b4100000202600102c005451304100d00c10305000140c13400050603420a06081054000923040008099000900806451000ca0140f0440c1a1076210760180c800314907140f170740580240014002d60f13020f80c020f84405c071001003c841c60407802500d0110140d0040c4030a48043e5000034440c3c42e0b50404001c15074000c078005000b0820755074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 924943893 1250 924942643 924942649
    0xc1c022413020a0324050105010804021e0604090c020105040c05010903021008041a01140f042d180f0b010506040e06040c02150705120901060b030610141303060e0705 73
    0x20040400701500610900401991110420b1102456205001e0b4841c1e940a98007001c4034404034103144212410440040344651051403001c0c012039024100b810b62885660410300d031003503012070a03900300c17106110001d6074604074000d4031070f008182c0c2c000013040d09150a003036040c00e0719a0041810702c801210100300580b00c1d01e5885030712030b4040c58041081e80f20791810104032a0301034118401c401580d0008215840c1480c00742c3c002820845a40c07050b04251702c2400107031840201c0042d954010824509204061582c1c0341810355103007980007620901c011000380180c05c20030415101d6a040a103c0d00411511401c11809010121031050070a8a8602100014440100305030b0003161260704240758640200110719219000f00c083e1006032070229001070080e0000546001c605015102151602c40306205850541c0c140c601502c2c619590302086c88103e1500b10303a03090410464403415904034942070040c2c600400400e0708143d146144d4185442580c01400d840201070300040342c200135541e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 924945143 1250 924943893 924943963
    0x10080601150c12020c06190e100806010e0303070f060c020d030e072304060602010b0114090915061b0706090e19110d02040e2a0f030c0c1c02 62
    0x25038850f807000c0540300b90460880c04c1001c045880c94202d140410007030070403146100948500c00c00707640c1c0c0440320403142080007646c1c60036007000c4000c51221008508503508c2811003040da107002604036480d103c12569018981c00010100b0344500d0340c0d90302d0540c01680d043c4800c2100102928087c068080701c1c02e00b80303896201512580001280b03101041d003403941c0e010301c1d0301e104280c02413041008a54a041c0640a401e00c41000b0303000800c0781c0b01032520400e502c81511011000900350013150f40c1c5207000d208036811a080000d901280510003014188082170070345c01e55100c82400b5140d0343d8070703088000d0700008494100600c11000041003000007400c503d40360780b03103440045c1d01142d01c1100b541280d101e0b11900c0340315000a800003a01280c03042d030740c0c0e4170340d40113221070a502e07140e01120185405010304c4c0c001550030160010002024544119001b9640100041c221549044102c43c2d140d132400c9401c0d40c0b100c54900030805010107164041c0b20081c00d00110040001103101c103414803031015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 924946393 1250 924945143 924945167
    0x3020c03030732030a02160920090103090c080a1505070203030f060f030708010914031e070302032b141003080d1b0503010e061c02130e061008060115 66
    0x80d248918500f502c841a00703203401c4010780e03140140d80c0e0340d04000301700079254800001500c01d100646200044e02155900c03504400300502d100c1071074083c1141c0340006195105d03a1146040588410344040401c40540080c0014500c0302c0003480d8000581c501050712a030300700d0414070214580003c00050903008401c82ea80540e284602c5250380d60b9200c0051400003000c00441d80510441c0c00c04944a101541f207101860b009114071b181070b0b82c5005142c1e5507031050a61000907050340c02000d18240300408050700c1c07080e2103401524207220051101c200308071080320035200d007000c42d10000c10804040b0b206403202654860004415458035400404403076005110003407410307400054080c170303072180c41d402030210200360f040d1391030000c102d048014829002030140c0c0e80d48500181c0802e4252400070440c505c1c4201d1031219550f2502503800f00078100e82142001164181c07500b4412001007014071000d803294100340380402015003000c42032881c0070016000340c040e40d0314030340420401580000002000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 924947643 1250 924946393 924946433
    0xa0c090c09150c060614030f2e0b1302120906072a0605070504210201080604020f0c06010b130806130204020a050408010612060506010e01081906051c03020c030307 72
    0xd0200014102c4440f086440050015441c0a002242d000514481189213040131821100f000c070b1a0804240c44403007038821301c1e146130b090800700100d0901400d03c1805480c000722000611041c181b02250880c0500d0429500e515400124582000c2d05454280e4012400d40014002c0d403402d0b00300505000740550114440214201036500300049101110610661002040c0945e007000480640190000d0103203e041c40190101c0d040c526070020780c0e48031081d40503550311039161200e500740802980208003011510004110034003d40c10200a198000c03e40384c00ca066652208102c180554012508115070706d40052062046031888458082c8100e5011100180d41d60010b41054441d03200700c1d4409541135003812400a0103a11004400960300d00960040c4200d42c1c0b064011145c00c0b0030b0340d01c05800314011101080d200218407150941d000098840003e0381d036291030005000d28851405440c03502002400e803410158140f0640320354100a80082d41405159650b41140403034034201d007aa = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 924948893 1250 924947643 924947669
    0x71e0f140c1203180102120402030705060f1204020105071b060e06040b040311030f0a110112020a1209020f18040c15050f0c07120f231207050c09090a0c090c09 70
    0x102d402104c40c260b01031180040c00071581c40c0340c01a2851550041142c090b8401e0040c03420004060615004480f056100c05110700d01e0102d442c4131000440b00302800a038100325080c0300c1d62000480c064100d50154200754044100140b50100062440702010055405000c1c24042004030302d0021050b0340c2a241d215801e01d1700440e401d03010078a442c83c0c0700c11010721480340d141082d060100f0700350700104004081c0c2e11080c25495030541c140c01c0c0d00c90703100c0c40350003c0e0303908045250191a80d07100d103000d1403004014503125000d040024144500d14032200c0180502c4c0801e00c010420000f91681c001c008070390004640380b040e85005041e5004413088502c91520000d15038003c801e050104001030050b0246c103080030880b07424288101c0b00388440c00c0315a05050321640e20705803e00030310410600540d2000f850b80405580c3d4041007500410012229071280000101840d65014901445181d100004020200090502c404403d50507403115544500c1c003e40400d089a1101800c0c096408051a540c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 924950143 1250 924948893 924948901
    0xb01030c09090f09051c0f0c0b06010813080d0f180503040b0d0b04050a020c010c140a031a03030318060a0b090105060c0319081b0405030312071e0f140c1203 69
    0x2c4094805040d00600c17074002c0c41031250501000e24040c4068110640d110800c019070a60b0503200d09550003406880d0551240000f465503110f40c03107665004d510103d101180001a03a0b480840703401108070b14818030340b40c441d07294041d040d611a0158030f141c0307501d410804c5c02003515120380701e226034041c055010000003028282ca00e0f807600300e000c0714100900100664a46621410000e4018941a4419509104041700c0103031190644401400749103010918180c2c3c00c2c1402d5008100c1c14a0798070000e0001030070b07110561342c00c0c80618070881d410780158604d01c1010488a041c004000c011046141c6407280380300759030310f03990f0720136044d41c9003a0b480315070f80c107581801c0c1441c50080c1440c401e03076032105c00000c40c40307254403140150040c10340c1201002e100c80c90b070807101c4503030107503008207038140d4800d1040b441c0001040e03040680080c1c26003001072180d4122851001400c054149110101da00b01e24103521603940031803200b903041c0e0788012480c241079464802c0307500c0d02c25008600c140390b070010001c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 924951393 1250 924950143 924950171
    0xc0b0609040f08030108100b061318090212070512030a0e010c030309122a051213080d02010c0e0901030206090411040f0e09010e0f0604122003030a0b01030c0909 71
    0x70b403499038000d200262030703607510714545544440229501041034100307070944c0e030603052100170707900c000701e21152030f028a6081103002e49480c081041d50300f40b0b003a00c440f480400340c0c50325290500443c180001400299007080c1c10310642e52191000c2c038030258800c0010158403613022040c0b40e01c1140c24a481081c0400500702240500040c0002804107010004403d44003a080000e01821014120f40500030725800321a00001001d40000a0101c4d000181d840340c90010580c01056101c081200060140c0e03242c096603441c1404c6030701c110026079924180040140d8002081140d1250210f402410710f60461f40800c84500409039181e010f50745071071304508811a54000d54000d81b00801001e8200d0740c0d642c904082401d015900b01e100c41d440c004124810a8000c60b54580c000400c1c4014091501c61303540c1c4d070109150f41c003e01c00c20072020400010601170301c404101c04a400c1c500045469042c69480b50b0101c0d041340181c0c5042c10310300b01000c110745810418400403503d884100203042d00d0f004c50700c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 924952643 1250 924951393 924951413
    0xf01020d0f0807211d030309100b060c0106122a090f060b19180608041407091401080f0a05101503020a030311060a111902010f050411100c0b060904 65
    0x102154680529111348520040c0b0743c0701c4114528050f004412054108515540342d10060f140500c441d003011665003441c0c2440c2d0004010030303d02502e46450004c00b07a540d18211034494022004a02910100000784120354441c010818810406110000c601c2d40c140090100e16102e00303540241c80f50449240c400083d8440300042450303290081c0c0d1192083c01c030000f4044540d1072600444e98400c120a49040c86800d541c0a030707483c83d143e02c03a035910b031910349080010030300b0521142c0340f140f610045031900c0540624219a5000d4035080b040354149102d09003441e20b40514480745503c020480f03800300c0c0000a401954000010001030000324594040c00c1c180034a40000c4e40203e17583c0300000401d64000705d14071164101070180d482c0381c2c40e2001c1035030a40e59014460300781c00c2c100344001554240c01440050388258035000000d030081c0760110300010340380201c1c1c0c182c0e131303401e103070106a81d0340d0905510140c00580c480c6011241c8040959403480e0324800509507500a8028100007410014803483d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 924953893 1250 924952643 924952667
    0x10c03080a02090312131a0301060c14120304150b0904060c0908060c04080c09040c0302040b2d03010605060a09030b0702030408070e16030c12050a0f020a0804020f01020d0f0807 78
    0x4141c2c1d001d211184001c51980e032086c540c2e108040325100f40010b03c5099403450f440010701d40c1c440d441c59640b074010100c4191240440030313141180c00300c1d90400c2e288010407030302d01400200d04100d92685458100080c4a021503400900a9803d00d8100e104980c0d45030b4456501960000000038400c550a008803018205904505041d1240d44144000b11a80c000580101c070480300480302030011402c00d00565540940700108407100c00182400103281ca500100117608000e00113a2124044801030880030b1030098007000c080042c8140c083d82e604082c001c1501505007a00c0040c42d006510310002d003011800d10018115506803008100d6951091088030f0040900f4421950101e4480c0b045468054080d03884030015030407a00313141c204d18064041d11007091441d4490304070b4946403410341c07400340c4001010b000710b0f16a2880382d42034000c10f030b00c0034000200c00c076034849640d49081c2c41400710802d902d586040c1554003510030340000d5a88000030600a03200c502c3c0031a02031300c8010080d40c08007001c0c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 924955143 1250 924953893 924953899
    0x30d09050303250c0305180604030303020702150324030109060e060a06140d12090906230a29070c03060b1003110a1b020a060f1202030105010c03080a0209 68
    0x400110103200d000000303180152160105200012140718121a140c0e082e1004040422400c0d40d070b61002c02c0c0540050103611030b0031055900425031107800240e007980140c004502095010500400398104a55103550501154006924600380038103400045211808403103802c1804c00ca6241c02900c00703410624103107034000c8062081d01d41d038058550300d80404035070000d10b230b6150000002e4110740281055240440c041c00c298003081043e19182c0ba804210000e000500c4184480056140481d00c5008000d050b1500100c00912070085829240f07000c0039101c9105420b2002c00f40070f00696845080090444040d00040c4481c0840002142d4002e1840c05050450340480001c10300403150401010406c00f16000c8600c00c46400042c2c044400c52024070321741005c20312102100d18005c0e100d03596043c80c0f4030f403403103a446207139400200c00c03450341c2d00000c000074005420b540740150006c03c01082c24500340d40a50542d0f0600300002e0912454a9005d8200056100400c3e844000d950485501c91006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 924956393 1250 924955143 924955151
    0xb070201020f1e060a020316081806040b0a06121205090114070b06040b030d080619050d05011a0105070b0402220e010c02060709050d0215040b1b0c100c030809030d 72
    0x3500c550718000c81c035590300800760300130480000d079000b4242c401c0384d11810035241015003e6000403001c0303071a502d00910300c408440011900300040e4030704102c1030348998410740c02a0402e10340706100742c0c1a0b600a6000c04502444003c0703080004480180780c0380e035401d0340d1814a44071205000100e40d00703c00c94508000640c00014410180021100e030f5034800c01c01038400303101c40c0d00b40900341580c40c541b020000700015640742c049401c0f4500038141000300d00114010100064880000500e4400c3c001411070341ca0f9596480941580704000e0103554220303090a0603401d0407030584412118000040c0700130300c5021010144601c05415400740c84941100d6001041107074450321400c5d00030b01101c41901c015106960000d9021807084280030140c4402502041040c0e00303990a210030342d01120180c5100a00c14000891510002805800310b0407030b0030001c01d1102d1001038001c1c10160402c4650340140e48402405c1d20b020341041091607070f030380d151401d24240c0e40c9440364141107010703030b03c040d00b115414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 924957643 1250 924956393 924956413
    0x39030606040c0e0616030306051005070609060b12100b06030709140112020c0303040302101514131b080708041a150307060e0103060503070501090b03130b010e091b030303010b070201020f 82
    0x883e1740c07070b43c400e288262402c01089440f81c0421604106040440000820401400000601d107402002884d88a800e000c5040c0c10007000040c400365030f0011030b00007688040c00b1918100058001c00450301025100f061450805020007011300501d03019034003e5002502a1514591040700c0d4070b004010102811510703220316103407554680d031007a07400780e00520616011760484240340c1300741c1c5e55140c0d40307042244001c1c0c50581c2403950308010f04005c03640809142110403802c40c10b07010f000820880c0000b800c080000300c4401a0908030b0180121003005030301010000007642080a842c0c2c8040d54040d0120740303691700c007140c0c40c019400c15407403034050050300d20019050760010700d400c2c0c00c02c2e000d0302d041c0b089a40754018550ba40005101e2140001c8607244100403440028000f150440340c5c0c0d810070842d443c003d0722140560002a406400c10302c20640401080a40611018080c403101c0d90608070108404800a5603a01060280100c103140009000c02107a0081082c0006d0b01b161100b40e405c8600c2d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 924958893 1250 924957643 924957667
    0x3060c1e160308330d0803100503070806060102060a09020f0d08040810020f07081e0403050721030e10170a0506030c121b0f0339030606040c0e06 64
    0x1c4120200c001c951a0000314101c68440100b1004000c03040c00d050a01c0c4504e0078604019681c0003c1903500514908801c4010131601002140710303004149500a00c10326200c10700d0f14100300d603400000140c0091b024003030140e90100d00541c10240b03a0300b01082c0400c9a0001481c0414009541d90b40184084e03221020051080d01800480e04640700b90360450585190348010303441008102a07030160104401c40c0000c580b00c0243c8000110245900c04001c1102c0d080031042c1c0c081d801c00da8203640026420415107508a007201c940c1306c00c400040c5c2624801c3d40d000760080e1884500075200758080780301410740358071070050040500d28a40b603224541c00d103101d481d8001c11040d00c62074020f0184464283c043d08060159600f06900b078801480036000d1980e88900d0118440d880f103030701c0307404600075071800d81d410852404011182e65400c40e4404400298642e14001032000b1400305440f8208098182d4007c00d202c2c5d0312080c141c502044004c410b0000711401c0c40001320361548080003242951901c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 924960143 1250 924958893 924958927
    0x904030207150219080d060803040902030f0a1a01030f02160b4201020109080a080f0105100e010518040c020f0706080c041403152a070203060c1e 64
    0x10b12050b50041c000c145444101e072295801c0440d20352120007840c4000010380040024941c400c00f202001580c591503501142c02c5a010f0382c0280e0301c298012040c07011200001022070f41151800504103c1019002e0001c0d00340b1482e0100303241816034980c074030880701449804491441c8468000811036091500e071403440d2010a843c0100c5486e141034441c5000e00e07680a888503440c45401d101480d0301c0d054401c454021a20810f0241155207500f220000140c00703001500c403c09890304c0341c00c003e180501d044410100160712862080c08000c01264110fa00440310340c03a401004c1c0b90481d074030303038041070442d2040d0a90f0f01c05681082c03403d40c48880160f408140441110743c55001c2d2401c4560303030708046441090540780900901000c0104100c1d100c45141d000401c0040502901c4807100045541000d80c20116203000305440c4000d040012080034000420f8000302d4007410905090b09500401c0c0d6450000348903007100400005e02940d40240904c85000c0c4590100c60140d440141d81840342140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 924961393 1250 924960143 924960149
    0x406092f060901051912110d05060f010816110a0b0105181021060c110d0801120f050307050d031a0904050a06021308070b04060f14030a0203040c050904030207 70
    0x9125040c03246046240c80412900e8002050307444070b040c1903103001c960001400b450b00c0075041c4030070300040403080b10f02c50203012440508010340940b03a8114449003019540010000c0f48103504030300910746c190f03800001581d0040e03884d20b9140040c004d9001d003500e2070680113103013003500c0c4909039100d400c01181c040d8003416108180d0b403c0382c01c42045450b0610307000301640e0701119003540d0f81050142000151318002c9602940b000701c1034100254940c0303001c40b8021890800003801c0c1500c8100000d41c1000400f20003542850010709642c034011203070b6145212064000d0a92801d1100d00742801002c01c01c1d10400d940050584499100400d4080c00910181d819489030500d603540d040302a2034108020b81c86260014080c2c03c030300709142c0d6104029404240700381000c1d480510b0100e51500c08211301c8002e00f51200c0da040c0c1c1c55080075805407000003840d441c4820029800d5640301107a1000c019603402c40d4145002680340c2d01c0710702c0c03c0c0340000c00540085030881a00400c01052507400203e407022 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 924962643 1250 924961393 924961463
    0xb06091207031e080a030b0607080706050f1303051902030f030a05041b0302060a080705130305061b030105011e05090907030f14060625020603011e05010905130203040609 75
    0x2540f10381c9140745154000000015018040502c44003940d24001d400c02112024000c00c01e41c82c04a5541e40e60035240c0040c035044e1103480d0707a00b040003500004e032412150028542e01c4c400c0c992414540c0c004000703210765500810056001504505d20134020000d88610751140c5012623101c0c03405180441c01170404a40030b94800034844400074528100c1c504034025a900070301402d1800400700c8080c1d401e10404ae0052040013000c2001040350161a002000074602c204040c02c03070350901020951101c00030001e4040c180404000400c82a0b0700310b44041e007034224000100711880d9078503506031100c1c051501c840341c000c034081c0100444c4a91551001c00c102850490800081c00d0304180c142e80b5030750480c1c0207a080300040200341e01e410b001c0100d482482280c41541030351540766501094050700207911410200600c0800d001140c440c210110003d44001c1c60803141076407a1500044461540031249212554000f0200b000e000c107581020800940050004070182107101c150f2480186100003404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 924963893 1250 924962643 924962663
    0x1b030311090409241e0b192c0f0f0406061a030610020f2a130905070806061804061803020d09140a0b0c0a14061509040f060b0609120703 60
    0x4111401d442200804150140c0480d40d00c1e03100e0000030b0082601c1d080803130740300c01407070601301d4104419052107015010f0549601000464105c9407900003234180b49402d610076000c0100000081d00d078184d10343c485948034104200740c480e403e04400505c695008810f9015901c0b074510594164200154001d101c03c1c0d8021041a03940740c0126200c0d03400b0035141800f41c2001c40e07000910181482103503084108144440500403906000034440791003440d030b07044055100c1d00c00c202440810b11006005054040c040e012520b0450009040702c40304c1480d45024941d044041401d00046c1d91100100401c03144034500b0840c0d6500b03019698100888a6a00246d0003c00210304c50408412104080e50041c0c0014003050820524800e150031800800410384280c05520340418580f003001e03445d01341003101825030740c2460020650b00b00e030464181d0340107a200310305000000e41b0b01000302c2c1e0040c0e00b102002900c0440500041d509124540105600c031076070321a882000f000c045006400c8030700c90000d000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 924965143 1250 924963893 924963953
    0x80105040c090504020f1c0c0e0603010305100203070504091a03010c0201020a05070f1712041505040816050708070e0907080a0c031704050d06090308071b030311090409 74
    0x580c1c900c0001a40000c01c031103001c1002e8100f0b134000c0d01000310b02ca510b880c2007d50302c4100110043c0c01c000107006103610b841d078102078290400c03440308101d0300c16a6450b140d0b43c190f413034807560707140c1c1500161907030f0364000000754000780301c0c10940e0050004c100d81403140050b20140b030b07040c0382c11a00299110754644200121a940140f084502c4855913448050a112081d00c58030a015407211080e65940d0390002401103c0003032000410840603410485881801d21b0b0a052001581032842000503500e0407003031002040d400c1003581c20100202c0b0005404030207a103015402c00007681d001404520440c900407070121600030319644511039450480382441e54a4035145d6841c0500c10f0b000e081800c040c4802e00c01b00b01006061520004c000c03410034686595140890010a1421030503240180d4a6a505e010141c0c003850181d0007519900d8000072445000d4240c10400500c030394010141a0713100440841000024140d9408500041c01042195103d04241410814014003081c0d0044040d00d24 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 924966393 1250 924965143 924965149
    0x19020618010c0c021513060507200a03021e060a211506050c121605061501050405040e070e040f1b081e1e07150504080d080414010e0d080105 62
    0x2544401006969110f9805841e03000d000b52201000032030250780108028145a152803002c0340c100906280c2c2e035032591100325051080007951034401d41103188031404000c4d0034582d102d030b08100c240c0390129102c0100c101d14031961842000c69403000341e004030010401d031400700d41115040421660300701c60030070003290a180d01803c95502c0342e0b50455114a4003428000c6030312800140c081203400008483c0100b125004040c219042428040482400c03815048200881800300301c0e0000106403607042c0e6101290000382c49409240a0640190750b15001c01e00c940300100704040050403403504040c0d190030300e030812404c4083c8071101594130704419164280e44e070103001200801c0f591543c020b000111182034240400890407186103d0520600b01581c42a5598092013482e0500c0d0800030100329207840190101040c4481d545001e010b014002080032910200e201e142c8104545481e803140c1d95207181c403460030f401a54192a0945c86c12401d41741001e000140d0f00c0c032048050f03c401c0c1c0c0da030b039941d410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 924967643 1250 924966393 924966401
    0x70f03061d0f0907170a170a0210110f030117070b0c06161106130606150c020907140403060603050c120a030806030f010e010209040b0301111e1902061801 68
    0x51550005010400560030210032140c45420080c04826112160303030300c944120790100b990b01400300e1764104142c0700d020000b010803040c50711940c82c1c01183c10203110440103516081c00010ba09205070315010f204c1003c80204c0200d40043d00d44201c8640c032541c480e004140102c1d190040c00f9400d00c80c406001c203890f9004000d40c1c40325101d060045c1072540c1c60101c900325841c0d41d05c0c411414059244201440c101007441b00074070a941148404800410a09120050314035030750180b1902100b807160441e0003a40501803c0c8041e0b0140c2d0032420316240c02400b1505c40d44684400710398450089030100410520b034000e641121302490448083d443c01c40204034242c0e2500085980c01c0e44513000c0040081e009075611540400c00030181c0b808001c0c3c400c417060a4854142c4121100d940c0007944141501c0c052080401d509408d07002002080c48580c0f065180d031140300d45a00701c107541c5400840440300c2c0d4404072031860079203180525110700c400700c0184d41c400050309c1b821800802c0b1500e680000d401482 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 924968893 1250 924967643 924967679
    0x307080a200a15181a070803100801060f081005010b03130312020a090918020102060f0c090d0f031209110607031215080d0201060f0611030909070f0306 67
    0x481d9800303036200d948102020152100c0a40c004141c203030b00085203a03006aa1080022039074544055900c0e07030100040010308503030010000300c001c00100e1521500c2d20000c2ea000b1582c011320050356512500f548000c500d54551180340313a9804c1030300c007044284070740e000d1008581081c0c0481d01d803001100028400d41c0c60900481c60300e22002d00001c2d2030b80c280303903108011013402420f00f841d1011b2030035004000d076804180b0180c045550f000040182c83c10501c1103900d1046480c06480740081780f640003e4460030f01504001140f05091701286110000343d0846068603001800610054074900d4030040001020b60140c0c0070600064440e01411524040c8101495201445020310041e00d401c01c0155000101c05404111400e801404105004e20600003405418504254050310703101c482c601d0110301491840459061200800000c0f26181c0604240c4840d41883e0180800c0710b580c503031642c041c400355140d104e003480c030070300c1040c0c0c1e046494120360300d0080e50103009082d1140c92540201c0a064 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 924970143 1250 924968893 924968903
    0x405030c101802040b19090b030d08090a330504030e09102c0c030603010b0618010f0c0b070e0910050a03060207060905030c0f01050609010303230c0d020c0307080a 72
    0x102c0e40700300520701a4401e4091a200030500304d120b5610810800148015030000c1c0300b45596014100603909c0d00300045080d0342013a00d4001c03610728210011036214a0b4149006001e41850000d00c401c440c0011810340700c032298541102c01c50350f1023100d248060702065406034003040103030400c82c04a040052510b4418410b10003103400f03003864500b42101e02d009415144441400c05240300d131991000f03005160050f102407880d10b449003426001c15084404007040341d40300d01010000134440301c000c484500c0b500c00e424202000110074064055034003141c0c440000b480000d4800420030115000000c0f03410010060b1481440340d615806d0004001e0014000c10364800100401000098220f8000340940f40c40303201d0210790b00041d551307443e01d940c029105a008942000082e6000b410b400d12402d40d1096040360075120a5145407000f41074626903601020b40842c5d8001500e00345024501218103505800c02115080e20766160001e468510710300d542e45c400e00400c0d4000403041d20003d180001a5000303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 924971393 1250 924970143 924970181
    0x21b1206060904060b10030213050d0f0b0c090d0807170c0307061d0f061509040b01050906030c0a0f03030e03010615230d050105091e01050d03050904050405030c10 72
    0x2030700700280820700030821126070f5110059200152542d4001450740b485d5a10b02513100c00c07541035840124495500214011911418241c0206040e002c4060015800624111940d200d0418400491141a016a801501500d00070042048543c010411540117100c03103100101e0646407650340d4410030344084407560050241001083c010707402850b400b00e440804d45861000a2070660074a03100420003001a00320703008000c05001604a1a101e24600310f80e20b84407490719035503101115506001d500c2c0a65519400a581620100101403030340b04000d0040d62600d80d11000c1c2041c450142c00103d00040e00315105420038141402200c007518110036039007407800407c0b0b03411103149140d00800d05c0a1701d50044a16030844c3c40c07000500c1c03c00d40300031001c1507942c104020b01403402005030122000a4503600d010701c110121903005030558030200c80706048643c0070304040303e081c081c14840c3c90f4041d20302014841005400002007200066900981e04121aa402e450702111800c8201207884016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 924972643 1250 924971393 924971401
    0xc090105030d030c091e0806090c010f05070201020138060c03092709030301090e0c03070e0a090605090a12052b1d0c0a0b091c0c0312021b1206 63
    0x290000b51a00c02c00740f500890880d65074201b408003148031003040f14107113010361040c0a001c7d020300609600001200041c000300804200081286980d864403d0130081c0200307405046a100b0b400081c02625044440c5084246070072010620000714060340d86210042034990180d07003001740590320380c05070308130145060800c20b0701404540e0038602074641010048a602003900c0c0380b120f0240340038690384d800841d22907040606000c101c6a1116016105503c00030342010f95940001e000404d8424003103414100e9111151030700003804404400800581c202420000c441000041c0381c05414020080400b8181180d142a01c41d8419142000c00c801e4106206950131207000c6104190128101c100040300b04266900c04262201800c541c0078542040028400c0c074030f0051900c00140640030b0b492441c0803c00c00001c0d03d1034409010f180b81c05040440c400341405602c200304002035401c100f58400410ba1300500a4880f01c042c3c60003019000d1525503801203080a03565140d500d48541c00620141e11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 924973893 1250 924972643 924972647
    0x1b0b0103020d080906030c0309070b190e0418032f07060e012a0512030709060c0c0e0c1e0406120203092d0601171c03060308070305040302030c090105030d 68
    0x802c0a5055520841c00c03c501c01e544c0d25003c0040d40715001101540e501c81c28400202424105d0a5100e1207415800f84540701c0c0008480e00703404001680750900741020f01088010030064a9040f0048007580143e00300c5200341600002048202080300c3c0c00b90000b10395000807d004404041491400381e801946c2c20300c0964001c2843c58020035050602032504c0c0c81258440000c61200040c50f141708021a0365401000002c018261000494450150543c40e00080003002c4600b50312035001003040c500c490300140000d4184c2000a481d03500320b00360051402444a0761194400d010390460b00074401c0d04010701c4c1c54418180c5041d19210b07501c01e900900d00f04502006904054030001d014000c0e4101ca44400941091850038814810701860030b0500c0c20302c5140c00c0c00e105a100c0408100888050310016102150300da40718560329030702e014050540002100100900e420003084000001403a60a05401c44050000c980c030031004c0310b0501410005101e1004d1080c450140c0682c062182c1c00765640c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 924975143 1250 924973893 924973909
    0x1090809010c030e0411040e090f06070f1b060203060a0b0405060712051b0d020c0f03150912031906080d02210f07060f0c020a0507031506090203070f1b0b010302 71
    0x600a00d010f1602c2205079000804a07400c6c0d14203585100c5c0b00250400490b035a0a01031540005007401506048440000042e10360100508190400640042e0b480c01940640c41d1010b050490710754217034060b001d03407610600951090f15540d120303480c00280011040001c20803502641c40c00b80c0f40130f00b080c07525a200c550401c3c500c40d10000b0300a0610401084403101454a8207990311030b4010410400300401c0a1b0403d800c4180359802905042c1c44140107440c00141c013400089441e1601445980d2f206105080c07006429075060800f400005111107256850103c203600740308035104001f01c90303071400200d07980e007021000b0802581000c80c0007102d880100d4080c650041c03503600100d1502200c80b003514003070303403060000320f079060354503021001141480e10503151301104900003842c08200507142c03e5076401944c84000d0140010110b40c07100c1940c503801a01c02041d95240030341d100e0600341c07005006021403140400004c0d5601c031441c031001540402400309590000f041006036400d54091012003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 924976393 1250 924975143 924975167
    0x1b1507050f1308010c03091104090503040302090c07080721080103030e010807020f190b0114090a0c0309020a0303050714061603020c030c0d180608070f050711060301260109080901 79
    0x2030200766900081052003800344a45608175941c000952603290300c1c3c2140b5054114a01d10300031890407a80d40c1c0001e500004a800f926011511340c61641d5901074035001600c2040c1c0b0040035000040b41200410000303229044600740b0001040c00605a00c09084844003802d100103070005003c1003802c00c0f5540070321526504016203205031601c08a50500c03440c503005240010707503140588241c0307140c103104404038164003408046950800690b131860001342a020050303d44521165582540714013070380664400c500881d8060011007103140e0343d0034040c2c010303089803000b074880b0300c00e90344028100c00c8080b0301c0a03c503107944142c00102c0405000101e00a4011240407449071004002090300300700100805a5414502c1d960040101805010702d444000c16511001c14055841d013401640ca0f000801d07943c2100b550300d03205841d6440c0e0f081520184c000c90009a400c007400200114625032044601a40c10110700c800c000f4415008551600b00d42d180407016200c4e89040c080c095407988034595107020707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 924977643 1250 924976393 924976417
    0x150b0a09050108132603150f06040807030b0a09051005040605060409021f030608010624020118020402070f06110910090302090105010305040c09020f0417010b0d060b12031b1507050f 80
    0x195858041500441e64070a8401d01f03032290610420002514007160507298040c4151611802c0501d1701007000e40e03805442c0802420301c0090400900160b0041d0f0000540360b8005084881030280c2d00070010080c24140c1c0c080e544903050000284260500b401030303120346640501101043c125482d05414960380b102605c030b04050300c0d405c00041120090040c01d0140c03645034a10710500c41c0c000007103600148182d9201c0c0544e4101408602c00080380d0011340541a0140c0300582e070380c11240b40070100c2201c04d01d4000d1030b8030301d041980b40c2c51303000746405481c84420942d90a41006a08802502d920203140f000961104400c1c0040c4415403098000c25001403043c0e050134074407a100d20000059810006d140d400352036001c10204000080c6451003411002d40388020082c540b401c4002c1042d00b90f8820380a000305407070b0138500c1142d840706580558020303014010b507034984034507204c103010440b1803483c000f100340b01c0c0044400360400328025042c0204d10903281d003403910003081001c041381d41060100d070314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 924978893 1250 924977643 924977693
    0x61e0f02091f0e2e020a20040f0203100915050306060f030712030203130b390307060e01050a0605060a1d100c05011b0210020706150b0a0905010813 65
    0x411520b5002e8907039132082c401c4a00c1ca51200d035084401c644030310300040600441d4010070404001c14041c1d90b903010300740f0080d4a00041d001d0810081000362121507e09000a40f00008100c2c0c8500c42081c00c60907148504010b012088054129000da48024055160f242d0404404620740345031070321020054613005000d590f0002e941701c0d20b0203280784036881e095001d42c00000c1c0700681d0b840450b0122000c2c1041205283c180901345280c180c0035400c4244d48140044002c85c03102548200556440c0715055100c126541e1b104c00c4c0c43d2071809008501080c444560902c8086071082c9844c1c0100c1090300d4002d00002d04000520808071110903040d203070409050800800308003140c84d000c0030180e641a4035140d211900c101c0d89021821113138101a10041042200d00000c882c1b940403801c0010002c2040b00941c4502d0a400c09a008194501c2d8840f02040b04c00c07400241a40c540c40a8054400c00307072981007403640ea80e00150345200044440e0b200e021103513220703800061041d5410a0307003000c41c020340c02c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 924980143 1250 924978893 924978917
    0x6040f0606050705060901061202091e0c090307090b01050909130c03030e03060a1401060f02011103090f071401080109020715092001020304052407061e0f02091f 71
    0x865000d07820403400070740c0008090052101c1040544d80044070403008110307041c0b030050500000d0550300f10091080002001042011204201c0001001d8100150034543e00b00100c0c00382180c0c3c09010010700a01030b4510008101c1401e11601c0b036805010307110f440c5024100c4013001000c0740010a4001d00c20130040140010070031201410024521a44482c000c0151b00820945401d5004040c400711034181502008404115084035044520f5820400d580b50318217201a07014059003200ea501c49a400300800808140028444569280840a40701c056403079000f01041c681d0032089550100b00e081c80100820204d03039000b07203c0315004200420f101020340400e5010f9608460041e5803100303180312481c0607002c00d2104000f000c0800d0004601d031a01c1e06020400389a19800b0710600900c0b0300c3c03000400d00b1000340894000c554848070030422010300c4030741d4090002c0000d12134100c0d1441c210041d03944194a108440a81d00001c141d01000e008d040110540c43c500384688808200020481d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 924981393 1250 924980143 924980171
    0xc03180109080403030e060306030703060e1510050118080604080a030b0618030601080a1e0c08030a110709020304081602030705120c030f03030c070627151a010e090604 74
    0x501101c074400c40900355503500d0340c18000e080680c0c544456105080804c14881030b660b0010780c1d08102c0398010400b10702c8241c80c0c025241052150b512040000c4040020044031801610510064500980303644114040010f42403040380c1a0340943c06560340000007080110384400c000d17101d52417081c680401c00f26400b001040141d045085020800c00000c003040e02107280600259002d07000c0d00c4028400700d010380d100c60031110682000c20f001e0080c00398410062103900600c44020f0540b20f030490341c1e540c000314001810548140803040182c000c3c490b011854001d5802141c0c0143c1d0404681400c060080d40c03100c80c0c00d040300c407040382e02d03101302040029644c413800c01c0c480e103425030304002e0703c0d0f0244288141401d00041014104084d002001040b04001c0081c1c241d0f28025000640041c40006017192032846980702d0b4660074910444844040c20800d40003c00002c003980240103001c0c0c90340c2c0e840b40340be001102000481c040356841210b40c2981c14040b4043e0362200c80144081922950381d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 924982643 1250 924981393 924981401
    0x7050c011517011b0509010309080904050906040b010812040b1308010e07030506010819140c060d050405010e0601050a06050f160503040f170d0806010509090a061d0f0c031801 77
    0x44109101c460700c44403402c00c40d083c440d102032881844100c000400100400811510403e480207040c1030b83c0740742c240c0c04d02c6401070507140c050b0f40260040065041020070a070b0b5030078044504031004a203410012030321800110700c40510f22003c031520780c1454100016050140c22040b0b045070303149264000010707418424040c43d854203298001405d8014118140542031000c141c001c00002d030b00c01880c62404030031101100e94000d0b003100032000d495080034840740c10940c4804180d0b80c4000c011a0012031854550310150140f84103100070404141204185030316100309200d2180d01001030001004014054001060007405c0c0d03003034191405012002c0030400c600160425a81e03984081014883e8084042030b103000ba29060103404e15031041406015074500c040d440b60800c002518001c0346607a4003400544210b011700078105c0740d01c0d10b40000f07601c004184034421075500100c884407031801e01851f02c46080c0204068007c901107551400c5140525500203003422010346c44011621030b040d902886 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 924983893 1250 924982643 924982649
    0xc030307150b1f090605040e06060a02101a0a051f0e010c02030601090219050c031e070f050f0d14070f02011704150507050a3905010e16050907050c0115 67
    0x1444010000071a10000c0c405111a04045c09009003000140f080c1110b40951607881941155615580c0e140c3c90b03001c074103103429001c0160100d410048038030200c40741c001d2281c640f45010340300709054507969010420342c15815094070058141d02000455190701c20f43e4181600391040c102086540c803d54046441c061090b0302202c801c0d640400c40701c03c0340401280303182c075416085c03810501700309002c3d203413070b441c4d1050310002c42c14025408031400c0c82c05c0c5600305698010350800c8a9104ca00706038105aa1510354210744a20a4000c8030505654a80101a0703a4111107100f8005400d1481da03640d104030007100c0440990621004032a0601c00043d00002e19101c1e51152808020850b2a060900240c8001801600078400d0034010701002c03903032020340495003240305a444600a242c1c550441041c3d8090100700d1004140c10341034006103d015080b8502e80394032841110718500c1900a803251001c120302960b50300c40f03008004501001e00c0360000d0100704040400010f4000711884560701041c1081d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 924985143 1250 924983893 924983929
    0x904060f23060307080619020304030201320a0c091a0c030a1701060e090703050718080703023f010e0106060806030606040c050d0c12090b010302120c030307150b 71
    0xd0400100e420f050000f20002c003039a0700240014145584114110a20711100304105c5a000c40054103140c401d401820300440b01404a204800c4401c04d03500425a0241c0d4056800c544040440c850b0801e074480d14203440700380e41e40d10342214100203034801c09030602d039400c6030050014414807011210034401014070311416140c0403d4040c64054810445e4416070100c028800e51400384c40290710350708840f41e441000c07848c0018807582e071a60165082840d07103184500c1d10b00d00010202e408000080c0e2001602d008070755140d05502e10121070040b50007026800c0b0740101c0c48a801d11103860885001809441c9001d00220340980448085401c4820716030003a00080c01c03c034248080790030240704e0740b80c0100080d901805600da549102900c640300381d00540100c507a42d00c1070340b5612840f4000c5180c0c1c44032114800c0c08120300c40d040c210004034082c0000d91103101310b0000f104501c40000b0390b0344150440a000f0394240800d94603030b903440c102c80c0c501c0c600c0090f480307040c8080c45030b44524295421043c84 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 924986393 1250 924985143 924985211
    0xc0a140a09031505070f1b0c0303081506030c07020103020309032203140109030e01200319092103030510030f0b070e041503350d0f0501050904060f 65
    0x90300701207061000b42d11080001030701e0b04d41403042440d40084281c3c80300c4c0c001d041c0804e140d20420300e0324641c88501c00d006405162110004810182d020340514010b49144089a940c072851000700300a40c40292061840103004001c001c006501940145038012543d2080d0780c2040440544500300c002c900c8003807146070300c4940042c810090810621890020302c20000c20a603045944d01070522028038441905102a40d02c0107007100e0350381c080080902e01044183c94551071181e81e040844010301000001061403c40b010980c410025111b0403411795603081e400700100151402d4006101c040c03c0a81d52100491020000c0344c0b120680d4940240f00b420340b02c3c01450600310083c110b000d5001a03503c0b41d414441c040c01c00c504004011030030f4030b401801e07500d103c00301410b03120391102e10480f902c4401094204200d1118002a000c0e1401e00f940c140184407010705c4843e0001214024025a90b204110801103800b18440b503010400c07a55030003000064031001c3e1000340300e55a2121755988000712203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 924987643 1250 924986393 924986399
    0x41505120a05070806040506030c101d0616060216060c1814030d1421040c0b19050309160b0d110306090c0706141303030c170c0a140a09 60
    0x59004007507108030303035290400c9181002c10000740000b901602003446540c0302e03c0850f0590f0f41c1800b001c07090020046c00914122000c036005000c640100510300c401e010100002e80f80c0b400c058040340c000142c210550048803ca954443c0000c0d08855a1b621021106860800020720070f4490303020420400e4903060941250344404000402403a007081c3da100a081c4002d07480c41d2400111904144000e0403c00e24038070304400b041113680690070081c0035281c50040c0701720b20482c0303509881d401240100c102401c001e854118800d142e00c510300300c0407030825000856084d003d114001550b0400b00080c1034856408403078406d800c0906880e0080009000009900f044a5020388980c0111014060005081d13161003000201e1489005100001003c0005100000c2284550081c565010204005061401e01000c4031440011401040740440d01d0041041c042e1806480c501407901d9400c03e08a0880d9541c240c901125001240b845082c0104c1a031900c130707540011005070a025030141d491050b2685 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 924988893 1250 924987643 924987667
    0x2120709060915050f040e010501021015091a0301240f080703110a0f03080301031a060d110d0605010909020102121303060902120109060f050a0608190503041505 71
    0x4015045905200c081481001042c0e004003001c81150801e060040d03c1800c945030a41d110310507810000d00c407400001d808900038800f144080c0c140d420a900300c0300e24988140c140000c40f0010712000104e6464100104803204141e00450b203548a6415400d00307000f48840401d007583c0501754400b181c50f08080050041440b05003200e0300500d4880b02d5001402d2900055689030344d83c1e4000078040c41c000e402c65002e01d0722481c042d00010280c000e0307400e000b66543d01308982c45030003e002c1191600f4496882040e8010742580c01c0c2c1c0a08001400c3c1c6020b1130069644500c04103620f02c8581e000044039200780080b0300c1310b00c901c41c020b00c4a94004201c03014940300090034080c0108810400e20b50a00c58889043c450202d05000d59500810024901400313000083c242c000c2a45092070540c00c0a000300c04002140c2c00214005c5d055a40a01464903800e40300001c1e2001030142c20740315800004400903041400c07000d801614000e5056910302074079180d46070300c088014003000c0041000000c244130690 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 924990143 1250 924988893 924988927
    0x5090f0906070e22021603020c21100504060b10021c09030b19021e0d0e0706020c010302130302120a0308010b19180e1812030405030306100306081002 66
    0x601c00f031070641840c4240b040021152110f0468030102d400441c06400c4030010994125040085c1c2000300c2844400c50340350003541e0341200000340d4001c001c802c002241c03c16141c000414050701c43e00291020030442c03c100801810000c1c820748025854000b005001c0e00c44140101d42e07030740c03e54043c103040c0785050782c1100c7c0700416020b05d0f810021180c40070800705506040b01508440d4824121000e411040d00c10b4000c1e0180803801c0b0705100200107e18195030040000303120903100e50106100401d10002d0a60302e9030200d1044601681101f94565440d62190f8000e001442c407840c034011410351a0b8012860908400c8100f5809502002004041c103400540d0140100882403080b807030051203040c66101c800190100c2000d100301d030b500001d003400c043c440a00c050b1084444113106072414400e070f030340b440c46140c0d10b1170018000c04010001c41d40030744040700d00c1581c100e0011450354440078140306092600150160400d1740c2d807440412030b40414446c01d08501c580c10300158866200e6418183d2507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 924991393 1250 924990143 924990151
    0xa02060d0c08063015190c020f03030a0b0d0602070c0e1005030a02210f0c0118080303131704090b040506040c32041e0e0f06061305090f0906 62
    0x444d109800a00d026080036000e0707141510001d000010707555901c1c4031500d04900490790a03002e407038040401c41d015840480100340c0075440c0d0b60030300407000200030a90b11039a020b0425811500200006081494550080c070340d0b604025048240301c0c40280c50390400c81c1c00090080321052801c0d1420461003e4039981c0f1a0090301d24807171160b5161074440065034544c081200240110221511686181d40100001c081d00b074840007940d0141c0515031200e51215041000ca90101e03903001c20400c8409130804103c1e040c1e80e0400000e51654494060098288044040460705031280301d48441440c6014005080140740008011a602e58044100416504004c1a40380a6403070402c00c0500203600c40521400481d040314a08540351040310340284d0000c042003110080d203000a0001448406054411071070b000000034166600d4481c2c0d004101300409035142d008500c440c0e40400e10301d1912000400c0b802403240910700c0495074071408a00034680c11550032844840c4078080040c0c3c44000d0241c0c0b644 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 924992643 1250 924991393 924991399
    0x120d060501081009050c070b070c0b09030c070b070c0b0c0a0204180b04030305040c09060b0409060e070f0f02010b090112020306010b1c050a0921180302210a02060d0c0806 75
    0x15450051003c280381c00721032142011240e200c00c0411580800c4008982c0031030b0704400410640d180210014004800e0804100c80d0344000c100010b80c0d0391320100681382804883c801400a6903d40901c811080e0060341058039850080d4000080581506c002480c0504070100a88502e811030700401003100c21030002d51030300300c421001c00c070b00040d01c6450243c0d00c1a49401d00151684480c20038089c0701c0f203640c0080041d24038000003c101c114100003d0411a41402d4081c001940c4070607035070050032030a850500110740c19000d80c04c40c89021b182a084850420310000800c040c01e00009205408207034031042c040c443d080d212078103609040c030180b4058142030000c1071920034500c42404c0101c00345194007006c03a980d00c01041b1408010f41218400a030444d00d2025481103d0050307120115104c081c28010513248818100010a0040284104c0382c00801c062a00e038490203001c01c00303000305160041c2501410030748500513500d010242c040704e00c410301c0004030b08180642c007900e40c25019100900c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 924993893 1250 924992643 924992657
    0x6030510080a142a270a20041d04150c030603020117092a030f0c01120908030f0a0f0e07210c1401050408100c03050711070e060111120d060501 63
    0x710400c90364643c55881d01c00317686485035403c3d50407000025600040303152500c424104284800321455820141404c1804001c00e203081106580f041d07001d01c5107210301c00c0151012020f40d4000e6904000302030348039004154400c640340105030f82400b1603840e880120040b136660075050040d0350b841408420380140004010704581440e031030281c0d407691126540000001d2011101d04910800c03503a986002d040681100d0f408090031150913240c402c0164a64005000c1124084980469000c1c08002d542c1204690786191220042104040300042c03001950a450310034104082903033f0301c11300d500d002c83d041c05402d0b00c82c20014030304040200c01d401c2501c10b180c90401800480e130007504110403030703003003210941140c41c6140040e5014010b076802001e55016207001403d180716981c20420f18101e60303580400c42c650380d00005841407801d0740310340d05099029610510201202daa052900490f05051100800000c0c5222501e8140d0b000c2c010900f00c2004150302209107158007c98000c0c0500b424409 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 924995143 1250 924993893 924993943
    0x70e0312192c040506030a0507080109031e0c02010507030c0f0f03030c030b060d0b04111201091d150603070b0703091d0c0a0c0c0914040b070f020706030510080a14 72
    0x200c03420800c8880c82991343c1c0012502ca542d0410a00e1030f021361010581d4006035030703a2121402401011010741c041525071101c000c0d10341d6200d420311450105a2505e000301e210a070011103840d00142c50890070f02c41c2100390703000030610482040e5506880340c04005010b907030030310f40102580c0705806004149401d00103041256510501600d405594600c0001248111000081c01400020f20004041440010140b5103e42c000403000c0c1660981801403244103040ea49100760440c44083c0040c582d000010f411180113030510700c403a00454010100c444a60325000210000d030711202c07084000c034440000030002d0130300218141c0d21222020004031798518000301a00300310310902c03c03990100180488640d00f041940800e040c05401401c50802c448203860034851103010060f0380c142c0314150400002214988500305480e00080d26502910081e49410401d81c064640503040405042804c1e4011a4000d030800840404500942904a075a2850300040c1d00f03055180d03990748000c44c0e00e25410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 924996393 1250 924995143 924995207
    0x14100e010b011b05150f07030b03030f0307030b12071203110f0a080a0513031142040503011112010812040b0901020c120601080d09030b070e031219 65
    0x71001c3c1d4248003452020041440c10b54146a090840c035540c241240003404810b8504c0c02c91a4881d02040c0c40070410380010b04201556401000c100003009241000012032040c42030304215804c12010f060349042010700404a41000b00d160030448650001c0350342c0303005141e884006600310907548009810100120708100762a0001d109001e04610800034841d0903e511810445035040441882414015120310b00355000300b8021000318410301329428491111140782c0841c410007442c000c082821072210b410003c0254244c1d0610800140702888001a40d482c280509203c0710801c00b0402d9482007600044214000c0680008903650301c080c4030760040c601e50104580544031423204290305c440b0b1820040349030840d401d034580c1d002011800c0c2c50f88051400141305040e03910705c8056840c2003501540c2100c800310a440040c04d60030049000c81c8505014600307110344401c01400f5130b403400b01e40b05200445644400c004d084421a10740504004590048000306801900b11604a241d9191001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 924997643 1250 924996393 924996407
    0xf0b1c06090201091d06011101021305130e10021e0a050f070c03050a0b0a0c0e0f04050a090f0503030a050a0c08042028050607030f051614100e010b01 66
    0x40c2095030399610402560b0280f00e0203801000e078040015075100090711507000c407160680c1ea00e808105d240148420001c01030003501d05000c45208004c3c040c81c070380300800c60035282c001c0e860107100d5500d1a0841c05038009010301d40014100503030150b5640a04c21082d03001e000310030400240341d0001e022280080798040c04541130b014004c54002d032610003500b040c03071a11403558402003039071042c1c0820004105c10100d03901e104070245d14041151040181d42a20f40882141c11994480101412010689400e6101c02d810111103480040e50940c01d980380d200340c40c5411400d80d0954404030820030015064001d1551080c0070740800d100341c181442000d030a211000d04014814001030340c21412424003030700d007029000c0c0000c001205140807204042d82e00400c1d8041c503854104204004200350500c51b04440bd6030340d0540e101406076010603001ca5a0740c2020342020130880341c0c4801440031818141e801034031260544c028218042016a100d41128807807904105103905000040715642c2e0403090b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 924998893 1250 924997643 924997699
    0xb0a0501020708150a1b08070e041104061107090221060d080909190c0504050102060f16110a0c030b09012d0c050d05040b0613060b0301050d05100f0f0b 67
    0x40d0000c503031540417111000d091b03456004e100c1c07011030000383c00710705034405102805010581c4480141c0d002800611080e500d8900000811410810040052500c101c0710392002d11156026240c0301c58a0704040410307640800c00392801000000703508407614001c101d821740c0024080b1944483d081c120750755140c1e82d02881c0e41e414862440e91000500d801e04041031803062007000c140170403131400b00400c0035200f42c200d400349900500c500070001380300341d41100005010f6a4044981880e44480b0700c001c59500f40203030310800b564080d0588000c0042c540f1001c602c041e610902c0400d2540c0303003500486003110050a059150140760340d181c000b80e040d1848550030a54001c100100d0340303800004080e106482507190000c0701501c0c0100b084284010349800078000c5004403994140380d9000c0d000070b8141d4090740900b0710301032410001004185131120642c5d01861180c0207035021003491034001c000b194002920811860b0700d8611412030054644100501d50100711030900340000c024200c0c14001c15464 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 925000000 1107 924998893 924998923
    0xe01050103050a02190e0a020421120e010c0b0a0f050702030a08130c0e07110705010c0309030611070206030109060503010b060a0c1101110d030b0a0501020708 70
    0x60240504a941040080059031299001c1044884607120f40585031145480f0014200052009080c4680c030344410040e00c42d4502030004400e681e003114101d0346a101c01c11702000082c4032132242da0782c2d00e26a192072944c025801006991304041d8440c05001001140100690041c00350450b1003001d10203079003031200e40c4596600340d03075a005400e03200010900000015820a00707600701c064109000310540c2d4002e50342c42c20813a039030003000d40c0c0301da0000300461140558000d0820546009003828a01194036a4061314005c04602c1c02e4000108413a845a0a06540031410b809460341c464004110943c0c80d42e58072001001041c2c548a441d000754240955071003240380400a440041440703413284013100060f40c0d180300d0038400a10004e41445910f00d890000082d04000c03903408035090761000900115800d04004c802040c0c3d0380000d0465015040500802c2000300e0801040c0710b0315 = true := by decide +kernel

theorem cover : BRFrame.Cov 924820143 925000000 := by
  have h0 := BRFrame.cov_init 924820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 924820143 ≤ n) (h2 : n < 925000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
