-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0660
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:59:12.946392+00:00
-- url     : https://prove2.me/submissions/9ab9bcde-f705-4d17-b5d9-b687bbd21bb0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 118525179 ≤ n < 118705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 118526429 1250 118525179 118525181
    0x4180b151309110d0c0e010819020f0f03010e010b03010305060403030b012d020c120d03050907120302010605040b090403020d0e04060509010b0d0509031309110c03031008061315 78
    0x804102541c21019981e610341d440c00701201e1640d51144103c2c800400c1ea0316103400e40c0d00ca080160340c01400c2181c040c1c0c80890000303080c00e40c02488038050100311400c1e80c080b13140036016035190041d4610b2283e03d91113981522340c0c00390400d01c155820038a5140002907142844021641038a81050290a103651107807020360141c80b0908c5a90b0400c09100c401d0a2a04038a400041d5010580413003065425400d1000a00e402400f44e80103100707007150552502212000219104190700c0b034100450280d1b180302d02036041600940c00811550308036001c2208055041d48903005490f01290100701c51034200040c44030041d01150001d0241c2d004440840074507000b01402c0000400081000c00c1c00c40c1c850000c01c803035850a03030007840c10460100e101140c41d0410b01a803035102075040010360138145100142c203075040e01132103485042030b5990000000ea00041d41101c0300710000f001140d95a0806031b035103a00e900c9080c452194103005220106480c2c10501003070380801d42e00508805080389454020384 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 118527679 1250 118526429 118526437
    0x6180a03180302190302150a08040f0f121205070e030a020f120a030206041703060d08070602040e09030a030e0606060409050a09060e030c0c0a050d0308041a09010204180b15 76
    0xd8000100c07080004010b0742d85031a01020440c0c0c036807415078424035500c140408400c643c03003180007089080c0b0648038500d0340300458070780c00398000c0d0810300718424030f08145181e080520b0016003180000e40c20064032603080340c0c1c4200004401d41b810403441e554110211400244920710307950540202d10030b580507103000040b43c0386a400090407142022408000c1a103001c4e68280c0480168120104110a01c4503c1c03141e04000d88121801c0e41c60f40c60800000303503000441c20802449007101007145000d0200365030641e00901101c2c0310704551400c0030300301d5a5490b0001a140786c0000e08060a090f1108000300741d0358010340000e04a641098108407000014150003002a0600c0e0790706c100341004104680071b81940030111001a65a0383c4100e40320905020700c14500d58000e8209100421580e1100440101155058500501c4079180d0307203844140c10710316800c0e18072491004da083c49101c42c1c5c107500410494a1f00101d04d541c0c440701d031082509645401810543c01300c181d1150410400c5258010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 118528929 1250 118527679 118527707
    0x6090b0a09091a010206061c0201080403030e06070c020909011505240d06030b010b0313030806030f01060807060f021203072703082505121605070e040506180a03 71
    0x451000e0b0b403100e031400304488042100c00840002180344003800c3d6014020385070001c5c1c0691340040c065805109081c40100760680c02070400074403200041c14140300b40c4c060103000f01283c0984209050012001706503048616050344904000f50104040c0b0205202e900c444901c403400706001c0500d072004000c225101c00311802160300300248032403001000e030002031200f02e201d40400602c107030560500c1120f6183c16045035165100030400d2141c128000c81d00400060381c140307004011a551800400d0505801c1c01c1c42900560030724402051302c91001c5108015035409035121004207200b61710403685c07003c010341d8400042c0342c2000416000e5106030040a01400798290600f803030110402e404544038965031082d0b440c080301040c03039201e03030040003071003911090340090740d03000c1410944415407a524444070494907401c000a11504158840802d0820f06030000d0a6440181d5500e280e88007020003190704603200c0c0100340c0080c112014503200d5039008200f180080030221010740d810b480310b81c2920740c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 118530179 1250 118528929 118528937
    0x1501090509150c041a03010e0108030c0709021305040f060303030c031811180c0304030306051516020a05040c020f0c090712090c0e0a090201021b0f19030b0c04170706090b0a 76
    0x8600d5000d12004c4c0c05c807030400c10321401e54a61401603488401c40c010782210040d030700701700044002006c00044100c29601010030041ea47c542002d81e4a5400403164401e036001400c2c594041c410070f20741d601007000c490123510288150040c3d80000c9040380c602c030010280080340022110081080300d42004180c0c90b01403d1008182c0240756400300044003168604170b0300000208010030940e06010f100002e2600355100e450741d08048c2c00302c1180340100501e1108200256a5080c1990788004020005107005001005003855404000303442d54005444d8002d40d104443c0001c0d405d0404950350346c4240c2059a450a030012044007980140c144040c055031003102c00070000c240d040e0300a800305c1c0203103038101c000504008688000790610300060b1050315601075600501d00d1580b1080c6c02c08015600494401c50200800030601ca220f030841d42029140020a1b400c02902c601082c0041007650751241c201c01801c9504040365a503000c403402108009583c030001004900080406032501c3d0f0b100d414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 118531429 1250 118530179 118530187
    0x1030213030b06030a06052503060605090907021005010f0e060901060215040303060305070e0708090708120a0c06020307111b06072d050d090b0301080712030504030b04051501090509150c 82
    0x1960000e03520280c40310350f08c1f015841030401d0078030304503034110140b45464102800403070700d881c0b0081c0c09805425500c034040d000d4180001c5405109110007151a20010020482940c4501108075030b8a043c0c02400303a07411100c0d020441c18544005800d0480e4402c2c0d00404041c40a2404503800c51005802141455140ca402000140050122001038400f07180310b10384c5440c0c0f0f107000030070704d09000d0a608001e40290f101441070305008102003035403010740c030002a134401c9003140c1219501030325900540303218404400c1c40385096001000c1410503042800f2a10400030300004c0d0a444030880a034903a020404020050000f403406003030340320244900321494000003841800700301000c61200e08840c0d035007200c07010703510b03441d040b10b51940070300200c480a505542c109503903107a60b01d0150003100c80d0011101c0340401050700c03d200326006594001d24074046c07820513181c2265540a02a07504503502228400425800c0d010f1060610800504001f0881c031081d801d548070440001400f60216110100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 118532679 1250 118531429 118531433
    0x40204090f08030103060516050c2d0f10060e0118090f020d050d11010c0e12010b060c0d1416170c0115030b101a090303090a0b0304020102060601030213030b06030a 72
    0x1001c3e50095019280200343c078600311012184540924034080d003844801d0020b00b42403270000a4008140c0c507150980f0b07203a658800c41c80600050480000001441a090940904c1e04045684440440345000c1440702580321010040305000034098014400e001c3c031815401c10345c0980000070124080c030040b81c05280c443c2c001c2410742c4c0c140c1105035800d07400b04026100c403552103da103205104461000304800540074100400100f10b1242051290030a10100154a41e0a52285000a60080c88a80d607103003000a902d0711508418000b0340856603098a1700c0205c0410412a01d0450b154070072130320040c6040d5035560307014001101000069205100100300706209200e40221140c1d03940b000e5031a2455407502d4400450b000b842d05403400f00304d5204214510140d5500d03919540040303446900c9070700940c00f09246010780c03000c41382c1c0a0404800011001021401540602c1c003c0c1e0940e80c2d19510340300158281d00c521a110780b84914011030400104403001c08168000000906449a825450b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 118533929 1250 118532679 118532693
    0x30c12190c09091101090e01120b0613090c0e010e0105010806040c03150b04140f01051c110a05040602100504050c01050c0a080d0b0307060e0105040911090d050c10050909040204090f 80
    0x808100d40200c00d00d410f501c840c2d07030064451b1000741031140c0d90422640c1401c1701030700760007110600240f034071406001250031540c0c8c1c907001e1703003075034840880c00c11240e40c203403d284070708002c90310440a00012603000071908034035004035141690010385403000d030f644070ba8041c04001c203140c00d4003200b0556642c103a1041000e0729407022004201018145072a41d0030500741049480103140c140d880361302c042c0e240320180e036005001d5511141d50300a81d0042c05d1030300a41c41c40038242c1c040502c0e1055030009165004650024013800a990309513003111308040044154404850082d113010300158480800d144241d1b1044005040c141590b00a0b170704480503a50700c0740c44a400080c90400784070b88070308158407141410066a03000b000c03146401c00840d030000340080c083d442940100c000c119100e08a20fa000c130718103c2125181c15001e440c107c44004242412078440141b018003d01c94104140c051440714440d10030761b46030540007040c0b0b400a0700d5640c204001415030a8045803000c1c1c405114001103845 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 118535179 1250 118533929 118533941
    0xb030603011b030b030f010204050d060e0712030206160f140d020c010509101b0e0f040605121c090305060f0a15170d03060311041d031305030c12190c09 67
    0x8548010405692032402c25052411708151b00c1916841440200101d03642c0501412517960031150024440c900045564104000c03500080359400410020380304041d40022002e110b200d545503480c0c0300c040c1e4a02c0458a06e90700340c00c10780010b2024814030151151820003462021031400006103004c940504580c00e66504644121903030b00002c0c01d800f51402140112440c03501c2038017000b0010300441d04041c01c1c420003158041c0c05007402c0350111501d031301c81e9440030000d030200602510a846120005503a607120082845090424904040c05900d020f8150001501d03400009000d55945a2060024211000380442000784d1543e0603710a404030701e1109000d4203216a40800c45032048042628142c010000b00c001c241c80c051041011840003400a10500d00440e00411000303503c0400b044444071070480049030b80030010714092402d03114046d2134200d80301682503ea4600f491010401d112151a00081e0300750041c00e500c1c5c295801030181c951101e845040f80c042003e407204400380899078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 118536429 1250 118535179 118535231
    0x305180a1103010c0806010804030c05030906040306020d0c080105150c011401030305040f050105070f0b0a0b1201090501050a1404023c0f031b310b13090203070b03060301 75
    0x40e00c0d4121600b030038001e020a085450070711038103d090000008029180c024809010030203507113020006c000c000d0007103d040400080086445a40702d0410b01c0080d4031004122a400b450411a0b82da85405400c3c6039048403c002c00030000c18800c1410100d150f445869408103555840c40000d010f1041203e03501c0c040c50180e9603054440c0c0c20710708102d4005010b0b4202c81d0501c032040c0300711400240100f81c0000120791054400e011901e0380c2540a01500c0f80031790240c1e0040a00c2002804044150702a02c2d41c140608020300c41c50b2500140d240c00c4a462007080100c0309000030000d03025081c890a4900c42c3e0404501d403900302540045040c0981c900a15030240310888003810203e2031400c0007403407100702411009454502c1028103260f003206030780540540100881010541200700a45004020101c082038003100380c0320115944004001d1200c4e080d20400e407100800f000d060540c414201d202d94007030001c0230b2141c00d0244084054200801140d0b042d900d8804c00c0d00c1d4803024080c09040c0310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 118537679 1250 118536429 118536443
    0x8040b0409020318060c030a0e19031110020715091401050c090a14090a0b0409050f0703031b05030a0c021f03140c0f04050d0302070b2205040c0f0305180a 68
    0x20a242e80003124154801c045921300b64460028806da00224100301d03a004049041d0000c1c00382070700c1c480c0608004088140242c5030041d044400d0a0580141c0300001100a24003030791980a48036075001c089014039030019002c030b80d501440302400c170321175488103410394005c580700c030070f8800404c180c035080d20070032100001cad081c10100340302d070b42c40c1004486500503110045200b00000403030700206840100041c401c100450703d0700001a62034440e40d210741c0b0681e4020044d2950380c0c0c6141c2155a50700c109100850000b50030703507800090f1408180d06505400e070310001a6142800701042150802a160300603680145518000d030000030301d000014000c074603d604c010172001c10140f1503032410440141000745001c0100b182440c01031a103021103060390001c486003803140c2c0490404a1920100b40c21105d04400c00040d180c9900300e2030480303c0b0442c0e6104004200c095140c209010640e0700203159000420001850003c0150190f0480c2e54040220700c032000000b00c49016292600744003203810b071000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 118538929 1250 118537679 118537681
    0xb0f0901060323160806040b0a0902032a0d020a02070b0d0506010e090601090909080c01111c0c0903080306010c080d020406080906010f03030503070210110306040b0307081908040b04090203 83
    0x101c0070765100e83c18401e050210002c00340360058844014000202511040144440005e00c031503540340e100790b92510000d01045155a01c60450030300a5005a84844c10890b9414031032540310f070781000c070701061016045860f040006080d4800060b4118403d150194043c1c00700119017050300c03c014050004e080710340800e080c00d11100140094603100200e034080c02e042d000b0440e60303036003101e41e18044400c0400300240700040e90510303400134050050103090325420030319a01c0103202890041c002c1c5241101d818004103809550b00c2c0f00b1948000d4000b00415841c42c002c00c0440d24460141da4000c00604020360b111305196565038080c0c0c8150908030055601007420310440d0b90281807a5848002c00b00201381550411604018200369888001c04002001000490340c520070701c5946501c1c50071600c03c0c800c40c0344240c0300c0c2e01a9001221a903019926041040c0b010703180c0058030324102c1d0526005400100006040e6503c40d00080e94140d84040c0704220001c4c0704004d08004000800c3c18a100680f2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 118540179 1250 118538929 118538951
    0xf270903091403010c1b030c020d0c080f0f0a1502190f020c0406080309060a02100c0c03110a030801052103040f17030403080906090103091a06040c03110405040b0f09010603 76
    0x3a0b485850786141c003030f0385091600441c8917003100c1100612046000160f40f100e00d5072404440d4000203400c0250001c040d140d0702c02c2000250421101a01c0b86902078405640c0101d640b49e60300e03007442c103100e0925402000c2850108070000301c0c64610081150000d03180120314240701c21040ca1030319102001841c54580b401210b0360621000300b420764212010311080e40340c02c2c944d603901e006038100f0511820740003a624a0507402044049007100c840c000c180f0044170342d0301e800b80c6200c0d5840401d4001c55501c0b0001c0c103084001160b41154980c0c5a12400c559909040c140b00105580e60040749401074081d40c01d24a2810400c080c000910070352b0480900182402148030400503410080c800d15441031200f440050000740c26030324034000c151071594031030361001d0040740540b2150078082d02c0c41215010540c0c49034003400d065449a4001e5505112890f0069421400c130317818007180001007101031105001510f0190041680c0840c024040c4400c0d1589500041c01c024081e4403000119540d000000380d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 118541429 1250 118540179 118540199
    0xf1c0c060e0a030204150e0f0106021c0203030f1b04080705040b012303070c06051e091c1202040305070f06090b030f011e03050d030b01030e01060f27090309 69
    0x542000c0c98416840c0ca101d070040b8804200e2404024070503a100d0055194290302c9a40417801404030410581301c07400c080310b6040742e52800303004142c01030003440c140c0381c003041d686e0121b4080301079a90700440c80c40d0b1341c0600201d00140c014041481d06240d10842800c8900752a0140c0003400d004805007a65a10b4001000102d6a504917820706021a12984e1103800d42e1090708010140010781c8036942d6680c5070342d02182c0305079a031840107242a1030941407203000b00403440e96a90301d204c600c0d0745880544800c499146d0f01c52151408024a48420850205080c801d01102804c1d0318810400742c01c01741c8039510b103400c1000580041a1105400000300700e00c591160405000f00081c6142c02d107181020a100b41c1140300501030002c2b054500b40071721160ba00c5004c2c0010081d60040141c9807042c110101c010090600a905140000e0034140728107120601842081c00b00cac1c5a00000c80415072401c200003180c0e21524440d2500c8100c016540c1415005501408901300e100b41e03103000c01103040031960340c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 118542679 1250 118541429 118541453
    0x21020a021002032101061e09050409030e03010f060e06010c050313030b0610051305150c0f06071d0d03030902010909050408030f0a0c021002090f041109030609030a08040f020f1c 78
    0x6204d0356100e0f0042250507000200e819040342c007030b0b1000d40884d80e403030402ea44034182648410340061401902d0010f15502900d0708280320402c030000d01036040c04603c100107440c0b041c040d140c0451020030200b001da600034610148000d1003041500e003030000b00400c4032214280744d4401c1d13a0390910130781040500d26201c07a80780c085600c0d508003107003009422a511494000a4021035003e810701080b800b000d05482c2050b14070203800c500450f1a24608072444949402e815200c1d040414495032a0b414408490406018032400242510100c0d01890300e00303c0c054008458142e0600118050101d0369a04038003900703109d5806203004c00d0792030034114180c10084034000c080e004864a030610306030b043d982c0403030b03032201e0b10240f104056103d010300c80c00180c0003d2044410341d40149020300101c80080160081c00d14510224181d45030f1781c0c1d5400115403a8411441144006103415000400140b20502280e2010340081c02d020304500021020030440e07070103403584500b2001c24215090800035007007150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 118543929 1250 118542679 118542727
    0x1303060506030307050a02010c0c08010221011d0412180801140a020a0c0f080c10090c0506030115050d021201060305060405090f120f0903061806100321020a02100203 73
    0x43d441c2c444d081d2111034541e0030ba484002c2c100311501d050759090051030851403010f0120b84008541d0341caa1181001c04c3c00c03003410000b80100400c0700000070031500d140396800c4076040c1e4441516041d40c842d030343c80b2007901d08071421405100d03440802029240003101c285014040c258000664510315111b800e40b080d0005000d1310307242d80100521a03e581e03000c501141402d130301280b03a2641d040e0034a00142d06010701620b413501403152a004110841c1e8030b8000071403090150030f002c104143c84009011003440309010f041c100f4500d400c80c04510390700c42e2001b41400e6602072001401c01a20003e00d40703135014280d000c14002038485007401100d2420388100d0b500b04003914010011243c24a03101070301c4079030030b0450b1140460080f07603011000b88007908032040400000d0a451040c9045049000e404906840107040c03032041c9000601404a40c854441c10340ea00650b900300b0348004d412100d000b00031100c0c5150114080d90031404010b890f80e035140c0c80e5000c1242c028584940b009206020000c041c2034903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 118545179 1250 118543929 118543933
    0x1109010c11120f1f110a0804030c0501020315010806060a090b030408040504090b060112050426250b0a020a1409040906090c090b03070302060d09140d02030307030c020d02100c02010b06130306050603 87
    0x8480440810b000880b0b910406e142007071034091b9203500b401d440b0482c1fa9200a010365000008004404c4940d0310100c0360564262900501621464203101c05805088201c60100c0d00401c1e0501c50320f0080c20166600c284108011854261140081410382c2c4500d00110f413400300e02000e2000a41e00b01c01028441051040104038078505510380704903031007440d1100d100b4001c0d0700b0b42c02003c8402290841e1841581c0444403030070514031620351038031201e2703503201511184803840101d10010103a0088807201040c0d5030740c000c400d02500c1c140801d04d80c00b0038585544160b8500d030110002d0550301038040e06034015590404000e20346503011043c1c070046c0c0c3c000c038800d4002c00c2c000d000582e5014103882c03106103c46c00006616403146080380304001c64001c0c600051056002040c0b805900000961040c81243e8007400300d55600007059a40701d081138032903400b40c0c1083ca80030410700c00540c05402c00c04a01d00c0041091901d80c2d01082060340f01e41c4820303001540b403000c14424800d1501800d0303007112007500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 118546429 1250 118545179 118545191
    0x140f0109020712030c09091802100f09050609011e0e01020f010603020102071406040b160201020d0c0209040611190302041e03020a0306020c100c030b041109010c11120f1f 75
    0x55081400e03116450f00300203169481924551142c420146c200240001c680c0412007415642041002030981c1c000803442140083c0c40902c540344604401c807281d92050321419242402c0c8810044607800002c1c100341080342206500000d500400784c11500e2240948076410b60706115030009081001c000c0e0f40c030019a0414030b003000140d900003208401c60759003038906554011071b000080c105104130b84c00b41c15060070101d010404550f01400300c025842c801d8084804511088109582150840764080e51200740b4800007000f0410640000b001c2951401e900c2d450204cd4084071800740c0c80315440480081d9000c2414402c0094004012001c1c1c1c050b4402c21250602c1d5030700140265010b07002c020000b81e00440c14100c100780400a014015460a1080c080c80c0c0000c0b000800602c1300d1404503215a0612510790034003a140b00c2150300490040c0c0d00d00228000503140e284440380e0800078980c1003000c0340d455003c1c0c410280941505170307001c40c1c05085458400c4c2c031040284101c0d0344541a100e840e041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 118547679 1250 118546429 118546433
    0x80105011d0405030f03040305042d03120908121b0303090d050c03040f03061e110a05071a040f0c0812160204150e01050a140a27140f01090207 63
    0xc482001c00100c5042012551185000c3d4214041d601c101d0003202c10110034001091b40004c040d1003601d03d61665442d05031040b0341c01510912280017410403031842c140c024008960349581d5050b01101908080b001d20382d407200440e1802003211a02c0070351801c0032802e20f490600041c0316900b0072100c00002c2d415801c100100e80e40780d4000e00000d0051200010b40a6112001071044e100100101c035000350310181c0c3c900b0144d000d404002414280080d8003010070003146417900ca043d0403076190ba2401401e0869007042950154000902911407092210307840720411082e00e80700d4480d41c41500450305031107280c03030850520000d030313040500e003900009184c008a4452005446c0200d6a02d444e84da0694424000701e4010030b0300b6045805c00ba42080c20220744004402d61884c12100c0039540c0c810055600c1c540026841d0b158a5a950f10042420040105881c4229145540000c0340400050100b552007038604944006004083c0b807003040c8e080021800314404603600521006000b585000c0c5c0c15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 118548929 1250 118547679 118547699
    0x2012c1504081b0307080d18150e091308030a2f0313240e07050103060308090409030e06030f0709140d12140705100c030b031f0b042408010501 63
    0x1001070f01c07000d01d81034903040e5036035904120510003801c1c80340c140d03800c8042812005040980c0c0e224036601104071084001003050602110030381c882d48035580c000d102d112090410455a074040d0041b542100d9001c088000b0440c0710380298010880b034440024212020089503a5401010441c0c07528600c10031905900c4d03c1440089a920181010640060351101d00d000f4192a0340d4100c0126400c0305105004098a000d40c4103810002600044640095139034004400740c691074000100100402c3c00f4000300c0d401c0c2908072001080c030a013002c0c0da5200075040414055001101c031250035403104020701c40115085a0180b0107801822084d2401000d04000701e2030842030103500419520944401202e254070840303004080200b00044650b640d4541e0a002e81d40301c0070761060880252a2089800000380240308003901d020010f00a4000c20401904481080c2c2e0344103403921103180c86804001c0d066840307204600c2401034645000c2c8600300300003820030b52082586c214030f80b1a80b500c0014800745c000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 118550179 1250 118548929 118548943
    0x70302070e060402070c030503120a020412261606050115050a050901020f070f030605060d020d1709130911012c0a0305010e010b031b090705030402012c150408 70
    0x811a50601d40d80c640c000424020300c070b68034000c4c007580301d2a1004410410040018441c0c1d50490800f1302d6035440345542c0c08100d1082d4810041d08000b031130240300000d0010501c000c1500c3d0320b04039030806d607604c8402c00c070140d0b03203c407054501003855560540204a01807041d44d015040301c030f40500ca441e0ba580c001520034422601c4c03020921a0204020125078802c0020744065100724082e650b130280d407100000c901000302d004c1102c0f018100400680306003040c0c0904d421305600104403030600036542d01d1307140c8980b0481e00c01c924080707005c000d42880c5d62074803404004601002d0000007665003550915082c5000c089018904100c0387c030b5005194580c14034000401d01d801e91200b0307e1560904400111007600d20741c0020070035400c0c801000d40210040d4807800c0d1821040d01a690038002c1f0b071002d002c200401e60010350703100c007100d40030405c4140700f0809164000e2041c10200643c1c03c0e4002c0800709018101145065140d40190201190030310004002e114005c5941040c1064107085e203950300c6840f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 118551429 1250 118550179 118550189
    0x901120c080613021e0309010b011b0311070e070e090601051305060d0b04090807051e070e070e120109050c040e06160e0d0303051e0408120405071505070c050607030207 74
    0x2e5240d880d03030641049503040312540580c05548001c03224148607103800c60b410440340316115509e0004840502d5004100520008090a518802034030f095541030341c0c0b514450f00001c00c0d03031103114400300700b411a07900554010045611460020401c4004202401000070503540c10041705002032101800704540031000c1e00d800700d070016150b151041c1ea0780018111400c2c000c1d441030801031031209011415008000b441c0c091019100840c44008641d0702507801c10489100d917501200041040d5041e4503500da40101c51440d101c3c0c40109103600040300b041c0015804451655600619410060108030f031410300c00042e1028404d200f051a4229107914008198800e959145107250141d140300384c18441e074032207000b410180c0e0b640842c2030040060004441181d030110841c0e09030181e140d1401c51041c800c0740d0020640789418004207100355924030180c001c0f2182d20443c80d0204040c51150744081070401c45642c2c0340e0712108030703050001c80e102d0309510403402503030b00b0004640840d0b804500042550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 118552679 1250 118551429 118551439
    0x302120718060f0c030e03010f0609060e06040501030203031c0b0901060201020a0801150912061103010b070b06040b0a23031b01020115031106031008010c110d09060f0f0c060609020901120c0806 85
    0x5050700207e0b0241803800030303090340c07240f60620120710815145c0c044800e60b070320010030000b03c0d921a42403004664082c04042c0d403652042c4540202000020301c0607005075112800842c030402d01e80c000c2040c20303102703070080b40c0507035004920401400c0d44002228010050b4403d480b0848040c1000070701150060300401d98001908215482844141d4018000d05101c0c403041c02d50702d603940e020300110340c1c001601c02c80e03007035030540d01040c0240741030b002c0c000c20540001d000da1001e0b032a01100c0c08040c140204402c0d4804c089014250710b9076814014103090307421418104181c11410000203003110703842c01c00d802590001200501c003184401000120345981601c10b29902e85903ca414000c908031a800700d01990b08090b4a100c840740d01018071401c4002c072138100c9460303040c0032100769008611405a84001060035580d10000c5204820404082c01c15041550311825aa15101e080e215940c0000c500140c000480c0e0f115035a11040040e11282460410410240464401400b00d81c000d41198412 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 118553929 1250 118552679 118552697
    0x10b0d020a12060b0d0305091008010302091302010e040507030c090e1003140f01061d01170622060f0608150c09090a020f03040506041e0201120c0302120718060f0c03 73
    0x101e04d6210700b8086500611910301c040480ca00109998080da510074040c2d041304011020180c0036141d90b906995004045c01d0719503580140c009000c0c0d50b492000e90421181607686800c94072039100b21b50055600380e90204000743c22002c043c210030555800001040102d00030802c0c0c8035a0301c202002076907800140d41301d44001c803a140d24a001c5d56a4240c12803540f8000d00040d199110205424900d440c07110444000c0e0383c1d031900b168100510b9460b004440e00300d540000e103120140203203c511100705100e0402c0d086040e40b80d2104581c3c288580c420724981e50a0107001100041081da200c142c80803080100702d181040100d0114000c0d01c0c4c0c024040d02d020310108406010b640c06540c2034500804c801500ea1078103041c43d50b650317181901c0c20345104030811403464000740790303007000d000c40c03601a100c0b00d04401c40103807490000d11641003d03008043c2d0902903502010b0a031114580644850b550392254035000c00c030008180b504a511030801d10917440c4070f4800e05a04003c402c42c1c410303010b0401c0480c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 118555179 1250 118553929 118553933
    0xe120d02030601110f010c030b0d05031606111201080c0f060d09020102070e04120f05090a0b0702040902060304140d090f0605070512040602100608010507020c13090c0b0a02010b0d020a12 82
    0x480040001030030344c0b4019440081c480b00d84c1507004800314122585c0502c040c0d100d40e0140203121800505c003810b10380042000300c6001040a0100c12101d104042c0015400314a070001c1c00c0701d40002040715144e40911004000e88041040601e40200c81150180020054100012194803600c0301c040000354644200e00107680c000d001d00342c02441000602d202034903141c601055803a10880b25000491640308060082c40d1241060341c19020000e007001540c0c90503c140d046147d000004103c0e40561510050b500503115040a1070007144610100400742000540380c0e8100169000210304200500000f00211103102d9220411240b140c1001961031205007020f0b81850354019a4400003000094002412036000595640003c0700e201c04002054440241609036141a03600c107005030f21480075230440341b0349401000c117292000d003000244480e030380e61507101c0900329a00c101038800020070142089602805900c0e1829000c9a4060708109180d0014401c245c06002c0d03030444481000242c0d003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 118556429 1250 118555179 118555187
    0x140a1109120a0605041121072702180a090905070312020109050607020c100206040b06062b020a09050909120306010e041a0a06020f030f1e030709090e120d02030601 72
    0x1a515400100500003032926040c92015900403500460192014000000740940c040300b09610107c0003030080d040381458101601c41040c0c920600080030365522100c12070080302c44c4014080c1184201e0000d5400302d2960400a152001d079011b10402400e0400050004502060180c241c0740c0c0911403100340c0040c250700300e0042c12444001400b61003040d050107c0c0070b40009203604800c204441c800c04102c440d0340e00301d0300c5000c152401051603006070041203452070000c01400b03000e03041401c10714017101c41e00c071640c01b50504140401380880c0e000820090203540804480c001e480155041034203070500602a9540e0010030280c043e1140010010130a1070380300c3e02d101541403100a20030711a10031494101c2070303a54601000c4511a00040c3c0c400520300b4000b09210141340c840c400550309040d40403a2402c0d90f81d00105030310310030558024001d104640c10001850084415684d00741e4500d0401c1c41100480b142084402d00c0c5e0b6110310b580034036402c400c2c4120b41041f00002d40158580e1a0b000050b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 118557679 1250 118556429 118556443
    0x50601020f0d0807050f22090902010c0f03110307060e010b06090108070309080c01020708040e09060f010605030604020403060612030f091406090f09010b0a02010c0f0f0503091609140a110912 84
    0x394080a00040280c401b0780c04082c108480900c15002c00c2d80140d07942c06407009c0718020358000b4042a02642d425010865903491402500d020381003018141074072a20007411030744030b103000300c40071686c40c2001c5408000c00d10610045440540b58140f40070344003000078010341001009201055250700c0042c04005040d0305440348201404001d54036082540380450103500203000d1381e40030500c3d003c001100d007540010001d00900d00d40700040110790818000300c89903030006240e1500246c00300000400034019101d024010305041056a51001c00340c9001000c0e40c0001008004100c0300240500110304c244491070300041044500c1da5446030a4804640c0807044442c100e5804904400002f41581c0740d0001080c3c17540242e0f000b0800b8072920a425544401c2622250001580607540410714a0140004540102100302110301c94403400c070701f610901d480b907000704448944502505e80503500c200310241d00306c1446502072000f0005c207004081980101015280300c1c940441006c00c6c0a11300380060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 118558929 1250 118557679 118557697
    0x30702010605150703080c03040f140109050304030c14010305070207091508031617030c040302040b010309050a03091802030609060d031202070c1d0708160905091009050601020f0d080705 82
    0x1240304440f4040c5000c02da801422054000c11a240000340500300440c0c1203038403c61384080d6041c40f800f00f03511030351075a8004224904d0150b5940100030042030b0100040c0009501c2410341240c69410302c461048030f2030158241c0317418076060805104036a034020a9a10907507440390000180c0302e15420300464049030550002c0200c0c00b0004100c03a0220f4080e40301040c560003031f94085500300d40560302070f941c0d01c0200e41c054043d40b814070041c001864a86c04c844160340f4149000300c1e0101d0103440da21b09101101c03000314041035a0440070016040401c1c03442d20400d007091000c5003989000700105d00402002000b141c0300d50204030f50740c401c240c0501c2160b1010240300c5400c54a45840d440c10203001007850044640d00c0000d80c02d442035a110030280d03540b086005a55040c890b455030020007040a6500c90303508244121108049001d460300400a8403490304290500e08091402038210204d400141c10281103410200d10a100090f0015200c00c000c40103103080c1080e55136691084806002c2c0501e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 118560179 1250 118558929 118558939
    0x4020d06051e150913030c020103020a0908030313150603020a05060a17130204060e091f0f1a040c0206010605030f07090902030711010b010f143001210b0a02030702010605 75
    0x900c07040310800d00b0744072079144003070b16401010388441c4500362140d04901c070b00031b0000e040343c29000015442a0040d000d03030350181c1052400e003a242d032440390468008980400010850a4042c014040c4c8251b92103a0894031460400c0207504640110351500c2d4907005103030041000085c03d400c020300c5117242042c03e00050b0500c8a0300c4c2400e09600803e03c841000c00d1b4800c6007081404643c4c4042c4040c1d0300c0c010091035000304410341e4a403540f40300c00e00ca10742c0c03984039090b6690908841071034180070389560f03604a03031007505000402e041007004031101004514219071040006004860f0040d0440f60882c44a4506100d81e41e11413100300c48404040e04440105400407007031090b0940c12030700c1004d40345105030003440194130500045521400c182e000d0800100368219522110700907800419811111084103008601d030701d00d410301140032910340256800f10a40c01042558140c0c00000f408980004490400c1142500d540d000c4c5107001c0c1110f21415400000310f003206000b503210900074100a40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 118561429 1250 118560179 118560181
    0x307060b0f101107090c0503010e100504060b040e0a0501030f020613120b2401090605090414040318090908072a0b03100504020c030f0c03070c080c01030c0804020d06051e 75
    0x640103002149444120249200b1480d0103c3c011003030380600c01c1910f0b19580c1d8a429a880d0500782b0f01ca03054040c2240340c0700c55004101103100c0d03c89001c2c04018010042100c1e0f6280d00d020700001d01d02000a00340311015103040e005000203038581c201e008050342c04880e180c4d107909ca10200540b17030202a42c08010781040006582c0100118512904d104910408410b08403042c0c04159000c000d05240f6250f0018801c520140a000e0065014008002c4050710008950070040d044015402094400350081132580c1005030b40f103000d500c0360b800503103040d4106004a60703040c0d840030b400e402200390041070a008604441c001c40305da9601032041ca4035541c001d202c203e6450034508503e40c030650307405100d9211447e010400b401c0c24000c44181c0c410590080d40ba1003090307649203c29412480400c2d240c0e000030407144010642010070b0401801e01200905000c2c810b82002400300d030802407024090200340c4c410040580e42d0a84c50356400c0d9086038020034103a840c0c07104900b405082003c0800300d005940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 118562679 1250 118561429 118561459
    0x311030d05061003020903151003050f0703050d0f0c02060f0d050411100f09090c030e03040807060e01031a0f1c060603021002070503250906140306180307060b0f 71
    0x1070032650003200c06036002075840341c104800720268410f4010b00c1e80c243d0303c010241600c50f00200005540b2280c0c890050004503280c2e540d01c2c2c14213460241d21030041d880500709005015040c4408500d0a9417403c20041c031103055000546104039201000e4802d038804a0302228841c10802169442483c288041010389000d15001480700c484924040c012001c240791000740d00e004a50f034254a07040b584902c0c043c20b240c0003101010300304005010080640307540c0501c0c0c007030030308002404c0501a003502400e251420544020184031003100070f0340c10581407683c03004100100899200740760101382c4a0081014581c2c000c16195100440640003030860f4408103010702142c1c2c2e003e5401da910032564594120003603c0101e81e503240758061741d0f0340740e0020400c11540916100e05500c00001c90320f0303405003080d550080340c0105c4015134005014220b03a00e005050134941406000e500000107400310b80798044c07400003240d607405540d50007426665a40d11001581d907525100070030049005103101704210f607503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 118563929 1250 118562679 118562681
    0x9050a020901091406061303080c03130602030301090f0614010e010201060b030a0e061e06120a050607091d01030309150203040306060906150807020606010f20030a09120b130311030d 80
    0x113000c00074a071066902048051074490112031011804610914141d0f003141c850b0304442d4030280c18140302d44810003040d414190485e0503135008103803a802454980d85400b41d04030540b426050b920400300e1604905201c20401d040b07a141341c0c0c450030701e020001d250201c0010b0340148502d40211100060220401c144103c1c2500007040024074502551455102e09060000e0140900c032008000c2d00450000361403402d242070280704403800030088a02c941060b0b100d450a100050f5106d4000440350802407041a400c401a13410016450007a40015855a1402003101207603004180c061280100031021880c4200f05560266400201c1008100e95030300b001d81c0180b1031840341c012002a185a8842500d010700700c00c034418032603500649515a0750b00c00444400000d84084403d0100300d0303c012422040d0248104a008440401181d5402c0b108201505400899225010180751040030b036000076103031000c0581101d40c11201d6405c12009180940e0f040c40100b082060780d2001162800c040c84007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 118565179 1250 118563929 118563941
    0x901020904061403071e17010f05070c0506070503090c130b040c0f0e27090c120313091d0f0703060b090103120c050c03030703081f030309060309050a02090109 70
    0x101d40c100001e0341ea45002591000311001000e5054100074010004005450100d032544441c14914241d040d4072a400074050000c6990141c2d074030fa54a150781c6845910f54400c840e0005005d0510212040d1075685850b9100390083c8290200200030012407145901040b40590040b03008044910100c240c0103c68014400280d06600c641d040c51115115940540f6220f024140d080c1e5070b13802020003208c1800003010701038003088005500c0c0004034a010b50818001d40c00381c0111405005882795074001c00400000300302402440b0341040054005410b25460f0b84800c5825200f004030300320034085071101030410072055000c080d01503a96501d6201c10041441da068a00c241030401010302c210040c8030000c602400006c3c44590750045002c1014003034104100c1946c0300f6030417500d0485003071000c6810341d04903407002c802046180d0280680c0588003115032842d0030003051021442440c585000307250010b00d20800c001c1c0b55a8003031a80c18803000b40520b80c0d1036900604041040e503514024039005000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 118566429 1250 118565179 118565197
    0x5270d240c1101050106030c08010b090109030b04150c02010209061204140703030f02060c0412330f050603010e1e030f1309050a0b0f0f010504050405040b09060f1e0601030f05090102 80
    0x118100010030191f00920403d05007031001c0d0341701c009981c240b081c030402d603502482d486030520400402c00000140c19219441c0704610802021006444901d90031341540c0d40b007166081036900500c1440784a44801058a07110340d003002180145483e2410410580c0c110079900080b5400f99480100034940c00101c611000c2c605503084400326591800020064021350003900341244503884070750003080b20382c03c80004085684451034203104241e00c000362a0341e80340b000311850507145d2024150403c002c4c41069403010041d0000e0048000401d00280c5800403104000c2186104180d541d88100040061b1001d444003101c280396a10042d00b034119405047e80f080100ca14100360000d1213521550046541c403410240c0b000ca29880d03400b0410003014080c220080c1003080074807002a26036698015503005038040c05032051075061100d6550305250f4011304a220b40340c00d10080c461488040c0e007040c0e060543d60511450582c0784c0400403400303450b015040854003070038101400761140041d401401e000c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 118567679 1250 118566429 118566431
    0x40b0307080d08011710020a050d0e0d02010b0612280e0610050111070603020d0207051606021e030304020105090612040303060f0f0614071703040305270d240c1101 72
    0x3e0303660395148041d182d40312440f850542040f00000644d006e141c000d02688011410034a080100c150308510403226101841d070b00710b6200d105c00155864080c41605840f5800b03889252411045400c4201c2c00c1d00c01901800380103034910189410508086020844203044410911001c83c03030144450781c885054410f0f2003079007503270000040e2542c000d001c4688030018030070103044464030308641a0029008102c000020f16020030035000080d8081c401c020300981d50581e0f0300111420100028038103006500700407004080703040103111382a000002c4d00e6010790f09203492581c980122010030620f0042c0250190804903040c1444205505508100196086422440401c55492001c900c00344214422540481c00e45c40c00c482d4443d101400400a0307d0144100740012540c0d00a05003455000b00c0e410340000d9008103840c54074051402d0b5046600401183c143c0980500d5000940d08050b40744005105460714040e00b4250483c81801c440a03044489040109000071040580003003500000c2060035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 118568929 1250 118567679 118567681
    0x60501050109050906040b030f120c0106080712141509060402031b0d02011107030503130905010812040608071206060203090913030215072304051314060609040b0307080d08 76
    0x65449602510b08444006280800540342d0905010007801550456509802a605140000030301000b007621594840220300c1d40c2d070a07a482c46d5508440380c0750440c040c150004501009400403405181e402c942c0c0003806000f805200548042c030344501c01c00c000044410a10402c502c0d884041040c601c22070094098640d000171861540440e0505602180d5200302d11005200c0954400c044050b41039010b103080310495a20b0f5110f20780b030741d00034100300140040c0103032040c05405c00c00d000301170040013404000c0143c0100d101c0180618000c83c0581004c00030210001143c0c948a6100070501d0071030150200700b40e688030000292a58055903070180502d41c00e0000c2041c012841004d540c005405901904400e50012060340960501a0183c01005003041881d81400e00031181c40600700381003005662340758135100038080d115001d40a01e41e0b0151401a070550142e944040080d0700c04011106c1e40c0e9109140c0b400500140b040b50501c6070948100000070410b0000040c50700750841c00d0740c46801345 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 118570179 1250 118568929 118568939
    0x8040311101e0c080705041403070b0705030a09060809060c0307180e010501180b12071106070807260a0b03030c070308091206130312020405030114010608010807121103031e07060501 80
    0x80c031019105c50000407810403042100c003c40d043e1480030880028140c60f030040d55803030702d020240c028600564403508001240ca500c550010000c40c020302c05400c010725a03151907154552665402022020032013000070000f1901c0703104a04c160050300c0c50031140c2c010681c90720b8818820b40d0090044c01c0c08190740100c01c0240c0c0508a11001c1115808614a4940078000f8061240e0050107040c04007441490040ca8520752020706c2118811602555804035030b150450000784032441d00d0046030001c0003604441241c507400002072541c4144e8070710001c034640c1c020a011900e10300c00c881154845000310325020040060b2040240365809085030756194500150f80031079190f4070107a80484a001418421800003030250341aa4600140b1010042c00c20b03942d100442c0c251000c1b03174806200742404800511582e50401189400b4000c90801002c0c0c8a05161144400100c1c0c1ea4010b09801c00841510580d035800304100c13030805030b81107103001c21000c1580740070010350001c0a0071a01d20341483d0010035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 118571429 1250 118570179 118570187
    0x9150e160311060702030a0212010b04180818030c2e020c0303030a150e011d0c09030c150408030408160806070c02040905010914030c10090308040311101e0c 69
    0x10560ba00441400d4800000b003040000b2984040340480e0140a4080a84d000d6560304c0307141e0001a4828002244040c0781108210403076a001a084004080b40503418000c603201d02d06030340125201480c21701c5001400300001c0d1400c002582c20350341c03241703c9118004d80c0304103201c1c076038003010301c8402d00e40250300c001c0c07400340c0e251b000110310b007034243d0f10900c0024a11040313500040e1403150018010815a501c2d40c424030200f81090300450245c00c1c0c81a80c1130032001010040c640c0c0001013030412410b00c00b009001a84a9024092980c4900040412180c81481110841300100b201c10103c82e665035407500b04035203840040f0b003c8034102d0110100007800c03d002040b4248915155a40c650701c040495007044001c200303094040d1425980e50302000002044c1c10310680b46048014000c503200c007043c0701d140b40340070100184407200c28141460000025009000160001c0d070500b40350010005080c10280303803001c0c030282015414100008000004460704504110a6031044103002414000c1d0040d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 118572679 1250 118571429 118571473
    0x3100c11160308120a0b04020708040510030608071205030c0a06090203060c040b1b0102120a0f0608010b09010501030203181504030f02160902090111060a02040e0105010f1e0309150e 80
    0x41d00e51542001341c50410790000501c5507120302101d20000e20243d2043c0410200d0700080780490b512000040c1c10f2269281a107400c11004c6901d180074460542041e030fa05480d0f0691340701d8800081d44684c50501000000e10a80d2044980d1f1811640c0020190411801502c0c00304800d0340617004030b8002c40c0846007044211001c0c3d40305030002c545003c0d5003007640c800e2181089410740d034655081c00682c8107800001c50150251000c100d0200b22039016a04c070908540c00d80d48404510384c90469400c0e01501d4103442c10781101d0090800503241c1c0c0c0d805140d110031070240444000340b03005514241c000015901c0030140214040c0d0b4508501c007c080100381d0341e803010802c050960311800602001000c415400903c2d85504c18901001e94880d4a05402d182c030001743c40070a0381c01c0c0c01090901c52045504c260311b00410091030080402c544c2c203503001d404048c840d005070b51050500b5200c640814065000303081c45a50003821000d1951144031700c03000814480c0ea0060b41da00445501501c2e08200300160 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 118573929 1250 118572679 118572683
    0x2090901050d0b24030d080a06151d0a05060409020d1805061501090b040806061203070201050a080406110708091003050c0d05040c08031c11250203100c111603 70
    0x100f5840d86803c502111000082d010403160100038085650750f5403001c0c00191010411511590303040e08100b494035040d01d9140d0040300b2101078802140248951200d00085034204102072803201042c03640104010800980005400003030000d00001d8508440d0b0050919040107070003006400e00700d0a03840c5c1500c0080602400c2079220700f020410350b2102d50f006000a4005050441d1071340ea85035002041034100394070860313040c0c0001d420007043e42829039815a0004601c809146011002c3d03001800c5c0e4054000024100440c21000030304000c45544030211507a02401c40c00e444038182e14100c88203030b20684845016072030036005480954001c1c0200740c020b020a140207401d00d0030002c404070040000410981c0c0d10f800031040040c411106000a00f4049940c603030070032200c02c01e0030307045040d281003941164010743e0801850710b108020007401c80c0347c8545101d180d802400140006441c0080041c01c09007810315100e5607100054100c2d175040c1c00800310700107503034072541101c0c01107035519024480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 118575179 1250 118573929 118573943
    0x140a05070e0d24062705010b0a08070c05100218030d1202070c0914041a090a03030e100c0519050708030601050306190605040e0a0506010c06020a0309020d0602090901050d 75
    0x20010000e00002c0114899014400a070b5541c200c5003030002c02511138542c0040045400700344000710201d581c00c5a041c03101c1000500f8805540342c07194500c3e891040d40003da0410190700b000c206140d1240b249030704502e8000c0c088640480c011542c00e0b00a501203603185100b0000403400810b01d040104601e440e6042946420301581c1020078850081e601c164000c40b0a000e40c004045010300c00f0384101a00340310a00a162000d150a140094204030100104c40105008904100000400140006c911503051401040d001c40b000e4815184c181489100f007091070420614003c06548400944502075103401403802091607081e054880d4840c40c0b0003d00003100030000228107500410045030880005440c0106d40071a1001100d10b02046404c2000082d0340000c040002c800000c1c0304a1b04400d105104100504220740040c240026550001305996008660b41c04964001e51006040c2a0040c010442e5441d051070220025841200d45d640f140c5c100b80c0c00807426051400f40e2000381c80d84554 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 118576429 1250 118575179 118575199
    0x30708130c06031a03010615030b01050310050f01360603020403050618031303060209030c0405090a20030d020114011d040b0a0605060f03040b01061b0b100504140a05070e 75
    0x80440144c1040c04800e101c8091001c0d8802d06910240704010007043c0c0100d02031f003407001210b002000da07442e0b40801410404184140543c03013102641400860300100c800e06481c0600710010703581c070f04400107800c00169545c020940001c444840e08041c400a455034440c0c031079219075040d4100d004601019180f03900c44000184002003c40410703015680810440381001c0340e4803081710300c09805400440d0916008100c48410707003420481180081d40854040c0700c54541041160303130382e0b004800094142890014440b06251140c0b0075294030904c05010398504042c00b9002a010b03108038000721031402c660078000100c41450544000f102c480fa1040980c1076102c588620b0ba84c40406004a1262982da070070000b42a40c0c0e5400511300d44001503000354403481c003400c00900e2800142d2005061191441e001c1c105150121030000c4042c3c0d2100109000d46c4909100120604042d00f002d50070034903040084010443c042d80780da11070603500900303204541d40c2c0342040300c41c405940302c101e805c503c07580 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 118577679 1250 118576429 118576439
    0x6090115050f0403020d050304091104440f070806060a050607060b0a06080412020c090a021308030c03030103050d23031f03210206060f010c080c010204030602030708130c 75
    0x9801400e90b902c0340740080d410b16441e07070000307189403070464401c0700c8580c0000340401c5485001e016440c1010045021981003078600b0b115054a03481c855008100301b54007403ca0002540703d00034866492842100480801d19070038039007540d0700c0c003804200e200340c07090b07040008407600300280c41880b40300302074184900f0524040a010003130700a050304070303421916550104843d8682590304030082c0351698074492a400e0904025849550041055003103420203020032100c1d440340300207240c00114a103070050341c960b40c06048040000c079503040a4000d000020740100c2405000004e103042c0c03070240003559941700404c0400d03141881c0162104102114200d040c2201c811904043d5a005002c1038541140c0d035604a030701c0740c008900d0703081168000c000f8040b420135100046465074a6100c14001021182004400501418084007900c1d041050403044401040580000e4500071800c0710001d5440d540c80303150180280d0400c071526800036010f400003c003400e03178008480005540003034449a04900302 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 118578929 1250 118577679 118577687
    0x30a0c060e0a0b0a09030309050303090a06110c060304050102030403030b18040209100503010f0c181404050903041e030b15090f090c10030605130e101808070b04030806090115 77
    0x504000d90100c081580000c1e00000f880040121115580d13a407280303103045140140800050713410184c000c5d403092140280130348420114106403035450500c00000e0714946401894281d903200d00c0d50300948088140403c020b8150007a40c0200c0c0b00b610103004880c825001d119540d0f110b14a00700307080c1c2c84800401c015040030400d40c1c0c0c00040151116004a444a0119094800c40305c2c60384030740d59484428003030b807551040c04050741c1800380b03182d030900c0b92402c0a141c4c8603000700905548100c0e03480c07010903843e803000c201b102c0040c883d9031041150100c00b10054036004840c0d220030b42e40484904002101841b41c01d14440c0c40c0c0c0c03070041c458070741611050b14080c44035a005000e000301c0d100e4410303000050f0352803002000300310406660108085003400140805d00c0c01d0322081e828460300340302d0101603141c000b28254840052130000004c41d1700036080da00d280d8040041016240140009291b0140501c1d6140d41c1d100354004d464404a64503000140110140240b140000d0405004510403d031442 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 118580179 1250 118578929 118578947
    0x10c020d0c02360f011a161209090e0c060a080406060305030d0905010b030109080703140409050c04050102010b0108070f0c080403120e130b010207060509011707080601020c030a0c06 80
    0xd4181d0744291402d107540f0761039403210070600c12140380381d00d42c04031100d600d190410f50060224a207900b407545800c0000440036004031165590500100e41901c140c1100f0300340085c9960003840202c9003041c50070000d81200e40074062025024109842414460070002e007102c01040301402035490048480b80c01c07691060081e00c201c0c2c00a481d42c1c8004003040b03080014041c1055031850005020405282140c00c540005040c280240d040c1354000e4080342145050366102901424600c0c8580d12562410741240715135000080c12601c0c0c84144081ca42c42c2c80040d01c2921000e80082105c031580300015100120101c2c1c002c400500d090100001613403055140281c1c0a208400560030641c883d41c2c0c2d039000650113070803100098aa0408851603151a00251070b120300aa40c0400485150030300003500c07001280101e2082c4000010b950350941d02c500070f11020001c0c2d031045c0c4507150a11620060a4820640c2c402e8018450040442009d00c0c0c00308407400d4059110580380c245a29020b0309580d0066 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 118581429 1250 118580179 118580183
    0x10618060e061b0a0605071101050c0307050a170403030b130902150a0507080d0b011407031d1f0c0605010f140d060207050d020c0a06050304031b08090301060b0702040e010c020d0c 79
    0x58401d40401910100143c0c91391610031240410907103001d1000401e9108402c080c0703000d0b40c1c105014802c44800001c11a5005003141c605070b40c0e2000f94107800e0b1200b200440c42c00708200070031420001410344c1580080c078240c8084035205240c15184c1e540c0d0060341c41440c800381d40403982c140003202d4004080001c2420003654140f040c1449080c1d110300700d95410078603600c03401c1c0d41c0b0b80c11441e45543c0c0c054002010b086413940403600303129498030001c0202e1801c2d0740d048051a0034101d080310580e55410404002070070410428492001e00d4401841b5800b403038000c540703c60614001041d0074010130800c009462845405008d00b500302e00c1003201c0c01d600c1c820280ca01c075508004407404140d040c00742c082c0c00c0d17080750002c22120500b5024000d01e646290301001c00c0220a105100000c1d5101d80522003410310000181c3c041c120508051005109044449a0562034601d000034070307110741c10190100f14000c4408100c0c2040124851342641c1c0c03201c4403070005030080303400b19040c03074021410002828 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 118582679 1250 118581429 118581457
    0x10515060901030b220b03070501020706021504050c12030d0506060306130b062101030309140904060c0e030106060908010b041a01050310030c09090506060d0c060c081207030203010618060e06 84
    0x411705100002580d1070b0121400020b071258080d041ca401d003082140c3c0104030031300c000c0000610b4910001d407074041010000c001801e00c2e4010078248801006922042e900049c40818a500d4103c03400e9901d5102a1b00380131102c6c00c0c200080c00c246020b10650f48682c00c05440300000c01c0d2001da0380c00040c0740414005921080901c154041c503012130842c100c40d2000c06100307264a504606014105000c1036110807161100005601400e4032500781094000381c0c1b0050128010003c0c10b0260707032110314a00401d4041d8a8007000082c7c0796401440d0300e04a40c0d044000300040b920341d800344010b50b0042003101c0c5980c04903c101c02d5070355100d40002c41c3d20001400c241c5204070748a58594070b0091140c0d10000000303440d082c1c540b06101c014003d05800000c1100d01d010980e50695035040d0041851088a0622020740340207018040c07040105c4000c10343c0300400e05100c0c41d01d82e1010b8020b410070300501000581e0b00c3d1644490901842c0303240282d42541d12480910540e2104015441d4010480c4203088 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 118583929 1250 118582679 118582699
    0x209130204381c032003070203060901051306090515091c020c031c0917030706061d040b09012417030403050304230310091106120a0b01050c0a0c08010515060901030b 73
    0x117015107001ca40303002c0801101a603918541d40c01007600d03103440940303804003a902d0701c414040c01c100c0702140c1c42545980120089012002d03030804a04282c01c640000c240544044100008282c001c0340d94489110281d84080450181c05412680d402c0500c2916405070b00900c6206001d201010040250a1072890500d0600ea141c402910088841420406090340082003400411600e4003503e4041c1813860110600200002a04d880011000e1f0014011280100c041109101e003900412820001c140360b4006495140404000c20b43c0c81b8821315003611202e114541091102000316811030f900100254105800c08440141002200118032810b40712000c01003107940b81070001402070000c40b2000981c5411b40d003041d0380b461950001043c4101710400040c4009464101840d401c008440303400100748040800517210751090020405651003135220700c034104092180f010064030b610400900180d04d5441901059219444500f544a40184044020380d480317580301ca005c1400080000e104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 118585179 1250 118583929 118583957
    0xd020604030b01090c0f021c030f02040308040f0602012319240f1505030a0902030304080f0d090303080c160c0b0c0f03030708040209130204381c03 65
    0x10560181d44100c0b0b98403400310042001c041d05118242041c074903402c000546a0001e00001e44600303410301495114400c481c51159014801d61001b104035056110465456440f410901102e8205116400c400b055101001c96124810302602d0b013036017071203035448058103182d580c0350081010080c50842c0c0140b0011140c281c1c840b4602a194216038a01a00300f0078080031001d0494154094000c2d0201e11101001000151598100e0f211412101c1c90116200c0d1501c00c40c1ca0302609036800701961511004c5008120107034081820b8000c09811030481d4240c085544054407480c140788030140200b8080c00004404280300002401400c0c205882003052044641e43d14401c50b500d82c200b2001060003054080b52040204403840d056440d0b60700460a43c94200001008404010030080c010540b20b404101e00740c00002d01c81c0c641c0b540c014814003a6880f42c60042101c00d071100100388011001010000d00c0040c11146141061000340c0030700340c10381100407090400c1c0c0ca241d004504000051440882c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 118586429 1250 118585179 118585189
    0x4030c050a1a161203090b070e030d03020a0c050d0509010801170304031211010e0c0a0503030c0c04020a05070503070f02090a0209091b0c010e060a0e06190b0a120f170c030f07020d02 80
    0x480d0b64400140c11b20030b40c1030009441e50000c0908060204843e0011100d0790002000311078180720b0711300941e80315885501120302a000c444014000d20400e501451000d4000300036003214a003c0c0c0c1e4144450381d03a9040c00070600c4558640642c290010003040c40440c403c07075100591000e480c1080045241d40014580c01c442102c00044840d8015100d148102e29205204600a20045009504100c1e58040a0b625090316115052080da40000d100d02814011000c2e140c010350802c06503529005541801d040300c0c181c0e483c01700e20810003500010a540d0040c42951403d46010b004032100750b84003041e615102c0c0e0b0103214031950400501412503140300074020a0181034101010340030a007040c1c00c03442c098680744041e1400301d8000ea020403419904002d07207010b02d0f400f030384400f050301800030002c601000301982000f501000000015024031204110691100d07201d0310721010742d100340401c925000c0c001c101c00003906030401c000000d02c074180c000117055042e000416040700e0a520340c1c0010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 118587679 1250 118586429 118586453
    0x12070f020d1416080d0509120a08190f1106040f02010e0a030804050f0102030306010c150207080c010507020d050a02030702040b0a091b020c180414070f06030204030c050a1a16 77
    0x20260f10580404801d5100c0442e0300c3c0041c40c6000c020b0240440800d0040c000d40203d805c00c0340100c1c0d5045001d2a140d42c00c1003155200c135048991a13980342d14810468034207002e4403c0c1da4020030400c0c01c0304d1a0302440343c43c02e800c45c411504041c10b00b40d100e81d52a00b090388600c038020303810010028460384081e81c641c2c1c4404003c601c00c1c0031442d640c61030101800301e405100d84403141550018420814a40d0300290303582c1c65140d000303c6101c25101c218414800a0080443c0a44036000c049201580c00005620003400350340e90340c088501d0021503a41c1180e1034400e0183d25801600148501c100604040e00595040c00008103030344001a03c0304110004c03150305900100c103240c3d48001c0d0401441d018043d41c450b0000a82d51808881350544042d40c0f603200180c4020112422034540c00d03005171040c0403a2007d8070a414081302d0259132010001c019421502017512034070106000054189444003440040303a001412481c40400380062842260300032103590660041c643d0810800a1f07800c400d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 118588929 1250 118587679 118587713
    0xf0206010b0f36030105130503030c0706020706061202191a0a03091202070302010801091406010c020f10050c15010f030303180602070b0a0e0c09061009051203070506060312070f020d 80
    0x9264602d143e0400c041c2503c001034007650302d0b41c0294040ca40801c5c004070440c3d9000141c44103080d502d02207498604002d200b055400f500880c600400452031405a050b000d012134000c4903841c0407230804002020305204244509a4035203004510181c06000300d0340034040c010024200066038038510344940555100c001800001600254410300841da00f1135100e80c0500701450040140803841c13210b0100c5008007600040c1031260f011118005c550350303c400f004686101410414440216110250168000c44041c0c0428021025800d440c4100d200302d007070484250908503c2c44030b02e1500c2c150000c1010714510300003480c800c0e0325803001c00c1560000381080c0d031040d5940e00141c6460491401154150701110003113401c07060080f05c869071103007102504550112482055a6440354060360000c52a9000c5034010018015813800c900e0b01001402c5272a025006a50103039950008164036203e81640707124014a0920459002c1492610f0f1400b1803031000d07040b250000055101d82056110b40a10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 118590179 1250 118588929 118589017
    0x30303050c1225170f06040207050a03020d0f0e0307051003140f0105010f05030603030d0b0303090d06020705070f030c060309060b060403080714030906070605040c1a0a0f0206010b0f 80
    0x50902e104641c51074101e5400524000d2a29540404c2c20005020040d195401030f640d03003130204000c0e0341c40d6411110600e511008480c0c544203c4d24019444d8554204000e0114985020f0401131030302500c10b070001104000c000d811070b00d0601041082e00c0e04040700034010907a0b108800102c0701c0802500328061840c2040c1054190704d0400010003500301c100e2a501000740a01c20b000c0252000010b5440300501100080340c0100820003091460040030f5132141d1215010300a00207120040e4001c2018500030410340f47c54948413001020140030504c0028101000340ba02080440d1095105511103442644041102821400060556081900196241c080c0050801d0410403c000c80888490550b4091401c015411000030740740d00402102034002038a80c00000d0811001d0407500c005062442da4034205507800d0600b24000341c108071014004624880c1845840b02c3c00014494122003c04031103c0c5400020b001c2902e0582040c00039051140348004016103a222160a0000b040000c0030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 118591429 1250 118590179 118590211
    0x3070305031521100903170615031302040e010603111002010623041401180c0504120602031b03010b030408090d051002030a0605060c0703030813080d02030a14060a030303050c12 78
    0x20302d844c200001e400060586518150740100000d8210a1804001c0750b0102c0303169031640d5500100d9505903005441440625001082040e501210a81c00140e580292000c000000030326045c40d00303c1d1074a01000d0040d4a4444a4003220310302001e45402040b02c1c4d10002c81c1590b95007010410b684d10500c044c4140208000c4040e015040c580308449108451200d48140f55152038003500c2c0d50010940d0890105403105540c50085001d44105c070b0080c540c800110b5135410603400c22000942090b2101080c0000001c1c4c5800b00c1541d4600380c0e41a01c1343c0700d4640b071641d200d980c3d0780b07001a48540d20442e00848107007041c1002c070380c05002c1042c0f004401280969686041141841100c81a03080300d0b2003003406205040640340001510011b580d85401c0649840c0c070ba00000d54042c906001c0f00a0075003a001810f0b800c6900250041c1d40620b14040040c05614019030000f0402c1d001181c06d5a00300c01c8902003000801c1c82504199081071040da0300350b01c0c0281200071802501c00071030f0364212112000c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 118592679 1250 118591429 118591489
    0x3070209090a0b04080901020f06010902041508040308010e06130203090f010501090c080105090c120403020a030e0405070c02041d0a0f051509030a08060310060905071709030703050315 81
    0x10041588040781c1d101400070000b080c2d840b443c0609001e0030160440308086040d15881e4020042c1610707411000d000c4550350740e550003500010758000c0c003c880b85081da43c10f00b101214060250301d400799506031650751140c0e00f031141c8051401c500503c0030b68000340308180780d110301c082031000f180240000c4024200d0200c08481c001c6c20750b001a40301078005441e1021007034101e5070081c500b41c15240110742c01608ad40b240710030810240100100c0701c1012040406100400d074000420b102c40034460b031554902c8944100400c81101e9003201d6503c0804c000360101001482c00c3d40c0602558041849103a8001201030306440c0703007007481d80781200d2101050780048107102042115040c071400c0035141022a10b00718402d9501ea028408000c001e104684000c52117655050001c03c41c070360400311003007180540e03440c0c0300d8010b41010b55080d80400d441c1010030901c0d4004178116072080207114021807820215640498031584010450406c0880c02e1081c004160b60300001c101010030f4204815007421900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 118593929 1250 118592679 118592689
    0x11b02030a090e090a02091e07110f060609130311190506181207060e030a05030403030c030c09060c1106070c061704050c0108070c0b01090507021603080904090c080708030702 77
    0x55040680d007049101c08000140c0e10000d07a2005c810b606440e91019a00e4403140800417003c0ca072078040c1c03056400c608004a00c1d41c051044035480b41040212030608087d15900754640f481507a01c20742096a4200240b16070313043c48254900d00d8440d1034021170385200e29110328102217114404540c09600300460340e041c40782c108a041c1d08003103d5840a0000c0e00e03c0d40d4072a6440b60900381d50a05c1c0c00d0042120410b1040e80c0d4442ca0f014a02c4105480c0e85144a26009005500031a4200c0c046460010900d02c1c25119128150340f0311039035200c8003401400e01c62f040c0c1d40d04a01000c100c0c2c0d010131000c0842d070103860701c8018041c0584102500c0442c0c0c2e04050f40504540100426035004c6046282080003248001600d0140d81d0b00a092a0f4090385500c00d04441031001d90a02030701d05031340d5030000184509684d019074400e14980c0d00ba6034126441c80b401c034400340054032000c0c10317041003440007089c18501170b407180070818030402c0300c06602c84d620a10b890800d130280d807000c00580c10211b07101d003c0d8108 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 118595179 1250 118593929 118593947
    0x3030a06060212041e0b04030506040204050708130219080a0602071406040b340e041505030604080306010306120c0303080109060b071523041a0405060f09011b02030a 73
    0x1d00e00241100b40c4088030560302074002c1d4070034001c00600d41080c0c00b400110300d219440185c02480b1056a0340d0303459050031039854200784c0c0c1c1240101e1038040041c0b0607610881d010343c0078824032442902411216000c019500942c3d00f241c20061074452000900b11408110782200584690400750b100d500d00d0a19501c68003840c0941c41581c0c22820802c400a9124403106078071040082e0740e40341079032401c1001a40c07080708a41c003021318a0035402a00e60990455400074448008840c1405903007207445007010f001895124070382d056030000012800294514010b580e008406242c0001e1407541c034000840c0c3c10100d48002d8500304240203081c024540e1090040d0701600b0b0850061200070302d00040c002d4548100c0c403014044003a550150940320700c040c2c1155112011256140ba0310f00040f110405501c502035804403074400303240628650410700780c02c1d0b985c45180c0203000b40c040c0d03a64021040c001414000e01d070002c030303558036850449500010700c02d07403441802d141c6c000c640f16031041f503014040c812 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 118596429 1250 118595179 118595189
    0x7031b050901120807020a0603020715060605091c1e031202040f06080406060b0d020a0e0d020d021203040e0f0916051003020d020f0a032a0801060c0807120203030a06 73
    0x500610140880d88039081040d044803c54440482c0d6440c4a043c01c0d0301d640180da10082d4001001c20f8001003403a896009024480d0041300d01081c440c0c000205841128101d229a07000724a040c84414034510b001190183c100100784624200d81102d40c2d030305001d140c10f540f07950b8a0b90305000d4135802455403001d030512000c007003c04110b1420b81410b2410600581070311802041106441c005001c04c95290000d0006044e41c02e001900d8501094212000e9041009003c0000380350380c050003030300d150001c0c0c403441e00c0350041c255813402605602885180d04254a1901c1540b20410000960f55034440f80984200c04201d00501981450180182860340c101c0442d05c0e0b91200b00020b00681d81c9200c004238a09809040c0180c0d620b000705500b002034000c00086120f043c0000c500d0401854054010f01c004550070117080c51f880b4030403074484c040c100201c1c11810001e52840010320502d0b000310315812442d4064501e040c1008116543c030310380311404072181b40050b0404402d00141c11042c0c007400c0301500e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 118597679 1250 118596429 118596473
    0x809070501021c0e10030f2009060f0f07030909050609090615040b19062a020d060b0301090c050a060507030509090a0b090708060109210201080c0d06080703 69
    0xe00c0d0500003552403558002107004500d035107014422460041c02e1080300c072200a0050300103506810000780084c078110a4042d029070030540901c0d4518190302d260407800744800c00d00e6091548000600000d6080030040d13030b880c2e0108000541c4046184005010a144665280030985050044180070b48002038070b01400b0b03444a0003408004200031410303d50000088405103000759584d00042c010703090f00b0051075042070b4a84040b078201c0c18681c0d2020266584d94940340541c030f240d07551202c2c200002109042540f020340380705c0c01c01442e2000307140d0789503800343c0d201084c50103d0f840041d085461600d02240c070a005850100500c0c2082240c0600810450901d9418400b55442c040d01501c14110558808d1045c04c3c001500354119502c08a054007000c0c007a040a45450000901101401e40b10b15000c43c4480e4000902840d0b40a0f00401d14440c0342644000a00c0340e030700660740b56501400d6203008442c20300c0003207801c0e0642d1040c50002c040c80c50092942c0c038914203058601d0341410400f03182c50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 118598929 1250 118597679 118597693
    0x1b0a020310060302040b0f0d14011b02100507050a1407030306031707030207060206070203071115031911040302060409050a140903040608090606090f0703291f1d04060305070b0a0809 80
    0x40d40e05c5541100b02142c0010703100c000491400d03527490041010500c065203d09102c1d1000040660020307407800c500740180c00070401500c07400c009076128000c2030881320001c0d07035084000040e00902400b1340354191190401040e03041c0c13070740d46070b41910b0340c040764041c070449001c40e02c4014103a0400c405401042140013174451410000c0d4025101d1041c000b000e0004150000b0002d00782d01d48c01001c1040c0c0e01004480ba840381030070303181c94560300d00b10398802d403103641046078100440d8102422503086990040c401843c0c0f13482d01c0008405088014484c05d00d0603aa5039110141100c142c041a01c0746848102031a0b03503500b0a40d025101c1d0364082c0c210034181e401a000c2100e182c4031400b025811000410074141650780317440045010b054640f05165904030450000d8613141c0c041340d0755140b6103608641d126001001c006104c8608140000307450006110821104294611100070030003130f00003d8004610741d44c032a00c899241503816402120411800920301c4e01e115400720110350070811007030107081c0d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 118600179 1250 118598929 118598959
    0x7080601090f051302130c020c100f080c040b070b0916060f091d0705030c0c3a0e1e060301030804030b0117120307200c241b0a020310060302040b 64
    0x10b03d0141b4407643c0e011958410344103880a008100d2903c4102000344400300342c0742c2d0740c00014500c040280d1400c0124001c500450341055a440964058542c0c070460f0900300105034640d811040e0000d051042d0500034002280d504140304201c880c054a511707141c1d040c00b07400300a0018030300600d40e445542d41c0701e0720b10003034141d640782d646000b90444042c1c0380c8a07840703403180b150b105203a21421b00182c10030300c80c0229040f00b440241c0c009a20403500085d0400083c0030103480030340048850100e09000944030301f4a8126440c01c0381900381c040d107038030000c401c0c0709801401040f079680c821303001514603c00102e01041000014aa454098612880554200400440b8a41c0d0303800d446260102182004070009402074800d00003230711080740100e4404100c2d554a03a04036216204e600720940180041400076001c0c0006001c80518402c0c0b103c009450a244c0610944a11152038182c0005001e10580000940d8003004070040d0801b2011001403160302e1441000210307101085440e0103030100c1014100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 118601429 1250 118600179 118600189
    0x10605010c080705070b031905010e060f0d030915030608010e0c0306040303180204020723010e1b0d051c020106090504030c15060b0a03020c0723011107080601090f051302 75
    0x1c4110b5124030815182d240c030b031816500b05a0304e5041180c0000c2c01208000c0907406803040c10700c8074101450200610f0b41c860006d0502d007081162880e4018021b0036114116060191001c55104c0c002d180c590161600d4401d86030000a002c0100c2001079240d4005102d0580c00b031082c501d00d0181d22004000d40d0307440302d01181c0c945130003d2010307041c5955001600d01c6500079a441c06a41540100115500c10003454000c20180b149030343c9800c0c1d004a518080c680440510503100203440b103800822540b40d1202c2a40400d1b250441c0362a04001c000d42e4040c001041000340c180d03000301e04100e82104000c2c03080002d00311240d030f501000c0c15a080c1030038003004c20f801001c2040f5190300030030b41207940c200795505940501000d074041656000c00064200741c2540c1603020302032100c550f4060ba19410341d5482d5600582000e2080130709500804504484150700481455000c1c02d6081d066606c1c40e80e0f0740030110304040c400d911903204c040d160069205040c40911072140c1c4080d080b80d07108218201a00454 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 118602679 1250 118601429 118601447
    0x91b0a0806010e070509030a060203041208010b0f090f030102030403030c17040b0c0703030e0a110a05060301050306010b09011209030203090112022b060f0f09060e0103050d0f0e0d06140901060501 86
    0x40750f880080d20128044500c51400c40c1d10840c000341c01c036120b60100d031031b182c00254000c541c15502840c6403030061509603c108071281c100c0d403110590900b441c90240c44103c1540c010281e0941c0f200c1000d4180003140c800303001030351050b40a610005822207004034060000300f000710b581d081c14802d101c04c110000391800c04658200148106090300e401c40d13464150000d1109615294a9119003110741c2c041002400800070890800c0e075005a03000c0e41d990520116020038040c055142c0c011600600c4160700e03c002170000307450145042c0e00c100e03c1c00c4200d203003124a40070007940140c00005c0c58100315600300754059400c08079064210318010006030050200c00512000c203410020319003045c1000c2800e50002009008508100c10009550780d40404035461242300d42c2c000c88e070802800103035502000c0c0c002c0d03040325000340251041d820f908400710780c1200b0300c042e2841030000c10034070341d1000d45402c00d03a180440d100d0031000800b03507010304e115010000014a541500d0b81803290034000d590f071100742a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 118603929 1250 118602679 118602689
    0x607030903171b01051f0e0105130209090a0204080c090f06100201150f0f080102040e07050f16030203120a0605241204030c0b07030b011409040e0105091b0a080601 72
    0x2078a90380c040c403400242c148a0711188540400000450011010065010703501030300c51010321800c104104040004071030503a200d520302c1d000242c0010005400c000c410f070104035030020710061a120030000061311a98066403500003072a804581407252010800000341d1504e400c030340351452840c00074101d07408e122004249500850340b280710314608900035088a8035481c0c51164882d459902c41020b8023240c1203e100c1d810386110144000150740a061007240c0130781ba190303d8000c14031ba0340d070f48003a9020350024108588515081080d504480103102a00c0c00d40383c440d5000e95035811010b801c050784a0790141410821b240380040c1088584c2d40c0c903441c4507103040c0141c081d40c98050b41d035204940f9030050714684040c0700300840c2004100350388405649101c501c500c0d00c044c800d4459800440c00c90310000c0b08280451400341019010b480080080c104140004101080c504c0f0341840443c01d41b0001d840c8580380d80c1c00514805440311142c0440f15410b4003d80c0c009404600d022503940d0390b04018810 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 118605179 1250 118603929 118603943
    0x11d0402060d090606080d140304050606010c05070504020d050f0619090b03012306010f0203040b1e191107060e06161a040c150507050a061112040b0103020108060607030903 76
    0x3028520b150550040c4031103a4000404120155450f0034140e1102c040984900024a051485403994002c0d6002e82e80542e801400801d0907940b080010b6035580794105081c2c4444c82044d50000312035845000034414508040800314043c10007100e20501c0e020048c02940c4203016141c50b4100d003400c5441e1007409c440e80380f8004640820305d88c011a004160025152402109129616803139000703920990340211020b990320006105900c0c4100d0310780c0640e000d000801c540812020300c40106460000300301d032142d184111301c1e218441c84010311101100b0752500110700c3c008656a00803c0910015008200e01d0408030030345000100010703013600c01c6000e0030004403180d4120000b400350311000d00740c41d51030301d081852960415041c4411b980312035118002c04150b101d0010008075102d2016070b0305485d840301c0204140021075441720701500300d111030000064000e1080508a40c9204001c602035801040a42895411400010a4072200a000741d0154004000100000350b000140e202181d4001103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 118606429 1250 118605179 118605187
    0x1704110d021c0818042912010e1c0f021f23040203070906050102030405130905030705060610090e06010c050f10020904050702010b01090b030709090e1614010207090f02131d011d040206 81
    0x6201c005070754010f40010341c03270007445410003500002d140042d50000c4d081c1e1010042d14640c100c5038807a55a400100503040200d481606560802801500058004021608445190310b032458503501d00c000540100c214000c5c4825801c00740081c0016009a04051000c141000e0000c0e40e24452481458010341220036508c02204a540c030140001e54000c043d00d03511241400c01980e0344005075075442c07142c030400c4101019107020b0700702c3d1811641da19081c3c07480c5a0b94900152400c011101054526018150f001032075134070141324144680c0200b1200589411a80d821300045400083c9841c041d603241001d000da0682c1c01c1a0080119400c0c05c0d50780e03589554801d4101c5800086030320003282982040c0d500308281c000451401054502e42000341d506550390721804400d52840a00c0c1c41c050380015501b4001c504c0c464000300040c1410203c0580341c42010109e074a502035059000901544103a080401e030769502541d00c500426456407500b441c0c5521a031642c06110016000a00c1000001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 118607679 1250 118606429 118606511
    0x110f1303050d050d06050906010f11013e0a200309090f0103150504080a030e0a081902100501080c01030504051e0d1704110d021c081804 60
    0x1402000185600009a40d528440d590029116400c0b00003030200e0f0303e0074060b010a0f103092130035a092060005948200b291000380e4000e54561040700512600c0b5503c0f079020141c600d14501d8054004245c2c21640943c0c011000400350b8262940b42e20910440c808000030311031244c0c00904401195182d8030b03844200d40c50712002d030749180b0440e0015500440b02008008008810b601d83c1812203005c0c240d40f4040400340a0703c0340880c1d50441d001001500144000c8250b10702c41e42c40071410340c0c944004c9404030b0035192103040494000c5151103944070b05040d4000c02c41a41440164500c2d813880b54184000d5051205498452100c500390b613040640d10360004040c000100034500c41e9030726a0306e100586038075201d400c0ba190030f01c40f80c940010600e515000a0f07440c402c1145a4071480e002070314070300f0500ca541c1c2000070558001303806a91254041c440701d030b40d583d1024001d20200c8c0c8601d4003159103089980100c04911050b51502d03200b28a412449020f0f0400d1207840061482d8403096180c00c1e40001d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 118608929 1250 118607679 118607707
    0x30d140705060c07061107050d0e04020d060801020306040606091208130b1b0714090a0509120a030b0a060509031c110102070606050906041b03020c0a14010c09050103110f 75
    0x2000007900c94882c081c24452121102d500401e0b1321402582c0500000f414500002018401c4482c000d12a512401045803070512a006880400b0f200a202514240391100341c003040d00d03015001040340d65800818040903103031600c034071310007480142850713074100d803501d42d85a0414180c50005402c2e43c00c0042c0400400346548541c10240c40045241a15a05026452000311181400c40c1c4071920401d940496a804144100c10300e52100a10091700c230f644a20b20400905130103001c500240c85010507400c8000c00c144042c3c002401300f5603000510b00044020040200000c2d40308100b448001c010041c51038501048000c11541c02d110004045c4100340422149489011140d8015520110301c80080011030b400c1003040755022911410107490341001c110403251400700700c0f1418807403d050010078134040d8001d0324015600704140d0754003200588980c0804070032400400306c030b6550b609000d5500c0743c001c500c0d04080d02d0b0a282c03c0244640c1e00c05103014034030501d80c0e65084d1a10118810b1406480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 118610179 1250 118608929 118608937
    0x3060f1c0609061b021e03090310020c030408070e09060601030603031704050c06031305010b0f01020a0f030507150b09090c062d070501050601110f06010504050705130f06020f060105030d14 83
    0x90103624803804c0c0e040100007901c810251900d60928059021001007a801c0081034402250000b000361501c1c2020f900c40703030001e50025151004c103000c2030000041464007840307110001c0400c06c6008949203000d19016081600042129042c1842c02d44180082076200392a0302400d40d81e58000c240076280c170705141d4600300c2105245035004400104201c00501203110002035544030300000d00c4042e4036181000f076103401ca4080c9600580c0000710306c1002c41d1400018049090090030030230f103071440988071200042d0000c2c244178151625410740301e03424103200c83c1950744102c0d094054220b14045000044092140b80e03101c0d0010751a0b0494112840c00c1c20400d90208115807260326a0760040f403a125001e0720048406034040b45040c00f1924010314042458550780a000e40581040c0e07007000f040200a1a000d0304003003c1002c00c2c03091b076200483c25400340010300100c02220000301d103070180c003d10f032181c1e10340104603542050004000306c0c1c4000400480e041014108040c1030703419900c5015460003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 118611429 1250 118610179 118610201
    0xa0305130c03030e010f020f150414030307050403020a0806040c050909010b030303040c05040507051c200c0115120b15060c0a060606090b03070f0305042603060f1c060906 75
    0x1841c08400403c0580041100c40101c2082e02ca00c582c0f9590305900340c1c1c94080c00c0100900c1900480340c944840d070701d9070700080c0d0321520400c600303040071600114092450b003046a000d804110005410300030741c6000707032a080c0205030060007400113140c5660b400d2031480c100e00c84e4600480128000c81d080c281e0a40002000c10400303001c6a80341d19007400e00390110441c51140a00403840c107004120b0640c4a903044038030868081c2e100e2044c0400c21500580100a200c28921080f490100401842c031030726401001f4131010301c2c002003909900e01d1750142c25160568840f1803640010503441c00040c034900d0f0304650280c41600b24101414a45021421901c1019000c401c20300840c0803600810815510107002d0b01ca442e61a858565140e4819500500c0140d900700c2c0800e0148400201e6503200b43c0180c0c0d03000344a6000b44000c070000d503401356007032455180100c582e07400c00310401c84a82040e0002140042d01110041c000304a2042da0b040c24404080c0e0281449454100c004240041074101c904010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 118612679 1250 118611429 118611443
    0x90301090803041e03050a0809120a080f0601020c01020c0402070f0b04080a12050705090f0f042d0b06070b1003150f0510080c1306080d020a020a080607050a030513 72
    0x110914040c0500d502c00c5504548100c0c0602245042d50100c4128444455054403100d1400340b01103019540d45000901c1d0390303414030a0940d03070030045440e000a0324194011303844840c40c5040003034444492160080c552411580055050940c070307030f03000a0842c0349800136600169200040d0805540400340c6030340240600c0c0411060108000b100002001c01805030703615001d03d00052150402641c00965944001070701c207103c0e0000b18507049950744a1b07440c00030502c8100401203c00706003a1581c690043d50101001d6950081c80ca404d840e200304c000c1003000313042120714600000521640100f5101901c06101c00e00018009000118031102070750f040021080f1140b80030851001900c0b01540c1201e0f054102008203280000c0103040c10261440fa002a103140d5942c03109000e08030112a407001c8280d905d8100c0080c03100d5041c4047d44100c0e0007075026141051450050000c00c40301ca9210074031503404102002810344d4001c0c1911214005441c001c906074650341110720842c1c4000002803e0341c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 118613929 1250 118612679 118612691
    0x3090d031b030e10170a0e0312070306050a0b0c06010303080603100908042303060c0d0f020705010506090c0c030405060d021c0c09080a020f06070201030e0703050c2121090301 77
    0x2c5600014000d0094104540040c007840e10141c04075800404600605814144074000c0b0b0035045094016080001404044a040408016020a1501040d81c00c0c0740441d644050610690610071140e00c0a00303500650949031080e80d94083c0c2d0740310310510003d000c0041080110b0794544d0180600b180754402c69400307200514540c2002c071542e5100c2d00c9410346446039800140400b8020360160540407000401400841d5203181f05440c0584c040d0710b6005402c0e40d100d01081c8940c1c40c0d840640786a50240300002620310b0594184525650040c141c10300881d024040b8100c0044000203c40c141c4a00340c52494071407603044201c5010340a2808640a01010240c012080641d11f9206103001f00d01560f403801c5407543e5203621620350401b5140650052404400e410706420040001e2031030701e2062400141c15903000c44c2090600c02a43c00446a5030043c1c4c900303040514040104c208090742101540e545a21040314803507984241140710f00f590000d0001054020f502001034903a1080060300038800c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 118615179 1250 118613929 118613933
    0x1a0f070f14030c0114060102100c03060b04080105040210050702030703060b0102031c02030928060902190f03050111030f010e060117070504051e01080121080a0c1203050903090d031b 80
    0x583d0040304000565601e003e001142a040b51a02c503401000180c024001e80c802804241014080071030780d51040c140c4581000401c0304021000b800242001e00000585090901c10401140c85104800c1c0c1000800d102170805654080307040b030f0884e079000c000000c8030003807400140e0450033601040c4010b00301000399280c0d0702c0b809400a500c07501540040d64484c15090201c4800c1b0201c1c2d001c004107034544c4403070f0383c1c1c0010070fa07600251015000600540c21000d8284062011520303641000901048542e03040040003400d01400c00d4280c01040100d081d8a0302d00e40c5110000700511078005a503003101c01003140e0381d0007081e9102540081d5070941c03900380b4001d20050199403062160b60701030000d111142550031452003d120110fa4169244240d90b46051800f814201c0181822130400d1140c503044000140710500401c0d80ba20349450306d21000c510fa01b460b070391700c181c20886041454240000c00c031030324001204541c000701045507403202d82c1001703050488550b6580d40845080001da03544ca030301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 118616429 1250 118615179 118615183
    0x30b03060c030f07021203150616030203040f090b0306131a0405160807140d0c0803030a060f050301200a1817061012020d020d0602030403090801061a0f070f14 70
    0x44141c8280d8241d0265480b508002c80e600d807886810705801081c11f001143c80c07140b8124403d583d181c00185001e0528100842d00900f030051001d088000d40e000103800c10055a03a40007201c000c241d9104108240d202400c0403a84607100148181c0c0c8c10481c000c1060304000c500d0080390b5061b0070204888a50380741c1880c3c2642c0c1c4a810880820312807012034000285000002000700980e0030244004008a06410a0002c4c1c240503031800c40d10f06500c1d030f4011030302d4441040070310302c10015114042840c0d40740c0b9403040b100c250b8581040c0c0c00b80e4141110001500307500845d030340c850700d040050a5582c81126108036201c00c1301c4448034800090311072000440a945c0e00300000c80c044420141d4411741c8030394a15a042010394400c881400684414a070094908028007201250001c4d103c0700340703812560384240c1241d000300c80440c04250f10784000c0c450b0420910890025001200000a121040c08026040c4e030103815070015030f1440005402d400c10800c4009522b0042e4041c22203400c101101039296 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 118617679 1250 118616429 118616431
    0xf0d060e0c0a09030b1012050709050a0603030804020d1b08010f0b1c0b06010306090c030510060f02100908040b160b150a0506181002010b010314040819030b03060c03 73
    0x42180c8240001c1244030005034110740c40030240e030b11a882e070343d0715603503840031000801000c10807205e4010800040d40c14608007540e00c00c5108030042c0014608014070300084030301c0907011f084d8943c81c1140074400039401c00311107500107070101c07403084468059103480e00072824800581616042403600000f103910054110068074a0310748402e010ba000841c0c1800808a280c8000c44001715588110001044000900940220041c0740100d902600c1c1c01c00e410586000d160210300080d0758500300b01104060b13289c41e00240c83c0a181c0b0b05d5824403c003a00a6407030003d0000020640e69504c040e8040013620301c115402002e109020a40f548500e000e003454680c058902510303080791010010b00c203840040d007001d0345040000c054040540c01c0070b0a1000c5a084802c020b200c1c0001c03640e411241d43d881440802d5000080c0c1e00210303402d1411000141964600b0507501c8a5141903014000003800900a031b645407041010014921923900c001200035180c1c80c4141c03a0036000710001e1007140c1d140a0015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 118618929 1250 118617679 118617689
    0x220e012306090405120c1504030f020d020d020d0302161b0501141207050c010e011103010503010c090807050d1502030c03100522051518070201141003060b01050f0d06 73
    0x11421039030301c0c50180000100111002803981d08203c404d50186004c0c68050030b0000c48250403105107900c4003100a040c3c000950301a03010450862106541c0c1d40c0c1041420403081c0c80e480a414a00382100019590f07a86030300ba042d06058001c248080180c10424145171019041440a10340700000280031110203554012180015a101c40b145000c0c80505c4c02c403610008004241c8440b0303641e02000311019005204854001d549840c6c000b034891009000e8080b2100c2d480b150300366130b549408109421103c8828100092004040d4200426180860f866088032001e0340d80f0711012009150241d00803c0031140d40e6409803021040c0710f84072441e48041c40c401d44520b002e0004054a54081002c2650300104580d61420000d118001e031100c1500b1a40d080105082410851415100002c0805c40d601988950b0072072071004014050381c1c240940803410066a109180c2c9041510a0384048a080d002c09030015496007072030b02442e4800c1003110310310071400c0780c2240c035901e88082100181c13809204c0c3d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 118620179 1250 118618929 118618991
    0x405090a051e0f0a051507030b0d031e020d08010308071406010f0f0603020306031e07090c0c060b0f0102060a090c05040e0a0303060506030705090f06040510020601030b011202220e01 80
    0x9441080303c00016014a440e4122008040204015001c0a48244010b14542c109520303408005c507591510460b0041407440382e12080324004884000c84507007800e0903151003c5500801e6031081d01034202d100c1700d0561f504402c549a48802e84c1c01c0c0309108408824079910b2074420b43d0b000044001e030b60691132090315408407200fa601aa20381e4224103900080d201c10341e1540042c0d07106600302c070400d41c072081406ca102c410740d440d06580f84c0e210b004440c0901c24003008101c400d5000001c001e4688900400550126220115241c0c3e0310b0000395500d00041034603500580d240c0000041c0309030395441400070113009105101302c05100407055114000024201d0100f410801c0c049031500c6c0c16410340b0311034102503a03100e05100c11001045842c001004580e030b0407030010800404c4540307510b130600701460319980040c402c65145152113800181d0507440301081040d00d070b0341000142e403007440119006819610f01e10308103042e490300000a29000600200541ca420100c9031640d1890105440050160320 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 118621429 1250 118620179 118620193
    0x160e090601090603080409021b010e0309090108160b0a0e0a03080c010c020d121a040f020702030d0c031409120a03180501030b180c070b101410080103020405090a051e 73
    0x402e8006807002404020724050b014403003800400781c030798080c0000301545c8030402038814260444900f1905180c2c402d0346542c000080710081400c00c504008d0043c030f0000024500c01d00e400c43c10713482801560203421458000001c00c801814440c0d4407013041c2000c01800714a942c0c3d503900d0841013540c0200103180e0a5400c29160004140c00030845040c24155919860202084c01c0d2900700141090041101103407442545a00039480700d128502032461001401a40c0d105180105840d00f00035003104c10400980800c1c107400680d11036586e009000440c0c000725151500940000d4480243c80c90490301486401c20304000d1551080c8000f5003040084081d01c521134644004500b81c038003800d052a048501090303080b10030850700440b1540601d00d58102818489c51381d0b5695000d08041d034a0100c2d002100005000d405070070300402004103800c030781c02ea040880c03002c0081c008400500c8080c2c41240d54a00107104c0c9030042c40f5844620358814240d03410412074501a507001c01d04024010a03d1203401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 118622679 1250 118621429 118621439
    0x9050c070506041101020a0b0a020c0c120309011b080319050115270e01150206010504140a0504060608150a060e040201091703090d0308040203010b0a050a030305070203160e090601 79
    0x31a4103868108001c0d1140f40d6880d00c0e0800c0d02c00c0e844403028118800c03d0800c00206104001140c046c020051015940380344410700c244c608448507508900c84c4104103240c2940401c00001c46031105028203042020005100c51200340003414000540030080001c100f09001d441c101005650b061042020406640c940070041141c80d019142c0d90045402c0641e40b800304c0702d4254400c211490300c01007206040703854542e80100c0c140f00380c1c0001d07583c038003070303004404410740610401b4050401500e04116444c4903941014501001400b40d181c015911404034042c0101c2c2d421480207030030110205d40f207100d80403c804128a000b00c0e0141910792034440b010801c4165080c245003e590140d503002159802c0c0203002540c030030746c0c2c0308050161100300101006c0d03854805040d50040e01940f6001c0c0103240600605080d24880b1040502c241803044060019560383d000c6c0c00250780c3c1502e8041d480b002c8500c0840d00d06a1424107507810f110348824001804490186550300c40d42d50740c0107540d07060b41d0300c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 118623929 1250 118622679 118622701
    0x4020a0e010f03080c03090312030f070e0f01050901020109200a05030a050a080325030516080c0415120908030907060503040f02040e03130905060f060403020f150c07060201060905 79
    0x81c042c440c06040e41e6901000812841c80c098800c8110075000e603881d0800f540000391400e02c0100310184442c0c2e002c02005170105208901036444070603402c20b10340036250100010200f0703050b20b60450500101090b003144e0ba91003584949083c55018810242c520303030380344a00340c02551140c0607501c11041c1c0ba4004c540c904011900c030000a5202c001841000c8a95031250301542000b0704940340b6107103214031041c00004006c0c18a44850058800140501308044004000c81814600c07205001115050000c001001000c4600711800440380151400c00440200e81c6078110304000d03601242801c2040d014490510001e600039690f40307085940c4076071380d0b10050302c1500040b50090130b031610080341c01001d800c00f41c0041c0c00f8a0000819240f0f021040d4041d0009201a904421109540c520801041d810003208480104034100c46490425180d540028884204090703410b000303021014050b900344245000703440030070018405541c2c0c402d40b6048024000c210500c11440c080c0d040801140d6440f1003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 118625179 1250 118623929 118623931
    0xc010b06090d0b0415090f150b090117010f020d0e0705010207030818010c0209040308070e01171801060314032718180d021e070b0d0506030c06030405010504020a0e 72
    0xc05002d01d00d2080711034a8100c091a0001d100740d030464400369201c00b1050342c5105d60b292052050000c913003130a1503402d00801c5444400441c4480c0c074a8100c00e10079660b0760604460460b90240303c0756600c0c010f43c407a40d60150418407490601d40e80003203000e00c01390040b900488103060180f01203401640c0d980f001260348488134031010f07000e02e504003c0710070030321a03c0b14440034100040c1090301a00c24198085902c00c08120790980c0020403240501c02501d030310210140d1908400d1804a40142c000c0b004800030034805800030103620720801a4400d0420203401410003103820600c54041000f06d00c203c2a10b9621282e2a008683c80d504214000c2c66840021184040d501800401c0d012410300c0389902003000240c26000600c514040c0b0340c06010341007081030344200d129406401104079010000450b007100b40c1701e8035400c5d0440c0005008082c990010740c0c006041036000490162916004a400c0c00401c44049030000300c004204410301005400060186109503a00c1440d06d1b994241d0f103609a0f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 118626429 1250 118625179 118625197
    0x120f0516080a170307350a02030a0b01090501020c040b0a0b160303060618050d030e0604150806100c0b041b06210b0a0b09011b030818010b0f010c1a07050c010b06 71
    0x80c4065030541c600b804500e0b0082150346c01001d600d01d0842c412007860b60b19003206c00d41030140d000020450703c0300c2c9500610314006020b08020484c40d003040000307512034904201d007a00480c0d64140741500d607030b10804580d0060152407a1560b803003130400c40d0700049200c007400a8001c0303810808001001403003510300180c0465025a10410103050401300704090040c801c041d420400301603c0301d1030710340e105002030005200200c0e44031404810110080e2001000502d5148140032b000080c09006070088003408079546d00c001c41e81c4044d5900e10704042074440340540c415420102c0c840100d10140c001010007144a8041012243e56807490f01c04c42c10349020b0300c026604440000c50400c2a41c039400f025010b00c2c1c00505001e280e45040009c405040e090300441940000e4940b814000b03003d0b1071900d003000c1d01104d14002e01c03c14140101180c8114040c800c05810400010340231003d1003101c0c404000301e44c0b01c1d10441602c03400c001d500281f590300003000b264015407074650040900e10f0104100c41c0c00344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 118627679 1250 118626429 118626437
    0x31406040209102603090a080304140a1404020304170304030203040509180d05030a090818100518090a020f1201031101170109050c120708010e0f01120f0516080a170307 74
    0x3591344c42c905503403132040c100d46012622050169011640c0d64000da1070140c10030354011030f02c40e0320f040c001c00514480004024001e0035941400c0c48a100d074520410324403d41590003503920303280e616001740344d180c201c02d50740d507580b07004420301c070400d98080000d1007201c00c00c0b20b10300d007162201c54a5060026042c0300c03a00700c99024000034004940030b14069079003c1c00034040000c1d850065168a42c2691191200105001d8480310300c40d007a14100001d00075151f007a00c1c115040000303c00511107031780c3c52081c10030311a2443d070000480b601081d03011141320744407400d07944c0c3e200c440c19105c80c80038a00a0000b01c0340050300c11241207913948980084411030b01c0c800b4030344000da440d099120000f05130260080c00403000c2044440c01d00440343d0f14040c020700581c1e0382d080c4150b1600f441038541c500086d00340f0880100c0030004106240e902e10841044503000546055202c6013840e10915060a900c0b401208107001d0701d000502d1900807452601c440d00a0390001c0e007802201e10005141d12007150070001007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 118628929 1250 118627679 118627709
    0x5042303100e03160201030e0f01060305300c030d061203020601050402130302041802041b0905180f15030d051b06130f171602040e01060305210403140604020910 71
    0x4900e41007013074000b150040c1400160f02200c080745070305091400000d00002d80d1106820002c1180410200b00c1c05030900d40804040c04680742c54404c44030302d100b4201c28081010420000420701401101e48040d90f240c010020b25560300c0d4070b03654a90101c08207a0140c01040d0000030f0794140b43c0200c81480f4102e11008400728103540c00c0200070550603030b0894643c406c80c0d074201c00580701d912505030508156403284c03464040d5040e000380400400e8000302c2c018220240b08c0f00c00805003039001d43c1c011071a80442c4002e681c0b000706000704292200403d540c588030354140105103e41003c010302d643c403c240000c28500300c51462155680d40c040e00c40072030304001d2501e0480410301403540072650741d03c40e9000c1106200c1300441814242c1012400050001d0451a0101149081d00c030341c1044000e00002070240f1842d588485440d101d81030703810301c3c200082050805218221f402202d0285510003070140ca80920030690315600c0700c0494040380204400004544d0110480c002d807000c0b03440c030940301104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 118630179 1250 118628929 118628947
    0xc030f09050105220e0916120804230301060608011e05030706030513050a0b060a0909052806020711090117030d020904061d040606061106010b0a05042303100e03 71
    0x203401e1481c0c114120021340c2d5070003c548285a1a4000e004000281c01064865001c03034000701b00f10307071170b80c000012091100901400a2003410907141110310103c05101c0d101c2c005213002401504040b80309902d0752900c0b0004c00c0703294001d58441c0c1038412143c8005c1804281c0034509015514501480b81e04d80d1082108004441c802d401060384120a50000c0020303c50560b00c407483e00040201c00c941c03003207100041258600344090044010030350b0b0314080c01120070f2038a506407106103c0c20308114140c42000c031440e2034800c507888228141d50080c011503480d501420180200440c40c82918800c0001100014044581410485c00d0f0455000610310700101440904000e43c400302010b84c1043e103c00002542c811004000300c001c01d0f00304c154846910702864480d084801980005060094084010400c010b002520340e055070742c24101c0c680d413460b15000a42c0e00b406103622800b0601444c0c0809281c40d400500c00003090602902100c1081404081174000d6811454003003065a1061043c024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 118631429 1250 118630179 118630207
    0x6070c0809040f02040e040503072f0f0a0f1707150f1803080408060f0708100303050c010f021b010c051c0203150406060c1406090715020f0307030c030f09050105 71
    0x2801c40c1d03c1c14005141c41d41ea079140715410b0808460a07280c03034202080541c00d1108050900b90715514881007412008050b6601c610824160608240030b01040f4294522544505032482c028222144008500713903503d40380a41c00008440c602d142c0303402840c1e00000d40808550030001501181d840e40d841c1b001951004803446051190750100c0c000c8a40000004a103019005101605804025002c640340441e6006032010000c1e1004e000c00801a0402c0a82c4801041c143d007500e80c0351505c0c036581c02101a14901410101c854004480e00c0054074010780300713484d941ca000b21043e01009010000c4006400c0e40d0ba40542e280403d0386004105044071f040205034011503004070200e045681c08102500401c04032070302c9400c641e01203a4582200c0301030011074120300d0390040c0c0b0031004005a18040110640311b84042c8281c000c44d105094000b00c2c0c150080c020080e02d800e150341100d458421600340100000288c40040c0c02007209074828008561156070603509461040c3c40f11071034028508040783c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 118632679 1250 118631429 118631441
    0x20c10021c030612060209280b0c120a02010c0f090612050408070f030203090f04061409041e0f0605090102030f0c0f07051006081203150d020a051305010806070c080904 74
    0x1401c1503a143e60200f400680c8100e1005920b024550060b100c00062061103102d002041c0d4214038a04504101001d04294008080c2a1070b581259a0349607c07450790202e19002d0080e00c080e0a07010003082d0f4503215a4158490a00d020709030740c0b820310261451070b0580700c12965005100000d129003401d00d42c0c10629801030394000c3d1040d03405030f00c1c120550b203500c006c5039850802100181c200140d800c81d5803a10500c1ca00d20302204031003c008140c80d040110503040d40f0810703000e0240c43d80c0c0d00020207020700c0c400008900c600200c540c0304000340ca45060b12030307101d84940072a0884d2404c40412015101407098174802e2000c5002600c080d110f9500749030f11078011211414a403135007040000c00190040c0400c41c030b071080702c0402041b403e04000956050213a40c514020180b8020320400c0100300c404c0d201001079000a94940c90000c44600101c0e03803900f46500100d03044048102e8040c4504003652245040381d943c2d0042d140749854003407040300c030500762100140c170401c1e0601c005440c904d0554420303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 118633929 1250 118632679 118632733
    0x605060a1b11060c0d02061008150a061212030c08040f0f2102030d060504020c03070303110d020c150105032410050415030b1f030605070c051c020c1002 67
    0x5440d4015040000302c07075501c92400d0088175000160708450a640400c040d41d04400c0d003c803803152440c140030013a5520007080c020748604450303080108142800590207100581562099000e1004036030808400880135040a030000a142c04144107046101d048002d000380e034400740ca0900b10f810b036195a0700001900c20309440c21001d21070556440f030202503944102d09a550042c5407528419031015080703801c075134401c034040d6004001c2d4050341e030030120484007400d0380342c2400140c00410350070700c15160040c2d401e0681c042d480005c49400780c80c1e002492301d20b6282894012030040c2c0c1ca0307070241922440340b040c81072031a4041c00e810707801d1307246010102c585c130a4400ca41c0c1d41103180c5d2030001900381c4021108010384000d808500f4400d119000d940b45601042c50a4410200880100f00c00450740b07080c0f002072b0803255514041380540f84101d002e0303059150801e048a102c00810301d01001000c806100480c0035103c0c00c4066820b038100010311612440c4203030003030040304142e01e40d0007030500418646 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 118635179 1250 118633929 118633943
    0x141e041404022502210f070504020c0c12011104061d030708030405040c020307050d0504080618060105060d0f050a0506040f062102032e0b0d02151e03090d02010605060a1b 75
    0x140d1741c1545281240c1031824484030f006004118180c0d1000d03051010640100c0d000c2c038010000a03008001c0003d1950203001d0136071703558210520040c0c42c18010300c2035880f0380d6040d4100180010314a60b100c141e0600c0fa0030040d41500d40b0407440c2c0101340d9201054401d219003a042440208404d03d0640d1000503400c0b401d0040d40e1510b038866032000d0401c2000040c01c00440e90104045c010362100b0008207502003220b240350325526803100040c40d5100014030909214040000f1402084852600321010b04280d10f90140114180b403614440602011240140982e00c4e011007041e401c062800717608100e4190b04000b400420440c041400e140e4254941a6018410107112415000c00c01e481c1d100c6440505c58201e00e17010f0020200300980380898071140c881c504049484015070b4903104042107800754500000da51302000550f0080c160941b0317110b242012004000c01901840102d181034040e40c0590080050701d4a40c010041680185031810f00010421451407114010716804d4a24050045036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 118636429 1250 118635179 118635199
    0x8070305060402090a0f03121701050d02040f050a0e0f0a110405041b0801091a090c01030905010e0307050f060c03012103020106050618030115060f141e041404022502 73
    0x40805c1d43e00035164000050780149603c2041840b1003e40c40c6060780030546098841018841110b04120304180141c41c4240521140201195215403141040d4a45a1000c4c4240d25004252000804490070021113500a43c0410181c201000c18402106648000c0031200c1800c0442840003c01000f0030440c1d90301c0200021482110b52001100010300c194030001c1414403203490850300350851341c400e403e81d98450300f00b88941c005c0042450000c014081c6400941501c0c10306046000d0180031444101c20b000004201040c0000400d1170706140e81c8150844140c0d8550074241001d62000740300307400921892480070303202842d081c06003403401c50081c80040740b480d440e070000441e15400a40c0c50740502202c0c20041302c0a0600780550300340d04071103c41d08811245402d8014000e8104c5c42c401108025000c0528a0079111700400c1d241c8000c107411080380d105034842c5403104182c0c450f00824408910506030120145070074001c890300d2075200c02c511084400c61061068003520031007800c13a48050000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 118637679 1250 118636429 118636447
    0x2070b09040f02040b0414030102030606030a0c09090e0309010305220f060b03010204140f04091106160803070804030801150504030b06010203070f080d060b19080403021615080105010f08070305060402 88
    0x100282001d400ea000815131b0350b503e0000f14001c500814080c0501a034014000c010186c0e47c1c1c0b0041d268407074148500421410241c0c68101c2d1100e0701070304200d01c403900e8100c50041c060000006083e4011083e2000c11054030703580340c100c6102c070101014501c2d561200e40789100180b0000034600c41c00e44189030228202d00b80b400084d09a8006401184581140003440344151500c0214000c01a6040d030701002080101d458071986440d0001d4610b00848000400d1410501c803220300c01c010fa504502d16131707141d0401c0c410040409009031026400030fa42000081541c1001603041d10a00354581c442c603290928556031000c100c00300402032130540c00113010300d10104a00000700c2c0003a81c07040940c41e03a101403142c81c1c00106c3d007a6030442c902c490014849181c0c80320602c5981417a1840c0c4e07003061101c0d550f6929040b468036a0a10807442d0a2039084000145c502002c803101404502a40342d41d0390682e210307001100c00350240004a0f0000c1c00b507001240300580030740d0029420485c080c202526052044c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 118638929 1250 118637679 118637681
    0x11070e010e04060b060703090b0306130908070605010501090605030613021b0715030c05040b09030a021003020d0c0807170703110c06010504180803042a06030b03060108060702070b09040f 82
    0x26440600c403200790104010030003400e0302c200f0314039002c1181d6240c240341103628018111809030180d004164400408a143e07540e0302128030445100090f0184010b80440c0b03004c0006402c01c8000311112070525001041e19070180c00d43c42c05442541d9034440c15590f80004010010b13980340c07103603540d07c0e03400c0114100504030301440c3c501420000c401000d4491600e24148038072080c81c00c00c1410146058120703400c0e943c1c450200c41c1100c8c1040c02d225281c500d8400043d041020500000394018070050700c0c0c4142542540281080207c03018040080e40c2c2041d006070b80300b0300100ea41d040021107030010081808900b04a898100f03109103000941c0ea8004a24a039055100c01442880e44d03102031300400040ca0030f80103408000c111003c14956074000b80ea101d0502c5d01025000904c03200018007040340441481d11000301d140031181d9825001a6107010240041400c0c80c90180603009090000c1481500042d08600405d2203900500e03816290101c510003a801141c56964016100c0b91000907070515 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 118640179 1250 118638929 118638931
    0x1207051c0204091e02012a0303110c03030124020309090601050304030e0603010b1806040503030a050703030b130902010e030d08061224060102060109060b09010e12010903090519080c0111070e 84
    0x48a4200345581d0400e00000d01f000d40e9401076005d124608848022900400d00c850340440c1e039250801050b4210101c2e0445c00074060400f028582d44404030002444405030b80720f05000c04141d00901081c0b52042000302d84071701c14910311719001103419005c80d005500c204c00965000d4000d10b808400585400300040d83c580c400e0f4811a0075900214100038000d4041e1102603052400302d80740d5140c076161001003501c90040345141c0c1c0501030003051306014940a50007a000036080103280804c40d1070b200c0d01c134900030320031542c0a070700040c1811031103000d9050003d98501002659242c0005540e1241c0402103880c4030000c4491036800f03111500120200b20054181c000741406010714003c0c0760640009107400c0050340240c88042c100881000341c90042c0d01212650242860500c1c080041040410b2128640486080d074541c40d02c9949010301d030740840c2a1095840448052280e1034107019100c04490b110f001d40d42a17500300200070846503000c2c0ca0500010901c4c4800e40b8401681c4008200c500d10b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 118641429 1250 118640179 118640213
    0x6030803090f071a070c0807060f0e03010b18130b090a050607020a0b0403030203070c150605040b12031903150608150603010608070804080903010207030504051207051c020409 77
    0xa404801d01003500c07000c1c84548504004000240007403441c1c14400741d042002e50103c442034030000034842c07003400740e0a010038010f44500000c03105401d555190007000341c400281500c001030500f114400c0e007481c040c01007401d030701c0b401403200d500c2c0c00000c41c041681c074602400c620b034042e6203014618000b414080c1d690380b0400440014020508250030003a007000e000520000440d041034803c80700040702c0424041c0c10542600e001a1a179441503000d40707045200d4040680303a8034580d4401c4000b90160b410a03816074006450601c40c02c2c402c1c2c03050180b00c0361490403844c0c09810500118280319802d04482404070700514010545a825405119008007660441000942001c081080d00340248642071a41d8800f1b44981f8515890228020419a0060301c3e21080141c0140803030300307000b65941a42c2c4580d000034000c56917030005140180c059031152140782e00035552543c074001c0258000ca4800100c4401070700f810000070f204c00100401d07610550040380d005aa03448294081103111907100d001403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 118642679 1250 118641429 118641443
    0x50907140c0a061b142709090105042a060503040c050603040828090509060102120a020c0307120f150905030a0302040905060a05030c0609030106090f0501060f0c02090408160203010603 81
    0x461350300c440d4100540c190310b0101400305414002910b400d100080b40c00383c042c0441241c0010403143e2061260780c801e014416403081c040c3c420b10044010640c017030b0b40110311500014250920504001c000c041032406000c6050001500c02c0207164007580c02144c1c41031068660a6036141c6170304c001406030700155415a80142c0c0400d80d0065450301c2c0325044046002a0001481c80403101001040c00ca02c48c01031901078105074010407100d900070415602810004808180c0300d8a55110084d076541c06489254443d00c10782400040088110088200d160b4218420b80c0505107a078840314515007620000c0340c046e50340d03110881d000c101c06101401070007600795400740c0c0d124680b24041040c3e80e0040d00084c45040c080d60104a036030b600045411030840706079800394540b98440c00003401007080380e0000011a08107080000c0740710440d80124140c03203554a45107000d00d0200d80803a0104840113000750428014808600030403094000342c02e242035188500e00300c0c1002c65000c282501c001e0f070f108490038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 118643929 1250 118642679 118642691
    0x9080c030a02070f0801020310090903020309031c020c060306240c1f060603050603060a11070b130b10030309120204020c03070b0109050c0c0703020f0409050d0c0204050a06050907140c0a06 83
    0x403890001d031071310007451410029415818900c4400100c5038040c4140001182e8550f41d1808040c0248144c501c880350040544001c3c084054014290380894003841006010317800c0301c1d448600d4900c060324007a080240000300a4080c4540e41e00014100f5820812800f4003440500d10164040224241c10300721403000240c0c60703420038101c8050341c4580e045242494204010004d441d10300062059009140500c0443c8215100c00101d400c0c0c410503402604031a5054100322040b02070003019104c15201b2140b00600c0d0b989c07914407001c00c07221800000c0c0040c0800404012000e40f044003c0280f0340001c03c0107280a40c001c01003850b41e440300c00e04948209001780100700f036007400e1080b55400031051401600d00100140003076220704850200034410031110014000a40380c41e440444040d50100403109a00c1d0380090181035a450040100d01c62420900021540951800b5800803180042e0024190b5210464161200d07842034040c00c40707090080c0181c1124020400540400500640d000288 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 118645179 1250 118643929 118643939
    0x306020a030501060c0812070e0a090509060a0e0a06090c0f03120f02010209010e09041e030c060c02010204051c261b06070905060f0c0304060f0f0c02010203090409080c030a0207 78
    0x2902e0703059220005000c400d001590119100404585201c0300c010010a10f5965120055a0803000c1c6d5055a41049000c4800300300d44c505940014060751003201150301e1542c070502c030013054074424402c40000d81c000910003000280b85400403440244140b40c04d804003078950000c0711400c107a41e4010380b240c809414102170b00c00d0b0809102d0601e4034162000303524266251002902d40030003039000e94001e44030a00020148800c121110040d12036a02c520711404c009814020b01d40c21084400380c2c0da0b1443d0018400c0b03024014402c6504503840030f4910288403c016002d0f107000c2e00c181c403050741c00920038000c920b24101c0c2001d03c6071a140d895100c258542e800c4511a02851441a10243c40399012001f4400d005800515840440300202c40855444402d00c80002280c09220f8246070244004100440c5003600019a01512562503507001c0c020784811204442c0d007940248041c5c0503801c1001414601e0400b40c204201c41070040000303902e4122005000346c2703141c1c07080c02c40400680100b042404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 118646429 1250 118645179 118645181
    0x403020a02090f01090b0a0e16020a05010905010606090b16080a12060f060f02060907140a0b0a050301060e04021218070816080f0d0f0e0a120b10090c020a020f040e03040306020a03 79
    0x403401d0b050300d40781c03100d6040c036410940400d0049c048002c241d050181040b9498800c0160101043d4400000e02420445241039406000342d40540000308170003840100342c804d42d407426219103c00c8074240c0d98440e08592602c100b9503110344403c4d0100901841400c94401c0c0d14081d2030700802080141103500391506100600c04014025880119000340303045c40094100000d150007a202070f041d40e0500410f2a03000513072a40c060354442ca011200100300c60700711541000c09141200d00036110b900c41c4d4281c460411089100d80e2010454a540d03074404500c102c0d00688440b09040b420b20211190262102001440c0500640f00c03030500c0da00450b0184040744042c000000b038201c4203c010a01e02011410152404204010020401500d0a00b480441e500d003084607005050f84d004205000e801810a204100d8080344e401350070840c00d25001990030703024407881243e086280e010344078044c2640d00304002ca00440007007540c03198030785100f0710b907214040c1700600041d481440d00590320b40115102038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 118647679 1250 118646429 118646441
    0x905070c020603060f061b0105060f2b0822080c060a1b0302010914010b03070803030c0d020903070906120b06010c0f24020c0a031b0f0b0403020a02090f0109 69
    0x4000c034040c15003006845190569400c032000700d4840c582e060841c000314105000321180d824029001040b046007440044d803045000300307030594140fa1245918000e022601001c0c0940c04040c020812030001000625030411629a04c910004c0386400c4160805c1e061381042c40da480c8940404481c03042000300000c21118500081c1910641d05104076034002034901b03443c07003c4a01c80703100c10300600750401d4800e5001071003041d800084070400c1e26540d000b150080000d0a40140a4461070070b01090a40b0000190381c8611140300e00b862800c441c841d0f00d81c0c0079401805030390750144034074507010400d00c0e41401004068a100481040144000d080c200342c80380c409800207042c00180c0e0000e20109500c1904102e106030800090000d0560003d142da020303d81c600c2e401842140b021443e145846804101c0744942402903030b43c2c4003401d0034100030460002480307800030451b4042240c00340c0042c1c024a0190382c400d0290058405441c0e094001c90541c1d1421070314a058a15030324010310035810184100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 118648929 1250 118647679 118647691
    0xc03191e0513020d030c17040e0f090f06011e0e0108060417040e04120e0307030c05210601051203040b0a0504090e0303041a060301090f06050406060e10031b0e09070905 74
    0x2c884070002540100c1c601c203410407000790030000f031a1036090a000d505d034580040c40914103407107592550b60715480030003203400382d60801c083c011001c00f244541c0c4d00056501036501d505c0d8060a6075900c0c1003640c100d285070082071005540310b40640003a81e14803c0701c4403402090300c6005011145003038941201c140c10f85c003100700d506000c10720081c4000c510403004150700641c8003407284407400560030140c941e041c1010700716a0605c1030301c00100401c1f500f0b0600208442c415280d1a80c51460038400b0000001c103584860300550103040100117628010086000a05c071201c00e591400340c0b01c00c0c003001386900c044400e10121b000018204240565442405c911140d00d4014505500300b5a1f90f158031703020002d0420300c50003164408101569000e40c444000b00e50301002281c10300e40c00f0f1074500060481110256945031502c900021200000c0000901c00c800725640c01032400e042d0b6861903510142500d1151120413103400125214403071600a90242c6c41220082c18050300c0c1102c160240c842c000c080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 118650179 1250 118648929 118648951
    0x4050c0405011706010302060d0f0c12050a09170a0c210912150902120a06050f06010c0506010605070804120807110a2912040308220206030c03191e05 66
    0x1111514400126100717055a90440342d0a5a81114200d2030025107005134240c0c645616000a002c1c01640004100783e4500c4190400c1c0020750310b03454128104c5070340c040003602d04a8005074001d0f49442800090000712100e040542c0405507a03151b10b0701402080340289800341021000b0b00e1881e82000b401d1004215a68840101c2c881554804018009a40103402c51031b84030f03200301c030031940d5604000e010715020f44c0403242018030078100710303015107002d40e1404007140c0c407140412295480b98049031003c030341003c01849a0703447e1403c201c0f40d03940081d0082d900e010043c4400303d15900308030b46140310075000b92005c17038035426582082240e03403050755910b611074090400c040141050844600f6002c00600844c640c8844200d480307000e0b544100500303030b94502024001c101c1055041076809014001c00d120f501c010082c400080c00043e91880d901952000050000031812201200115403110341d10084100d40706126040074151f803003440070341d01c0107006000d152240001911a20340d0025042c1d107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 118651429 1250 118650179 118650209
    0x30e0409030e040b030109020405070215060603070225030609030818010506030c1908011d0d090b030412030e07060f112d07030804030b010929040b150304050c040501 73
    0x360242c5010040c81c10359004030340729291941c9540d0294400c0c03035036640180062142e40b4066100a44030045981c1c07000070312843d000031a010b400c0000641e8426444c58005080013154002e42d4000c101c10541c0d8281310300700d9284040001041c034019440420301c00d44400050742800308114210700c1082180510f0340e07251004119503598000380c1428040000c0d910341c1c0d126408a03102e07000030f03412074102080301d40c2003801c02140e8010120102c080080326409031020b81c004032504a60420b0303107204440d4030310360500105002c035100c0040c9400301c2010341030001d05401c0845c0700500703000503a0310010208044d40307103440d44030340c04c90740085244140001404503210060b0303810303a01c441820302a482c03021000064805000d01004824051030300941100d880700e580e46001d20b2035240c00d0103008a6a400c0160b015003148038020101d90119119414104c0e0009810034400181480b21005501c040868005015090103030011340c081e0b8020005032141c40d60210a11007551410303401440750b038503032007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 118652679 1250 118651429 118651433
    0x409020418090c15180806060a0b040f05040f0b031506030d020a020604170f0604120207050607030507022b060207060b030609030307080907030c1404060b0f090105160507080604030e0409 82
    0x2c80203000e60328440b03440c1601c204015400c44404141c00044e410100300c070413000c06c2503d000100c2c103108000c2110808601d603100d000c010b4450040b481040c03000c1c80d61140600091405402c0030090a900c504001184501400003d14107612104618a040c01d038400b40807141c00c040c0602d41091415000424844005a000c50b085208520500c2311040511641160b5000203210402c00555031104590040c00c5c1814048214a130780d0140601500c11000001007508102c000d4540c00e43e05501c4003400c003030440c0c0a020001e840e00004403080d10780d4069040b81c094501807900049800350500680340c0d00310385444022607013880d07407461180d4000740801c20344c5907000040300d500616a1030912542d4440118640c40c01d54240c1000b40040d81c03150300468034429a9040501c2110102ca05104140daa0043c19031030348106012034501d41000c212504243d40a00d0080a4200c80f04000a1a41c111a1110360624245030058455508514180014141e00100580d050349045a00b00204441a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 118653929 1250 118652679 118652693
    0xc11031207080c0f120406180e15041118090903040b032229060a06020c040c02160b0c10050f07140d0905100606140d05100803040902041809 62
    0x1501004002c0000000c201e0a55036081c4000ca110001c02e00031600c04032040d55440c54039422500450000a000d0040c6803524501c1d5480da1048a484905408050316a0403144088442c090768031900b06440f603820014603400d001c0201444c802010912160a085030100000114080c000749100d5009001c240300700100402140d420004c1980340501c610b80c464180441d4504001002d0b0500103e40ca06000807804001d8403045900c0145003142c03140c5c0c440c8108031065241d4090200181d010039552061810280d0180c05444800e00441d9401d500d581c420003420300d031581100c010407001068104403500c003000060380300358518500b4040c501c1c1100400c00c4e81100201044204203010f910301c0414480601102d0340042d07081004e014007607040c1010303a55900040c84502034903240c2800007a8a910030b002000342d5420b03a034041d07841d14500110b480094400a070400850311640350001030144801c10040004010607240543c469150400c0c076540c0e00e2050140305020b50405075080001020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 118655179 1250 118653929 118653937
    0x100b041a010503130c080604060b01030c0c060c022805061003030503150411031608130f0602030c0c07120302070e09060403030507021f06030b010501140f0306010315060c110312 78
    0x10070701c0c0194503a6941348a441a06441440280185005100c0401e86540200b20f8622541c081e4200f88141c2e50164011002c403188034440c0c4002810071f03074800d03000a00c02e070440000d80d007461040324841c103034903018004220b1104000001000610214104122003400944d0340010510b04083c0780700d1958502610b94400207142e8866001c5514101400d030b41c86501002c004070507449142e890b4074000003182003911070205500042640c407000600070883c0007921401c49603001007038403916241c40e51507601a400181204003200414001c4050711902040b0b41001840621324954940e900340c00c0180c1403120380e4000034a007200c1e907010041004800224142c1243c0e0507e0001030f940c1d40c0300c008a003803006405100c500014a102c0c028003140250300b2032000d59020300342c0340d0800c2e681d4400540700c0c11158111854204814820080c10b01303041c102959100c00c041c1004104407a2410368002c1000d40303a0000e41c081905a440101441940f42648101c01001e50040079010003542000c862801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 118656429 1250 118655179 118655231
    0x3090411190e0108150301060b12041b12020f15070507090b041a010f0e1905040e0a0f0221031218010b090a09060f050c041e15080a1b02100b04 63
    0x2040c05c001d150f0b9403800d5000000806100382810344a00c80460040b2840c1426281552542c0d00708420b81510703004286030104075104003180380c4000001d5030074404681981c180c2d8581c01000380c20b000c030803828140002d00d05140b0840c054001c00741031210400c210b0380110021805a894600c000c0c0d602030401d20400031001c42401c2440c8a0903d41d80100c44414064071020b4000382c0b20a201181000001e0807103007580c50485090101c0e0b080c81f10007503581d0031070301e10241440200120800c09400c10040c0a042101b0406041c4100141e44010034074607030000c500b504902212008003d421148a101c010016240c64000d101da4285a03000411208020b40780d1988070b1303035980b0440200820b5500506000810300c0c0309202c0c905d4081c030440125003091040c01c4008800d00c08000b00a2100005002501e02010428210071080ca2003220a994000e11808159a81e2007100070800d88012072284140000e5000f442500e801c0d607221010348440304a5640240c0c1400040c4c66403241c1c5901c100c0040e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 118657679 1250 118656429 118656451
    0x14090f0d050c010b030d0f0e0607020604030b060102070902030903070209090a021302310306051b0d0504140114040c080d090e070c170d0b06091003050903090411190e0108 75
    0x1040d100540750050858a8206034144034a4506e42d80c483e030000400d030faa0070420384034461403003800c02c14414184221000298811410001400091400d4082e9500581c0c180304a03494a81c80780b404004076401602c1c0055950300218843e0708516107441c080d079004000d00041c1c503c810481d40440c17000c03864030324144107441c0c02182c1c11f0700c4484440464003110410b03403178056159051110000b000304050006403030103810400001d00c104402c40090b116a49080b030064980584c0d00140c01c0140000f0700201e606160100088889085c00d004004a154140e06030305501d007460b240c108a000d01c1540114001c3d000221159a1a0f0304002e80300c08490785640c040c40c0903610000102e9000c12601c20007044030b98055806c00d41440f00201814410301801010070000b03d08208008040c080d000b44290301c8500680442c102038402d030003d0760041001c004030f034180858071000800783c4100040c40a594100452441e6046641601002c00d1100350704210720080010750008202c0d04000f04054227030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 118658929 1250 118657679 118657687
    0x60504020f010905101d10090305010e0604030c110d060f02120f070504050f12010507050307020c1504032012010b01080f01080a02010503091005010b0901171012110d030314090f0d05 80
    0x50740450300110300c1800045c107402c7d405400d000041c0c00311207a40420b0b601c644c80c00c0107008a18200040030f41c01103416803111001d4000c3e03a521490300780441103a083e040840d8160fa01c2c0000c6903070140c0c00c14580c454601580722030014401d8100804001d0503000e8040300c0038103110a250b001001c48007969030545002201009a07000324840d15040d01400006610741010400000d0740000170350b0190090ba400d4507030b8459500100902c04903408050184054104420000240701c2c01032000c40398074462000d064a203003040003826100c0302c0c24400e24a80d440e80059001580d02003c21640045040410569541000c4038a50f9658295800074144103000000c503512031070800c030180d290b0310340d9601448590f8454500300256004143e106000c20f03d08501410302c4000100001d10564214450440c0f0528105102c10280005441610b00b42c03405004510320792a2012a4440c1e01d00a840c082555004e41c40b800101010041003c802c907001041616180a408580d44071071000502c0e1164032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 118660179 1250 118658929 118658957
    0xd0807050d1a12010e070f230d050109030e010906091206020a0216061e0309120806010c05060c0a180e070f0e0409030f110312010302100504050d060504020f01090510 73
    0x2691052146450b031241c0154020043c007001500724400e0850b03084255803040b561404c0d0fa0382068400c1c01000c003182d8003114402d140489501c248100361b0401840440102c049449041c21120120740c190005500201a2122540c1040c1c000000705103078500700c00d0749498035122440b030100f0301d4401048641c0009602c440c05108200c02c40b02e540309105020082a500e010203070520b00780c1003c56809031800003844c90b82c58020305ca000d08040e01b01d100880001e601d0ba00480b00f1003001040541406508100c0d0000b0401c20080365106190000c003283c1e8440c1e05001c081d2510b448442141c00c1c4111045c014804401d0310501a500590030342000c6880c2d400195046d82c00b2114512855000340c07610320b1800c141507101c105000650102d0b00e81000b00d201c0c0070400c0380c90348260044081c50711911401000103041541c02c401410100349419800d00b80c8030b4002031502040e1520688007151564248001d514007450408040002401c0000c4200e103070134003040b41d10043c03d06110a11a18445241c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 118661429 1250 118660179 118660211
    0x60906070b13020a0807030302010f0525210e01050a0209030d0e01030b060f0d0c0503070e090a020706050c0a0905060403020a050108040f0212010e190c120c080607050403050d0807050d 81
    0xb41c1690081a0324026900c5035159550707170a451006800540c207242540e00b040c105072244c507004a440b030745800c03821610000300804410f005100c0e04204a40380307112181c0310728585180300e45039404020200d030b80065100d4003400c0d81c0d4098801850140b04000300802039800050b00c3e05c000c902401e040038003802000040c2c00505580000340d03044140051105071901040e4000d010305c1800c03610400c42d149120b10111513500003110781d40046440c4a01c4202136203061407000e40e01460780c10001d440d0103070075503a000640728195030b444580000800e0208416030402900000740405541d25801d1600e142c0001d040b400c0a4450304d0f06000350f040c04242400505030703020030803d40103440c103000d5032000c00446008040c941402d820034010450342c90f44040d0b50320350b05042140c100c8441400e550808180f8105044c08003030445150026640c001140001401060310810550302d17260b442d0b62035810010300708100c08410008021000f4100310361031360040c06845040d2010400080c01c41601c4100b06 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 118662679 1250 118661429 118661461
    0x1704030503070f05010c11070b0d0b031605010f021209210a050607180e0a0e0f15010303110d1e050c0a0605090d09150503070c0210110606060906070b 66
    0x16200780000105507003400640202c081c02a4130503002000b60400801084400c8641494285406e411020080201404240203041c01030307800c620000740c4d4a03200d000a4500f81c0882c3d601e4010340c01ca40400c00c410360700004030054068450015002c10747e03204500b105c8074402c5002c5180f00d11140c6064440b0030111404074007194406508448010314181045235540304100d84a00001c1c401c0602d500c05a801240c082c41140e03244603c0040680352000040e002c2c0c20310706a40042e40c0310728003041c1103c06040000807004c0c0300e808400461541036040003424030002c046109110390002c20300203015079100400004118000b200481240f0450004071101e128000320030f40c4621882c1c00c00d00a009465000c1d82c00382502e84200d4460711503500c02641d20032607511450020a560142104015001d00c00460348016540380240340d11002d40d00103524441c2c540d80100c005411411440540d40d400c0142c650400f9080f5032203800d002d00140003a000d8814a00010401da840c480072518074850a43d1038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 118663929 1250 118662679 118662683
    0x31c0c0f0f05061f030201050304080d1416020c06040806150102071509080d09050d031116060302070c0e15120f010608100f110f0315031009060e030c0a170403 70
    0x10039592071150510594401c025518030030100440c010340c005043c50030030340c00112503041c1c40ea5421035440c1d46410803030b03411140ea10340916840d56041d054a0250904c00e41c03203a459441c00c11050302c04d401009162014601e9900e0180390104130500258000240195102d0015040109900d64000040b810408158800d50000c1b19154140442c0c5800002400554288500b12203003903080da030003200d0002c1e251003400d03082f1000b0040940401e100d0b03071502c0d0400780c2050450b070b100c000d144650a00c0c0b16255202c0e20000394049075440403c0941051000104454241c00c10182496140710039418402c00c0818801c41c0000043d11030011305011404c146c082d02c0307000700480d0b0b03030350000f198842c0003058482c904249480c4040703d100701c0ba40300b484500440d0b2103103e41014411040b0f0180b80e4070241400533032490450550811380d0f4104280240402e5080001c2030050048c5800000e1791401919129290402d00c52522080000030b05131244039004010200078180002c003640b5903105503040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 118665179 1250 118663929 118663943
    0x20d03031e060303081b040b1308030301031a09010519090c05041103060312041406070203010f0504060e0f060f0402010305070c12180503012009040605040e010f0506031c0c0f 77
    0xc000d560150035400030044034060b8a0b17000c1c480d680c01d015041c1d40107400c0450308207454244000e00a402c03a1001070001c4140c11000e0307008450302c6400c4d8030f1035a00268401c80c0d0f44200030340860130319809032020640081511000380207508048844e8001400d80d8200d050780710b41d640d00702c00240091031f0340034402400090010482c4c000402c106107499881200e80e40e00038070402a0b03460b0680386400403902110601d07200e00b8104071a00e001c01c0b000c1d5100003002da0341592250a0041c002405204841c000d52190300001035900c0709052030f5003454119454041681c10600c00c01907011600701240740d100b6424a40001c9580c0c400100342d0311603094580c080c1940c29107110700c12019807c000e105101c06011904851304540d0745040609980385603000e0300ca00c2d18071a0503410303200003480c05001d80400c0140081090f0740c0b504046400c0719480e20030025a0f03074407109880c0700441d10f40320341c940250069000d044a00700e802c58000d0340030710f2898041c04100c0c40503205800d21100c2c8051400203584891 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 118666429 1250 118665179 118665221
    0xf08030702150a1704141501060801050603070c080a0c05010f1e090606030b090a0308180307060f29130501030f08070204140703050f0601020d023007080d06050603060d020d0303 78
    0x2e01c4952080c0d42c502d91b0304103225200c4040c40f04812190054100d03501c44d80c176034800740c2c00e000c11f00c80d80c1e4101405000a008050300b07070400091005014000324042951448440245401d04509440013040f4031112039140000380b8100002c0d015402c1402810518003080700c10315460500c006003000d900241c080c0e0000c1d002c4c40030041d0041010212540280d0b14191103448200e07840010031800c03201c130403103640304002c1e030400907686402070010360b604083d000418030301141094440303505064848400c400d8010300c00c031440c904510401d030400c1c80e803c8104425170459072040a0000c1d002400340003204c0204010045503074030f820111001d01007030303440215400e1488025000c1c000c1901c1c00303c101c08400b030020f0681d502c005503e03c1401001e80c020210740c3c00e041d82d05060b0080e16000f80420402c1d0320654981c01401500038544c05100c0c0004955131f602c1d112100003100e01c99004a0f200780300400502c0a2a560041c4506c01c00c0d404403210103119441b8038056004041c0d221217003d08094901c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 118667679 1250 118666429 118666433
    0xa02060705060a0b090f0703091a1003301103090d060605030606030a080a0509040917120a0b0105090103050601020c0414090d03090b01090b0d0b040c0f08030702150a1704 75
    0xc212180070300100c0805002d0250345100b04a484001200e034110450350940001e00b43d1f602c240c02c03804503a0300684059040d5900c025184030f003408125078201a480c07080508004002e000802e0f51540c200f4524406009114a84402c401d010401c0d000c0c0100010380640c03d40034201401101d600b140000e2013000450340d00e1170480c0140c40c0e20f2150900c41e001da0000625039080c08075102880c103911240f01840e0140d501c0c01900c2a4014002c0700760070030fa98192520008200755104000100310a40789522307011024074250707401d83c00815440c0d889090a481018690708103050324000398003400e010600e40d464200407460800307400d440d80c1c0c0c01400d04080300400d4059400c1030303004450030170a072460650304845c00e6091790b00c202c400418000d10000100281c1003141d00002c4007600081001c1c01d55a480c0c0c445c910071101c02d44007943c241103103410801170380c0c08a803c2d1100a16040f800343d07060211540002307030318454850700c8029a07070b0005009020f40340708180248500d0070200740b21025042038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 118668929 1250 118667679 118667683
    0x140a0801030201200d050d02040b1803070f15030534081308030c07020402040305120c2b0806060409020f07020a06050702030604031d1003090201091509170a02060705 73
    0x207200a07804100d05000041c45005200131003081d001c484401010301400002003100d555001302030480c0c5165080c080462003080c40c40003441415a4001f01c5020310301c61200b01400c101c2c1d0f0f03a0102140c2c0d1203154003004542480c0000f0b00c0b04e0304c128100054940d44101d501c80340685400005003040101c00b201846900050400b03c000f82c000340e40c1d08078256100a0303101030112400c0d0001d04450024000101c08605240c000c1014a101410140c2400e59a0f5201031809103e280f500c4032400c800304400c0514842088003110091403502026a00308200e00200c08003141e001141c070822080c00f001400c640c4407442204d00500d240c240440d07460110f06a41003054104000481c0b040c1e092a00014100344188240d03050550010007904035030b00d070b42d0b60a489020514403034101c81c0740c00344104c41c1e06035102807000b50092401e843c00701d420031881c4001400c4010030b40100ba10b507001181c000c03a00c1603100f440003041d9880d41403036a90301460f1008282c506241c0490007503010718002100d038200440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 118670179 1250 118668929 118668931
    0xd090b090f0105071b02400e03030402010c0609170409020a020106150905060309160b07031e02031602010905060708040e01090603151d06010801051801021303020f01140a08 76
    0x400da008101c50b4444010840b5005009002d00d4504a8603178458405403600c50001c55043e1444400c900700307003540042e1001042c40c8501614441c040b1b81082032100c1c1c00d640100541c580400002c0e516503d040e50000c1c205e2401c000010302030f503994501020030822504c040508540030840b0350ba4545995100b50000795100d8080034005509004000404c8a081031034110690425212007a1450400085c0602500000e06c0c2d69100d1080c0280250081c1da14509600500a01c598441e51050317103044c06420a1940131010f4104a403a81249840c940e01005030341e1110380746992281100324500049943d00415009554031640004045080004000c001d01c00c4400d440c502100c02e0780d1314400e003400c03140c1c1c511002c0d00c0320402107946524000c982d441320825050400b20b03109024610004145032000903002110b1300da5507181484102c1500c807442c07c85615606009516000035040c0d0383d500c1c11010b200c002c0c0500c1c0c00544124040c2c2c06201100307076804a1604290f203841210f0401024003038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 118671429 1250 118670179 118670203
    0x306150f03060c09040203040c150e010305160806060a090302031203040b06030303040804140d081804051317090d080a02070f17031605010e070807030204060905070903080d090b09 79
    0x1180203400e03a403504011401070310440a5001c003c2c2042422801e00001e03510007401182d00841e09807022603000314000045d121a4000e41d5100e050600801c000350444401402c11050450041c1020100603885000d1951000f81612202c3c1c90b060869001d46a2604940000b54036020365154005a40803c00c05140308900440c014a00c684450703091540b00e100940703015104400800080c026503102c01b9041c60544005004050111030580718450140c01c21400c0d60041e03100c080800a80345031900415070006801c80d401a800841540c4000e10f5410244080051000c041842e04403581c455100c00c0348190480a4507582d12203100c0000d4652082d40520701c00d40e9030481d004104001c90303d210840010084004600c0e100e08250309140a6a02c620120707032640d00c842c5603c61000c0309024410082820900829411b42144100019035810350000c045047c43c00e0200503005911a400c0c0c01280e8100c1c0040e56a64071b007400703e078003500c00701030040d2440030340740e080c0015844001134501c881c031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 118672679 1250 118671429 118671439
    0x9271506090f0c050f030708100e09100f020315010804020f0a0b0417010b0604030615180606091202061204030c06020406080411041b1202041e030c080319030509010b030615 76
    0x1015841d001d603070901a005c4d20450745d80050000900d0b05009904481e0061748101d110007440303965003220800c0130400c950850032070300079a0400711b48001d1030241002c5202503560070b5040d0b2801720100d020038003900d00c0085c10054090701050540d1560360410308161000750152103001c3c0c84500625141d84284a81141c4200304028030540309410b1080741c100c403400500c407600d0946941c0341e000c040d001c14003508646054607840003650311041303660300314607102c80600408c6240c0380c440090400441903000e004052003034142c0b0310041e500c807400c075214204010011403403a00c079418212080644544010445480014003245458006c424140305d10301c200301c100401d4a6003418403084d1411941619600c844104134a004180038a0110f014580d0252005060a13900d0702007220000201e1092100514440740500c240300c981040b00f00600301d110015480c1140007031200001c00b1503025818100f541d0365010805402e0290081c8ac5a400c00804440c1c880c00e00911500c46803606030160352090b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 118673929 1250 118672679 118672691
    0x905030d090311060c03090409050c010215040b010312021f050a0506040b0d06020901110102040e0403020712030203030a09030905030604110108090a020603040221151009271506090f 80
    0x9140304110070426070703501002c118140f00750101801032a400412116000340000d12900a00380c94500c103101d50039000e54001c0241c010010000383c1000184040084102c03046420003020806100c20141182d900144111910417028400c03070800e00441303030402c0c04441c0d0001e94110210203401c8107004080d8040208600e40714102000100c8010200c80f03600101503101502c046201ca81c0070303000c1440181000000c0301c640c640c2030303822070740039400032914400f00900f0301c4203040d8108036203005000e0b040000704407a0f14548001c0e50f03074000100303428072a03600c1303c00c010100361180e61100005c0101800b15016410b0a05c4d000c1c80c0000e400f83e900d80001c40c0c02c40001c000c26000142d040d08540c01500c0c1d41d286450f20340a0040c171401c0c00e1000d0690b440d410b07001a05038075040000e8030341080c40d401981c0503401c001c01c40300641d5003254440b00000d810305142407844080503200c444030090701280708044ea24117182503409140307508241c00701c0524182c00010070f801150488100105042e07010495 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 118675179 1250 118673929 118673953
    0x6020a0e011d090403020c04060b120619031e0804080f0d03060609090504020a030b090307030305060d020109050108131202010f11040b0901050c070305060703020703080708091c180303090503 84
    0x121500c10341280c4200b40c080000c5150b9410014a0181c00502a00c185c41d05020711030041802e845465209402403000003440b110f415800810300f0341c120300100c070b10184e0700c80c80c15900305e03944606020282c80c025000c40c00308c2c00e0b510400c4079001103582c00b10700130b900d45948802e074503121101070065116900810b0501c84d0301c94460303c40e05054411039121010590304085001c0c005080080c4100d804c0388a811001c404244007000c0c0921560300b4500a61380d645080c0380003400c0d507034090115402800180c01a40c0181c0e0000e0340b101c262034003840e00810550700c4142035480109800d00142c88415900030081c00c8a5064005076204c40641901340302d149014a4104c0040c4030364800e2402c14082440541c11a61280008105800b00b441c1204e10940c4c4070b460f0b880c1032520941d401c401181d0700181100070580c0045200340d0108103403c0800d510b2030721121260329540c6080f05403135401901c0344101d031300c10300034001c45050403c2d1480c044e00301900c1c1d28010302070b003c1900520384a4840c00703030440c030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 118676429 1250 118675179 118675187
    0x31e0908060f0708070e01090b0901182705010305060105011b02090414150906010509040215040815090c010c0b090106030b10030b0c0319180618020405090705031c091206020a0e01 79
    0x46d508010382d00c111200c1c1c0b415800040a0708040d165a0401100c1c2000104294262b031843c0c0280c4600c1d454048040d2a4150b556150390000c0c4491a130282040010000716a0104005045402c00c0c02e00d0784440d8541d0300c000c0e0311108003601c020b5100c0d14400520092041450a0b80d1114004004480724400101d020340007500b000c480030b050ba640801c005115604004031344a81061028220190383e68400ca00410b244d00032f5045a4510b50100105503400d0b40403075107141d00030742044040c21180781d190000818000700008013508080c00d0030007061446a09503c14001141c01010110942c00c0074006c4141c4220360348001c1d90f1100b120b4000c20381c40b0000300c041b00e01407010f20782c1166a03001c1072000a4098501c1c0140743c0540c100702e25898000c035205028036404200e43c0050038400844910401080314005005444507500c00f450902c021b4a0005900b00940403000c0c400100c00210a4200c403219500e82044240000c0141c800e802c02046401034160500c0c1c6d502c07400145041100116 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 118677679 1250 118676429 118676447
    0x105010609051e0d03020a080d0e0606180411120109050f011b021f150b070201021e07030f02060d060315060e0606040e18030f2203031e0908060f070807 67
    0x840034604215040f0080d2400000c164110f92080c01524180d40542e2650f030305640042610352503d9844a10420b011403042c00314070782c0240d04440c0e03903514040300d00c0d024058103c01003004103042c0d29a0291943c0e80d4824858020000c031010003171000d481c40e403820944070300084843d041d466003000e040400b0500d201d450401d0184031035006005441c542c100c88103075031004200c4200d0085d61402c00d4442105004880b1000c1d1500c01c00c0e83d6520000d600c0020b1034003602c9001032210305600300070181d90311004210b082c1204d4121300303000d500a03042d0000402a11915908a054902d003a4001042124511480c100308114450801005507115480c1d0b00802d4100c40140d4080304c104802e000c0d95281040780783d00304c00d105030003008a0503c403055502d1a030060f45502d00140c008540001540c2c00c0301c0003600f4a0420801c004891895540c000c1c00490043c44660024001d001109000603c100810001804504125034290070401c8181a409806589610020345000c00089616001e02648 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 118678929 1250 118677679 118677709
    0x30d0905241c0f02040f030219060e0402070203150906040b0c0304150509010b0d03020304051516020f0d05010c05030105090f0405060c0306031905030d0b030d020307020603100306020c010501060905 87
    0x500d00300110300d99204401160621400443d40c070780300c01640c1501407000d080174100c082c2404402e10b043d401000161000060140d03a40e80b4915410720801c2d0b840030401c00300410558016866001501c0080e04040070740914200c6c04002c00e0400c0030151000038480e00a0b80a00e0780210940c40b110420061031004860180540308080040e40380c064441e80150350005401000044d410035010000d54681c84109007980160b0020606101c1032070409503060000c1d202d58042441d001c40c2d588490943c500800011744610b2540c8103e080c962100d40061643c168804000c1040342c1ca403c4d0003070083d40084c06010b001c0ca8a00780040c140d0080101c030540956005001004540c0d02e80d052214141c0c40202016014059071600401c0403242220000c9410701c0344003d1341d00d0b110360114000c11654040c1d0054401e9104004800301650003004a076a0301c2c0e0150f60b4103940782e6170b4032a081034800c8198002441c0740d100144a0b4030000040d400181078900039a0380b14161940c401c10130541400c2c440307007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 118680179 1250 118678929 118678999
    0x7050906120309011803020607050c010f030902031905120307081603020708030a0525030203040b0a090b011a040b1602030f071802090a0312020a060605060316081302030d0905 77
    0x80743ca802d60040c00d81242443c0f9542809108031384070350100d0f203c0d0f0032500088890740c0c4450107100c560341c2c0000356007041d40c215160030000c5600176000a55511030000d5100200030301d0707880e0741052080501071850400302c5000d17600d95904045000074140041216484629041820005000c5109000b00c1e41503540151000d0f0564590848c44c000514001c2d03d165089011840c59601401403041c070709148801a0328010380701e00d07041c1440110003100038055003400c1d1402e8030110000e858412044e040d1141070340840c08a03201884025102e11450304016070781900410034404400b018100c02c03441901c01c0d02900c4090018480304d650b266014003e524194142c0040c0345040d030015805803500d101c0050a240040b0313a06d0719000721a144c01034050700160044007034201400070701d004810007000141c9000d451458080044205000c0740b8000c04104504040071901800d2032020702d10942d07070010255034260404100282c1000032911400d402000c000521022415003003410801645003025 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 118681429 1250 118680179 118680187
    0x19090b0a051b210a08060906030607120b090f040203101b030b0402120408030105030d0e0906010e0d1401020a0306080115051c0b0a020307031113151b05070509061203 73
    0x20080d007400310b08420603105442034061405000ba8820075450408108946041d0ba900300e03101c0003068654010708032401500b8070000c0c03082507100080c1c400c5e840452458003034020300c41f20207178001406c7c100b0016613110314040248000050070b4402d940c003884c030807012a020b80550540300d030140e9080140c0c0714054050140880c03001c40c000d40181c4482d120041c0010310300f582051848955510039202074850301801320042c4071a05082105d0444180300c0d04200045140490000700c14600003007802e07040200c03a0b441e401ea16180d0f00900480e207540104007500c0c032500010014000d402001c540000030303003000000221040c042c424445000c50807414891900e0820b1305003c1a90201070f4010030209550740202c4c007080c04074029a00810a807140583e403410008402025206940c00504d280d503403c114000314401b50b851300f4801c880101c1c15031500007214170801c0e83c08440d0a0004c00610b100399040000304800400c442c01503e008440010203034440c1e03004c1c4100041c07c000301c030710396900c108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 118682679 1250 118681429 118681447
    0x108040c0303110106030602031305010e060405070b090402040b0c06040606050f0310021b030a02150109050f040f02240c0d050c100203060604030215030708060402090a1205030d0219090b0a05 84
    0x128200703c103a98440080f800b15a00d503502000ca0b0300803a818030300b018203000d500d01003200270b024105050103000020703c8141000c0d210b05450b84841d115420b15844009244441030b01c564058a00030100c204100da1034a403080249a15400304a4044440d180b0b4541c01080600d007800c81030b90206405070003000c01c1d24a01800b0f900070350000d400b2050401c00c40c05105030540d020802414011041d5020b80718120003a11214000c100c180c0100584505010400c00c801c4030000d0010b0303015401003081041d030340e03240c008942ca1034500c8044188880c030030110310300e20784200740080903228140c5040b90400340c48900b044131103000f03081210419400c0400004c480e041d81d82c0296400041c0100010302d41540c039800078010a80600384480321307900110030400e102d41c01605030359201e54250350079403821108030b0025030381252901410706003954403401c1006200b030410a86400070009281159140d65450500d120014541524030004055520226a00c1402000e0302c0780b0885944915040084030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 118683929 1250 118682679 118682687
    0xc150c0c17030a1b0b090709060801180312090510061d04051914070905010e06031c0c06090219080708030c0604030c02011205041103070504020f04031e05030c100b0108040c0303 78
    0x4070002040740c01c004c1c4007078010610501c2d00728050700510000b425281c0c03801e000305003594404c2e40640e0843e450142c079030300c02950001d00e80301c01c80c0d03051074060405242d1528000040043d160050124800c160302061544020741c8410161410018110724001c424020404084030490340140b0941085e054481035001e41c6810300d2010344280c0c112050240703054a010f00d401150341c00424944e880d00010800200e501410a4101000350090801c00400d22407000383c010482814400300a00481038200703002c155807000d20000ea005008614114020350001105050b0380503062007801044000185411b00000700d0302039443d583c01511460b612901d05641034103003480c059051184407080380d01d20140324842c00d071007144201d0004880b103006109151611305030780c1005001d0340c410009a9245032540c81907800310380e40100074000406021405120100150304018018800450340e448101c1000c28183e000001c10501008228004401142c034080192409002800c09000c00e0001c80c0c81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 118685179 1250 118683929 118683947
    0x30a110f0403022202030405030a08010504150e1b16031106010e130c080a0b090d0c051005060a0503070603020a03050705030112030815030a0308090c0901081203040c150c0c17030a 79
    0x41641c941c4d040c1500d0355103940c1a6401203d0454040e080051961001a0084c8205003d01000d0f102003203011200004101c081101c0c2c014030035464140c000250135002c1040910f603810010f0304c0f12340c2c1c8134148000400750481800f0001c070003280c1030f03a104000c1d14074005001c81c122148030300c243c411600c6103c0c1e0b03804010480700080c1c80032400c5200106054004122031500e0b54411908490240b9000a0540c20728482c48802070400100505800101b003000403c1c41e19249c40c504000b899444040004201c250264443e0350107000d09540082e1698066020f0110301045032024030040c0c0e83d48a08036428802405000c03500b000000104010900c1003c00da80d200b991607801c0e064100900d0002494100003d4046001940703031003c0141d0684103104006400700140d821050b50750520403100d44601501040f080306a20200000e404d0000915102000b03180d078100f4101c005052201c004c0c0549001c28003540d0020b4811030011f807004155199140c8a0380d090b0107103003410803c000840325505 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 118686429 1250 118685179 118685209
    0x1309020f091c0606050102010c0c03180e040f030f05030103020a090203190501080d02070e040f0f08070f06020a022a100504030804060903021201140c0304080d060b030a110f040302 79
    0x10522064010b616141c0480d994a1116500c1403a40d4100340352000c25181c05400c40f50440e4148002ca400f03494002c4590118107502d420020b400a8030084201c000628552110703081d400b414081c0002c1c007061940285c401c60096642031440407000c031042c1d460384000e120094000c04900c000300620400d6034080c1d030300b1201c01005014100307040c2052030203550003a0003038242604400740e084001a01000342c20000c0042c110500118902612003c45110202002170492104071140b0400c11052404030f0780c0b5181e10200c0011240f8007818074100030341140380c540c40588540714500c0c01b0348484914070340400e50440c6107040284030708400e0040404a070080042484010b100c013000040d002c0000d000900540d507901e4040070b20b1070040002d08203084034084480d926002d510b01c804006000c001c0c4d403207040407040f02c1e92511140b408400034441c500b0710105c03841c03406034042001c404140081d40203400c802d205100311009580e84214078802c900b11801c0045040004200600b0141c1c040b080d040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 118687679 1250 118686429 118686457
    0x3150302150909181603080301050904151b030c230a090506040305010203070e061303031d03010213080d11070905060105070209040501050106030f020f0d050a020408011e0c0203130902 81
    0x14000110f2400340d02540c1c00007000003041909001c0b1181041032502c10a4480054042c8030300d10740345c5402c91303c0103015145c02400e410001030140100701c0701d240c4008128050402c2a0791700804568111004103503110006410f040c4900301a80c0704121042c143c01c060113060004950304c0e81001d45681c0203200d220103100d400300300025a9aa50340191005501800001d60f4074580700500421101703061413060310880d0305114204541c0009102d040540340c0c103050031030502d107041001100380e181c06141981c0c1340d800003a0200b000c0e8085580718041710000e90458030580310490064500344081040d183d0170f640004410485400e95800c01078000300c040c18100c0c030705070051300845d030040750440d416038a43c0e455000403c0000c2d07051058032400c146207a421030900d5030564030682a4401c040e006a00e03243c8a60100341c2a510380d6044070000d1004400070004002ca202220007407010718060802c0030b030302d0b02c1d808078030383c0e800402201c07001594482004a4079061249180003034102d6801d0310080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 118688929 1250 118687679 118687687
    0x102090303131d041109180d020601090f020703090b0304110901120201020c0301020a02150c0403140615011404120606080624060403050c150c030f1b070f17010e030d020a08070315030215 82
    0xf0410238000c406802c461a40981099810801501c003510005180051800e104008540201e507001c5481e0040d0b031044c42d513080d6a51a80e00f01320100d224050340c040d0f4072101c0f00c40006040310032110b000c201240700381c094a10301450f44040600b00e004038001e00c80540c01c40c250000740071a030081029407001082d00c84900742501d949a01c80781c440c621240c808254490340c18040703100d907922888201080c0034a00040c528a881c83d0b00340c0341d4041d911071482c0e6104840120010407407150011805880707400200c60030ba140c6105071000c10201c40321418480340140c203046500782800005c543c1640c0e080002054041c00603003e20500001034040c90394100814070156108030b1051004103650a01e0310b81c00758903200150f10344005200e0388200b2080c1c80c0c2c0061380070840c00b00b064030050101c45640c4034401e50542c000b0001409040300c608207203814003000031064032812103079020300120b0b4600da40c2c3d0510781da100b01003a8204d4040d0360b0300281d942e0300e154080006243c10142030051152000c9002d0038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 118690179 1250 118688929 118688971
    0x90305030a030605240f0c030712081905040b010b03040305131e0603020304030e090a0608060f010e09031606021b01150503100612060209030102090303131d041109 72
    0x4542004011900181c3c403800208070900d0200d04034440c041c452840c407101c0c01201c010082d018030450511303400c090808251315104000900950b89604d41001c403010540060300e900401c2d82d4401c031346126280300340c046c40c0d1401200c2407060920599010704560303040c2c0d00f00801c012981d04010000c030104039040000c3c2c030790345114140d020300a00c0c0032900443c00000c0c54542008001d01034114408240c81030007000003090b403215010314a10410343c0c254269460700c2e42c2d081d001e0072817900141602e00c50a414080034000c0040054100c0b401250404070300c4d22140e0304148c40740725000000b0645c0040650030008248998000c1811111541c0c5c2c50b03e40e001e0109000d801c0d5a81000d01d06c1c03148890301d03000c00683c141030106c16640c4040300720401540741030880d00c4d00d041441640223020f9076400305419072951825412100c41c0d02004040320744441d00d902c4400c2072044c5c64000c00d0348a03005040d041007105044c54949010341d6101c1e0302402c00d508044144444250f00603d907044e002d0b41c0024606d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 118691429 1250 118690179 118690183
    0x9180f020a0f0b0c0106050909190c1203080603070614040e0c0409110d050708070c031101060b03010f03030311070201050708090a0b0412050c0d12120b030102031303110c0901120201090305 83
    0x2004051226009450b500000512403c40325079a001c540105803000c108445000c0c00701e83c001c10212242c0604080360ae66040040740700c2c80c503400c024a0085040e41070380515801c8980944640c0085080b1259283ca547c0700326030040740e05200034100e05041c070061000000e0f907103d242d80240c0207600181000e0f9101c3d162000d4134400c0d02d49103000302c0c001400202503811030003682d60058550a1440c440e0038405402001041e041c1c0015040164800090040100030f40103c00204103142a01c3d80760758607091300903556001480b085021901e448507072600080c501044c1c030300c01a016100c031402c0c603d003900c4002d4298088020f155204050117008100c01c5490809003029108400c4c5841d00d180ea00c0c81e205141c000c00e2076a0314829603002c00c11200080e11000c09280012a5150060600751078602410243c5a00401c640c1d0550011081015104c241110354541c0d40c0280d40e002c0c00e82c4000e00f50340780c45249030001700342c11920120040c890b2041110707242808510624000001540c0c948440d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 118692679 1250 118691429 118691459
    0x4030305160215090310090c140d1202060609090a030f140910030c14041203110f0109080702090a051303030b010e0301060e3c15060a0801080709180f020a 68
    0x3c41d0804085906482810100289100c9480c048000c01a4a080c1e0f01d80d981440420b1103180004540850381041e00e850340d011180000303521100d03844131813010b510081e454841c101c550a01034120100081c415032000202d800d10380347c06440700d041052104e0000c9652184818042d003110030104080982510790000d0015140010b5500081c1100701c58801042407034024143c2113117010074002030140e2a00101d0808a01d5414205078130001c05060300c0900317120803214a0b0800d0b503c6c00101d8410302030310038001c01d01248210307544103842c1e941d24210b004940b401d5030201d00c1c1c2c0c0c400020600c0060702a0f48118201b20050421000e0306c509040000c0c20f644e000c0c1c100400c104105418801c040303105070300105c01100604035840e203c1102c07065904800800700040d8080d48860310105141c079065080c10800c410018150a83e90486000013802e456401e10070f0700c0051188040010759040075100b00aa8004c2d466a4500c410311251a020002100c40b00180c2e4060b02084000410000c034007141 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 118693929 1250 118692679 118692709
    0x9060a0305150105030f030408122b0f050a180b0c0408070f0302040e0c03100b0d02040c110f010e030d0e03040803030916050306100902030a0b120a0b09070b040303051602 75
    0x42d0781a60500b02814244802c0000c006000c0d4000c0c0014000090b021808908031020310160b0354407418140002404546441008980401c0320b02c017052450748650032a18000303142800c1406140c44206002046900c06604c10284030381c0c04584100050040030520303045507403407100604082e00c820f1b9040c1068001c2c0e00c40e01d03001c021502c04008606050140d0400007641c980902032104c00e020100740c8800840d07200340d0040399942c100c0e00081e5030f140003c00c000d0750050003c1245441c9a01c024240e40150307450f48a2600c03880d5503900200005001d80030f1012004005541000d11025481000d003014540054003400144000700e4400790070005903200d803412100800c401d810182140c032580e40c4541155019030445002c102c884600c40d00c050341100c07195a80140e0303031750340c1942279002040d020000e0744c0d02c149168203880c0e040c900044c01c0280140901440c0681d9140c0082c3c099403402c0ea4031a08881c030b00700340002c002003030040000c1d00621081e0b0f0110107074681d8641c00601110100482 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 118695179 1250 118693929 118693963
    0x40f2709060f32040803160c05100207060b090c04050609060c061015050a020606010507060906061707050f0906060a02120c0304030c0501080603070302040b1516060c0c08070209060a0305 82
    0x307075410450400043d444614510700403815103060986600311688001401694004144501110010712a02410002d40e8010301515698054a00f03020080d50010b4015100141092501600c900e4502c05260003406044106e40c5410725110a06c031540d002000d0103607010400340311484240e201840350390b1185803010b2021b03040c50305103101082c60200c0202d841040000920800d441e594001070390300d4101d002401d0071521910740d0300e003c20140200e40c070020916400c0600029542e208082410410f900001c20b550405031114180520b110101450790780c059805404244142400c00041c4011645e6105031002e010900742d096000e54440500d01081d9403001808205011060f026400548400d281910240c1440d80020356601c06600020344207641c2c452207010a80e0715440c400c0030072141c64400c5901d07000c0c010140320601400c1030041d02d805050012103500603100790a0001c240e9845921941052155000d0004000c0000e29560f04120f4880020001c11420444a40c003080c078800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 118696429 1250 118695179 118695221
    0x5060c09090c1608161b050a0801110403110a0e0c0705010c03180308150a0303020705040b030304030c090c0c0b04140f211c0204060203040f2709060f 66
    0xc180008807500800440d040d141c18050346442c440896030000e401c90700449000c3c0c4a4801c0c04105c070061036440c0005140310420350f000d400d007224825840c02114007c07125039010694442c119800d0b12464029640f04c0c400030030081c0001482440b04a11500003c2d205d03001980c0c5070700000711340850559980c0f10f10000884d0b8072040107024051540400118501489409250808503c1d1085d030000b0007020300031103c000a40345c240c102006a03840c50000e2070041081e03501e0401035103903101ca01034030b0f0003a42840000c0829050010441307084903405035140c11800d02d007148020090031105418800c0040080094002c180016240fa000c0d9000e6201d55500600c404440ca16240000c54103443c1b030341048108803c42d00080700c44c0d140400062511035983d8000301020240c500001c4400040c0d90302c0440d022941581c0040a0425207400805400d205525540450b0072540c4d02c0c1100030004180c0c0c0300d52142145a50440c0e07142921415000c50241080610407064500300c1c9620004e00c0c440d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 118697679 1250 118696429 118696447
    0xc030f0709050c070f02010f020f010c0f0206010f210c03050d030204050f0a060f0507050f030403050106030506010902030c0403060b0f040f0c030c030207050706030506060c0109060203010f1d06011b05060c 90
    0x1110b1550000604511245003044030350710705002514185010703040c440c3c1042501c00d000e0083c4001c180b204407800017001031512108000e491001070340c440da00140314041c000b042c503014403202042514071514100c040000203580800070514111000c5581510120001000960402c0b0322400c0890755240941c5071743c10704051000b0b40c1303450400c3d10300c2100d15800421250307421001a416410481c6041542c1d0511802c0c01c520340600c0c10041d101a10001400206000043d8005000d4a01c2001039440c0c40e640d82007048103070700040c0c954908a0388100001c00000d107250b070142c17a0350540a0004c000740f40e00c40b00013034101c49455501030100c1c0c0d21004001609035141c4a0361803121118101142000c2c41c43c0c491a60341c10707003401101c0c241503580002c01d00d103649401c150748036900c40c00000d0080d074050703140204c060f410a2058843d04064680081030304018410040d6800d0028518862183e4034800115010500320011710300030413000500e003002c10814041d0b144601e00664040369981144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 118698929 1250 118697679 118697681
    0x90203040614070e04050c09130e16080d0c0303060b030403030e070b0a08011415070501020405030106053705041401031109010b030f0712020301030f030801050a0b0d0e0c030f0709 79
    0x2984940c0685001d003c0003c50350300034a81c1000301c002901c0010340da80d162941c2965501ca07200c00b01d0f0784101e10081c1144c0401043d0482d18030341142100361036910400850021031a0000c3c010b5040c01d0300403c5d0086012032240900b0200307180649804110680e41e03034085003003940265010340001e900c440700f104080c0c0d0704020f0b8400800001001c1850000868402402c1c03d9041c0606013900f90540e07c1c03513565a95144080c10000c045049282d5112101d00d0494002d40c01481541d019500300307600000c0c50b1400c00b0000c3e5209032120702403019680104650b090503100900190040800c5031004540e079200e500c142d8000c200c16030781100d00355045041400300c9145500f80b00b882040128014020070041c1c40540381c01c003408181450041c0c0382c622050703807400d0b0108040221103201000010911040750544a4401c0c080d407a4030724543d032180e050011a000601800e07070f2003001040780350720160081d884130b242c0443e0703082594070411207400080d0412210039002c0c10749501540081c8a0940e60b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 118700179 1250 118698929 118698941
    0x30c0607021906180b01060903060e0d050a0804050a120c03030f0c020a1b031a071205060303030114030313262a180108071701090f0f0201050705070902030406 70
    0x100d030000b4920382c2c4400c16035508000708440010300381c83d11a00e45440f09268000c00072002d6500082d140700b590b031521402880031206100544d46182004100e080c004808900c0c2105190f4076500e42c1c1c5032071404141070714050340142080f00c143c801c989103d00803854008a12070003035580c0da18902e01c0710a60800400352001064400d50561920305008400e94001620440c82940542089119203440c0000c0b202d01015a0025000e000c190142260700017401e284207100344480d84905800710040031000e002c44404460302509a4010001440103441600086000f600020100d91400504007041114184e495200c40c070010605802032801c202c1d0550301105c3c1e8290070f0001d003a000061a00c41085180c04190740c00d0407911040c008130942c4910308410724a142d0348502400035691001d00315030390485803040341113140102510001a2406020300c4407a603822079691451604e482d2514103a03541c0c0307440101e0512008105920000d8403e102010003000151801030b105c0c6049d0030204141c4035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 118701429 1250 118700179 118700191
    0x1005061306260c0904030c08040b03010b0a08011203120e0304080a060504050106080313090b010e1c0c090b0d0b070e1201090b0109021c09080409060e100b0405011e02030d050405030c06 81
    0x4030300340455244c1c6480d00c91550041e014584103580152506000000e0b10854210b088210b900000100300c8c0a0008d000341219000c41c3d542c000940e0ba01c08100c0050903030450002c000490079098010303600f200350400394014003c42c050381c0ca02503580d0301662070410580d0044030300644820800043c003200703108080080c00c010380558030780020302000c11180c1d0024040c8807090740d034820a00e403007a40300d45807081400d0005405141c0b8401150140142540240e408071400c5041b010302081d0780c5003070b001d4580604405006c3d40440c00b00c60741c4002d4982002040c00c001c0140e1062110055030f5a07207a0003040903c10400001d040c0551700341066603540503080115001e00401041100003c60001251420f035800301c0052070309400c0c07800c0c1c4c00038455540303c00270b25400c2003c04160f200710f03259070500440300c0d000301e041c0c941e5035102c6014241c0130b14401c09004c690b202140d040782e21741c41d00c82130b00080c81d50302c1602e281c0b0501281c2e60f41110000e032001d498603440407982d082c3d070100801429401075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 118702679 1250 118701429 118701433
    0x2030f060103050303190908030901021306140421060603240515010e0d080a030209090109060302010512070c052a0a03020f0d030302040825060c05100506130626 71
    0x981141c4441c2c0c0d4030300c80900b94980740d1b0602c6000f0281001d0f258441c2480360350100e00a0740d0b9081070428a03001c1d405c8072807901d526003a00c04001520502808207241c000c00001c00301d03414203140c4006608811540c07484000701c03d10080030080010a14402d00015510510a80c00840a00e07015480c101e05030041030640a8980b0060107000300460003c3d910100092070a0085810418041190020641c40007810b841c00456906c000c43e402d600a050350740c0c07094034600a60780e070380e841c0c4005890f2540b01c041d0204d81c0801c070b003000d8a41e003813404607800f040e00d041c100726000306a554070745021200035151511703482101104c100b44050f030001e880000003ca6a01c2038103825900080c1c502100304d000e43c0d1081c0c06107250301003010300940546000f0040d40003524075080d10b1840c1040801800044940d0954125602141c59405440541203085c1c00500801502d81250001d100a02020b41003641c08403600304040c1e40416076000d00400351146208440988030165174140000022008421440d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 118703929 1250 118702679 118702681
    0x7260a0207050613081b030d050405032116141605010c090902090f10271d041104020304080403060e1e0f190812041103060c0c0c0f0406080706080402030f06 69
    0x8030758205c0542d803803003044c400034030304081e101202d49155100d0803e2040304c1d107007050b040001b4414048091300700400d8065810140c1e0180a25010103c08101d41c0e50b000605466080c0046600c42c0b5401d40c44103840b043c040c0d11305410031031800b00c60500c0e40b40441d0982c2d1507109089000740d001d08808014002c20f0010f5090a4000c000129120100c40703460b0300803101c02c000c2010042c0704903418580080e03285010329488403800c000301840401c44c0a43c00b00b00804005c4050100302c0600d0043c4265000744c6200e0303c04002c1820003000c0c2d440540262401081400f0200100381c5510403102001c5001008050b040c0903800014140c2d0120045054503402c240c40300c9440b940701041403510301c10308040400d038200e25031400042d580a50100c0402010070402000104a04185401e03000c074000c07801c540c0e10345d8400c4800b8810344200585800140c00c000e00a4089080c00020003156100c005d10100794aa25422202c1c0f8220a41d0320880000c0d40150a100550230140710b506034900480014040d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 118705035 1106 118703929 118703933
    0x130902070c05010f1b11060301080d02010e0d02030d0506040f0203040b010806090c1e03150702011e0506090726130b070806030607260a0207050613 65
    0x159141c0c0c180031449600400e13030411070030040ea8940e40c030305c081c3c80d442083c0781d4213681c021070301205804460f021594460020703601070700041009043c03e8042c014001c0c01e41d00000d408036480e4000c91100c107038055001c4112a02520100d50101c0c064941e400490020148103041000705031003c4240720412a00e2001c403070490700618110b8980b6292003800c01c1c2c4910803100d03603a90145001604680c609820803061107d450000c0c16686510303070502d0320600c0c0368002c446160050b590f6000c4851051303001b003440840810b14940c104482e1405502141104c1c901034454002e0000c1c81420075a01022080d0050290a40c0c0945800500b800300e4542c18040000000701c0f0280f091070700003001d0313078801d44946100e290024000e000c0307511180d4060340d500306c0881c5901e641c1404114408000724000c03001e41c0c0141d80040c00180d85c0d0340c0a00b48903040c10006042c50719510010581100 = true := by decide +kernel

theorem cover : BRFrame.Cov 118525179 118705035 := by
  have h0 := BRFrame.cov_init 118525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 118525179 ≤ n) (h2 : n < 118705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
