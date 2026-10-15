-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4698
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:27:14.488989+00:00
-- url     : https://prove2.me/submissions/dcd3a2a3-03db-419c-88c6-46da41389b68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 844784172 ≤ n < 844964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 844785422 1250 844784172 844784189
    0x61803061e07050c0f0a05030415030b060412140609070302100201020703020d08060310050a15051002190303060504050f040c0b161709100503040c0f03030f0e03070f0801140c04 78
    0x400701d03116901c103d02521400c1c40882c25100c50107003608846140050201080341c80742c0003c10104202c0403034a040c003503c6001402c00780410360602000a00620540c0a0b400202e40b500b0722410074001410030151001900c40f007110307203d080080e0241c1d42c2e504180700491040c10804003040010b8810b0003981c88507541600104509032000c0d90640724400c005250071303058410662620b8080a090107210700a8150002c00242c03001d008404000080c015080f0900a040e04d003440c0c1c03686a400200380e40c5099074000d0215100404c1d21f81100586410b5001650040c140018048000318040030240913502c0b55546210720b69071161007c44900824800e03014508103c0404404989100031100100074030b40d40d01841c001c081000214508241c1ca0317468005180032007003000700702c08004520054408041c075001000e00d180c0c3e00601820000740041c08100d450041101e0700d8600300100000380a10680030350f4542d45861405009001d8802c1440381d040007207010609019001040b1401d0300c2c54134 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 844786672 1250 844785422 844785481
    0xc0d0c050c060f2805150102391302030610110d080c070b01060801081002090d02130608010f15090b0f01050a0e030d0309110103151a04030206180306 66
    0x1407040343e4420000500440a481a84403a0607107900f03a04294032040800020004040c00c0018a00d2100040c5880d56419540050012104900381c0020314419402d25626011000302c10050050003038015603200d9000b0400d400ac1060000c0146c0103180f00b40c0043d6609500d808074414101ca45034240c003d004100d400c46002960f13624402e000d1158841e61042105140001c0350381e41203e600000d81c01040011100340040c829840144160fa81da12403813113041d81014083c1000803003c00c00140000c0c803030403000da0750075004038054110074000c00720400204101c500280ba402d020740007000b00c040c203071b440f03420b0f02041c2d160482c0f0828500b428054a00c040b181c02072001941c00c2c4e80a2420f0206200030149050078607901004280c43d074014135503000c41e020909152600420840070000d40c141820030300f0385c07000200c006202104035500c480c6400017400f82c240300c0941e10b1059400281d00280c00007840c418840303050102a824010503801c686030390359441c0c0d5003e03008000054040d6900d141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 844787922 1250 844786672 844786681
    0xb19110a030c0c0203101d030408060a0506030c030d020606040b0405040b0402090c04170730080d060b03040605060306070f021c0e1c062418140c0d0c050c06 69
    0xa03921020b01c184a6041c0780380404244e400192400400d84071010b0780c240c0795034003080200c0c00001c1c00401c4d012010025824282019101c0703440385002414ae0910a903990001095030303404000c0034260700800b5080d9480d50350701c108001e4480c0c9003241c190b0f000d075007480c0425680b802e02e845a144615007096424800e074031142e0030010300c084007510043d41140d083c000800d40c0b803285903c1030800d41c2d04a0003004007500d0002c00c8440c085144900031034500300c2c2c400306051007008102280301c259002468540c0ca02c81c803e0010000c000342e0300103a02060011080000700595540001c0c02214114104c4007103546106003110a4101481d005005811002020201c0c5140d25101070362540c00381482c4541100342004110411100020640b0a002c07258170641130044c03520442c003208411041000c3c804c80c2c5a4004024a0040d00c01c2011104c42c1209200d000d955a80c0402e80301e003d02d003188886414400d1240055404c0304400e0035800789010002241103000b44101c6901e031403690041d000d141da9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 844789172 1250 844787922 844787927
    0x60406050a02091207031505011203080406112a1606080a0902130902120d09030b0a0204051005120a051b090f190603060f0e041401020d090b19110a 65
    0xc014000c50103003034003809190b4541ea114059904261959002894914618107215045206800842d03500900d04001440b054400524044040d80c15080194294940d80b80190081c940d080100300150404542c83c01004d420b00403400c0c856407585102a07100d51001c8c80180c48500c501004406a84004000c0101c02c8c010030502e40e0001d13581000061011450700803482851165210010003903035500010210714215010403035004040009001c0c110f40e041000c0c0c41c0071014000a44002c0c41400050720080458044038050003010b0002c0e050039110440107007998000b4040350400583c5030002170184071003486014801c82c0030944940b0001842c0001001a6000000c0550495040e00380c1e40c055845000d81080001410440740840f140380901c000c0031070342560040144d0a00d071123410013500d40300c0841d03c0d1308960442c01c0300320311011070b6440702c1c0280310b00900c0a20050524135044140016030039410302c034a620450700c410b0002e0621403003044992a240c034190042c4140105e800d05803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 844790422 1250 844789172 844789181
    0x52a1207120510151806030c0506090a0918021f020c060d020d0903120e070513180f1a0105030a030f030c12052a030f04030e1809010e060612060406 65
    0xa0050707041d41e040f425022030300419210500705009503103034120700400c2001c4c00546a8000020b031090100010341c1542d460002c104060321919100c2c02001c10860071b543c2d102035040c0d0040c090303100c4c20854100d20700501ca02c60b0310340d10302c2a88204512000001c0c0448207030340c0060028507643c0981040070200041040c15004603401039003881d400c3c041903050843e24031480b142180a07880f0102150040e41e0600306807001d100d20482103800800c410005611b0744e5488036000c010010b000304045a208801441040d00d0100c09003884003c03400c008144000b54528001510007810061901e81c1c0b5142410742c5d40ca40c803880100010341402c0102d41d00c0f8401c1c2e010079182081440d0440180341102c1102003564000c2c3c0b510031311498113210594008108101440c05120300b114064213620384000c101c0321910000704042c00707102900c20103094990700c50f42c0e950300d0031045842c1c0d45450300302401018002c102501c814081880303104040781d00e0b441c2858605003031904480013054680e545558120182 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 844791672 1250 844790422 844790459
    0x90f05090c07080c010b1c11040207020f0a0905190509031e04050a03030207080f0601271d010506030d021c030b0a0f060c0302070509040c0918052a1207 67
    0x55100740081e80020b4070f240700500c40d1040e02d0001244085508042224001e600404451000e25180460000410402c05070728410f008540041c1c039840c9500204010450a065055010000b44804a5000f0581e40424081e074102c1600f030451b8507905860700100c075415103064443c2d0b4818404001060b01e8000000013101c00c9218060526580700041440048a0f0b08100c0268101490034419084204109080d407624035005055a524001c15105807905660300500b104960101c02000c41045400802e140c124004c1d61506041024148a00801081d584a440b9008940401207154230000d140c400e211401da00201c140310101c8803c1d40180a9010040d400034034101d400221260070b21007071001000141c0301c040d40001c1300d15000b820506581c1000703119000c10400c2c00040344d80750080341c080e90750003c000140110884115a004e80401400401c184210200464000e105041207d01400d0803c0f084161181e4903041011807105240349005591105104200054103090b141404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 844792922 1250 844791672 844791691
    0x1802100e0306011203080c090f19050d080d0b0114090f01020114040501021902010c050a0e060724140402090412050f030c0406081f0501030507050c03030411040c090f0509 75
    0x85110000c0401d042141c260300c07411440f0300d152080e07401e064002c080030341d0013500b4040301851700301318a0000d0784000444030f4140c0038010302400c40c44c120f40f00700c0484001d441c00400443c00d184c41460480701990201c800880d42c6818010191013950107110311080325080a84003901301007080c0c01b405421100c8110550440d9220380d40c0040c8901d034155058041c070f00410002d6966541c80d1103540003a22841407a0086a00d0211040781c10344e84041540c902d54951f142400b044258040010194091210060520182e208251218606c50111142200311101091003425181e040d84480700c081103c020350805410400140003403032030300300800071920754241281045c100400e4031805030800c80768112020760008040c00700c04d030070100080c0d001070000c00349440c1d2001032128051840181c49154180754540c00401c4101c1e0043c02690325080c42901200c0e2646400d0071701c04609a56844854012494400e407506128031410508040c1c030364001c1500e901600d000140000448020a26020b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 844794172 1250 844792922 844792937
    0x190227010804030f2106170d09060e040c03062c0c041d060109030812100b03040f0b07110a08070618120c030513060f140c28020406120c09180210 64
    0x2d081817a1290001400300010400801e1800d0000580f42c2085440c02909100c6941c008100059000c3c6140094140c1690f0200d44071031404410f4002e80308030b42140c014040700c9d044040103800c9034000c039000d201445110b50455260031070307401e2052240f802003582d52035085105c0380c09025400c1c451500a0010b1411240f40d0390359840741c01c9035800102d260702e04010690309000307584650315216000750110f6010140fa5040c40d40d41c1000958034440000c10100c1010b0019501c51301520300000313407100d240e0940b90b52121518246400741d1001e00201c0301d56240403501d00343d501c88020b40c00c00b000d900c01003542c1107038a10705080e1418166100300702c042000c10030410b40c0300c09052020200914480d100c0c024180e0680001a03c01d000342404156124400c0c002902c0c1042c0010f00201e90240c081101e403400700c5400020801b0b8114003001035082820b00100044080c0c4400d103400e60107000d05603007110940c5482c03800042d04c4e04401c0c40e0041e0344020414001601c0d08158505200e41c0c14180380c3ca = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 844795422 1250 844794172 844794227
    0xa0e0c191d010905060105190804030c140f0105010803041202120a02061b011d0616020708062707030f1e0c08060702010b0315040b190227010804030f 66
    0x7000381815a501d07501036250071004000c524035600400d900040b00f420681d040c41107940205c0310b07010283c000d580c03c00c2000c0340410305045c010759218901d5500440d0b500b481c0d652020745140c1e14a982d241940c2c60b986400300010702c030315001c8182c40a85200c0c10850034000700301c5e002c000d508580500c02a0b8640034103110000141d440800800b00140302e4210701400c0201540f0721421245010600030b480075007410b14402e662070118100341c2c4222000c0b034891a03c041914100e20742480b03a00b00c3c3c485881745509000500075001803ca0346c04c0b0750b03100c810b40262114241e454a543d2a031000a1421143e0003107000007400c031884441c101000c5100074111403202e9113810401c101c030340d03100319030039041171050103c035030750a004107003084609130000e098803c8038084058030940010b00260110500a003c40c072000c481200344070000341003c07029521401c2d2502c2141ca00e01c8448605001d9160a090200044d40180c01d01d40c440e03a056200d20485842e00c0340182d581f0012840c1c00080580c9828458 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 844796672 1250 844795422 844795439
    0x60309030c010501081606080601140f1209070e1b071e0501020d14060402090306040b0402030a0b071d270408041509031a0f04080904090b011d0a0e0c19 67
    0x9001700f1800c0020481c804010006494501e150303000041042007800400059036004000402040e603071212141e030301d03e8030714107500686c011040c81e459003600c08402d000c030034800041c14600751752501441760b445c1e44459074084529000401c40341d00000007886000c02040c0d0f1580c5a00221600015054100d0b115035526400ca0744201c582d0401d00740c0c0c2c0d0301055000801c1e60142c69100106580031407600b5035110000b590b8200040000308071b241c007000090110f403014450002c229a001c800c030110307402d11a0b03000c0c1c00c080701c14025074004003603101901854541250361001e900481e0b1268107050744080003420f14403000420641d0102410000000c8038815170309143c00803041c59490b1041141036140c40c110510306515000740c1c6848007418000c0c82503014000ea50415442500150354000510200d00540406103001e8020070058000003843e107900c1c0981034034841c2e09003840360941d0754820000c045a11421320204e03990b110003004419400c0242d1301d18450390841541020240d030301c80c1403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 844797922 1250 844796672 844796681
    0x914041203091203050708071d09060301020904060b030915060607030806030a08030a02090a0f03030f1d040501060f02063103030609020c0a05071a0a03230c03101211060309030c01 79
    0x3e01c0000381d80c0c0c17400c0051181c0d11401043c0c00c0402458039a544025000e40c1205900d408800148191880d90114115503802d504039030107036002030014440c69a0351898004107030070485001006000e50303446031180480503200240708007030051200342425000c1d102102c0c1e1850060100c1d805104d240451000f255000d4040c501c54511408050798030000c0e402800340c000a01d91084420303508041c810b20000303400c503141c45480009460a05551070040c40c494a00c005c041142030740003450f12001142c80e942c010f1925048505c9074080f203180e9103c00c00145444e1220390f030b02005264958100d1720715040302e02c4803a09000e0080c13a0102d906902ca48008040368800384150007940d12030380c02c100401c2002c1c132240d00141032050034400b48808906ea400300c039209525100c000c255607842c3c140a01480c48071010600d40114400f076005140400700c02c90503a00658240b21044050000040c00ca8900040c030303444c49a1042c40c04c10130069000500126400c050900d107110300086c00740300342c902c209201e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 844799172 1250 844797922 844797953
    0xd08030a0c080907270218010e180a050a020903030c0a0b01080a03050406080403030e01020c07030c05030d050d02181e091605031b0d020a0c0507091404120309 70
    0x1565520306103185944216006008490306001c104030800500c00f03c0850010300315a0b400140b000541400c14900c942030707510031040c250f8030344045194070703c1c00b008140501300c2030003e0700c23104072604140d41080300e1019040c4084200715075500025460030345542115400400703001016081071509400641150803440398130001c0e0b44510200c4007800500035181f0300600c04440030301b40b030340760302e450040c802e20650150341c060040803404501018880e90200d000e01038083c0085448407101d01c10315407200228401030307541c05044a400300c0e081c500170135264203003019600c03040d2610000248650203900004505205c035090304920004541f240031002d4814004607042c82140d4025004210a004000d041c20b4048030604080300e1656800504030ba0b0400584800c0201d85400d011203a401842180c0303d141d203450004c03c0030b5096680088400d03030014401c0d010341b6101612420a0401c44400991542031140760902144c04513022910310407540116140c0821b038080c171600e4410581c1442030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 844800422 1250 844799172 844799183
    0x111902031e180d051b0a030b010305010f1109030a02012706020703060516170a061707050102070504020f0a1b06110a020d03062402010b091314061b0c0307020d 70
    0x1d01070350402c9128000040350001180d10509200b0291200d030343d241c0e00790551a403880c02d0150741c088140c1e0303803055a07402561321100c481d0030b070768507842c0c0103018100a0301c01c8070700507061807030100000c40868290f81485402500404604217907800449042c84500c0040031000f512003082c07040c500c1000481e602808035500148002465854084222500288950b80c2c03d050240c001c240f4580c0810843c040ca01c0c0f5481244140d211110400018a0f803070344011000131402c1d4844082d03000c04195441180c03000d8095038140c1790344100b840241c3c841d55071400c0b0710903003c0250084490081e49070700070030002001c8014020308070b5600c0200700c4140b584040c400c240c020400c4420309038104150f10b06c084646c5070500010b40340840100020038038684145000003220103d21105100f544080a05600182a00b07000d0401c0c0c0188200d0a8613034005449456481c41514090000004c905005035024004210b4203981c08a00410f241c2000c44c1a05840c00104800000f6940d651411800c0b00d0061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 844801672 1250 844800422 844800427
    0x22090602040905220f0b091e01061d01030503040b13080102040b0706050105040b03070b1605151803040b0306060d090f14011506081f081c0e0103111902031e 69
    0x5042d012070850944401103000c5a1005002001458110700046240d61006c840d048030b8030796580513414610544c255500c100c1140700c1080c40f210741508400202c0e6002c0035480411801010901e5121a003400007038002da000b00000c21041890000400c0ca0ba03540f501201403840d154074841d401c0ea401603204540c1c41c500800e00c0000d2140302c0c81180d0041c0000c90381003000f0710690b408240c0300ca01c01d1007803440d811343c04108250700b14414403040c042c070380d840020390702d04a5054440341c1d92144155245001c21600800740d500035003000080300d06946040380024207603a154020000c483e840101d5110441d620350314190001901345100c01001031140b1314100001d8a041c544508440089042d8010920000d0040061640004440d034214a072200e150510311000d882c600b8100303070070390300c4154203110700c003050328100c100341c0e68101c0c1c3c5840994808907a071006030f0044096038003468083d20382001c200a0840c01140c1c0800e111800940f50050b40c0c10300c0350b60407a050303941d030104151604c002d200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 844802922 1250 844801672 844801681
    0x9021303120507080c010c03050a0b010f030902060c0a0f12051e0d150b03090f0601050f04200a05030f0f0103021003052502070f0e15120f0d030605030c0f22090602040905 75
    0x3d40509c65020352240003c0042c003180c040020f004807a0300c52002c1c04d041d0340b40508010342d00d40404640c0c18810041c12200100314518103a02d480c1c1c520b460a580d19a82c140b122414141f0030030803200a42c0b0a002c000541110720708007021150300079492002c50036a41c42c011480d44070382d03d0800300101141384134292603140c480d1055003019000341140c101c40d004280144901c1c1d030303403007144180300c04107450000c0c1c45100d001020408910303d10595580b000041850055554000000c501c80c089120595025461f0a1900c44101c4002e0100960ac00e9002c0200c414092083d444540e109821011a84c60260701175411500c3c000d401c0c2008005802018050084071300c3e40038908010001035031004002e140c15001c441c001c000045d1400e10648548142c5040d00e6820092200f00c82e01800655000d4039021001034000c00e03040c0300341406401902c245542c42d00d84054490310420700500403484c0035040c4040300010034268656008c7c0359682d0310000d804644144080c00240240d0580000c00781007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 844804172 1250 844802922 844802927
    0x180e01050a0e100e1e150103080a1b0206090d03020a0c080c040e12040b130e1905070c050a0b0a1d0307031116060c02062704050109021303120507080c010c 68
    0x7007104050f803440c0d0810b51030307440403040000d0b401302440d140c42e94103807180900c01c0481d0030320a2020780c180c80544c0c0800048280603104004021030800c1d52102e814100302940d92440c200d04d42c8030080d41c0400140070400c2c3ca03007000107501004d2446072060382c0b24882d0341d41d102d0264124a420000e042e50080f5045500c41c00d00b40b18441501644100910b43c3c01c4080440004500c6507000c0ea51007030901044d091300c02d40e05200018003030100d4030705400c02460608900b0303508038140d01104079084e04200c00308d00814010300c03d508455030024042c014000d02c0c2d8545124006024005027010707603443c02c0446c412001d103071017510350b040ba44000c0c55842c401420000c09104c0c10300e05e41d4845410001c140d030880801d410548003143e031181044001c0580f00d00000c1d102d40101d0401d40288801c05e8038030a00e940e1208a48800708030121810052a41c0750710203e01213002d07a280b002000300c0b64a80c00e00120720883c1048180111920b402072500810f81d6810801c1c0e041500401400d80d100c04420b42443e8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 844805422 1250 844804172 844804183
    0xb010e06040302030c0d0203011b110c010c0b04300e1206070f1409090112120306050a050603090304240201060b0304030f051c020406050a0e0609030304180e01050a0e 73
    0x6004a44440c1040e0031900069151a0b00040c0d061003058141410401c546080d040a0382841004003100510070044501400040250500044c0380c00f5184040d071856010318619080a608602080c000d50360f80d07541c42404c40700e82c00b071071700d002c13072900c071a0803035884c88000d80c00f0000038243c0e00d01464090540601801052600d1000c100341c02031000c1210307190340030203c5940e94a42d4a4078580110450725854a94407c0d555550341000405001103550380d50300d500851800c1c4146400c2c120010141c1d070407000c4441d50f0141a6000c0ca200604000d13501d42a4040c3d0380010408042d40d1409039500220408014000040103800c450044240b282c44c4c0c080c0301d180010500c2a404134079601d400d660040581c0d4401d01e24405100010650f0344003c801184a80046d111080d011555603132106400b80107500b0000054000a568450052250402009407107807103101034025400c140c2401e2a8220000c10fa090311085c1c0d6a807882c00d5003032030100b4000c05024400e228030008400d880b907010309040a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 844806672 1250 844805422 844805447
    0x110c0a0902071a0603061303112b0f0210020d1803091d070509010804330e0a1a0408070c030804050906030307031706060403150203100611060c070c03150b01 69
    0x2e01d0f041d0100403030b0380c5001c01e505034003248914a02c0480c08503442d080e03a1003500448410110311030000402500340910030301d003465040c01c041542c0340b100d03012400c4520480801c118001030b00300f07070644a840180c5402810500d000b07400041100418513003a0a00401d1511007900040e4031207204111080049101c01001391018100c0409450106009030480c81030090841c10090b81c0d00006050110b0000300c1e200340250b0714a200c0441c0b540c0035044440c0031800d03042207209031411703c106002000000f000b600c800c7d0b0104441541b010346400e842042103001f0000c2d10803480801c0104000f84c14500c000001c4c40c0f04504072500d0324240018019480070040c001da0007540b00304901c4000c241c0141441038920a0105a441c45955002c0484d00c180240c0e0b0000b000701040301c1c580f91500301c164000d14415032004002148042d52480101d50302d03480301100000540040d00418054801080107000c00e901880c20039101d01d54965a14800c40d43c1400030f03054555503174010f801650ba005e900c1d80100c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 844807922 1250 844806672 844806713
    0xa020310081603080f0c06150a090605221506090807051806040915090f110102071a0a02011b080915091e1002130e09120307110c0a090207 61
    0x542d214100140d920000340805002d840003c2801000060440d00301c820304001d9200765620781c1007003074102c2079903c2104ca00c00d01c2004030701004030300c0451501c61742c0111800144000420b0241c80a000e103030b0a04801000101c9882d80c0900c03511605010000300100101d50384c50710802e10f480003030390600d0460313003001c2d100d10051145a88454441c3c0a52500320b0003c40340058039000c1ca1a0003000c00c1c001c8681e000d003050424810030240440b98003842400d07030007520f01c1007001d030f0400d004980302c0c0304d039004405005000031321800000755400007a2060b502d43d070000082c0629501a0383d00084203440c082d10000c1c105804208001e0700c00e2140d005211154a1900c0050a100f00c0d9143c8520884614450980e041e299850480c070f0208074602a03095603210441d40c40f003a14a4184107502a80164084e103d50403010503a403041c0040d15180200300c0c00305490070340d01da84501b10740c1000560340c48000c0c1e128100320002c242d0b8440c805a0b0007030002c07010040c0c0c0c03403151f868444817091501c42603205 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 844809172 1250 844807922 844807933
    0x1924030302030726030103030f21020c01050f0f040f0501090c0e091605010f0509010c231c0c030e0105090301050702071406070210080c07050d09063b030f01050a02031008 75
    0x101a41004c1a41c0c196981414502030011002c1c200300c40455074650110859101c84040d940c14100643c02401c0c4096000c00a0100d40c0e1100500c190200c0d055800f10036919540c40000c0c040f42c0c689104500c40380c401d4002082400c81d54503080d0440d40e080d000b1843c41d0b070b054030034012380c41c4080000c011202e2030010138000c0503240000123000d10304107550030f8052100020380e03025168803034110b24900030781c031840e103074194070300641542401300803410000d407148101d400c2e621602c440740d1000420080300355104800182c0940e01200d4640501e031525050004c18844174000780d4007800341e1403103241d06900901c1c1207480d04010f80191014850303641c2c0035141c100030900143e10346104554050f446420300405a403200c03000740c03130030b480b440d2005460b034000d4401880c5490ba0182c0c514084175829a04c54120709640b0140c241001c240c2c01a21403550324036003001042c9421a5a0300540c11401019108221075180006003996004c50b0f480c490740d540081000080c01c00f0509540203090303070000825 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 844810422 1250 844809172 844809233
    0x1b032f01110c041512080c0706080f01030f0c150c02041a0604090e0c06040e0709171b03030c100b1903170702060d020a05030604050c0319240303020307 67
    0x151698101c00b4454015911442d45000580820700500014241e105501502040a0401d212940c101c00c040700a0780c01191800030350315200344c10391806160010020481e0303920319580c281128146600c21100c040351801e001640014520fa403403001a07841e1155070100700d00b441044110389031105108100b52401211030381a0f140e00d8146c4003510351400300028104243d4540c1d51a00800c4a606540448005000325443c19130301016405150103448255003280c60b00781540d51034886407041c03841548400708841341c40d00f99007144188104082d0a80c2c2c81c101c20320041500b031540d0819070403080da44074803c0f01d540e030401080125601080b15071310070907241543d8400150440c0000c007080414804103a10095507100c1080f6445070410758411503540c00366480103082d541007240e006104074500720004040b88070704002c50317105001e02000d200c00c01d07030f8452648008003084413181007804084400995000841710400010b076020b60025610b80e260b0349803079440080185441c442c803025201018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 844811672 1250 844810422 844810457
    0xf0a0f181e08190810050f0d0f0b090102090a05030f03030708072601090b0d051c110102030108060f0a02040510050a170a020a0e0904020303071b032f01 67
    0xa038000c680c07040803050340400703500304140032640401024007109030001d0384a0722482e1030039160341003e256440da030480d95a000c00d001425003081c4a9242c0086040102c402245000c1518007052071160703a21080200c52511030880c504003c40751600140c0d4005072080403031070114500c00c000c140850042601d200350303200040d140c0c00090030750000d0100007000706903828090550401c140d0100254945000ca55040c1552343d080d0130303c1030b1180645066442106420803c907000081d03904031008110212080a03001035001007c240001000514991502c2c9444203000035402000e03144002d0595081607180c0844140c0d0280c45a400244100010400381e00ca084210100c6109801e0254a650003107005540e0042e031703c001c8591804404c001c10680d684c071a40035204940c190b0b592028005032510a101c0c48410549002e540750340248520b00001d240b0800c404c2c0c140341740c0c91420814540d80c1d504c1c461161458590a28026480412520030045d0784200c2a800e00b42442c3c0240c4c26072055044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 844812922 1250 844811672 844811711
    0x1e020708070b0f0f090a08030d05070f0c12050306011101061203080f0411010e040f09030801030311070b0306060f0c0a0326071707030216030e041d0706120908030f0a0f 74
    0x130038544500100d400d05c2c15540d101520340081089034245ea03a070300354500f01c00008080854070b07000801c0681c000c4281300c0d441017000070f01d00c07644001c0880c1e035038150071402d8610750402000e440c104a8840300d5010144000c0c05090010440300b19003000d1506c0518026020000003480d0010500c3d42204000100d058880300681c030075401e09001d0227507003000c1e0100e406404055100014282011121410554049021412a4041e507030301c062500603092600c0e01c491451003020003e0300c0c02d1000c0340061070020700500520042c20b4040d49802d006e00c00850070140c003203000fa80851300400000d000d03600c07641d4440e5211181203014038078520303012b480941550180c1c820a00805c845800207440c55019604a660320b80d0200c0031900c01242a25000307150340b440e000d885000f2402d0408101c48204802005e44108548002800c5e010b400c00d401100c081c0301c02a0010309250f16400302001140c07030100294015440350344444164036113580360740c094803051004221841e14050304030604000e403e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 844814172 1250 844812922 844812937
    0x31140412030f06090216110301111813110c0f19060b01090e01090614040c02340b0702190503070b18030d0203030612060f0a0c1e020708070b0f 63
    0x1000161401c0b2641000010109030704100c28991000540500400b0500d040000301486200d01c00811888038090600341d81d4030751500d0406c20380905c001c401c0340174a45034600740803c3c041c00220380510302407a1042030f0391510400c2803043d840010003414102040c010f110700c06e41d500d0003c0100c2030542c4451a05000c0c141000341000759500300d4103203e80c0c42140303220f0080802e24084d40c03042d6121a0070000800107442100131091094141a00c18141405117812012042d0068603030110b034421162034428880b4019104001640000c40858482000b044007400c3c12034140f540b00d60311403043c805410403c1040d0b8190080c4100104841c5d9800900c3c0800c0d22014028540c0b00e0210100e44440d110320024803d80c98002d10b007084111550000295104031b508039074401035040001441c0e40c5662090b035100d0120350901d000502c6814558000c5c10446c201e61400415420342001100749480034043c03d400140c000d440d040005500c1045407902820400405d00d2412928041582c0c16100302c11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 844815422 1250 844814172 844814177
    0x201050f03090109060f060f060c0b060f13061e050108190c14072a1d04110306040b01030507060e011e02010207020904080304020a091404060b31140412 67
    0x1d150141c04c1d0015120303964051410f0000d0100303441c200001e040c20340101e07a4a06089000003520b02c4c400c03107d55800c25000741c0390507203944030078041c07004039002c0307000380390b046550320110100445141c46100000c00c107504455540140461040b10f00d10119071190381044020030902800a942c0111280201e080c2600007030142d085000a4031241c1c2c5010500750441008a140f030706110110b50f092581e40d20119071f40740003c803c5960a04a03070b00c907015480603411761410608203603522088540c3c02500030f42c1c0448071400c40600080c82c200b0200e40c01c489114013070004000b0840c0030841c01c0d0140c41d0b181400f2509188000c0024500541900c819014082a260780d0050900030342c12610324035001b030100c5080d8a020708080b0495403056070103d020310040300000440c03010038454210b45082401c2c0b0190b89480d03a444e07107009132800780c0c0d0301c40c0d0101c000840001040030701d82d80640c05c0304240094629645020200c1c0e01201c0d00140e9244200303140340100710003e1030700900000c2c90741050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 844816672 1250 844815422 844815427
    0xe042012061f0e01030b130c170604021219020f040b1c0203070228141b2b051204141c0201090b210403030207141203061c0206210f01030201050f 64
    0x3e0f0001824000307007000c0c4047e030070310f01b800060095a01505100d800b0141d11203c40305a06d40d0410300c0300300e11a0455815406038580042145006810405c15440403503040c003606040681c3c0303060515074040e40c80210001d1300055002d4030f980f224080141c1c10401480c04500314540740c1c50107500e5149028110784d00158440c0e0903a00c00d421000b00c0e07540305030020b4881c0f500602c100c1450350346008028001400010300381180b151450218405090307840405610b140e5800c40b030402402d240a60b00040f0341c207029803201c06c99500010000f40c8011f01482c992500204001f4040c0300d1411185c085020581c09074421440150f41c20605200464036404201c82d6120f400c450038600005100700c071070410050200512041c15819005045814041e081d86050742420080080d5659016016001164028030000e00240303065008810303040e142c60b928003074081160740015126400f038501c4183c644603034840c0c0c410b181e00c2d01008580c080c483d00d041c84500d506680000e042406400201c11250200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 844817922 1250 844816672 844816691
    0x501050f0432010609080a0302070501110a050a0b0711240403020304030b070e0112023f012912041b05100807021c0e042012061f0e0103 60
    0x1e42c0001600168481c001a51440c603003210b0600c2a0401e00c034160000b08000d0010075035401c04102c01805540c19002410214600801502e1008810300300408500070166074a0201e1014482c1c0c0e00c100c0c0c0b007001c8000291404003405018140c0030b100d480c2860703100100031410030400361140005280386c4007142c030b1607540702d107022032561003140c0000b440901c0400500c4909600807443d09881c50090b01c4011907840328840a50481c0034441d000351080e10240c448080d40030b0340049000007040b0b107821501005025403100001300c8002c1c1d008160302070074956103081011000d0003c1c40b003a401403018510300b0802d024a40c44100d00a040035118000701074111800109061500c070060801512884402214240242075000100d803a0405400f4024070070f41e050b15181e415000c283ca143d2101e00140001c40c007400014020042c1c0c0700410345e0034079041552250184080c0084050900c902060351810328107003c03075070741c10030355180803020070205e42c6044c180c00021000e5039078020300e00003404115 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 844819172 1250 844817922 844817951
    0x62d15120703080d1404050c01080a0e070e1f0f0303111905030d060501020c01090b25080d060b130905040f140a170921010e011e0b040501050f04 64
    0x180c031903901220301c207006000080044003806081c01e01503410342000025641c03600c1001c49001200c00a00540010b02c02850540c0100407450304450004400507003803564440745450840950447c0b000c030254081040103000f5a07084030309500c10300075131690314246020703803416645159010050620100aa2980e000c0744204040d1654000040d804034101c800d600348103440e6808600d01001540c10b0410104455000060780c2e085240e040e50391542c03240c60018220102d030049500440f082203040001c1e8040c040300501110130311f00680d0100e81c3c0702c03e241c0c030b4203080341e82e00d502110b9100401d01c81054400fa03100c0280302101d0000d400802c042ea11444c00d0700362200f2000d8020860f50b5290344009a003100013424241c802c0c440d01e040c01000c1191204606a4003504101035401070066228000c6018146600c52001c445840041810031190f401c4600303442141c415000704035403804101c84a400140200d08001c00103480800c05541044081240484181c600a0060b515036080c40102e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 844820422 1250 844819172 844819189
    0x6070305090303040902070b060901051339081e06040c020a021e100201020f03060105070c0f0902030708240f061c0501240206060f010c1202062d15 65
    0x3480101580d58450312171824200075042041c050b2414842000003480c40d00b0300350007041c11785500420761311071900e02000600c007910b01032100300158038800c40e0198160541141c00c03890082d0220a903502d40c8a521001844094002c1ca20070034444002015020404002091038000d041a2b07000704540001140c240e280c4603500600a40001c03032001c0f000b42e1040c00e0503003d12142da045980005469001c14100d090307000d4402d100e90a05d60030000301d01d1a6000b50018514184100348444034540c0d9003656008110107984007810454001003000515a801410b46070700c035411904404884039000891010190a01043e5008041030400320a1540da1030342594076424070180f0207003003041094001d5001c0c0c80f003840365070310081d60040040000c800ca808241e125060b65401400190744100c101700308400042603090500031070480b2507010071101c502580c94183c0e55001860141003075205415003c01c511002c20000941100c00412074102d2085507800810144400d101241d0100000b200321 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 844821672 1250 844820422 844820437
    0x6040e03030f0402010909020708040909020a0b040b18040911012a05030702040b030a260706231602030f030a020405030f071422020d09051009150c050906070305 71
    0x600c03001c01003003203800103141a00e100700c4c803e99511a0266640055000340d015102c0000c04118041c00288007070343c19940300d400040d0005010520300e81e5190707030101040e8050380000d401108001007909010301950f072003002d21503003617504000c80c01d12610f44240c0b0240c0300e030003e41000741d14014210064a070b500d240280da484140c060100001c9840c103380d40394042c900481c080c0e400c1c40c459a4851402086400720b464200050b01680316601126110250300070180417060b26080c0010320100f00c00d0b02c2814210080252590198819500d81c8203400f900148032030f05580d20402c0c0211000c0e8007005507032482c0e40c1c0c411840d0300c0351900c1c15020040c0c040d075080f440d00740c416440340d08072164001031850100e81c40708c01001c1d0720f52465400d2120940e5800400701401c50550120800c00c1d130321f80c0c01484d400406400028982c00b0541d155400c0000520707a42c8825030721a01a071091048141303244040c9900c40e0410440401e0420000d44140034513003a407441002e0125813081414003a20440e00c65 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 844822922 1250 844821672 844821701
    0xa050105040905180f0f10050c031b1e0c061003021f020a0f0b1803030105031b010e0d050c042403020405100905011e060c020a0b031008030705031b06011d0604 70
    0x7000c80344402a0b40d500780322642401d03d204441c42080ca0030700e9413040d01d0180d912700d08090b2460791011110f141e2480550490030742d2103010044001c3c11680404000c0e05c8a80c903c050b5036403445181413061030a9006460300c05298200141040142d0300c0640b00c0c0d0f00d0105000284516500400c01a4200031051102400840120740b40c00c1c20130070303070506ca2485141e50059840b1000c0204401941e240001d0054541552011a00707004d02151034161231068030341403500d12154007006000c40c1c0c03010307503489007202c07076a001d00c0c0d01b5070315441d160141d014091900f000c1c140388131126900a14442603240700c041c0c001c6503100301040302d42c440d804042d40a0000c044050001303582d0b07206102c0c10b02082a1009031001061100032440c6031080340440130040d0014403c081403410070103154030692001c0c0026010440044c070015048400380050074805005a000e192250341c5040502445410a2081c00594110200500002e84045071010f40741890f180501e40e03030381c2c44002003001419010400e40d41d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 844824172 1250 844822922 844822933
    0x1030303110d050c0a1e021005040809041803030b062d0909040c08070b04031a10180203061008160809101b2318030106090e1b0a05010504090518 64
    0x191310b800b50001d01ca68030340e80d1b40c0e40241c01c4082404400e18a00281c200005800c43c1c2d20940d120032154011301e8216002e5005146040301490016088825203620b8a00c0c03045d20b043e04030300f45a01407041042c408410b41e417441c40d100c2544104211005009251a00c03200d0f200150348030f0010440950794101d2014001030130500702820011044034480c8a00340d010b106810010407082c8488007581c0450b50700100300c500003010390702401820031004046000544021100140800c00c0c20700131008101c008400603038a003400000e1000d100c00411103081405407400902c00892100b00108040030350615024046481c1c0c420380501f8601c15114601c6803500b44103007440302c2d00c01000f2039881c1106d65101c6042408508516520390f6403803501c16100d042c03040c8103201540c907202c40800c441d21401000040d000d0340340c4c200d9400720703038400c9103810099000c0b00f804c2000c118102410311035250200c400c05806850400020050301c10380c0074080003180c844002c281040b491080e14200e504040003900c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 844825422 1250 844824172 844824181
    0x60a26060f01170705060702130b03070b04180c020703030c081e0307120b0609010c030e060d0c080c0c0d0c0807050d02010e010b04020313030e060403201f020601030303110d05 77
    0x146800c020b005000d0350542c86000c010450760000f440720112480038081c0d1f030405400341c0820005190b1140d02c042095251000380000e9a401d222040180194061b9142c0300e5042c19950700180702103120340720074646003c40020a040d00001c20804407940744c540700800315160316058216025105400b0f1450402c0d803225212811910301541c032501c00c0d0340c0c84209400001c041d010a40303d241042941101080080c5050303544100c0140850303e0081c10a000d000c202d013004a030140e84031014003005961344c0c0000f122816480304c0742517080421040014200710b5404022a1511002c9000c0c6003884070708070018040003481d1b02070351080794006c4141c41e04009844c002902a0240c652400041d5203004c03151203840c91f0500c05d890244401d0000c0762607405455405030303a240c100c40c0c00c880e4821400d00001001500c0d010541c6a0301c004100312401050815080c040800b11a08450320486420180c903441d056001408504494040c41d01281e8060705c2820600107100c1d40c102210744600748030401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 844826672 1250 844825422 844825441
    0x105091b03070327030e04021b060907030210170f07140d091b0f1404090b09070f060f0203221205010506090a060501090939020f0303060a2606 63
    0x440e0308181c401c07040509142e0302e100c5041d100c100f44d0307001004620700c0c0c1251001802c05078058014070101e170400d1888540c4000f00030f460308070110b41020007580001018001c50400340d01c850403444243c00d1151410414031400744100c000202850343d0200840c00194440d03200b076080a070302441c042c024030790302e400a80610010b000346900c00c0d1615000d4400c1d43d4011494038420b801101d0210704a4044241402d051080c1810a1502a58000c3e116682ea00c003050941c510203000d03547e0302e40102103061404041d5001c14a03560f2112044c88540550401c103d60044201e40200500f51400b810565441703510761880310464000720784610206a17020308100c0c0540c8054000c450844088115980304520481540c0f4107016403030010300082d104010918140d0840040074500040300c083c601030490704810300301c1003410030026581001d180c40084a8060120214000186000e10f1551074080c000ca0030030059440348003030078481c11000342c0c481d50700b4201c10302c145400c0f0010744100d800d280040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 844827922 1250 844826672 844826681
    0xb06071e080406031407050c0304061d151306080408042903010801020a110f1906110703050304030e0409032a0606060801050307090915051302100f02010f060e0105091b030703 77
    0x142900c4501105c0441e00c034500038415200710781001c10003180307000d050800448110170426210f2040c000080e0007681e85a0301e50a40016080328450b0003500c9003194240c6103500d13541503000e5401e0141d080c0034031000c10310030012202a52824081103900a00c88403000c00c070320800500400407000080f0001c200c1c02c1e4103400400110800e030b03603414240500310724050307103c103101c01070b10040e503102c0001c1e04051100141c207025141c0c060480001c0c031008801409196500401c811400104000304100401d90486814a0441015901042141040c0e50b000d400718203124052915905040d03650001c0c2540c1d40c0701036418940c05807061000c1d942d19540038149400070701440307120380500c60000c07414580300c0c81550141038105410814105144451100908026000f008071040c05c0111070050b880c2d00083c050001c003d50764200d14011f181c0380003403c440c20400c0c402c0303100c0c3c10b1042c10400c0007030200600d4190740e821581d001c59601c0e260074241c2540d4030720b5000c0001c510040208000141c140d0711 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 844829172 1250 844827922 844827941
    0x18111b060604060b28050409090b040b0109050f040305090f03011a01200303060d0f0506070804030e0303040609030209090102190905211f020f040314010f0b06071e08040603 76
    0x40a000d0f141e00d6411180700da02454040c1040c200002e0804c01c00250401d043c0c1220303207460b06101d4039158458070302000ba203681d100242c0321800050140000c008802c08028014107503400200540d0900700409281c4000181019003040800b0428402c82e9032643c4500d4a2000000c000b0028081070404a02d96240101011800306408010589003d00d4500b40030a5084603940a14138540e20f40702080002071402c1e106983c410232500255000920401c0428060045900c1e1a030f45490b041c540206a010391244c8580241c00610042100316001000c202c152079040702c1f01c170819950310050b64024000c0b0b15862000190502c246884070b0b0304070700780000341d4100713a407241080b81034a60811401062401c428100ba03020300c0c4100888284004044103a88007a00050701e8401031034082e1a46401c15082521703010024180748042e40001d110301c4440000c9100d0622201e501400016424001c829020b0321213400010286491030460450006550b4807924040c1c41c1c584030a4002c005008506 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 844830422 1250 844829172 844829179
    0x5210a0f05090d0309050703060507030e210a030209040f052814040212010f060603151d180309040207210e03190c120302032218111b0606 61
    0x403080341048a9005003485440c0060080c9250310740600110020a24490107603181c6c000c0400103c0000d01a01410380030b00110fa03004036019501e200c60740c0c200b00503503201c2005080c450300f1420443c1c0b11030042d00c10f440198200162201c3d840740205000e00150030703004010720b00e490208000240484d480344c0c40e080c080d849260105d1078100180d800c03181c03c2c440080c00d0311045c4001030010702c3c0400c281042e0083e11400824151024032003001690196003101e0040b94490a01c4d41010440c041c04000400b6082425524941d00036058407540c00c000e03000c000d40001c500d903c811800c20800071100300700e5000d84110b642d11414280b81007000407403e85a81600600404010600c3c0b10304859414147c00401a007e103904200168002c4420410100e865000b103c038002510303480145480a8517000307402035580d07801d02011014004c01c450441425000c0a920203000800c0034940b0300f90b8200040a00050715421030710b0603840750098149003101114290b0101c0c1c01e000c000b042581c020b0901743e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 844831672 1250 844830422 844830431
    0x15061707050301081203060102010b130b0f15030f06060f030106120e0105091203091e030409062102061602091005090a2a090528051c110105210a 64
    0x1001140d10b880284141031031a8000e102d16079540c1450070045400102c140000105d128aa4000c600219540c400113803006a8580c20b05a850602181c03909280d078040754140080035000501c0a568040035103010740c034000f0400000d00340e859003c01c8981380880b40d4403c507129a501c1000911085101c4034015015040c9910101c640e9130501403640650101400703054070000c001c0464155410040c40320303540c1d10070b1182c020001e03852800032140b482c10020140d551281440d080c0c5066a0b000e6012908003001c00c0d0200b061000c1e60141095000d504403116941c070084001110ba40303441b0384001941c055100e00c01d10030000c403114100d20881e1004e84031100f159031464015002c0304c2c1c41001c04162400c000040341081007128206079501c40690900c082d40030303120710214005120a00088003001426070908100c19000b07400d210050108880d010350300c1e035454201226640c052038000f007202034a60703840d00d00380e03008000340c40c540c0000c0c071250245041d00d007125044142d000e1310035017001c5261 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 844832922 1250 844831672 844831681
    0x6041719051507051c05090d0e0916121406040605060a0f031107050a0b1503010516050705100e0106030303060e0c03161205040b270d050c01150617 65
    0x4606000c04068001c4040c0c0302c4140104500d0071140e40080c12003041181c00c10a00c2e4001008a010030809401c013403000031280782565a480c0340a46010f440c50038030040c1d154041c0c1c16568050128ac0c0040c03038030f044000003500c011055400c0140444c1a0340c0c1e40b82004001490441c2400d03030f162050300c0442d030522a4640e96014040c0502c604006180041d00341404010f4403400b17500058a440d01030801186894142e8498030f080000201c02115003020803400c0c4800b100d04013084800c0c14904600820250a02404a54440d054122032200b885404985207052041c02e00c000e8040ca101c1c2c541c14010800080202802080380f400110b000c207107042d9000c65000c0da00c0070b5075807080700220344a500d0b648924403683c004500c130100c1351080003609602c40b198440035002c0d0b24001c82c4074107840d02e07050905900c0c41003440310400e9032201c03085100d003003000c43d00300c0040c0e0b1168001c12410300c4c1d50740d8004904100c1c0944454a10002018440e080020341c1c194400c15642c211107044a04c000c2c16180c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 844834172 1250 844832922 844832953
    0x30c01030504050607030c02160b1b030306060301030209040f061103070f020c030727240504090f03050a020a050f0a060b0a030309050f040b0409140601060f05121302060417 76
    0x400b82c4020745198000d0000078141c9021f40d00488010314540101c52000401c1010200c454250350042d10f9022004201e07601502c00e501c503100d094050140156007940f07401030126102c0d000500c000f0307102d50300003c00300e014410002295921241c00140a100c03070814560403202d180c0c000c0d04c8120000303032602d44060182d440858100704014004004e00a42850500e01107000d2401c190185014268517259100e000428484e1080141c50708400c15140e40e0f40d0000c40501440d99400750f401581040c03010700c0001e000d20518109d4036418200340f915610788050803032900e290f040c401001380c03240254000344007000007069a0f02030720544e000c4c8440166002801030102d820700c4020046101c44105000d5403404074030b518441003010704006258447c0b00009019520306100075614408001c0e1030848030b10042c05418050b0200342424041040714070302c01005071281607241420b000311140400d840303002404400034456001481076440c0c640302d00348940503490f03540e4103001602c80c40806a404c9038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 844835422 1250 844834172 844834181
    0x102031005030d03200903070f140102010605180f0a021b0a0606150203070303020307140318210913060b0a022407091401020a02030d09031502031302010c170a030902030c0103 77
    0xc9104101c0c1804080c05c5c1c8003800b50000248207a040c0a5039502007080d040c0c1d80c0042005101041e1001d081e0b441010029007154095040710740a4840100c1264581040c02e5000b9000a0044141111070f0380fa011810001c2c00b4070240071001142c00c0c40d580c1024070300024482d4540c1e00420b0100b0610350703603a400303082500c207000c0c590025070028410040443d019038082c60380051541080318444e4400f80d0301c1030300c60744129a407600b00c50070411800c0c002d000400c01400042074050b02c0e00c0000b000324041854501400c640d0501c10220450041c1e2010350607003008000b800c40c016050b8440681d1140a912021065000001d1206500b010751545003c10350840c000e03035444c0c0f9030741c43e2142401c0b000e0003440140507565040d03208605030580180c40800034004e0b404010b5681c03800c80d0342507191900040b0004003104902d60b0040c814000812031005c10042029424241200090070360301c5c08040ca100d00c900303011000d0102040450150b501074100d0341103c0d10840c19200b1000e2440010340489 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 844836672 1250 844835422 844835441
    0x2040e010b041d130b1303080a0501050a140f0402030103030e1c0308060d0f0b07050a021203040203102004120b060103050f040327090204090b151207050405030102031005030d03 78
    0x88000c483c0e4040090f5001507054101c05a080140040f8800d910703109280c0304240d900007022a1454003880c1810b500400385034002001e0201840079526082c001079550350b0341e01845000d5018008903418039a54002002c0c2040030103070065440390303075034140988400d01615445000d15084080260503441100c0840c9d08568103480f4504151168410300c4494014108100d032014540b40400011800c2d00705814420145969203070b68074014201d0090030440d0a2140d0058128140240030040ea0007094080c0440c8800b2400100311110054440028500d46003d0032a0280003601241000544040030002c0307024080000075516410011001c4500c2180ca891080c3e0248003c640004d10a204545140c014003981880b804030704081010442c100f64000000c0343da0000f42001083d0031401048001c9004582d180005c40e5918940340c02489164040800340c4001030019038064051410b807400382401400031500d03894500044041c04a8034024241309101c2c0c8001c4500140c030078060600d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 844837922 1250 844836672 844836689
    0x80c150703080a0902040e10050702011d060112260d050c03041e080d151e0f03260c01020918061c060209040905070e0708010f0b070212070902040e010b04 68
    0x10740e443c040158010308070110100d038403944441584035030740c1042040100c1d0b91845000000ea605180c01d0290071aa103010365403900140104c442410540c0c045405411540e46c81c100d02070506003403400c4a04c894800400b00d0114084103244001c0c5008080a0444603101840c2009151581c5541c011180411070b030013841c070035410120704011612681d482203d1446030010381d05200f02d104506c001d445080f041c004000040001c00c01046001045507100f0030b02c0315050030a82070030151008201d032070a0002a01c041e48101d95403000c40003c0d9421604200030409241d1142e080c0c0b007e82e4041d50041880b54480c140600358803944111480180f80034000c000e081c0c041d0b581c010032600e03a060945c400180c45240d0f09000001c102e480764000c45240b544100d0240c81d600d810000303000d40030380028080504000c000b000601c403046080c0e001c14240c4400d80c103855194501c5200140043d602c1c1d071102d8000d40140302c40054080c00c1d580180003950506c4011200d00c0e0780f60003040840740170324850089c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 844839172 1250 844837922 844837937
    0x150612021311030712060b04080d052206030e0d030c050a140403020d12080f06060403020d0f050a0605060f01051e09130e07030210080402010207030228080c150703 72
    0x501d009800400d00c0c6000078000329a600040c03034400d04541080369002d003c140800c403d08880180b0f44180c502400e10601218105800c1003125039031a02414030100c140200020503d042042e030400481502e03201d0800040591b8681100a01500c0303600305049075445240b903180c4846009020314041c564855403a40d0400000c49004c0718005840010b50b011110300b0003002c40540c0ba95440c0901e100e002d11004026001108001400704a009005010f03c0000105005641d0f0742d0070b00315030403290115601c0301103030128141038000e0b00c201c0303000619a00c24800b4010404c901d50704680d10400c0120340e1480060b0064006488903c2884010103444a441115020a40b00d0101400d26040058030050304114102500c104407036246030320303600c15072129004008620708038500307110340395880c0352001150400b50f0010b552500140802842075410542c000d541040042c0c8205c206451091a1080300d980d40c0889625849581c4100d40501440328104601e82440c4044030810340d450340e41c841 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 844840422 1250 844839172 844839209
    0x18151424130e03041d09070e151c031707020a0b01031707020a0806270303070f030b0d1103071208031f050405090c04060e0112140703020901080a1506 66
    0x114112031403203101d0a940d03600034490360240200003078000781c000059010304d400b80000807401c001c040101100d20f540d011050500099421107140746c0c00c5031031b07030190541022465002800040c811000c00c0b02406820362490285544941c00c510903507443d40700391401e0f407100800bc0743c880c424a400601014040001080001c01c00c3c04500804151805c07500e040c0046540001c400707111507880782c007203a442003003031141c1c264503403801407860718502c41c40c88854404248541d8076400010302d12410710460882c050340503030081c0c000c2d0031b0030b5000074401090395403a8a05081c1c002d0391410003a001e84246900812000700c049249940c0c80d410000d02800e6507104801ca043d080c014100d4140800c2211038005400d40783e034000c09000d10700b0040070b00807109029060104a4415034084100060700da4010049400e8180c1e402d4500c42e0401c011a11010003c0c911170300d00003060f88000c0d0443c003828000501c0400202c0c5548145100f41c0c00c184654881e4182e40040d50312074007a940b01708256441c1c4a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 844841672 1250 844840422 844840429
    0xc3006090a0b13050a0b0a06140127031e0501110703020601120c0504060608010e0a090b01060e0a032010020708120a030e1204050f030f030d18151424 66
    0xb6a44840740d080c41d2224070145030380781c0d0304004400804880512000040c0414588103010b05400340c130000c00845c2d0400c00c44400201956540301510360700301d03803c40308500c400b0044100b40010b150420402ca8410b0b03125141201c480000d001d05031015440c0c41e1426584052a2044039080c607019030003414130364204040444031515902d0100c81204420100040d2911760b80120001001a42c680b03442940c0b40c442c42c0050305100512010880e840c26182e140040d21007500c081c1502c4035442c3c180e00000800b800b154102010b40c101138065041180c6048110400520f4084109001d844c406495246c242090b6030310a568001c00080743c220b0007408540d404084083c0c20300301c1c213525000c586100461031484c100300c0d040d0805a03240d03000160130b00050914000001d180181034009046c101c5184401c0c68803402441c0c060b0f454035481d070500e11040280e180090700015040600c04c03c1c040c2e040412400108101d04103183c584503550001106000502460200c42500910380710b1015011401c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 844842922 1250 844841672 844841693
    0x2802060414010c1406010311060a081504020c030c250b04141804060b01020d020d080a0203040203120c060106030b06030f0601080a0608071701050901060506040311030c3006090a 78
    0x542c1049105000103010a00381124050707414102400703401d031541141024140302c800419070a00490041001c240420340c0400a9584102d80070140c5410300b09446c00034010f48201080380085200c003140450018101007045001c8003030142100c10603444402c0024941d54040c41002e1007143c00707000401805007441140301110300010481070005014602000c1c26240c00e0310141d6443da5103200881c03003560108500950111940010507114410b454014040c3c003004060b5a00542c020001c030381152010031035202140b285641c03154840a808071410756605092141400103800e15260080c5400c260048038080d5102e01c240c00d0107030303485a00544051401030051201c0955809000070841c000340f0001c0041c10401c0d000c02d0b000c442269030700d42580d4024288080c1a450303c0c3c0308200c1c540c4e500d004c80d0120707039200200340c42e0300c0b030340c240040d003031443c00e10031241c01000c40d100908000100d03104032028000ca00300c3d0036030360000100b074150743c1d2780c0304075007400190f44044100c2d400309440685 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 844844172 1250 844842922 844842959
    0x7030e071703121504140c07021509062113030c08070f05120a170105031c05121003060e0106060509120c060a021f09081902010b09040528020604 64
    0x45034070b48001000c1810f6085002c440d500340c54983c1c80c10010781841c01d80211044030b14042d43e60103881c20003d400c0c581605c25414028030480500004a0028801c0c8094503400c00004240c5511100c42d00d5443c0041d4035142c01d04030070000030100180051020106146c10700d601030303561400040507a541d041c2c5c1c1c3c1d0f00010042d01c1e0946541d04280c0011000c101e07a200360111440b00644070b45081802030420500200d4850350301100c0d0b4018440c0340c41c0010412440e0303d002034040c00b051001002038a6a03c01c228681500d007007480c0811480305548580c44088922a0204102d076820803684103003214824090b1100091003089a99160700d0000d0090080f00d041005503108401404006401a4031030545100541c00507240010f400611003003400e80d4030f850580600040200d0307540c4070743c980324040c6090180c160050706406a01d10175070282603841000f40800384070b4201030130541e68039401c03010202e110717550b103c0d02134005c10943c0e544040b49c1e0768003030000340c2042d0505d200e502141c031b900d90 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 844845422 1250 844844172 844844219
    0x90f03060506030309360402090a1e0603241e050a020f04120605011502150c07062318070504181203021c061511071706010e07030e07 59
    0x300080142d503a00c2135030800400220a80c40078003c401c0304408081020101745000903401b0801c100260301c40000d00b45e03211119010000c0d17100c0f070134601202402c4280581301502842c1040101c00c2201242c042d12141c001c084c0d01081c840d0003c03e0700c80c00c0c0c95410b0045440076500c4c52502d1880310081d00056008822000c026042801e111480207164100d07a0100d61032414521036a03040c0035561040f1805441d80441e80c0c5003907454804042e540d1103181484483c00b03602031740003d00e9001c8201c1500c0405610581c18802440d88021072605040500f00688c45a102c050118807030b0310082c625160740042c240c0103000380c2171400c41040300504840e040090b0070213200203407000089850714280118241a200140c0322201031160348008041803800b013885603e050720600c030340641c44840041c07150706490a8038110503400901410140240c2c07003540154151185140320308804111103050703c0140c0d401c070710959078541c0308030305503001018078014682043c03400740066000c4450f440c1b810015035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 844846672 1250 844845422 844845427
    0x3030e030c150a0c1107180204031a07030e010b011b0c08030a0f120203100b070f08030910151d1b040f080606012316020303030705040302010807090f030605060303 72
    0x10204582030924000141c9240e030030300d008004540200e846042440d114924117100c840684020180d40c8024a019108401708142c9103403400070700d580c04580156600010981400a042e0414612010305407024000700341000d504090342e800520801001c01d20594503060b16079100404011541003014090b546d00c105490301184a180030802400c01900950300e50110300300d080f40003490004100c510350111401041448044c106d40404001600d5102103183c1d40d442c0c840c6040c031840c0944241c020301d40e172404010040845404101c504ac000c982c180c050024a011075041d0b90303409024003aa201450000c2044401c10002a611603030040005883c0340c241c081d05072240d0ba054009074000c80318540780103801c2c40444002c0c424a0b03040070080c01c015940c10003022990002419a4204006560300031401c51501151010849085e03038000e800d8945d28200703201e0040c032a42c8a4007069012400400100310880d1085040d00c046400c1c1007440001d04d820765179040c0141030068095035152206 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 844847922 1250 844846672 844846687
    0x5150f0403050a0b07080108060a020a0c120e040b180411030f0f03030601030e010c0f050d140c120106110309100e090a0e0d020705010e1005130e0402090f060d03030e03 74
    0x140001030019500400c0108a40d481a2911180c2480001c00b1101000b00325130041000d024009030f05130700301614080150b203d07040403204840e510b00c2c40314080c0c1450122000e90b900703280c006009454280381620203002c1440e00100380070021566204102d922400300000a011404a0540300c00e202c0c801004d8030305240402002d5032504aa058510341960800000d01081d0740e018800c0d44041015078000b406000300c2214098065544400306105211002540e0000c16030140e04c01059128964170410f06801c00d00207802c8103803c04a0f075001120039807000842c40032301071101d41050081c1c48005501c0c00e003042d02804180140405c004050244042411400d6912180030502c18a0141000114420342c900d000d4a0300001e440c05c0303001d541101d50706100710390f445104249801401e42d1902200c031048481200c1c68031400c0701101d98003000d01404141c00001c10b00742030059000f11520305003a00c840d280000340610660328160300050f26620f000000b8026040165410800000d59090440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 844849172 1250 844847922 844847947
    0x90209180a0b030118020d0b07111506100207120f1a0103060b096f010203120411131b1e02031c0612060b031b06040515 53
    0x30039103414040586408004590b420244201100484964000084440150082188505c0e2147c014261030180c80024030318501418010b20f0192064046803041c0c0000c061a031a224002d546152050000c0210400698030010f2903105072000076100c1030341c2e0000c50360b841d06603480760b0104031481615404100d11203090085098002c50180c038000c1017000038082004100540207025140c0c0c85441141c40801d41603450028a030880d902000740d45198912403045a0600c00c101c4520300d203100c594a130080c2e2040d800394061102c00a500e0600030262032070041e41c0b030780070300224400712001800015010500341c552403aa030030380c0030b42400008200c00b1031300400d55840d42c82c0701d000c40f0351482c9407001255116801e918044030200b04060003940e6808002d44910602600c241401c00c05000c0b1034002c05144d00410040034000c3c0114a010520314081026010a803160303031107802428443c04028114885c101d0145000034111b921301403c0c01c1c10820300d00d4556107880028a42030145004044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 844850422 1250 844849172 844849219
    0xe060a0e06040308031f060f030207140a050d090e0106022d010c051c0e300c06070305220311121308070b0c0d0e15030a0501080106080a020a090209 65
    0x107005066031aa030346404040d0002c0c103480e00320704d50346d100c00d110420005e07190b225000d04141c0c269894096654440350421603404008400540d1751400740740044801c000d0001034001c1007030160744400109969440426094800910800d070160f007100060301e5503851249092040113040d5010700c2e51200362041d17004c1c01c490324001104086000003409a21415440a11141c6640015410300c0404040c4025945640c0c0070151000c6001e40b9000f41104007001c000c410700d2920080821940742c05030401601ea032084151490340c0070070310b02004a0010340c0d00640c80346010031700c01d0110f044c00c165581c044400703528206618816004880921441c4d1442c800209490008030f2060f002041c10190487c0c01c00c0f2141e80300000f03008082149a11000c1c000c80c0000b004038003824001240d44c2d001d00880c1030f08000070000110000f00004001d0b08000503480941640d51540080091a8441c0c104aa90712090f40000e50311148079001003040b00002d0b0010b100c40d55010346000d10140400d6039880010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 844851672 1250 844850422 844850429
    0xc0d1407150504050f010902180a2a0905010908060415061502030403290c03060f04020703030e07060203040501021203090c0604060c06050609133f09150e060a0e0604 73
    0x1e619502071006010701080b400700540c1002d0002c000d80324080e80014855030640d401c0c03901e0031b900c0c1c800054910070300342c0c03240c80d00200d8070040c2a010000d480312024018000304200000c03400b0164007051075403040b11040c060721169001054180c4564030381407000b40c80c0182c04030490b0313101c0202003152070f07250f29003014441e8079400654a503400c0d0b00c0c0c54108410700940b1101c1022841903d2101d990888440a4200102500880e540d44445005c0303100500ca225503190000d000241000c1010b5166010788800b5640c4410360b24010717190f40d0200c1e124401d0f40308035801a44040010000c1c0b49150005540241c81c800c00c03202018941004217000f9085640140003042c5101045014000c29005099102034200d50f1000b981c94182d8a4080000541e500540304018454400c1c45103c03400c0c1074014264282d50301526030034840041300b0318080c5181c6070b01000070106040040d05814003640030048400507111204c0785480322090201c2e17500428660020003081c00924080e0742c44060052024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 844852922 1250 844851672 844851713
    0x9090f06150e1806060405190302030717060901060b1b011401090e070f0510030b010516050c0a090912111f06060905190e190e0309040e030c0d1407 65
    0x182c14442e070803c8030411004583c0007007981c1000401055a40f824102c50075640c0450b6607003490140d211017500d01801c1c54100039014858440d011529046007680301200003020320841e001d558400b02560b00f40e0b10a441510020803040c841c101e00901c00c3c110744651a401c000000031940f07132007450300a04180030b9000011156803010380358500341d000d0107180040c1c0940b40c95100503920b0540850004800034401001b019582c55103040240e124004480d40a421440a0b10340040305041c80c0c4e40340c40c1c85103096031042e2001000060b001c04640146c14955401c5103205200d02c0c24400c050700c522890303034486c0e2520301482401c52104034100703280884201c1100e0f40010b0703150074018007600080594000e18403074101e6202d0300c4560080c21803032206803100d550034801191110300140b01080066800760701f4403401c2c5909141c41000010280408540c201c800f401002032480700c0944a2040b01c4412580da080a440695028000d000049002c1c2c24403501510b03080d07107030316050410240180f49404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 844854172 1250 844852922 844852937
    0x9051e180403020705010c03090e100902030907081b0d060c050c0a0507091805101e2307050f19140706090b060406080c0d050c0301061214030a09090f0615 68
    0x30b0607070411407000640300c207081004108a090328081c10501281c803c10180f440300b1000102848180000c0c080100020320040d0f40700d0074007005058485065016540c1070b4440c1c101c07004550590010880300040c00507265000f0307290742d03484030000341000c0303010441071140070084020461010090841400e000310083c100c140e003422051811369030340003400c9070011076207104500401c13808036203203034505018100002c444017032105424005d000e0400c1c0280442c50f00c02504280002207081c110f044156140307480c5180e541c0402034409011707502c107000c50f04805000c160701400300040742e400210701905200301c2c2e82c0c8003040019290743c003110044031940d448500e541c08101078a003490f90003070000c41d000e0000b14140724009036640200c44055203d07802c52100d6005110040c07000c0d008012002d4020b0203941d440b1500080584441d020484a40f142484c0300803960703001100742c41340f803031071580c840c29014640f00d45100a00302043c03032a170030159541e0340041e203441c08840d51a00e045032a1038600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 844855422 1250 844854172 844854181
    0xf0702062203061b0e040f1e060303030b12030702120304180204170c01021015030f03020f12070305070f060f0e0106090e070e0f04030207090c08060a0503010c09051e18 74
    0x40070344800c40c80b84e8003034007100302140400d00d4100103d2503107010305550018582d00da01c2038090252074503c508008002d0a020030030b11100d04c607000780080c0c0c1d020303440c10b02071640701e6414000b550006180c00091394205112401c0189803240c44010301c141460304a0f410151240d0104e00300702c0c1c6070503120741a244c0c00641001941c039000303c000c01e145c00c03504c0985003246030480041c0d2a841e030640b41c01e0801e07603101034004584d102d4400035800740da04400c4036000207204d4600a0750315102030381552124468000e150b41c6103007592045482c40341e81555001d06280166864441c1f14880c60f008807001c03501c03018001c2219000f4454003018402000000c501c0030b1400d007541c804c440520800700e070150010b05050140d091500160b54015606110085065542d824224108036481d000504440e051100d443e15803940500114004c040c225488441c41c1c0e40c0e401014201e590750f0b64040040360400c0340410580c507010600c080130540d10700302002075281400001349104064200781111015030360031701 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 844856672 1250 844855422 844855433
    0x801021911010b18060a030f060506030114130602131508010303080a1503020d0501021c090b1305060f09010f020a03020d1103061c11180604140c0f0702062203 70
    0x51840d0481074020041d40042c030010503029400301420071070740354080001c6500794a81c10310320001141c0180ca5810204800e2400202410055800728070a41c20042189034040e007110400d8000d2420105034601000165500000382d0401c6254018250000c04c00040c8032450f25522216140391b540e03042490360441c603001c0c0c50610090510305029140c01011a400b10f4001002029250115038922010807585002c5000e8803940c8000315820071810b00100c801d15145e0058010302e44110003201250b41e41803404400c079404070300090025484030012420b0750050301c0300d99030401400c0c00041011811181281f0a0342d04c47e80107100065800120800385140c188654603405e031805000c180756003060000104080004e0104032000141c000410342001100306010a00d030801801440400601c280125101842210441c2c001c9081811345401c403854111020300c0780740340c018003604145480541d440c1540062200b207800520822a8940410f07407041140c10202555200c03030703220350440c41d04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 844857922 1250 844856672 844856687
    0x1a0907450608070516110a080d020c030313050103050403090f06111b0306041b050a180e011401150909021b1203040b0406090f21090609030203030a140408010219 71
    0x41d810080120107110140d6401011140f00b4420180440c1c1080010f003404000c0384000300400350b001c94032000003d4450004101c000c0400e4840c1c09480d40541b4150916847c0c3c440da24100f0b08100400300180300c10740c020b41c09141c01c00e00900d4111810b42c2c49504040840c1d840703030030801c04a0b951441c0c03c90301e0700081020b0301c2501240d08200c2910158240802e130340d07410140000308500c80000304020380c0401c211a8030000c08008203001c4c22140e4400944505003480c1044003e514100800d10750b04140500601913001051034000800380e00e0b0030340010b072000750036020340d040050344030700018100c0c10360020301003094440d14012042c001c031781010342ca020010310303102d03c111005004000c040b8114003209a80302da00641c01080809031840c3c484044d0f081104e0042242209410a00000040203141000140c0380d4461180d134544400c030648030b20b0500e100096040c1d00c10801c680c0e04500c00d041d40c050303070302000d00d0140c20903803901901c07800c3ea0441901401a54049025100c04660243c00d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 844859172 1250 844857922 844857929
    0xf060503070f080a080a0210111c021606020c01020f03040507050316060f05030a091406150a0b030c0d091403090a091b030b1507151a090745 62
    0x71264407503241107000c6444e020420b201400d03c000204981481c507000f88001000c002d4191320410844c0d5a49000034284c4e00200d040307020381b00780075080e2031707240040303201305c0c0c440704421706503406025101c1d912030300698080004c00905540070b12200d903400f0124000355000e40c0c80307003000d008900d003014181450250070924100101c140f14108100302c5420510701c0b11821560310b8260384d60303910001380d180580104580102144c1c4a400f42c1481c0c08000b107541030041010250784a40c2190715410003001010768040c0c04140b44041000c40c104c180f888000b00103050000802040d646010b4039850521182844221125003000440c0d00d46450f0406016010304022541000302c1031007103020a00c2000116554002d066989040c5a003940d80d411a02070020f00080a4581d10320841c039015141021039117282070007a052200303034070840108003190300380e500002d00405600d0f03640300742c1201d040341047c2c5092900441c08442000b8481400c8640c2e10182c91000c2c1111102e868034442959245540d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 844860422 1250 844859172 844859189
    0xf0c05031303030e0a02121501050301020a021b0d0b10030302250e090f1207020406050603010302060f0d0b09011202120c0f150c1b030f01090b0a0e030d0f06050307 72
    0x1040256140e0071604681140e501850300051020f88044090b10340822294040d42c132a00e050912009404009044420380e0201ca01101c1140da0703d009040c240d018032942c020158004400101c107400c8010b400c0e614940c0001c016212242e038136240c18440080960301804002c1c02d00d013060040c1a01049010701070302c0f6607400d04101900c00c0800007221f000c54003802c80403002801c0425000c7c0c0042121100340c8410206545c0066001c82d030311717501e070b6104000882c055400d10b5070000e100d28001c03050b41e04a07500585000c2c1340a0840d008069a9030003002210805607903a940c600e00c60303c0d0708000902806e21060807544210749401041070f2502c02103d07041d40b59010385802200340d02c50460400250106440070705003200990765454082c050000c211740c0314864110003072004d51b895464200c4058055058a0400320003200003800c0c0d402d420382c09001003030040086003550b00b159004164003009a070940b41008400410070003030750340a070104400c1c0b5850720400d101c180b6050210000401508 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 844861672 1250 844860422 844860427
    0x201020918040c05100c060606031b051c02070812090c040b0402031006140412050a0201090b18010c03030603060f09060609090203061314030309030a03050604061d0705040909060f0c05 81
    0x1583c84815100d1640200780c0540340c09104000304500484a20320701c02d9100702c061141c1a00c40800070002c080d141141c2d012068014001da100b503001300e0859031800900c2194881040a4407030941c0a54821401245d609100304002d03030300365130006032890080782c2400161070100d10800c10001a0345100000e10f100d1441081032000f0800081400d4045901c642804901007000d403500285c41d004590004030404411443c2d2400c01501050310354a29100741c0300c00744442d40f9202c1c10170341402100b80181d019006c0000302c2c05c0541c02841d01034562442441c020512940301da4807902170b11300707005500004540b0f440d10502000218050807014010076481000f54192940000f684d03402e000d0040400c03901840290818842c80d401c4041c603240340b03201265a07030b0030711002665a90703101390748040c00079140c0000700f2500e280c24000c110844034103603400d100f0000030120003080414054000da003401810040080c0072a650b003e030f5041c10b8010580018101501440c28050b106010200310801008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 844862922 1250 844861672 844861681
    0xd110a050706050a02130305060117060f130c03060608031902120904051902030711010606030c0e0120010f02120105040c0512091504080c160e01140307150201020918 73
    0x98107840e4502c0d00b00b40046690b88441c2c1c000c10080c40741c25000d41c000441c0540110900c0f0002503124103d401080c1100003803843c03000c00c11f44845040e02c14407040500345020070032007040369040f02c80350360060311040345082da44c3da00c21303040301c03460790010120340c1010581d0520501c01d1041800060f0007400906549021542c0001c2544500c858141c400c0b035403000800c004003006402e0340104442444210364906040d0009007500f5505c44d4028080d60900f0b401250140c42400b92840141003900d903140180480c20040d207001c45654517100c41c44022508814501c0d10034010f030b620340d40c6522801a40c1c0d4803a08003000110405030021030085080c0400783d4074a5501c40101e910f2842e01d44c07803d81e2680c589464090030311201d030022004964942c400e11040c401c88400030500400120210341c100d462a000c03810705100f440c8100f036400c0e44204010880c02c89000d010050202e0020141c0300065100c0080d52a000006144000180c0d408038184915003402100c000e04c2841100307841502c0e151 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 844864172 1250 844862922 844862927
    0x91a040509072102060706140109020c060103030309061b1e0503090601090c020f030406080a050f06150a14030a0207060b030613030e010e0603090a0201030c0f02061303020c03070602030d110a 84
    0x641e849000c0039102d03c0081e00c01214100d50b14000840c1e8010515550b0709003500b411409015000710541d05401c21070000031b071000071442103035a01400280a011644c0c070b0340c1c40c10381c0100407d450903100c0e251941102007428130150641d013440c02072a00c8941e2401490088001480e20014014082c0b1400f0000e02450b0000010094110b50200002081c2040340c214100c3c10f0103001c5003210090320000c6000f10b804ea0f00710040d41e100e0100000c080207165145100300d1110750060b10000d40007a0450808499651402c00904032070400d41050103000101c46030341d0010b50700454512078543d50118034441040402d000c0c051203810200d0040c1420304041c1da0700b40302241003410003814080c032003003c921142d02030481c44501900c000c1c0f44a40b64038207484401c0d250b07001c561040b80000c1c6024081d00a0314054180d018820580d0780c01002e403039540e808100e258054000e004d4081d03101b150100a001d03501006804060101035020f1501c6035140c0c01d540d070036144034034091a000c1c5070600501c070f00c15030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 844865422 1250 844864172 844864183
    0x809092401030c02121b030a030c02010f060e2e060e0f0117010b0703091a0702030136050f010e0d02010506031c0503070e0a14090c03060f12010e07091a040509 70
    0x90107400103986d1501d49a005400055102d02001caa40c0804651041595059070140c01108120340090094242000418040700d00c01e00480f0340c80106800490325548000305060000010744521180484000c03c1c42e1000b40b40030b90000002401086a44900f0b0400c1c840212000100b0f003041c00403620510044c0103800300c14092100038420100b510790505210f03088520003002d9113829441a0140114071178810340c4040001c2c0cac000e60801c451020001c0c646000c1d0500590030308403d9443e140303540c40c064540c0550020a8601c1d10030aa401420f0324020310902d04d16082000080801692180300a030039036000901d41071180c1c06c6001c1c4052030107822540b010f00c00c00503103003159803070369001c00640c3d5500144030602d42103002c100c00410311911128803e0948482200d40000c0c507503c0810307103000c40c03104464843d0000d403100400002c9050440b450b18041d0510000455001080343e40b403481c0480d103500400300a62a8401d820419100140c09041c080050f070303003407025141c0b0f600c0c22591503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 844866672 1250 844865422 844865443
    0x6030c030304080d1103040e06010807033b060c04120f05070f0518090303070507030219030f0e0402032e12120f05090306060906120a0b18070608060d0809092401030c02 74
    0xf0bd851000a48101d00ca40e0040700d82504104c4d8190399510850580c001c0e030081150f01c60030401e08074150304e04e0802d00107100c0e440b5049407034100e8a03085c00c10b10782d900d00d54200103084035011b01da002008009001440254058a08071342041907003454541041000c80d54040c0f003030403680e11a8180032175103501100b200e40c06401401c1180d81c0306800c4c5003ca250220000da032420180d01072400c1c1c1c1c20994084032540150380140d41d07070b0041030424410441203210984041d010354003242d0030250107040c400018004420800301240350f20b607840070054912003014004403041c0885540036110a034000c0200c01d420340c0300e03140060401c4115000310b0b07502c0c08050001445140790340300040b02542c64102c0c000c0481201c0c02982e40302102c0e03280150380980156101d694505410203801040324000600c0c204549250395084441c1e1540000d000c200c2138440340903a21404104102c60325520358814a6018614810300b01c0100300c051443c94161001121a642c109400e25084613016580000d152401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 844867922 1250 844866672 844866677
    0x90c0b12062403070c060f1518020c06150306070306050906040504140f0304090c0212030403050a05041d0f07050c0703021314040c031106040b040e06030c030304080d1103040e0601 79
    0x4120074214442401490a241c02403020b0000040182d840c0d4000305100f0118401ca4081c01504008004042655080405a0801c044101c81040210a5400100081051703003400510300503170780b40400c0c1800b41c1151200f0040c00421315441880c2010402164415881d103001c003e100d041c000007403c4000301074141c138400c54444002c6402d0001000e41802004c2d00303901211140c1105603483c94690b08148101a816850702d0f100c03030381450000c01d51100058010444038550360f240d80d8165801d0b003104a075002003050600c80880d00d84007410072f16080b10f41018040c519454426500130408a0080c0b04408011080c045c2d00d201e031324001919000d407507048a2900003881c0e4400c540c401000e00082c241f1500c20b81c81c0a0005006c181c0b0001e07001d80303008c0c4505d040c28110b03020a0000d644520322505c00e2a00782000f0400c4007900483c070460300164018251215803400100081c40d40e04550400c0e682038000c01c00303004005070803030421102007513140051404d00d0303d402d6603c1d2024a00400781c605 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 844869172 1250 844867922 844867939
    0x4030308010f0b1c060f06110601240c1403070b011707050604060f0e13021c0908040909080c07140102010b030106031101180f0e0708061c020111011d01090c0b1206 72
    0x102c4c81500d82214010f4050406070448940e81c0b198028070a01ca1044190014028540042a5020f10b107051035460905000002001c20121104698a104002c4299280c1c2d0700083c0d40022038105100070801c040c0202441030a550403c41211641100070302108040c3d03200308400c11054442c0001d030340c2106c02c903040a900d00c008a140a461007522080b0103907101e02403d400e0b034140025503000c0d011007603070350b007894802d1790705036403124100d80000c030000c0c00c0c1c1c175030510042200005030307004080210702c904882030800d5805005241b9044440d00900d401c034403511003140655a09100740c1e207408000f01c009100b154615114804003400c441c1d290741c1005607024030361040e5040b55005c00b009042c0c24500450241d84c0c3c120096901c901501c82800290b4500d0100e41c092812050013080d60b207100c448554252030030b500640e01444403402c05c400d25501d03007640d204081d0608105001d10030503d070002c204810710780344c03107030025032190404c0300304038030901c5503049144000803030b40d6201c030040e04c5142 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 844870422 1250 844869172 844869217
    0x2040509030906030c0d0c022109120a0506010303081e0103120903170301030209060406031a1f060815010c050607030b060403121805030d0f0e1f020304030308010f0b 73
    0xa0a502c240064190455400814803900c801e40c40000c200011074000100700742440c94104070b89900924102403d4070401480170440440203000502d403142c0c0052028204265204080c1d05015072820140c0d0940c04c000b0040007410b41003506281c3c0f0290484002c9981c4c1c1e400901410320050600010b40244c400c040c030560740707900518040010303581142d40204d101e402c070340e01c05e9615442400300300d0140075a040403400c80d00f40380c02882c003626408000060020b40c001707807440340d245d0f00038464103012500442103060340b030340b018500014140391b6071f50691914044070f800300c0846c000c00c0003c1c1045103aa15400101b080450750a421481c5403030089100504400000c1c003238080c41d0009000000710340700607109290806030507020b0200c4e00380f20b04006030751202003649074550710000d90041a0308141144601d84030758a84a0a11402003400030060382c1c07080009600d00c130505245001d80c1c0000760510a06810003203a5004020800c0551070481c1810003800f054003514049610780202c149081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 844871672 1250 844870422 844870441
    0x150305040c03080412060c0306050a031212060f080114090c1909021c0b03010e062d04060e1507020a08090102011e05060f010e03030708090d0f0308070f1b020405 71
    0x700041d82c00a040c1900daa842c4d00c0403900c000810318086800915005a01d82101e0088c0200c4c011158010b0010a00d90701d59180c4603034400008603044200264441c0ca08901400c80c401c1d0005403281c030206049207401d0002c0d06003100c2420f481800516010000c00c0821240000c80c011148001d03181c40101000c818010482c1150750780100c0d50050011822074242e01c0ca503410541580c0c11810b003801000c400c8000d0500b203640c0c808101d801a0071030800152038540000310b40c9028420403402c80096031120448441800c401d6401300c4100da2500500f20b041e00c4108001904040b0203001c804260900d900701a6440500910050030102c0104000c10180e00030342c0220000f01c0040c162004103034145000000900c000c5614611a0b128840140083d5205800b01148000040d0066240c98125180c100040d0080200b00703a11490313003042080041e400440c040c005500c2074480d1001800c0116020f8035495000d490f9000300314080d001106260804203000302100d805840000e0710392940000d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 844872922 1250 844871672 844871693
    0x70503250915171617100506030a0203030c0a0210050f0405041d15180a030504051c0c03030f12050402060d050a0b03070810061a0301090c03230f1015030504 69
    0x782c1c01e030840d0840b541c6260700f40410707400011400d244030f42c04425282c410300035400301440d00829656020b580b03240500d017030590000350480d800a041300c800d0000c0c2d50009103960b00a600945c20790308032141d440c0860915041c100f0070041c1a04001d0708148229140c0c06440c080d600c2114401c585600114424032808410201230084040a807043c036080038040c0b40412400b0341c0d03141d211920031904004d05403000b02d00504d489615988040c41c0918110402040307500d02031202d15030200c018070883c0006e6107250003100031442501c480c0f4401945000c0500120515541c010f0400d007407400b00030040e44d03000d00f1200c03491100c0300005065214041c0ca20024100000311a4252080e000007041e0303040002141d000400c0b40740d0f014400765860740c1d2807034070300481c00301240111002400184480700c456048201411100d1400040109049100301c0007400117030440212142d1200500008120406e9a15409041107845221030b91410074903a8a460580180740d0800d542d032000b180412660100717 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 844874172 1250 844872922 844872929
    0xf0d110d0c0f0b0a0209010e09060102030405150409020a170c070c03081624050603010b0d02150c03160203010e0708070b071110030c081501020a021509040509070503250915 76
    0x4a03103c09107000d0300c3c248029130181d14140e01040c0104a900c01518040070200d21558043c0d0140d0f0605e4030300418424070b43c1ca0100140c2420134103010204100c0d4051014141d0801103540f40c004000d204000c0711810400982032007605041000900c0c0881c0000d64080200c03a48040c01c207507a82481807001840740c00202000f45454142c1c4d40c080182c504282d03074000700e403244010402aa40700d41041508940660307008941000000ca1a44050b1030182c0400e0380701003201500500c0c20f0600041c0c81c2c15680003601d1205140710100e850419401c00b481007400c2041c180e0000c0007018140101103582e09424440c0301070000002500301c0070080e50300007002d200c81010b002d1440c01c8003160000703005840a1045000000c1c10080024440d02c0945000001514181c011b01444005c0c0d03000e2041c01014103480015a1404014a034820b842c3c40c4110b030b101e401050094103209040a04040c1841c01d03510416072108110b60304100716062030b28542089070070380900003c140405420313482c00f10b4010350 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 844875422 1250 844874172 844874183
    0xe071b05070e01150804110f3f030a08160e090c04030b241c30091a071406071d01110d030c090510020f0d110d0c0f 51
    0x28001400032980382d0300a0594045113500720020f424658103ca030010104c40c00340558283c1c00200196041c281585000f0f0340000d0084883c00c400400391301e030881e4151007042e14229004880c850300da9800b25809400c0c2a079031020714501074803000010b000c00005000665001400040070001500810b50341052000c003500f418140d1911044d40041e68020b88010345120035250002844001c070a91310b51040941e85484422003049102030207044e07060304001141e030120310342c5143d02141d49002c6940d0140c004142510f80c1c207032914003503003460141011031414440c0c5280144999407001d0310003840c1203035140b20b080d254030541c00c4c80c912a40890542030024065030042c084401d03444803824251940150f8101c4003480854011113145003000f4084400b07030084017500002c00d110740c200e00f00d01e07901343c90003011494440000980d01199841c9100c0564042800c0510702d55040c04201002c50b807900b043c820f0212403581054032030a140c0b00d08410480c649264808025440340e040d0b0300980c004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 844876672 1250 844875422 844875433
    0x12110a1d0d0b10050607020105030a2d0203090c03010605150304080d020408071d0c090609040e01050a0f0614031c1103270a060509040f060e07090609080303010e071b05 74
    0x2e042485111009907001110b82d1803007000490745080c403400b105c00c880d5042c0c0d40c0381c0c07a50340e844e243c200c000c0082480100316250340020034001d00a015031458000b180d954401030307072030620f07096551908101c49079042c000e0b410b007401080700f0750307403a801800140f007290341c219a26a00d070700d030141542c4114a52000c00b10710206000c1214080019610265800e24018086955243d80d40400740001107c08031000d5030204071700a043e0500d54058518a0005003010036840c400000c45802c4d64800c46100450595420046003014a207001fa000100190444014684000e0020946454a0495203001d11480c940c12446884c810041d42c1003591500e0141e0f03899003015152841c600c4003070504070b591440d910040e0b049a2030559900d00031100745880d1103207441e503200d09100142000d100c0d140e178107590741d400002d43c4840c181601c51240721955130340c03c2c4143c00c1c10400381c505102d0381c022aa0f0f036031051006019840002945640000c442d041400711185001001400520504e00c000d0041c004c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 844877922 1250 844876672 844876699
    0x60e06041101120924090203010609020d0623040b0315010e0a050f0702100e0a06060e2d06040921110d2d09030b10030312110a1d 57
    0x1007141c10030101d00999807440854000c100480030b0b50070b01140070700816816030140c1181c141c00030000702204480d000200d0141d01790303000242110303e241e210a0300150002000407000c0b005108070f00161100c1c00c0001200a01c02003c5254a21200041402640d88110302c1046e80d80800032590003080c6800b20140c2076031103c02c071184100e8152000980c007814800170440d0b08901e2280184a200f1741c2c0c1c010702121842207040000750114440841180c0205455203001c1003040c02043c001c1d1090100d02ca40d1410598138544980d4030700d0f8401d0500044182185008141c01c107641a0448801c88010403a003003a41407144000d0000d4840c0828810700c407844104190300070f49020110031950040e03030441015418166400c0400880c0307504c4201c0c61a040d900080032541c0c0408001059103085d048094803991900c6900405030741c04112640003c0d801c004156020f950700c034030341d002076900784141d0072500c2600417140120700140c81404070201d00e2810140da1107100078a80c0c01c008014500c003a10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 844879172 1250 844877922 844877933
    0x1e020c0427081614010c18360e03030105180403050f0c0304171c020c060703030e010e010e280804030f060b0616030315270608010f0f0b0a0503100207060e0604 70
    0x152851074400300360880103d11032080510396080840740c1c030000c0711040252103290b03004e140354601e280b00c023440c1c0d807484014400f01041c0304501941059000442d941c2d410304081041c040d031000d900351070801440d0f08000c0041c6d480000c2d81c8410b244950a140c0310303c0914030340b9080d409a42c000601c203007101e0440000c4181c00090f0a041002c0b8954010512120020200c1c1c44007002281385802410820030100000d00c0382d4030104d4816091800010300748002c040090a50f900b2103494200380e481004007440503008400d84c04500040640070302d5480801c0d40d9158460b000d00d103c05081390010070000303028462240c102200c00f580050a460782c5184045130b8440440d0b64000980c0000c0c41c2440c1d62100160840b4508141e4144681c0805032080d46065101d54505103020480d00e0b64642c1c40c000f848101c240280d505081c6290b1002c82d24031020450f40c011106101d10b46882680424001c103c2500d01007502106603000085c0507945c4c5205041030310142003903c103072007010300c50481040148034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 844880422 1250 844879172 844879181
    0x1109060331200105041206061a0903070f260a0501050a0204080c01021f05130b092a010906030c02152d0906010e06011e020c042708161401 61
    0x912a07040102c001407101c0c01e4000482d9455405408507408000901c09400b44007000d01c1002c0c4190760126946490700001c20110f0035001c049820300030085050109490f050081d100905690582000e10624100054000340c42590a08c204262100c0d00000c541c03d083c0600425250008001e20050900c0c1200c40006c0d40240b040380c0302401b0b01c46100b00e00e90320100b2441d40c06021441a000f0000400210f8401817034003608024400f20400c0144000601c961300181c801ca084501801c001e1604000701c8010a10b05414480000d5030b41d06503410f140e03040001d040980d221440d0001c0c0e0140324003c240d1400c062828003400a0440c032041002c046034400310351244000d01440701c4120f907510200e011100358261740c0840650025001840340c2c600c1300a0641d8001030500d46006030b501d08081140604120110010058004000d6095981840e0054042000040c4280e80618039043d1494205683c80d04d8003c14000b0b00003098030390103a00e40e242182c110341003072a01c010b41820340340e0b081c000e2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 844881672 1250 844880422 844880521
    0xb0a0302071221020a021b030c0904030804030306061e031d030d0603062403140106330503100e1f1203021b090c0a02120d0b01020c0411090603 63
    0x440c3c00407580080008500036284080e07500e40007000d0143c1400c55107400301d2000c2c0030a0b44c1522460005103125a6910781c91070245000b502c07510b0290410303040080036500360340c1003d014440c08042c0981e58000c0c0d080d0a40c0f07103580030b22300011801c1080340800c914481142421580b403201103a500d50307408481c0c0c0a002180c0c482c680030000b8402d8401006000b01900b040303c00e1581e0214030400c0410052464616079042d00030000800c103403250650185007250242c0d02e020304030703142c04072003455030a401203107005000d6050080c02c51418081c1030a071750704103008404103800e400c03021903100c410303c400001c2c2024414070341c5034080751900390712490703070741c41041c1680184517440540301072108030019596080d9024000101030303034821481d00e8580d4003403c507030011441031614100748104210058030f1100f501c00c002061f0b0701e0000b000240340c0010090030340c0c82980b6041818a01c44070010480e802c500090303407565120307525451109024100048901801030314100c0182001c05100035030000c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 844882922 1250 844881672 844881707
    0x1605010c0e030f191b03150501030210031406010315080f0a03140c0d0503040f15150b0903030304062309150a1b08060a080114010501020123010b0a03020712 69
    0x1040751640400d83c0c4031100f1a0700b50004010302d420101040d40d6145c5401141d11040e284170000f03070b490742c17203904d0a03a50101644015660784014800c40c42d2108044281d000d06140501c50b200d00c241008245810203414039060560b190034250b40e111186100c0d20080822005990014100c3e04009440b00c201c200214006004007851a60100000040e00c00b540f410b54020440400b140c1000d46003903102820a840030f0b1184800c8000161074200060042607104102150110054142e1003a0b05055044410941006c1c0510039003914000150303a44a60400c07008500304130a1205c10130410018002c40b01e0985041080080010000a00001714017000c0b40705422590b0b001c1c041800c5620180140150040010410b120301d1322580030036820240c01401448401c2d0b5810702c0351300f1540e0707240d07906205c0c0c22140c4c0100065a0203115100c01d00008610045e4000c5c140c49442c1c1443c0300502905101503400304940148030b101e54141c6401a60100b11914002590a03000d410301c036500f0644510b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 844884172 1250 844882922 844882933
    0x30206100b040b1c0c0c0203010c09050f13180f1209030203030307031104210506130515040f0804090b210d0815090106051b0102030705040b1605010c0e03 68
    0x80d03884450100400c0340c55100d81c941c00d090a0150052040c0d1000e4581c92051000f991901c070348812505c541040380034a0340f11120058101d10501d400c0d203c0344007500051002e0060200280c0e103c00f540074500840c110b5040e115400541ca042c0e00500076054807500362400302e80755008222556101501c41d86c01120361400050241c001219884030740d000c000e40582007440410010b0f40030b0740211f0071190302c1c906424202134071004c8003c2824403070703c040754918001160060600801b845080d4001c00c5c500903d284a0a55440722551565000d6508d21141c500c4400a4240843e50b21144040c0303901a280c6030780e07580d40b5030020000d000e08440c03c03441060028076120845019070030842d04051654081c00020640c40000e507040040100800090385503c0d03e400700550700c3d00712207400b07080e0907150152140c1c192a0460352504000e0030031080342c0c1c810420b01c2000c5e600f100c19a0700b16060786e42d0940d5100d0200001c0802c481e82080020019820f00c041410015049440c003c2803200c103908846 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 844885422 1250 844884172 844884181
    0x20c100f0e0a0b0a15030807110d0b09100e12041502070b04090b010f020d0912020609030d0302040f090207110405190f0b042307050708190203030402040f0b130f09080f0304030206 79
    0x1826085c0c0c9100c000e0540c002000304900080c0c00300d0200c80c29420041030381e030139403131540c6410600010807a651644d580001031600d071106101c0c400c03c0910058000207108212466881000324400c0740100c10001c160822884003082c801c00003074010345000c50003182c4495039a2050380c0a4259242403a01082026034520000c610001e45170b001c08402d50b48800c10646468140b000b18100068266000001000700401c513807010032005074403802079600140d4407803030406410204007550b00021841801000200082006180403611981d4111070006a80d00c0704a40c0c65415031054800c02c54035400c0c14803e0441004643c082011205d05650600002a001e840c9203450074a5040a000528a42c000f10b007400d84110080d012a88c0705140d19860b0a101e205850b180d08072060f00e220040c2d00c000100002c5080c28058441e0500d000c070000c0c0005050f20340043e601040c4000c003080c505c0d0b03a808505240a45507003069240e160803243c0d40350b0317800d400d0505140a0b4000c850039800b601c908000309 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 844886672 1250 844885422 844885451
    0x120738041e080a2117010e061309050607020c010f140901030f0903020f01060f05130507030902120604020a0b0304050c090c040911130803070302070902070516061e03020c100f0e0a0b0a 81
    0x5444045954005045c1c45c2e00303040c60341e609680d014110700d4020524501e142c400345524170601e003800d07020382c0040808c1e19008000a2400d419036001c0d41c10003401c10007419200307411495100c481e04010300082e0301c0f401e810004800400081101514143c1042184000c2c507030003140a000040c00e403030081c81100d4035030f501004042014410181c00400c004507400360300d03030654002d6412003000c2c0340100300404503800084000c4024060600300360400400d0008500d000c0a425009181e41c110140c250b1829448050f180c8013840c0b40c950140368070b0f80010380c40d0407920313007100c000c0c0400ba07004020901c20907a002d0b46035001203241080245031106d0110b5602c40c00803d0314142980f66005150f50742c00c2507001c0c800394105110460f1144030b0382032503048090f00c000910014003505d5a07441d0721046d011804c402212004685882814410000e444680c500070981c905c60b144107083c081442640015070200a02d4503002c9040980116015801041081ca14035170050a03441410701c000c0f030202856 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 844887922 1250 844886672 844886687
    0xc2b140a2a060212151008010e0709080d02010b040b0f0913080405040606030219030902030c0f060f0f07030225050d02120738041e080a21 61
    0x250001c28180401810244031070301c2a000c034144850710001c140100740c0d80300c07001e9030821040407620031500310401110003280e03c1880800f0f0340c00c459030925500103210181207224107008140e4035221541c0095612802aa400c000800602080714801018040024028603540c240e4920580c1850120412480c00d4400c811040700014444c01d801d48030800d204c240000c4d00c510407031b5414003e000008960b9100d22640d0000d24442e1000360392001584c2c24000c907084441b40340024075190060308800340cbc03400145c52100e0001a640740a04031b04442c001216030146030360001c032a040008940354030780481e00c0038101541c803907000ca9a1448142c160f501402c000d241048136500c100403820040ca2400110001103140040c0140d08060140311015040c08000e030481d00019082140114000368910002e1061000d07040c03048205420180040d1020f125901c40c400016a01000d40c2c60b5500d01e805040740104040ca003180d00d008810b01d401800700c50340c0340e42c41c40340c010202e070076868142c01000c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 844889172 1250 844887922 844887937
    0x1206070f030b0607020618150c0102030609070810090507171006140c1207020604120c0f05060f0306040507090e040b19020f0703030e030c0a0c031707170c2b14 70
    0x1844e04210303030700c03e080c220080030041c21607011490300d45108090740604014809e40f031070380c40056aa03150003002c2c00484030024129004000455007000210001c0c10700c12816141c45c603202190036101c10340704844c2e00606c203d10005481c00300049c0401896041001000c0700c410b510b480e8044040d14644a805015005400400e90089254aa0a20103003070040c01d240d0300c010051418541c80e202c3d030503005048510100c0302e10319146014803040340304c0458400203090440d455403034000304180d65400780c04080c082d00c2c0625199400300f0112070099861a0181021522140540c80e290901205511040d6040300e0484181304100e4900507450080740c02d103121510704285040401d84d4118001c2c00c0c5014860f110740000d0220070b98865040c0212030203103004000c504409811800c2880000e4182d1a04102041d070400120300000e42c07034041d01c03a200d07403041e140d942c8030b4071148076040c01c000c800360035004008005510a11201403445e554000070b442d580c0d4407540c002144600c072070640309021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 844890422 1250 844889172 844889179
    0x51503070305040503070f150e0c03030a0e04110703080a0f0207020a121403040803040306060504150e09030408030417010e0d1e17151810141206070f030b060702 71
    0x4500c580039801540d0024443c20407079241a4072521120701c2001081404c940c1500c0c064055402030119008a0440802c4031000e085404400300c002940c034030403c500f0307209200720600f45013100e0340c49512200141011100c0d01d5600e1101d807800509210046070b084840500c1c2040b04002e1400d288265011070354081c108a62440c10110301c1c2c000c100e20300303004562200104155620001050003d031004201801c02191a80d0840c07400109a540075008580030303a14091030307029105416542c903c11260280560340c41500c5114140d81144120380140c00648000100024400e8205500a4454603031100810556802080c05c4d5200c030030442d0303a140013803540c0304c0380d0404805c45180440c0361565410810194081d5602000c4081d40c206c9060072105110f960314030160409803031741390001920020f0148146000c80c100b58920400e80521242100415a40752040d1640c80c4d403d211615920304444c1540750122004003410340250580e400a4101200d0940c1801c01e0300c192007a565006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 844891672 1250 844890422 844890427
    0x20a03020904080714010b1201050f0708180f07050906032b021504150509191b120f050106060201020406120e01060b0403030804260714030f220515 65
    0x503020490010405482038844903401c0202400040c114245c0a288501d1100080307141d441842c108940a1414030131107800f43d04100800142c54005240e140e800a010700f0140c509403901400155140003480072060702e032003480844880c100700024100101c40080728510307810780c0c804041c15191000e8040d014a0303804000c07208000000d8205210b102524184121600300078010403500250200356000e40c3c6100001d0540300760211203004040e071207a60040105110041981940004025040060550307182c0c03080603c200c00d040700c00704009160400c2094074200c49820304161030020b9a00445596107010030010740799006000f518112111a110b90301c1040031860303e20082d21005510707006035541c400002c168181800d0250004e94000d954014003071400d031504141400c95a1003c01c0901904124100f1041080003201d48c80742d03000740300004608950300c00780d203103000341100c11008a1000c504442c03202240003041042d003030f1500300988442e584106102042c0c90441240d417070300d03508 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 844892922 1250 844891672 844891679
    0x9070f020a020121060b07060c03141b0f1206031e1f060807121a10030813080327060a0e0904050a080d06050f032d10090507051c020a 59
    0x489880e050300c2440c940c0e48600d442c1d0349541c0c1084174803d401c01e11103448046003a006012080c03050b02c62000c84c90804001c4c044484955154403000201900c1d480e16800420048070364205060b01c980e4007603485102c0d00d8140024140d80e2061080326050b000340300300c01c41ca9001d050041c0003469568a010081c01044203000807940c038042602c1240c0141e5500c586000403e075000704400b000600a044240150a00740d14020f0040141c4050010001810405004a4028901c004000c490f030040d01d2640d9000c10205001e040346075a48160602d000100d56007000d2620151501004040c4002c103402107141300d800c0200500510604000042c2305c81c1001c0f005003171001c0511303086400f95003100c00a44142d903c00c900f1740d002d070a52030030440d11407000300403604014807001001142100680f403803070ba4407240b62030051002c0498a251240301035a81401080500031420740c0140c00f1030a111a0100b0305006e542c60002d48207040c082d040420000355180c055203210120b01c0d42c002c0c03990342c10614 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 844894172 1250 844892922 844892927
    0x31203140118060312170a02030c0f1605010908130608090615150406210b0f040b0406030f060203090d112116050703030801120b0402210609070509070f020a0201 71
    0xb110141481c40b15541c00011012540d040745201c0314a01d1036503030101c41043e041c949117203048003400100f0b440780141b0502026640d180c05541c89007481c140744a07260317103020038100c4180000310000390155207482c21740d0080c041420028564908010643c1580c80d41d030f080d0483e900d140031146424640c0000b0082128406e944c00403c80954004190b1020b140c0d03410401001580580c0c800c00206070642c03011140000c25469855011a203808204010b40c92900815043c1c10000e1189101c2c83e42d6800740c0b45a03035a1644024040c6400001400000055180040007944143d8180e1900e204901059100354824a03c09100313d010300007610516004104051040d400b981e604509804144980c0324201002056500c0480c0100001e043c000d145042c080c00346801070300500c103e95034062006000c1460034100c80d4000394180d0303100220f029003a090416480000c007480701c40380648400d01224440002d01102650701c1121a802261503009080ea801110000341d000580c000c030906a01660 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 844895422 1250 844894172 844894199
    0x11d03070b0a110304090605040b0a051c051e0102090a0801051006052503021b01030204060c17041203090303020c060a0801140f060d2c070b0f0708040905010312031401 74
    0x154146003c03814011650075041d074002e0f40083c0301c8142e40c2e51040100e80350a000c1c0f0700c6a00400c0c0d46803844c080c1440045405003034051a484e101103156418039081003c1008100d031490560308410000440701c1603000c1c080d40c407200c85540b14054038400803541c050f042c40b0712070240003e000903c85052414030107841c0c6030055603043d0402411031180240900b2a210402110b900c42d81c0030b400d05050313803007c40c802d40c81c1c865445030400d03205200074010366810400c209141a00700040030b00c0c0103403124114116101c0d541103028266007110480e01055005420a802ea0b882038003551907204010003805a01c1c0103041c54400000c84a400411a4007240800028104c02c00b03003446d03140c12102404038060740d1218100407411030380e40039401c286111800ca00b60501ca804200e034040614800b040642c0c440c4a40115440d036840003485d0354440d9010308c12202515070240840e5102ea81c2c620105005000900c019074001c04060702d22020540300b445100d0400c0a441031184040e42001084150700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 844896672 1250 844895422 844895437
    0x60106170a1b140702040504081207110613050c03070905040b01060302070b0a09060b0306042301020405100509370e091b011704060614060f0717040b030a050105011d03070b 76
    0x303060404c00000541ca59006513441a4001d0030402d0340c0b0181c4518000e4600c0700102000d0410008601810818101094081c0c200d11440d0001d00e0700401e900b4120f0410500c00e0b14542d1610524100254500c59a00998400d074020b450403480744c2c0c0e82d41c1c0c0039400d030303c2891401001c450b04100041c0c0f805c803d41d403280d04000e00400000480f1544d02003c64540001518203490400007140718846010040d20801c66854407480203604240c940004128441410306441c81444400310380044a62904080d10390410300f4404800f07070900c80b0000614003505a100e030080c01d40c10094000c5220340601c400e5a0291081100a0043d001414201112030f03044500039410044200803083e8246504081c86000d14052000001c440f440c2c08601242001040c0e51280101c109101d01d00401c1102c0050f641600c0d00110407090282555812240e6403045400c50305d080d6038044240003521916601440c1070fa10281c868882001c0039044500c40902d4840a4a625070b20500742071258411140190105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 844897922 1250 844896672 844896707
    0x30b040b180a05150601020a02090f28060503010c0f17250801080f0c060316021912270308090628021207080f071103060106170a1b 58
    0x754003400c690420305076140070388155200240c003400103490035074410341141d0240001d21038900340354041210640f0051021701c1c2200030324000780210409105040c61034017420f40c801c00301c6981c0003030360009144cac80c06103034025840c00385c4c17142d4000c0c001e8003040309003101d5843d82500000c05100115a40c01d0041007242c412803000350342d01071030000107071030038100d140c075181d0555541c18040344620f0800784d82030012041e8820b0450401c3d80d00c41c0e00c202c07500601b4401040e0309618502d001039160988040b0354001e030031115140311062001035421480c0e444440ea40300c1c880300843e251194007001224202c4001c40c0154070b82040060f00d003400400b40c445010f031166050511090440c2c605140d110904c458048a018007a611f1350760511204544071a009010350030001203454045050092030b01c4074008013400903000040c421000f844074480040102100c2d4190385a400050170785202c9441c038070040c41c9210124106244038081c1d10031078240000140c1c05082c03c07141c102d4000c041444a0340e40b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 844899172 1250 844897922 844897951
    0x8090105150f030a24050c031e0a0e0a060516020a02030706030e0a0c080a051527160801022a10020702060c0d05090f0111120c012a18030b040b 63
    0x3000e18005500303240c103442c0c2540307009802808171015100001c1c240c2040002c00c1041144003c14030341640a403000d0400c81444607610780c02c02400520846042443c1031161801500410100350481481040302c20340f2900d104490007401d03070303039441c20440017507058200c104140042031096010602003e100c2007201e6020201d0340300c98000b09850341212150b40c000c125194107120302004030201c040031154010104c1e181000c80c0400c0c5d0f4100c0c0107a4905d500e510a1510081a010400c40074407c2122003c0d03524240c0d103111140c005e41c45400c074400d56845000150f400b01c030101000c1074208c444c45024003510610446c0c1280254000e1001300e0b4007280a2200300420101000030345808080d607101c107542d4041100821a15100c500e10303082c1001030840694005a101080c05910007030030300d60694540b103103000154050b2282070741c1e032109a07440300c0d882000c2e0410348103000200c4010340caa0380345102e05c0700a1000480302a0202500e074820540210f00000d007011b011607806100c1583c40035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 844900422 1250 844899172 844899193
    0xa1e1b110c1c05070b160204020711090f06010f05040303050d02130f0b0d050c03061e12160e0903030c031603060b0304031809050108070303031d070e0708090105150f03 74
    0xd489040215410000c040c108042d1010030904101c0d450144c03081c0341d001802c26160352000900c0040018000703001e00e4003c600b900030404c400d0902d400a02d402045811945040758240492030811030300c16002031500c41088401c180500b0456081d82c1d010380c1c40e907203844120388907500658060012400d50300f42c070080004400c9200503c00300078040129a20750343e41035100008050720006064031300b40b00340c100184a070702d80c0d891402c01c04029a0031a1414040d08420005450a01c107c00c500030030b02176049d140707070360749000042e07071080c0c54440307511400c2d80d141d00c1386c40c1e5964001103c4419a4281c20400718950300703059031324241c1071300681c9004202e03207440d01110202d54006403001c0b804107000402d00300700c010100b40356501500c1c0301c58003000f1961401c1c0045595035160721000e018581e407100413208143c1c0c11042510000745840440e000d1994900d2440e10b5480f0444458000640c050049001994107025a030b0052100324160b0b07042518800c100418002c0206c50103915102c0c5002c1c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 844901672 1250 844900422 844900429
    0x40905070317030f0604061206050603011e0e192d0204020703080906150907140c0304061e031a0609042306100c02091f030501050a1e1b110c 62
    0x1c01c5180000310343c1c6a040c200c4448500b4030001c1c2603a84034030300f0400284000b41e207004030350101980000010a0a444000120b40105160091842c219841e12405c651218003504030745a0340b815602142d0b0740c4120981c0301d4020360140080181505000036005640d00006040301819203802c80b00100401c409500040c1240e00c054000c074045181081049140002849400d41c0940c00ca04084210381c0401c000810f2403a0040c108028080841c465140c142047d41c103940c4d107140c00f5000c496489864030b50141045000e0704000c80c20003d03240544401c14844d000360391202c3c3c050710b200b00c0101402010003441e40c21001602e43c0080c0c1d90011041054035030020049800d10170600c0000504003003041c840c0340307200d0241c9031003803168070b000d4900103807a40d1401e558007101b600c0c2025004902414001043c07082c80e80064859802c0c4011310150003271903030100344000d20f15010f100034680540702c11401c3d149480b5240c240c2e190740440c80c8014900846072501c83c125a00c1c107a455003110140007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 844902922 1250 844901672 844901693
    0x1e030702060402090c03070207060f0504050d150b061c0c0e061209060610140901050f0c06060a0f050906010c02040f1a04050f01080604081c140f061c020409050703 72
    0x1100060740003400744000c2d4100485640d0308010b960100074594684001c0284d82c0706000e02c1002c5c1005032004912451502c100151005004000c003905100109070400d80a0611a480d14050309071034a40b1070515881c217442258000185056100e2040c0b03541d8040c50300515444041405000c030210074100f00350398100091101e40d901e100d1071681e03418500900380c0b41040041106000348400c100704c18229801901c12080368041c1c08216558400e01c03401220b4074051800703810b048206c040b8a40505200114066108640545142c9c0142e640d6102e0404101000e10401b60400901c0c004603545500c90302843c580940050808032351201e00045000454103001703007071280070386c2c41c1c1c41419640c94a40629600003141903550b51442d4103101c201c64030750b00c000c1d00c004d00c0d8101c00985414041d405205a104a001d02c40007048040b100caa05d15860080132140080300289650000b0304e86d14005110700c2401d40300805107000080c9a509100007024902802e4400b4030442c200080044c8140c0b0f075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 844904172 1250 844902922 844902931
    0x8030402040b04050a09140c033415030b01020309010f030f0e10140609040209061c05070e09010b0d050d030905070911090a080f030706050a0f0f0b12070f0b1e03 71
    0x45c00102c0300c40da81008590508000d00003019038120316031710f0318a0f60700010740300303401d10102c4400843c8103d60003803c41c800407210003244020000c40e4002401c000181d041e41010550f503101401644146001240c403881010085808206901c2c01d10070194400c4e070140c8180580b6041c00a60b00039412200381c0340c0074040304003542c9a5242d00c0760203001c90030713a010b090704184103507034044689c1416400602c0c218401005540540501d52403404210300c0410300303007000740d0007100344c0e01c21546400300741c80d0041003210070071b0300c42d8200540c445e40c9080c03402d520320320385802102a060500f05c02c102180503140342070059840c3e100e00d040c0070070f1340c411501c10f25000340030360000c5550f03886108080c040d141642ea8407541d4681c102e410348105a00001c021240065800b040010b1907a503031144c0c8400608120004011301881c0100745101c0e02090390040143d19421225042c0008c0004056030b40d5200d0390144071109050ba060401850440d2000f0f0704080c40b40d2800070152010034100041170303820488 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 844905422 1250 844904172 844904191
    0x1210b04351809010e070509030a06050a060501140a02070521030408010b011704030903030c030c0f05060f0a0e07120501110d050f070932030d1706010f090308030402040b0405 77
    0x81c04144202c0300020000c103000081e030340c2c0311003503141c01c000d00c84011000300b40c1c1082c44000a601c0049903814084204020351002e001c02c450b040c00075508005005c0c90140901180b0b0300d4107a800554082415114200e00075801050694100420b00c03103011420205240e01e00c41d0110280001c00041c8054000380800b0b034000510070320f071680010004816501038940c408520018000403d5110000106507601400e0840403422585011035040c014013201400c0221984880b41c1000004110940503010207a024810381e1200c210003001c9450300e855010044d0300c010707410050720044c0d42020103041c1c041e4000060b4a032001002388101c3e0300c40440e41c0c04191b62203041280940b44424010380065044c07400044c02410300094050380030101000018044082805200050b002284a45c2d1000d000e41510b0400a4070000900154852402450300451710000115a94410200046504055607031940c4007803031a100e800c403c0d800940b0690300031751030b20100c403a26200ea01070709001c1c04204 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 844906672 1250 844905422 844905427
    0xe071205151b0301030303090c030c030605041101181404021201060504080114060f041e1d250302010807170403121406061e04050d0b01210b0435 64
    0x100711010a00090440e1144450358290b801c0540a410649040d01e51509000800344064180009045c00c6640020052032840300080100320481d04010700541c46051740c1343d00200030000642c0c1c80002c41070803074149a0100000c10141d040c090075010130800107400149031420f01c4030042003002d8260400e1000c01c074005001c004d517050910480580d00d006000c1149141840e10005816a070762000440c0b007181c5500203a2074011926050a0010302e8104042080d0181059440400712000800b680c050244200029049101c3d00c083c41c946c0052240a46150f81554015100a00041c040d5002c0280158460070880d014200f124000c9009455040c0807603000c54010b826a0100c0e507040d9510300c07000303007440601d841c1c00d000d175038004104640307414025800045a0410b07004503400300b5809086185007805001040b19041d050701e0751080ca0901410a00105100303111840e003000b03041054520014020949007c40d540740d40304c404401e01380710b071020030450b845680c450a0400e00f1a100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 844907922 1250 844906672 844906693
    0x180d050304061e03020f030a090204021204050c01090812040626090a15020c0a020609130212012111062a0d08060102190b060a031403040e06040b060901030e071205 72
    0x300f02140e81511107403a0079440c0850003072440c0700c20701014082c1382c989615a20420215070341c90701920b00115902c1d45210700c038034080c24000d0796112840307980c1d408199520400300b00940c0c00f04900ba61030b124948450f01c0c1c54605402111001100c0d42152a07600c1d00316020310496118400050003020800000c1501c0507007070404c2e510003144071005904480c4104114039041d003000c2004031965404482082c1c543c031540d0042000d01c81800c2c500040d041c8002410f4040c02c5105c1c04550681d0b400c49080c1ca070b144107510b0300102e505103612016000444124500d04103203401d000030300420460058141118030400351050081c1100b10082d040d5401850841c0742c0c56034881c6055901110134402000314180078030001c108201d441402134000420b4200150140e2074034064000255442120700d2804920604c11a07201d401501825982c0d07545a000b0942c0707480c060040740046040146144e20b841951401503000f010898100400d90003038000c00a0100f80c031006181e2054000d401520f041d024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 844909172 1250 844907922 844907957
    0x61a1b0d03051b2a0715110f0d02060c0f040b03010b0d150b0d02030a020412050312061801050906121209030c2707120c05210606180d05030406 63
    0xc1d00c00c0b00720a0040c0503c01040c48410304000241c2c106041d01e040b680e00b4280c0740700e540c1081150340100011625402000308001d502207004500c40c0c7c24041540d00d440c211098013034854420300c95003401030748000b020417590700c040401041d0300d807440340c80c01c4e1038185d86240030f044c01e4000343e00c104030034480400c032902850f5003401907212501109500a01c21405c003d5440d0f258018622041d450300d80c044005940500c0940c12078001d030a200b80b00642d09170440c40c10940e20340c4418402d280342030500011503c02d0502110401d158041d021241072907a08007001c1c07010041c0018991503000d081c0030b041105201007030200100481840c10707007035500d01d11041490703d05040b07141c0710350003400c40c81c0c803494160034460311a01d88003005205100c400d4450b040304840c00588160043c800d40d01c3c0003a00b18170076400c0402001d06808880e02e510b01c0c44146025048165011161203810403420410940c2540a01c4500700d01802c2c0201903511025a41e140d07a8550341054026001140c80210b07004603214 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 844910422 1250 844909172 844909201
    0xb070c0b1b030c07080403060e03070507090506060f2803201908060109030b2a13030b0a02040f0305100b03030c100b0111030d060f09061a1b0d0305 65
    0x42520a21408951060001d04032480010071598000d600420700501300000e0400f103400454201009210301d048d0082030725125070280d0727012921482200000141c40d55280195480707400c00518080c00e10307010700c02c02d15039940040c00c0c040750000312100c48042c01610400c4c2c152104569a80000c090961450311251880943d00202c040b80003444203945c03404580c0b100c01808980c07854186402e4491200581e08510300740c000403d01100307401001075040c6c0c2121580504402c540c00c03d8400c3d04030046141540c840d9280000d80c0c004428411b101045a18509075008041e2039030062800340d541c5440c940032a280d03042203805401c000141c004002c245d00411103c2141240034500d0f0600e281280b40e0790303500c8000d008114949071200c502644c0c1c0525403800c18004000d003a669510010420103000b0b10305801007403440708101001051004181c4200e401b51b40701c00d1841611241600c52185c01d036001100340800e1000c61610705040c0c66414411400e0b48010303030320b02154505019003c1c40500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 844911672 1250 844910422 844910431
    0x120109060807050d1401180501020c0d03050f060d0314131806061209060f05040516171f0e0313090501050f130e0c03010204290703021e0a0b070c0b 65
    0xa82c4403200900007070b13840d02501c5011562102c81e5103035030341e1754105442c05010003180c40340c0c030355600b12803003028010190000e110382900c50065640e0080e445106900300d41041c0d56150708407281500084050420100c01030b1154041d0130320f400091105441c400d2a5844481c0e50307034150203060802c1100c0d4994071400900102d43c40828441a07041001c028254010940b098480581710324001c0305108050340300000003c4148820310092526040c02d84d40c618889100d420980c2259100080ca500c1c0c0c00301503040901c07450082c0100c1c403042c81c2100c04800ca824007c0170642c3e0b031400138201f9144108002d003064200f0b400d5401100e8a8060302e9003c544050b4841ca0241e2051014820903554240c03501c1107645070700f0030004028000000c009d03d4001d50708041505036200080103c0c407003000d0006108075980b1390060a100490460b6041c0c0c150040000041c0035a0161941100070b8040b08034165000d200c5904940c00d9120b5078035040c400741c0302540e0490101d041d000100040c40f03241120158030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 844912922 1250 844911672 844911689
    0xd200d0516230403020d030e1804080a0c231c050406020c010503091e062a030105010806120102040f06110a0f020915040f06140901080604030c03050f12010906 70
    0x8070301240002030b0004900385070100c2019800b100040c95980c0460a541c003664001c1c1c05c0d01207910052802070015002c81d100984501340c3e04031000003009000d102c19118079800391182d0b040452010040c0d4241125040c200c40681101004032002d10300100d10080f4840c50800609080c9800c458032812900ea009034102002010041070244540001d68850b24500c02e20b0b009540c2d903111014141007150005500d485075000080482c04100005100c90141c03255241007002c0ca554205900d00d0b1001e2000c2c0f8039542c4009000402556001c0d2011a41c0000c01905042c0007002200f0098220b82c8507401800c0380c60002001400071691143c01d10f50704a814030000d20111030552150031800c2d00c0400000d10030003503080000d51007541055010302220001d070082c419490007083d032030060403442c0184400401c0031400482e5515191840c00d0486080c00040c0540d07854545040303502c1d07401c6400031780500800304a110b11810005000703064210b500e8202d03400550600c481e03202a140c0070f500030100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 844914172 1250 844912922 844912951
    0x1c0f020d020307030f1103160303180f0204020c07030f0c08060c0c0a0b0c0c0a03110c09060a060807030209091e090115060c020f1c0b010e04170d200d05 67
    0x350380c0d400204840344941c06040005c0c102d85061001c89080c05002006880e41c00b012540100d56045a140100020300c60344051220103a00100708001c0030460501900040c0150808005410650300400c4c1d91030610055a0045440c2e8a40e4403510303d00d000200d038603401c003074400c026010080c0f100d00d4000201c144003614242180060951300c0c0307011000506506028008200004080710807215180449000e17102403021070304014003031010302c00c0c000d0164001c10113040c0442ca02408010f201d540700034245528541031190803662120010448414103034204800304242e07546a203118451020400d205004810303080455903444806000b0303001607070405000809003400c0f4010f200a441c0c040c982030780400d100d8000226421040c00d944d42d0000000d140104480d180110050111405583c502d5080e9a8408140d44c0d1013070200c902a003401407c140050140220000601c480e148285001c103804c4010107141005903038403640494030403c0001d40d241c1d07880341800380350743c4001200c01c90300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 844915422 1250 844914172 844914193
    0xb0108070608130311010e0d02030409060f060f05070302070302060414040b090709140604050d052a0609100302071208091522020d050f01020a110a020f150c1c0f02 72
    0xc80740403480c1c00101408803051200240d140251f1052051580e00b4013180d071130b00000c03180a03443c0d5001340203c611841c14400081107244007e2041030455036142e90310b96016000d030008a07a241c0040c2c4d012421030290400020140c1c0e2140b010b000581120085058440300940c00c010031a02c105110902400002040000203500681c0070790032200c034002004c0d0a0500000007802c288256003015074804040001c0c2c900f4040c0014150b4020344c2851001c2e41000d0b0b501a1202021044110b00b55002030b003080717a082c00d4203140f81c1c0c0301031105444c10058105000e41d42c0e407008020404607030000041000d02000300c40c440c100503803018092081c900e50741d58104000001e0550340c041400d80c072503079030381c00280e811500e400418030b158503000b406940e42c0d203001c1c0000601030b51040315134074001412841c1040c0100e030042903100580e540140f212013820b6084007404500381c41e041c1070441807142071000c0c1c03205000500289545034680451030b412520760703c1028000401441c035000465000d4007651 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 844916672 1250 844915422 844915441
    0x60801060e0a03110f060304080c160e01140a1d06010801050402041d04020d050604050f060a1415030c040e0a0c0801020c03041a130303210b0a0303050705030c0a0b0108070608 77
    0x4200f074a801c4107811030903081c07540109a41403180380c030341500305100104020a029040024069602091003940c81c007504d1401480c140704da203401121b00443d680c00041200c08065255113070a48000342c00c10103425603520001907c0005000302100440c000c0f41040343c203603842414507024080c2161700b142020300b005070451020415050b214442221031000c0350a40d6120b809e80d1168a900034215030683c5410b00c0e01603203441050080355058844c44001c40e5190b9418000c0012140d101c04020f015690303002000c1341a842c503003000d1601400b072a80b030003003546c03074078040c00780d8541c010001001d54a54074903040d2080081c43d48502c059910501c441742c05a040031040318100c94140140016449000704480103074400d800100f4001c10749800c0c0002050340081c0c02507a41d69a030300740c41c0c2d1400c0d00006103206852181c4541940030b03101b040c081c000039002e500038000160255049a041440b00e00c40d492924a002c102650f48103d0a0010011800d040000c640900038900e40200723181800d40a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 844917922 1250 844916672 844916689
    0xf030a050c04120602090d08130e010602030708031627050f0f0f06030c090d0f0501510f051201020a02060403030f020d0609151a2b0e07060801060e 65
    0xf0a04e640002d2411442c1d511501d04040300c541000e5810b80d6254038150080e2070040c0c40c13150b044611522000000c001d800441a1031489402080951031992003101c040c80161288900000748552a21400e11040340d80aa15001c003181c601c10303810352420101000720844d842910180300d80509131040328603488405400018240a641d015160b0702c41e03204104081c080e111243e500704541040700ea080c4400809803039040350150000700000d41010460341c910320700204000a007807034160b1402c01480040064068200b4804015261400e0703c40742c0040c403042e45610a0507150301100e014051450b090f4407904092103000021071070881d00b00d034041e40300c140041018040c1070391540740b41000812a0111800050158020414252110940c000500d400110004907000c4035002240c2c10440d0780045603138030300b4404040c0c01c103405030700003201e03461407000340a0f203075043c005c203224001b045406400c940900700e8000d0320303001e07061500c000d1015205901c020104001c000136a04ad640b10f6400c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 844919172 1250 844917922 844917959
    0x14091e06061e0307030807060501090c050304111002030702030102040305060f010b03091c0309150c080901090f02040b060403020901060903120e2112070b0114030d02061602010605060f030a050c04 86
    0x106550201149400213062500c168000745ca00e40300054914104001d075070085041e120382c0041009140c580d0001110b87d4001210010003003001043c0c40e00a629141c01018118100342c8100d0b440c0c1106540402c2c2a600598003c0352143e000d201407010f07500d50480158050441042218118548140303000c2e074882c0c02c2d020040c9164010140c0c1400b50384a5000407171543d800001340d0111040d003400d6440140111804103000071440c2022400c0b0794012700420041342d41207201000c0030345054080100410550310010b034011400c04c0000010788800303d0072802001d181d1a05181e19195040c010403074201043c3c0c500c2000219040003d41c5d41e038a45804440641c40300c0c42c14981071074414407074070300150084140808100400c8a00801c05500c40a505844100200264800244050640c0d900180c1408405601b0060000d4281c546034010710640c0e1000d440003140403981e80001c1003080c1e1040810b0180040300004205041c2c0340350142d01d070040f070400001071030f082c5040495800d8941e0f0740f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 844920422 1250 844919172 844919209
    0x71a090307050607120c050c04090b0603070533070f030801080606240c070816050a15082806090c08060f0102100e01021306050408101802060d14091e0606 68
    0x46d100c1041c07001c00c004c1018141c201034020030046d41203003401202c8440803605c01d4401c0c404d0b4070307000c00c4e641080300d44102c101130600c0c024000304925418041e0480702182c01c070780c10404244200f40c0440c0ca002a0403800a000740c981c028254100000340b030900740020202c82c050745030041042400012042c42084043d0070b528096122251084e00a040c4001a4440040c41c8100c61004c80406403903c1030b070040354412509900002c4d95480c1354003000400d10305041c0405c43c0c48000884101640c00300e0581c1c80c0349090541000c0ba83c900c0c0c40350486805810143c0000c2d600c2c000c075180c06411481d4660000c000700d48210800d495900000d590324440140306082d1a1904d0944443c02c3c0f00f501503854600380c2041d42036050b520b51000402d21341080c440c920a40c46511401180b04405100d107222440480d14070240c12032042e000d202c03640c0d1050b003c0103500765031004507400103500e1421060041780b141014003c03071017000341c20701c04a01c001201e01c002c94100800b84002543d4840c0800c91520500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 844921672 1250 844920422 844920437
    0xc2d17090a200301060e060a050108100618030510090326150310050f07090b03010f0302010c0c05101707020f06240306040b071209051e071a09030705060712 69
    0xa40c0c034401c418261001c0b050b010740c249000815940c280440f260b1081c6001d43d103080b0311035980c6c401103e0202c4180c8074001c5030700060801340700503442543e03140103000c4416134892142d9901c0d91082d10305920040644071243e074400e2400101a44203040c3c02014806e00c0c064114681c0c0803109216040014080918070455004420515103090140034000482d500041000d4038041040b090500c1045030802e00140c1a02c1010942d0100902601d05907810260040102421640151041e202409080c2d403100400b9100080550b030708070789241b802c0304940d2000c51580401d810303010304420140c0844195003007411100701c01d000018880c1d030302900142e103142801c101100b0380c00c9803001c50b00c1c503a9051b000300380c2000144200194001c0c010681980d5003130100f48040202d008a076482c0c41c2c000e015421003910510200110007980440c07a407134106a898041d6135603510416554070245481c80c0c0c42c8081880c0c003162405009520081000760f6803641740022694032141c1c4454140000030902081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 844922922 1250 844921672 844921703
    0x3050112200a0f0b0403020910060f050919121205030108030703080c070501022107080f010b0d0e0106080a020103060f14060a0c051002030115140d0c2d17090a 70
    0xc1d80000c40007840c8204107200f50a0f16007514060603072103404103138040c03509080494500f01c460b100031812684c40760780c4ca10182c0f0300e0000072202036007d282400d6102c0e41074038000090b00d004078103540003444088240750b0403c24a2518594999070980c000080c41411b00c010006d048011040f0313095251306280840c034640e28800e1003501e5000360f5030007900035880401d07103000014050780301d544a00c0d42c200680e0f520b5036840a040310110011a130803d41d4041c03000c01004102c0c41e07900a0004e01403810303008107070303018520420350071592a5408003995030301504050081d541c05105581c0640409078115201a05010f005201c405801e01c41c14020b100c009020452207100f06002c0800b10360140556405100148245010307400c01c0c002e061446c5d04040a003c920b5005480d41c00010110002190038007201864141c02414040070395014000400000030702003690581204810701c8001c400e10062030390002c018005603410a002084a4003035050241c0f0030b078005164079149034049291504401c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 844924172 1250 844922922 844922929
    0x11060c01020408100510080601140904140a120f1b030e12010c09030c1202150a031d01050a0c0203030c12190f0603030f1407020409050321070305011220 67
    0x3aa0b482100d03e4018816030081440352601320728007511030a214601d5864032215055140d1600303116007800010a039030750340420305010032b00d694058007403010b1041d10b841c4070342e0860400400040841e401550008040310507608402e40b0702d80213466241004100c2113000d59034440d110b142da8082c0c1800102c0c0c40c0b0600d1035807009140e19040700000700070320818889081c09080f400b65404210b40c07452120001003110088501040402038004090340d4102c0d40140c248000d613401139000c10101622841103640420212403201800301640c000080c551a104842c2e50407101450b080000315042003003481003140305201622401a40f49500580320f07282c0000710000795140c900f0b81c4810f281817030f01141ea030900303c1d03000c0070880f0f000b1b44440b0000120000d040b60a0396116070381d071440c644184509005410280d110448182c410f030102d0b841d0521540301c11041549074540850b05290b034004200c26558540500350042c0601045840060201d94803041101000196001c152400d01d04070151070381d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 844925422 1250 844924172 844924177
    0x306061b06020f2712210c0102161a0c0d0c0207150309030e04050c160206040e09060405010e1f020a0905060c250b030115050702130e0c010c11060c0102 67
    0x3c01000000e079488003410200c4c555144110f61342101c0d80c40f0400c603d0704600f0140b4034014607034500c0c0040c1c075602907a0124006408652031011854900a001800a40d4400d10040090f0000c221500c1030158407171070b0045104c82da000481d807030301c3e07500000e1000441e1058196000d03240401c42c00320381c103020140300302d28090265000320401030442801c21003035900b603485501007501a9944a04010103182400705032031040d622040551010040d00c0e5803807034400d003488400c2d4402403226150a90b100c082414216080c3c0300d000558011400380820440240724079030000c405440a0300c0303034903008a5186d82c1e00c602c0c0382400b5020398001400c0c90310390344110840c50180c14000d087c3d0b0b0f220544075144613a0380d500341b0220201519003940c04400001030b04c0d1780e18100c85011f80e01c1899a800c040540111481c1d180300c481c103001b424017406005943e8008c080720400794004e000a01c40e01c004800030b01e0300d010302464506108089050788041580e020480d0000c590030b556442d51280c11007525802031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 844926672 1250 844925422 844925437
    0x60f070c030f0201120b060f0a1806090e070c050d2a0308090c120715090e040501140a0b010e010e120109260c0705041d0d02010c020d0306061b0602 65
    0x8031a105010040003007680d1881070182c000e9035280e9112245034a05000c442d250039140f0382c0054140f029145141803480107188030354041c41c00b810043c1d1000a04903015006070440342c04100825001d0004480b200d121030382c004624075000050584913156540c484e841007a0303c80400c0485c144101e440c042c110b00000000c498450b8421804915040080c000002640d21015502070b81d654809249005100c176007600e02450701400305145405001d80c071500300e01c14004140301115a0015807144454205c034480d9000e5000820180355504a03807224800003001c0c00c00d82e5207443c0c00d410032a640058880019039007828940c2000b08848000b800805040c1e50341003482d030914503080204404101040001c0050a40c021030740842c25403031510303502501c80a020980d205c1281002203107030681000c1004075121540401c5a61200600ba0412264082000242c0e4440401c3c0d0390b803643c1080100140003d612302000583d0829000034080030f01d021304d0b80101c0c2c25800f00d5000b4000664101c41c03c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 844927922 1250 844926672 844926683
    0x40206040503031b010608012307021504031706061810110d090807060507020306041e02130b01121109060903100920040203010f0618050a0b07022409060f07 69
    0x110150440090013520180e80095825420030800040c240014003030011944003030902c105070120800202031015400425038421846441141201e4610b80420f03940100d0103559412240d00801307001200715600076103140d0040c031041184004041800401e040400406c480c00180d0240c6c01c402218030800706442d6103e140105034040c46002d400c8040c1c42c044561410a540080c0d6a912094489000c2d461010790503070040b6002800141c1c0690030784842a1861400d4003800505402240f180c115043d99a503403559984101c2420b90b0b080071034020004044082030200307a00c4080c00d4540d6014040700c16004101c0841c040409903803d10420140f098103210400c4024114244178204d40514410340444002003244d00d403140c2440d0007100d041c1d81003201e80c0d64281d4a000802c031095008011080c80018902e070b03020601f9070310201241c009000b00b41d88161a0341c0341e4010030120400200c140141d422204080c032a24480203815100717205000c0b1070b03c50b1600c00e40c031040c0f8001d124200d8010038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 844929172 1250 844927922 844927927
    0xc0503040b0c0705040b0f10020f06070906170c0d0c051c0207020a0602010203040b012102090c04091a0a1208250618020f060a03090c0906080f070b030f04020604050303 74
    0x280c90302000c1c06880300c01c0d441000c40d6892603840044c40110b5031030039507594020300700c0c90583e049810075044040c80001d0b503104a60883e06003c901d14241901030f1662400a540c02c102005110384c411141410554031078064580f9082115015240e80308025050001e00d40304c902c0f02c0740f4540243c090710b0100f20740a41502050300510401ca00941c48034a04a204440403a00820402d01c14070036070341f096500110408041c0d003050b071901c4107008018284820301c00001c410400584480f0700700350040c450241c0b456115400c2154134010345126007115000c600c4220064030746951210084000c465031144c030304032103641a0410019034410800c0680429907089004c14070541885560040d49015503402c210300944081d4010000c01c000002035070000f10402500840d05c0e0100051002c50310500b00021082440c3c0e44407442c5035016440003225981d15401003048000038010407911410313000c040c00e1441d007040440e05032800003600c0c80d2200d2500d94001401c544a0358201c0300074000003002c0300d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 844930422 1250 844929172 844929179
    0x1302210a050f06090613020f040b10021b060a0c1b0b0a08010e06090408120a02130602061905101503021e210907030809190b0a03050108030901050d0c0c050304 70
    0x2c1e900c02400c1a900020f00c41c6a00082c1411400314540d0700034101c2d10380b10005560030340c003000804400d0040d103075030040d95405d0368000c6e983c4100014420b405150098460102e05d12804030107049809c886500960080007000395599000665440a0358050344042d1580c4c500c03200c07500800d02d01e030070602500d400002e1014902e80c018800d0350490310b104808800c16903c030001d00030011170a84000780340350780910251346034002c41284190321030100c64005050200419000001130b24a03840103003da003125041c40302d40094840c10281310005450284180e0408030159684602c40d80700e42d40501d000d0011107602c0714032a0301100d00c600d130021261014040d8101a11519600c02c0041c285040c039410b14041044440c80d024601c240d4211020f40b2025203103441d10201070384800001584800d00304c080014212466010300003800100c48a00c1d01d40c18031140c090104c98040c2c10000c00381e4000d01c01d440182ea40300c400c951130340f048000085401030017141e0030f8034203000c00031004005010218020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 844931672 1250 844930422 844930433
    0x4180c06050403061b050412060b06031905090102180d1704090c03150302150d0b06070303060509070c050703110112050106030e19020f011b0f051c03051302210a 71
    0x2401980c2c0181000c02c2550490f501040c071140788600d060303010500610080001e230741480980c440c81c6005100102d420b211030307400112168070031644459002c0e180516109403402c107215190380300f000301c3c00844c074004c407038203403a808040a9003e042c4109460341d8818200000b41045108880c1c0803403582e40c4031503c81420801400c0c2001c0c5100020f8a80b107c805104141508074004582d005085a001031418030035001c00c5034000030f22840c54513101d041d100065215070380201030280c065034001540d541840204600004080c0c1034400701b00d030120320748001c180302103044401c036030707202c103000311030200400040e41d007101210500d1800c10300d42400000c0a58058104003e01035108003618480e042a140b89456100e4280c006908030803500c60b02d4620754015241e105210030b130303041d845852841a80e038038440b04480780c004840541094030074403000c10840b10380000e00b140c941424130080c980501c0c610b40c882000c1c00081c0c407505044c40110044035003070100741c220701c4102c0295844041c03c1c0c24003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 844932922 1250 844931672 844931677
    0xe070506090d170d140c0a0c0b060d1e06110c060703021608031008070b0c03030a051509010326073f0c0b070807050403062d0e0c0307080c04180c0605 66
    0x8000c01d44050300000b46c0c06880001100c00c0090383d0b440f074101c1c4188603111850b22000041c09582c0000d50020581c0204801544a406003c81da803000f1010184602d800400e441100d8a0409140c02c00d00000d001b5101c04541a41d01000a240058032401511680603202ca5000c50250400200100780102e03074010035100c106650015003122404c4d41c2e140510b00b0a44142583d5105640051001c03502c41c40c0a40c20040c2c000c0c0d211464a00c1c0180c01c03100007000f048017079000301d40e80c110384800482842c190400505018032442e901b07500784a056282e510079043d0405d0321380e00c1d40c1c1c0800150780c080c800556001c01d1040701040c0034940516455405050412402c0c0203855210501000950039881880c0461150001e42e885a0401d07246944038805001e054510314414240346d0359164000c1000139002c286003030b44003004900407035182d850b1407e140044401c54000c0e00b002ca402d2114010010303020500d0b01c1c00362400544c003601011582c121086045009080801c828000506580d00902 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 844934172 1250 844932922 844932941
    0x306030c0d1217150f0d05060c04060206100f140406090203090c130c090314030f0a030c17010f18060504050414061317071b090e010e070506090d170d 66
    0x7604001981822070360181084211003004091100130150941c03402c1c01c181072802c0c5038018008401203681c1d540c45a044c114100d5682840420100e400c1000a504002d2a42c024480407140c040040c1002590b62101d081c1e40900c4411410f844031114280c0c81d40d43c020340080c202014215100d0900c6000c07207841e5880d0400b624031a0328032500960400610b403040502e0301031142c8500e08074916540c0c503510b14600f010b00d10900b9000603c410610140c850004101d91619503400040d00c000a88005e405020301020180d0030100240041c07050041400c0e00e01c00341c80030890000400e43d00c6001e0040500103d4010a40190420b800d20041103104201440e81c3c01d0705100743d5416545054042c01c1440801ca40585028135201c951203030020031000900d000d81c06511241915003800d0404c80380f003c5503a0100405035542e40c0110341c2c840c1d0a02c103c00c1005010300107001c0541c541700c002a0a8003603011030318400c010074241c4108000344441e03158200c4095040c1da986070240e01d49007600500c000423 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 844935422 1250 844934172 844934177
    0x30c030f011b0f0f110319020f0d1806030902210d32131e060801050d080a0e0604150903170c0307060c030221010905220b0405012c0c060a12020306030c0d12 69
    0x102da01e44182c2c0a1443c0a801007943d00d05000c2232f82c5806003c4015100e04401660040896205030700c55200850300d82003031007203140c001d007505030400200801000e0034080c0541031018480094844012001c6070004500341c05e031041d0345455406281c030b00300d0b03851640106128501c1d001051500c601c0c28800d0401c445454441c041c15a0360f03601400070750102d50b04020702c0544100401c5030054010445e02c0c010310b9001c5d10140c201074598614000010054203180b01049511608004001c0040c105442c10f80194100d1800c00150022090b0b0341d000d88903005000030b440e102c4242e115442641510004011400601010480303004148035003d000c0c05000d49047c180f00001d0440d0100801100c12448419034a400742c82068454002d0020003800440d41c13552141450002c05011501c038080040008141c0f1290340841072449141003810302215025400912940d9203050b0407114080382d502014101590701c0c2d4801c00003a00300b91310002e05a81c419903910004082c80300c00c1e51410895075403034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 844936672 1250 844935422 844935433
    0x30a02070810060608130f020d050f010e0102130b211f06020a020f01230a0e011d10080c09090406060e090a08030a0902030c030f011b0f0f110319020f 66
    0x480d40358003943d071a4011107010810310001304910911b02601c010300c0340d0051380300c54001c9000b83e0010344c03045414201a030306940f00034a040085a82841b03800d003a40c0700140214030381800e01c02c2c22425010f0301d01c1024840b01c4042101e4003012144800c0038180c0180c810038031402d1405040c68614106200c007500c040303140c0324401140d03440c000038880241e0b81e0000c0c0b6140c44d2a0322a801140c0c40d007c14140642c1000350b0f4080720844c407295402030100254503880d103106541c0540300041021307200004d120860301c081d0f049002643c40d82044a0b503418030350300c2e0000c42940c0700305d0101100d00c10580b0468110108a00b08020b01405038800c0090b2502c1c03003107400703182d100c40100d1552541d111501400011041001c140c83c1c40c0302da80701942d041d2024050300c0000780420000703800d207004100040f2450b5103d500c003048000d5220640d0941001d181040c08600c060070500500d0700c0518249001803101801402c02c01410070000e40d50348040c49401d400b03028074901002512456061700380441446403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 844937922 1250 844936672 844936693
    0xf0207240501031a06010203070606060e01030b220203041b0f060f080610052b02030604060512030a03021b1c1b1e02150d060f0b03040b1303050c030a020708 69
    0x650041504a941002104a01c0f42000598856aa80c0170740072a0552204000c06000903805014001c001d014503200c41c0e034002516400941a030303174941c01030342c4204400e10100192364a040f105034041b5501810041c8c40f0394440c64603419040225100030304c290070003c00005d84401c0012400300792401d590b02c1d0194600c504100359412001503401c05e50244094001009040c85600902580d008560641d007118003450102c500d03181c0a040c0b45913080e90000304116041c1050b00481c0003d00d030544042c28503504010049032240205031300041056000a86098507462500035811541e41d040e0544404584680c000c2c1010600862801c002c00c0d0030340281100155240b0300c46444030b81001d0a840c00c00c0c0c92885400009500090403030340149158154091011040060901a240c403840011040e041c051011500401a480703410444020070400c40080d4003080d1079904083c411602c144442c2c182e00c1c06440500640618884501c40031881368200c69000603d90101c0322010280c0310990304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 844939172 1250 844937922 844937993
    0xb060d0204081e300a0302072904110f06030c09030c030d2727050604020f040b0a020a021507060e1204030b0a110708030a150503120705010f0207 64
    0xb89078540320b840c0c202000403807141803c8021165080000c6074603c802c4903107080800182d07001031341861700084c0d01080c42010019405c4510140d00c0c01100d241c8410700e540e030b040e848402030040c0010b102416a204c4c2c2280ca40b10600c2c42c00d64448000c1405445c2e103001c0e031b039480450b013191807028072a200b07505520105003408103c0705544001940c0341000d070400100c4d100000708280e0500c0500d4045503000191490250140d200016804a22103040044c01076107030058510250170944240d10410880b604522030300c0849003122065003240b03464030071050090b410714290000181d040a01101c4914150380b1030001000c8651240400700800b0b0302c510580d641d1207001c207200c4800c0d01d500b00414004603c54a002c02d900c81496100403484002c0b1740c1e02c0702d000d500500d004946030034010042c440030300c1403401401c1e003c003408142a2030b109d20b0030002a5403041444901881500001129000c0c40002c1d001114010911401950b60700050b00e400f0720541c070307648804c5140b200600c000100d03605 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 844940422 1250 844939172 844939213
    0x60d14060406050303090103020c0a06050412170708010312030b030a080c0f061b032a04150833060f130b0a0206041b050d060c0e03010227040b060d020408 68
    0x610113001103052042010054000358070031509942c480c440c80364101c1c00180c0d0360166a21851144c000042e031100c21410142c850080c15920160001000d01040b0181e42d02c408001c0c1181d030006a05146100d428000b81d0080181040d4190036000d4500700c0402e224150004103000c0c00000e04450f101d6000c940125180c3c102a80d450800c102042c0d09a40d002c00c0ca4005540c00401d140c0e0800300c00d8104c12841801440b410303c81c00d00e5204040741c10403040d0354500d0000703c0c0c01c00d01d003050a854540358850030448032031850f000680e41d8113000b405469800c0d801c0030682019018007510303554498481604195001001c190348404075003900801d489000e40203503055903070244c004181c26151951020f13000303600003d50700c11b04581c4400025455907041e880d08038080c01001c0000705c5006c5c140c0020500c0b071070b4915075030080c2e004002d116842d0031000720100280d001644c1c80c4500300901000100a0089c01d42c031030340d10000201743d1007070003800e0385c3c000d204580140003203480c0e200c0507001d40b00104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 844941672 1250 844940422 844940429
    0x60702121c0506190611150106200106050402070c0503070504020412080703021f021210060504090e0304171605180613090804060e090a060f0611010902060d14060406 73
    0x4441e076111400e5038260400c0d034100500134200c014060b1a41d02428506815501c0a0000783c0a8528804010070038400000142d0102c0c01030b007001d40c106040075001c1c80340c03240b815007810340d000e01b1318005003401c1d441900075100080042d0354130314803401c0c02016982e190041c20f109000390440020f0600e018804c403421140c4103c0000001601901e40c3c4020b5041500d042d400d41c014000c10202400300d00b15015501e08005100503125016040c08806050004181152180e1100024000c0301e42150564040394914400812004140030f440c1303040d40a030f80e1105680e410060b60004284001080641440e104d240ca25600c0e965110708010b0140c000001981c4086003001c00f18801d07041c0f0180c10760840c00d00e41c1010071070110a50382c050361580280d01500011780c0042e0501a1032401e2080a078004441003000d11040e07080c41014091004184114000c2c03150201e141c0d040303180c0079044052150307001008541c07180014140031010b4200d20b808003624101000c001059407800344502c0c0203a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 844942922 1250 844941672 844941697
    0x70e0c1305060a020708033006031c02120a030507110a1101050a0507020a030c0f05090f070c03020f0601031b080d08010302040b0409081b0c06161203140906070212 72
    0x11540740405010041c0d005495850860041c45c0c00401c600ca003c100400051b0704502c1d80408540199005a201484001018114411400c1130103602e640000d0110204024031180401860300720340203900d09801c0070f61486006002003454030245405901140c894a03d549034100c0170000c4c10031203612070f04400b400038986005100040c6142d44510041c0480c8d13201810918035103c8540c0010300502d003946c0c011905c481280f00c09000041e000307100607008100c250703100d808509180401c1003648100515210070000741980001c1814400c0215126481040060b2201c658403401e018404884540071450f81406d9424009030381400020504025a881da50741e2034141d003564200030140c05142e600703550040e2a00f5500300070800302401400c124a2501b05481e05a00311903140d400d0100c0304944a1041c0024081d2010044480344036941d46a401103000d44044001081030300103190001d003018001d251350080102032140001c0341802010706070201c0c1e5a25032102d11200643c4a4403042e8441d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 844944172 1250 844942922 844942957
    0x80106080f0403030e1b0316120f060b1908060f070c032f060609060117010e1b040e0403021509070905040606090509070603051e0403180512070e0c 65
    0x15581d00e108415420a100b403a02050f15a400c0c00428945001c1b502000b1203620411140403c501d0100210b42c00780551403504222189050034052580f182c5d9031002d014400b9002030302040100940c01a19044001400419400314044d1000702c10702d40340c0503040040c0314040210790807000120200f44200940d941e03040c002404c42c1d801302da40c41c040c0101d891604940700940c4241c05a001c00071120301e86034100030880ca1500404010131410301601d001d040c0202829200440a010314005043d1b900d28003820034940c81d1850381c10411381c401010004c00401c082000f00702c0c004415402402075010b54202d074160706455030881d10090050701c03840d201d50b0040b0010030003a03805800c045c0d0300c1401a0700c0010280d0b52414018141c0b0400c5030b07600b1142d0083d80c0e041c401c0a8041c42541e0b0402d111614030514108941d006c0c40076403401500140602c0321852900d00b029044600e902d0140030051b2a416908001c881410782c2e8140902400c01060711075030024190703028110aa510120b95040840f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 844945422 1250 844944172 844944181
    0x13030b0f01080102072103062402011104150f0e0402040b03040614060a060e0f0607060506010f050708120c090a03030201020a11030309060c161a0103140c0102070504051f0e0601020d08010608 84
    0x21000c86032684d0000e050311740da0009a5090001500e0000031040600c6009c2c00c0d021120007800c4441c0300191a0a804040c002808901c0c141da500c0e1411111508021509180381d00c4203841b9580e44448a5a01c60300000d030101d1851003c0010b980580e02c85c2d40140224503c19824410300030702100c5941c0c001407158810860741d8443c9070003804240003c0c10a130000c411101c0030481c283d0000070281c500a45803c18400c455a01403559a51808c3c1894042d040002d00d50f0b038402c82d8840c500050f01c021080c580840c0380710003003000311420000000c1c10b2801259907458064040d401241050020841050488600d8080841107d2040021038081c0100381c0c0c41174040f450a404c040d000c000090810350341c0e00c00240b0511050364940020305c40e104020740c51440d000300080f10602080640350400c80c941d1003280d80010315141640c60445022445a40d803400c2d080110440540003400052407020000758100c008101e80e025010070b9080d2640e4400c42101036451110a1046900085d80140042c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 844946672 1250 844945422 844945463
    0x90a090b0114090f1e090708090d0e0a05030f0105070305130c050907030b030d08090730021507061406091611032106042f0c0313030b0f0108010207 65
    0x404800800400d102e100c43c210384046124507007141c3c03021121226030200e0311703018984144040d80c081110724120322540307403030300c800340d1142c034030615090601246010300c0006a4400c1c40310b1000e0709002d021600e1282d6969045030103018242d40c858082032038480440c0140081201c0d00317110680188600b41c000d81752109016620000501c100308240c0e5800d0780b40079907501881040c420020543c0d030b880050030501201402d140c059800040c2c20108841c0400b201c40c2d0b58002d5846c443c000030098900009103001040c0c00c1498030b113920404007030004d00442001900d510203140f007018440031443d00d944000a20401d4001035800a03800d000347c9100072080703032050030168034180c1d424054a0601500d00309008014401c10360041c0c080288004100d601c1c20140f298603108646080500300d21070b59140c03c2c6001c003410360314075940ca01700064214000d031410001c030780101440c00c00d4046110b41d02e08084c400703080180d4191090090314000084c1d014814000e54410b560803642d070741010349080950 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 844947922 1250 844946672 844946677
    0x80730091716080f07060e0108240a060207141804170f04090209040f150b0c24160207030812060d0b010602010b040b03070803040b07050f12090a090b0114 68
    0x160382082c440c060074462040d0040c2407000c02000040010318008021100070740c2026040d1b0060b2040000c1448081d42aa03406000903400440001c850100d0500c00d44140d40200400504141c1202030b106002800d10341c00603e080403205102503612601e42d00d00c007005008010100030700340d0240404041781c003260301420b80c14074001e07410340c00e2031600100358900d603010340040d800300811560205000640741002d0055584041c0c8040082125085000480c074041031240180d00f039511000c203002100140801031442581c1d03406513801d001156881e8081c040200413120005035004660300300069030b00015420780bd0f02e5010303e51504200d0000318640344e404008280581c404003204d540800701e880d000505010f0704166002045807160301e4240002c2e106020280c1d4025072081030304002100c4044142c5050710401d41c25569144240d081485c42c11102e04000c20103070140340d40300d005d12902e040080c607030301800b60741000c80f490342c81a0400844150303107400e50104403503054180408145000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 844949172 1250 844947922 844947959
    0x7090c02160605120609091209010219050c01020c0105032203120207051006080d050f0a050c120c0d0f050a0e01050d140f0615070b1308073009 63
    0x1241d408903446600100d210819600c00c00125000080f902c60400190030307590740c0010180c07201489400e143c4401561002d02c0d0414021070880421280f9150b8420302c000003c440c459503041c101801c0b5070400c0e507122183c841400d40540310340700c0034080e554014403d89104401c018114010200f04940f98165503150080407002c102c20000341c0034800d006807010300707240c90142004040740c10040d86c070708044400d03035086038009600c4200303200b0310b040e40402100c40300c245440115031a10301d40e0340c0030f8030980114030440e5402d01500803d00c02540c100720140c501e090000007114100c01c86c021003500c031802000483c00c001441002401c281501038003c1c161075240615100380781c1960008080102c0758683c814440b266214000c2c48880103646074081c2d08202c0484102101c404a840c5e801c0d45489600c6006010340300c2c01c4000383c02c103075081403220f1804d6001450180d49680c2072404094083e1084e042c0554015043c1c0c424542c03182a8040614440701502c800b0301860410480030101c824410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 844950422 1250 844949172 844949177
    0x61122150f02250b1c0605060408030924040803210105010906050717161a0708010512150403080f070201140112080f1801170f0c160f0c0918020307090c 67
    0x810010b0124035003c02460841041c030905c09034000180d034060140c440b01d60126101d41414001803107102d2022045440d0f103041280c0003c05107501d502ca03150264a45815040043c1c1c011600240c080380c04001880c140c011f1000d804112240481c04440c40d8000380561400614409010b004042c0203c0c01008070038010402e41305c201a43e030041c50310986c06500700c00717120b5140140c0340e07007004040345110f50000d40d0311140f00350b2450400030041c400ca2051041e0741c4250003042c052004034805201c41c007004001340e44035107502e01d03150401a1001d4010381c0c01e000130680500008449910600c03070b81801c98918040c0b08000c0e440c21060a0747e8410b1000c0644e0090001c10810340440c038480018074071008030010189500341c1c080000b44c200148404081c1c46403a8880420080714039450030984c1c4514081042500d035103d10394070810440e40c20000801295803030f1300c01402d110201c2c03290030848160500034407c40d02208403c28000400c4580250594000350003403201180e2a0080200c550052 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 844951672 1250 844950422 844950493
    0x10061401080603150106020c0f0a0311060a18060203070308010504150608090c04060e09011508060a0c0c06050421021b0904050c0306071d010503090307061122150f02 73
    0x4560b40c4c070100003c1e446240942e1000301d441646003800c48080610710340884800c1400351454441c484604000c6021611448000803184001c5000c2c00407030781d200c0b40e00000e1910003501d5590203581c07507020460560210b607124000050700d141500610042c06282c11107400c89030300c0e00c0c2082d660000c0180c07810420340159000c000058483e485104020402102901040c0c200b04203441c1c03c403140000020844d24200c1e00c02d1248000000c6d80c240c101c40c10000001c3d2112050b032044ad184610000004c00c0b0a007080103100c14440c0404107038100c0d22129035004288601c000c4241e036130b03800701c20903520203074444200610f840c6409024164814010020b840681e4403100010741010780403500300d00440c0d8030030080d0f0400e510440c00c240c0004800e080840c61420102240c65480c050f64400500c0305403100030540d450109031090320045066074800c51110503a5605c14140d41e6020300610503000f800c06261030b506407040d10a00c00c60b2040ba005403007502d4440010f07032a4801c4401c240c00d1100140d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 844952922 1250 844951672 844951693
    0x100c110a2106050606030906010608062202130b09030a0f0602090d1a011d010504091401050703020a020f0c06030f07020111210907060f0509130e07050310061401080603 74
    0x900c80c0312644000000c0c4800705115140071400c80b00060a524002d00c01802085032004001903818107683d054205207a0990f6000009801c0c52100d03410345c0b51300180482c0c01c1c0020809034000d41510145040050165070703d0300000c41403801102c0d13000344c0c1035121445440c08207e880551404083c00f1702030140c90842e410020a01c0810840700c100c072059505146100452041940701e40589031391100903400e24007154000803050030600502d441195030390070600c1000070540380900c000d480d4400074059442e1119001e03000f504400d41c80c0d000b41c00340402074015131310003060b5451981001401141180c03030302e1100c0200703610001c0140055641c2c64051100780108a409480c61007003103000904816013070341d0b81c288101c00182c030b03c0365180e2240d4402e020454000390316a40c59009480e0803901c801e0701800040e601e40f50b858045218134a80504400380c004041117680a4aa0036400c542002c00004460022141c0a101d44019a40c140a00c0060781d03224420040d00800c00804844080b103a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 844954172 1250 844952922 844952939
    0x121c0f02040e010513050c190c1403130b04080307060c05120c090a0603020304020d02100201110c0f0105060d0c05130609050f0403020d020c180919050c030705100c110a 74
    0x20981050082d401001d0041009180c00814075602c03d44000f4140903d0030684184002070151901820700b88003001200c17400180300f00200c2540316001030003c1556174080010340d032603030b020440e01d941050240c40046040301c0d20070201d50032500c1c003000035860a04680c40c0c10005100400d41d243c20000c04001e00811003842d100e5a90003850110349003a5525410780400c5000381d402c1c0d0042c020700d8014030030000982c1c2c0b203400104819070151141044c149002000700e00421885c0440902d101012600b01400b5400203012a81400c220008109a0b10b800c13080104018140e00018454086a9002e000c40d0034124045044034450b9100810703290344914404c4180c80c412540d00d210f070b0310204200030070b05070b040140151340038181c00130345003440d82c1c00042640c1280503402d440c182004100030a17010101085140a95003407503900c410b01042500c2e2003915414496220380c03280c410328034045482e00e085645007410714095210005000d54070760750807054840c0a1f0103150301541d0311000040019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 844955422 1250 844954172 844954177
    0x5341a1b060703050915060f19050a091b0306030203121c020f130905012603070503120a0614100810030c090606020115050312030a0e0a1211121c0f02 66
    0x8005850216162800100007880d1440710034401215049000500001c0d032100d04881085150580350451100e04180c000c400c042a035501080d00072f140c050f00015000c241e03905c8841c8040301c5001e000540703501250101c3c1992010300001e54075400c800c03030205031901060024000c1a800c660080ca000d020242c10b10100d030400c020a940402c00080c80c000e00501b1554004c000d0b04801104200d0355040040300507929020044007001058100704012040c042001541e0000754402d0481c1d9440c800000f031103070307407030402c2c1c48140304241000d10124105505041c091805035000d040501610586081120400310161443c1c6000d0003924000c8049001600024003500e814880410098982070009003150280c2c1101d24012891602c240324540d0085001e41410151500c0152692a2803141074002c2ca610703540040c2074891030711035404000070245030b148480c20540b5415000340340c88014603100c120049440000050800c00d040070f80028160201d0080f04440c4000340b50025510381504aa = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 844956672 1250 844955422 844955431
    0x607031101052d09100b041404111e130c030b031203090c01020102041401050c070b07050715110c0108090c0a03380103110d05341a1b06 60
    0x405014034840c0c0043c202d883c000e040165055003681c903c4c80e01012150319401003001440c082500d40400c400c5a40c0c80c0d0700107010300548540b01500a04003450301440050812404c9030046140c0140c01074444908030300403d041b917000e000340740003101c90810f00d001080c42e009031005250352010284038136101000b5801c070740c12401d40220340e0780c1040b82060b03242004108107a411680100030601161401c04020720b600701c002e0800e10b44441024207118140b4005030040102c0c0b00001c601042800382c00582c44003100c082c0d402484000101c110102c91482d075440c20010b240d44291802902944204581c40c0d00c89918400e843c251a0202c000503980d260075401a15883c1c01c06c0000e0140b0700d184607140050400c0411046c1103005001c420441c20f00b0144409080a10301c01581d0810380c403950328420b105680034041d104607205055201d8006180f0381810300000101d030b090082c954550a2010054801e0104a1002241030400580003a44204800b510aa13016007810700a82420052103014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 844957922 1250 844956672 844956691
    0x10c0f0b0412120b01020a5606061c0b040207031701080307051e030904090f030e04020f1602030c04061215020406050910140c01061404090809060703110105 69
    0x40648558010844014001480121450308146013402e80c0c0000e07000910aa018014250b0300740240000b8440c6180c404045800c02800b001c403110b4aa140c3c400c818211049070b5200e011164000609941e846c0c0865103150060001c205011600a00d60744c0302d00450414180032030200c6003c00454141e0b0000201107021501c44100c10000e400031020290141042400075410b021950321000d9031107a10080071361401d0745000c1000360500d014002c48440a2000d8014058040c01c0d25022001001484041d000200d0240d600b241074036141c021a1128841c04210364280711010741d51501c403c182d4103040307901d481610460502c035202d500840004101100b615002e41c2c501d402c004031711407880894098001e20411080c40b819170018142c454941040d500086059080c0400742d0716030101c1e03031b09110060b002003404400c5070015000102910b80300590faa04284181c030502c4141e44034044000e0100300c080c81100d426090000107010000e0203403030880006069403103041e003140d0096424800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 844959172 1250 844957922 844957943
    0xf050d02010c11040c0306170f0a0f0f1707060b030111040b341403070507090b03030c011406210304031b150203120f040302060f071710080d02060c040302010c0f0b04 73
    0x88e280c0e1107949409809840c1c054094200325010280c1c884100f00700c01024070014024a00900c054002aa544140e100400050441c0701c3d80503106540c00000044820904002c40c030749403414107001d00c0b4041c440c0800028105420580f030b540041d042003c90900d1805019021440d80111000f00f0412210340d01000702c096540d41403902c241005070740d8440ca2907104000680009100269900c1120b0341000000b94081107080024214860b00d001e9615070743c20141ca1640308551030b00c080d80603113000c9071001a84141d003d21001894004003800d94540c105100c04c0002c0341807584400c14540c00c080d07055170300c0e0383c0300c200d08508000130001150041e4000301e12240d014000e1000141c010b1221510f800d002d1800d664021340e60000104400c462a071000045408030b8050106220700d00b501050030010782c504031000c4202e00405200710159407044501000e102c0d4000304442d40240c003045e100625090441e00195500e88801c0000c40368004140c100380c012401c3c820800380600e109103940c08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 844960422 1250 844959172 844959179
    0x21020c01320c191104050a0207120f110c0607081638040b04030c08161a06060f120621060703050c0a2c030d020a06060f050d02010c11040c0306 63
    0x42c60100f0118082030025006000b0b040441d42c40504440c0e040c2c4212070100e1285e540c0384810340a4011004010300c2c2880d042e491000441e0030100c001840342e820358455162141c110348203503131058040a0a6003182040001c08045144036004060155042c0c20841d407003404e503501c400341131100100b008110311106901048041a00b01070f10901c0c1b045094404281c102611031052f80d50002e40005c09010500304641d0400c4454802e036828440720b080100840c000f582400c1d540e08024014000302182210002041803820f802651002c00d0401e8010382030244900c0e07003421701100039050b203502503100ca150101e03804980340c41c44a1a07a260018000600b0701d881c0207020b81e00c0140040f50317000024046508401d42c49800440c0040d103090260820406002000b17a009500041c1c01e505400351096201080d074000401c0447c1510031041004376954a44041c1d4040d0520300a00740d0000c00e903410b000c0590300c101c05042c4a907000d42c8140f480d441050000030f00300c40c1100790703d40200c0d4803044100b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 844961672 1250 844960422 844960447
    0x40215040e071220030a09060e1e060709150e0d03030608010b0d020135041a180d0c0201030e011410050303160303020f0c01051321020c0132 62
    0x600c4803080d1108180324035030094000403a0f004c420100d00c0b00041e004400200312040d00e400080400760803e0040103a03a56000c65142c0f151262030f01c1341c078102c02c044e903d0208401d0008150344201c02035500e42405501f0706205c0400c0d28a440090420420582c50f10b18465403002d100708400d6201c3d44000400c20300e402801800c1d6130140001c540700f440d40003001d80140c1d8000607901a1000700c1c016103040d883c03442020b66100700d40500419002c01400701088208141c075121180201907800d11980c4540e0b44502c440e0034a090368049101503003285000c55501da0040e10b029a0700c910506010a0905d2520b450714215551000628070154045090224020350329003040040c0100b540a5032411824404110140941c0702c0020101940022081c0408529400345d49040500c80000d116a04211040d4850705407039400648402900110f01048224428240e8030140d0050300030b000f806410200654600b030030010f4402c26400c4049407103461f04004291007031418200c0002a4490b140c00300c05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 844962922 1250 844961672 844961687
    0x3020111060403080f07210e0105060d1709131815060602070e040f0209070203030a0b0604180c0315030b0907060906020303040f210c020f010801060f0503040215040e07 74
    0x15065900700c9014040881e52000c0c0c1168405806804010f0030703140c0d460200e82c040c1c0b0000481140400d141d0307040101140603041203d802d200c0304c000784143d441d640200002130051510003821204030b10502442d00e003042025040f0503000810340303030b480840140300c0d2056541e09485031000c140200310501c104442c0c0c1411074008200d0031810000d09080039401307562031420740516140c5040810008040002e1601c481d40340300e85c0600f910302141884c0002079a40c0c2c0017911002c00003401d00303248000e03e081000c155001c882c18611540c0910102440d4580104202110441015210380c00c852411858880e0340700110300c24003810855142a45800f82040c0781c1d900820104241c0d80410071100f5400819203421681150a04200600310f02c0c0c980c0b694070229030788016240e121348100c8800c9411454039a4154000c8d00c100c0c1813103452038011550b00ba024001e150106800c1181c091040c0d1085000d19401480074104402c511002110511103070416030285413803400d000104607100380c0c08480b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 844964028 1106 844962922 844962947
    0xf0c08100e061f0819090c12060603061b080f07021c031509091e0209010b07080f04170f070803041205100614040b03070513050c22030201 61
    0x40e1140101704c44c035558400311703201c0b0070201c00ba81d40190140c0c25401988880c40741c0c18041c0c0b101502450010690302242e0300c50300071001a0f503d200d0f85140341c010a41c00a00354130114001032040000416284031a179804040c001242e40015072450b0b2101c0d4072081c50380803c5403000840080ca60980d01000c1a141c41000260a420070750242142c41d001e0101024611390441d124103540318400c0c4001d420a64080040000d0303003410025000c01c502c034050142c41c01c43c420140c0c2e5a241c109810180741e20500b0220341000690800c808299111500007a20f1800e00c1c1c0542191240194460b0040768070028540b481040000c0c400c5c604812001d6008002c41e548a405a4004c02c5903a00c240707004038a040005011494005104411500c0040c0806a100041c0364480080d1a014064007940441800341c203202003401080d200c0c04281006684850078034600005202505041 = true := by decide +kernel

theorem cover : BRFrame.Cov 844784172 844964028 := by
  have h0 := BRFrame.cov_init 844784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 844784172 ≤ n) (h2 : n < 844964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
