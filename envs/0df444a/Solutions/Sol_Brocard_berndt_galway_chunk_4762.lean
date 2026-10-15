-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4762
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:39:14.486053+00:00
-- url     : https://prove2.me/submissions/f66fbb59-c22b-468c-a653-a864de8742be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 856294964 ≤ n < 856474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 856296214 1250 856294964 856294969
    0x306050f010f0305120307050c010518250620010c020303061f1d03070506070813050102070b0409090809060a030c03050703090308130809030f0105071b0b0a1505060a05040302 77
    0x10141c0c429a50b1180105080000c950302003120130b401684810101d58950355024156a280300d0301c50840b03101c2d840c1008200300184400ba40e4039405007100d0544002040c018900340c1c01110340318490b00e9000f07041c030040003054043c4915550b9426400c1203150b6400c20303a031100c2d08444400340f00e0809604004200021480c04c00c88583d803c401c1812905494107100800500c048042d00d6420b0802d80e1000c500b0400b5a410040c610040400030401c6684103464a82800d4a400c80724a0400a65000e60081415800410b030081500c0103c01007909251800b607820019200080003a180d19208110001540e260380e001030010300c420b520049118000000c0c010f00f01c0c1e00c02840c01b01011305c1c20901c1c10000b84d210b0b94090300601c1003502114480c2c100c0c01d1015092040c81c42d480e6040c03084019051701040d042d00a00d201d4045034580f00c6000681d1206c200e0f42d074100c46401000d01c007000c0000707010040c080d80400c0c3c0c4000f81400000c8080e842d50b0120740c0710740c0507101c04c00128a0101e010001c61 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 856297464 1250 856296214 856296241
    0x1080c04050f070e0307171506030105070c0b0a1d0c01200a020402130f030b0411030105130803100e0c070b010b13120503090402130e0f060a050f010c080301030605 72
    0x14a016030301001185003016416416030400f608580410000c019094195a801c02050001c0c05031034082c2e403105800141c00715030314400c550040000406a20009040b4907043c451310748103010304d41f61200a80381d0340e9111a02801c00420031400301d5620050302c80b003003c0d5150302c10400011a801042c00c0c090001c00540600052a8020071b1201e16980e180e01c080000704908107075941c1a02c0151721845540044604003076542c01031071240440e00000414040e6400055001741e00810515503060681010306003600c6084503e10007000c20015481c000604c114002c6511601240c1d12041d000d840301444860b2400550b204038a02c0b001081450501400c844c0c100e00419803003a003285403803103510300b50071004600d1103000c40c040100f41e80b100a210060085510503000100115503491041d003022000d0711007130084041d501401c400003a0b0f11312010290b02e00581c4000c00d15443c0520708410000201e4010300050b040000307031040f0000042c040b8000d140a9407095401062601d07005107034145030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 856298714 1250 856297464 856297483
    0x405090609042001021e0703170307020a230607111023190c170f060a031712090604030e060403030807050306060c0d0207090f1a090403020f0a05060108 67
    0xd0384079503040c030000400d0f40c49004403456041098100002d2088010f0b42400004c800050720020b00b100400c0d080a804560391050700d02c1481041c1c41120341e011440f40c1c1c0e010442e050750140c1d02001d2424041220400c0031100c01030004d80c4443c040c50203511090911106880074070100f00060514018910148030080e000a03090204001d40d1040380c511515400032101d01c0b910106500c00030801d1690900455007450500b0203091000c0000307000b005010450680c25188030421941c00b00d4040e42103141035a02400c00141031a00031821510f035070900aa10358111040b0380c07070030002e4502c2c2840032080ca501c00c030b003a04e002d032249103001e00300a8480e80c6034040803031040750200018400240c004041641003070a1386010751710796076504081641c40c4107800c20b004051003924101420301d9400101d800540705040d60030301c51001114031a03010744503400207100c00d5403482c00803008113040c03088509500900030320489115102ca00403550070068191000c0d2802e80000300180183c82040020004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 856299964 1250 856298714 856298719
    0x1b010c09120305090f0a0e01031b140619031806050405070e0105030d0534060e03091e0d020a030c03030f020a03090302010c050a2405130c051c120504050906 69
    0x5000280ea40040040c800c0e411a035120f660715040740032040c0c1700c011b000b2020303000108070076900b56140d007002210641c00206604039682d8000021458010300d0380c417440e003024058003040c01c1c992040c02c6031010840749007441040640d101d15070540503e881c2c0307582007042d00a0200060340d05090800505080860308182e100d001080e004020907240043c40b4181084285403845c0c982500c100624000d500c0c00c148292a1510440584582c4000d40c2c0ba480059100d0a0304105509400c41604d840e401041e4505d40d001c10709603095250303110083c08002c68150002c0500d01e044900f0f80c0055296612500141d8a04181c0e400078000c140c3c020040f00e54140c6240000c00903828a5a00284070030b8050000038108400b8140300700400c081040324a0a40d035000b85aa0344a2850640f02c420340542c4040c1554040d0404010a0301001c0420010010f42e4010716a000c100d414074080c010781c0000104c0380030100846c1d501d99070100d080214014200c9075940e43e807a940354500ba04111480201824851 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 856301214 1250 856299964 856299989
    0x7120c0b0f040f060c0c03030b0d03080c0f0904020a050c0c1210150e1602060a150b0f090405041103070b040509150109080304030803071713060b040e0a05070509012702030a021b010c09 81
    0x4000ca03412140540c1d00040c6888040d950f0043b09004501901071030b482103030000d002240140c0340d039030030030301401c0f01155081c00c80c0c004024800411102c004614100c02864100042c1306c808a43d01da0804191908001d800b10301050381c0c1d5103041d901c400304841441d450040c40c13000d050840c1c2c0c1801880d406c540340b130400740700801580b00002c2d507200c0503210302c01140d4400500200c0307003540c41040c0d03000c500d40280100128680790802101007208946e980340700c1c1c050301601040c03001c2480d0030794003610000381142d546c6560b00400c49604803620610541400440040000c10709810070050014610a850301a00c9042a240c0640803009199a1410051b0a50b00700586801300d007959a040642200b4082130304007001010030300500c0703c8111320900d070103030480e81c0d418090006200c00456a080d03440d415241c1e62403800c5041c0d4403600e50106840c000035541c100c03c4500300d8000c0c58004215003c018980703500390410b01040000081200d9007a5151201e540019400c94042c070014007030340c038540303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 856302464 1250 856301214 856301239
    0x906040e0c07050d140405010c0c151e020106120204180804150305070e06070b04060b18040512070201050714070f140a0602011b0507230307120c0b0f040f060c0c03030b 74
    0x85d50040c0d020b080c1c100160b0b031541c0002d00201c05140402091408031802e4140e201c07450041824480040e007200304c0c0c0c4407034602400c4520500c1988112800f03040c03500702100b1103508000c080c0c2800c503800c0400040001802002c52411401400200107404179081000c40d040c0028058590081000b428400610942c802c0c030b0702c403003007280c08407503000d2000031213070384d0318a000c00080945c800965000441a00c0c01606216a0b181244c040c46c080d00c1250034681d242110040760303210301c00d0024009202485071000040c036640d54840c0100702c1100365480300361203600701c0007031040720750048054904c1c5401c24225810103c00c030304080c00700ba100030300c4454407482202c5100080403100d0002c110b8002003000030300c072506141500c0703614211342d400d2034090703503442e81503403504100800c0c0c54517074030b2400c000c0b80d071405140184961584810401030715134464500f4548448010002c1e00c002500d00c4980f0300065480c80f540d40104841e0b11000c007101a42e0600804507010000014010705c3e02c00c0c0d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 856303714 1250 856302464 856302497
    0x60210051003020120010f022d03010506040b030a06030203030a030b0f010903020108281b1b110904030509030f1605030105010e06061e0301080105040b0604140406020906040e0c07050d 81
    0x70500c1145950100340e603661700d4401210300421f40702a11140803480802d00381d038030141c610189030a40300c01c0d407600012089000c4298005101c01e1207032950000c410842040724007003500103140c0c88845180c0015181c4d94076004242158071100040d000250f9401340003a1910340502d81c003940384030a2034013004040c21540064039198010304003d007800021031480c441c100c0310003403a000700200c0000c20722032032081d4890380d844104034992600100d403481e107580f004461022207547c101900850149013103007400d01442949030000d84203600700a810480c0741125201001401c0d0020480c10003004a2421007400700e1004116401440c4242d040100402c00300200080250308224119000ca60390840c2000e00c166504500c52142880940480001800729041d03222620a600920800306103690b814204005c4130b4424910700e001d49002408140400c1165018209658014013201d142c1a10f07103441c04500b202c1202c0020303a1700d4001401c1000c00c20144007601c0785d0740d514101206001c0c0301c1c124 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 856304964 1250 856303714 856303727
    0x606030a02040e16030605091c05040e100308191b0309053102040501080c0c1b0f0a030b160e03071503090c12020f1f0e0303040f0602100510030201 65
    0x40191049840b6a041c0c680800b00740a103481010213446000c0e03a0f299289030103070282070102d0b00c08500d03008007030500405804c0326821400f181e007650780d030510b0103080c04951584901e014100741c2d52410b006c0c501000241c942001811007580f2240184800718403428010280b074150861400c40c0c080c096003c000103030308080d8080540310119400900217500021b40801400c20501d02d050392500360689418441e003070b6000b0700589074207a940d4096a0791b000f424070f410344607a003801d02d03256019845c15a9014028010042c0c0804000c00603010f150600f800235030088816001612010300e813009018000114080c0039107201c00038203189654105000000382c0300d28291152420034803485109030480c512a43c004007106500481c618512903c0c1c244e03003144004143ca04030b02421025550781c0003442c00441184924910a20020340e52104400c2142e010000705c5d07a40d80c03d444144000f003140d0b690b800350307400500b0095004011400320014502c0c241c860107400340851620100080c40940d03030192 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 856306214 1250 856304964 856304983
    0xf07120f05090f040f1401080609070509040b15030d170618010302010804030c05072409150e04181a0121020609010507050d091e0b0415021006030305030a0509060603 73
    0x100e902d843c0390501c602040141c00c1040e07840340d09a16240d030300305180e45446d0041d0306070b40c000401c80d2a00c0d510112065900c604a000315688030391408000780c001a1045c0c0340d50392140428444005003000440864604144051100b011446c0d0082801d403054020400c07075448041120035480d100020001907200c0041800080d04222450700000d01781402026201c1055078020202d030f41e00d95a40700f0388000a4050010100c0844500004164aa2140440c40c05880e8580550545440b072440203860614100384a41e070442c2e16441240b2032000b840c0b04c0419124026802085501190020401c03d804140c00054101400c206640c100c04282c0120032605941503840030303030f2000040c005980300d00450500604900c00c01a400045c0c0b50b00c200c210040314004000440500300448440049160a0081028441e001d10040181e03000030b006d00030243c00e884c01580c80320074210b0214401e580c8039420550118400006201e2042c9240c82801c0c0d1085080000e480c413030134487c1c00652280001d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 856307464 1250 856306214 856306219
    0xd05062806120615051e0301080114010e06100f020a0204091a090a030804020d140a05011b0302270105250309090b0612150a060c0b0a090305120c040b0f07120f0509 72
    0x114408202801d5018151803041b0b4185030b00c0d4907983d690b00d0042c0070300703620b03080311048020102c0006154450b0b001040e0003110b004050810440074941c0440344184c0400070141144100c81068016031510311802d82107a02503080e001c03501e02c2100d001031040301d01402a40e0b0b00c3c0d00c40c90350100800d07400560b803600168111002d868034011418450140714150503514018081c5041da0402c00c40305604c498000798078907621f891500c010040580c01c900a8601601c256800301000050409986292808501050501900b4108403c17141c03107080100040440781800000f5020b424983c104103a41c00800101409103c0701000c08041181ea0142c4c0355441800710a0302c0204080000341a42c12400c0c00c0090110441140d866100070307c443c03107100c001e0350740102c0c10010078a07500240c051032112540580700c40385881c90007001210340a60007031a52114500c10b010110311459404000c1c8000d0f140c1558550700c40b152805c01c0201041d8442400e028070401140c0e0070740803600001500d0044c40c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 856308714 1250 856307464 856307467
    0xd020a0b070e040e010b0a050a120f170a080907080303071209020109080f210f091009050d08281b020402070c0e1006140d0506280612061505 62
    0x48801c00d90350003440e84000e5034428200b030398030b100348034055008020341c1c03c00301e60704020320759100d0034054180094080c518011f0040340e002c0010402c901c100a400901c5a41020030301003007881c1242c03082d04109402c01c002208401405840c250401601016181d090061442c6041084c00a0100e0034047c403200e030a142c40300f50080c03d580c000d0003a44000d22105042e202d401e100c403d02d0356180c40d07801251002218040d4600407030414000c1c207840240039811541450302c500102001a50000d010054041264401003c50a500c480382840c144501c119407032605e0308010020000c907080c0b01c82e0400380300146005d48100f0b0b180d0203800a00d50481c000040307aa20b10700e60000c14080d106001019140106000300000d0039555501014030849104c125000300b143c940c0340442d0044c200b0b002852000704148885d106119441c0d0103203400010040c4080518042d080003803282492500c129081007420326000c000c86904a024240250b4002608112003828040e2800d003280c00c40050303c041020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 856309964 1250 856308714 856308721
    0xc070509093903070e100b0705071e170706030e030945070f170c0904060905041b1a030109020a180f230d120e10050702120d020a0b 58
    0x1084500c591102e0019080c0d410503a21050a00c8052006035001079504017000000510030000c001070301d41443d0320101800615150101611040d4450700994550446103903001a4070101c811400102d10f18840182c0890361511002600319520140c240343c05801c01c11030020b083c3e440207203102c10004a4645243c10050440400c40e82e07141c4aa0f01160440390048480110680380c440c55100d4845c1e42d50303505440d650780104840180c2481700302c000201c2220702081300d00301070002030000c01740041e0002804a43e02d00620050364000c0da001d6804080c1d90380400c208500f01160440036000d4034a580009042d41900c040381c5100501c280c1d20f04540c0403560010301c5202d050001b03002c4903250458420076807203480b410050207041c0b05d010804450008c17001e81c048504c0180e0296100000c0004140d01401e45420040c0d04408805004006400309180090360b642c0c6401d1400c04203981c0ca8a4482c0194814003034528480380d0715840700d5104840e6410050303030006118440c02d50148070602c442c0c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 856311214 1250 856309964 856310053
    0x906060309081207031506020a02280905090109020a030f0c0f0f05060c010e0d200105070807050705160b0d0b0a080a0f110315091009050319050d020c07050909 70
    0x1c5c0324046e140030700d04440001da55a4001810b840550080b6089140c00d1481d51000140da89601c2030741c802154485000c2000d144160711540d404044100086040e00f107aa0009214130420340088414494408a1030301740041c0c0c115420203003104101c00200f45040079415551501107110b010312801d0000751085003a5001c0d0018000e0060390310446d03803180304405010f400700000044190128408100171042c401c014094030340629070644800d070703803a100c401c0202d03104e50012005840c40e02c0303490f03082d4516021540064006046c4684d02c16220407284001800380e401010665201d80754441b4244070300d80011421900c80781d0f100d900140800c80900d00ba4552140302181c050745409201e125440780440f15885520a1440c50140d4844501d040030070170440f4031701d21000d001680144000714990b030817002c2c0070095565908003c1d0524005400b00d0042c2e80c45010700c21800e8000700003c020f64200050640e03004000f000c00303070000c001c03048030f06048500030451140441c0c0106001ca1082d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 856312464 1250 856311214 856311221
    0x1b012f0a050c011802010807050910050306041508030d0c050c0c010804240510050d12031d0a14060906010612050711010e0f12041d09190507090606030908120703 71
    0x200d01c00d0700a20500003800e4200c00c40e800c5000099000c1549580007808c91031045088903117860000b031503154414200d1500300c5298100400140c2c00035560010603000d48070705a460001042c02c10029a500ea0244448400355400b40d00d40e2000d0110074800741201079408590003441050a02e8140544e944505103403034024461050020b1605458003000169010b50308014480c18910100c6103040741ea87e42400560045504060015540881c40a60988c800c0d003201034860034a05003020801c07860325032075041070b600000865082c45d201d602980d10300b005000b0303181e0004100011300003d6261030800f0308000a41011103d81554681c0001c5886000e4580030041c44a54802000301909291142da6507201520b0221014403488050b01c40d10411003003140d069501901e103c45800316212401c61100c2405480f80100b406900b002c0494040600c1d910800e01d40218010020170b46040120300403250150000310415052498200124000c4005c8030031542c54401c804a081e40e4205048005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 856313714 1250 856312464 856312477
    0x9050c06040303020a21050d1521200102063c0f090d0219050f030c100b060304110607052b02060606090907081b1b012f0a05 55
    0x12040100c1c01000349940066081910b9124280241010314181000150342c048040c603540000d0081005500b00361706500305a165100b07076000c0c070350f81a0b10b40c10302030124040111600c41c00000d904005080c88441d010403040e031680041c00310022484000003d48070360004151070b210003110842c0c80c00031031840101d0044100440c180000b0481326903a1b410040c4410b54038080248050400720303040d40c1c0302191100900d5096001030107890032402c160b180780240c00f00c0a494030b00400174014081a000d10052104a0f024006000030b490304440710000c039096002028040c000500421001405200d0304040c0210100e500b141c694203540381080c606107080c024440780154501c00d0010500da40c0c00d9080311070200303400b5185076540d1842845080d0291a00e03007540000c1d0280030600e01e030b00803010184c0014402c81c814414100024216001b81c0c480c54003459000011035072410709140a20484100060341030303140c02c1d0a003164000200c80c1d08080081c0850410004407192a18051030032200c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 856314964 1250 856313714 856313719
    0xf04051b0c1c05070219050907140c0616020d03060302090a0e10060f080d0813020d0206040e0c0405100825030b03011a030d090f14010507060213030507080a0503090409050c 76
    0x2446500c02c03030010016000b8440c1240038802e90320f440c00307101a20511820070b039000984001699601d620301210b611180d014030500002d0100703c0350142c0241402041e214103c1c0c448006900e4a00f860001e151440c90b40d075110816151100a0006950b1050f68581000d2098000301d20440503000b0582040800742c070025884d85000c00001d401d1503401429400c451801003910350385529040b0642d20300d20b040f980c0e0024064200c000500514000c0c0074004154000381c4101c1c00c094580d444100c070780b0000d40c0c3d1a84ca2000101c0c041140f4606a00c1600509565203400c0440d03003080303c0000c001c0c150903503c000054404148000740544282c2c49011481d100900911085000c1002c03400701c01d90b400041c50190240002c4020014010704040c0d00725030842841c00041440c01180404402108944904000c1d080290340c020404a0002d0245042c04c03120390300d01d1500d10702d0b2561500d660360380003482a030003c0c4c0a44010400200559864100a540119684805107030a9042c640940781d01079 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 856316214 1250 856314964 856315003
    0x160e010522030c08120714011e06090b040209011d040b100315060c120f0e090103060525170405100e1e0102071101031806060605090f04051b0c 63
    0x6000702018509504032400780310840c0701c042e15601540d440707003001c504030180e55600b04008070004001510244480300c4c3ca80001545640c02d0300c449079421301d2881030360f002c81d80f2100140a446018480c8612600044a08500e0b0450500018026000c20148100000044102907007561104c0e000f84445e280c004192a00c0300c080000054004c1403500520000c0c402c590002062076130040d0359207101560800305802168845610840340e907406a10745508000226070142c5450301c0c1d1100060103580b10701c46c00700309841d1220b16007110b81c8000c0070640220084181c2e140400340c1040542c150300210003034512055882d401e219140c00c080c7c0b0203481e071407460030304202c03451500440c07581508103a5140c6521600c03035a810203800d0b80a19200900400003803c04144658040c0e40852a0502c00c900481c1402c40785481300400c5640d0742d44040c001c035500040059081c50502a41800302604680c00c1185061103400c0b021400d4072040c40c0d03c018540026a29200c000801030542d0b190a02410003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 856317464 1250 856316214 856316257
    0x90e01052e020102072001170a14100e06030c0609060702060405030f030910020f0607050a030f0f0f0f020c0a03030c270e0c07110105130509010923160e0105 69
    0x34005d40c0700c0380302650013071000f141c400000c420341d00814858a80583d00c0c0c80b0b031442c450000c44090103000e000300c17050a583d0303054188070000004140d40325164078040380c195149403140ca5480e00c40300810051094002c1e896050319581d0715810756a1100068a20503180d0540d440840da9038802ca800c038070360520a483c00020603140000080000c01c0c3c0a4450201c1c0302401d10003a0f1755290120302c5ca140c00d0b04050001200d89110f0307000b42144c04a00e180202c4c050000480240840d48801e80c60002c058441d5120307078038010180901c08074003850020441c5018056828940c641c000d00400408140c4c8039202d90901501c103005417a0420b09140900d144030300450f02600b42d8450520444c80d800508000080029803200203464007150080c1c2d00261002d592401100c0302d5104111519070000418408101d0780c0317403250214040c0900c2000003640395007500e04100300702140719a4504004e03855042081a904191030013060320b0b11814800c18080c080001a030f03890140984000c5051080100c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 856318714 1250 856317464 856317467
    0x31509020906121815010b09010810120606030605060105180f150c0a0c091802010806190801050613060b040905060f0603090105071107080717010e071e06090e01052e 73
    0x24400c0c0e404c3c07000116204811541c2d0003140b500b00900c62900d4402040c800540c4c1e0754040c1c21215482503420051034805500c1c0c2111500c220700510043e10429610703c3c081c41084801d1040680110b000d003001d5040c4150345040d1034424506085290103001c0c1c002c03007003809440343c8040035600b000350301e01291501040c20200395180040c1e103003500c4138012036a0000c0c107201540301d4a513403c1d01c0c1d64030002032665a038005440003103000c0c01d41034111081c50107014401c006071056030302901c03050002146909105003046249907040720400307202803815900b04000303501c4404803070444580c5440403990b40e42c0c00300040e0301403030b01d6041950440310002c02c2084400b0103500452040c112034441c450b40400c0821f00607501d080034002d1240c4c6074814501402201c154015940c020310100c80003142103210f00510600b0101d05502201030a4500034040701d00740b0303282c10107601420701881c1040c42945003050000d428601031003120300506405080307030b00e507100642100c2024841000c5030010f010a6100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 856319964 1250 856318714 856318741
    0x27030f05151602060106031512050a0b090109060b0f0904170c0703030c0b1b0a050d11072613050f03030d140a180b0c030705070c060c06060603150902090612 69
    0x1110040c001d510000c61b40724040d1003007103038100c44803003100c004030300b0042220400020300209841a10503980c0c400001002c80300c1c4103200d0069800041200307501483c02c0310a881080c0c4486201c0e1010040c1ca41940d15048070184c1c1c0190889006004c40c4070042c800780280c803900301030302142d0160300b4012080c5a00700c54000081480f84141c0c0269030740e603d16a01220b42000c0c0c810860300720400509541c1c0e8402d41c0542800807104100182000e60b0540502c40755001120031100010a03207504455048040c038094080302092107146e01d01907014420100038941c41c082e0600c200d1254403261007544040040d124810015641040000a2101c2504001c207085400e1460b480c2000111000700004407264540d080e030041c030a9285032138510003850305400040c4447c0030008240600004210b61030189001481e241e111800d0b80c5460742824400e40c0c030385402600a040c10f01108041c0101d000b4510011140c20f03400050329603e100c0c0004144e8070400e034100544208041c2845a60410b000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 856321214 1250 856319964 856320001
    0x8030408031009021314010e1206090d020f070501031d010c21020f030c031503120d14060108041101021011031e07091406090405070e0127030f0515 65
    0x107082081160751600100300707030311804807990315105115008000007114286d0030b440300a8141007803107202c0c0201000ca01e43c0c251000c000905544a10f06000b60000184070303400201445201601403440601400355484015108441c109640e03882540703011443c502d20084205c2051f0001d00c04e05240700c8005210f0210b130b9030f030150503000b0207900aa24200750710880c1c801c0030250301044e00f190348440c60f520898000500d50000c480040d01c000d81240d40c28003c503100b0146c00b00310152214a964056002c550310030128501c40e041e50300600c18160381103114240e00c01e50188900300c8020310100100d06203036152400704a00ca0804124054100c00400a1840b480381c001e2040b607500400410034510003800d480300381c04215949000d0000b0350440b000000703003000103400707a49049800d03000701c3c084900440f4814009110240d14001543c0d200c00e4910488640035962030100380704e841c0700c08800c0d00520001300818804c081c41010080d0a1241040d41c9200520000d00391a0944030150600183c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 856322464 1250 856321214 856321231
    0x6091a011e06140d0c050c0111070807060e01091b140d242007031107030c0918060c0c020307060504120f020102010f050c1306050f160c030803040803 66
    0x5000228035001d080614101d12903511040805007881d1010507542e50b20b03c00000f181e181020000d6486088150003080700ea0b213010b5a0b4950303140c0c000a0120300310b580c40d41400951000801184010400d03910541d11781c260440300c0000c00c0302e0000c00490040c484804010100e00c480c6268410b03205074809035034103c0d510700301e040f1421400003040044464540c440201446003140c5400d460351100030b01101c1080031001c0c0003c2d4124110030b25400a088210740e000360043c0000c4590402d548142a404689681c200402c04070703045a4801c402c640303842c0501d265060b0780d01c000b0f8005d10040110039040c00d4002d10200014904001c000346032480c602c4099000703110f007110002d0300c41c2c410b40031181140c20404a2400707805041da030f070409002c60038405a046648440c101c2c03241500c544a00c50140f030784810f42e83d90b00c10340c90703e90742e0302000c141c0d0102c0240b050a200329502c0c2d1030160119043e095140309104000c540d1460880000c07056500003908a0030f01008020070000c50800950088440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 856323714 1250 856322464 856322513
    0x11a18091e0f0a0c0e060a0c020a17031b190825060b011e09030b0403051c05190e0c09040611160506010f1203031e020d02090406080c15030402010504030609 69
    0x44507054440d81d907610809508000c04008041d1022300c20840e109810748014601d0940c00c0d51103440074504074410700608015000020300c03804103428111203140080c1c008001d040441c2c103601e0448409040318502510035a00000c0c284001c0c2003035144c03031180c4080500344640c1440c941c1088001840c50308a02e5000c540303411010300100030030004400400d506946c9807000383d41075680d0b06040c1a0301500840a0041c10302400711000d420341e078041c102070920500042c5520b071000306001049500c4c010030745140d00d824510b107030b800000710304160a0356054407118001c1d1a603117000d030014104105d0b004400d606c00b2a40030100810080441c502c5030240d802c840c5180d80b10007104154060f54403070000b149241d044044000790007034004942d002c01240240f010014100b02220030b90b13020307104400500e54001000b14891501d0320404002e0f00c50080106614403015021806203810208a110030b0140403001504681c03041d802c44010b9544a50140041c140300d1601d820b08104103c9109103c080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 856324964 1250 856323714 856323731
    0xf1509070b03010e070f0309020604060804030f081029070302030711040c0f1d03071401031109030606011809090c05130519150b12011a18091e0f0a 65
    0x148010b80c1d0681d40ca40c00d804145031208842500c05240324130303492040c1500c1313601c000c0150756020090001005c2d1a10792002502d0940b40081042643c4030001c0700b448100400e00191310f40103074821050300e20030500c40300340002e001c00d0468081304220080119407000152034003010380c040041c2803664410310803203101c602c48504002c15209640310200002c2d041d0300d03000c245548904551200c0030225031400c981860240003081c101266074010101c00f10501c0c000080659140c400e640300840c3c80c43e900d50a095003280020381350381001c4c201d581008622027004d1344141000980c5001003881e030000700443c96843c41c0180740b0b0703421481040d10441a03403c81c0440f008a500034140f04403034501c02071107010310756080c0d0743c02042d105422610340003040202040c0c084040004107040d2403000310048066160465298860344070100308440d80c50180070194000840b080490000e14085078904019506c0d461400300041e0300d4901d0601c0218400103001c15144a09082da0142c010f0700c109215515 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 856326214 1250 856324964 856324979
    0x207060e13390c02091f0303081906030b010303110f0d1d1014130b0315041d0d030c030f15030209160905041112150a1202130c020f150907 61
    0x81c10507082d000458071860700300b401481d213241120340c002807811030040c14002055003071581c03c00f03e40046020075821000c0c08982d140706444049000aa10360030310813541503584030800341006100040c00e22459001c542c811100502c0305080040041c1c0888194400e410002011030624541000601a203e80003101500301100c8110b29102070342c485844580070110780f0003240e400100b51229000c1c1100000c258248080b0080d800344410074408020a2120710402c011a200c0303207440c1c2e11b4014100041304019001084021450400303090008070000d0b40c10054002d030105101120341d151901402c1d0f95603041d10b0300450290b80c02070300c01100a0380c403c000400e1115280a40d03c2c0452031802d8100010f01d82500110150103914695608001c400e4204c407040314015101204081d0460340c12501d00e04242115100805c1c10880b9540041c0050300802e00201d0090a284402a203665528881d58020480d00c001d9228150840f030f40c20303078041c030240f1000d4001c0d120400d00d03000d91080011046c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 856327464 1250 856326214 856326311
    0x1e031406010c050c0111010209030a0615050303040509130609060603051e0c0607140111040e190203041218050910030506010f06020c06030a1e020304050d0f0207060e13 74
    0x42d64403400400b02400200c006441d40f00d007004a114480d9000c01040840d0f0b00d043c4169004c56201e9003000c00c00e01040e1064074040e01a503000705010ba441401304000c0d80e940c041c04946c00c0003402a59104e0082c5c0340c100070001d030030b0304000070b881181407000000070000005554803280c43c040d40340441041704150300c1500c95010001e03031940030030140807407070200d20140358015140f280400001421200c0401500e029045070b4000070901c00801c0821001008014881c0010740002c40d045181d440c15580e48404101c441c9049000c00a00080e20f80181180030a28009444010320b024094a0820030080640609001c204ca881c0295000021081843c01d801700c20b480340d58024094000ca03020900c6a1500010941c07405c0359102c13114010480c506e1913a060303e41220003c056542d04d040e050035031604000050060811003104911000a980892120251061307442c2042c10601c51000103400002c09075006900c4d68a04440c2e030300b00c002c0b01520425518402000030a00741c01040d480b0f00c44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 856328714 1250 856327464 856327487
    0x106230901030c0605090303040806010b0c070b16030507022403090c15040b28030b040c020d120203090a050114070207050102030a170a0f0e0d031a060403121e03140601 74
    0x80c60f007042d070240440e82c0a41e010b0701c1c900c800501102d0a00303a80d007000521300503080c6e000210107400000c0c401e03022202401404040c051441c0e1007860030792840740b11505500c84010203020003001203500c6086643e16010040c0c0403d10700c50800c2c05c2d515101281c819680152000c0880740304810034007002e1b051019285200c42842810f5a081c2440e000305c800d11648410a04c0301a0f0044424240b4000c0c041c08040d108810207076400100c4c1100c0105100c100c40d01c0c1a0804255480240540c28090b4400c4c000008039203003200150b100c4c0c440540d140d151550540c00181154203005a81c11300f0b24900c4042441568280d08070703070440f1fa0355401640c4900ca03400344240015840341000d842c000e40d00785495041880c03280002201a05c00b640c40d011102a011504000d40010040c140c00319070600849408601c254a004000c010410014460344501d120060822601c00f244948646c09644001c140c05c200314811510b40810f13079002002080d07a030300a40b08407121500401d40c154800c010315501c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 856329964 1250 856328714 856328723
    0x706141f090e0c0a03080a170c1605070f12120906020d0c030c0b24190501030504050a080f1c150e10080d020d0e270705070203010623090103 62
    0x16508003407a050240c403004090020760712448011150320780f10300550100540c0540c3c8195250007200300d0051511400c00301d10000c0302244002d1120040b4984200d46049203480c4400316176200c01c3c41d0550800c0c5c5281d0001000c80e03501180040c1a0f1052a102d004440c41900303040d109105810782642d108055006030360042e0b00c41c500c207903401801800820720b000e00038142000f11014680d1030020204080b20100264404203042002810b0050503800d000300e011118410401340d54403415503a00d01070b104060405407201c02040500800f403000d0741180d0f030442000c2d0740d207070721103101134015502a1070704415600349540500003125151050718904034107107940c45521482e011000903014005061100450401c0c600018210000c0113200141e4940d038018090a032080b02000e09a1100000201d004043d0740200b0300c5180a05000110200c030301c00c251003490707207030b0b40302c103d07200e0040c440020b406620340500840d60441d8071145051106031164184035800d142030903c2442e0100b07100c001c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 856331214 1250 856329964 856330021
    0xc04030606082d120f214003020d0f02150103170d05100602070f050d0b0c04170a0b010504090c1a07051b03060115141806070614 57
    0x4209090450f8007014080d40804440c208140c50740110000d510508141da2912400104030142004072402d00241106041d0100503518112410010803104080441c01901c100e1400b05504000e020040b4152002450f0a040480483c0781c080d640d600e01070f8001021a604e800c242e0b07a0607100140754040c0c40b03410802642164038684d0307803d40b1881e8488a009091105100100101000c0d03c0307141d1041641d00c440d050318500c0c05801074145041900324004046000b40d0074003450722040303812180c01e40c1c8044460016914820140e020380902c2d00310307240301340f01074040c101580c80000c1c6822000307028a02203031036642e031503003000304581e0b1380030b001001c0d01c065003420800c0031880980d0000c1941d019414610f094036640d6901d080612442030130a10380c4010700600e1850808001150140424003001115041021009032803404003c2582c41c040d10005003404040203020084280e030000a42a82c0d01c61403546045409001030a040c00e41c80e4800500155a00840c401d401c100d80b1042c2c070401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 856332464 1250 856331214 856331263
    0x30516080a0f1e0b0114060a020a0f03091509060201060f030f0b07210f050105030307080d09020d0f12030b0121200408030712030c0807050d090b0c0403060608 70
    0x118008031107402d0540d1248440d1681c5060741c001c5801c01d880851140d13200d00003d60604800c5d0105a070038100c1e5900660301801400e520f560001884000c190b004082010b255049150444c2c61004c140c200c07800780c09505480300e210a4021000710181d5007a60024030105484500c6550700150902c0040c0007078400303984c5000421030800c41141c01111f81e02e85051a1400c0f03102000000d442c0b060440c1405946664020740300240c1c0c440d0f14050a0124003079880c1865680f07400e80a0300030602d14040f03642d03544e540541103664030310800c0c81c00c0368006010756111003281000d040000c452250480400d0401c140c1400075842030b10b003c0380751403101c80903002c1810203000031001404203d07520064401c0c40b103003138100b00c00e100000d04020316040c801036980d4422458000110f440442d40f0005050038980c40c540d0090304540311541c040c90920306503841c1d4240300a50340180c110000080d100c40003903000d0210ba03160b0b8a00401c02e490040005118003940c503c2034541e14001d400c0503c252203440005c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 856333714 1250 856332464 856332473
    0x1406060612151f03320703091211060609250302040308040b0c100207050316050a0f060b01110a050c01210203070302040504110903070e0c22030516080a 67
    0x225000b003106407280b001d01881101040707902041c00c0101002c1030f140742806441503850300883c20100400040313a02114080354112295189115849181d000e080c0c0025011501c00c0d8415400a900700c1014521546107400246c00304040741c402d19050b0103a08002225801c005103414002e0310b07803400c100107201000001115401c100089031003003540811000021500314400341010340310080061365103840e41e0704a0351900b40034503412180c950050004c1d80110b1b6010003078402d60780d4400110080110705150180c282000c000005180e4044000410b043c0440c0340c2c86102010401c1c0c1b00c28410302c41d401442e5a0754a0268130081081c0e1284c2e8010441e9407069140c005602d80048107021221601a410790980e0000c440000020344d000c50304116505d0f0501540b80041030310300c0030500c3c0803911004281c59014078020b2180780c0c0016804241c140f222202112034a001000e0140c1d14500408000c69403501c1601c0103440911401a400210f585102c2c190350440c0c1081d0002c08200b100c4c2e594 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 856334964 1250 856333714 856333747
    0x9060c0c010e0a060212071d060711090906040c141e0d080a02010203070206130515060609040914060f070c0b090319031d0d0c060b032814060606 64
    0x50301009540356108001000010000b40702d0003845032a001d82c5450000c180c040c42c0d16001801c580403c020014085103000c1c050003134291405d400d46103195641501d040501040500b070040a400104001c104180d11f54013203801400345202c0e0481e283c0d087d41c1d039a00201c90030384400c4038036800f00142d80315050912002040850200d405000c1c2e45200d801c98858207625002103680c840541d400104201c09503a060084d103510500400031345140d2142c0381c492556a4001c07248119601c04e03c040400d80c1940d80c0c00a42d200080001e01c103100030400703071418400f8a006000102c0b072a20884010071809850b9100084c403941c0655103000e0821000d84520403441c40c050440901d42c00204489203c4c100c0d0742a503400c02951980300802d951880c40340148500709200d17080f10f09070b0410500409025440358407509942d40080010030b00d12480310000b800c144031224800c86094140000c00700e52840c0c1c0c821513846a00807050410385044d4a0f80079512854200c480980c41001003000310f40c0c42e00d440c1c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 856336214 1250 856334964 856334977
    0xf0405060319090c031a04030c03051e04091a060414010c110d03030b10022107110406030629030309130b0307030c091d0303010504091406010b070c0b0309060c 70
    0x40b214010076481c40284044405600742a1603079402d18200303009000341c0641c0c801144003040c1040c049803174180c6005140c8911888020100100004c03801152040c00d906007a11410304004036030358a0391030205030000c140400f000540c02081c070301000702da80340c01020f403411100b442c050704180d4009240112480040c0d60003c641c0b0340c82c861003401c803645810461a1081e0f00c2602d000542c071070940b00300200a2000d500410455200740c1c5a581c29a40e09a0000c018111981c07040c0c2c2c4501686c0381a0b0703c031211104000d40c105140040c00420b0140c01c2c1c105400c80c1c3e107954444440100340707035108200101c015040b1600350b07008102c01d022504049010f00300404807400000f82710070b19180024200141584280c078811840034040c0151207152140e00e414540480c80c00b603010142046403074807800148905c1d4030543e60b58004034240715801001c04a001514401d5940c00d40c0c4440b40c0c020950440711041c1e0300c0c220040300c08039141d203039002103900601018004151f03507aa0a5800c6485a0010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 856337464 1250 856336214 856336231
    0x9070906030e06093f03010f09230c0417030306100504030506010e0408281215052430220203030c070602030909060d0b0a1515020d08060102030f04050603 68
    0x21101700e1542c0c0c15108070741c0112400b5440030350340c3d5141000400060403a900400041d5207441886022141d0302c000704009803182d000c80c1e56442e40d400030701c103441d4026a4000d1b4841b9001d100e501101210210045102d030500312071f40540d24400030003c88007405076000041c00e0758462001803000c4542032120b41e500500c10600c491400c1c2080c1c0808203818401d08a07143e102da10a220f904055412580860b52803e59860402c10080282d903507022588081c4201c40c00799400e4000d15076070091840f0444200c180d44143e803550707090300380480b2181040d454542d60003511018102512171081105003801001c954039101400c0f0f0412940348040d1000e0002281c0c54401088105440b901c20303c2400000c00c1180c01541d140c002e810b080c0110f1050090820744034071401000b802c005110101041c3e00580c0c08400000d62080101f0030700b032101d55940006a42419400502d002c5c00c1e1300041c40d0105110513a01c4501c10384500c0c0c016070b540c1c01203034002d451011040c081440705041c00707006940d200426 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 856338714 1250 856337464 856337533
    0x1b06041e030804060804050706140f030405120c1e34030506010f032a1e12150f1505060d0902061620011d01020a0209070906030e0609 59
    0x3250b07210551580294041c0303001c070b00100f0400013072110a10415004100600300001608016038003042244034602015510402c01700c081802e020040142001c241c40381504159509001400290364100044250540246241425011440c003140c115a40d09401c3c8810035040c0780002c41842945003003925054540803001d001000c680c1c1000000e000f0100e503584610f40d98194101466903101184080703d08030560070015948001c0400c0c00380880d442c80c190318504902074244041c080d0707056807021800031104e4504a083c81030890080045101d9004200f0100c118120114282c91200d03125201400101d8820003442c10004000c0000c02c180041c0012811101e0380041c01c241c1150112103105540404e0f48420000d1920800c94014515013000b038a14982000080040b151490a00703240055a003403198264000c011400e10303070782d008013862141d107400134004190500c039101d4000041d0514524001f140d0300400c2e054000d880c51400f4020540003d00e9211440a03402c249448600b013 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 856339964 1250 856338714 856338719
    0x3150402030a06060f05030708011401050f010909060602031c0b09061903140601031208090d1202040320131802120f0d1205010905011d040c1d091b06041e 68
    0x6461003060082c180c000b4105d40310b1401d09081c0340c6031040c250403007901e0f40c1c9407a01080f0000007849034541101d0089824801074012100126001d11242c0d00070608142001c00c08115036070040044c0071a40e41d0308650160f5001c0080d442c0060301c0140d17013510b401503005804500e690501c4010340d9026402042215001135503644d411a00008400d0b9500c10703500000f0041c010000d64080b030074002086403400107a2811b080b002c207034495000809240034000d0031980700c0000301c4181c040e40c00554214208032003072151500401100e40031402d4142c4a4400c440c1e180401c1100703032250140c28000340e80c0b10001c41d001c0d40d00380407580250300702c0d4420360310483d00d0240c04024200290294509030381d0f00e4050749124458054251a0180c2100720054148001401083d40790b480588503141c03032131304190868445050080c0d6464841d001014507200d95510741030b039024824440307406140c0007400c4480341c40c1760300800c00000300c02c0c00780140d000700c0401007005070043c02c6c00750300000d2030310002c0c5062080d0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 856341214 1250 856339964 856339973
    0x280201020f0a2303040c0b090321091302040609030b1012121805090a09030c150e061006080c0c010b060a03050108191e0c26100b03150402030a 63
    0x704920418800503110b841c4641c00c03039509043c0b20f500f484002501c03a04500b4282e0310b041d00809035014082d414540800c1e01e1141d6a000c018045101a039401b61400342c0045061201da03075030040303002030300910402d164031030291403501c2110b04641050740d0f805091403c5641d040350300900907080000707000c840480419408203000400800b0780c4900ca024035620045800940741d0f20843d8090000084804400c0290f034550300c802d10b80c0450780400000b0f980c2c40307602d8240c800115401d00500500007410741c00450382c58070382c050075402448500f03c0301d05940b080c2c0c0c6400c0302441402641c001406031004038040c58050f1014220908880c4000720b103040481f00880c03665000318010000198440740100564201801181b452401020101c12180030b541c80f09034000d00c0c0950b09010b640c85004408041c00055140c00c00500480c04981c0048864054003505c2801c000d031610300940643c0303452001d590080d1181c1100150090094061031509554100241c0349c020410390701801158041c44c00078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 856342464 1250 856341214 856341217
    0x20a09060518010303140f0d110306040e010204050f01050f0c010504110103050708090607300c030b0102070f1202010318140c0121050907030212070806060402280201020f 75
    0x108a11440003844915250401000540b961211009034507903000500101c1c0d401640c3e02c003105504500d142e6142c01600e9511440e210740039402d4065482c2c01001c0250800510086000f0381048500f444080d015010403070807485a880742c654007010441e02c2d600c0c50350140c8007800a800c40c5903030540c140071690741c40c0f40c20341f1402c0790b0072105100701e0112b42500d5a05031107a2a00444c4614040143d450004060390b40e41300702811200610680d00c841118111240307449124055222882d0440040d90040400c00703090151211170100e400c0c050340344102e500c0007030120202e8006102c1c141d1000e06d08242036a0706000300800364101511942c045020b401c0700710f40f03119114490f06185041016080d0050f003810210034009040050302c00e1702000d200e0354840340ac034402854000011707031070b200c60540500d46007041d48001d4010b090743d583c1c9072460101240f00000c590450083e10007564890081004a00c40c03c0f401078401030080600b107400301c8080144886803002c80c00014035110480c802118507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 856343714 1250 856342464 856342469
    0x2031201060804031b021e0316030b060901090c021b030a060518070e010503340b0414010804080f0a03140a0c09120b070f090306110a0305070f051801030603020a 71
    0x21826001c180b204145c1e0090300c00c49030801c400c4503040082c185a00294a200b155864032a514a02c0ea1503400941c2d410b01c9501c0240c0f00c401150849950342c0e2074a110310701400c03214648070b600c50700000940100c0350b01514011241a41c0036244643c0a1440c10200c042d080c85401d415200e0301010200040369842038a00902c0080319040c2c50741d004000c0a460220550030102a403101c0341c004000d207803400251400c4550b0140b031031140b01401035407801800b0401080c00e0420300b0b9020130024003545018000c2050f00c210144854045002c6401580c44600a403401025180108800c0d2910f01078407002d000c1443c42e40c40c0c08202c400c032400c55081848015074080b82d43ca039451400c1d00c41c41e82c203c4207040082c043d007840f00aa0004c0c64035180f00401005020509005000441c11611031007290844d003d580e101404018031034503072444032000d82103c10060003192910003c10543c500602e85030780790307a1496039050b00d8040030066000288001c0c194142c140f6031680b0001c40103940e00002c82c0301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 856344964 1250 856343714 856343717
    0x403020904241118031f18120c2003060f0c0d0c050d0e210a1e050301030204050105010c02031b04090c0306140f0103080403030e0f0d0507031101020d05190203120106 73
    0x1302c0d85100c3c0c118081012201c01c2c0b40e8881d07031000010702880800c00340741503003081041400280c80658080700720241050b465008241c000561006e400d116080a50844514000e04031401c1c0c840f0300d500206589800002d43e25030580c807071000038018445c419007480d48501450aa1400c000100340f140c030a41d46580c520402240000c034480c02c100c006845510f030360100744801840c08888041e03000e1040010312451003001000000c0007070b5058011020810580c510344411200d9980c001d800900503042070000320312a40c14080001410342c4100e20a01009800802074840c0ca400d02d4a50090303522001c03030b500d800030749402c041d01c0414010185000151f0041601007110072200303914400b80340d07000b4036a0052010340700043c0b0200300e040f030581c0c040c0c0b90300d42009442102010000b420b021005c1c4400380e07101c1e20101d00d800c1081808502c043c1107074428046003071100090001a42c4801c0221600d400095007840344104032a500031049082c1703d114010313030340341011042c000304004000760000c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 856346214 1250 856344964 856344967
    0x903140616021614040b03070f031a0609071d12070f0e01030f06050405011508010207020f090910091103010c18050a05220e030a090503060a0204030209042411 70
    0x141210804000c0c041d680510251542125541e0f60518141090280d0a01070920040c2c0c4c129544642d80511380d00e120040881d203000303a5550054809140c07602003122100c5807401215001c03004122440d0258030000d2480f845d603981da0b901207a42154079003602c2c4480110801d404a5034540c20307410b680740500213002e4001e0301d048c00f000c0c1500e581e0b00c0c2c0c40000d07a00041401007020a4101d0302c20131140341e01c0740d00883c0d2901e642c18514007600c1c200d088924403900f07200c80062006130550003041e0003442900d0042c4524102020848400021036030b1241c3c03078210701d81c8100c0f141010390020b83d40b81c0c070444601101b00c0c68880400d003110350902009021665080c90242d200d241503003920010306c802c4940d40055400c00003c5a10741e024010b00504466503510703000b15003000c1da00010165540081241d850314003284c401020840c061148074003a018040c040b5030700d482c070f81c000c50b0162900a004035500703499550b036054031115010350b08240017600c11548149400c40380a00700302910120082d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 856347464 1250 856346214 856346221
    0x100306022a060903040308070503040504150e0609190b060d050403030212100f0605030720031809010302060a1b0606094b0b04050405250605090f0109031406 69
    0x10038180d40e80c00c00140d001d6116908003c00d1241c0003044800b40c9501000b02520707090a450890b14600594100551150400340c00c2c11802c5100c07080b010880e13850a42010b91622400e050140c0021b0640b00800b0b6442d586800d0320b4162107d4120211141b80a0710b41450400124402c0d8100d40e02600e045001940000307548282c0c42d07000141a0300211031030011081b0380c2c0b40402141d1184050310a943c18464080000351401d8000c000d20342480185502d44c001d00d10702d24031181d8032680300004035900344888680f5198541029603c95050300c1e8064082450010011000e544101100300240c11445064110f50002600e0b401a2401480c1100004ca190203890b4504428004001005051050320070407070001a240079400d03c01e45103103c18522101c582c481d500902a009140f205034100d8141414042040710001e800d0400704101c076034a040d2080c0c03801000d00894018403540300055000d00c890081840c01c031020030718580741410b222a084c1d60341c0d80d400c1c03241c01100700e04646940048040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 856348714 1250 856347464 856347517
    0xa0201030c021f02191403070f0c050a1202100605150c010b060c0d0906080c0702040507090503010908041502070503100b0a1809030e0a1511010e1203070212030609010b0310030602 79
    0x402d2100040c50600380c86d5032100082c0713141c890000034540010003440c1480c542126006407404000e150700107050314a04076080c20030308410b0381001c105c200140b05909440c84200118400c803015a0030042c203521050141100c4040c458002c600340c01541d5680f00060303030841e5900c50090035a43c0310780d4041c0c60314a0140c400640784076140c0d8088810f0090003020802040222400c032060f8660444000903242c82e400030884420641d03400090f01580380400c0d42d0148288c03000988210342c0d003121401c0040103080e02c00c82c0c86842c944201034265006c5241000b400d8080d4010b2200d0107006072000c0e0a803569034038000c0c07401c801d0255090049070b0310807445082c5580802c440c0140030b401e07a1b07590107541c90059140d642ca2990304400c0200550f42140c588030382001c3d0011128071641008441d281440340e1007521041e03000303640490152162940c6219a42c07212800d4174071a65005000078816845c04040501c150301c010801d400f040ca8154000c8001003082c070141c802c401d0008014141c40030688034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 856349964 1250 856348714 856348747
    0xa0309061404050a05090a0902040c02160b0a0504031e05010207060504061a090a1a1002061f0b0904050406181209090902150a091a0a140307020a0201030c021f02 71
    0x4405150307150400c0706100c3c1c2d49031001c110302240d60940300c084440d603411080c10018241c400c00250300c1414020440701c1c141d80003c00308510100101d0340c0481c0c6580b00d020b004140300301304520003c00d000380010000304070900a4500d0817280114045d500c81c084d91340340ca00b2a4030081c4101c0700e071550382060106001151003484410680d880269041810440000c2c0401c0401480130000039120410042c44920b00800703050900744c0603081e409803140c00302010b500c8200455003060f03008800100751031180000c061a100300d519002e16a480d00c801c04003440080c1000610599003192520080f4071700480058907940041c1c0116921206100340910060034080380d5404140041d041c01c5104016030340c0d55a68070b1401e070740c00b604565038103100102600c900700150302c0340b404c04481038110340800c1e0340b0310002c0c20b501c003255039010f13640d50f00d000c00ea401a000641e21100143d100345038400040d406548550091b0001d801120b0260000c0c1d02c002942100304a076490700300d900480c81d4520000d0820 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 856351214 1250 856349964 856349987
    0xf0d120b06090a0528120218191104120b0f09031305040f0603020907020303070318120f0201021c020403020307050d03080415150803131a040e0907080a030906 70
    0x507103142c41d02180c2030008005203400d000703c40c0724a0040110201c030304000902030013801c611000301c4404e10703642c1c510928000114101030f80506040f440c43c0c20411800b11103544616040b440d20703c0603035250303809003008200114551070f10313000c03c010200e00030041c0c003250700b0340521a0840d45809e10b0904402c000c085400f40101007075034070910400781e15014840441054640c107481c0041e896811410740e401420840d400603401c8119842840348007940800254416505628144512461200605490004100302820388186486000030031840341e4019107014019100150400c2c20200000701e504036802d070350b003002030340c0083c0030811401d060000303d000705030441d5003e002c1c1c0e2883e00d019003091401080285108030f64282c0140f160719a44c003c40300c0b0ba03038100030005290745402c41541d50b0350100f5074000440d55103200000d0a800d00000510515010206c094101454504800c210010142066401e80204000810032360703000c121206105000ba82c40031401d500e05800500041c20f0354 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 856352464 1250 856351214 856351219
    0x130c090b19020705030f100b150f0703031a0604050d060b0306090a0203100203010b0a14040b0313020f0409020a0605070309210309090501060f0c060219110f0c1c050f0d120b 76
    0x20071485070740d54000c5040f10f0061f10383c40c00800c81000c060300080340b039051410980d010980c04074488a42ca54080d01030800140319132020002c1d810108080c801c0034140c022100c0e8400403c00041c041420040c40b400100b901c0b90b4008140311704488002810f00c04103d894403101d40c0801207039025841d0400c920034003040c81c030500718555410500080c2c820b03c00c46082c41c05000400f0020841800c81c10700b22801011000101e9480382046a0307070301c6d06c8a105807820b034410707090440072201e280f50074410810301030750003031090750703104c0c80e000081d99907400168050701070295a60000540c00c40ca4110110310507008054550114110f1070081d1440d150b9400c11600c562615006100051300084200480303503240c1010140710141c1c4c41d003000a8415040244030320a00281803010694010030703c07070006030b4407606581201003015080750b0745003680c3d801140c0c810000d602507044451052080e114081c0a9425942c00c08290b0000d113290800111407030001648000031804c0c0f208a40c410304010040c02c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 856353714 1250 856352464 856352473
    0x30a0b0408031b070b0402150c01020a03020306040c1803150b060d0906181a042a06020c120613060b031e0c09010303020616360b030105130c090b1902070503 69
    0x1142c61701c1d490110020002409280541c1d4922401e01480c1e00b0b449801200b000250b5480f0701d06031000f0040c1d00b050b21564011407c00c10341c058201d02541e80c0002c00112062081d00851a40e110800c1b01d81000d81800c80c0c42d030741c0d0a1744010030740702c2078010300f115040404041b51307054140c54254200c03100584c07a03000d110030701c030002c000003540040c0180700703000440821002a19a4100300b0000724a400a003241019900381140daa803000b00c0c0820201d4001d6000c0c2c446d0110004148004030300200108600b039003001b03002a10307002c3d94490610405025a1001603498010340c0801c3c503141210f041000c00c54040007000140190410a031b044012059400c0320107545550740c040e50f20354001d0000c03402d1820309071509107054480c0c18020000c980001c24505e030303c411a60380381c80100c68580c0d40000f1103540d460200d81c000c40d140c00ca0b4102c40d005004d08140c4001c3c800c9020080c05104850002c00c20000e50010311034054a010300440c120204082407060300d400d1b8080c0c6020500e61186003c1e402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 856354964 1250 856353714 856353727
    0x908060708041e05010509070e010b0406030f020f0f040e060a031205071a1512030c031605010216060b030105090c06090415081501060f030b0a06030209030a0b0408031b 74
    0x4042001500322490707007420a19919945000a82403030000100600f0380341c00844001440015080903004007195810b851210792101000303460300e0024040c912804208010421030b0a00c03940c0040320240081c0401400d20000041e4203046911020103640301c080042004d001c115843c2c0402d6401c520200d803d403c00c2c1d441d56a030040501c0c0c01203c20014810017040060600c12814200801c02095900c1010946003c480030a01c03920403c0085000320000145c107000240000101c600985d032003801103061010495001003004403401040398155000e000d0807581900721000000c0c40c503c45d4a0114040305498240350850308000c1044d0100e03071140c00610700d503484982c11076038440e07402d840101d000d10301c1d40c800359008804c1c0ea0190136103209902502c01c0700710504001e14180d58590792a80c0540c03030281c10450a84070040d08440d40040307101c200f00031142c040e90042c585841c02030156030a01e00301e030b02d4442c4161011907085e10040800000c0000302c0005040030f1000d41d1f0f0a80d4040c1c00e044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 856356214 1250 856354964 856354979
    0xb090109090c05040216050706030606110102070507120305040b0d021c0b0a090f18050f060603150f0a06170d08011508060d0204060806070306031106070302100b0103021b0610050109 80
    0x36214403c25004550004540d80510000700346440125042022500681c2c1d9455006000b816031b4441c010010303560408025a5840c10b000304c58003140c101005100680c241514082c010041600450600904000c0011010010005840a02010600141c8550017030480202006060203841c240501e03114007848113664003103000040d508424000140c2e2056000c0000042014100f004c4000c545240101c040080010ba04000c1656043c1920516111902403550742c54203034241c0300075841c400001403c880402403005501c5664540c4c08680d807a035448030000a0003240c4071259842c0c200102e5080c1079500015242d004005142a0605888000e03000400c0003002034111849100304041502c01e41d5100d1b003058010b05a0074080d503031a414031070f00140091010b44001c480100d020360414801e0310f8030780c00350307020f1513015009003540c00c43c10301100e0002d00759001d00e04d043c0f541c280035180c6050b1a00826a40c0803442d40000c00c03150400c004a4800d0b5941a8441410041e418800740f2829 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 856357464 1250 856356214 856356233
    0x3061c14101b030b0a0b0f0d061d0127050403050a0206070e220e0706050c06060303090f210d11010e01151a04051905180c031303140705010b09010909 66
    0xb00018600040c01c5401c1070002010b02450303500800ca809000b01b0001ca0f044074090050001031004581001131980e50103004070485075084241075030001c0000104940c003829200d0707464800000407030042d80c10991003601c1c00c903042910140d000840200b40c4007951501001165000b4005003068000b000d00c1d0070000c1c5034410501e22918091804801109a8078055000702c40c40e0b030100010b4506443d2240d4006180790400d010150603840352101003189418003200f02c40007014007a08286440510100f440381c0351403080045080f072588026800080310042c442050b07000390380d42c6c80200b5400e08003103403825a2882c081e9034040340d16280551900022002c0d884003100d62201150070100c0c9216a5080c441c081c03a401309802c2103400d201080350b821000098015600300311004640d00e82c0c4541180c0080904540c00090744100b00b01064042c2043d030240b0324858840c3c44c4c9481d21000190607480b40340c0000a045506e0382d101c59507819203250120055016203a0100100119013981e114080c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 856358714 1250 856357464 856357511
    0x14040b0a17090f1209040608011409190519050c040e01020c071a03010e09030d230a020703091e170c01030c05031303080a0f0e070905150901090203061c1410 69
    0x8070004411300e172074681c2d0b0001d500800081c0000c00c2641c80301b0803c1820380c00100d4032030b409405110702c80c0c0c921407290f0325052071054120004120b03850302d00031048040070810209585038481d40140a4290740c0324003070310220196800015888500c500c84603403800b03280d50480300800e04100c06082d08241d80c502a80d0454400820106041d01d0703101140303003180314140215031003e00f0f0251040549126a41100c0d00100e08084a01c140e45d07007105681c124003c00d0001070003d84030300410010100945041ca8551009080070b00080383d4541c04c2c0103581d05041c2e458007030707500301070712201a646c3c051041c26051011400c141d441d61401107500c80140760f0441c40101030102d250301041d46456141d10079a0414151a0100310001c90320040c16505e420741e200e00d032951414000091403080050340807086400d00680954056400e05031464041c1d007000300b8494110b025900380f20381c2c1e01c410502001409000f040d9112150442590003402c0503440e100f01c04d0068103207000191b10a1407400100e10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 856359964 1250 856358714 856358743
    0x80a110d030c0506010e0615120a0e032505120a0f0c06060521060c090d03140d15170607091419090c09080d020a020114040b0a17090f 59
    0x3245560328003540e441d00196000350140c498030f000442c1d44480c25010500541040b640d150410401c0b203a0b0105c944550946107203107002d00d101151980d41241c000048044100341500e05140c010400c4510800c10002d8108241100314210814040280500181e40d6044038440d40341010460b009810003c0c002d82c0041003252540c1054144040da91003a006413400a0007a42c1c0c1030048420b900809004034a080218043e1001080342842750b03070201d840303000e0040c110b40c02822007510290f60801c01c0500c00c3c0c4883d8400c01070740540201a120b6050748030030f200b603201191402d04c144558072482242c1c1c200c80c103072310032170503c10070b1a0003d040108840c0b08a13100a059030044012401d00004040017a4030030610000204010005802c5040000f01d25699540c1d0700341d03145c0401d540d40a51240b80805a0800054040554031a0700c0071108101510b118070718060741c402181f203040e0b0080502500280100010043c0200c00710101c50f0003070991001001e1011a08103031036101d8542000c13408 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 856361214 1250 856359964 856359979
    0xc0115210b0a0905070e150306071b0507120501060f09090c090c1106151005030c03161103040e0601080f250e030307050a030e030a0b0c0a09050325080a11 68
    0x4108510383d41005084941c480d095038140d0b5030380c15401e103854000765800303050020400903071036070f6041c00a207481c820065940e034415a20700f240c02810704284c10340e00c290f81034041d5180c013060080309c81c07080010080c030840000074410f24055156010b00460b820214046040c0b030248000700b4030700d1051805071402d0740400205a4010401551040035114001d8407a0041100308008200c070900c01541050080d10710004070014000d0495551004417403c1a4226042c0041204111442003071129071400b030170710080322000100d003103245400a9016080040642c800c0102e1941d001807421380150096180c044642002d0354008004d08080307a10383c00032a10300c0e1020109506c03601f42044054005000d032030f52060070b400d14a48501c5117650542c0400d182d41d68500d030074240003540e0308007103400807808404c0d611103800000d2a42c1c04070b1030220400a201e840810159000d1000440d404004544e04005a40701410070005032880c0d40080748030f400800b01d0001003204814102c031011021160702 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 856362464 1250 856361214 856361221
    0x11d03030a020d0212151c1a042301020408120403020136082116140705040c1d190618030b0106020a0501111809040f080c0115210b 58
    0x1040240a98108445903440017804d004541c4100403034090a581c0030b45486040010f482405092955a034000a24212200e550807240c0110f100c41150441e00c54801401034008038112441314001d6407101240c5030750700103400c02078404200101040b00d805800344508152850300080c20001e00c0d01481109054602c181580340710407503105124a5401c1c06c51521115140c595150ba00ca20080b08e42d8070a40d0082d03445042c5814500a440140318400ea4886076084c259403841d00d64000c160800304a4882c2c414082001c0c1e0359170080300410703111503441c0c40c80380b030b09030420444500e02ca2007407600070b1240c8402214012401c40070300c01600d00c64101038401181131128281002052f5001529040b000d078000f0800d03960201d0a41082c9006078001e110342240480701c0d0016118560342d02801e4101d900400c6050304240c020517a102c2c0c002c4d03d08840c11071068640100980c8080a40034049e513661040181c0c0d00003515102000c1c0c0000006541d036440c500c00ba5032007030796103100302418140380000003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 856363714 1250 856362464 856362487
    0x10f030c02011d0c0306150d1e060207060c0e150f18040612030207090e07090b04021c0b0a060504080c0105030c0705030712030e010e0d0503070905031509011d03030a02 74
    0x108959201284000003d10650b0980d40e00c0d4243c64160511a000b800c01060280d502074140c1d0300c0208005200c5034090409694422050940f0500190b0711100481108081241d503c05400d21500440000c541c1000c0301c540203001c54001b01d581d40c494061b00010f084000f1150b001c1d03550b1104480180c0d03a8814801075045600b15041c60f02c0c9a005052002c0440c0f1001c503038000c500282e20a408803094280c490100d2000c0e108000d40c4040c10b540050020480c403512500901c1404001600051500d10010f110a440351541180340c4000b03034660110860900789041c5000060005150040c1030034100040b158980c02c0740d04140d4100400030001c44c1414045004442035664400c1c1200d42c6c0e0b10309407800d02495614100c2640209181c0681d280d92054180140c078001f074160f0000d48060513814500b0758240c0c1010b05110308204155201058588080080c0c20507d50170000f010150724101d6202c40c2555403034102d4444006000d019280c284100005403900520341078009a01c2c0e1221880 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 856364964 1250 856363714 856363721
    0xf020402030a0b12030d060b0403030f0e01051210051f08043908010b120624030703140111070f12140a03021909050607020415050303030103210c02010f030c0201 71
    0x80f825400f0441c0d804549036808000010000002604000c0c071110360348003c001c205010724803024011030348084449080d02d2144002809800050412303074100107556079a60341c9404112004012801050340c24040341c50543d145555480c3c12241c810126001c2505c0101890809440117140030192030b009400183c0b14070744e40e0b0600d440300420101304410600e10200c40f01c40c91040b0300d015440c24403441854200500509c0d50320400034010010343d201d000208141004240e011124075220043d264941c2e6400d000d0340d802036024408072a0060b518080850850380019410f2601807400c008040018001c070121842050300545e040070240c10b008410b40301c07489910141b980e4001d00007100340425070150302030854014815001c7d00c24000111084e81d0701013582c01001e81c40003050002c00c00525281e0003820000354030440310490242c0d40e80c003103841e5800c20381044811800140c0c3c002c05001000348449114105440c2aa281742901c3d0000380a10301445281820181c40c1d0700c4100d107441c000d41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 856366214 1250 856364964 856364981
    0x340302030a0f060e030a1e090302040614011409030c010809030909042a0608060d0609050609010504021203162022060e0c030601030c1b1505060103090f020402030a 72
    0x90594072450200d191141c5080c0070414121a00c503d0240200070021002007510950300b10307a00c400b0310b400b01841e20681c680c94510303158000c2203110000800107071141e01801c40117014a080e820f540c0036030f52002401048074288a8001a141400010010b0360000b550f00c140800a0a003004c058881038001c41c05c510410b5030040d0000c54101c00d100802542c001280e04c41440481c000b80d04822007950880c01412031b21802e80003e6041b000300301c003440c0800251102c0d5220301e0001600380c1f1103a8403030341030010441c3e081506942d50000c01040d420490325511400d14807a010f1450502e640340030255403a61004090004545e1602c0542541500e4044501580009101e02024002a812030316100710040d2400d1000b0304006001031180c0c800040d80c0e000700c081141c11400c650318900114001c04084800004105042c1100c905a83c1809041c42c0803500070036250198080c03000003c0e080d45c0c0d025196a041514008820020440340304821a100d94110707001f59890700c031400c40e50040e11a01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 856367464 1250 856366214 856366219
    0x30c1201080304060e0108040b0711070806011502011b051206012001060314070303020a0f0602220305120306090609090309060d0902100c05031e1303051608340302 72
    0x500201d0391400000c094001c071a650350310301c542601d103c0011540c2c074206940051214843d10040358000303006444000b03242d186a030484482c0340d55921018035000080c1d0081040c000c03034049504c0c0c42a8280201c6018103001e41c032250160844c803400926620507490410140d20b0487d0105555a1080c000c0090702000c1c400102c42c1c0e0580d069280d4021701c0640700445144c0c021282c4800b6203031001c20b01000303d907055000f61001481548480c4072010341c101d01110415070800400300750a0b506038284042e502818984245542180381252401c00c050304540d400350014010040240c0d180f0380b4031a4000020b0b20094941c0e160500f01c58518098034204582c400000b09284a0824903940107044040c000c0f1500d0100082030308060300c05440c1d500010b1f0a98008000510340d04a0001340c42c0440c90394031104030329128a03001c1900c01c9048581080740c0316000010018101d00c00380d89610090084a0040c200355040300321030040c045154001800112001c02d107031010000c08119080066401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 856368714 1250 856367464 856367497
    0x18100306180f08090f040e0a06050c070c030b010e060618040e10050106030c0e0f090106051b010c08040b07080705030114060403171e071106070623091b06090402030c 73
    0x1149000725160704412030550180a418428405d14039040c042c282e5250510405801c0c086da00d5110240079210041201340c0c001c40c20810900051200c03401e02c40218000e50102038294100091144130b800c0280445200b140300f80036114103280d070307514100711681086600150446043c540c2a0900e01c3c03203003c0c50000c0303152400008146801d0381107242001495950301190030b44100c2040b442d6580c17041040e402090300401403002d14000d4008000c200e24026110230b9050f100000c0714292081141400c2c0081c24070b40500080244980d04280c00c042c060414088915201100400e40d0005108440000411603541c401c15141d000480b009913030045070800d0b10170480618034049501152007481c0e070b250528460f110302c2c40140103541300d060f03102c0200700840280c2c008102d90740e0000344060f254190344221100200c600701d50a26070088502c0f035000c020b890002c14007400c14010701c0c04c00c40100700e03584400031665220030440b610283e08440040e241c1d1200140034020340240715086040046 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 856369964 1250 856368714 856368743
    0xa030e100903020706020f0f0714120601120b07020a02090f060a0b0f04030c151202090f03010f09020f1e04052a04031506120b2d061810030618 63
    0xd02042030310170f6401030b0b0200d9003130a4a980d102680c840481070901d24a40100300c052105000c01c2e0f000c89101c60300109605407101c20b10780380c1030800324282d0040b042048144515070410004e5946aa03002c0d0031400917022040291f00440c0600300010720f4084220912400140e09a0320700c0c40318406807c440070101e403103c80740854030080703071700500050742c0200c403181e800900681c01c107000740d05044482d550002142000324400300a50812180039030301a078403156046c40c3c1d07107091007840302161a6840219860030b590040c0b100070b00c02502441e000f000030249201d00961044c449035032101e82a40c0005403680c41d4031128a41c0c00341580c0005210224401d91880d420200e00a8400c0d00d0280f00390a0240305800301e884100c640c54490b00803c3c0a44020803804100b260031000e80c8940c0301004100000000c816520340181c0303401c41d2890b07640405090200c0d60400810b08507034600040105002401d0076201c403010103043c0d10000b0219900d840101d400c01d003c42c000050865800400f00c9513945 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 856371214 1250 856369964 856369967
    0x20f1909090209090607020318040f0207060207021311120c0408120301060201050a060e04031101061809060b1e060717031306141005191a19050306060a030e100903 72
    0x140703070002603220394040c40204a5020012070490b02078484d80c1c0007946089600952440c0c51100e10454503402940c1e0382011800c08a02d000500a085c85070b50700581d580090301c100080007040d40d0101900b5441c01c401070031403c5164049a20601881043e81c00300c0d510003030006203a20442c0c10070364850255010800c5114a407202079030690700c15030000c1c40b090350303070b5000c120481d0810f12841c0e0841d02000c0c0420f0100c0d000f103107a880040002c00c00801c10b01e8a84041d90f51540f072a0f4810702c2816560111305003409424450042e00c5407046803864000300c402911f81030302415143d0070901c00e000002c0d0003001c1050181b0b0340b05d40e800c201c014040d22031a0034141c1c4807152000c20801d4400f241442c2842c0d81c041058120f452143c204101d003950304904100900032080e2429000000700c4003c010041070224950701d0624003145d00c6501d283da242d6281145403013421a0944610a00c2418401d00c200f9685000550300c0e460010301d00043e994030b0800c9490b1901186403c1300c1c83d000e280440319070626 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 856372464 1250 856371214 856371221
    0x6030606080915281104080d020f07060e221512151e020d02180d0803010b0a1707170106050a0903140f03040602070620030304020f1909 60
    0x484054407414026034880c016a902d5400c0440ca0b0071020b40315200180b06040010390600300c00940125030030103400701c90a5201200c004502030100028082010030156204110f40c001c00c110610103414841054a5116070300c1e0424055034081c403018640f00140c0303458401202c9070400c10740307150100000307600354080b0040c5851302c0c0c81501d14080714404a0b449000030850100141d01c0026242c0316501c0c0080f21006148010390074840b9418082500100d071620700203850220421000180c3c1c500184202c007801040701020a07004808005682001c035001005484c1101c03c41c2080f55503c80c07890504851100101403208201406001807105050f0b1203404a0205642d0002c8030a1698039030b0401d0b41d8034000c1070480e0700084c46001007400010132030807000054880c00021204401460341c2c00e581983c0103a08500e005a01207101007110550007100842807148a01440d85001104c684007500c91100502c040d004007070882200c0c7c41c0d0380ba482c600208116031154043c065030340b5003100700c000c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 856373714 1250 856372464 856372469
    0x120309030613030e06071a0c1317100e1b0a0506161203020f07061508150a1503230709020408011d06071b05030c0a080d0509010605060f071b060306 65
    0x13801d00340307540042d400d0803400ca40900d03401807040485850216034140c0003c0000b40002c4014109200140d200d41c0030392032020107010185000e54690b0f8854407402e281003509914014124203003641d240b40d0340004209090001c10790504602e222012502043d041c00140d808aa0086000075280c1c0880040181c207202e81489106040c01c01081040c0c200c059000d084024154001c04001c2040024960f6010100c0c0300c0c501000700c9800c591b25414107040100c850b1040c000d100059003040602a29403203000b40c620000c1003240740c41c904644480c0e07038411081c1070560306156010309500c40b080d81040940c000388013400c0d0039540ca5071151800e50107429030200c1c036440341000e60480d540459000c01d189111b09010303aa800031030007031078240300d4074807880c4d1405440c107000402000f00169000d1007404584d40c0180801e645d91004880000211341c402416596036924014081c809580c581044684440c00122000d85660043c101402107282c002410303c0d0045413000c0014260b40c058004c0001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 856374964 1250 856373714 856373717
    0x120301150c031407050705090c03070807110a020409031e03060f060e1c0c0909080403030807020303040b16030204050301020706060e010e04210e100305040b0603071412030903061303 80
    0xc0c1a55212000d0761240000700004000c00c0028641c20340b070b02d09400242410b5805002158441a0b545002c20160348041e10b5031b15403a480041040795058008082c07540201c100c1c81e100010082403400f071503e0300c1804100920440e12204204c05241c4544104240c5444401080004503007200c0c02500401d154800d201d00844152000210702d4018121040028030252220103860381d440c1c160103a25603980c81c00c448030640040d020903034540702d118403d80381d407041d80c0941e039841c01c508000c3d1404030001c0c0320030215801003003080005461600240e0308110304024488545902140640103030140d40c2110b41c1543c80484da28003071180315080b4a040302c0c24143c08040c030b6600c80c074880003866000c0f64003401d02e581c2014809012004214000803a50f400d02e4030105000c00e0303170006220828000c820a000070348840903c401d100000344229009041200101007040c58012880c14000c0c0001d40c0c1482194810140d12240380300348100c0d5140d4a0080c00e4234418a49040301e01c00301100c8000950 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 856376214 1250 856374964 856374989
    0xf01050301061d0610140a03020702041407021902122e090503040b0904150b030601121a0f060c01060b0c0712020f09130b1302040f14160c05120301 65
    0x5240d0440300d1191425007000c500c840582d5191300501041c1400c45505008000a02c018200041c003510003600b40d06642c2c1d41c1c0503a07510b60070b00400c07007a20070305100b00c1050041318050140d41074000504400840b0106040424015140005401c0b00d03041d600310402030141c982c8007c06100103425000080d81841014a0f2a2031034148810484054180c010300690082009000440600c005807981c02c030000d00c04102c506004a214425200e2a4404110240c0100a1081940c1c0100140f0610200400d04011011410314851005011030010758040d4141c840c02280c02d441d0201110802d2101c0c400034000141d662241c1c0c00140e021114400050003508408100c00c0c3d030075801d0070b41c0705400420040344003219008104074404064105018110807441c10400500c1880d80d6034866540005c06403441040d40c018003040c2c640c00078480c0c021070701e0a01585c1442c4025050382d900710748100701809500c00d003644103403849070304904050308504c502088003521080311001181070702e810104c00c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 856377464 1250 856376214 856376219
    0x190b0a0908010b010f3b1e060d020f041203051308070501170c09100e01030609090b150d05150402120303040507060f0e1903031404060206070e180f0105030106 70
    0x140c1c00c03a0911048140051490103182c071919110380c80380380c55240204410f00783c5510704581380c043c000100315a400c540c421842c80c0d0710a072034010382002c640103a07c031a1034000905d200000c0d40720304c503810304030741e1040d400302e032800c00038001d6070581e0060501c208080610030308c1424060300a8010304141454880b5030980400c1208010a61004490b01a19010707404101c0d40b0603154420401000c03484204001d0100403102c0d9141e0448a080b00c11a44410b40c080443c02c0c0010b0540b0f12517002800b01c00e04000b4104005000d01c0e00043d8440c2c91a44550a601d00c500005000040e49a4001c0c006106411400c0001000074524900a501c210341c135020102e0843c182036141c0c0002c6801030b00c207401c01801000500c5c0525000c103441c4e500c40c90000c112010000009030050200340b0000141d40d41307140c00b07008258006424000081e15a41d00c94180b0389001d80082d961000280320104001000c450f050207500c814888903c22406082742c14054039110700c620800b50002d2142c41e20035030812070300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 856378714 1250 856377464 856377479
    0x1170c100f1b1b0f15030506040b1807030c030e0334050105060a0e090a0f140106030c1e08072907051507030c0c0b04020a0306051f050603130f02190b0a09 68
    0x4102245c82040c02c10b008004100c009600610000b080d8076006911404900780c41d0307858020124030758500d2038020603d03080104d001011102c034440720105044c83d00440c0000c0050000644070449038102c0e0342e8484a10340c00d00da00c0441d403030b42c108212107220b200c2003c1c10064190007481c032490b0f054461140d00d6a441c000003104510a9521540d1a0404188c81010600d088103c00565000d0303846021419500c0030321508540c0c1c2d5910580317568801100610240c0d100c207506c1103d0500040100000f03d040221903a2211168030070f0310401c0301220b1112400c0c1110141c00e80148007100c51140d265185820903030744544a00d0040203100340480d0018401500a100e110341c203c01655131540c1d0f07540c0f40e66070030000c2c20000e48162391102c0e03030340d000200081c1c1c44d0141a00c00c500c5441e042160707a2240d010307119608010740006104810074020488503000c0d48070201e1501d80c01c44005480c46040e0300101e08140304418402c0003101d02001c001c10990710f004024880360000341d85090406503607001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 856379964 1250 856378714 856378739
    0x2070b131e0617040b04150b19030507050a03210e041407020d0309110f01170a0c20030901050d02090a0f1a0c1e15010e01170c100f1b1b 60
    0x38020320082561300424049051f4141212207a09183c00c0020070304054400101c1c0c1e2944140115100c10001c4418000c1000510201c40204400c6c0e44000c0c006040d541e41c0c1103d0600110174400c0d81d001c2c2c6042c2580c0d40c0c401c40280c0d0031200701a00030003215818482c055003650084072520050300c00c19629110052092050990898000c2c1d20380c0c440c0c4200b1400c001c5107c01011025040041815150300c01003480000c09000d00303d03450000890f1000d042c0040c003011446440c07040b9904103100102010030f0080103c2e0320910f0240380450340e07a0143c0320032500a000b0401300c1504041c40314004a079900240345258150f4510003510030805410164840c83ca105402c2c0d035003003641102c044100c0440502d51082c040c0e5a000c400e5400c40c000c000c04807500d61a0036404010340b0f1640c207004200c4c4108000320aa291907a0340080c0c80011966004a202c04103814140c03001c119050b9507034000f9900c960040c2652249004140000242500301010600360800d030a03454080020000102a0b0701e038203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 856381214 1250 856379964 856379971
    0x60611100c0201060b120403110f030904050402150a0206010905010906120605130803070306051f200f070e011d040b2d0403081608060102070b131e0617 67
    0x10304290446a1a000250401c01d00c600103543d240c09012032000071150190054030501c500700c1e042403410341002000b00c3c0300581c612829401c80407083c1d04a140200071540441e1040c0ca003c191911103101240c0c5481071120103071045400030801119056010404c64100ca280d5007043c0080e90300d0b4043c0e2004c0300c0d654426030b14003c0e0018051b00000320550012503021000201c82d400004d1143c85000b00ca07801124050300103036072181c3c117021901c3c0c41202000040c01d06031345503507183c10104014000101090340e07010046180356440689640401681c140c66911780141c41080341d6441408104903c203001c0c0c0b043e400d107010f4001c81303403501312580c052149411030b1801030321f40c9610070740e40030f000c90182c0e01c04442c010308121140702c54100c540c0c05005911958904006250220b841d02c1c0e0102e480c4080001c020301e104c103001040ea8001519030030750312040c0445940c0c048003014040510b100390310080c0070050078409910555040450401101d6051301d80e0380d06414080b000c50381002086 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 856382464 1250 856381214 856381247
    0x1050f01061e0806060409022209020f120933090102031501050310080a1a061009051e030a0b010611070b030109020c0a0b280501050306040206090a0308030c04090606 73
    0x15007040000a100c2c03c2c016400500c0075122620302600d03142c0c2c1c5020381e440516816181d000d8001d03c12213514003044a80000d18a8010840c14801050003003201c500ca400e414401031115003022440711401030154903070b06540070074801000c900c15410b91a90804086468514040031000142c0c440d0701030088170300c9450640e4200e400e442290005586030782015141d05c02114a052021400741c0040203041044c40c0281c401520b030941e600008602c4c10001454907000307c002c0c0d1a100e0005800c40212401d8034400c4400c103000140321501d08091200c0303ea100c2c0c0d454441c0c030544000b80310b8101c0e1114143d0303c030760ba10181c000307804458441d40c80303401e480341d14a014820801045401d036264060f100110f07444090360420368444c2c039003004050b020f80d0343d0384060400c020381c2144403805807003898440c00509414071480d807608000030703100c850003003001e401010b000641d5100f55850010342c1e000703948c1c09180301c0e4403402c0034000450b0070b0700a4051680d00a1918a001c1000c900414038884181c0341c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 856383714 1250 856382464 856382507
    0x9040317271605040903050d050106021c0c030807030c050702030a081210060912020604031b080f07080a110d0c030303020d0c0e06070204151701020c01181505100b0a0201050f0106 79
    0x80a05100c020580c0002c142c1c07c1040030300401180c03034054000d041c0200060b42c024003580c003150118281c000e40088011042c460948842030010382c000708a140d00a20606000a44902c0d49030241c07054440d0580013036042c0544410035040004200203000c0c400000d6040c070a0395a22620905000c00d00c90007904003050b02e14804000c080320500340b804070341c3d101800103030030160340e5035418010f41e0b0b4810201203401001101881005400c001c4c40846108420081101615280d001030b1201122000604510107041d46a402a180c11450703442c0d41f54815080c1320284d5890600500130b40000a8010046080a40c0d50f40d14522444002510b903400a0801d0700d0718080307608001c01004100280d4088000700e00c00001c2c92543d051714210400f8104001580e078512454001e0b085030f050405030003400310502c3d003160100e0000c1e04000c0504248203000a45601e510f4500000300c90740c0d42c0b080c0507070203000030a0a141035043d00010301800c011303e03200d201a40c0740c603010b40340c880744400b01c0c0400c0c455 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 856384964 1250 856383714 856383719
    0x70305060a05190e030706020d140907180b03031e0301060905040c050d090212010e070f0902040f26010c0e1f020613020f0604091401080105040f02090403172716 71
    0x240784e40038100042003c022640307045080d95848090340c2001c1042d0f65034956502e091041444003542081e070000307000c000340480909054803000f0b580059081062141c1e55407d51001d5a00e08100b105c16110740b000c0c04c12038207a0102050451580240154400208546000221820a0300406444107040d803201c40c100048030100500070000e24400741e038000100182c039a0b12031000e00c541c074854480180900142824840d150009410540c00400c44902c10841000382c081201500011b445098052450000303d680080d20b040c00445203c0d8419407070000e80c0405181c0001c10803101c5a0169080d07180101081403002d140d0b100b0248000142c0c02c01c400061418501c40d00d010140791004254142215502010a02640040d08030781c0b1801d55907100720080303c0d0305040da00d00400c034010082c860ba00d81a41c0b4035030140707550117000380510380310400b02c1d0405000e08100900c0d0b6903404901d288518000822021440722415501e110303000780c1c050540b85006c0810750785010841c100c190b128561 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 856386214 1250 856384964 856385011
    0x20f030708030c360315061516060204060903020f040504024005070801330e10020c150406080402091509090a0203070b0304031215080f070305060a05 66
    0x103004c4015510941940e4144801140400d40d090502e10384c05051070013034403407500034103162409030303507407070144101d100104070180d0b80d44045050340400210945480c0d00309031202e108201d000400041c403507800401e01140b85503103c0401011030303008460070301840750140240001c517801070302e001c0e4200f04d0102904101055a81042001d0b40b0512a8550761001131030110030514a44444410000e45503024062400d6110f0001809030900708487c80324500b6600300842e128000c025080c05050226404014441c014000300c10141c00141004400c2000103100075100c0a001590a2007100f00c07020080300403500c18184c2e0107469498554110356100d503020000e00010042043c44001240e181c0e50030b20b51181c3c0b0605000e8052140200300c0c9018a10415060407200e401c1b81c07003c41760504c100008a0703841031030b100c0c500e000c000c40060160054001041841d0a98025411601c01c007200203014040024080084034040c000795803040c0c640f0b001036800e40f00d0640344461742d00c0d490100143d01b030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 856387464 1250 856386214 856386217
    0x60105012604030212070305040e0604050c07060b0316060f2c01030b030109020307030c0e01080a120f030b060a05070311060103050d052b05041109061011210a020f030708030c 77
    0xc1c0c040c4c011280d0b50221040c2a00e403e91240074110000360740450b040001135000e075442c0c3c1c0c0192048a00b488285003175690744083e4002e088010300401d8442090500b2514148a0702031850f0f11401c07982080b85e2650740140610303041c0019000000c003041120980052008030001112414103070415220000000450243c41141000d40d0702d950381d8000680181d82c20060752000b10302c103042072003666103410481c41e02000140d0148540350031aa0b101d800040d881c06410f0141001340c180a041030b411100c0c2100104045090310f50080d4000501100558000010b42902032080c3e03107001000b144104001d469070401e2200900f507501c0150001d800d00e00990113009a2554841c080c410703611000485107401d10700c0d0342c2d41640c02d0f43e2101440180140300303140c0000c040082d94441c0e070900700781c404502c6c0842c0b844050420070808544008000c007040c011051110260350b06069460a01c0c101403800740d00c003011103c05031007207680f10706000801109a5980b5032300559014115030301c00000d500e45 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 856388714 1250 856387464 856387471
    0x2006010b0d0e160302100516030804111315090b0f061b070f061d011211040b0c03030703052802160204021b10060f140303071e02030601050126 63
    0x516155010007a40400800c08040d0070341400e15071032810391450050103846d603801c48440042200801031011145a80040c04404640c0f41c0750a407011368139410440400001049030b5540455055000c849214150300814030050250306d03500641907440e11550100c50b5205001c40e00094071145404281c900040903000116911a0481000005210441c05d04210350004220421640130034080e81d94820701d000002060114a517460450010000e480510400d10394031a8a450b1540e80e880140f00800b507a00610002c15203a440f0ba444400341c5450303400450311000000e282c880003c0400e922000d0b2105c0703001d00580d4248217442d21603024000307903102030000201c0c030980031902001a240c501c011f10700c98090f56200d00d0f0581c4080310b002e0400a0203550f5260b402e04007842408000140c0b2a501c080700e14030070429000c400c510010a00f180106031010f000d18917031101c14044031012038010107000b0f10840c01d0303c84a03030b2200f00646980f00d107181700c50001c4002c201000704ca00d4030729640540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 856389964 1250 856388714 856388737
    0x3020a0b0a06051c03020105071b150e0304030f1a010506070b0604091e0515060a0b0319050414060a090c1205070e0106020c0906100c0b101203080105012006010b 71
    0x842c10780f544013080054000720141211035042904020034994284103c542181d0380e0302d0070810900b08600d04901d43c46038070101401500809000e442040c5140c0d004417214440b503025aa240c030b540b420904020031101d00151404d03a0a2401c071007807084107060a42c10780764014042030520810fa16035120044004158540080d501ea80e01c901040120349001c072000f400104411007000249401410148039030202482c1000080a200d40c5a907145510002d8843c1d014240b6120768030181007545805040d00c030b41a40520300030a103c1842a6280341802644c0703140102c03402c5845840d9498101c520021020303109800b00e100521a80c05528900c0c140140102e080350a1143c43d0040c2c0424034038280e10000150340320b4903000455050010b085179001c48215452680c60009480150000003000401000c0912190001b00045001980500a8035200141a4503101c0380e00d00074000d207100b802080d0104040750310004030f541509800405800c001c0010304644c1e403900703102910310780081030707c800c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 856391214 1250 856389964 856389971
    0xc0918074406130c21050d0810091a190e011a0f0d140703052e060e1906030f0b1c02040c02011d0601031202030304120e060c060709090e010903020a0b0a 67
    0x680610410b03c40c0c0d188000900d0089a171200d00d240c00d51074003404000130000e00001004001040b6020140402211000b1a0100701000304285000580941d58419988581e545003400f800c2d000e90107050042c1c682d094981c42c240d036207449802d1340c01c2482480310000c10301c4c1004186040365805010309141e1800b041c000c202d80c0c000400d4404803000c1280c41d440000d41c1e030402c01601e482c81512451104c1c00141c100b444061004485100c06c10160044074240015102c1560040d2100144504011402ca42028159440754070007409095803102d1902400e051002900003840d05664490036040304007219005900181e0a020203004001025002d40d5a900c0340d54104214815105103031b00d44003005407940358103500e4604807029404403010308542c030600800002448140d000c20400c0403d060100c40d41841c4c0f400a4001d01c00c90711707448224081c0d04113201001e07402c010310006031454030006109680459800d9400c07191203030750140042e40070000c0d65000c00d205d5030100340c100c840103d012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 856392464 1250 856391214 856391219
    0x518070e0903030a09142e0b090610110a050a030228020f010e1512150627040f0203180c100e040e06070c03080601020c0918074406130c 60
    0x2807e00080d070005940d0381d031030002c9030704020032030302011880c00701c021400708441d0300300c0d00c0401c0a00c18001c03c020702500c00c01441c5030005024100c100107405c800b07000c880d43c2c1030703d0b0b150003501c0340031800c0105d01610a420300e552002d0009081c902c0251400d0b403810900030070507002c010b1440314600b41e142c140700c02c0320000c0c241902d03400c5c01002c0d1014081c410942c0d403510048461200d40d401001215502425122041c0300d81d100800c441c80c48042c0072400b0092043c02c110008040120001c1d2503105140c40c100507054040350f0043c5101e505004001a000c1080315511501c4281c1140c80d142d02018101000714801d0090520307015044000d1310009248400611039440d00905440041c007184009892208040d171020740c05511036800c0c07000d8240c01d41c4041c003180b8104400360410b00007503030381d8440d0740f1502c3e4104010002045906da03d800d105900001e6200b1105202460340014140c0e034a04404181c4144200c13403109849400070f01da55981ca403001c4c030000c1410704c0d0440b040c3c460390100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 856393714 1250 856392464 856392503
    0x4020703111606170426040e1015110303160c08070302060610030902030307060c020f070e010f09110d0209030304030c030507051215010519090518070e0903030a09 72
    0x207280c04001d85480440002d424010054010264141440440d0304000108000100140c1c189081c0c1906249060100d002d41c001840c02c6008680002e858200041d04000c030844100312100104c86030700303c04102100c04581c04440c2002e4070b50110795554403c002285107120045007034100490180750419a69210740d0ba60309159114010070307001a880101031000b0307450000c1c0e80c0d952081982c2000c21000b24940d010170307141d0048481c0502920b82d203000c40058180203000c40381c00d801a600560340510f0310b440725801507000a000c0d90800440b4044042824451845409940c2d01c40300c1803641010106294400a5840050502c0e054041808000006012401d0703d078047c51044000c3c02d1805d0030002401820315594540c042a5801406500910440055070341d042d140190b59501030480b0303081c20001c810050368050041c040c039250802c1566030080003030244a4141d80c042e1742d10751b030ba940e0390306c6040360041c0e071015032a400800105801c4c029945c4008402071050800c011400e140c280ea = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 856394964 1250 856393714 856393723
    0x60d080c01020a0e01050c25031a09060105030a020604150c1a0f060109120f0816050703050c0d170a140c01021309110a110304090c020d080603070b0304020402070311 73
    0xc884100380c2d00494032041d05504102101e020000c03e203045410006500c10480e6540c0044083c0f0441900340c0b081000a41851510071000d5038101f0b00a40b03482101c41c0f8100030310003013200c8120300760184000105891502095401c09190010314040c1014200f82c2d80d96429120039400c44140508007000000044850700072002104010a00180514051000079051180100114100109410140160300046030070040c510b4004d5507012111401e0310785115540f181218038070200e920380c400c1c0700421030b0000c2e0280a484c42202501c0c0507401d06402d0103134045062500400c1e03000443d04100071038000b41d025082000e0245400490b10300c840400c00e02603408400c04d80150b940001d1410300c14502d514403840100b10943d41049815540c40c0c96001501824174580c0400c10f010f040300040303810030410703a17014100601e81040b01c84440071001c4d40d00c0d1000120140800c1400f4005081440c000c24400b003220300ca450010b14603a51582000000d41c8900001c4091000d50380b000c034907900c070410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 856396214 1250 856394964 856394977
    0x11e0512280b010602030733020f0403020301060e0609011a12100501020d39050f0a0317010605031603020c15070914030706110307060f02040e060402030f0609060d08 73
    0x494a0303982552070b040a622101058104c0010b540c4204410000a0b690054880711401b840180d0704080700100c04c0380340c0d07101c14604001c4080b800031688080d4007884900800c100e80c4210020090190341d01707180d07030302000d08407822503008841308010007089003850700c0a00303104582501c10707140000b84518450f001609a401282e0303000501e038240425601000503002003081418040d12000e52000041c45030040450603180624107000000e220810305003c10383c130640d0000c00e8642c61200405c11540d5201406c205500207204084100d001c0e0050480c1141655130b80c0d541c503465039950400340343d12691081c8c1c0c60400c0507420400d040000605001d0304820194520b03090003a030401c10760003006200540c10061008400c01c2e4402500d5400240f440c0071613a0724245680a0389103249007038298081c0020241049052010300702a5403890740c000c0081e60117141e1040d08644a00003404201e000444120f00b0350100103002c1803a43c6816041c8030780c4448020011611845070b030396007820680000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 856397464 1250 856396214 856396273
    0x32003250303090b16030f2001020c06070f140906041211010f02010c0206040b1b12061309030c0f060e25120302060f15100512011e0512 60
    0x1030100344201030780110703190000d00410744401d003080c0050700d5545030801114030003424008060305140c009030003442d2090030700341c40d10b102500103207a004003207010f98070800512200b40075100004856500a2001980d0f00000303942d4031240c0100912440342c590310280c0c409038411802d100000d15500c800c1c0105084d288140d5428a0000600e030002d0302440108200000756410921070030320655001800c03e0740706070010203985090312030b0f1140c100004070f08807580310b1003400083c42c04000c4500c044414003c410556401081180401c1840c3c100c0d07803078070342c004c1c0003540c01c58000010404400c0c500c1040da01881000984404248600d49004031012502d040c030228416020700201c51076400350024030318010044000000741e0740094a607200101461550100c900202d000701c2a9850034609041e0050800910340064000c003900a0f0407000e204540104100008107030800503150302d40d0070686502c0c0303a00500742081c00300243d0502641a6080382d100742510340004100546241181c8501e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 856398714 1250 856397464 856397533
    0x10061403040b13170d0b090105030c0904020d0b071827090302070e010906050a0b0307020712031e120c0906020c0103021b1516020a03140d0e0619060807032003 70
    0x642c1d080100391006c80200314840e04074000104902d4a01080070142c5480450308000395035500d1001554220303c0c0c4201409641402c0c04100c860740d000010350f4021040301c1c00b4103281c00d03910301007103034010306200c5e44a07800d050b48401c40040191642105031442d101f8010359480035160301c40151241001d0b8803c040407500c1e000c08110307600300002440044c2c0001600c840c51880d010300040c4d5141c5091141000c601984100d01e0103040c4284c4007804054850340c0044082000160300500d60004211040c0c005440e2241c0745a07028003d50341d51080350919000381030300b200c201005400a40028544030041c0c450b0403d510f0300341206111b81e000010034540c03001510305010302102c003922591a1300c041590304c03a080c2039022a40007908005900c820a8601756113882c8502c11501400c048120005148070791020300050000e914100c0d48685060390303003040001d40d00c400c1580e445509100146c02c1c444140040e11501111800f10018030034040c08a400724440925410740c00c039148003c007808440c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 856399964 1250 856398714 856398727
    0x50d27150c03090804060507030c0510020304110f030616030213090e070b030705120c0c060702060609130f08250f03080708190902150c010510061403040b1317 70
    0x24030301c80c02001d0700603440d0801c80740c030b640c1c0d0701c1c00020704c1103000e0f0b9000e01202154081c2014070401c1c1d6142815444000d454402041e109100013940041e103044130718200c038001e400b02d2410441407000420000074018150703600c58130300d000200382c4480801401c0580070000c2546401c04101284001c0054020020b07042c200e00b00494103042d8160001014140104148141141d11009460306103040340345907109070311015247c0c1c4c401e11030041c0c804554011801001941900417810511580081d01d102c01c3e5540d07403291442000754050b034001d09d06802c403804440860350b0600a40301141c0322411598400c10b070b460301c114078124000300c201c2d0f100c00031004100805912441003500b11000b810060041e00b8500552041c0c1c482694a5900d420380d22142c0d90107540e1000541c003006094a01003e540c0c02c00768860f1400380034100e0321040311604440000070038034803452030b81c040f510400d001d03903065454590711107401c0d100c09801645451420040784000c10149501e64080c4200d0400f4070f43d0710368 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 856401214 1250 856399964 856400003
    0x90f03070f081216062c0c0a15050d0b06041d190e2e060e01080f0c0a050d0c030b072c0907081803040b070b0a060807050d020303040e0f04020a15050d27 67
    0x10707450300b0409c1c0d4800c0340c2c520000400c2d00042603c00704401c400000c43c125034154040380c43c50265520001402080340010340c0c451400c2464a0b026148480042c0d241c1d1540c0f4204505a581d0710032440c90340d03441240400441d1482c107018607141c5c40c0d403000328a00c807900c1603559001c1d03d1003508005010342030702d001040f08141c20840407141110240c050022a174820000403004059445042e0291000b49800c1d810007800b130610f10081d5610142804c030b5401c04c41c10040030303407041d20980440f2100d118405c0c1100e540340b403440c20100308000d241200582d10964215848400500010704410a908444002110600140029110302031019850b2100b0b410300c01d0882101900340c0150300e19018003885001c0010612000b40d0b5000c0e1804204c050103840230910f10300c903685c04540900907000c20b01c580c80e91201c0290340124000c036150b0003001c1e1105018190340b4600c2c0142c40110fa41004490002d00749600804422064100d194100c030400344448031010152140c120b0f1803141e2180c41407802c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 856402464 1250 856401214 856401229
    0x60608090a0f030f270512071a16060c020c210a0303020c030903030705070305010b032404020d05100504260f090f03070f081216062c0c 60
    0x405a20040c6400007068550100010203400b020f0b00f0044048203104140303000d00442a0119502002e4491441941580b038442c0c3c003030390040c1885000c601d552400c0d226000902e0394160b40040300d146010282071f0314881c10a0f800084194180d500018580c00800d4240c41881c03c0d20506802a1404a402c1d200308890700b040c0900c940109101d0038100c10b001c010003d0100710076545400d00607550b2241f0210310f442d6000c1c002c141d0341e042c0f0001401c44100013003c254030040780d110790024006071000408154460702588410807402c9001c004804071400e007444080e4111340003811a158801d55a29908e00703054100c400d0440807611031040c84104040d110a4004241c0d501c2c241c244040b1351220031165074480c5a904e4415a40301040c40300d220348c0c4489240300d01100041c1181e402a50baa003040c141140c4500c42c0d003005000d00610902504c60110803a400351219242400c00c80307000e991903400900214860994200080f2504038080381e005640511214200e001407000390751080800020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 856403714 1250 856402464 856402471
    0x303010306110f030a0506060903070311030f0d1b03030b1c0203060f073203040516060206061305041a15040609090201022d101e0e03041412010e01060608 68
    0x40c407000b08002e010f1981d0010036250864100b120214a640300c420000b032060080304401940340c00740d01d0f4000200f041030000244510710940030380c3c1d14074946051041e00c0b42007103003656010a040400d05450300c1088041c2040c10380c440c0c1000141a25540c0200e0b858a44984024001c2042450008150701c0c080184691205150351070748003510b03061100900305002d05c00800f6600c1d11500c50115400d0380e40c0030800c00f1000c0300581640b20302d81030400d640d80318010103050406c0c152010010840d1407011992510818020b041011440e8540380c0a0004000040064403241524401080c001504052070b0b80107440e013075104091003048808000841f0005c0e800710103c03d00e48201100140d801050848034a00c03040e807800c039800d51025070740f41840c0b065103a602035801400620125500c070365001450340030003107400c07200c84040502a0801c0f550200d903a680c1d1a0b006101c1004031102c1261400000180038040f0181454000d602c42e00755500c0101040b5244d45481c2c0074811240d211401030751 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 856404964 1250 856403714 856403741
    0x60509190311150904020f090117071e1e03060501091d0c0a0507060c03020a0305061207091a0d0b0603120f0f0d14040b010618080718110301080303010306 68
    0x945491955020140c030501e0b008a40602d0204584151402504060300d5012001070000c0d0b64400e07131864242074552004940c907020071410a9009020940d40010510500c0251201100d054140b283c9040c8083c51980710404c00040302c0100240d01444403104c0601e00303150b01c02080003410100050940c1381d09402c11041440c0090201c1c21600c51081e056070000d040003103695072501c403001c00300c0712881100d8000e0101420301d40d0300c04c42c059259009004040c01c940c1c0c01c10180d01d581c1e0420002481e840b844600e50343c0703c14070034403020f40e05500110081c180380006050001520303000c03840041c00c0c01c030196840d4a0400821615080074043c8a80d55a042800d407841d20858034000c01c0c080c0286111803040c03040c042040034480301c1c543e0000c0c6054030400c603542c8036441e140c03400c8cd0385100d00340240340008100c5210b000303d0701d02c5031000d8410388091401800c000313410002c00d5620340c242c204c82160a551a60114410f40e409800114060300710000659030725070450410383c098500801c524030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 856406214 1250 856404964 856405009
    0x902271914040f06020712210501120632090f03030c0d0e032a07170307030309020f0d150e0316020409030918060e22080c0102040807060509 62
    0x210302520070402a030b0b00c1540b080d00c0014055160038100000c0c0030303080d001004105599a880c0d401900403050340c58240240200101424072010301c070064580a10880b074882d00103841e1500028026003040421943c00c40c03801602c0f07095200700a01c028601c0d10820408183e200030b000c100402030003080308200d6200025461418180c848a019101d280091801d40f0341c4e0b80c20030032210005004a50200000a40411403c40030742d6603e040710050526101080c031a804000a50301144c031048200c685490f809942010842d44050b4040c08440c40300700e9005078283c0304a0360f9940c91040059a42c1d0181049480d80485011428104c0303c0504441c60b90b03920600802a5008141140c0c001044d030580300401c204080d40350030b40d50003680d074100b07400101c800030700074518980c20352000c404c9034105102d46034103031155074900b200c0b40b41c0310403071520300e043d81d840c8000490100801040c9030000c06000506c0e1541d0380d0881c0b410008e850f04a40009500002c9010b528903007000c0d03c2800282016459 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 856407464 1250 856406214 856406231
    0x1090b10050a05220e102106091502040501020d0203040b0a0e03010f2405090103020303030112030c0803041b0509090d0f0507020a0e100807081009022719 68
    0x2520101549000c0d03410800c00244400205103c2c1060320120800405101207900340b0840c030003c1480e0740e006003408105000b000419800c50141c1100403507240380103c0c252400380c1d1480d5002280d0b450070540710142c41c2d404142c0000c0030100c5600445006507001030301c03281404002801d041d02050542d0441d88240b01c14442e03503e1007403c551000304c407414410081070303c440109000d001d1459420324518503100f1030f040d1842402c0f211a8103010400c03d0106282d4480d010826030f00001c1c000030390164000d10041c0144004c40c45802103003402800c1034200044140d94a4450382c1c4100d808490b00c080410f914410071020031181006040c0071200e001e05458070a4240b40c1d1103482c1c2d103010307040000924941d20454081c0c0101c410ba030360040c0c184c04046403205062500034030b054032481c0b101000d404000403100740108401d4180da110030003811501d00704840050180c000c4c05016640300d840706020740031010f4690204503058805c03242040f0710b45402060300c080c5030000c00e0500806800c0407001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 856408714 1250 856407464 856407469
    0x207030512090a0e0a0501060305090f100e1e100501090507230c03040e34051c06060f02120a0f050319051311030109150b0d121701090b 60
    0x4800040103040d07607448005040004100044a074007400c43c0072450300501c1012121600881c3c141c2d840c0361400e0100d41c4400351207556403010310b94951070b40d420400440c840e80d2403541069030380c045400e080319200d1081a50b00d8242560840b08120b0544c0302d0f07061044c04141500405005014007213080019140011003d803c10420401d00000c03c00c0300d80300f1046080300310307060b24100021002140d40351031300d03403039034400d281c41c01d0310207400702486020740c5038461103230107215401c6003403e03d0070b04800c48a40e070090341d0710340080c20340c05543c2d032500d02d030340d03008a550748036030001400c96664403400141000ca000e810641e9034101c4544404080103250b8810f50001c03040d403540ca0403441c0240d0f40b86d80b603103540ca0500c4c100103004100f481c1008240807404141960300c3d18258040c0d0300801361103508e0010913003201d00181b00240002c50740c0d1000d0400c1919584000700e01c55014044140c40d810b1a0746548004440c03101ca080403c40c100701503517182d03106014090141104260030000403413610300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 856409964 1250 856408714 856408723
    0x20c2406130203060d05100903080906040201020307080c03040b0a0c1e08030105150d09050610081506040504051912140405130b010203121905160c080a0e06070605061002070305 78
    0x902900c9600000032039013949a044110a095411906a81c0c0100300781e4171a0015050b1910141e00046c0300b600458408040401d0701401107134140c00451802c82940d0f00c0030410f800800c441400c070f0006001c00a6201c52a400070109600c00790380c1c17029040240d11b0142c40003000c0d03503124240034499a16050000715040103c9065680440d01844460b044406a08092160845a010b0340342000c070306504200c80099003034000c0c00b0500e58030801584500e0000d90324a40421144410500707100411043c0c1810340c410390704980204180c0751400c1c1c00303c20481203500030f5103080b03801c0402c400d03e1001d20355010901c007041038400c500440c905484c001c001240c01e00d2031a40810300c90740c0c6041da20100ea0007042142c40d14503066030841143e280c02c14521006500c0007510040641c1000e000800d0b600c0c81c121081d40500c0340761180c07410b0075a50740300c4070156003010a80200744086080300001a9540d1006040c0c00352107880c1c007088514005041c0581180c3c41190f060079135104540a03c002000480c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 856411214 1250 856409964 856409989
    0xb370c1416090b0d150209090115020606010c08071b0e06060a020c04110405090103030203030105100813030c0c091e0b010309030c2901080c01090509070e060705030409020c2406 78
    0x42105101000010304a40030601d00800f005d42d050001c800e401103d070003410b0048000c940300051a130340c81e5030140004655a0301700e0010f0b0072100004110b98019034403104968000c0b01440c0c1841d40a560b81c4002c02c018446914646072411020003c000003141c0d8103900400554802d42441c044000203907581e010070805e544038985400c820b00c1000110f600395402003500525200701540d40f0700340a512030707000380106801114a100700e2950b440c060a0030758018130480d05155441d40098608440b00200c4440440b20300c840341000107017810050103901107041840d4400e8040c008a19103020440d0310b8a0780300743c14503042c0440c00000c00e81203001902529000007078422041c1801608c035450754152004943c00d48840c00000c28074410001c3c40c40d1030980f0a8840d40003180c0c0381e030b0030001064012500d050019540300102403041c1060781c041e01041d4814404c4034102620380c01041c0507070b041002c140c3c0d141c1d03118600e400c03001601c042800205d40f458541c0c80d186420300501241c4180f0b520b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 856412464 1250 856411214 856411229
    0x200c150603120412030207050f0604090e160f0e090d021203250909140c030a0b0d050111070c230409050c090406021b03040b370c1416 59
    0x180010025103082c03141c1540151100c038019640c40d103588195402c010000400c1e07005204103e0046900e0416421701103035604014a1141043d00c3c1c106c90001034056128920110700030803121900d01d603641510507000d400010566030382c150524201042c07500c00241080c50642c00038401001d9290042505c161018a01a4076071740e84e500c1c0c10f021840a201510601e039500032110070a0b0b08a54040070800540308070040c03d100c5050860305009000d5404e4a0000220700204003040e1f651030720381d100b0b590505016101c42c59882040c1c4840c1d003140c44220507030704002000900101008000031079900035186004049101040902c40d6502c0081c0c1510380c5d43c011559011240180f003420404040d9400004242c000546040d18020001e504074008010340344007044800b800807a4084190307000d8a4010b9901350605600754852a8001c61103820503200301c2101c0710703840369010a500130f04c0c26000c1685a080c00340c0b4003464048500b060924840311123801c0700312149003481e24101410202d4404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 856413714 1250 856412464 856412503
    0xf080d05071e17040b120108030901080a0203100302030304150f080f06010507030c051906110c0604290906040308070801050609090c090a0611010b010806090a020c01020913200c 78
    0x40d181030500c0c10361074041c0700349800d40820009017a45500c13001300800c8081360301c07101c0c0990360f071003000d07507203001300c840031408140c000b0000303014902c040e8065903100741141c040040b0250790303402003801c640c0507030407683c1d82c601b42075078039180f40c0d80201904800546500c2d02120524150150400044000e000e050402c90700007a41d00903d881408031507602a08401500c08000941d0420603190202c00d6040ba03000b07090420b1030f4458110441a84d540d404444041c2941d59280d65400c032004443c40708000003591403c68000e0380708164141c0314170601c510340c001c08407402c05042c050312442000b010802003085a0005000c01d0320780c24181c1d440b101c0c00707940c1c0442c3c5440361501d80e0060300481c131401c2c2d00070314000d1340026001d9104034181c64041c0d500b4000c010403201d007401162004004c50b80107400800380300200754007014035402040303074081d070200041c14240244009249608450380584440351200040c0781181203080c80d40c05c90a4070314054500d004003034441d40749c45880341d00c288862600c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 856414964 1250 856413714 856413773
    0x90a030305040f080a0305060f040e0706030e0703080a0c1406130f03030e010e0c130c08070c080702090c250b070c03110f0109120f020c060a0314010f080d0507 70
    0xb0f0407032403415859200d91203e45401098000400420080b0b0700b042c864141d180c50307a0100e09062207004c4801728868040c200d05800d0410a40c050035a114107105144250480040481c1a0401422040c2455a80c0d01c02403000c81c00c24108010407000d8400054000c80309100c4c0000740584998130143d80000c03620444195030074150003c151040c485040355007840b0710081d00e8a400306482625000c11200c0031040b602e5469640101c5100c400c000c40410340c6c40010421b81c50260081151a51140c16602c1c82c0030356542c04140b04100981e401401c0c0400402c10800715050100462441a400d0718241c0640710343d6222826101c00280c04e05090080c1c51804009252080c5030011500c2c05450842e015001c40100f902c2c02001e02c041d09071400f02d072906100d40101c0c401c020088100941d82e005181140c415003c1002c16888960400c0a065956082c6a261aa00c03444e2900a040e41c8030303410f42841c5031200042c140100e9204000400c501048440001150399010385194002da04212030904d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 856416214 1250 856414964 856414973
    0x80631021906020609011d06010e06130c0503071d030a170c0f0a050601080714010f03143d090b0102120c01091e150506190f0914090a03030504 63
    0x2255410260011002007800b0070701507000180c40b405410a42e008208000000c4603025009500c58079242c0d0580042e00100100d140307900b0aaa002500100565660011a1228811142c1552503000466008020019025000303142820180c000940e8170802c450100002900ea200c07124000b04401e00030b5410020082401094178485110f41003181c520031400a0b8159480349405400c42d590f200341d03000490001c070049100b0741113032305042c106040c0140c0c03140151090079143e1082c0b001c0582c1c07604844404030b030a029103400360a04102040800014040b107403d030030204481c88801e4110150804100740b00804008101d0340c0702035001601c5012000102c1c00d114205a03484034003100402d10885860040d40190401442840c1191f040b0188092640f10828542c8024044485148400c0062609508503940c0180010514103503075041101c0380900d11102d801211044050750014824ac6c036540c444d1040e0380383c2d420045092403516000190361048207000c0101055140e42c080340401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 856417464 1250 856416214 856416229
    0x62d051e0903030a0206190605010203042c152b020d2a1805010608060d0204110c0304090b040209030c010f03090f120e01031512050309040e0708063102 67
    0x7100d00030306032941e8614024009540700000e5500c420b0188002401001c01c030024842d560480e10306070095402c0c0340c83e103403144a40f0403440c0c004220400c1130744c070055424220070a85a114844a038410090f0007030300d2090010325600141d02980700c0c840201090a981020700500c20113580c125000c0030041482c2c5071030203407810b84e42846c14503503154a07840b8004415071300d01502911450402881d40d081c075542c40c8020b8602c01c2c0304d4800841c1030399003c41c1035403c0404c000e001e410f001500125000240f03444039405a4405010408a9000800c1c180102d010318000e081c80e0000403107055041c11403080000713031103800210381e00f410b00000054002015019822110b21550412102c0e072105025040c0380c8a03443e1030130f04190004060040c940001c1d8024803880f2007401c1c080c0743e82d490b01d90030400e00405101440c81d0030303a81c46c4010300c6140d403075584078000c3d00e140c0d1a003000a01f10b101c0c604460280f4107100134000d00c000003ca580c10300251800748420724a680307628000e001c1d0440c03003400030403401c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 856418714 1250 856417464 856417477
    0x506010c1707290103050d02120409020c03090a1401030b03011b2a0309050901082d0c03030f04141005070605060d08071202060c0f0403020d0201020f0304062d051e 72
    0x110482d650fa0020311461400b40d09040300e0203003096500d4840f1944080343c03105031078005610440b41c28002407007010300c29809081c1008a507811246010b010b280011019805644000c03d9800c1100c070810791560f0500030a00854000c2d0001d2003400355810365503121004844200701040038011041c1d203050280221074264080c005180310182038181001840e51810b400f80c00d00540954000088840c2c00007050304018a0381814050355402000e5182203003000400315040610620850001d01d0354240700420300500303814016035640e890b203031411542e81018690703144140702c10f030303000180380fa00903044038a1103600c0313100043c065540c4000600c101d101d94001414040e00414500c0030080310401c1015405001d130200d501c1640d0390b05110300c56220310359030084da40e81e042c8410001402c042107440c8800384140140c45c1002209a000b9155401c40d50120700011a9804544490381e014140b1000c1c00041003402601d02800c107401410610440e440d0310105100401c0285940016405490f00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 856419964 1250 856418714 856418753
    0xa02070c030f030311090d030e15040909020406080f060a02030618040b07030e0105130303110412290f07110f06070e0306010b12130618030906030506010c1707 70
    0x30140c81e0b040c11884418a0607044010030b242400b1810482c4e0350805403507140000038408040103003250760403185041000300c9260460703030319440305000c0803401c0c000d0806440380e0b520000f045000c9004020699086a001c3d0056422891000d43c3c0f80c500881c0ca10f03800707032440c036001d0b07660340341c24010500c1e0060200d1444210b80b0028207200c20840c18818440c05040507580a101201c540c0794080d003241d506440794a00910310300d100a001174000d0f08004115032001440c1d078101a511a00b200450781c034210b0460781180c400751148000b1030300811800345034400078808510f80c6400380183c818028040c110b0824458101d40c41e0480400070460350041c038900c034099840310b0402c520007601c415144402184030740a45c80000c51081040815150340e80e00b8441c180c9416141c80b0300c0c1601181340c00a06440d1a6162110251031035000c40a1607402031290f5a106030052410800408485015094030f0400801e18260004a8030702070242c0012030200c020165116a607140c1981c010781407000198 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 856421214 1250 856419964 856419983
    0x40b121902160302010b01081510050c0106080309030f030301140405090c1203041427060307080a0f1217070e011106100618350f0106050a090209180a0207 68
    0x5040802e8000c0001d4030922940003842030028960043d1901071080350042203250070456109003603e020280d602c0803025a040542c6480700c1c880c081400d50f9207503007248055034070004820031241010880061904101806181154103140c0100e403290190320466104584981c0841d4046a00380a040c0500500408042201c0010078040b1748940251040f803000c0400741d40c00461a0038120400c800c00c5542410340121001c1c6c4003160288000c001d0640c80d014400c07568003207400c1008211400e8040d01480846024400030714124400204444003102003200c0880c4a503000c55000104581190082c1080844242214012140044c45068071405c0c0d1084105002442042d5102c02003a607410b41d483c102070003e88400b90b82098140d1060740d050714100c08042d00d803505002045e104101902c180da40200180314280741c602081d00d0750490301c9966403682040240b0340740010382c0c000e2104490541c1007000400c0021602c0c3c0f03882038040d00c0441c40340300244000c015035040301c40180d0701c00b1040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 856422464 1250 856421214 856421227
    0x90b18070f2d05101713050604120c0f030309060f230901020f0d060e0105010e011e02070306050106030e060a0608031c09060507090e060904110d020406030503220b040b121902 77
    0x4100c000010082c003100030303050300422481b003c400c0c444240f641d0000700402d40c64580e82c0d82c0c1413000000070385402c10042c0725010b0b0000a0796102c001540d0318081c4da00810010000d00b05101110303114403690901a2518841c40101900300d0000d85d0b00400c0600700312480e503644034580d4060321801c1102d04c41194002408140310006030700c40410303204040a0013901e42c0c1c840c401551041da111007150f01084090392003020f0540c4d500f0043d03503a115030344143d40c1856603d64610040e24402c3e0403460110303440350240d01301c0c00810070405901881107041802414038181c89640c80744942d044220340c100942e03501003480c40c5250041030360540c2c480c40800c41c1d860301403002004e0000324081c00a5065540b0007150161800b030b208180503580020282c66403004400800843c0d5881703820880e0099164940000807803010b2003e0040c49141f1a04409000c1007264103070f0740b01c0500d0300891031010052200348900c545030303c2651741002c40c0c2d5070600d806880d40713010900e1040c03090000001450002462 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 856423714 1250 856422464 856422467
    0x13b070b030a02040602010b15090613031502090414070f050c1f090c12020a0605030603010e0706030b010f111507140403030909110328090b18070f2d0510 68
    0x84c401c0382c080354000c201c9030a0000420450f08a500a0003c0e00300e0103008100d51442d0450003400031032504000003200651300d0703851138030690b070f00180444400d6000c00c2d001100d0900c1e00641a0103011280e0f200150715042c03101030403409860000004001c00402d151420080400c95120349082c250201a00015060304000c042c0c00708860484490303120180005400e5040400700080729801009441000c2c1009400c85603500300a056951540d200c83e00305090320700c03d01c0305d14060941540c0110346a5410b100140040c00f4848841040040301c146400f12102e01003034a4030501c80321a003143e8035031600c030800c8545c1c0c4110301102d407a601e000170b400820550080744040c02c80b0b4003218103210050b652440300c021030104035102003001000340004c00035202c550510182500c0c608200080ca103400d9103c0b042941002c81c2d90b025200d4000380010400c400401070200204005628249490300389041010100120003c844000c0c00307a241640e0000c94003107401740a03100c00b8200325450a5403410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 856424964 1250 856423714 856423717
    0xc240a0c0503130807030c08070b06010e011701051c0b0a020a121b0c080d0603030507021201020327070918060c0806030a0206071a0c0309013b070b030a02 68
    0x104201014038100d40c400e511406034050300c2c8a5501104401180f00701c1d82c581380c1139503108000c11820005000500000190700401a0180c14043d44800390039182460002d4207100012a03041d042c04011a02560344001286800c0d041d0b480c2034600b40005404440505410b520860004103080304000400c14035095070350250844a5a41d03a403151003030420b8055600700c800414441c265040c0406650540300c0c01402c00c14600c5101d01180380c03904003140080c2007261181d410403400038000007446030a41c41c010000d660081c01c140000c47c55420712000341007a107001d03034150740714420444d112120340a005110785d00041c4941c040901503155544046420011880f404803502d80c41c1096003e0b00600c154442441090301400404880d030aa800700b080c1504030140407148650000b0407040405615000300d0301405881203031030340300e0034100319490035240c02504402088a0180780c0b50030380001c01d02e901d800c100d84d4603464a90341960001841c00c203800c5030401c07051180008103000b1507000ca40d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 856426214 1250 856424964 856424971
    0x5041406010e010609032a080304050f120703022b063c0e1c02012903070312110a080a170f0411010c240b040c020d050c24 54
    0x5040d112a81c1e2038006203400480c0a000e41c00c0040c40008041c0005030380c045441032001107820106c000c0c440060702c0780010114a03001200b90360404a0100224100145003e464031000c450001a803150b000c2099924640340c1300c003070304c1101810303800c44c03042060140854038004143d407071503101041c90606502800c0c00e100c0f000354500b111440d00d0b00c140920101e8155251414184025410b21607802d0800b8200900c400c981501038224101400781e6981e5041c41003903032a0b000840c0011180301c0c050389070341208034008a005401c400c984120b99000c0341c9002960390052015010f4445080e0881c1c00025014000303e9520420145009110701310026260703051700c5a861285100300f00c4d41c0c81101075810ba0303550141200e840041070000f00920082d022801042c9011850040a42c81d2085c841d82c0030b000c180c02014448404104440250098103961a410b89007401404026a4002c1da100c01c060285005c01501040341e81444401744150b180c6013548003089640071040500390f0641c0f40096 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 856427464 1250 856426214 856426253
    0x9050f070201090c05042c06150105040e0402090c090607060f0b010512010329010e06011d0108060d060209030a15150b0a12021201152a140c040504 65
    0x2500003038003640705005216115500004074012285850b0a01c80500f008401420340351080030704003400c1c80545040d81e2440ca901c20024081410103254095500724901d15007410002e081205002850340030032601c0d04075a040d6940100707540d030300f1080b0030300d4041c0b0701016038417803800508070003800b1081d0021140892400700070840919180d00659552103480504e1701c09462420040000c10240242c1c00150715a40e0000c0301c000c540400d0300703000c0140036041107184501c54801d008603968415070b000c0c091242c81c1100d40c81c60081c0f40000c0d060600050046125494192545040205940548010240180495030182030a19040003007800c001003003018280382020314412a2000941030007102e00c103047e264a020441d100c201c5e040399459001928031502000b20050170700b1911031060003008107000000401c2c844030300042c2820408002c81340c116185140e140c00403080e1022032049141c1c0060340c0d96140c026001d0302401c0003c4c4448841e8018070b08070130072052104540d0701c5180070349130 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 856428714 1250 856427464 856427491
    0x801020d0c0e03070302040218040518070b070b2e0602030a08150108010b0a090f030308063a1401051003020a06050301150e011b0c231513030b010905 66
    0x409007102c103101c49440d519030640c0599010005030a01c0c4d03004290340c03c0ca4040c49070705024150007241c1a204182c0d0344203580985010050080300c400d010f4140030b003110400f45440c050007502e0341440f0b0400a4504600c52092214100041541c010000b6141148040114899a481e00d01a41303079040314030b00c2c001103034199000605640c000402a025150141c440c02c04503401d007825282c1681000c50b0b042c09103e1a000013003460b201000e80384005511980c0c50348075501c2e003203090091a402800a912201aa90801b007500528440c10380300c1414560390a00003180305801c2404020031260b4600e0b129510301418008081218500c51099a00a56030000a20344c0e841045900744000d1080344820380e103001c03135200810b00c2140c44000305041490500c5011040320501c03a085030703c0d41d50031280c01040900c1008240320b54a424086113100c0c03400d9903852400c100100d1602d158442c40591740000019a40501c0205140000301864100c1240c014968440503420000c110903070345018681e45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 856429964 1250 856428714 856428731
    0xf0c030c06040f06050a11030301090b130c0f0503270703050c09070905040513050d0806010f11061f150207030b01050d030518060c0d0e0a080c010c120c06060801020d 73
    0xc0c45400c0b501150092604030070107924001c0d044405130860100d1a0401080c0d40041e44010b10403c0914083e004020740019150200c00802104010801071000300f1410402200f610701c2d00236004111003603440c00c00079965662070003c1d405102100d04101d06501d8214109075859800107808403c0c0d0303224804517928101040100103040340112100300c0010b01000e014000d6003130139082150404070000d1100452079043c0c1d46e1906103090300b0300041c0042c8406003004025a070101c80a0111409410f01c26404103400e15180e860b6a0010064085e11001d0780d040c00302d18026a849100622541180c0c00051055980013506d4405520003030b83d1148425002141d9441c01c00c0100440702d602d5119507241107040303140c05044240340c02819501407828049000041e005110f41c000f1500700e540c880d000b0a00034400c1242881850b000401294840008641303140d80059100b62025000b4010500d00204240d045601c03079101c3d02d0007031149003800c3c40042d46001c150007400a021008405110320340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 856431214 1250 856429964 856429969
    0x140102120402090a05011523030703090b060402040503070e040f1b0f0605190f030b0604090b030f07121509020303120708091c030209031501030804030506070302070302210c0f0c030c 80
    0x40c07081c06078080c0f40b0b042640241600d8001d071000350a4454243c0009060303000c488c01800103410031940c18012989410f20601088003a10a299014108480460404d42084080390b03940d083c2d030182182255004003c40c4c14000780b81c00d014501135001c1c02e42440c0340d00c42e1a60008421840c4148114168500c0c80440c4581c00707841914001c1d0f060800c0c50fa0303d41c141d40d004480150011074843c041c1540c94081215a441d4000100042d0250360300210342410a2018541740c050100619022500444c01c1400000f05986110079120f4000551003070b8900c800303041c58003d04800c04029418840000e003c0c03220250043c40c14401c0101d6140c0d1a55980c0350312000d0b440c3c00480d90754030b54642407002004680d60096000e4403101402a0484000031050741c0801c2d5006001c0c2c000340c6c4c08001c085010030030400108092940802c0524066050070f013a50b50195440c2c1c692442c00c1d55000e545003a203022a840d8500390f5480714161b2040b60080c003411200607803a0111821300714000e000b59484203c260 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 856432464 1250 856431214 856431221
    0xd020a0308070509010c05060c09130b0d02010309022d0a0801090209190b040216211d281e080634080603010f110a0309140102120402090a 61
    0x229096111070071070b5650b190040351541d000c008080d0600030600b17031070000318500b0480035103e1100f1520440d51081a0010040d0710101ca1601001c45402c041202d030b081d8035035408410f0b1055080c200855500c585100195003840900c864990034180340f6030110020b6262640c81440750416038060344030300d0b00d488419099a80030340001c1c0d004210100030401c48a03e07807290b0064496004400904c003203ea000060903a8044150000b0048404080c401231040c14400f071003448480c05401d5150391000c00b400740c00034440d00b100d03d50070306103441101c0b031f551140070412010042882001460352501103031449014124010325100940720750900b40c041ea110f0700900181c1d2801001000c40399100956140421120500b1010042c90704000310088102d61414450310308154543c4403e600c0c246050500719503070420095842410441498041072000045446412451030007044035109800d0042400c401086046025803001800c184046220301c81103019034422619480c4035102d50305010140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 856433714 1250 856432464 856432483
    0x150108061e0f0102010b0a03050f060906090706030b06120103030302030435030a062c060415060c1a01170618190c05040f0615020d09140d0605070f020d02 68
    0x21045001c0c1549240c01d410300d002d010414800840e0485128000c5041d580c000d80c8226070b507034040d60900301d0805050000780d0380814004000d041a00c4c00c0354017159030304224882d0805040d170b1100000c545032180c0c001c442c621030006080c5c1210307507501d160040085d8001c032810385c0c981110750070850202d4000e00c8003000300c4400e0341520300b807610000d03042e00c881da001505400d001e660390000003aa00c0c450b000103150680199648400e41e030710106040c0004136000307200a1056190940e040c26410b10b0a4141054541d03901e040c0b001e50440d4a0f2405e0000c099601c1001e02c1590300300002108001030412800754030681013611410740b1207585010840d0540c01101200d81c20064058802366580308039111054000d0843d0300f0f94960301c001107170032500c150880150258541c074042c014120000c3c2c4200300c800d087e100600c5080300b075501c0201460031320f020300d0507001ea80c129414060b80c1c42d48111000c040c0c000c0820001418840000b07000c07082a008000007500035403c1d000c1031540045110002d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 856434964 1250 856433714 856433749
    0x31b07050f070f03050d0c030f031a031b0a142202090306010b250b0f06030304170a111c030509010c170a0e0603010e0403080705120a270312200315010806 68
    0x10b49d901d00007003600503000c03410084000041110810030517a40c10041602004601d0303d20a0386d03d1081410f02060b102e85412280401304000e51121403511556642074100d41e12006003a245911607824001a02c140705035103070b140c171071030001055040304240103004400d030250000c0000755200000c3c00c06446410b40140a50007080000381c80c0c100fa100646911920040a69141a0704d650708024041c1c00d2300b400241c180e200001540170031104031078091084070101c03601105520034040290094480000040030044046030900103a4000c2070f80850345a4031889145510715801ca9256641d0090306400c0c0001c0c4000b0b08000c460f05046048034144d0700200c0e280101c0d13654a0f01e068400d042c0240403402005010441d44c0a050402803a95014462090001c181c1d20800f607800c05041c1c0202103504001c1803076407000c0c0002504800d100345283c060101c00b144a6100e0b6030502025a407030300303282019a400004210700b0b0404204030b104500003d0700c400c0410303217420060214583d11041c0e1001d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 856436214 1250 856434964 856434977
    0xe1905090d050f0904110706021c0516030902012003030a050f07170c070b1806010603231008060103031206080703030801030b100b0a020102071106031b07050f070f03050d0c03 77
    0x2600100740d48020304d01240d0280000c20980c801e00e000f0092503010203401c2c1c90080c0d010890100c0081ea01210020007800c04a0600c00d81c20060411107401060000100606030307502e141c41c08590240c03801c806500385101016030780024843d03400303859520495982d058103142c140028907558070300e050940034150540c1c8156904a1000740014a00006420b85080c43c40074089040010201910144500c40703007807400380090b200d641c1c00c62800006800010a040c18072a0740c00641d0300800d68004080001600b94485442c4e0100280d86817aa0350442201800f0b904004014141c00c00c0b40d02c20303c8030000e001005a00d58940001d512820140002000034241200400101d0142d0700314030b400c0f901c0701e00800340080d44c1d19080b4071aa03001d11062b00140c2d401003100400d0200c400c542c0c2800807000c0c0c4803e032075440c20b036501c010518503000500a291401142c01c505100c02005044a4152000c044a0400f5207031401c84011882a00c0215414452038510b444500d109a11032016a50301d48c9501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 856437464 1250 856436214 856436227
    0x60e0403050708130f170c01020120180405070f0f08060d03140c1509070b0f0f0f0d0903170702031e1605070306020919080607180e1905090d05 63
    0x50030742e102c8207807144200090400803070100300760000c0b038004140d0b0f8011b418001984000060070100d01c1c1d01a207066900d001e1101801540c0c8240951800301900704195540701c040b00000744043c821440590820f141c6001c00c007025400c14440300e8180c0303442e2071305040220480740442d050300701218425040640282100c0009004944940200151400e03c41c01c00c00c01000709450078040312805008030202e10140315440c041405032102510045000300c1c40c2c020700c810721325603520600d1001c0c802040000f540c1c044120080d0291200a005071200380204412420000c0040018000002484444001041d107250000044501c000d0030030045400c02800c8843c105503a8000d041071440c010b200554110003c2d0741444260080c2d03228400058403100e001c8284550160901340d28040e4504080051006603000501c06034040307120715110211524148520300100d0003035021000104000080c4800f110f07083d884c210079802480320400050740d40d0000360b40c1c2c51000324501e2011507010450b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 856438714 1250 856437464 856437473
    0x1e0d1d0c0405130506070207030b0105151603030b1e0f04050f04110f13050f01091415010e0402030708061302270a0f171005010e010e0a060e0712060e04030507 70
    0x543d480044042c54002e21441c0782c60302818844201c41c0080103030480803060040108011015000d00029036890759030110714016010f03984110222200012800180c000800d071091700106022140070b481c7c10b111a10045480c4c481c3c0303a06500c480d2064030b40400060340c0b414035105807071082041c14040f0394151181c0d1101010b0007070701d81120b0341115001645c060140c4038641081d5030303900e296034002154500003401120462060b04241001420321310441014000b0310142030b00f0200c2e22850800c0155240010b9555081c030520480d0864004004c00c40c000f60050302043c03040ca003da13508200400c010034254220b00c50039200c00148506044100340e8410054400b40780d5540c0600511200744d1140d90400130810140d12581580760340030621003001100340820341c06002544001d00042d41020f014008112050241444c40742c2300d5000104001407542064005181808507006142030407400140042c08542040610038107100c40041c0d50318203800840c4c4501c1c0c160b0703582418542c0f03d81c3d0707 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 856439964 1250 856438714 856438721
    0x4060504020d06020a0203070c080703020a03170c070905190605091501110a05060405072403180606031b080a0c030318090c0f0f0503101a1e0d1d0c04 66
    0x10590700b00c0604600980060340ca0f1004000e02103d5030001c6403204031500d003164041503107030051200da402181d800c000585414084105613940108090300b0021300f850150100c8c0900c561061041c0310710f07000050007814a9015034020039090245601400002e00d190051312541c1c410365800080010008030301e42c440d0911241c807401c0501d40803a250090b076107841d1501e02221420b0300c1ca42c00c0501448100b02080207140020301c90f0301b52101c0321400a417006611400c842c04036005054a600d899402d00e20071805a551007a40701504118481d26814806001100c911003440d5180c61610046036441c0c001420b41040c542c0400703050262030966604641c0302c006068000302542c0302c0c51012a00000c0b0740035941c103884079a900d50780b281c030107480001c1c62014200d000000b4400100180800104003589daa4240ca55220f032000a10429140e004614411483c41d880d40c81c400315180140280103078020a455801d40d0024880e0805e00e0b03d245480903080340640a0641c081030790103680381451f81 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 856441214 1250 856439964 856439971
    0x6120b03070915170d270306110c1f0510080c04090303022802010515010c02010c0302121b0c0301020a090303140d0e0c01030e0613023a060e15040605 66
    0x1050000300c80c4c0c0d02c40c0f44a0441080c90030703964160700400c3d0411115035004c0b18007216850140c0c0d4011400030700740f0f101842c200c480d01000d090944c456590002c0c0161b070350300720b84802941c00d00302d511044100c0740502502041c143c1c0c03a40da540c181008215040740c40c28081007518022009070000010103c2048010100034404400f8580c090158040d0303400400308240c0211010a80040180360720740300242158401803081002641003150b440b41664080b5846a40c10390a090150004600e410107034a00f10007400c5000003404001050744103802600b88000724544500111003081140d00b0426080c0e0080803501c000280c0c0d0b2074420408644628104c00814032540d050918220700c00f4000b4094543c16800303001168002041b90b8050b5074076100e201140d0b5401e5029181034140403951240e02585c04201910034151004055450b1900c20640104201c1e90004a0440400d00b42d882c2c0c0c500795840d5082d00c0d01c6180c85400c01582c00e0100d030340e1080440b9000a082540d865a6030840100305c0074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 856442464 1250 856441214 856441241
    0x91e060d081606060522020a021c0e0a0503010c0f050f121005190b19030212090a030f020706020705120f0a0b0a15080318180406020406120b030709 65
    0x10a061000c80d1102008040302ca18400341060080c819003402c00a69400d40c1c40b09001e071400481c41c90910200044180300a41c3c103140141e5141c9030742500702e280420040c0c01c3c00c0c00300e6241d149802c4140d040382540168000503142c41790300c559038800701800c86070351503000c101007201c10072a03214540c4248014040c1880c400d50840c1040c020b000740c003201020444000315000c1202e8018003c0380b401c0081032070390480c0070120110f000d0400000c241c5500801d0900340100003000710400c052070003501078400040c0440d41c100e29a150025203a5520b00480c04160007159508046000341c070f02c081003000c141c8070f00f50000c101e024500300c18040c40f8220a1202801b5020320a4440341500c000d0080a4580e40248219841810b090140c041141e810740005407040406542c1049017040100980e401d5503040c02c1e8004c5245043c401048012418110140d0101c821800300b008018883e40503209940240ea59480e414050b20030100868889441007a4554030104081010340d4080e0060740310038010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 856443714 1250 856442464 856442479
    0x3110909100306050a0f0e030c0723040504050a0605060105040f15140c06060f0a0e040204051008030d020c07120803131104060b12070201020702010903121707120506091e06 76
    0x1a40c481c20201c440a4680200c00c0b41c0721814031410700b076580a290303520001e45000e0361401270454102541c64455100e014841c101c40c10110079941036481d43c1100c00e20001c0e20500c210f10b031502d815034860501510843d0003600d0300d004511154415810340d000c0d2844908039a081b2818a90048551205500400c08100c0f104524006108482001c2c2500c1c0c0440c00040080b420003004102485c2c450900c058068004a902000380c4180340c01c100d50042d406950000309911108141a904200e82d0007040e80c41c0310001d6040044807255000b0407840c240c40f026182d00c0c503100c002000c0c2440803804081d284036070a00100d400788104000740c0208a100b0358a55501010000c0400d099275070960109900000128020a4002004618940c08101d0384000c501e010700f6030f40080c1c1880702a00000e0304080341401c03642800c50007264114072100301080031030741c0c52501020003800d2400c07100c010000c0a08040c041282d90601c5030f00140125044404030b501c0c40d0841080e8801004020f041c00da00003503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 856444964 1250 856443714 856443719
    0xc0306130b19080f0d02030a1205040c0f0e0f0906100e0a091205040501140c1e0c0a170f060105030d0c06110d05010e090607090909110406090510060311090910 70
    0xb40782c10b400010401c000103000607090254034941400c0150840000755081048685025540140761038602040464001441d4aa90078406000c500300c2d04407a900340b0444001145060310b082445103c2c5040043c600c1c40d07a500c05075400c0d1210030540e0340f22a22006403600307101002000a8490b84450380820000300130102d03450300e580c5205004124000710b003000800344604e503440080307504030032910b41219182120040e0480da0301e041441c0480271055040560160b40b2405210300c08101c3c40083c01507591644889500329400741c400c200e45400e00c9441c00750341600f4030110703038a0304940005003c0d10740710480945c10383c1d2640b8540c40c112410303981c0321210090f520448010f81740300d80e40864005280c0d030420910030b41c08007026007031036003c2e48002c0412095903440703c00601541cbd40c02c000416050701c01e2170304004100d6400c84595101c0c4c105000410202105d52000f88070340b10640308285180c1e91401e0a42c100da60b00400045043c030200000400ca050500700950400c00181485000b1503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 856446214 1250 856444964 856444999
    0x509040b040504110f060301030519080d06060305010f05030a0c0603020d0204121406070801030503030c07030509220b0a050105030103080f07141b0a12060b01140c0a05060c0306130b 80
    0x180e048800b2503036804c04102c45842070801602c551070060056805038519419a00c2c0c85650310000e003a480c6221040340d40003020402a403080e605503014064040c4801c035210100034001c2c110034055610809011b0400081603d0300040c80d0030700c50340001c44d100310241044001c134041d5021071083c006442c0c0800001622154944807a08101c1c041c88ca000844074025000504150014164400704409040140b0101e0b00200440c4d41020a5100c9140da800c210321301a64180550400243d0108806030f009180800c0c200c4d2170904d40824010070868030f00c2c0242044220611030081d0f074000345040c4018000a00702c0001052290611301d907090604202e551802ca4400b00281c01c51950341141d54804400070340d140010317036110f0301111149001405c10860303003d06c640b48000503204988504180050342d026044445a204c5529100c0b80c5e10491220000d607a20403d447c1180c0620800c000221029047d00550b40204002040c0d0b60704404d084200500ad01000749140391300210041c80c003078004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 856447464 1250 856446214 856446221
    0xf18060f0621060a08120a03020310030f0b060102100507050702120c042a09050d032708030a18030206040506070302011401030b040519020a06140c0105070801050a090606020d0509040b04 82
    0x149074002c40d29094076001090041580a5502060b8181e118481d0003c05408003010340742e03008014035005032032399500354503407280e00c00d0f940c40a40921030707030a20142071000c0d5140c0544206c0c402c0c1c08a922204c200e2045804841007107898000040b01401501e00520b002043e50340c100140c1d8040315202e10709500010129102c00901e495030a90707004500300507200c500107920040b000c070b0800580080c9484042840c102100e42c00034100400c43d146c0c800020000d00241a404810400070041c56488142d03007a602c0c1c0c08402d250003c100c02c0c60ba070220707204406c1d01450549a0103800030781003924180522030303580c0005e03200310b080d5501c2e820200c01c648050394005000358000d01102140341002d003070143c10001007000b80030901da182c13000b10000d42c940c043c1900849d14030345010b80b02600c00036010301c0f5500400808030555400c000600c80056482010b00e81a504101c800e20b880a507140345c50002c55a6034400d02003d41c0143e0204224503000e20050101c0c0c2e5005040800c00b003400c0d00024085 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 856448714 1250 856447464 856447507
    0x715020a1a1806040b07080c1201060f0215091005090f0d0c021302160222020f07061d0a030e0f04020703020105010306051302030a02210313050f18060f06 68
    0x21403032001d003000701400c110150040c5401441c1d010307100904054459050b80170000300703040e060000c10808504440e1040d801c450340c182030f2001404a55840d95401003036442694142d400601c5820006a080d880051186015058443c010051000c1a00c44080a81001410721115000e15a03034086021014065502030080554440e0b2084a4a10422001043c1230b804580d0013807061000b022880c0e40c0c043c41c89070f425011540c1b0b00183d43d101c602c415040b4110440390307591500100d451080b01c0c80344400b50110341e1180c01e081c007d80190915101c040412907101d14910b62003da80307107000c28058140188030410280c01400848069000b203006e9a10036402180140e40d242c1c010020322100b13100d029000218038102040c1e0140640000781c1da5440c3d040080e20690705003452180c9902003001e480d000030380381d0064030f894918806c2080107696442c0324690007a00300d132a81091900d0040305039500c880b620343c1c80841688883d01841600401c0d101d00d160480010003102c00840007078450703130f000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 856449964 1250 856448714 856448753
    0x51f0b03040f02180702060a050c16030e0f0616110306041e06091a09070f0b0a210e0607090902030c07140708011505130908031b0d06060804060507110715020a 70
    0x2242404580201189d00091251200c10f0060007000030303c1b80803040311031102e134051402c410449043c80001d01020003c82c0c1050740084001440d20000003400c00c2030140c03900410010b22500e04520030306481d40001c44000b03080c0503120907100311254030105803402036401840d00140f8a000c0e652a06000c0d05481030003a04818148104200078008210750b401410f01c0802c60a5500d181400ca80454005d4280380801c2c01519000039040b445404058510f04038001c01c140113070314441d464140c5466080d80d81c200010013141000c203c0c045a80226405001075050f21864512a40c4540100f15084400303140e00f40280c020000c3d00d03140900920703d41d00e5542c00226022494541080510306261280315000c50610050601260f881c506580e07120522280120400e40b200e948189544984e440c4040143e2600d000800c07503d91004107640703c0c6118000822a0380c8034038000703803824001905409500c4d84510406d0180c680326030700c1481e1a461600454900f480d203079944d6183c02071403152212 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 856451214 1250 856449964 856449973
    0x150c0302070209160801050d0516170f01140f0c09041e0e0f060403050f1309060f14091602010f1b090e0f0f13020603040501051f0b03040f02180702 65
    0x254904104107541121a604181070442400c100c003401c01780051141c9446901000c0050041c41018040e42840720024a0b060300380345d4075105140101c0e59501600c510354800c0e8601c0307a468a00500c92180e807030031622411000355480c0650350300700da81c00600700315104405016290f903e4540c0d009080d02020703003001d0045c00543c14000d0404640308059113070840e80c00300350584140480410466001505442c02c903035140c0440b44100c02c03512a0060740103c040d6100400180d40c1c031954842c03800d951184503a101000d83d204403214426624a402e10ba020501c000800d808280322000e90034040110700000c0b912500190311603003100e0a410881442c00c41d0004403000842c3d0207003141010309607000b000e09603401d1251421604903401001c1107450041403000c00c0040420780c20405800e40d0041405581e4601482c00d135020342015100060351184404800284c210b400e00d620090b5a1104405410750380d031901c0300c444d1300c500c0d20301c1a60402100c0ca60030030030680e0b940a051240d0700395001007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 856452464 1250 856451214 856451227
    0xe0711010b030a0b1617040305070b0c03150409111509030601050402190e1801080d0908031602040504060f1b140403030f0f120e0a0501061202010804020904150c0302 73
    0x1420741d400c140c07120380300ba00a4140c0000044000003002d402c11132070052660b48001203101520f624880b090780204000d00344040008141d44400103040c084e104843c0c0180d1a200c003030b80030079640401c0e501b078040b51081062044013400c00f5401160118012200c8000c02603042c0c011a580d500104181c0c180c0d044000340d0700c031803414200034041c01484262401c51600708503e90460010035200b03003410402448020314074840c0e071240c8800c1041d01c0c1f003a2821000356940c0180c81e642d404040c25210120b50030f20400075602c5000f1007a22102c54103561840c09441c101e0b4200001011f004000722000c640d02d040e207820b101032501c545490f81410300300d40d030f80d5810162409440081c0104e082003480d50100020f01c00281d029500700d900c0d0300346003806d003000c14000c0400d590002c1902446090b01780b42a05011076a0360000303c00403483e00800c000c00109444004219400c144100040d021030801d801280050400d041c000781c0c018022036000141707000c0c4c5800c0c84c0a0341c04844c10398000a401007001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 856453714 1250 856452464 856452497
    0x1201110408010f110724020f210906040203120a0306090f0b01141c0218030d0206100b120714040b13050406050d030c080c0109020d0c06110d081605040e07 68
    0x518100c400300000c0c01c0d06244e0316958100031074840400b1220954510664041e0b00d810a40507207118601c0440c01035154279042041c89280d00c800010140501c015402080024030045040c134003d03a00074015101d2482c0c8070003607200321390001c00c6030700c00c041d0341701230009c0d184c111403051000d0320524000125403150024001012084c0c04140c80c40101c00c20040704145860b038030306114941030b010704003503101c2100d441c0d4a000c0445410543c0c1e0140606550a1541540860040d2083d138911002c03141031611030710600014010304400c0340c0c98004c3c40010844042c00b480c003140a030800043c5407890551550520451a04051090410741400800a1100d032030940105006004282ca201c060310b0f000d618003c004900207000948128400201c00300c89050a4200c0410182c0207450a907580000d03107000c411034031141c45103e00084880c0740c0704660400100b00c1440c0300220b680c8200e41602d0300c1c4844040551400c010805200040100040356184810b000c0d2050003107840b42000e20107000003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 856454964 1250 856453714 856453721
    0x3070302010b010f1d041d0115090c0e09090c0a03060203060a0603021204240e0304031b080a0b0c041d060f100f080a1104080609150c091201110408010f 67
    0x2a03007810f12056040c0800b515501039101e40000300d02d040e80d0001c0e0707601400820300507d88094084c020034031640084916a20540160808040030807000b00b14544d111140411101000700d250000741d4074900031004c900d03044c28199000380b1603405840824040d100005e8440540d5801101e01c1034011080142e00e1820104a034014901818290700d080030f04002c1c41c0003c2c100502c01807001c004840815600798545d01910b85200785400d040102c2c5444c5c40341190341e0b421621007151050f04d40644d0080c204294a4a9021070392048010980c40c00030380d4a00804050042072000e04803010b110005104110310031501084448a015160a003040b0060101030018030410078001c00070903078580c10059108124200e00d01d4a03240c03d00c440d48401c10300b01c002c0d2a04090008a603140482e000c101c0798400310341c16014420f1641122044640300e101c90f0b0300702c03104851a030700c800810301c45c855050424294000788840d081c0d00011710f1800c0c1182e000301a40080c0c1001c031103071b95200114010200c1511 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 856456214 1250 856454964 856454981
    0x1008061f0f0317183c03060106201b031509030a0315090543050a0203070b0f06120309090103140a0b04030503040b07030b031002090a05030f0307030201 67
    0x1030341109490a60f160520b0300301e000645510103050006018144c3c03075990006041d605801010b800100c0280034181a0303610b0151403610043c440f40071814120400c00113003096010000c0c015007044e80c40c0840641e014240f10241d12103032207a9042e02541c0c8075091103948150b02e0480100c00e00398940c2c0c01414a4000c01e1740c9050000c01c4503400740400b894000060380d02a600c980740c0420b1103407441801800f1030420f5440941c10505050030701c1950704034210405034070081440c1014220481e00750100d07094078042d1466820100703180c1da9002c0544039134000d018078030307044c012289400c2c02075844030300e0084115130840749078006c1000d1042c14601302000341480c40200001710b0400740b00500080c8954410f12005200b40c0c0340411400b8407803414010701d0361071600011400400c0c0780c2418003800e41d40c0101d40031540841c400740000e076518024440c4856a42c0c0103402808221078240812000354450301c5200c0d48540c01d001c000039907540c200044178501c80f60201035620b815103840c02a09564512 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 856457464 1250 856456214 856456229
    0x30b06070c0e270a0b07121109030d1704081810120513170a09030c080d0905010302120411040f0906020c0d020f100c030204150c050c090705070602031008061f 70
    0x8800611144400500c0d11004c2d600314280009035101c806c0c069600c4060006001070031030512a080d0f42403130850000d1f049282c800c1e02922a4810102c40407115444840c9040d8001411240400c021824010107440d0703440d17030b820a80d80f91000810010303c0d580084041203000070007070915504140507134011550866941c02504042c05c29903990014400c40020010500103400f20303076034410038030039441040159000003141c0e03a0641c0342e400e12070f1500044501c0300c0204d02407400008040d40b00b442241c1140e03007100007012480d102e96940240c860b00302005241d000d80c440401900d400304910507a9072087c420500140d8900b0420441c1e0b090034041025001550001e030010381e150900800e80c00105c4002000014001c1803c50f0240c009000ba900815008900100380b081103903044031740a14a18054030455020038144004c20a07804401c03150350002900620041001416503000380d504140301c4120240c41a403205e011b50725112088450021000803d14510703030501c45659500b001d4103e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 856458714 1250 856457464 856457521
    0x171c0903180b0a260405070e010b03011d13061b030b0d0f0f0507090615081f12051504230304120b061804060501081e0a03030b06070c0e 60
    0x1410350903245801041103410034044000454020469509038003502c0713007000c0c90100c8880c1410300380140d03030317003002d0180c00d500406040c00032035410004c07401d0b80d0403120070302094006c08101c5000826022000703000420041c0905620300700140749405806a50b01800c60344500705000e4100083c1079440f03812056000302280041200403c030034800c0a070100d90401d110211684807454800c2ca403404503030014101c1460403801107075280c5800c0c2d48500440315582d0740061500e944000354201b080340070031001485505001003241202620388400c00b030340200151040c0c01440b5500c0d041108040301c04480341041e11022111040b050a0840d9a1302c5c1d20380000c60909040c660103e040e03030b00301040a0144071600d0009000c5603662910385000d03100150720600103003030a1400c08042c1c03800380038004541c020320b5000d001106604540481512420001b40707488280790300c05030020550b041c80c02d500141c041044102150101101d00014440901703c40703103e103001c860b041440c1c0c007012200350b901d016 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 856459964 1250 856458714 856458719
    0x20d0c02060304080a200106030b1e011802071713060207061209080418090c08010908161109040809010e0126060a1517060f0904171c090318 62
    0x180c1e801070740d40c0181e00014075030381c960703503002c099860386020074182d00e0907502000591001041034200f402124403c00610207591641042c10b0100a614400e0600c500c4d46140100960b58654400c0c040d440c40540e0010720307247c1262a155286071a40011507011940040c07458202e11061011900900b050700c05042400e040141c01000c00c010700d55846541070702c400144007070107500c8040324002c21904200d02001036500301c004000c0c0600f1002510710400c0d400b00014419818080c440d081907002103d1840c090000b22003a201103c101d000380d030209842120211645c407039164031030145020b1012a501c45902200052002e00030304d0100d41005031802d001080e22088208580800a0424122801e9a15500414151011035000d941491a1030702c0e22070141c3d801c808030140810b200050f440c0181d075118188020452001d900d40d0700040c4003400600400e024241c600d01e01121092610300e4199081272010f0400b90340c1d2143d5041a83d54800c600030940c0158059107100301c80c81c0100740c201d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 856461214 1250 856459964 856459969
    0x50709110a0503250f0801150f11070906030b0108100b0112091b090b040e0705090f040c030506071709010501210f020619111219020c1f020d0c02 64
    0x80c1d60080041c0503021011070421640d14404003905600000c44840c00e407400100102078580c81811400425995000130540650164015100390a651034103501001d0355042110b1940c0d00c10018282ca0154010200741600e56004600040d4007841500c0e6095041103880740c100055400d0701c1d540700303151100581e02a600110842030040300c84000207817000081c24098610b03c9403915110007940300300404211201540c0c8081c3e80d0880c00d0340c3c100070603818100380560b1640c5a02542d94802443c20002d01d641001107040ca074401e1180d450350002e540c0e60307681e1503d051b07000d8481130007203404c1001c50004d180554843c0384d801b251003002407105501d001c0d5164501d0100d10301504504803400858014030101e044034084103940500720603601c090708406900700803c0011090f00003108004e403400f94110000b50404070001e0b10365101e1901c4441030710380c8038014500d60003105502135051584c5041c0e8902d442100840c0c101620159021030480000381002d61000e490700510070750210410242c2c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 856462464 1250 856461214 856461217
    0x4050c0114030906010b1c06090c0908011e1e02030403030c08090a030c03050a110a05030705010b0a060914150d0911060a0207331e0e0d0215090d030c05070911 70
    0x140c03400701d0aa0f687c2c0d05160215555040c0700e400340002107043c031000040403401e6500900880000740c0da030101c92a19004000d081e100200c070405a1074254801b03448084110741d01c485810240ba040c810b000a110b501e5a00c10f0381c00484080c0d0210ba030740c203a20781d1095040741c800c550100c0c40c0780103001c072179406940161241239405000b60801c81c000c1741d18400030f4001c0820505d044480c0007141d500550300d1504070b0752584a0070701190f255003404580156803c141d03610005580300b90312501410383c10902d42494036219900780580c07108000700807803003281c0410b00811a0009034580401e480300305050801c00046a88003650184104000300703a00e4a6002c11ba4130305650058100c56482c00c0500e0300001d503050402c02d0300c442c500c101f100c442140d5030041041e83d0413035107102c512900700d0609142522030000c40c10001da003040d60707603070381c00d00503c2c0c00001040841350b440d800d141040007150100307003681c4010a0440c0410565108901448410005c000040180040910038200340c00c0d1100c54a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 856463714 1250 856462464 856462469
    0xe010b0a110c150309010609110a03091104060308130f05010c020111010b1804050706020d05250b100602061b070209040816111311031f050904050c011403090601 71
    0x1c106041003081c4140d1028002c1c1c40c24035900030901555640c0d110800c9030190b105940898084d0319244000412160b94003840d941d02c0c4142640500b404e044000941c05030184900854a01c10351449003115551548180c502840c0200941a00c0c1c0704200700500030782c950391b000800014087c1d03504004681e4043c3c040c82519030f082c40c1c5240709a807003a60f118090950b80d44100d43c8071004400c0902c4062440c44107501c224000c17001c680c061030b076500d0300760703100ca03080b40040740051010408251041850030781c2018011015610410156440e1901d502c00c0105071061030321911111000c0007e694100131041d00021740c0210100035543c2e0f07a601c2701080c41214030080c02002e0003000141880410000e840e20145140210a4620002e00d004215086454081441107100400000d0407170094070a0100b07000401810500d9500d404130070700c041320049041c00c03ea0360514075010400d42c4030080d841d401140b0a6000301515014100050a41030f2a10840380b16210706004110240f080081e40310304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 856464964 1250 856463714 856463717
    0x12120b09010f18060e01080d0210090b0109380135060a210204050f0402090a0506240a02070e04120e010e1e01020d110312070302041206060f0e010b0a 66
    0x800e80f04400311001a1000741d01003000b030420100001145c00001c251742d06001d1195090311600ca81c1d0144210440349445c8002d4030b40401480103110b164065400b429100c0160b1404045000b0500307034055000c1503291710b0b01c0d82d07042c40311502170243d600205803c400d07400a0086d1038403411a508000059240304032914880c181d40b201050240e00c2b0031202801409801d01c000e502d05940303e040300081c001100e801c90280345040d0000c1d00c0c40750a0080b440c05141d00078040302c4152510071451000c0d002c06030a1035808203030200340c1003c00b051450003c01d1815600c00003501d41c1c0003000080d08069456101502e00403645042000040c040c01071610251503500f1300034840c1080400403201c4d05901c0a005400c032205403014017400b00c401804c010a444240d003120001d01020700121061042080c55000c0c0c1e500500804500c0015a5130840d07100103c1c1c9001030034030340d82d00905440c03420250301c250b0b6010340d00c22060200c80403c2c500740c8058030385513102c55860f5160020250301f40c4503c8242c04d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 856466214 1250 856464964 856464989
    0x31b0810090201090e071e110a0b060102011b030501140604060210020c03121801320c0c0d09060201180b07050702281403060709060c0f12120b09010f 66
    0xb1a801508200e01030003250704907055600d0021005050701107504001c912aa01c1400c040007410f00c00c076201d00c803120b40c10018101000203a80c0e03201c03506c00090012030540d520b07086101c40c52081125410a0b600c450b075400b0500394034086619000311400d80010340522130811090290a400048000e000515004010b94805600305a68218026031921011884440e400d015000002d0201e00710850407210003005010981da40389881c2a6081e62a0340f44078103224150f1005142e001c6c0c01e158004040750081d890f0010341101e407414401103032116004030314825010f114203582407145910f28440c195183c82140d400e616205070092008101c4020000006804c07011521552040c3c0308400c1c6070441070117054000300311341d8010320040c02085034660180720304542c5450002481405103103942c44180b14941408000c0343c1d400d1100d803090f00c0c13003204410f8040000b045410440d00d00801230707440c40d035030100c201c0c0c5840548600680c243d1085030300341c00601070710060500b480110b41800b80c545 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 856467464 1250 856466214 856466231
    0xd1d03120a020d090807060e2e1b08070f0905090a05090f0f010b0f04090f0f0f080409050f0601111f0e0609061b0c06061302071b031b0810 61
    0x40c4041e101d03d181d00488542441410010405040058800188110004c1c004050000403896640030146003401c4101d4580c5c40070101c400094110b20202810541c001c1190b54025030b1607410300c001440d020000032711000402503280c0e801103142d16910b40c0b030b1505000f45071a000010380d000750050301400c50681c2d80c4002c603020200400205081c80e8051007a940503112548096000b460300101c00c034001d20880805858901c0e0034494503040a13070040d03184030310910701e031509000d52480f6201160720240c0003004502056140d80900010100c001c3c011410b403031b210503070b40c403d8413010b8115414031000040010310741c60b0200d00000c41603045900c6500c1902c0944041e00900424942c2c10140d01840062140e21003011400500c1408482201c480a0000e00030340c1e0100d101341c841070889174004c18003089091500d4598055034500d80080981800c2c81b68440d04003010091301c46248d91025008200100404101c0031903101400b202d6117100300307140c0300945454442c0300d00341941141c0c1c2c2e91400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 856468714 1250 856467464 856467481
    0x204021303051608120a090e060409081305030705040e0a060c0513061817060103080703031103070e0f2b0c0807270b0604030201320d1d0312 62
    0x5030004641007803c03555052116440849100c5144c06064003d0045130340d001000026181110510b0009030380f141826450301e03500c50400d05000d010303694460380701d06407071010400036005800c0025185036000c01d107500d0903041518000b02503201501542c1005041100e4180100d00800300c1500b060011403a510424030032038240c85002200d105641c0b41140100c4d0719039120001040d21000c5644440402c0d4440d0140d024040c00c80803500c0543d4481001800020848009001c02c00e210381404204015840d040001c9030b001194001d0009000510401d1103141c001e503014100d14040d42d00108441005c103d4a1040981c138104580000800d03049404000030708c42e001c0020288142a034001c50344455803059140c5e008150316400c0128680000b034201c0080c41640212840188440d103002c1c903603401500c2400d01e5072503810010300c04180f402c1500d03c1c0c524036640014840f50078a40d172251164200401c482210803d510300461100095410000000072990840c4100c019088566502c070744 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 856469964 1250 856468714 856468747
    0x6032313030e100201090209010f080d0513030c0e0a0506040b0a090b01020c06120403020616120f0b0307080304170610030f05100c020c090c0324130204140301140f04020402 76
    0x702c2c0c020902e0b03d41100c400f54194007120102c3d20803a900703009039a03a015206130b007461a00501000c0e810421609040e00d00a50041000b44030040d0781e00d012075600e4450070034811883d80610303400c0122004104107209240304041c1e12000c112420401514454081013660300940201d214065641ca86010790768001c01050b401d4445c0108001c0d41c85648074000034084d0740c160750840140c0314140100d02c10308060383c00720810501c5540e87d2000c4016025005014128080248540c4e544e6400309148035241441810042d122040c015030f0381b94a0410150350300d003402c502d101d609801510906c140900c00c07041540849410641000b0340182c1ea040c0281046103201c17440480324030301002c810410340c000c1a01513020313000b11504a80d40da03405000e881c82e44021102200340c80c5003840b040c5510980001c1690308020301800001e800300381c840d02171b4101c0c0c3c010742006e58850714824610030740749401d0007200b405601c401c10048481c14500b40a03820400701034002881039401280d500c48100c0c0030070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 856471214 1250 856469964 856469987
    0x190305070e10020a021e101b060b06040e09070f0503070f1a2104020117070e190810062603031503010f240501090612050c0909100603231303 62
    0x803e140d0991070458401c6410201140c1190b0240c007a0001081e915800740b4920010308e40011220b1403d1a4907644d12030060484041c1168030450920000c030354501c2d2a0040e0f0700c1015604001d0514a003404581c50340c01e58103a0085120350301000d018082030071090b216a0450785d2442400d00807804203850303c1c01600400445400d0718203401078100207041041c0446000344c2c001c4c1c0b41c503d000800c04505200d1000101c6105011071700080030248513060407850140721105890803900d42540b1990090301300003040761103140705601c9a10500c1011444035a5003000d815aa440030465903069460381e13100d010081c03074851240c2d6078811213980380d2029000040d85034185c0c1401c010801c4d8a15111a4190101d504a031000ca099540412903501400003c000d88080da1150351a680c0488640f2010300701c000e00405006406204d021f06c941ca800761413038000d00c81d0481d1016018100784006049a00ca20310159030b0a0018407a8000002c05c003480a8000400b500300513040c00903418107540700316614 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 856472464 1250 856471214 856471219
    0x5190608132f0402040b07030e0d0c12051014010506070c150804150b13020f0412210e010503060f121609200306040e0f060c190305070e10020a02 64
    0x18003a014000000080c261003403030101020000b00b03449050100b28001e41c050801c50440030003034000402d00444506010341401030896013000019900c0340400e41c002d601c40c1501c460240c40900c1048014403080810341c103101b00c01c000c00103d800c01840d1845c410b1143c0341c05480c00140c0d1509000308107803458044c14000640c00940c40341c20300300801880080340c0c29205e4000000400c1200c450500400d01d0400c001020f1001c15400d0003194002507010020302d0b809040704000002e040900c07111034161050103000b00c240c5921401c00b548000c070740300c130f03000344108101544803030046da80081c103076504014180e503441c504001034008103002c0160109103205138490b030f003220001d60b9285c41d03040007035498802060000c900c2c0c111035018150000c194885041c4401d100041c2941080e40c0201d072041b0380c2d8000c0300c0b500380260f4131882c1445826211548447c5001611010001030002007210880c5035290811041c54080402030001c1c1208090f103101c0c13102141c06920680c030802c24002490b400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 856473714 1250 856472464 856472483
    0xa12050d020c1e0c090402191809030807050301120f032a02100e030c040902030a02090f0a1a0102150907081f11090a0b0c21030a060519060813 63
    0x1180c0c0850758032821910319401a0142e282e07032119080021513000c0716041c0c05003113000d03542c403035608100010003880b500142c20305624100007a810300304283c40d81c2c414107171140041d110f180c03030400802d9440002c00302818004e04200402c40807406604803ca403a0300b145d040500b51209242c00c540c1d85c010b0752000310011142c0100d501c041c4000c4804400154400c070350b103280c103c4008405980f00b0b0105d4520542c581c00c202100d0391542003681100d1229072004081e24001003c6500160b1f000c101a07603000311003462041040000da9040c4640c0500641500000000ca410140001e560303101f910004050010003001041d4800420007201c0050130742481500c4c2c130411b5101004080ca1050190260b1b405c1c01c10352215484140841103400c0c041d4041d0900d009142080b44000050f80310030451a81d601c07942c04403841c0c82124401041d1541001040e0580d0fa0a0002a000541d202a00100c0c81400c840300300d00401021500700b0012a08107062440c2c0603600d0304640f5540b03c07421040070b086030f02c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 856474820 1106 856473714 856473727
    0xc03060a0501061d12010c082a030103080a0e1507030315050a120312020a0503090609070605161a0f04120302040b04180b04140a06060c02030a12050d02 67
    0x380500002c1c180a004003811b800c58408112580014621a042c000e5481300c281c82c1d010b1081c0c4058105844081c00c0e2040382ea688410311005040f5100040c4051280d40168103000040b60b00604407003950f80d0032042559664840c80341100001d103001c2a886a03503000d0b419503c1a00d9010381400c0701182800381f8038481d40110350094042c400309104801c0541c117180010f003501c002665a80d0380700c2c00d0484800d40380c004003a00c00e1405130000c02080c0038680c0e00c14260b411607540f130b410000c2d0061041c107000791006a0f12010b0000103074540d08110381002c1d108915401288104100d0001c8071240720114102d021340e000b07140000004000400a190072206030703a80b68024500e0008000c003c1800042c01c03582800e031280c01e44100e04041201e50a101d11824009000381d0810946c110841d0b400a52202c142600081544000c070024818641c461000d40c0d0541038804021981c0e0030 = true := by decide +kernel

theorem cover : BRFrame.Cov 856294964 856474820 := by
  have h0 := BRFrame.cov_init 856294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 856294964 ≤ n) (h2 : n < 856474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
