-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4690
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:25:37.831853+00:00
-- url     : https://prove2.me/submissions/19c2a5aa-7306-4ecd-9ce6-edc54d004b7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 843345323 ≤ n < 843525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 843346573 1250 843345323 843345341
    0x160c0303030c0305280c0203072109061e0c03030207050a0b190b1c1e0305090120060114010311120405070b12060405070e28051009120c0513 62
    0x1408000a82e05c100359101c5108110500300d40c00502004907661005484d44604511000750040340e00f0a03580e1340d00c0f1401042c4025010400b810306103450291702c0d411a4200d03000d4003203806c004185940200c105121552a0380c110420003600d03824001c203050081d8110b45030550410152110928070781841750414405a50381c40b86c5c40000d0060403200035240c45500482600240020802d4001c03007801c4a400440207015074910010703100140e0345603d0401c0c000d1400c0e201e5141c0036100d11000d8009009103140d4003c02030444070082055403d0240855550b0544014054407404d407424000106c0c010025414a8a0102030028040d000070075056500e0780b065100748100c51419455804803401800f640da101e048071094480860f0381446d181d0401350b40241c003440d184415504e210002a00c89107103503840c0b449102000000c7c4110031040c3c1c0b45001a01c0d066410380d078464451315000703101200c0e5116101a140601106900b08081600c908000b0300b002014041c2d81407400c0c205030000c100c144 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 843347823 1250 843346573 843346577
    0xe0a140702030708030f0403051306030b1528180e01080708010b03120304050c1c03030501062a0507051f0207060201050c0415020c060a030b0306010b09060f160c0303030c 75
    0x100000d00d10034800400c41d400168001c403801d05548901d5046c10207502c000d4412014030009101c030781d00508107281424000d1809a41c0030400d04100c6091210300018010292074081040010300d400d50380c21b010380040c4c01c58450600c0c501008201c1c04944114130325003032001d4408080e000007184041a000c1d18180c41d0742d0819035001d195900d002c2802c840350407a05a8140e00014446040c404d00c0501450784030f40030313005550420400500083c0c090003078400c01c6000480e101ea08030145941440303514050700d1a410104900750500310400800d40707695100e1408081500d01030f90420406004440040c00b024094032000215041085071051060f00710b60014400c44500003910361050240e0341c00349041480543c07500b0308128055004494810100003984120740c0d0b030118a803507120003400b007182c01d42d40006061481a04040c01c00b001a4001d007541c3c042400310014640e200c00840740c0c880c501c1e104081e52000c040e540a003802d00d08040242844d13284017000400e042e00364000d0842440745e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 843349073 1250 843347823 843347861
    0x250501021002030f1311040501090203220201230d090803010501080709050108010b09030307051006051e150a0221030a0c1803150902090108011d1c180e0a 68
    0x150429000c0307003c01c6650055400b201c00115100c1c49000310340c402e071907018640e454411000314000c40e00340d4600b070f8071580c56564000b0070813044220b10540c071158001c10451a541d100c0054000074010301d8600c80082c001071280410650289084084400050241c031051205a20a081c0006290800d1107180e02280c00e4900091047e803254140d41d0999078143c45040546c0d0a01e8003040c61600081d20301605880208a0a404a0020045402c00308812900402c04900300424802c010296080701842c006018610185136900d80c07041c001c1020126010740e40703c001e40b0a049150001600c180b072068040c0d40c001c20b080300201e000861240031268824403840524010884049a443c0810141002101c40c14000640450012014201c020101003600292500000d44044081c1c0c49010b6503950b486c2d420300040c0c1c50484040c4407401c02000703044c2e403120905107210041881c002120400c514107020001c1180c43e1080d2001511800c01249003614041c0340010042c1840b55456020b2200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 843350323 1250 843349073 843349093
    0x905101d01121205120a06080706030b0a03080904090f060e060f0405030a1110020a0507061103040c09021c111810020703141009260918070225050102 66
    0x462126040381d03586404242c1d2251a41c41d05407260b081c05801008003c0308010034400b40034544003913400b50300c5003440040c0861807c02080d2515480d584040c080c982000e0b0342c1c2c03c190361050381881c00c907500709000e260f036402082c000900070030030054020b2100160450b00c50601416600805080c404c0d00c00b01c0340b003615070868101100d842210010140d500800188a20501c11004403040d034a4000440e02c014980c0039801c03042e80c10111803a00015000715141040c0401e5000f40701e501d1807500c40c80b5256041503124408000154040c05029580014514100300c2d8134442998801000350400c001c6107240b100c079266998404401601c00b50000c40c03100410785031141250503001f105030003c00c4140d145a850b0200c031200c006840c602402001080c10000700c041c007030400d01e1440340418500602240601071203801e00524441c9040109201340070f8961100d4032000116004540c003401c0300d54445104070f00d03140c5c452203a0303541100c0000c0100301c0da110140e64903041c1e5500760251504190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 843351573 1250 843350323 843350369
    0x30405061b030f010314010605121f0501080304121b06110114060108073c080f0403141602042c01021303110a08071d090a0c031209090510 61
    0x2081e107541c3d0303110310070380c0040001454078802e9601c0d504c00c2600104160350381d03000080e4007070345010a92071603802c05504458054420800f003143c0f56510142004107504021500341d0340d0240d8040c0c004110b2188403070074107000720a00410705000c0d80c03040311600f1239211000184115460700c442c400c02d6080c149175030046045180301611615045c3e4a82a4a41c1c44650446081d8140003c3c1a40c20b60443c4808800c2e00c0d4995101d000101c4120099116031030030500100b485000420015070081d1541c144000a54407024001d212540b08040700e440301c0c82031401082c1c0bc603200800070761091404008104c18564241c841c56442010301301c0c0710240e110b40b0003250a074401c2d00c441200c0340100b0350040c4002282c00340c2403c060346000d03099151003074550030f6440c50030310184c008092220032446010046d40401c0300c6280c5c8483c1250240c8400100c990f00c80e9403100c65400000c0141c40b4940c4052521072244e0003c0b03006200d1900e0500140c241300b5403c2c11020118000c0c0d08401c06070450b403400c406 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 843352823 1250 843351573 843351577
    0x30102031302040b04021b0319080106050306010f2a050f0c06030f0405010b21061006051b120d050105311a0d140c1504050108060f06030405061b 64
    0x21148490021071800e142d820000188404414035a10070b60a20000b0740d0f1400b030501e11804c5465180003569105180e00c11846101c500465203c100000800148089540035041c2d1342c0041c02030a00307211900780800e0581d0745c8408041040c904903030209800310403600680d10005da080c026415603010082c10007609845800c0b03450a0b540140c03041010a07039000c0b03560340065200740142d000003014407010001801c8100c2601c0c40c0140c4000030320b120212580240411508214002d4070709c0400d92601201920324003410489208081240b1040ca920703400174032040b405100c500c43d103190344800c01100d03800105020f028940c0246800a04000e42c1c0c110403240d10312000c00394074000241054201d80701d01402031400d0100480340b001301c00301804d4548030f00d40c0d10040d20071030b9a0700710601507002c541c0c40c0c0000c0d000c9c840d02c10700e00081409034415021003198180c603820301c0d017042d050343c607400800c00007000100f640350400300002c100814070001040c051700442c0340221040c00c0000a030503c070340034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 843354073 1250 843352823 843352831
    0x30e07050a060c060e0d0804150501030215030a060b0a17010503060601020703140106182310060c020105070819021623131e0b0901030b04121110090c0503010203 71
    0x1191084505108003806a8203c1c03d03010310030040072401c00e0100ba02d0500700300c0080e0031040801c00403020320040144134291700c0070200030460104030561441e000a07544036140019a809103070000302041515007244c000030060442408060382d90b103140e1a00600c6000f0f03001403038008d01c0b0b990001107981d25010502c607004190590017480c69504586900010b02c6100351b61013170f19036071010002160340760442e007003410f6270042100082c02c840221000440c8280c5070460403500d11444100600c90307144c680d9440070342d40c0314608045208140d10040c0d039540314402e000746c1154804500c1c1070075a14a41c000c403031005810b41c299590000000d498017180091400340d0083c650110314000d0307850300110ba034807409120007030024146403040c1601c0c0c0100c1d41c0c90260b8641083c001001075402c1251030040b58103030032040c3da40d10030a6156840d05140c1000c064402400200c60041c040c40d568821460b40c3c80c1e5a07600801d50b1954041644c0744401848825400c03140042144030000c1d080c54184244d91003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 843355323 1250 843354073 843354079
    0x40b030a0201050307050c07091b020613110d0b040f030306060206040506010b0d1b0c02101d04020a1e020f060604020708090d2301150e0408160609021f030e0705 71
    0x1403014650300650360390700020005010414184100005c00104001d0503000b000600000154201691013060226030546425815584081c0c24440e40106c88030400300840d401881030029900c0400001b41c082c110080302801050b1881c05010501c014940b0f5082c280740302c0d0702c04020703842da6010b00381e0f00e1710022039018001e504003500412040d101c51000308000c4c0e21100d0f0009011107240084454002860000400501500250011400d03c5404100c50401500342001c1e1203844d010321000036454081424090340d00410f0310703a40300340540365081c00c0c40c2415180c03580144072031074000d507107024030040148503200b40c80c0800c0340c1e41010720031640c9050b0030a000307a152140041c02c0c801c001a00078000c56004418070f21050114001d026020440c151a00c00403801f0804a00c50b0030700f406881c3c00c088104440078042c800018456405c449014800150b503811803649418410700a102c003d0300a90041c0025041c0e440e4810317031240c103003c40c28580c2c404104400c02c4d0008140d98103102d01640d60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 843356573 1250 843355323 843355333
    0x102040f0f080d0c030c05120c06181605040b04090f0f0c09020f0910020a06230a11090d08070c06030603060e0c030705121c02010c1209020109120f0b07120b040b03 72
    0x10134413442e81c1c0e46d0030b240110121815809588008090f5600c94694850380b038001900344150745460400682903020781100600c44484943c1c80d00303030041740900c207003446a5566100c0188584441d00148440c0c0e03000310025442100381d00b8090b4202c900d814040f920f2007901350001c501e152452080e60059054000c646003481c03103040501002c603000d10559820f42c801c50b00b0844c0010301a0040610b001c04070400b40c568107050202600d0002c0380588199803590412028400070858138003507036074802c82142c141c0006540d50405442c14443d41802408150480b107001c40c5040c0c041e00210110784c4140d070704000c04524a8609500c0b0308043c0b00195150700110001c00191030021307178540003130452900b1b41e104502194401240301c409800c020000d41d447d14010416180c00c41406103140001000c02d21a455141e070000707008207007600420b410220302800c0c500c20b01c1040036441080c5ca5003e0700d00081070810400242c15000c40510640c15541043c42a02060034180201d10540340058005c2c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 843357823 1250 843356573 843356597
    0x703060e0c0a020f12040914190b12030c070e0703090c060f0e06041706061801290304110a12020102060103060902040e060f0106022b030b0f030102040f0f080d 70
    0xa1200e0b0700040e4164110700c5030708419030100782c00740700d81c1d805030000c1e40340365a42d5450710b401442030340c00382c0d200348400820640411440301855820340d0303100d003041d100004196041000045884030380071007014a900c0049500d4680c12000941e0394207071004120103040301d0b92a4242102910503002d00100581803c0c0000c010150160322482d0500b10035041ca00301c0541b00f9170200d2002c1d0043e90060704001d40803003040030004030603c4100e401c90340c1a10300e0224076014004d80c007503c44042c07044080301f011000410791100072008154081065074880e00b9982d00305410039080e42d020b440641441683c1080c000103400c14141c0c11001d0190741030700500140d80c40c0d5100c07800105400311090741c01c181c0721103e540454071f051191502c40c070449004030440e9410300c040286411317800d41149021080c41d56048409a2400d01c4440c000810b07485c2c0483c5012802d4040b420f5411410381c15a095070011a01150000030f002e10002a035807150032100581c0d83d80c0002d04d41c0d80454040c00030100f00310103009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 843359073 1250 843357823 843357841
    0x309040b01200102040302090a0c0c0308190509030c10020406020c09060a050604080f0f030a14070215030a0c02120403080306011d0916030b040501060e040915021801080703060e 78
    0x881000d610504080c0c0d00c101251a122400542440600d0416503001909004501d40f143d4080e81040f81e110041010401500c0007400d000101c1c14041d0500514000041c1448041ca003560003000300c0c408144506d05016001565075040052030744a0350141c610a005410000d02c20340d000c45101b0b44c020081462520140070040d20017406854100d4120319000c1100c1d11004002c1c8010694080206400c0c020345040904210101c001d104c890b400400507486c0065000e0301e80f9803114009004c01c2d0b0f80301d080c1d2002400c001d510b488001801c10000c8200400604280d02c8020000541d40a850714515207031410009032145001c010010003081c400701d0540e500c945800240408045400e801004c4074a00140d40b0000440b0034221800030420900c0040b0350501449034003120584091082e0f5042803006031484140041e0a801560369215003024401e040428141e540d01c440700455807003500403107044c1740c175907610211400325103000701040b50f0500c070781700d024204c3d5074141c40300c1c1070b946030300e040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 843360323 1250 843359073 843359081
    0x1b0a0f0209070c05251203080609281107020301050106091a040b12060a0f0f0906051c02120a06090804050925030908310501050928030c09020c0c040e030904 69
    0x508481c2c01700c0080443e1400010910184150194503640c506207080d90400420560003030240810208040342034030781026140c401e121301c40921102050082e20404201c243c1e01583c20080e5040d824040000780d1203801034044000e50344500c51400c141035a031082e11000303120700d00c1144c0c032500c020001080018481940c0e00e4101a005061000b6141c0d40c000d00107540980380c020000402c1c40980811503a46103205900091070142c2e00303501b40030300951000c0d400f4081040c0203800b40a48910f00411085c0910004016035801802089480464117055500303411038061203000390541c00120b2150074104900050220905404070006206280210b0107003106040846081006001c0083d2981d204161412040045900c0c04081111101c041d40380e0ba0041e4092030500c00308000101085e03d42280c614004490103202e021440551443d14504070f0959101400440a0380404120380c429a0000d26846600c041102d0060030343d03008010858000c00c01c2d1103860b500c00c1000f1501742c18207801c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 843361573 1250 843360323 843360373
    0x30e0612180705150a090510080a0c0e04060909050c19060e0d0803160905040e0c0d02060c0604080c010b09060d151512050f0d0e061b0a0f0209070c05 66
    0x20940b05642d50b1000881c2c40f907a41080502c030f00c040b02180300c41e400c59001544900400c800c85100409240c021000391184201400c5c03205070301e40b5101e041ea4924025480c06507105009441003008641e10a155401032a032600115135a015a054121462420800342018041c070f0405010a5034074103a02500e6010003490030a0300324820b000824080346685c0f000c0c511500c44207920441c010411b001c01008c089160f040035200710301d0007220302c0340b8100008858501c03003c1560000d03100c0c1440c0c000250755005100402c15140702d100c007080200082c2c98007030040390600d5402800740f82e260708208918088201c1e42c00c0e82183c940000c10002c944401c50203042c1910078000000c03164487e80305e83c0c244200c140c00400c00c800340000c3c24420020f04000100450607a00042c0a04e210201c1004080c05190305e51316100301d002194900144032040080350b51075000c03000311074406005182c914441c0c1000359080e4429a0000700103000701d805000d2400d4061790020152210324200c040110354568250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 843362823 1250 843361573 843361621
    0x809060d090b011215060303120f090501090501140f06030319122a020f0c060703090b07200303090904080d0b06030a1a06070c0b0d0f05040b04030e0612 67
    0x5000d103020400b4100400d0207010b203018800c12003407090504001602e851000150a0703803500c00200040703503024500e02081e141407400842d000300b0050341440505020800a07055518001e00c240c01c114056208802d101075901481c07d0a666440c05101e01c00000c40c1d640d40c00d90401c021070000d8060030b0b8007003c0c07404414245a01e00c99505215001140c2060b060114034051564091580000141001c2401c80044c4018500810141c102645442c165002e150162502250700e404041c0542c00407800780c6020165942c944502c3d040c441d10800805440f1501c1c0c0c0051010300b095801c000c41103e2050b24040c1410406881e80c0e80e07844c8035580000b4005042e40d54840700006141d0b12580114000c440300780e000b00f030004c1c01c4400c1c020440350702d003015440740c00300304150b42c0002e10860b0780e0f0003210700b488a41d0361203500c80201e02c0b01415520428159841c41d01042000700040315032503d011748e01a90316045842000c02c2406550701c1545801400c031604240000c0d2800707004070361000d010b84d0390 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 843364073 1250 843362823 843362831
    0x303030c030e0a0c1a130e0907230f0105030105010c0f020303190309020f0910031515121a011d1504050c07030f0206011a0c1c110106050a030809060d 66
    0x1102d000c1c208044141c01312584c1d0481001002000c20004113240100704410000d450602c1a8115402e00030740340c42646001c071180030008500e00d50501c000c00042c0707a9440031504001460801c45c0c45111800c4500b44241d0071074a40e07080179481a4180c0b81a02d4068442c003240c040c40c0d4541814441010301c00300d9044c070080185014441c0c081f903800c81941c8c1103840c01b04400d1050301c10050700c00c404604150250807204200144c0c4103081c4200001c690f0000c102c44500f10a10700c003100074168208507004080355441700098003007180c8001100c290300403034408203c1003c03800d0034100c184081c40342070362000445e09001c100c0110340e41042c1e0803c03000501f0a1945039210080340c00c1e02d40454207802c004d18046010310070f03d908040822100e04d41440079180c80d41c1000503c000c1e00000a011120000c008148400f50340300c108100400501c42001080158601d40c000514454200d400003805500300003002031581806404c100517268080c1d000c0c0e061020120501c03081d0b0304002000c0d940b50340c031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 843365323 1250 843364073 843364091
    0xe0f07050315100f091514220f051206010605030601030e010e0d03021c020f07060506010e090a060611010504150203130c090615050c1e031b0f0d020a08040303030c03 73
    0x3464800f4140c104460311440303100040d0450142018140e50700100202c80c41d2141001c8241d4404c0c49158141d100d480c6858031038200d10310443c61071405800c4101c100c1c0244201140718406042d80004464048851006040b60700c003642ea29001c0070311494000c5070081c00890b2583d07003c0d0300301c407585d0303240d003400080c01c0c0c814070751901d04e440e00a200c05004241c2c000344d9194100d6224412070142d0494140039454003280c011003040340e12034407202501c000e544202265240e07200d00504500c18600900c100601c0c1001346251004180c0c0d84180d1000c07aaa2504980040381c040c054284556000b61100000c098000161000fa51000703204ac08420041c440a00c001510310804401070224520000b0b407045c2006116402e2894043c0d400060000a00610034902e600003650785d102c5005a804000809200ac2c280b455802034008200e0b00030524231000d12444000244001c0d21009203003140d00e06910000180e0300c2e00700080c006011900c0400c0203001190286c0c001e2100b203840c910300042c0c4446 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 843366573 1250 843365323 843365329
    0x50114071506050f0a1203030b061209060f060114040902030411090a0207050706140d090204060b180a060813030509150406020609061030120908070e0f07050315 71
    0x10884210803001a6a82c0c0103000314204135845621161060311442c0c0ca084c00d1403511000400300c46002410107850700b1041e02c8680358074094a811004092000749542020700f0742c151203040480341110580000400100250701c00d40d00300d0b0500c0350b400381c02031030310341000c0c01e510181d48010415500003284421300390040e00d074401000d2048464510041e00d59055262a505100551b40244104460380c001099000b260790110b6141100c09100010303540514030200300074003070036400719601c01000302d1400321000c4600250303009841c00301d076800c000c3d9455203400d40c1c08541c05d80d1003d0715240c203400c01d440080d01400080003188402800c1c10b001020107420b51074140d1150300614010f8000740f0074001d11000801c22a50001c0c11742540c404a20708001c6504428101400000d00c1040409848171030658440a000c00750340c0c20441105030040e804001030100d0090b403140200b1881342c541b000407055585810540101804405591241c03100002140c0c83e2300054950100c0030100400c520407a0713 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 843367823 1250 843366573 843366593
    0x60a170316050d02071d011202190b13050402281803080c010b010e030d0f05070c1d0114061204031b0311071d060d080415020303061c03020705011407 66
    0x14460b00041000304210b903c02814080107070b00c0a140c515181641d00d40820b841032030141560f409202900300c01c0f09900004a1040341890080b8075400c54075004100c10f501e400040103034804002c00101c0040d9500c040c8800c0307114034000701395444485408003038074601c00041d0200750314541c1760000c0822607403d002c2042040683c822a0002c40005a00c040715400b17004080c0044824203060900d003a4500210b51a2141e0a002c2001c2150307000d024002680a030082c1d075a1aa0080d10000300300c0c0d02c5030b502c404d00d0036040c05045c107104074007000065440d041010703d4074050000b606076420910741800002c0541400b4008a0a0080701c1046690004040c001724108038000d660310301c001c5510304543d500303004d05500b00480039031160405020800540e07040d43d40040050b603100181560a0924203064000d40c1c01000c1c80040070010905041d81c000065400741d00100c5403d50012801003401c1c040740120740008016070030640c0100700a40c050007182c00b40d80d4140c008989008115a1036007509 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 843369073 1250 843367823 843367867
    0x4150c03020702040e01050925170d090806040816080702130506011103070b1603021b0f01060b091f030221100506070c0e06010302090909010b010806030303060a1703 73
    0x81d0302140503000e51501d030246107080d41d4510020401e034100580000c0e02c400c040400d1180c00e0b061445107203208a2000000001007054240340c1d40d000c1404903102c3c0d120712880442000080c9200400f00d80c100f400f040890155600040451070715092014007001c481002e01c0646600c00244100009a21482c10780d844a141481d030019640c42c10f0000075001c9030007102c80c4001544148117480000c0e0445942d030350042c4080302c182420981d94101200a84109040030158011181c0588101000080ca038400c0544500090140d203884a044074140c0c00360b180c0c034551054101100590760344810b00300030383c16282c0303190240c9420116020141e01c55482400e145003070744a0000c1050129041c2d8004024042c03c40340c60740340c09002c2d101e0710040d0711180207481c00d1500040c08650b0326070203541110310a00010b000210240341c00403c0e030303000380388289916012482d0540001c8691034040200ca01c1410020304501e141820010414039010740703840302c6081c9100c204840800a40014032522031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 843370323 1250 843369073 843369077
    0x3030c0510060306021b060c1c11040303050d0b040209060a030b0d17040f1a091002250510090f1406070204020f0301080f030304020d08090d0b15010f09030209040b04150c 75
    0x41d443c0810f00c2c6c154a803131282445446c1c0d4004409202c90f056803501181d0802102c03204003401000080702ca8002419001c1e98a004042c001034004201034009010300402c1b00342c500701b0407800301382806100a82c4560200954002000c1120300c0b046806984040d152030030240c00400131034403030354801240504180034035200e6403001c90100040d020140c032030070240c214001080e00c51207160f140c1c031031240955000b5501c98004050b113042424400c0260009200215151169aa406c502d403000490b0f924007649000e54403000300416014094010b40d4103da1800442641840c030384590030342203c0a0b1142c081e4420401c21034900507175510300140c8408001201c8007541ca5142040207403410016982c0e400c45608180200009a903036602c603071600940102d04944e4601c624000a015141c000300c006081d4481c18007030085c0b03101c8080640d6000380d030a8032a48003210301c0307460a0715503100340c1c03000941c000c2c1c41d40009000100c074141e5072a00148a220240031400c070080c260030503180700d0014080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 843371573 1250 843370323 843370327
    0xb190312080702100c0e15090d0602070f0812010303090611060106050a020708120a170c2709041101180320030f0d1809020304020d06050c092205180703030c051006030602 75
    0x80c04d450487c1c2c07042525504c07080c1c1c980c5002c1c580030100b0f5441c0240000500619402305116062045180714141d405911126265030355114010600c6100340038082a400214045404903169004c1c2e100b000c40071072202d0003003100740c2c640b50080722558000102c0c00210301485a00082031001045140c0380006080000d40c1c0702c0c03504040c020040c2110b4190300b050a1b820000b4044014103040441d00b804214150015100c0307040000d00364049412000c00342c00c13030a142d00300310900c0302100f13502031315220036030f035140c180b51070461031803001d4a0900001d0f102060b5000000c0c08800342d641034010308071015054484c2c4c040030101d03690034404014031010100f011555079170029030b00d000c0c5a4000d04130f903620440c15400c064002c9240881d003403000a00c01507881e00415400c00c107107016a880130340c0081a04030042000840b2486090040104041541c10100030032280c21000502d20316607441000188012440d58a00b111000f10003902904c843c044e8041c21880261240138800255006031070150b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 843372823 1250 843371573 843371597
    0x21e030711010206040c0e070903020a081c0305100501031805061906060906080c09040e01050a0207031214060105070303110d020315030c1003150b0d0b190312080702100c 75
    0xa8220207039800c4035045420100800001441e984002001c0e00c1c6505002051540c84030b509592004403600060750040c441c4000080803440010540f485029600d07688800412a0b102035064503401e681e00c401c01001041c003489154401d61244602c51000d01d0075550000b1a030700d4490a0a2007070b07859440c1e0152500c3d40c42071361005400b941c03009080f1454260151f525080c8010032100c400750207192959030003d01c0241c02d58998000040264800c07008011034101005034000079880650114003080c3c3d41c08540c0c114990501c0b6031041100348402410055460100440d01c0b50301500d8100d05155a4030071580b944032400000d0f203140003001500680c6c80c03d00c8055400028040d6004500c03d07400048022200d45401800101c80480c905022032203003a583e49217880d50050341c012114080c17001c01e003000900c50a80111800040c10f03900b6152810b00340b2070840c2c007245140405810080301c1004401c80070310815880d94010200d1040d9500000c111481a094170810500400002c0e9074441d54 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 843374073 1250 843372823 843372833
    0x11505040510080711160b0313050f03040915120b040203030d020301120b0903072003191101081807061d0d0b0405060c0c060a1104080d080109050a05061e01021e0307 73
    0x80030310028010024081101061a42400c100040c01031f6104001d0101c0440d40c00107141c00d60000e415071005c00d56030351241c1146801c0d81ca8000e4824400614242140001c05506500b480740a03690062034504142e44c032512283d8a101d0007400c2260148410018401d01000c0c5101031030103813500c0c07030345064000150b080100001c0c1d805001c010340c0350010401200020f00c2d01002c0041913004544072400620b01c44006810041c10800303820154070f000315880d0802c203071510340401191098840e8001c0380c444c4510321100e1200e5170980300850b4000c2009000c414080c1a050b200e0964019070144142c02e15070204070084080d0000f115905010340038002000018001c0b617078460313030141e800340c18000c0c1109116074448002d8149100c4a5440d961040040c442c1000c030750181c8140b00c1118ac0071441c080c8000e00c229001d20500519901c0c04021400d00314890040324042d0400030f140382060010064400c1040d8491308400b410b600c00e141c00e410720f40300c00003104800d1040c82c0d0b01941c0c90300401e040c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 843375323 1250 843374073 843374087
    0x2703050105010b0c0a020405040c0503120904050a06180504020f210606121e0a06060b0316020a031403060a051f111c080405030c0304030f060b0f01080115050405100807 74
    0x44440002130003200c210280010b070078603045030100c5004c0f40c0741d01c3c1c606144090f41402d81000340c060041c05015078500310a42d000b03210090b01a1000c00503651036034401e03000c0394443e000e08412410006078034040d511494022a800c80d000400e14140c034010f4900003000b0300078503100041025414030604210704024010b50394440381c140c07100006107a1144c422030301c408103c0c5241c0c201030b00d030300410b02d030552042243c03403901944050708224060300d0300991200c0341c100300c44101412098004142a0900c00319210700c01c107030b1680b948481d01000303401584081d0401807001e0b80010f43c800000980e962115003582c040c610703107c0001c0559980c000010210307480c43c0050410341d070040707080c64000014520403500c914401e00d4052995141c3d0b02d402402e500c40c840d05505544004540070061018031400c42d9070b601d100d18010489404940d0a119020b2011141e0a01183e280001003088505102d8034200440305454924500780c0c40d00000341020410f00006000101024200002c0c40d4120203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 843376573 1250 843375323 843375329
    0x5070b070f080310081b13142d040f020a0b040303050313020d1221020f0901030c18030506070801060e13020904141e0702060118091712040b1003051507270305010501 73
    0x141c00c0c840c82d15403945003092340e040a41a11361088510211030380722100d1148160400401d18500c583e0350606080c408409a81810103034440c0c0e44644002503058001021641200c0c2c0c952103080c2941d4481e418440d1008400c94242d070082031456804002131809803c1c1a00e00700240c440c0250340407282c00c006014444414048640743c4100706000d200d44180d01a0f400058003483e0105e884000034070100c8480f0500e807850b002240170800084100600807518504c6000255110440c5a0b0b1f642021611360f0404680c89401c00140d4003d600c1342d0005400501d180d51001c0c0001c5607000781071102ca000c080044600c603a03215240503040c21400130080708550402d0b0070344000e050035414000034211541540c85000f03240c1d9600e96140301080340101c0300034480042c00300303100e40341e241e14600041c003d14102c034102c03566a070711000030750360080c4100141e082d80e400c94000c5c0901d9081d20119402e040300036016005100210040700d038a4202d074820118102c460341a9044101e00d03518180b4203440043e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 843377823 1250 843376573 843376609
    0x903020f0c0604060e150c1b100309031706061b011a010503060a230d110102010b01031b111c180e04110d021201150305070b070f080310081b 62
    0x1204000241d40505c400c2603d61040306c1502d105000200c0607002441150072004941c001c00c44101412180354121101010781a2011401ca800010044040301c04900d8010089418144080d0300740505601c6c2c00c0d4098800f8080754074040c080d10358000701080154103441c40e03030345071314442e032404107040810010313000c081c28190b003075040203000901c024915002c1c2d0040317141c0201c2c4940142c01415580144040040d01040d80c20100e4204612502e003d104c28a0140d070900d0111011544a07104100c21800402e070800704e0f208045030221040340006810041381c0c49424011040d1040702200303c1c0d030f0b200307940e01da0407800400000d82200103002940b000c1394100340d20003000003007444060018051001203c078450814800d02c0015034400c420069120301d503280c51140318440103031032005000d8a00440890f5513075070355100050f602c5e2054940081c00150f03991003000000f0702d04c10140d42c010140304030740150b464440540750300e4000805c240050b00710a0400d1502181003201126241c107240e5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 843379073 1250 843377823 843377827
    0x20c0a0302160b0334050403060e06160c080403020405010f0e010608160f030e070e06040f2c07030b0a0522020a1404061802030405010c080906010510120903020f0c06 73
    0x8104000c54074000140700b880a00b001703154455a25000501c4020300c890b03c0d01c01118001d98455004026400a0008403005498852008640d2000043d090f00c21580802304891071400f05404a8507151101e404455000b020b1001200507527130f9026940c0680412031407c50414079088056100c144182e101070300303000c0040d003446600068181c0b4608071030800c2c10800d2440c21200380403001464a82100c1409005180c0013042207038500c849a40a0902254144016a80c1c5d846281c1100c5200003003003540da1090344001d0f40d40c111000c2c1c00d10440310910645250540c1d23a1180d0b01c0c6200101c5940d008640d560003088081c1049500010650000068100c11a400742e80450020b0780d0034011104450b0890042c1103140c3d4880e0001c0740603007907580d0032810740791041413540040c1d0003da030102ca6950030aa030841e5403610902c140b600c2104601c0003001c060340f82c002032180e5030f900f01024800f013160038003801100a06900034074051900c65401010103401901c00c1c0c50625100041031881403000b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 843380323 1250 843379073 843379079
    0x5010f15150813151b02070506031f050a0305010c080f060d0b0a021c02071101180909080706140708060906010c080c03070f0c0311060405060d020715020c0a030216 72
    0x100c81c0e074080d011070385402c0c0010310b611030520303039181c0008102c0001d1543c500c0c4c8060b0b124800490300305217103d4410703001c020045036041c4d40690b1691001c0c01103580102050000074041c000313031103012920912203818403480703030740358404108040b0725a00251807a0307440b81031340f0604035802301c600c079484400d410007600c090500f40002400d084403030101819518070317040401ca1b0340c001ca5048680c0d440011050221a1110130044c9000c0d40000038103a9000c2ea200c0e4009159500480701c3c10080c151a05840741c20508085006000300341c015810389a125081c001c07403000400324070401c01c80b41000001e9000d07518200c8001052340d40d00a0503079004a071510180500b590b0010002406598406842500c892849a40500d07500854034003a0516040d41d81800a12400300c055405481c00f41c482c04000a80030000d0080d14070440c4169904101c08001d03403000c0010b5640079191040c42103580b02c1c200d1785034150200076038100d501d100416401074003c4604050b0104905100484a0210007200e980303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 843381573 1250 843380323 843380339
    0x7031b03090e180f0708240112061509050f0612060a020a1b060903080903040302014109010e0117070e0109181d0c0f220203010305010f15 61
    0x1445210001c04120001c0382c401e01401da0900c242510b450221100d00e04e02038406541c9110510800d07046004802e189580c40b00c50080da0442404a9209040c00340d20700b0050842066010500760345c001d44c1c910480c1032070908051003100502c12007002003114104070b0344520b541c050143c0441d22070703040c542050030303481808640c00b0760007040d02100603202c800c00d0500384c0d056460080c10380000c98a1540180c1080f6182d40702070040c0e4000e50315840c050303981d00b481c2a543d02c00c074000607020031041c89601c41c480d14189032100c100c03420905802e0002c480f00908082840611201c0000010080740381c4009582c052175442d10107100746042d0b10014280c203000c00e06800b01904500070420501310504499008640138001800c0869107841041560382e40240100512042c411480c40c052031243c1c01c18a00082c217031403d14004000018042d40760382000102da10400001c2500810004036070f02c403e00a101442c002c5020b0b4002241345811039803001d044030004100c517020809103540078011381c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 843382823 1250 843381573 843381587
    0x314030403020f041401050f0402040b0301080313081912050c0102030a0903080a021e0306010c170a03050c12180c0307030c0312080f0a0c12020a030e1006080309040203040c0b04080307031b03 84
    0x10016942300e500600c8600103e8003900c05c54204100c51600040000752103400007004000000201056107000f90702d0b8004191910705550401503040340550590700411030554407107442d8880303810542d1611802c1e440381d5081e41c00c00c41d082038019640c1d644070001c0c181c1042442d503010003d000d04515282d02c01a54601c00e0040341fa1142d03200c0c1c004800100f40c1d9000c5d40d6541202a0081c25444042c2e459480784071982d48200002030000f810722021443c00c0800d44151031b038902410080c82c41580c1d078000c01c000301a0102006100384c2c41402c52030200f645052014070007442c0140c4031244164214184500b07060300781e1007554200400c02d030800c07807010100141d040c0c001c2442800811610b446860889040241003c91051148001001942c00e90140d2100324002000f105817061040008000c1c011036050b40700e55170903908200017845143c5070640c000c0d6440782c4101a6102000c0c0c681d044040c05411035041100140d01c0026841d0034181c000464141801c501200e503030304c08005550003030402c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 843384073 1250 843382823 843382829
    0x30906011514070f33060e0c1e031f0f03050c09070c020406150305070e0f040c09080a030305071409060915070615170f0a02190314030403020f041401 66
    0x2d140003141c440c04004110b9032003030b4801e42121900a030030781e144500010390380c0c1292450a181e150409100c002d41e880d0b000318021501c002c00511280d40d1840c0000e04e080c0d021010404a82d010820640d00442000c0091406010819110700105400e04050121400b064200f10300861204004000051000480c0d1030a282e0503074034000180c40d09102035504000a040003548a4104000400d0204032030307614844041c074a42d414025500d80c00b106884480c0d101881640046030392059190781d040a030416042c1088038174049501c01e82ea000f40e1803c4c40702e0080210000303600d44043c00310555001e800e400b025002c41c81094900f404150028000d440f07012162400307001100c031680b00c1c0c040d4440c242d811541d0040014131441e402d1484d0003402d591140038000c42041818400c01203d60006040c81001c2c80c040000c00d02c1b6a440d03000c07c01134a48172102c50352500c003010b00200000d205940c207209602100c400079500c0d1420740c4100400b03411402c0115015030307d064504a440380d110203c007411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 843385323 1250 843384073 843384107
    0x1050f0d030215011203080105061c050c0909090703020103050603120d0b060405040e070806130503070f110a0f0501080c07081e041a0d0506060903071a1306050309060115 75
    0xd46900c516040e8105100c41d803509852220340700000a10700421101e8040040c030039919005103a80344c004000490080110070044c2c1440300c1c0d481a6646c0035136024541040c03104480e9414070b070190002a04400302110f400f4a25003214a0070030440d60107004007600140114003803c42404c115035041c6840c06005a0400f200c0d880e850411a40d8803074404a03009488090010f001c46142484401e41d01c2940340b2070509640315101c0000c80014081c00c070300c52a554048040c5240000310b4652403805141c141e000e40b80a014450415016680c0f850f00c44000c1103420784142c5a5440e08002400c07901c001080d083d00000700700078620000d407803a030443d500350300544d2200d960a2140484a140c6006a41101c1c0a00903026142c250b900306030000f030031610005000901c203030b03503d010510000d03000d10424240c059010719030a020240c03001240c00014945100321604102c2c00d000159414002940840c0c085400082804800d003814130990380545241d845890701002c00881c002d04806c440210051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 843386573 1250 843385323 843385339
    0xa03050a050d09140a170f07031d040501080a05070803071e0f021003020405270f0703090602030a1e15170f1506120604080301171603120905040501050f 67
    0xd8108040c0d101600c0284c0140c802e0132183c1080c00410340c0d681c03940105882c40c1a0726042c030414407480d18211040c0030416034030182801000c0c1d8064503030003020100d00100403040003141400c4c0e151440303240c0c0240f0102d0020618120755007421410400b254001d000e13150802c0101c280400d40c2c0b07410310f11003076058803c1c6591181907414103080071440c0740002075101c9100c2541403580d541c55000741060b0740017241c00070b2a00480368001c0c143e4600ca008003030403c460180c0000d11040010720442e6001d8410308021a40000954405040303a10841c0e4088240c0c0c1e459506400800e40000510303003503400e279002000b02040c9005001d000300c4851045025943c0345550310310305000d00340400d64183c0c605a00b2500048040f03d01c407192a81c0c21584540551600c5c3c000209189000805600507a0030a640a140d40d0a040c1e42002241001d45400c030180310381d10003425140015000c0400031400381d464200980400c1c1c800810300c2c0000d510552245041000500c225541d8404908264100b11403102c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 843387823 1250 843386573 843386587
    0xa11040302092e050f01080613050601050717040306051f03020913021908250b18060a020a0209090d021506040912020706122f04080d050702040e0a03050a05 69
    0x183e4481c40f2140c19003041c10002030b0b2403008010601c50641a50012100b0701560301150004441e8003001700c1c0d03560b61105020601a6820000b5404942c0040041c07412510300380043e191440c000328480c10400300148005410402d202d40c40c403555401c001715030409001880001c60454072031070540000781c40341425070041440e62958611180400360f0141003004800e409141800116405205100c1c25015003420191080004082400c654000707000710b010080c00d041c403107e81c4d45c001c2e5201d40e07416416000a04040d6a80002601000e0210740c01441c00030090310502044002c060074880040d8131850701031030700d070341c010a08041c4400d00721902ca84a664000000d00a442c6084010b00001c0310184101019a40456640c0c00e03180d49440e002d681100c180b071040e0441d0b019a05501c10110500214031200f401c000c00d00e146617405801440c1801d46441156040030024083d802c0464000280e07c0114100342c0a9003800c0c10340c0c07401800ba0340c01c40b5180600a40706460b00078003040400203585d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 843389073 1250 843387823 843387841
    0x10302030412110c041107020f0904020604231e040606051606020315040e0a061401301539081305010f0507030506030703170c0106051005040e0a1104030209 69
    0x10b0410440081c0280502030a084901c040e50748281c7d0168021a5039441d03083d45802d0043c0310a0113030368090043ca150a10b08008403078201903500e0640c41150a2544688582e0b56401f0030021180030b128806205544800820003150340f1684100c0c01c2c490144140c0c20740c07441c4604041c0304180c001c10003507960f6070740c2884c4c4c181285401d62910f03486490314018040001e80012009102840380000b00f0404540182002c52000b003446071203950030501c01c3e59a800b918601100006040c0c0c081001c0005178a170350b8003910f0450084011171001e80d146004c124442c4d810b40511990608241d100400d1010311341c8504039101c88a48400900800502081201051056410b1f0a5410800070804001d0058500024240540701800064105000718246203008142d56080784d034824040d42d174012003591415601d400210104440b95a10000010261a060107504807100b4039a680d030341d51801c07d10188149280580720000a602d0200840b121141c40011a0156034048840d415143c0d610009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 843390323 1250 843389073 843389083
    0x10c0c03140c0c10080103050717060601030b060c1c090504050f010611070b0f041a0a020a0b0703061d040501060b0c0c060f160c08010e031c090201090e070c03020c01030203041211 79
    0xc980d40001c070354401d1308600c2d0b62000e402d40c103882c41401500d044590300c0c90340900b40040003004035a10340081c80444c01c0f941c003d40c0410601c030006003a080c10040e419a055060510607529080000c012400f4501d09960204500000d008102d4040209041c40f52010041900501503c0e003400450707107480b41c3c1d5603c00c0040704010144140b01355610404001409580e80082c0b013000c1180d4022581c102da0042d44206841c048441603005042181040d01c447c00d810b00e000d03180c0c405050b503c15000ca5103400500514011840d2582400903a050038a4820f0854082c0e91120004800c18000141c01d0740000c03500026a510884245480e421a991071802e288640101089201400c03282101000b140d6422101220141c0c0c0c02040390a0317400c038a480c1c50384940310904441041011005201c50080c1c0d000305446801890107400c565101c001000e0565015a42a008109049411020150f040100142e156001c1ca015400d50906035908004000060980d038288400c01342100390001c41008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 843391573 1250 843390323 843390343
    0x1005040c031b030212010c0903020f031203010b040501090b0a120c051c020415031514041103180c1e0103150b0a05030a0c021207030c11060315040f05010f031502040803070b010602010c0c03140c 85
    0x20002c0ced83e541d4403080892180d00c68400e2a004c00c19035840000c0c40070104d0705440400ca6651a00303002c80036081503440c006e006031001081402018081020b4486038515420302c1c03e90600740040e669820613004481000240300850205410039450f43c16480a40400d28120741d810b0620311900b1442c03a00007006800000b241e09010380001c010070407050203030a40d0900900900701500d07020003203032041c0031060006801c403d00042e0b005c10410800d51185d0f00c521111220294030a0545848003000407191388003021000000d1408404c5c001100340380d01c24940318803a580024188100c2650b00d80c105070007214400f905200c0203c0654052021402c00403020030001054240c2e286846403030b8508568081107100d00441c98085202a00c105c50b200380f40c140c48804c500c4810032880c44da580340d042d542c00c0c011a10a00d400380000900e50400300054400c01e44070f1402c002203907050450090854030805400020041140080703000b20760400c401da40f41901c01d0503401d55400d55044001c0c6080c403001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 843392823 1250 843391573 843391603
    0x4061409060d09030e090f011e0306022a071508042603070f090e0c0703050d05040305280c020906120304080604050705010507051005040c031b030212010c0903020f03 73
    0x6041902c44100394880304000d4866214117101154520502200c10340c00c0b92480358498038080103005e41d09034941c41480c042c0c454000d80b1620398907951020284e800c4a804502690b00790361010306050318855912114060803001080003600d0040044034089400701d0a106000500000c50103000350202c1c0c0003900c805e55145918405403c4140d00e0059104031180000107104080d191005c40c440c181e014112043c041d0544800d45401000c80f2566000403022424400708015010b02d4210700c0c007485114038061b032107440d00c40d240ca2040c0000c454030360b00c070491101d107440700d083c001d150031203c0d00140e50b4064401001c41e0340e4550104030756000031600000030f4840441d0010b107055000400783c0c801c81c400c20a5515181d41c0b0401520207004918008019401c4403241082d01841640510f030300500a0201114990780d907164907a407402c6054828000351a0000c3c00e10a605069048031016031008000f0048041c1d0b0311030042000c042d03400000d204050260000c1c0069030300304180c8030303681602 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 843394073 1250 843392823 843392827
    0x4091a09060109110a080c0c071a07150b090f09030c030408160e010803190e12010c030b09060d02040b0a031205130e040b040303020306031f0b03060117030406140906 73
    0x4140e009566040912803411450304140300c05950a50800130b403a80904a511590715030385401d408803002e50805118900345110b244000200030310000300c040750000d1005c070b0860380c4100c9820900071981800d060700c9070310360402140041503246c190150340c0c051000c0d0714902043d1541c54102d0f0a610403402024820f110214002c0345440b4041440d60a04036240070b60000155141400c0403070242c244901b82c2590400e0040c80d1607103403030b4a0f41e42c1100340c2030300c0c00c2202c03000984002240c070701b0344807100c00c11a07542c2c031801484a038041c8103c118000040304d41e880d29150000004500d10400c0000900540d203448640d4011b480300d030680f00141d58040c40d5450840c1920400414940040b02104804070300d000c400140e0505460903580036a4200c211864540e440f078405401943c8050032042d050b03c2150014410b22152440107000e074110346001061851845003010f241900c180c1207542036a40e2101142d01c5500000125011200103042200503402d555038040c070a80140d1142980010b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 843395323 1250 843394073 843394081
    0x40213030b0c0904050f0408030f0406020d0c050703230307050c01020403080d051015021506190305012306030d031e06030506012409030b09100f020310080d02030904091a 75
    0x1001c083d000c445000e8408024a41ea00701c90403003c42816a0040d0090a080011451000d03591002580c40f80c080c440141c80c021000800b04c0c2150342e145000c00c0002e1010801900305640042c2100c00710303c90440c40174041c038452954114a00c0094220360500c1000036800d0302e1500300790161001507401002c240d45175a20540d6a00c060032040380c02000407100500085801c18452960000318443ea50080c070b80c1c810a1f20b0b40980303250003c2c1840d0b5220b008421003200ea602c01781d5100000d103109074001b0903000b02040040b020086841c80c10003003220b501d010010680c0300059680c120102c0f17468080340c001000c0f5a00360305c05034010700d195200d5080803c04000d1283c00605c1c14101d45100500c040c1c64060b00800b0721a4407041c3d4815000562009002c0000c00e45083d241604000001d0981d0800042106102c04990640c140915a03030f40100070022070324400320940d4001d003204009400c4200e2300c1c0d10000d44a2140c61101446103a6400e446014002d000360210117444207103c4841039414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 843396573 1250 843395323 843395341
    0x9150118080318151908101205010b03060a0902090a0f140a09051209010c06050a060504090b01080705060403020a17100e0f100b0f0f0f04020a0c1101031a040213030b 73
    0xd101000d0501509406500c604c401000001705d400e1292024441131364103900032170403503490320041c2411414164200010a4003a50742004105c41481383c5d00006490308100280350402d2001400c0b004070901d4034008034050f8440c11510303613005402520010b5904a03981d00c0f4401068001003071490b40d40ea510400014601c2036001c0003074136000d8003c68001e07204455142c8018813400000c140080c00c3c02c1d48110003c0e04542101742c00480e410310114106440d030780071a00321050b40f10151450702003900100050741d070500c03030100a8a016070303441d858582980c002c41c10681c5540f0404a0101c5014080700c118101480900a0044030000610400d000000700300c1c1e460000070004240ba000d020980210304140f0f105020070103a000e0010740c0c40e040301204120f5551481c82c80940c01c83c0009035400342d95600c0d80300801c00c848880c1c03070314407208485080244403014250030f25810316103012003050060188c0f88036404d590300100c0e80580c0e940c40003e00820007151540c0018460400e000610031015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 843397823 1250 843396573 843396607
    0x1020a030e01154223040b090a1a18101b0609050312091615050708040b030a200f071709040c050a0e04090c05012a0804090b091501180803 61
    0xc050b951090368030b882c1007001e178101c070780105ca81858400c3c041208001024000c005011a501d000300b80744510b99131030b52251a0446041a101400a000911100e03070bc850840354410b120313000d640041c3c2460301020050708151280205501010030440d0900030000070ba040424450791040650380c807546902c0720404100f906641010b040c3c0036644141d0484c261032007400003142c0c503608400d000201218800d0b0345070f6211031002cad40c6030607017008089200d80d0400000e6014180d98a0b0000310000700f49040c4038514084183c03207290660403c1290b003c2411581641d0440303411030041d80070170310314160706140ca06c5488a85900300d030900b0030901c51550010702412841c00140c4440e0802c640d40d904010480f10340100041c00d9030359a58040c805544075920540c881e000d030084040b01c1c1c40010900b01d020752240c9074200c0b41a0000141800002001c0c0158148801c068549107602d003856540c0c000d4503551800210f0412486075035075850541e199043c00020407100095035a45c02010040c43c20701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 843399073 1250 843397823 843397949
    0x2301020d0b030f1507020c0d080a020f030703140310050d0b09012004030b070201090c03052a0904030f050f121b2a010204090e01020a030e0115 63
    0x10501d000a05122410082403040c0315010120150900311060b10203010304001c0a8211011445404425110b9440744400180220700880703401d0384404c1070600003840c009041c0030711480341c0c2003484081c0000b500101200340504c0c200704500d4a0356a01e02c1041d00c10780c6a54419a4444142040c550500028008040c0100d1020700240004280c04401c0f0104c3c105c5840081d00075681040200086a81060300e1600b0640d10300c00400c2c404a56118145c1c0d03c00030380c0040e00d0b00e8100581d2460702c2d402040340f102c40c40c005291982d029421980002d1030841c1c0041003e4140316114110040c035502c110100d4801c0340a1518681d200c1000c4400808604021035050700310036000010303015140044825203103410045070301c10528800d1402603884110701c8689200b541d40d000c0c040895110320340d020f100a1250351000041e12550a001e00071305580c51044e024816914203814000020151088641134441c901030088825a01c100301c01ca000d0604001e6a410802c40020344101c2d14040d2801284 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 843400323 1250 843399073 843399097
    0x20304050105061e09060a05150c010501080d050f0705160f03200d030c1e060c020c010e010912020f0306010306021e040509010302090c12070201020913110301030609230102 76
    0x11a955103024403900b441c00c0504d82e140000782e00120025440c0003c6070940c00980030700940981c560729070105800c4000e2841c5008400804241004812400d200340b83c0107162000081001c0fa41c120006030951180184410081030700007031200501c90f0030814992001d203080c8821b40c1d01595601012684031460004a900c2892401c0088065108032410a04904000e1002c0178030b0181d0303034080d9401901250115000180b000c040800c40e1400d010420a09019000100e034006d12410000c1c1840ca1720200181800008220760070a40d0740442c901040c3d4060700074114a21a0b20f00010b41c41403810071007144d040c8583c1001104000703054020f0440400a107480301000000c032143c17080a8000e83c003403c1c0e008005800100090316007881c1c0c583d0020449100c3c0c1d031601ea00e00d54112011401102c400700582e400181540c09400c202d456400316001c42c9008006070100380c84010350611041c80050012a2a4010310061050f41c401e007041c0051804c01c9100382a41c3ea083c41d038040d401c07441142030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 843401573 1250 843400323 843400331
    0xa0302030a090b12150a030f1a010602060403090312050f19022e090f02030a05060108060c0f0913020f040906030611031330020a060e010e0721150203040501 69
    0x20b500f651407020780760303152800c00c01c003195036440358091200c0e120020740040d07121991000020226044007100780130b43d802480085a020404010300c414494181e1090742150700c603504000100350300c05d1042080d640c1c406030040c1b205101000403192070050140340f0f44007042c00038a0011804420a82c3c61941a10381c0a4075a8407a0710008107a0800c0c0c00001807005480455016074001820b9205081c0c0318410341c000c0d00324881c1d40e00428940702845200f03c900ba4080c400601c4119000c100366503020940c014181c1c5001541b400c00d41c00e6009844c0394070b0290690355141c81ca01d60032a0181c1e4030040c1000d85140d00c039a0b80d80f5141b005484d41d07210a890091408042c220b0a81d220b200312442401c2c40584040c2e5940c5542e101c14411840140c5030f00c060006800203081815004800c0d45c00171100d40c0206005481824030300308403004001d92100302d030300d8050340070707000300011519200300c8208121482d00c059401c5d04500701c0040e6100000c1c03607044010190f541031015940030b14080c80c080c0c80200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 843402823 1250 843401573 843401579
    0xb06040603050a0b100516021903080309070503030c1b0604081c080702010b0618210106083d0906050c04031b320d24090201080c0c010e0a0302030a09 66
    0x1000320030f605e400310000344c02000912401c1c10309900703050440303102406040406241b2800c2040c59070b0300e5041114141000003d100c003009080042034081c05044018500d000d4440e00c4545c0d0340c109443d407921030080009035440b001e50f01d0206032002018008103554045a0006000d07520982803101900030502810100310250b105102d40c08420001030a040c0c41c0426002e00300c0750084041c046254400f180c03880c09034203040850301003840911000000f03d5103a040407225800e01c003010b88203c1e5904120304000d40c4540c401d02000c0c40c101640011503450900c06642403019006140001d00f06a06220621407400141d800507c00c40b2b005c0d41c1506440150702c0c030900c003103040074820342c0030108001198424a05400d080d80b480f00c00e02088041d51024040e02146020312094015204514010343e00704a03042c05407903045501c1c031096410050408240d0010341000d80240144550030800b04424181d504254006c01034111600b0407142000e40d2850025540d03480f4801e081c000802c140400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 843404073 1250 843402823 843402829
    0x30607030524010c15021b030c120f0706110f190e034c1a09100b134403090d050312130605060d020904060b03010b06040603050a0b 58
    0x1a994000b05940705121075086848001d8200300c065a0240400c2c1c1c20030414000c0103c680508514a8491010307503140c490f00d420321030624594800740c3c14808402c0044211201c0d842c42222429980003800040340d26558010500380c6c016039004c4001c02000140080c205d101e03100014030200d00e55a00d04c419425030170241502d58040f40140c107140040810803500310026010800c4100269075034511b80c0c4411020211000390703590480402c0b20f50750b0071103025030001c9011000104207099441340c5003401c11800c44480184c40c1d00c00c08000041c04200e41c11000104400c10300240003030708041d01002c4105104040005581290300b16651504005041c3e142c4d031500c925940c3c082c454040d50601004000740103200300545400c89a038042000500c0402001a80242c01469203080001514140d45400ba0481d131010f03100b00e101d211180348490050b41c0d02d040c40d0b035103e540500b000c5149444007010030b000d0164031001c1544402d01003808140320f9410740c41a4898a800c0a05200c07500542c5d0038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 843405323 1250 843404073 843404131
    0x90a0807180902011b02030c0307061206090608070e1302040f020a031512080906040b160c05010215060121050c0c1005010b0901140906040311010e0102010c091401020106050306070305 81
    0x207000c51150000400f005c407900d00c0103445280040e05030b0343e40c40c41d02c40009080c0740043e041440402e11a800c100c1d5460141e21448000e4414144200880c07400c01d01561b03640c0c285032042814103044034000611034103143c1071034620319a000c0d00c10f008003a10000500069001380040e8000030b482e080c203011510540c10961030841e42c0300c5030f40c00d01409041d120000b80d44d2003891010703000001000f0028440c64440003c00818042c10a0300d007600070180784c243c0c5081019444981154000b0007080400c89040b17180b030350007003801d00300690940c080001070400310b14070041d5501790500e404208081c4911000007800400411001e031040c00031440e280008555080c0100000080140b205151550282ca559000a076401c0713146820b2214210000394640c0c00740d08129440e81516850302515600100d081441506c00d0009006001102d4002040e5400510420702100b0781c0d001c4503400e60f4001c3d0b120a0103818040c06644103031510010103409481d041da00c028800e0f110103401e80c408032213244 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 843406573 1250 843405323 843405341
    0x609040c05040c030b0607060501031a0f0f1305070603150503070305031e12010803041814071b06050406141003050607050306011106070801060206060f01021c0302090a080718 77
    0x100020036800c0c141800001d00c0c141001c0d806055481506807916501c003400781924900c540800318817981140b1301a40c080c801c40d4051259018082c00380001010100000c1c3d51020020340d4000c5141d540a0b2800081061404060010301503031902040d080c1e07041d0030141c0a070740e405031484100d5945d00103041c0d13544498400038109030403c0c480d0f100d16064030181640800010600d450400604170070300c200903c0203a005410b65400003500300292001c0044140d04481d12480c1000038140c44098800080c4000348068108130b442a1071940d1010030711143d0741d60641044042110349400c0c40c0c010003c11081202510525034800065001c00c1000c2408043c1c0354030002404640d292910195915000948100d04ac0865507404075903c007001c112041c45145c2c2d55440d9034480d45029000707402c218018024901404840c805004240d0300003803592900044503603240007003019200210004c1c0180340ca0030b07074001c4090f82c0008484030300284034403e407844a0302c0c090104006811540459000d06 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 843407823 1250 843406573 843406583
    0x203030c09040e0d0c12081e0403030219020115090603050304060813080c0102070b010801051608040c08060118050a09020d0609050c0907030c02060c1e0a09230306060904 75
    0x944158400340580034051000c1d1012580801611040703040800003045100018000850a814007170240700510240585003011620303030405101e100b000e03045400f03000e00155104408142018403903411540e60320f203080c041c400001d1103004005e01030580d0010900541540b01804909121284a42f204803039000004505d050b1038488241c401c0d8100600d00c18003460000c1440001ca16580b000b0403d1001600c00107941e41010f10340031101c0441a089640a07a07d031008002921400482c1401030f0101410905c0095079a481c0400030340b0001e40150802e8000e800000503414090410000302c50744001c41407007185e4858100344221800342e48081c1d40020050300c0c200100324154404400e542c003d2040e00c84844403500880c502c41c0041d50004002075a071504006010342c140205e0781c008016800440c60101452099042d8032804a050300e0f02050028100b11140d0040c11000c0082c40c041e0346c032100804100c0d125040392084d034901d440c001d01543d000964076103800403440744034039405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 843409073 1250 843407823 843407827
    0x151014040606020706080c0c0a0b011d070e010c0c08120a0909050705040605070f0507180f09110f1c080304030f0f140c10050f060114190e010e060c0d0e060a0203 71
    0x80079041b14264000b401c02c0c1303209802003052132000c81040c441d120103240500440e04081d4908141d6000010111002000207070f02802440034141c0c0c441c559030650402441d00b841c030b0b845d02d410003d0f00380c0415800800c084c0f280c20365055000300450083c1400c003115840b203000d4580d4a00d020700544004071480301c0000d0080000f886001d005901601000707001f000400701d005081e81e5030b2450300c886178000001d0f030180d11110702190480c600941c0c1c110312040d58240000c02c2d0640c1c4120381032000014242c030a060b0202d07019040e803038803408080d40310210081d4000d004c16034148040c40fa03000780c400742e00180005150310b0100340106403458034140e2035624a03006103241c403ca184141c000032103042c01d0b406242c038829103404d824017801d0300842e4048008281400e202c00054002a40b0192480c2220350603c150100d419654003c0c0c60400e0441c20000c00240007240121960054406400d9001a01180d40381104000190004034191541c0303601e012a100c1c4030800c2458000c0c0ca10300070041e441 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 843410323 1250 843409073 843409079
    0x30316020105030a111b010608030c071a130902030703200703200102180901060f051b1504051c210e1e06070305280c021510140406060207 61
    0x801c00c021544440c40e1100012480d40e0149005c0700c540c0082060320300411401000c43c2944028801c0070000c3c1208401903140504280c1d00e2901d41855100d00303901070300b86462501ca404003c5045400743e0004038003070b00d0b03035584a00002000303400544500000900d0030510030356081e41c0c4401a4000c0403052551070070102030343e070220784071080340041e44540d503284103811410410900103090380300c900708031010200340e03810144006620144d10800401954803410454180c02a0032122109000c0c11034940d00340d54045010300c1e100540e03840c450310510300000c01c000e0090104a00044080700c5603600e0751085040004c8805a020b03241d03c1e0824002e81c4025800444207501c8007980d034048d81c0c2540c02e109040502d01d00115103e040c20116900108100241203515101c4c0d1a404040152508a410071116518440c0c810341000c0018159a03054a842c2841c000c11121034802044071200b401481d100445442d800c0c65842009964100100360741303800c0c5064011401078907059030050104903d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 843411573 1250 843410323 843410327
    0x115080a091412040501170c03070c1b170c0103050c0901030b03010b0603180f010603080a11010b1306080c03010e15060a030c030515010503010905100213051e0306060303160201 78
    0x2400720304aa026494141da00640c91060254481c61652000d080d03485a1600707001500c0c08100000113000f408041040103454451042030360340121261410030410034080c0b174400464a6058114000b06a0160740061181c010b034411b81070540800d0251402c1011490056042d1401610040c1c01028103010b400c1c05944264401c050301c02c4c000b000403070410440008034490794000d0f102c05800300c0350390041c030a0825003002004074503240382000304034480c5561a000003a0040c400c2c100204082d000d90340c41c00440c25002000400e1009144d101d12610119003a07000306031603c0f0303c841b22f0280024440003441c041c45660b030407080d44c1d0054140500000d02101c2c0c522030040005620084000011000c00c4040380020b020311302c2080240010044903000780314070541603000074882e0381040c11010004001103000ba00340d40320084050303200e034125039200c4030034202a0446904100e8811100301040340d6030101241849007a01a02e02544400c01415184e01c0340103030810580b200c00c41c1c9240154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 843412823 1250 843411573 843411581
    0x30621020f03070b160b1f051905030d0207090501060f0801050609030327031912120e1902090106030203010335070f021807120e0a020a080a03080115080a 68
    0x140040c1a00c10f07181c2c0720380391054990800c400e0613100307000194812013041042c000c0c01d50042c008014941d80380b07004400c40700c3ea004880c0601400f034440c07602110503180c0c1c40c0d80403102800c00182541c50310201032034020b43d5010070f8407800303681c0307801e01c2c0c00000c481d40180b6100c02c81044603540c900a60b8202014004558000e100c0c540e014481007105240303803407103455030059413601c40800700500c0c0680020945000d0010781ca1070340141030203c04800291003030443c00302e8000720b810a5024507a01003003120007031510f1a9400e600d80640d130300c3c0da200d200c50340c12a20749280c42100c03c0150350f40c03103540c11001c902027400000c01c1e5180440074850581d07030005501a011504400c05908891040c08100c45a004558100c440c51103480240e02146490380307202d00712040403554807006180048004110941010300700140ca0782d50010340c00c0300d607070034400307404c8168002c2c00c0a01219500c103025a40c0d1150b042c000d1b00061400d100100c0c4ae446000c01e0440391560036590710365283c55440d0307a04018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 843414073 1250 843412823 843412849
    0x90a02040b12030f0d06050105030c070b15120312010b090d0807260c010e0d0801150c050109030807080108011808161505061309020a0e1902031603062102 68
    0x1c180c034504101e0166404000400c40b1034405004180c84105d92010301041e0780458106a041c0013050041003201d5001c7c0007035404942c4c1186404006848411408400a2a03c9a22a00445400e90100d4501400030003440441c0c400307400501c080c1e913119107901d81d502850400e6540854003100720b101080300000a04450307809188907001506103007440c10500358110003a24100080801d030711a180c1d20038401c10001c1d120140c09030000307150402004005440c140900c4d10441c0c600f004020f006071080d0341700b0500c0e0303038040c00812140c0341c40e09001c0c003c1e03541194041c000400d04000801d5101c01030180e101059505041da058aaa5598a55420350009c61860100105070340d940004600150030304000c40361071550004c1d4500340326045c01152000d10340080c0c0700508120340040142c45084c840c0045440c10440c1841c03a40300d090b80a50b210404204102d0146c0c00403040c010341d11011010306c202d40304680ca081240300d54805504c0c01035403c1c25407010040d1030100c2544003604048242c2516 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 843415323 1250 843414073 843414079
    0xc01080414190201030c1d041d10060311030f1b04230a060603020c0c1201021908060f010309210e0406030501060504050906160309020303041229090a02040b 69
    0x20201003900e03554504180d491640700b0010b1841c2e0500190350b00342c8034a1641c40064a40120304010280c207401c010340741c10f1011801140d40d10520b009404c0040011041c2120503002d13104003a40e141c20b184080d00755401b065640c600d04007485001840c00148040c0c103528403102815416025039507044c0c101e050f1000f1980c11a80750704c201514110541c51100c0c81d28050251f5002e5820800104000ca03201c40e00050180b510420655188200c00030790401480c01c11030700c1c02416080c03131300c10901a00840210b61049035043e44a840c5803070304801c145200345429603407010510351002c011002c0c0e030f0f00180c001c1e10300d400500d481c40400700b8215100b04800b1940c10400c00e413040d000d0203e000c854042d4015a40c0c1d9542d84030a00c21842e281c021aa041010a401410581880c8042d00d10a85004294105165413007400e002103450600aa0700140303904107000a10040604200f1003030f01d51b501c1200244074080b0040c40203025100801750082c1c0580c0e00a00241c80c05a083c0f02c01442411582e80d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 843416573 1250 843415323 843415343
    0xf0e0d030527010207050709020412080d14010305060f330109030507060201150506130608071e03020a0f0206070806120f0d032a080613020d1b1d030c010804 69
    0x190001a50b0392081500c2480d000599a03203041c01d007103042c2129508a14405801000108100c008040344080256004844903035240001d0348840000c00d000c01d541001249480300010074000d0104206100d0b0182003044184e695481c1c1510038400d01110201d0038103449885600b40b11400007000f410002070606000c04610b4a03515410700e0840703035902450041c1c0d1249184080505032a0402c00142070030382e2078500708110500054a41c0d00700b8081c0f001007014800006a03614030440c5403003607c9640344900074030702d141240c00034041d50145c890803010130144134482103140e02c0090705512450403a5070b8800540c0301c0e24100701903000c20340c00300d0034284903444840b28041030600501d140d0100c240c81c001591040c01c0200020450441c04c58040b407104410805801e5030450350712580300000300d403128a0310900800d003070020700440414110f441c1c6898503031103c40b501e0441c450241206600c030320a43c21100691030798003400c1c0c107018507056003001c02c8210440d4041c40b01d15400070700c9540b10300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 843417823 1250 843416573 843416611
    0x6020313050f010b0f010e1014190507061107020d0b06030c1e0f18010b0706110304030305011a07030914010e181906230a090903050c010f0e0d0305 65
    0x510346020040c050400e84d41d5050050b00910700250002000310f42800c4c4010640a558001404800c002d907080c0288241a00d900305040051001c5511a10408544c04035400300342200500b940c02001d41211031034030703101e000942c10b1560826514460f9006083c0c5c034110721165942c060400010700625010703ca03028210010741ea40c1c9421000c1048042c203c07007401c804900c10440141504942c0740d0050746545500d0103200900d00286040d103da601e0038566070006031402800030801c031818000110300c0441440b0425605401260484050000f001d1a2942481c41c1c0c46880c800c4a100501207070003160704009070004d54010040c80e4005040c034182103190000402e200c0d117002c0c84070f41c1a0260380c00801007090b03445c0018900c1c980a49004000e150304000c90380c1c228000101410450049580c40c48109070348050460001e4803401c1020f1141d00e1031450041c00c141c00c6030148903455420109800c4418025105611605c001580100160440c10308190300419000d80940910740c4820300c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 843419073 1250 843417823 843417833
    0x27070518220e1c0c260d020c030a0801230d020411030108060f090c0a06051b010204060c110603040c0e1b0f0706230612010f0504050106050a0812030406020313 70
    0x810040380000001c2d18020b001110a0050f01d802180310006018080c4c80740400702e01400e01181c0b5100d03001100c0b8110b542c60954854140c003d841d80c0a4000b0700004400c03001980c040003500181c003c68131044c2969884501c0031120b903000d4007841c4603010a012504801d0b180c200300104080d070014100180c43d003088001281198000d800c01180c55100d90140810060449002a840b040078000750a02030070410004100308028400c90003000004514041b0503100100c400c80700c030079010000c6507101c0e0b4450024246909150080c0e40044105c1c1440549091910440c1d10075031703004c40c0360003000303050041210000034042c21019450880b020031707095143d03264000304009102c0d401826254900d600e820030a0b110301050340035144248158420307892007041c2d6500d402c1001103d1a605500502e0b81450042c8102200b050150b03091105210900606501c54000e9500540300c000e5015120f9609a550300030940c10300640760760800001700840e280345d01650300040141424000d01e01d00d5250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 843420323 1250 843419073 843419081
    0x7031104210b07030212012309041b06021507110a14031206031b090a020909151011100c140d060e0a0b0d02060304060603022707051822 60
    0x8403200c81903481c0c0410501c5280e400c1568030030314900e029450a80c604240341401e12040c403a10707140080a24500041d200d441050861401000c0c000302403924081c100a06041040074230040b0308000c20341d02103a181d101042c140c84410400794503c88035103031100100c84046001c00148241c1c040c40d010600010300ca1007128000c41c4031030380203584490405140c4443c050018003914030a9108000c3d040e056085800d040b000280c04541d00300c49a80d804524001910503141d405600012210070099041600301802140c0e050a5880086094602d4019200c0c0440e0710449042640f00108240d00c0c40d60b0758100310800500c83c81c12070070340d81c0721681c0c81e210380d00300060184895031140401c3c0010000300d810b1381c0c1d12002031002400030aa880c00801c420300085100a07004982c0000010103010440e0840e600665015106594252040070328441d0014120b036808244688400803807030f40b034400d000b510140d0351860600040c51000030300300406040302d0100302c0207940039400d0b040c1d260089442 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 843421573 1250 843420323 843420359
    0x390507080d030506010516151b020f061503060f09032502040f020412081806120406051003020901091d0f0a030e03031e0d061e06080f010e07031104 65
    0x100901c0d000300ca00582036030402840c890400000307021040c1c031a0618000b101d410b81d004121004051290f041010280400624103100034500c0f002c0c031120203a00084059800c09510161070184d1215500820b402a03131880d82903055004c000481c4103a0100102190460000c0301100d1401c402c9140c2400000040c41d5030f5810346040c110140c0960500d4000c6a032100e03000c0d40214642410300710240f10010316460040e02a00d008501c20741003142020301000d807041c0007040c5645032604d0780300619140b03408a0b0304540031070806003c540d041500e01031030810f4a5006208180c40da0a200c6040c0c02440140b03842c0080703041c0a40c40c0006043d00303002025510f054400645040c80310303070601a000003200c068040c000c6d803003004a131710005250007883d03800c2046014203a070b850304e4070308106001e840c036038008000461126030322907140c64a25406404942161b10b40030b42507500c51a003079001e28424480c20b00740112003000200001e22070ba00012040c4005e01358681490340342d00d404c50391551922 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 843422823 1250 843421573 843421589
    0x9122102100f0b0909010e03041203031d03130b030c040918020d141b030a12020f060109200304170a090f0b0301030302120a050d05042a050f01390507 66
    0xa0030040d202c0c140340402e02e6000f40c5c104000c1c000030a001010f540d0f40d209a116028451400f48005000c1501c01c0e0825165003030400c50020301405650045516503107c000440140200a071000800c1c450f07450949105000c200d4055050602d08640c11010345205860354103500d030f200d5078031001642c44035100145070303010390102c0c014074400b100c0d101c2c80c1020007110f003024003100500d45246654002082c0d0040b50788a050f0016944803180180c0c036001c078484110f486801450004035402c1d00c00e60044d6454084030003010250f818003003986806200130b0350050000048083d1100c0031001c442d004000c0880e4a15014601c181ea852810406010a400007110a41c0000042060607410440c4208400e58000c03074904d480210840900309110303120701840c055480c0c000003400c1c8866413921060b00e82e0304855200e05200410600c5092448a020f054483d5406c5074080e0703143d520403002c5500c0780d0031104090b00300c070340c020b80b101d0790341c0218a0000b205820054008800a02e09100c020002c1802c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 843424073 1250 843422823 843422831
    0x30209040e0f160311060c070e010e0702150103050604110f0d0807060f11030403030e011409010c081f380d060e0c03150d0606060f09122102100f 64
    0xd02c00d0307141046408007008050004520007400840c1c900060441d03451000c0300c00603540d50502101d00d081c0310a40d88a543e203804243d000182c0540d2641c41507129010a6003550248121440d24540700d44080c04050800d03400381002500043c40002e15855001000f008881e424101d0700015015171000f42045410040104844007003241500903942c141070300344000e20000110102400c12400018005410035403686102140408290f0205201c0441c200820749145403454140e406020001240c50014020f4800281b0441c1d00301c61aa2400034000c6800c00802c0c80d084110001e00000c0c0500611602c8000a008030401e0104013041040c901c400110b07121100d0154107000c4502941c41102502c00950800030110343c04811658030001074606254980c50303a0001c2212080c00e001e00406051070003c01181560300031a0054512520b0380c0d03001c1889845420b40c00601c0c0d104c00005044148407802c11824250b5403868540756002c0d80304803490180c0c0d4090502c1542c5001608240302030f91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 843425323 1250 843424073 843424093
    0x302040e160c05120909131a0a0b19031a06031902030c03070603050f01120b0c0c16030606170a080a050a1719180302150711060a0507180f060c03030209040e 69
    0x41030303034141d900c02d017011f142e400001036684030f80011070707501846d44541d10910000200c3c100d25560041c60325100c0500703120400050642043c5050b0001c0c001503070b149400355080d01b170905541080d5403103014040c1c0030307040c0c11010f000810300007002030300d089034075000320040707000503407410095100142401d40c2c0204440c10143c19842c40c40c00107810500013121142000408101511203003600900c2c4031201a540310104060385041000380c19030001003514010000007880102e42128056690b081000c840107001c01008554070320800000400008060000c198060300840c082c100580e49030420860b001c40200e51790b042207404170748440902c802170003461003000c05403103900150b1701d05600e1400c45a50a440183da52009418003448031207040c0c000072f48181c41031124494600e07108003116010300f466412900500000c4582d100060070b440600381409409080500440d001c5d56905448142410000c43e01141d038003030290241030f02001030701401c8d00c0343c3c440c000e003484d401005811141e007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 843426573 1250 843425323 843425329
    0xf140c011b0507030905130b12060702061806060d06020c0a0602040303170118053120090a0c1407060507080c0301080c0f0d0b090f0d0302040e160c051209 68
    0x28a60404400c0010070f1202500203a0002a540103403442122500a100020070504024050001c001038002d0712000c0d900c481c0c0000050600c6c0107400d6a000c3c0c814503664002515004140c58002e50352680c80400404d5090410300c1d4098101c90180102600c1c2100500301c4034a07088826070110b40321680003030300708140b41e40118200310000310000b0b00781c11075242914000c0d15410f0500300301861603403100810380418002084034140070101c0c0440031030000354070001a200080000a50b1264000c040c52202c1280c070f0802d050600c0c50080c501015521661422001401211810350900c020000c1c4003680d50081000783c05694858900400c00c0d2800d41401800d24501800d0700741d01074000c1c03005004111000c40e81504448056a5510818400707000107001059443c8c0042d05808042003030004941c0b000c25181c1d0244000030856079040c06250301203040b40b003140b162004040340e403c00f2030407901e030f200082e040903100752800c1c1d4956480358548504102044800307160980001903c190641 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 843427823 1250 843426573 843426611
    0x10303090906050105030a02180307090b040e07081c0c1b1e050a05040e010917030103121d010809160807080f0f10020304150207081c0218010f140c01 66
    0x1c841c5810a004003441c040000e0203d01002d000800c5950b008200426038a0b80c1e01c0c04040901d03c0201240c4070165200004402407004042e802d00840c01c04002c1c440429001980307070304541804d8004c0201031003415084400c2941c1d4540e00080040c4940c0300030210b071a071040411a21607440000826500d015400d001801000c02c115045007540b69041005598610300030044500c261004034400d0024000d56005005000d0010154400074420300c1c44c084009002d941620f1241c0e01c019102e030581d00c416950041d1035039545c400c1d0b104101c8005165442040b055400180b9141101d091541083e03400c0f09211060300300344603036804180d0420500e4400c0185205c00220720000d000b078109062035091702c4000002c5124006500040401d04012240c0d030b002103060000302d021900c2c0c4040b481c2014881e0b02c400350343c0040c15851029100c05507890b03c204c1d01c00c080d044440e400d410040000550300724581e54118001d1200035036030000c0c0c00c900e2600602d40e00b1072603c000541701031505001d901c03a07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 843429073 1250 843427823 843427829
    0x130b1c0606032a050f2a030304080304080708040803031801060b0c0a080f0417100606050c0307031112130e0709030c090908190c0b010b03060f040f0212010303050301030309 76
    0x5082c40082a40c0c508001c03680401000f103034841c20800202400c0584961207125a040c1810300005045a41000305034280958610340300601d1058008000200b90b4034002924040c02d505800c00c0801c0008285800a003400c921a035003460910380e949942c1800c540080307c00c0c40c0c028840e4081e81806440a00c11403015240750f11007036092810341e5010079680c0c1084200140400d00014001403e003c42a05690007401400c0400c0c00c0c40507008101525410910a190f00c56410040c021030301601500544151b40d507800000c1d4200f00043e1400c44884031009120300681c000c05c002c40d06140459401000460801412082990f181041d40c0b905001e005200300c0801c2080d402c2400040c295940540c00c5480b480004500309005043c82c240f240300d0008101080254003112040181e0441c501c403100c28050803001400d40e82e2032099200a200c200c500d1540007084606120301c5241030b0380305202e11070f8000c0c801800c001500c1080032180380c080c0c1040e004200c01000401c2003541c0b2081c10005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 843430323 1250 843429073 843429077
    0x20d0911040e1002070f0506010f060201050f06011b0c091b0914092a0a0305153708010501320d12050c12030a0f180206130b1c0606 58
    0x4400010311030952540041200f00b0600c640009210050209298054604642101c103540b5156902c1d1034440006006118400c05942400c0000c2c010710b8400340300d82c0c4511010303111900d9904009200800d10144d5041c110780c030683c01c2030301162084152149050424214030080d140e18480d803005810b04960707034065901303414402c0004110351560301d20103400240309010500603d841315501101903265481d2040440b4011882c44041c0387d042c0c0050340a9a20081115007501041041c411181402040c0c0e503d0340038691058141420403200c10034102008907000c2045a0303d0344996070030750b5000e0b41308600b20030f8a01c8180066006c8800007034245024640b034460000030103c00700e013040341c085401070001601100040a42e0f8001e40032581d03078505001c00d9640d81d510380180e44546410030b07038810700150f10704000d005804900b4800c60442c0c2c1d4008c0c0c410940c00440e642000300d164014042544079000c12400083e1814a21024008140c40000d410100e1035060520100f00c910755402001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 843431573 1250 843430323 843430331
    0x606020705120c0d060504021302030c0d0516170709080708070e06010c1a06010507021207080c04141306110c0c2418010219030e030f071a090a09020d091104 69
    0xf941d480c10f08103088030b940800c020505036500e00010703d001d203803070602d181510f000004002c000080100108182d50070004108400d4407807040002c42c81407010540c00c04110003100d00310440c1c0c05510140d174000b402e850300070855600c5051041c100745056220300c01550194805000d0388001030803184d8041802c4c40c0c18540c0f0f844d5904c860500d0024054201a101703c82800714a46074415411980ca29402405086140d10440d041f2551002284070b40c1129016034009031500c3e203000e005402111106506c03850307003030716000e020000401a42c003007242c0d89983c510714090005101ba028140c03086408000d0010380b85280300f4042c00780041103624000126100040080d0070002003501c0350240c00e40c5800c5c40034503c070f80060345000382001c100401c41b403094141d031003010703800304034210580701c01d40c25103520196030700e907031540e5840501400789401490a001e00950190f0b00140c004d42c940145074491303990341d0f644182d0482c3d01130302c100713071071161907260765030900c4107142c1942802007055030100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 843432823 1250 843431573 843431593
    0x30501050109061a1605070b0c2b020705010e0607060507080702011802060301060e0d1704061107080d05030705040e07030c020d080c09010e0301150b07020a08010e0304030201080415060602070512 86
    0xc100781c4100d407410208040380024217410320104000030070261040c5c49003c0e80c1c40807142c42040d51307079000d62100162144200324080d040e480c10500c0400c4206190001c1c44030b00c2c05c0200554420f2800348070300d03801c09000d2003803001060305405018004c5403151142019410081c030000d0a45015254030304840c1d02040d00d03400140c6400701104d0449200c1e14184804042c520b001943d40c0c2d45141000d4070302d60107265040491075403a1300900440301b2986441810318909505aa11802684070303070a0039801c41250320b8100c5005500a507800191498514940b544620441e54500d0f400d079032050001744d503100d40c0b0000d0342d0108040041070080342454942460400794101983c481c50102038100000c4000c10700040d00c0c2500f0542084e04040c243c074854a440d0f071071039400d0f900044401c1c0d100700600840001c8082042c03080c10304101a94001c0c604d4542144c0056814406c0684129019103a80030703990b19902161141901611480d0b0181100524100400085104403d030240c49500584000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 843434073 1250 843432823 843432869
    0x3040c23090c090301090c0303020c031605090402040b130c0f080711071811030f1510090504050411031c0f02030a09050d0c0e0708040c170d08040c0f03050105010906 73
    0x1e40d800841e50710030590340c800140110780900b200d2440200000762020000c0109034020444c1c00e1500025421a0400c0141c45a13800401e244c44c0b08090f000040040032402508098001c22024403000e00141034803410003280d00d04868a0085120000e40c2c0001500500c036400f04ca4990400034606d01050303207004410070f40d5200c500c10f07c500504035142d9171041441003421b8200c0c102d42c5400e44100342c0c492400034101c2811203421240c40071004d441101d454500d141c052501e1100c190503940303241581d030500303003880b0090030040d001b510f80700b00d184402900f51341c0400452403e0141000205054543ea80c00600a40020b450320b000f550000e01203450180d82c003025040803144221940e2098420034102624a0a50741d001074040300442070402c103180741c01c07025580c065880307030560284140d1b440c1c8d03500021842c50000d03036030503412038002c00e232200e84124003982d040b50203886c4000c8099502d015071001e4040540c01110301d40d455000400c00b040d402c1c4108802014280301c907040166401d01c039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 843435323 1250 843434073 843434089
    0x6030c0a031b020c210a060f2301060f140c0a140736060803070309050303043501050702010b030f0106151412040606180b06030105150f03040c23 64
    0x26103014280780c40c998042010f92485e0985031411203001c3c0c40501e0395608000019001e030400442810703041440400507064201d00450f01f00034001d251480d1070742800421625900b51010400412544c800c1e80345d14214800000c101200b8044002d1054500625088102c40c21a0b0021401500014030421020000c81d0300701d032046c52859142c08896101c0f4084505031402030800c4a00710785001804600b0610000003001018020707201d00c1b00b00740da01d00803d5903900c01c42c000d0401e10701c0100001c9006518001484401d80c900e05810105100860412401c5131811540000181c2d11201d880e869401c003800a00e43c04601d6100a2110300d04141ca59156017013064140c0c02048060035031241203010940540f500025207000040e031906103401c4c5400070380603d024010072016040c0454004001ca403140c0d1941c4540035007041d0450780382c1000c010084940d030785403421300141000718694610503070703000b0340c8030740e114040c2514003505104010402007510b141091844940d111981182d55038000c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 843436573 1250 843435323 843435343
    0xb040b0d0b060f03091911060a050c030d0504031403070e01030f0b040e070f0b12010501181502150f1513060302030111070b180a0b0402041b021506062a030906030c0a031b02 76
    0x140f0940c4c0d8403018540ac0710f841c854181e03000168040030541e560303200e90b99000300d4069802591044103501d60482c4048051009a030208049030782c42ca4118025402600220107a214110f0700180c81c44603400414203072100e12404a480d904004070900440010b4010880504041c584290a01500d0000006224070601519041c80017500702c0314903004040c8030460150485068003004006a5003001c1e5890034111142410243d249000846030f10007904054880c20454003000f15024528041c01001000e006c01544283d032a6a00400544c0b001d0140558043c05a6070465850b1000d003807045030610080d214012051038050b544000c3c80300080c40c1c0408940041c000e41407903c1e688001130040011801005804a80300902454581c0100301d0581d040e501c410b049406070303501c004200c010311440522046080b803856401e420020140909440c50001c0c80c01c8074500b03039013030001820303070b030411613040d40c00c02d0380001d40000c4282d2500074403d1180c031480c0202071fa41c0e09204043c0d12111101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 843437823 1250 843436573 843436579
    0x1a06070b06150a020d0219021f020304081501080d0503072715030b030d1e11010f0612050c0306040218071202030703060302190b040b0d0b060f03091911 67
    0xc03000c076210780c1d124401000c842200301c0b04240c0d50420181c0c084d49032510440c580c00580541d091003031030031001c40b40c00064168001c0ca03640c1e060301140c0140c04520702810100f8118402444003051903001008507100e96910031300309071032642c0b404001d10700d04480300d10084200502441030105036504628820071101a00c03410f420040b0f0050200b0b2011031550380b007440194110241102d440340c0541c0034120300c51040e41640c201040c2120f0685103409010030300b00c001522044001d030898450140311300140101e4001085001d0b900003900252501c07130f044070098802450040c02001000c1100148010080d005401c40e480c054001035540c10b01c80900d6228090968005883e04c0d10a0403031104e001e01c0e1040454403030a000030024028880c500049002d80194011101c0101c503414210b030486001103981440d2600b40702c1d000103907800042044170002c0d200e00c1403012030f03a500320141c22513070100714032540c407464600f640f2441d1202030034582082a00c85140140400c14903140980401015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 843439073 1250 843437823 843437843
    0x207051c0215012c150d0203100603301d0612070e04061208071202121611010305070f03020310030c0b0315030319140403120306091a0607 61
    0x564059003802c1d11150a034094079902d000201d510910300d02100c41c0c840550715440d0110380d080c401211102000d844d910000200c81d4248800f131329090a04004241c400380550300b20409002203d4140c405c1c0d5002140d00030f03800700d5960001c881d0303143c10f086141182c1500c42e49142d040c26002e0031140d903950a128405d80c03507101e40601e54075504102c401240c24595130704011314102d1002000e44908218040c40780d0b0504900003a100104a0340c1e140d00b03900300c8402e43ca0102103941d041091611000c1690960040c040ca80380c081030a14043c00c00d1074107690348a443d0101a142c0001a04c0c40e070001c40c1c3c1450b141c003061120607640130303a00e460903103400d040040e600d03140c0501c1100030f83c04552008100d251101c2c008100401d107903014602840e03104c44031501c6441182c0815842e0300030800070b10190a1445415005d042c4290ba02b28003250084880c91f01d00b545a0700c0d00507010b1000d204d0000800d032501c808000c80500c0f0f100700e4080015110b40b0082c0c0340b030150001107072403240c500702401440032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 843440323 1250 843439073 843439123
    0x1605190819031101090201050f09030a05060408030a05010501080f1308041e0e0a02030402010c1104020702150c0c0f180c0f0703021501090209060412050f03030703060f09020705 78
    0x1600256025211100446030034a0710400c0700800da11031800100c1c0000c0c1200c1030b0720382a0a05004034a1005d905855440c10161207203022800c5401006100358584900805000454000c2c0b050034041c1e4003900c1e086540c3c7c07030f001c0d03506000e4480680c0b103103042002071020080d095540c105a190040035030b642020000149080c20b089502650300141e0081d465a41d121001c1580640c106080300c9103c10704c4841aa1014241001c0303000031500030f400705421340307000000a081a4643c0d410018010f10041c00d003420303070300491400c0b01c090308070410b030041c0081c1c1c3c0104464104034408100d24215880941c0400003004030703d044800040800c641c024880110300c070107035503030155179501c0040641e0503224034150a00943c1c99100c441e0380c80346040400000b00d0903201d13500272901d40440280c101807800e480e2462511030004c00d0001694107010308004000c0403c0c0500065014040c5075a02003039050501d880c540610f40554402030b4490300c100b04004c0050f402041c01c5142d554404540e81000342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 843441573 1250 843440323 843440359
    0xf04080a030f0906150603060b090a1701110403140f010b030c1c022806050403080a050f1c050703060e061c1704030b0a1a03070308031308030103061d1605 68
    0x30f09480010940c1d8107050781c500710b402800c504082122195581030181a94a0140032001e1240e1011540c0005c4469424804081c0703800704c23980d0704038204c0000600c2c11800308440c1e941ea00150002c40b070703d4030441284800d00c2010000840c2c0003d0320b80080110707200940009a40e42c2540c40707000d0040c1ca10598130401035807081703240d0b80b1568001e041d420003080c1c2c18001000310003040440300c01c0b802c0784a0003c0341c5203200d1010749042d81d47c0b0030022481c00304404001c1c0d0310b6800a403a2a4241d00c001c001d10700a80d0020201c006d90000041004103041c280090090107441c059040601c600e03500e002004896505d038181d82c0900410000b5104100000341080c0351996141d603d2644a04000030b000420170240d0040d05108120202c8200310341200038101c48101003502c40c40c0380e07240d0700c090020b00104013000011908480d1142d8045514540c9070b9035039546030426032045e603440e0365900e000030410012038140c1101c481054050320100010703649030380c0c5140c698080d190180721160200d601110f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 843442823 1250 843441573 843441581
    0x7141221060108070e2205060405090d08010333060e070e1e03010e0303070e01030b0a05010f031109120a17160602030a02090604080a050c060316050705070312080f0f04080a030f 78
    0x2092203400901c210f600500000580000e5901c127025a00c0e0000281400d0340201d01d100384441c07185d8480d54546d196840340d91301c800040c1002c0014030000303150b010117410300c0404a00d8003d1a000d0206400e4a0020a0303a400800100300d2000c0c400018a8100907690740c150100310421400a001a02425400400c1c014a404100d96425100000c2071200030740d085140a080207000341c0c2c1c18031038562002c0a020009840d4411680814174941300b0310420360007500100584074290030341d5810034031404001804803848014071000703508241408028001c0600600d821040c5035100c1a152442010845814034851003014103002c2c1c0c00300200d02030003a290125000550020305a44d240d54449022584504030110219242d04c50820000030314280001980e01c00c0e0140f00d071100c3e940d03440c0d1809651a03440604d0413100c0e40107a901c0070002504050110303000582d5070b515144107103094130002a0f004400b90144503142c0301e880130000000d100c0e070115140d4500a2038041a4ac04803820b46401030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 843444073 1250 843442823 843442849
    0xc2a0415080c04230112140a0809010305040f080a0906020609061e090c061813050402130b0310060f0e0a090206070f110d061a011e0507141221060108070e 68
    0x507241003c00042d880d9410342d0b040303000b14003908400040580e40c2071580c3da03823402d890000384846400c3c00001c1a560280d4403103540303d401440300c9007181c09542d4a40003141c0c0418000c4c008103411440078010f03558100320440d4800c26010003441385041000b2021000c43c101c54800d89100e0100d800100604803c0c0846c0400040c050010754603030000d00c0c8003840d00300070419018000c541c15a0f610707081d80c2c52030040901654000d0802000108015100000340014443c40d03901403090704407000401d1303010b109007c01003000090f084102801c100e01c131950030b00040c00010556003413140900140e52054229540c50782e0001d03960b140d83c0070601d009000c50740000c801540c82084c4d2045070042c4000d980018260038483d900b10203000c403411005503142454058600040085000003041aa010380c00a140940c059010a210401003115192815a0040c1194400074000c91814509901c03210801359502001d40540700515101d4002061054028900b03030400094052203032164036030f180b00c240c43d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 843445323 1250 843444073 843444131
    0x1b05130609420e10301e15050607320a030c0302060a090b0a022a0708060105060f0a03050402041b170903090907050c2a0415080c04 58
    0x40031070300c0304007800e80720f0b803642c1480c000e00301900c03c0250584070307001d1312400509071105410340402c80c1c05000750035800c03070048076105035440307070524030722500c262400805c1c507501135021031071400241d803021140446070300c01c0b0b0280500303200443c005001001034000c0510804401d05440309800244403020038810902c144601400041505042e44071039040409801303a02210416165102c4210444103414005072071020844003280ca940c286400a1080180d184c000300420f0b00c4031b402c400d11741da4200e510421182d220607004c2040170400e00100e401004106e4070141428652102612036200d2030b40d592080580d144c0002c5c04540c1e55500c010b42e00100e204111003d85001e10020b0320b00c00e110300c0305414902c041d0001983d403080c00000c4130031151014001011545038001c9c280d8103034100002100c094010080075040c403403083e40070162079004001205518000301400d01c0101c0d012000d0002c81d6444900c0300340074800c000070b440c0030030721f03419100080e1200c0c036801441070701d546010389401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 843446573 1250 843445323 843445439
    0x8120d0615020f0601140303040b0f0f03190b0405070e0405040203120d060905060604050a0501051c0203070e2805060714100b0118060e040f1b05130609 67
    0x201e42e0340051800c40c1c64000c003080740e0144c0d80325000300c0c14645102040c654150f00800060051404160150521440c00d060312400c143c0c4201580d985a04211020121000741004500c0c012080f40961a8001000c4e0307020041404e00f0800240340c05062030109004076100c502140031900c0800c04035454809500c0480e0320703101c0c801c1c00e800c09849580304818440c0c1c18a4041040c92402a0480c1c04940300140560f00c010b140400546481e008148520310104172561660744882490005522442c40399a507142490710b1541000740c00c4071911400c811100062140d68540244604203500307959044800326101c803501d241403448850711095030740c01401044205d9000d04007541091111042c242c94408a8042c1e040361003803034448034400c580014450740e41400c5213080c15889484c8e0420490404104005890200000200041c40c1100092400241e0045502d2460a02c3e0060152840c1c62000945041c2c050441304a00401003040c00f52442c04411400d051841201400e00b90089104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 843447823 1250 843446573 843446609
    0x140d060c08100806090a060b0d0501180c06030218150c0f0c1c030212030a090206130314070f032018040501050703060503031801120f0f1508120d06 65
    0x2081e0007019250020181d02998000c50f0000340461610700c039a51304d04c000d02e80400151192005400c0240c6015004105014080003094007805a620140300d0f41507400240300701d62a100c08840c5059010b501058414070805c600510b6044580f10b1401007201c045035025001044001c0078420b1242140182c4104807160064040120b188c400310007044802d244007442461110480014a10380180142c221404a5079003041c410040c6801c4540e180b400601d0b03140b16804141070398014203030a6100030300c041c802c02c01c00600e503404110b601404006440c505160420b400807401503804020700c42000300c1d40442e109191030b6000c18840f100241400d20084189142e00c402100c251000e4403e0750130000000c1440c1d010780507400032502c5c060001c610b8070750841031503020f0100e0b1030503450400181c120081d0410049010b070318501490000006807540c400c03400e0b41b0460305081083e400581c2400340c104840c80c0b0202c2c4c0b4401c8900c45010030756491101c0c1c03160200806080d08021a00780303080d01c1072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 843449073 1250 843447823 843447827
    0x10b0604030c0806060613062a050c12030a0c020409061103160f0f080f130605070f091e0e09010212040b061309051c050405030609030a120603020a140d060c 69
    0x2c808071102c50050394103030b807205d1040c82600c0c4102c0c40c1450441c4940a0100030f901c1c03040c0305e000c80d050243c40c425483c9000440d901e031343c120b55000c41540c03207900002c0400114a44090340c05909900540203501d000100b00001c4e140d0014680080c0c0b1880c1e41e5003c54050060b03580019030110750303001800345d80303103400f0000210403041c0307034105c0b00019030301c0b40e0000f1b00c036000754011081552a40c80e442e89036901c0650107420b100c030041002c840c200800d0b030108001a081c0c0a5240175a0980e1655282048485130007810f400c401d5220a65400a51914101c494441d02901d026940d42c1c85410103155950a046406031084644c24001011580100010720454001c1ea6000701411140c511035150002076403c161003058101918542280b8183c0a0b14088507501d200005000d09001e07040130303955030000c2c1c04c082045404031000d400000d00038540130303401810890070824000c0300b0801c2c1030035600800d16940d10382c01017000e140442005d05030f696032031001858070140e0204050114200c1c000300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 843450323 1250 843449073 843449093
    0xd031503021906080c0405130b010e030106030303062d15020a08030123090f01050f180f0a050f0705070303020703140711040b060903150414030f13050a1214010b060403 74
    0xf6800015008404903803841601802c450880382c009000200790a14941c5220052a0b009040c5052000300500910340303480a0081030005d6010342c0340000c080f4078140111401c4200381d03d0662004810304001a440c0316030b8144038060320b01120389520340d98400c110a230f24001d4074200240403201d001c000050070482104d00f468503041400260050a000c9005000440300140c45012002c500b6400520043c00d2042c0a1030007035400400340f003600d9504030501e50783d002d0290747e05001d1096030400c1090300f20540c0a129000b4407207207201c03901c1e407410302e07402409801010002030416400003003103400d061180180c1840024288100c9903144640d19084002240c5405c0081c0580c0c1000385c0080035281210540e450250041c0145c06609030150301c1000e00385005100700d0314105407140d080e03055541003000d0301c10311102342505541d6014517451260b541c801c0d40e1041d0f20480203a141484088560700550404507408003985c81d03503883c8610403e000d025080c920a4215001140001c140840566 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 843451573 1250 843450323 843450329
    0x6030a0e15091c0507080909041e0f1403130e040314030906150619030f0e0304082406010c0212070504050c071118160e04051008150402030d0315030219 67
    0x3d850640c1c1880350152503d00401e03030042c1021405010031030050604113080342c0d000e48a5410000f40602c841817120394145204002e07a12403020010800c10040c2d070002c007002035054800250705010701070400f859070b150107020b410320301c500c0240490109809600344903a10880041c0701a1a490312400345956180c0448607400800702c0c4288000703050818808413017940840280c40d00528030760020640140c841108409941039032046400c0040c0704c148082c00141210b070000c0d01219094011201a174807408900e242050410802d0061580e0048c2c0b075284290380c103881c00a0400f07100b055407400c01340c4980c001c0f070f0818148020004541c0081000340f542c03c2c400c40741c0d020001c040b9400c0c0f0a408c19500b15400460351213002280142121040d100d6046603c0e00c0d000c00100242d60100d27007aa0360607544100900105030b420710020f135080c012900f400b52030091501ca24941600000e541d000001201802c0c942c1e541d100202c0001303250b4407200a55006000350110350442564101704a641c0c0c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 843452823 1250 843451573 843451603
    0x22d0405150f180705090303160308010617070f03050601050c1f0c020c090a0b1306030b06040f0b03060f06040608070e071803080a0311090424120206030a0e1509 71
    0xb8a4220340e02c0c107011504030000355640226141c0d6a4035406483c01c1e03100c000711903418172050041900081402100200492207a0f50b00415945014005000340c0c401302030300d920400300e030b07020040c0690340080585010305582ca00403540c0e44503200180e800d445440e00c081c5c0f0340e014400c8256174403c04000d20217203101202c0ca041265142c10f610490701d079018080995842500c0c0c00c0440d54015064001642004005120143c0c013a0351507221000c0300e056900407249a10183c0c2000554a071a12440c0703041181c00740280142480003000989504006100c84882180300002c6040c40c0c0340d03036007d60060044c00c02203c4d05a5281e05012100030011500c0794005801a03000e20508107c07185414103c96020b407000f41428440750050300640198141c0c40100d0340b0902103c80c02d9500d40c02242002c1030741803110a4200200c4985907071075009030b0405128804607a20500040e2205412250300031a8000c00080e001410482141400080035021200901010038030034a61408120743c1c0b1000080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 843454073 1250 843452823 843452839
    0xf070303090b070c050c0d0515090102040b03072105010b0706053102040c030e060a020d0212040f0212060c180310090c1707051f020c0312090f060304022d040515 71
    0x10b504028000010715001001c8d80c002c0742c11f00780c101460025240e0000e0b1944000350500713441c1d9001071103a4000312008000180314044110401440095006540710300c0e180500c00381d0306291020030076114050008010a907205c00140e01107020551086000e440c1580400c01c501c80105445040c00c40040b082c0c0c802c030710f40714441c01007074003910540844401185c060003041d0fa9400803d002034111a07400c40e402d80e000c000d000301030394078211002c0c810751003200600000c0a01c3d006101514143c0b4140b24a55031000040c441d000c4000000d850740382d0881443d030035018001c440820305110b19002e002d00c085042018100c2004400c9400000396100300d58000d24504004141c9541d42103144591034109600742180402e015100322009848001d50045511492104001c28174055000c081c810070844041000c00c501d19150b40e07100c002200881300c0509504190b0000766807114440c0b60803001414050500300340f400d03103041240c114031000f03100b044640345c904541304000504140c010703c51098 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 843455323 1250 843454073 843454093
    0x18010f0f050c03060f060c0118080a080f0603030919031703041505010303170403182c010b04060c2307030c0e070e0111030d1505040b01020a080f070303090b070c05 72
    0x4860940303204400013402c176003207048090280520b03584030411036000da5494040c001c055440e81c10f100700c0050301c14981665910b500d488000d2000001910341c2c5400c086c1d0780c00f031200c29134000081e00c00c00f030b800311559441c013034140d0480d4000b0301f1903a000414025079480242d0001c8110f10103584641e000b20740c407108484445138150220742d02400020085515400481c40703e070111040f07198064030909084401d21400141e44070906070503131013085100f154091803a1100c61026100c00d032620700d402698000e5040500400141c051400b031002040fa0b007100020500542844050000105003c5011403145424916483d031816020948038412400c0c00081d100e84110703062441150250740304200f035001c0300011a01e5650071441c01d290780c0700a00c0071101d560018420a0003215850b0f0740c81040a140034140401c1d590b0040c00f030390564011784400d03030219210354201c51008110480c055500e0809140076030080114140160600210380208264140c02c6144280d11030301444c1210b90303d44c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 843456573 1250 843455323 843455341
    0x100e0a29061b0706090e10270e06180106060c020603070e1f090501051c0b0609040c0203070b090a030909020f0f0c010b2b0206032205150609040305030f18010f0f05 72
    0x401a14040501081f00300200000021801f280c1d03850f8070140b0300b588000c98008451425a80040d402802d150448024869100380c411502c140c1e1001c2c2d0300080c450b480ca4070401078500c0fa118100a401914000f0029407111300c5005a8030f801c002c0141805a694500490395a2400401c0718043c00b256a55102040541c001c005075041501211400c00c030a040c403903100000340461890080d081b4034180207007204d6956038001d07413258520a500450b190f05072418800b02c0000c0140440c0740a070048001d841c00b190b803101080c010fa03008140003590301c0d610361070703541301500c5156400400c0c0d080214001044020641040c140d50104960049001c807a80d07403440b000c81c001d00108001c0c040c0380a070140060034508061580201c03d000c41781184105215041108025480308507595001401d07d07140304a4000512504031038240c808045034645070341c014000c1c0c400a060500301c60305c1d01001a03002c10312682d52032a0032001c400240b00840c1003600c40d4000d01940c40c0e401d01414186800079030584 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 843457823 1250 843456573 843456599
    0x90821010b0a0e010e090703150905010803031812030c030103200a140d080d14150d14030702030a143a1106100e0a29061b070609 57
    0x79041c1803406240055501003a529a598500034a041c0461014030206560b104c04449108070b03910345000ca0b5000507580710304812100c6420407034450b85024014445984c000007921381c0706501c070600c8079201070118805841e00b001042100707c500000410032040f151a68003031070481c0d00c80c8040b4120307d8492524484d1090103054226040402410304119404038881380b0102e81402400e40860701c10710b0b4641c412264040c20205880390340782c030340716002e20f1200b100c0d0319030081000d0740c003d0040b280000011140e40744400c0c040c2caa00648040c1d0032501001740100c96040da0b00600301ca88102461510b0700080c1030050301800c25004040c03040d40443c052040119480401c5e014520245079205030304e1610800c410503400c00c0100fa050b100e072181204101c890300484009541d606200d00d00054050048401403001071242d08102164040c51800000b500e2001d40d0f8444840d0001c2083c40440c45900441800780040d0540100e017030028100030a05000b503456070303aa4061001c1e10b5030300c070300498 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 843459073 1250 843457823 843457829
    0x41508060409020d02240c01021801091206050c0f030a0b04230c031003080a05030a05070e1f140d06050f0604080d0c110a03150509190609140109082101 67
    0x200d03048086184c010300d45036021205071011907001014440803031490702101d810401e54018203039070008a0840d0441d9002c02e0b01c1c4030b90000d00c0e203094440e007481120342c4100d038441310050950303803103c0201d4142001d01d015600c00307542c001c0d2150380b03034031781401544054618410f6450207186481a000c0c5a01c3c90041d00e4840c0542d01441d5028507102c514005409510007481e5201c031412400011000414100090420740081d135039140e100e0070011558412900c0140410060003114001c411030340c4c4400318155006008000101e60302c1c140302100f0b81da20f452103501105944800907040705070070307115803144040d13070802d88181920b14015800d001d003074072590090000590200241c1c9003181d101d10002e40d012132240100c01050013020020801c0000b0b1600100c440b640703480c0341000c2480c218424690300100442c000d04010010307051040d1840ca04e40006800740313848a10f58401c2c40000020300c5070940815008110407003031400c04810a0b0009409680d20f20074114000c10036200700461203041e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 843460323 1250 843459073 843459079
    0x7030b0d0206090f0901032316150c1410050c0a08060d080702030a0c0825092d06050102060c091c05010f05090d0f0203042907050304150806040902 65
    0x40340c0329000c02020760080e0b9291940f02c100410900380680790700018500940c450303400f0f415a0241280305801118641440350030070361090781d0f82034132241c0174004441241c0c00d5901d25659030ba051003003160303c810700f044050005074a458090380b00b080000340140c5591400340f400c02c12a11030841140292240c0c0800600041d503480c003090403840d00d010710080c40791180800518000155002c40c1c205070240d1001e44000d103904404020b404014402d0440900001013109a40b0700342d04002d44c0c1410940c05102c001030340e00e6007042c89400c008000c09803400480d2032501d8130148407841c2000513080b2802114010300030380d0081082082040705498214000504c407030030701d40844941c001ca20401d200d0031750f002d41d22049042c01685c164850300d030007542c03444050095120a02400b234000070b9000a0081103600400042084450140c2401c44202d40481104d120306641800441140104a130141550000003000101c07140c2e00c60303035082800e515450384c2e1010794594007007008031062000040c4d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 843461573 1250 843460323 843460339
    0x2060d0e030c0f03090405010806040b010902090301090c090204080106061107060c021302071109010602150a240b071a0c0a110f0f0703150209060a050f0904140f07030b 74
    0x5181015040103541409503000ca904040c46030034001c0c50500f0340b00341c50704150000104060700f0709050143c10b015080c1c0400074503180c10035a450104c4403034148545507080380d000c6400c403203a070b402390040d1400c29000b44a4204c015110050036000b503001740301d40d551540c070f024000140b107800f801e48000d629413100080c0603c20301c5d0000550b000d445500080f680001000c1c103400d0b0490451010f01000782c0a04001044061440140840c145041e0000c1066620068281020359440d80c4542e40c000651240440c201d003882c1e00104440c40c0e10090340314441c009040104506406902030451223000329098200365803280c1080c14000340075100880000010044104024066003031242410310329801c036886407d42891150a000130000c5030500f0390080c980400900c400d8144041803007803050f000710720304204480054440d11484558030b051100110751508100321010075690750500180041c04403030f06140d900d0781c444200b2510000541c074054081140244a4403c4522440c00038000340c0e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 843462823 1250 843461573 843461587
    0x503030a080709030b130308061914060409020318010606030603020f040c090504020a1214070e091e181603170d061205010c09060e0604090203090f010911030106060c0206 75
    0x2641c0720002454034060041140700040041c158810711841129018401c00e03098000345801010040c010b0045403280c051184020b20203c040c032010303070032201c81e2001100c0202a100100381e041c007860b0310600d40c0610110030014a002c01d41039544048a400008206013900c8d22019022038265000c0a5045081000c07140c0c20f505240d40b02c1d0407841460b05050200981d10030019080c2c0e8029115a8002605c159241000d405240120781d0b084580c203109403031519103203a000f0b0220404411051242d5000300c00b01d40102420804050a00c4800c0744083e49860081c40b4090301041600002c2c03a14864508142204c210b1007694500f0307a94041700c03013901104d4110071803902d03412060250040c0e03541c45000080c4410100c403504002407013140046280c261084000d440605039500000500005203c403d0f110b58a80701120280ea01c500001030301c98852a121910b41103845480d40d40c41d41c030b4441104244401d003980030340ba050085009211040d10b421003211644500000290408410300082d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 843464073 1250 843462823 843462827
    0xb190e07111509011506030b011701031a040825210f03050c131503230a052e05120d0e04020a021c0305090c0a05210c12030408060703060503030a 64
    0xb140e04103081c100041458120318000c46a462440e50010300400d584172124150b550300403542d0030510100d070050220035850b50312390b14010501000d0b0f00307601d039641c02c000504100803038090703640490303821005035080001e0590721411040140300641d0403043d40f442c211250000c090800c0f00001440d659400c07442c5001409a0150001030020410304009100d80d11814111003200001407c001a0b01c050011049102904880c401c003050311300f40310800b04c05480f09024106c4641c011542c564005900d0b42d480e190540f4803442054042d40380383c3e000c42c1030a000c120510360741c030559008403044e800c2c0180c010103890fa20303180c0b10600300200701c3c103035030b455100d140c9627019040c148014010f6032480200c00500c040d000600030360f0031020035941c030180b00a003030040058007543e90094411641c140d00f40030004401d081c4c84002c01c200003000e0b100c03290242006010007090401d002e040684202000b0114503244c3d0403034054601103109440001e06414841e00581d011910701070055450a5059442 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 843465323 1250 843464073 843464113
    0x50f0f041a0d03052a120d02040306060b03150301060503070b0912031903061203080a0e0f0d030b01120506090103080a030e0304180e0d05030a020a030b190e0711 71
    0x4081c9085641d00d60200541c99a8100301441072003030392456a180c15220368000c941c603c966605141c2400390010050b9064002008000c014101c01c8451304c0748070300042500070f4890340d040202005e080c01000540b2a200c7c6002c3c0d4010000d43d001d140e0005101c6060500704c401e544030740c1d5450303448018104025049400140b800004c00b60030481c01020307100e081071a5920512a048220fa03254034a0941141d16100c0e401c09808000c40c04101035071313542c60042815402a25051101c0e84d10b180880d4203800400c201e01016850b04291041c00c200200b000d0000c06041203a240400c0c02660901140c6c00c0c14410300b8401c00005000030052b90840d216820035821034016002855aaa030304080a2a800c00241006255840d442025403080041c3c0e07606550450016281c1c640c08078601c2d00c8501e030018140c0b90701114039480181c40d4692120100e001d0000351114a400c50103501e1045c5e08060104403a1081d81c0c8081400314903074484040464810489030011030440c0c0283c120103000c0c0d08944a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 843466573 1250 843465323 843465341
    0x6140411161a01080a21020718021b0714031518070e010308030a140708011e03061509140108060403050703090503030c0d0305010f050a051302071407050a050f0f04 72
    0x154210110282202c0c422034024203800a65840c0e1200600354100041d00c80b012407000c03907000e007481442484200c06559074a89000b007154962890030b1903010000240d042c0d07000a0b220215080c0754449210680351110038600541400e41d0340b1150520b41401c000510300460080c11000c5041950b45100031007020301040c0784002e0600440c003000941f90b52000d00c1e10701031030203a43e0075036881c100029000e0072100094610101e82101008101c09960090f0100741180c1000c446408000d0203041071714400c4005420040000d841c0010583c4a1940001c0c070310180d408000301000707400c011144000301480240300703411480d4014000140040c3c4200003911001d03200c2e04240b10001d4880c0000b03829900449101d42680d4048000c6c030801c0c6074103004d61401004060207003e4242e040c0000304840b007107140100342c050300484e036040340d61034080e60490b040540c000741038074401504004003076100d10b40d521035036229403000100030520b0b14107000700554481c8002c0995001b0002002440081c0140c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 843467823 1250 843466573 843466583
    0x40905040804080706020f100e15060a0b13030c052d030c10020a1119030320070b0d0608150a0f06051207050102150106140c0c0a06030614041116 64
    0x8000083d64803000c0055201600e5680c014118542c840502c0c03038608816145070002560400007404080781c004036050a480d465016822250703542c4901041029400781e1100425200003d0310800c03080760b0070b402009681c8500300c11182a0f658404200075465030440265452035880035803190620750716829513852401030143c40c3e4804c0800005603603080d652040758056040f5032160420803405444650405404440e80e8942d414103a030400f280031402d000007801e01a41214007140303025180e681c60104030929007120f0761103840340400c07401504242d5210000d1410582c2c0400d04a40c040b0390015210b02440290300e01c6d540d0303401080050507441100602c0340795102c10101d0180c41e44014050130509180041101c00c2c50f04000a20302180710166602c0d014103003006010031903000c40b206104e02c40b110216070312180000046030400800728142a48001d003010300151094168201d502100c0500f14001c0341c9084800a0100382c031924810503207918003c0000fa200d100c0307024000b1200900407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 843469073 1250 843467823 843467827
    0x1c0c06030e06010e09072c130312050106090b070320030c0f1902060d0b0924011403070e22140c07020a091a06070501060806010501140a210f0b01080a0606050409050408 74
    0x1503400c0c09447d84d010b07550030141040d00001c5c030091603000011000c50740103208003001150315040e4010300c40b807030500810000c0c0f280000c0f14410705114400340080070110502d5842c0e001d00440300240c0d640e10014404940e4001e95003828400b50010600c03a0a6000c0051070501d411025802c003c6194042c01c02d030541c0030359514003140251118114076106800c035080081000c400d899030604e480074480343c1541000314000f40d8140f80c0c03078084242c0341c1182c4542041c0c900310300d6130000944440c04810300c480d4144200e2044402c0c1021030f4001c020101600b40a10003d40c4880001011610039201e020f50004810001001202000d030300024001070456103004200c03403c8070008125920600c8180d6250307441d500180136248040c04014010002400c02c25041c5800c15071302c0103a4054000c112040c00314081f4070080100d005180607011105c0c4000821140b4903542c401c0009281d660720580c00589c5610024260101d184100c07401d8a0080d140c0da82003a00d00041e920250000400841d500002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 843470323 1250 843469073 843469139
    0x6060403060515040b0307120b27100c09030b0601080718030c030c0e060904080d09020d1a010509100b0c0111070c151d1c0c06030e06010e0907 63
    0x440c8142e0340030304001c400f541010020300702008196507086001e20301c00e40102c041042814240c02d030791035007030350310002c0d0403203e5440e0306005010140c0c5450701c12030b603050340621a18074480820580c10b10302e00c40004004003514818201c8400d449400700403e540f524030045203182d03000b402041c0d40b006151030158148440400800e00354070203640200c4914a44107014010012030425030303c0640400029000740d17103410000619883c86c080c5c000380c121007001800d46050000750b080303100000c0e005041304507004800c0c549120380940c2c034a2080294101c030380c0042250301d86510042d0003000311140091380136081c00c00800031903100d903485204540d6a4441c0c45803407259a005495594000e50034014840d10b040e034402c11004c81c2d01c00d48130030400e11544145030a0f0140080b4607100078152212103510700d01d0b9102000705044035a001c2d103101c070070600c0020142e41c55009220b1601a1805640786a66070710410409101d00303a8510184d60000b0b442840601c2401408242e03900c844d030b0f403070003480749 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 843471573 1250 843470323 843470333
    0xd02060c011b1412130203210a02100228030207080a0c14060c0d0c030b1305180703080f0702010e0901080102191b020103050408070b161b0c0311131d0127080306060403 74
    0x49100c2e45148d00d45010036024900768041c84200307400551f2a9003507240c104520b850480f2181d102080c2c0c048201217540046a05100b43d05132150164032022003030b07035a0b1000741c0c058800302c503500b404c640070b00c000c103600c80f84e0a5001c41d540b401a0b00d107480050a1034030a40c4101c019040c10109a000c040e0354074002e0241c3e9403101000c0e490142d0460000400b070812039041880040100401d500d6544082d0f4204005020501101c606000718034416807120030b2480100d4a20500840c400d03806244c0c600041085e81041d4014000d81c01c02c9101c1030414060b00c1c2042c5c0358503170b50740018264000e110b1110342c09075002c0d0300b0240d882480382030014942101680e4495a07a28242d03080101c05420900e0349010981240c452a0001071940c400c0004448641d660030890342e113400000c05051700151052002d84452205417038402c3d92070350920030401030580f542c07143c00807142403074010341c28060110140007801040404210004002441c040219100c0b50310079032018090a800c00010400040411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 843472823 1250 843471573 843471613
    0x9120f09030115180c03020c010c11010e1501260f0703052404030f0201061701052202100302090102030714010c09050a060e0d02060c011b1412130203 66
    0x6100225948820100040c107003110075804400ca10000800f90a21040242e03211403168071900c26408114608110740c22000380c012480d0f0554a5030804040d0080e181d0002c1c0044121041c40d0020080c6a50301c3c1171117991001d4000300000e1071203e030b0b4014410039203240e40990310300f50500140800407119050440c40c1c5185030601c8811078100840510800105200c0d001004d4088201c0700380e2003005584c0c40c0080c1c00c1c00b80c402402c2c05040301840038401d0003900080020031444205504071315020390054060301080751009444c11200c10310342060340601d21010034480d009004c0c410842e82d40f850a9009601c80312006065200900c071401c00520541d8070b04507032061f0300002140c102c178101c034060700c00c0800740c201314440c0052d1407052200561200c0b90795801281190318024040c02c0e030010503120f202d00480702d4001e508240d42c0851440f85080d425440302c1c0319035654090502852410140e038007034110010342000881010981c846030341002142406d000800b5180034905031a0034050304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 843474073 1250 843472823 843472837
    0x302120426040522020702030a0b040c0803032e05030f0106080f160302120a1e0303050a0b03030a2d0e090106020c01020a11131514010c050a0b04030207030605010e01170a020102150912 81
    0x7504941c4104010004c518181ccc0d40141160002141076080c1000c0e0014408240a403841541c1500da03012800d80c418515071000421000d4141ca5800c5001400715003c0d000c01d0042d0b895900c911042d183c42098001551500511303034410104d00383d0305550800820380081c802c805498030810100c44081142149070b2081800014000c01e2545241c0c0744c050140c440041090300307020b24140175a980c58a0200c101c9190b60110724158070381c0e516000c11b101c4040b10031182e178818192014445501203030888102d0040c0c40c01160b10907201e0780e035620101e80d0380c50b4045031640182c00c200c081c000064a801c0d103c0710320550091072012180709520100d812035a070640404801620100b0821000c9414a0038021401013843d1407401d402058803816a18070002d0002802c0010980010b81854424070903540510340c051000c1c0078550399449041d00700007081c060400641081e0904058202e0001031404800b503068018203e45d10b5000700340349e10b001d4000d1426042d4003c4001100c1081070450091490b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 843475323 1250 843474073 843474083
    0x120f03030c0a12021c0f140c04030201082505090f030d0c0b0711060f0601050702060313030e040912080403020708010c051206030601081b010302120426040522020702030a 75
    0x540d00d80a40003000300411070011690f103441080441200340d103000041040002d1508040303a80e00221169000400c1c0110440243e1a80b070700c1404540b6950400a2045034000da80702002c5490714000c0d0414046441c0d110f0f507000c2c0024986850050266010b0a80707010010507041007501410007003030522030758051200014440c2021700003000b82d80020035070460346d5403500c001c0d0b420b414111035903980f030050555011f04400c5000686280c0c40b8104450040394003404051300d90500e00c0402d6034020f45100120007055104c1100c196500740ba02c90707031806a8200355000910001c0d0042a40c1c443c0001e401038085000382400810400024082c00c1021901c51b6145903640364400b2604a9844c009000b003846900075000400502c480002c20703ea09200248a0700042d020140040c0c1c024802c40450480c803102c0c100c02c00c000d0000c0c004103208510060030141c1800030300294280703100c0c4503d003e41a40902c001c03010f24402000920350140c0c0070440440103141c5451500000e01e407015549046039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 843476573 1250 843475323 843475327
    0x12031d0f07060f05093a12020309010504230603010f08100603050706080a0615080415050601080c07140102180112060e010501110309040c031d0c060702120f03030c 72
    0x900d4803030400804004104900c0e020007046203404006000e44038041805208896110351852061a034001c80400c1440030b03000e000c809894a008105041104442134510790070803d11482842c5c0007204541e04400d0580d9500d140506044851040e41d001a080d07500070800c083ca04d44441e210400294040c1802070110703890760707103002c440c00e24007022140402d08085c24a80d080001590010f032620503108a410110348942d594031040008220715802010210b955550700211541c00225280c002c0c1e0140d090240a40440c24560307042e0b580546200f4005812900000c1c0b0000300d0501418000348103000d0110a015407803803a600b66048031150104070f0f03180341400b500039a00701380406094040408188452450495110007461051051030f06001c00d461405444040910031200c081d08028003c110510000c03a00070005e04d12211049000080d0440d80500c0602c002140100b40b20300070b2041c0d00d07120b910386c01d0094640b2889440107617842101101038019805001961007a250820055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 843477823 1250 843476573 843476593
    0xc0a050d140d0305090f0309150c10140703110c0a0204020a05120103050d0f0f0203030c031003060218130618020a030207120f1805130c121406130b01080412031d 71
    0x4c0d00b090b1259002011b69441008840c2440d181c403444a034103495039240c242c0d2103c510058041c1004a01903440413802e103491a00d13113400b0b001240080c000d4055541c104828614460700340d03550f1080000e0724441d82d002c204000018500364008000e44026850120704151030314415010b20f10003a0012110f94025800c0d214a480d8040c011104403ca24a0306903800540c0b000c000e03440e4840586901c4841000200003202d100f03100d1000c100440e070044003107554154841e1407004000480d28503034810020441040a030341d2490017110f00741d070f40800442c50f1015140d01800c000b940032140400c24903800303103c101d0102e0300301c40c080348100c00c40e51074060b0b04020200307005221242a0514176a030301c3e025071040c0203986401d45c2c11400803000f41000103203094020b030141c810f8494101046c801d18100740f507013178420149000403805450103076031100070309416842800c15a5624a00240000c00c81e80c0020301103540491001d0900d942401c00207166401c110703480000300600040c181d44c60740541f5440b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 843479073 1250 843477823 843477841
    0x204051215060102191709090c0a0e01020705100c021807020706020f061b07060e0706090504110a170c0d05070e030f01090203100c09090207050f0f0c0a050d140d0305 73
    0x6550b001c803091000d00b160603620b25400c190794403001405010212904502d4840a06400172600d03010001801e0070110314050741149050742c8612a40000608010000202940001269425158020a00200062500c03002c0700c800703081c040182ea1003d2000541e6603407a0740b2007507050181441e83d000d131101d181000750113840d24140841003d130f140c0c005c1040010100a40881a180006280f0031a40c3c40d0f446c5c0c10070310b028100820941146000b54a00000c2e1650800240030403500e0650701480400340e40701c50091503000708200d800100328a0000001c1c81407a500440b54821082d00000e41070280d09558030f401c40788101c42a50210b40340c0007030f44625280402980c802c1e012890300a0015440c2503010a44407485100d8020305a901d8400c250009070041622101911034041e0464807080b00d810328507600c100b807001e4156680940004800c01da2004117011100820150103c0070301864103050080c246015141500d201000d03500200800f07005125805200810f980c010407241010180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 843480323 1250 843479073 843479113
    0x101d0607210e0a0e04050a0204050901150f08030a0e0307080604050a03090918080a050c1c1e02030a1206090203041506050117040b040f050f010f0c03110d0c020102040512 75
    0x7400b40010481e202c0007a81d02c0b1410001640d07007036840421281c543e03241003032500f400d0761002076006092008002413100158010400140c6003030740c1001e40ca40c1ea480750109081c141c00352406a03007040003031041c1140078459258a901c00a4120723400103689055243c1407620aa501b01c407281c01ca8551482410341c0280128040c1050240c10003040300426030b10b9501c41c8602c0401000c5c090007003205081d150180c4166502060181d0541d60803084c01d620440e80c500c440b42c1c05d80c0200744207290440040e81c580c0308080d0f46140580080d0700c0c01410700000c0e2280d038030108042100540b40c80020032f0500c45c0e80007441c040c520031410807281c0d0f020306441314152409504514100300017004540f0400006945503504140c2290030b2804a80b03c3c1c0c100484081c10350740c809441441142c050a20f48101548214005005100200000c94032200200c098400071918030781c0e511824446c07210b40c078003198410380c2640302070b000061900c1c2d941d10103e00450343c00ca0341d2821540141054094050b100c2e40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 843481573 1250 843480323 843480383
    0x60a02040f15020c010f1209030504080f030306010c0809040609021903110a0215090a050723010806010807030221010f1a040608042612010311090402101d0607 70
    0x44805019582407009599107200084141040490b092180c1910b02500e503603122288491f5040c03113a41118100508242d1291082102070f00c581c8540c03c040440103c1a00d005180503520780301c80c3c0b070b41d580b101d89640d000070141c00c0d0702a540e5000000c001d99688002c00f007039509601c0c2250704544090018088801c004100005c4407010014070484a07404600920202c0d0126994950f036229401007610b01030300d0800080c818855070f4404104d180784d07408142d00f807402013402c85d004c0800d01801103d80100580700d031400708480c100802c00d0b01c1d000340c0241c20a91140000c42c0039005404150200e014820f03844020343c41d649010074060340410566030980c1051611201d4542490654000c212802c02030002d0100e5195444581a50b030b21701c940901092641034407251564040d0b0600e05001c07000b8030080350105240d03400c43c1c0d210b041c14040c0511450f001054800c180e10140c006440d03800c00c0d03240640041d90140050b4445549990142a0701d900030600e4441640d0b90380510b05100e02898 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 843482823 1250 843481573 843481589
    0x603062103040f15210207051c0314010815010302010804030c020927060105031c110a0c05180609040305090a0302030a0c0306060b031023040504110301060510020726060a02040f 78
    0x5c109038001c07410314540307200e44503100b005a83c0c100300d041080c02e00303022050411a08200c0d4110501065140e0800d28031a10050b41000403070341c0c0c404199540b40183c2090400b40e1b0844001003026600030003195601074000d080c110700305000369000818800088038001031840c00d21440040640300e42c544500021144402421194102400031742d451126145034543c0c00c0100800041c1544207a26500720400741e00c0c11920100e9032480d0054400301c0c10700600740199a039901600d4008070a0030440d0045d180544100401d03150b6440413100b5501c00c244480e0041c90301170740000141c03401c105904e031090103040524007181c150314101055902d02d5000301c0364060b00f80203000032003105620306011210f002441480d05142d1811900c1012001111320340e1140c0303804108030a01801210480601a00b20020090503480b8000c11080c0b1710038848090040c0c0c400c041c144620003500f80c40c41008104034036403540030b80c08896440d00c1c04004035448a06d181c0c001c2000c00c114290b0761107190241c81c3c09 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 843484073 1250 843482823 843482837
    0x21031d01080112020a0f0602010f1a0612060f060a02010213080a050706260901020a020c060414041119050d06080703080f160203030f07031209020603062103040f15 72
    0x1810009021800c18016150300c82219207400d0b0442d0b49a0410100a00308014444031550351040064001c00216907061110784c00c112010b401c580241d142c4010305e6000916060615691071000c0303c000f10000c022907002180c0b00480525591000003802c0580703202e0b0b0000d83d403070603109007030f000501040c0e101c90483ea1280c094000040d40200340101030303400c10310307002a2000004004585041003040c4200300415a042442090301c0190014422640550200c580d0482100d0a00080c0d10a9201e140800720001c0c2d201246894035400401516409480c400d042c0464086020045104e031800d120100e0f40c0000c4003042c2000c503005060050401c0d5001d86440303443d41e00d402c2c1c910700c140d0b0a0603424540024204156403019500e0041a5401404807034956001b50500f420a520204064010603c10b4002c159140194010700f561a40c0c00b4041c981192503850601c03501c400c1179480744584160482190b4030049082014100401021030601d0350039107005550149144c41c52503a02c01c01001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 843485323 1250 843484073 843484127
    0x2a03010f030b0c190816170109110f040b07022704060e0a0c09020c0c030f100225080304150e06010608100306060905090f070303021c05042103 63
    0x4180e90110840e60000c0780c0d00703082d07600c04585000d40e104420050820552190b00c100d0440d500160f007034843c50b840819404101c42c548815a100303501510b4142500f070709100180480b400d290003d0203c0c3d140a0306482c2403c00c5c0030720340c40b080c5d0401c0e00f14480011003c6001030551031301d21001003981c060185040f264509464280110301401000900a41e44a00318150002c0c3d04101d9400c0540e0851200c5841c1d544501ca401c02941c41803c00c1c2c0c1480c403902c1e40711159031601044410450b014400107165541062240e40301039000a8005120381c0800e51640d06010103400e0080205440b03442d86a80c0c81c0b0b0f0500c0c04d20603c11850024040d074519084184480310700016074641514001e0401428a42e02c0c20709140011155400081c001410001c1c0058085a139402c094047c61f407800c10b541e20311000c51942c9545400e83e120180040e40101031240b49084000d98003111140f41d460711514194a504400554000e01c03251200d100c00c1a05200c400d1503440b0151310690314881002d4245042c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 843486573 1250 843485323 843485339
    0xf0601030c14250f0f0c0f060504090e0c060d2003040807260706090c140303070b0601030209040903021b06090d060b031e1b100f030c020f062a0301 65
    0xa14504005070f18001000c0c0300c0045040801114441c1c0d01c21030700e4101c00e19619220704010040c940480704131a0100300450151000c800c1c6900365101c0780e840d00d00b403500c4c008080000d0400410150141d0007500511040b0303845100040c04481b280788004218202c1c803005162004050188603006000107000384000581501b049039200741c0c1102c442d01d481411002d0588554500034400061f06400041403010403440750082c0d40003501800810100c1541c400604100d0182c032440d50b0380c940c0082002c01d001a0801c001542c21007418940113040c000640d0210701201c582c920180c015a101100301032640100a005480e0710f00182d0b9410b0400a1004c003040c58428081001004507440b410003140507181040480d03207030f0190070024090540403802007916800358014182034190b24241081582c00c180c800d039108400c141e036462540b202c80100446c001c142ca0b1003c0c0086020f504409800c5180030055580a02500f104401c2a0030031000b01d011941c2840d00c0b40c80382010107000401060f4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 843487823 1250 843486573 843486577
    0x705040e0117100f2901051c0b030304031a070c120e2409101b02101808060a0606110601050907050705010501090f0b0d35030f0601030c14 61
    0x103004000389100c8014002e0500b070812681512141d00d00e4130b0981c4180e0804000c0c1c20540440074041c00301071345454600d0010021481040c0e00a001c10f0381003090111032295034440325081c0c01d44610006565480c1c800003800c40d80140c0c41903e0307000c0144c1c0782101c2282030380100c03504090141804003040c08aa42d4000c05140c0140b003a005111050390801c04a85030f0b2030044c03050858121951250380d404000b95025a04000100c078003e5007148030001c0c0c5c450040209008120031021003800221203036003044444010307480100c003000f01440d80002c11110b2141400d01510303124010740018039003100c169003141e190364400c500b000800382569002a1011030f100e81554015503400310142d5803107000ba54580701e010f00c01006980b91034000541d4200d030343c0c08041c840c42c20000510204509104024005510410203840150292105005241d14541503243c0704003664582e9a8980d40c000c40c590f981c1c1086408400d00483c6404001b030039a07042c41110000c001c1c03818a03074804201843d07484403078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 843489073 1250 843487823 843487829
    0x1207290702070e070e0a03211404030807231e03040608160302160c08191203050a0b0a0e01081c08070503130c090c03051b2b09050607080705040e01 65
    0x2007280810707840f03440740d282a01701c1d1401800300c02a8642e2454a103990030b80d03941001550041ca032020080c01440f490508041c2e04004c0c40c424101800c580342c2c000582e02c040011660700b10313a4074000e00000c0081100c41007900b604006070011440d10034400c04030000040310001c2c03d0b0010001400b19039001a14103411180c0c3c948280a0100c06141c140d00a120f0150555440f000101001041000d00340d050003d0f242c00a051b80c104a45412092900f03c1c0301d56001030007048090040d04482d4401d030b00c500d41c050040400818411340c580d012a0781000c40e500031041404e6180010310040c8000c0080c40f91410710300c1c4000b0640240c440c001002c01c0e00180c49401001b1001005ca030004011540c0604010b4000c6020741e507803540c6001080c0184030090051001c01e0400c000901106032541801c0b403094500448a80703001e141509110f0011403c140030141051000d680c405541a0b0340304610b0994882d0001302158140000c018085000c02845d010400000700010300c0b000c03014001003811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 843490323 1250 843489073 843489089
    0x610050f0a050d2703111906050402031623030309060a23030703060603150e1f080f01020a2d0f0234060216030f05120729070207 57
    0x100c08445005102a240c0d400702010310303810584441c08600c115140c4082c5240c41703a11203480f80c84291140b10b842d42054110b0b81c0908240020141c0890410340000b03078002d100130309699070104855015110a14941c100f040066a101c030725104080903500c01060105041300110300303194124000810300d2040001420030081043c0202c00b143d00041c2100c42d43c18003070141c042d2689801c14005005002e28814007001034180030b045c0502801c0745c0f4105003035414120200c02c051761649605620340f1614121220300000d1420700007480c1c0d00502185004a000c180050b980340d075a80c000600102c07a0301e000403144051107024040d000184500702c8261840c90a10a87d00c0f1261a810f9007005010014400b03c500c0c01c43c0c103a225100d080c91000d46d000c0b440100c01d01da950b1100340481ea03601c1c5035a0007440c099054242440402c0a603840c0300d42c0701c1c1c4144c3c11101841c503851a0500660800c290481d0511441d8406600d01044501d4a854200325108640700381d02e020301000703659101520a10403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 843491573 1250 843490323 843490327
    0x1f06050f0f240d05040302100507050c1005090a150209210705010c060e0303071809020414131e0507090e0705090d110d0312050108030c060123090403080610050f0a05 73
    0x2840d419240d0030748803100d411190800c004c0c45c160602a40b550300601c04004804e140200140050707001e80c1c1a10a1038060300002c1c84503102c5245944020325010309100700c0780c4120142c3c18001400d05040b840c00201404015841d4070b0307024207100741c20b1001e02090340c2448070800c04040e80880002d01004070b9000346820708501301c030350410742c0051101e103103191000e0000008110426070002c035040c09041c084910480307595650b0b00804101d0056015845440002c400700810701c2c035000c0c0803074507230000d03030300300054a1024002c201d6000d0300d1400b00040c2443c0c6590800c80341340d4100600c100184040c0ea020040c0380740694008000d0f208850249100c0e01c0c040b490941485946407608011101c045c0000c803c40380a81006085000d00f40d002501003424140042150344e00401514443d00343c04c0c000302a544d080c034101804031208000c7c144044001100b030f05d00b00d41c2d81c60109601070780c0a0b0f11403403050305040301400303821001004a101801010001010010b1900717044401d4850603140882e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 843492823 1250 843491573 843491629
    0x32007021518120118060b0303040801020a11120f0d05100f090605041a0306010e0705390721060612081b010911040e1f06050f0f 57
    0x84403911616a09100c590340800c01c14040c07815000c0c2403440540855440c80100310b0703c002c103400ea50f141103003288a01d008400d000c0c0040c02c81c0c3c002004140006041d0380c1407a40b02c00740c107400c9800c2805c03040c0000f6840d86030390003070207000d00c00541c8200c0d0340580b0074500450150800081e1160020015a0994070300001c0c00412a154440d4094849403d0040d40755681c2c0d203591001c0e01caa401a14031551a1491522000d006492491072201c000380c0034104070781c6842c0410300c00140c010b1590040c8041001100c4280441036880c0c0c050000316003807510010040800c0380103900c03074240301c0c2d0038903440200b061040b480e601010300050b03103008080400c20b00981c544034015003500e60013080801400003e4104010000000d015800c600124900040d40300140c0c0ca4240c44011001504209078141400c84500b031a41007008100010400c86850744500707200c0360840702e021001850717269680c540a01503807138242e91100100b407085840d6040c20701d00c1c0e00042d003403107000c2c040a8540c0480c2e00e055 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 843494073 1250 843492823 843492829
    0x16140d050715020903010603050303150a180e0f03030f1015080c0d20030718180b060408190302010f0b01021b01020109050a0c3002100e0a17010c03200702 68
    0x135024020068020b00c09a9902e152082d9247c00596a0310b407000a0031108000e07600700000300c8000c403200b4198401007100038805030f400a10041040d030300700c0c1c000c13900c046050780f10030002507000d013200102008142c503008140f46030903099900026031040009100740ca255a201c40c1c070603080380d4070019065494040ca440000280b800300d241d07581c11100e59040c0352810711200043c41c4035003c661503c04066080c0018841c81e203103d8060401d00981d10000d0bd558144035a000d450482809031016241c5912010094500000203a030b10559205a5803082e041640c203001d9a02c1001030040700784203132503201001075180c081c403034240c06103030a221034102e440f82c0c401d401c120b5071950080c0940b600d144032401c004030040b03914000c1391842e84c042c803c1d0003a1900e18500c0c2c2400b02c02c01c014139003003c294903403c0182d0314203421019800c10000524208040e524228504000e1103480f0300b403002d007902000d406088da41c481d041c0005051620000d40309031001000301c0710603074044001c49d640e1480d540c400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 843495323 1250 843494073 843494077
    0xa0219110c0316050909011116081e1b0c0a0315021201080a0c0608130201050c070506030a2a090b0a1209030e19030201090b160816140d05071502 64
    0xd801c0d0b00d03101c0e981880f0a0744600000403400d40b941030f07624003d01d903540458079003a2440400240d120b03510800180f90810820303000c018615119a1009107405000001000c10007188400e0882c0c100b00003035400702034140d00c2e1000020010340805081c500d06032000060501340d141c0b0001d0300118000203500240111070341280c40c801d81e00725900645584412101c0d9586ca03005c41c04844080e511756000c50300c1800354045500c07407401200e4030b0100c000d40c0e90044620340c10040203400107110310f01011030b4540d50f41000c6c51044041c1c040009181a0704a540c0d00404080001c20707901504008100e42d00690010741101541c0459004a54443c410300048400303641103a1402000303447e20f02410109a4003823400310700341c00211101c0740542101d02d41081a03625a2000030702040210398200004070078000174011400c0c0c0311001a044d10b1284d00d50540c1c0f86e0002c50000900d607400e030310400070401c00300c1d0640c1c00c0c240c48130b00070040c21281c50300c050304601c00c014000d08050b41140c091a00d01c805901 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 843496573 1250 843495323 843495343
    0xc060209030106031101022509020a202a030a0303020a05070c030b010603063201020c0901140907051905030a0e0a03020f06090102210405070b0708120a021911 70
    0x200800281c0c1d5a41401005411039008250040c0108050252300d40a01004d40403031000c0e0f9403411034030500c6c00d08880e000754450445002032140d030040b140d800245001c0d202d1141104400600048441140c601c08c0b00803015180721140f11500b5212607840c1c4000490111095060400503610b4000301026649405552802089626500e1001c420030980d002c0c02812508543c40c1800303c142c075038088288500184203c0b40c000324100710b40000c12404001010903040c3d06005546002c18140081000b0b041c098220305204c40b16400790f0003072400e08808255014000346003a60404070102200b01c0c1440c50100d000b001c110000c00800c0e500d0340035503c10446d1003612011030340803e91900d0007940b1082800e4115a060080100041582506008a944590031450440c0b0a03403018444813820b8040600240c0301d500c9401000328040000308021f1a005020380b4540391138200b049502480498011b20140409005109185426030390742034400e00b103d02414941002d110141059241901d030613 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 843497823 1250 843496573 843496579
    0x603100506041212172719111f032324010207080307080d02092706010f090909060e0d0f1106042a0902300105100c060209 54
    0x1c0c00141064107010740038900c3d2090031501e101c03000c00300055603955841e60314104000201400100324060011b1000d44140c00c1411504074010b01c0c044403481c003e4202070b107680300d03500300300b685050020701e221b44450500103ea031140340400300034000000300400388020040c9612062442c3c3c030203085140382214441c440c5d0b0b0506030707460551404454182d013001014800c0540c541c48001039440810f8240654036540001d40c0741c06090b9543c46c2859002c0307080c150482e0b81c280040c00030f40da1010f012009500040000403001401401c000e00b1408020308414144401c5460408605420035010300850f415140000350001d140e08041c8040e01c080f50104103640a5402e0075118950000280c2000da0703078a98cc0d0355100c44c2c100c40c07641e0b503c100030341d0301821014000590641601801c44c1c002c0c020340454000000307440e5501c00000c1070740c0050407420203440705903035096a1041c400e4004d103c01e1080c107070f10301010351400c8042a40005088074a000f0440b00c0043e80042c00a5501110100c1c0c40103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 843499073 1250 843497823 843497827
    0x5070503070f060e010515010509010507061103191b0e03010902090a060f05041416140f040e16090501050d060f090e150906010501030b011e0305070201060f140603100506 75
    0x42c942003100d10a005070071100f0b1071400d214110a81030520515200300e6408036058640c4000c0801920960030181545040120400184000680300c0c02684240300c00c2d0740404d6101e041104880742000300d80841804210301d0300f0045a030420025814081304403840c141503000020700000309016149404019400800c1d130030920124400c80c1e44014211030001c9920070203541c9400803c001c1d202200c50300400c1508036808a83c995070100300156020401d41008040280c6040c400403054000042204220402003070410a01a04510303050f40b16014401582d4101a865005042105180200c60401c2804030b541e240741a00d5a11890181c10540e0302155080c1d981e25502021b0406141d8a0380f0791301441c495900910040d00b0403e02032a1988058802c0740e00b17007001100189600307a0306a04011300030040c0d00d98070306030940e1410403641569000ca402d1814800103802c0d1001da901c51120310022003010407a01580350010360000300125600c035920b458182800c240704140d600266406a00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 843500323 1250 843499073 843499087
    0x11e0804061d06040c060306030215180a240e01051605072d0509070c06020703120903031d0607170a0e070807030302060f04200301090b011d060303030412080705070503 74
    0x14440d1042e417203503295000703150b1175074822401d0303480c54480207400c00030345802c3c02d041d50381610103800039402a00800b502d081d80d182c0012178082d032550084d095160f00d015030031048002c110f000808550ba80c00c000d0400218200002d06902c40e854082290344d171aa0600c03401c00900340310540080040c1c5550445811006650007085a03911419021000c1c4103d00090746043c1128036900c0340c15203884840080d442c0d80c561801070341c000c0608130200f02005013040c030b0b4109c20740701306c0c1007941c026507001940f9050120402845100560b120013a5403040c0108110650b110940000002e100b501c14500e40e103441c180c09001d410f02140306000d601a10340d000c07403450303c00169803040340e0081d0b084803070980b917000014101c06020b0b50003812860705000b50344c1c4103600007901c0700780c4160f018000080e06425512240c46a050030303041480c203c550b102c11440c1031120100b41c5070304110114007440c6103090560b190714509a822418405110070480040c400500400984060540000689660b070074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 843501573 1250 843500323 843500381
    0xa0207090c0f08011d0c070c0803040612050a050469051203191103010501020f060f040f02190305030901030e0307030e1909111206011e080406 63
    0x15902d401d030300000f5000b100028001211480700260b00380b00344600704140d2038900381028281d1001200707a41002c030b24407000404420400003400209200d9850510760140c0c0120007042d500c014003000111424802800b0115400300c00018800c2d03142c2c1040070000079411400f5000c2c00361000001100d140002003114418101c03e00d0501d2000e110700511840310502c0e03c0301c0d0b155006900041e0180c4d201e9a0366034014440d1200444d00700c0e240c400304549514040b05000c041d554040754800c0b14090100041065580411000c41a145120058103070b030326004045810b4000020405803540e00c408041d003081d512040d0000306581325102041800d9502c3c0d0030515a01d9008600d1240043d20703182c16611300840220540340482e80c0340e40e0310000d4040342420404581e16172440040e41400110700010741007420f1180c20303680558140030a80f01c0c0003a84c0c01844004000b404141480076400c14280300c0002d1807000e03010310803d414010456103a03418220003c2c0003442c4000b80440d0b4540319508058 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 843502823 1250 843501573 843501587
    0x1208040231020d02210c070b04031209050c031c0e0f0109080a05010504051606210204050a0905010918080316140d05100f0f0611010906140a15050a050103020a0207090c 74
    0x40700030b040e10384070000007a8154017204022100002100000e00409001603000e050260f045802450315208008004075408107c42c1d0018084800e5441440b0324408c9040a0024000021035403415007190480000094600c4c42c0640b0000d103c0c0d80d8803031111301c080e0b000d5149240034007642c000300c40d03030340e1441d00d88540202003d55003aa035502c6160f011076400b08420884c642031b030364642e950061304c14091b0103c05002c103614802c542103d80a100c00f01d02910350074040f00c0244940b0401103100d515066000e4200c6606032103143c601401608140302040c0e4110850b0307040400780c00c8580107900341b0301d02160540000340780390001c0c90000598509242c4c20360007460250700011300355084607543c0c1c403c8a003038080d984202c0340c0001210740304000b2503000c0c500c02054100d4802c008558880207640340001c075080c2c1c00480c030110b01014107016101c10244203096030311b080da28150300d81e81d0a1400080e121a010704c105810940c0004501462620901120b00101141030040c01010740c1c0c11005007030700c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 843504073 1250 843502823 843502837
    0xb040e010819020f0f0d120c06060e06060f03070306030606030f120206090601120807021f021b1804031107240207031703180d020304031208040231020d02 68
    0x7032199542c1e010240100352807040c11142c0c01000c15141c03410b444280034041d044001103a070300041d820041c5000c00d8080c404807a040c81c6507a030b407202c16401480d08004403080c5400a01c0c01d008071340304104050b29004204d664007850040455183c0d030b034040080300544415000140201c1c2444070000c2040a84a001002c541c4907400055561900aa04a035a21000c0307410320010b500c804010031410240702c8500058038041e40c04140707440350301e0700850300b12010075408142e03c2c105040f00800041d4140400191036980c00b4464151a8018002805800040058500d043c06800c042010036005000c020fa26039040302c281c0d80130341c0e07464050210218880c071110904066039004008a03034404541c0d001501e43c006480d54400e8400311448145070001000c400b4030640d04251280400002c10054a40303007813640c011039a90f411031800b10042c0780c0304114101489606000d20005941d000f640c04051901e070142d007002e4803055548610302480518120030b1031440040c0304181030034190010044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 843505323 1250 843504073 843504089
    0x40803041805060f0d020922080406180303080403120b03010914190b01150c0c08060103110d11010f03060b120f16050a0509180f07170c04050d05070b040e01 69
    0xd99603844060004070540b045099600a24850700e0b0401891b00010023500582d0451500c600100c40743c002d000c980150140a0f2015440400d0421580b6803280700e01d000c0c40700046503031918518641c1e01a0a00344090070040a024151100b0b910301e058a0b0702004010900400a1180040504005d010341c000c05042070014061060041084403222600720311145d44001240403503860000301110003500901140100a00110500c01003028034403240040c000307800c094280c55145241ca00300c0150040076450080300d482c032040c0b01103404c2c4842d4401684003800c203c8800409008124014807213a04181005200451030b54220511136600754031510310b541c450246038403000c4004a01d11440005140001d6040040030b221521a401800c881d00011700740c481d140b85031b01c2c03a022050301c045441580da03101c0c14017040902c2e940300848032030700316500b684c041c240c0c04c044a0f05813051040303029460060800c4803524007088000c10807c001005000303401707a2181d0b20340d080008420fa080c4101a0703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 843506573 1250 843505323 843505331
    0x6040b06070b100608010f171203040c0e011a040905091614030c030313051e0306160206070c050c062a06040c0807060807030b130c021624140408030418 67
    0x110280254080c5069074284421441c076245883c01112301d540b40441d41c10114040c0e41c00b050804262030b00918040c0784244a240c0000741001410203003203038142c0c8444035180c0d41d0b5441412401180c41141d041e00c000c100080340716590248860700c0c0080311a441c68203d165183e0010f0a80000b0042c140c2c0d440049003644c1000c000301e802c1681d24042d000d20161078030002c0000f0010307807902c0304506d91540450a03c5a800d80c460b02c0000307040580403a090b5510301d550050040f10a68103010b03907079100d900c40c1001c0207484010f03107481da03451b10400c44041c021140050341c0110588080700a8141c8001440042000302065640c1350715240250b81c01c60f02c10a0304517000c210070802007449419901380c1e40d1a80c80d5130361030a200710b000c2c1c81c0901c3d08940100c400510920500e041d40a02d04510310190010b04d2079101e007450481c0300e52140d80c801c0036200d24840802000e80c811034400c1c0444485447c14001071070b001c6807012441d1003144c0c0082014480000c00180340c410a207042a0f903565640c100b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 843507823 1250 843506573 843506579
    0x3120c0322080f0c0f01020a020a0c1d040b06040b1c02010e0627011202070c050a05060f0d0507032a1d03030304020409080c07091b030b01140306040b06070b10 70
    0x4a07103010a024002c051400a0010399105101d942c05809074031800d104958603d0004c107242801c91b808207902e030300142c0100740104103000f2544030040081849556015104c602e112380c14142000c0608024128010200440c14568440d045060b0001300140b4072900c0e500e92000560444004c20070480c0401e00300c08030340a1504e0304c50700340c405252401d080d00300d58100c401d4010301600e00d100051418002402c0020f5209045ea10240c88514400c1a100d00001d040404100101c419580482d104000c10010036800005a80940340ca141c4075200c0421252640c0000b9000b034000513041c0d003140e000f254107000b4801c800b004100351090007626807803004a00310108005080182e5211038065100300003140042c01c240d440244802c2c0030b09881c508042c80301600a08001d010360051a00c240c40d1003040ca01c003d800707501010340d8080c0d070600300f209042580018102e40600f0100c4500604040001a40e40d1211340000b15921030003005260361300c02c3c80c5000d0b505220261040001222003004c08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 843509073 1250 843507823 843507871
    0x19240504050601230f0a110c040b010914120102030f190203060f0d0c1a18030c0f060d060f0306050a0f1505060f040b030c0405030609070b030f0903120c03 68
    0xa40200b10603502c892480301c0e5000344103014907001c101c8145804080080825040600340030b8400f0f8005641da002610005110301741c40c3c07041000c04180301d0703031400d140c0d480360760303003020417002119200317503800340c03481845000111030820582a0409550001080080c105c01c00b1000030300c102400308648900d15007121648003280030440f0003540010000d0483c031402d00d0f18800303101c1d286210b00a280002c0340c80700306654000c104407840040c400c40c0403c100002400740f0609000701a4180c4c0180304050a001c00561030303c4030601568080d031000282410034030116001500500b0304600b03041603e659902c3c004008040c121900f0080500d464201ea170840564019000c00d40f4508036090207207424081041543c0c0c0c4042c0c455482c40c0401c000c0041c12241c1c8402031445030585d070550030785840c680800c0c581000384c0100b2a1901d60081d1106010001c1150156600b0001d003003058801a65400030311840d41c42082c02c6100f10041c10010003005480c03104c019440303419103601405100c1210801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 843510323 1250 843509073 843509081
    0xf030b07080108070902030603030c0106080f15090706030e120f0a0e100905010f2703060608060c070303180b0a05090c010c0809063f060d0201020a060519240504 71
    0x30f01c2e07581e4005600802003540c030340c0c0155401c00d0004040e640790401e1040891700312812a4400d003d2038002d0354045014800511030406040d004d14030b49010761410071121501c410003805410141981c80445200c1784400300503001c1400e400a1000303030790754000d0300820002e0b000811861300042421b1261206170800d06150381d1a01c0300c60310b951002c075043c200159a40c0700e02180171000c10108120144031560900004241800b0420041c60042c0c11402d10070140c0b50351380c20002490707110760280900100e10f10211420190076140018000300b41d810500308201c928074003e41110b0720b0074144584440305034841c600400c003079000c076400e0400f4040196110040e929003d849250140410740850410500501e01c08411503075041d0b02050b80c901e42c91000210508000c4c0b1184040d405003c516030450520380c0044003251540740b643e900e940000e43e142114040140200d4403840070800f03518050303200b5240d4020811040c400c2c0c0380038298918501041c1c4c001020809204100002c85040c60303c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 843511573 1250 843510323 843510329
    0x1206040b06030424110d050f0108062d09010f0e010e0a140f030a020d0305060103060b0403060f0b1035160207180906380109050402040f030b070801 65
    0xa03607802d40d6540e88900e4443c0c24000c1c20466101a004014814541c96104000340894400160f035203586003507403140304862004015414242845005110b10180020415807254690300030780c0749200301c941800c02c1107034071181e442e030300d1180501800811007042d040342c21b40041c035410801a0b40003415800f030a13185061a003ca05411030b10600c0302089514620194000072002141c40c0e805119001ca0b20f1a4000d855140041c0c120a16203030700250300d0302032076401103000d1030148840780c14204041c40300c4c40f0b507110042860365291024442d9150b203800000704084002c210b10744460140300081c103002e42c4034640342d04525912944481d01e03410300e09400e0080b4598103e1519031798a4a20081036500380b031f001082540708000c800902100f100c01c6c8600d00d03000e2040c0105990304503242c41d03001d888807442501280078030b403070300003d0031851303040f88c20118011484e00c42c5040002c00c1c0181c4e9a82031a41241e9001800000c02145040b1002c2c0c10031304481c803400c020511913964442c102c45940c0280 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 843512823 1250 843511573 843511579
    0x312020703170f070c0b03101a030c0a021510050420030c13030f26032806080303010806070809030a0504050d03300c0c0201090e130f05031206040b 65
    0x315041903010b403504041e2407900a0611100d113003c50645422151541d90380c00101908070000801000c40c03581d400f51402010010000003010200c05002043c6004c003e003460303403001000c90114242d074801c20903880c00c001c40004013515410f192241982000780c9005403070089061000400c0403e0290461200d900c4049075281d085441d4501c08001c954031511842e0549400c03000e001c408150007203c0508041d1042c008620340f01c4175182240c3d10b0003545601c002c0940d03014810020b01c0641c0c4200060b10501061780c080c041e85400191030002d140c150001c0186200120011074172100001d01d4501503482520361401e25512801c0d0300e5500c0c41038203220400144c00703200400043c102810b03d00e1001c0e1080c1800402c3d018090a0185002042c40c0f924800c0d0348800c01c046040440340c441e00d40c1d41000b5240c01070340ba0145800181c28884a889041c00c8040c0110001d400030344910070780c1c81c0f050f41c080c120f5010320342c0750700707045541780c00086040740c01501c00e10115001e80b5103071103085d100480203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 843514073 1250 843512823 843512843
    0x50705061f03080d020301061404060f120216060b030f2b030b041817270619091409040f080a1806110c04060806040b13060c090312020703 61
    0x4506002100c034045252160120300710712000c8006400c041c00b0300a81c5514500050b103d41c5040c0c4018016030303422080d07011406082005200150788224100003007211420300050341c070b640b00e000344000c2c420fa240c0868141c140302c2c038100030490300e41c204070b00544084040312240201c00c440e40380c0b1485100040f90340d070303e00741e03510035001ea03810756107658801010300780080c51542e06804541540c9002c0500d199000041d040e1000700540c0c09c1c060250480c1105409092031000000340c601b043d6911604810080000c94914040d62981d0407982c40071080443d06001c0c2d500c1001c054071410f03042c041c0039034003c1a18205071041c1403d00d47c40d849160000070845200040340c03510800c56001c400101c04001030444c0030300403036140d5210b500c01840c07a41e45070301210001030030642c01c0a1411035201e1107035051120402081d00b000411075002500191000d5083d115411032180184512000801c424108001c143e200364011910104580c06440c0d5141e10340c1c0c0c4002c0484c0c0b10091404014400808 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 843515323 1250 843514073 843514081
    0x15060f0a03060e09070513090f0305070201110c010806131e1d1f090201020c1f020c040506030d030c0c06090b06040b03010e060f07020717010614030f150a1103040c060e0105070506 79
    0x3c0c542d170125142c5140740004007123086464030b040d5081810810703070118400280034030031960310107141c40012104402800e00301c0314000008003281406004c942c800c2c211807082900002d1107500542a00306010104c400117200030b80000b02900071036a603050300611004101c8102c000126811006903a061108049690b50300f48d03010040050700b00580c1107100741080c441c2140c070307501c00d00c15081800e02101a0100c00e02c090091074807040c2c09003580202d040906015944c2c80008a940c10b00310780d81004100361400d100300321082c0844101c0070701450709040d1200140104240e072540544816070702807008c00c40c8001418203881c00c01000d031083d9800b81000983d43c41031407006a401024500c141c0d410740f0b0f942c81c41d120345698030426441d11030755102c1f420003e804068071085043d14040c0d02420f80ca00c000004951a1046000400118150f401c0001d84c3e5007010362042e40c050030b1180c01c03282c4030304081c20b140c0744142d864082d140104603a0181b00d901c56000e0000d40f4a1241d001008141580e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 843516573 1250 843515323 843515329
    0xe0d020c0409060b0603041b06030b03030d021b0706051909182c010203010807050a24180303110d140f0d0b03070e150a0e0f15060f0a03060e090705 65
    0x400c11030b054030910750b904520f030b405584100042d40110301403001004141461441d034000500542d12060626103441040710140c0c9011040e20400d203280100103030ce5010400906186106080002c0d00d140503030000455040c0d0814040c041c1140c0180103d2202d40649509552020103401403c90400d080344001c40c0025035500482c8029113500901c401c015016842005054081b903610795181e50040b0061088107000c00002008000407a44c8140c441d00e00082200111103070355101151444c2c02850107074250182c58101100c196034141d48a485503682401407070f03c003000404c8a41170290382c00031102148101d5003040d0350001c0700c429a1402d1520b21900703101390700058481d00b0041c0c0b00c40d0000907580c2c0070300003000100319051050311580303040354000321941c8035050214400c6941c0d070024800d107406004034503440318030482210059100d118960030511480e40e1140d504c440b00007080690115004060084884592024418a42c0b6001d104074a41011214040c40da4400c20381040359207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 843517823 1250 843516573 843516581
    0x60903080c0f0601180f0b0d1e0f0b07120c050922091a0c0a021b0d050f0d020106080102071e0201120c051908070c110303120108010905010e0d020c04 66
    0x19442400b142e584802035045542002000d80c46004a000c101d10030341181d91050080003214410304c0360801c48101d45c0030008608082c8514058001400914481e0719148206400c542c03881e08180c0144410b10145402a20030204440001c0000d01e542581c0c4088441801800041c030f009442e801d0030080340900380319011101200031140404424000d00c04410070b07120b600300460040f10703005410061184d40416005000d80110303500f420801c24030381326950110380c502503c078000071a120702a103000005018280e200c50090300500844450130b040c047c0005081c81c20f0740003174000b48003481c4d581017406d00b00d00a11501412040f1000e01c407442a008203080c0103051841410b007050f0842541640308202d581081c1d2440125100080c2052185a040c401d00564201440c05507500e14000400810030811100c0c000c05100c0710400105c0f440e40c06109903070520b1741c0d01060210b01d61355103034244d000e4080000256200d5103800d1880e00b662602007502042c2c1c5110350001e00c140144030091000030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 843519073 1250 843517823 843517837
    0x4032a0803070926120301180906060312170105030c01120c02070f090c03050604020f0a110319020715021617010b040207051e031303080d0b0a0b0a02010e0706090308 73
    0x81d90001080c401309050a034040c4040c4007540c0c1c0d07006807100d0740c07903132600d0070807550003035281400e1004000f8040b0803581c06010010010000ca169981d600d0880d0240101d40c0004103d03d840d800d11000060b40940180866410036950490320b0340d80713106058a5110b1360b8600750000b040040e1140c3c0140c000d800c07408041500e84116803480d0340d1100d104450320030b903402c81e08020703484050801c441d41d414011107800c0081200d0451802012206051040c0301d50050074061065481c90220918824415a29241e8101d11800e080c58040e82000f9140d046034002c05036480d09030110b9105840c4006003200c0306c0800328a0324001641031821100040680c00c0400440b0340d210520001d80340c0741e90010f0aa5544980c0c002c100300407e06900d0390908100c42220000c1d90f1051107005501110850b502c1e0803030307400170b02c02a607078034007007020720081e216040d04d04c0e422209203800000d604181100270700541078942c0c000c10081c0000a241603d694040c4034820014081c07150500214070410002e0440d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 843520323 1250 843519073 843519077
    0x31c0e060c0c0c0613330e2b060e01060504050a2c160b090f10050a12020d0e06091005040f1e060606230f07290103050604032a080307 59
    0x11551b540c041400d400e01210140504500d0b0440f03056040040020f54203007405905050b01d44024010120320310b98104030781c8040003200064400300702d403445407808075020340049003845280c0c511403415020300018400e00380141d107000c0028040800c00d1041d50442c0500900110b155071000c0d90f203929034820324a04116600501b5403aa01005401c1c10500040c400c9103a559120484682004000c00d100388032180602d900c54060000203074024101c90b04024a41005080c11100070071110003070040b003003140240c0e1b1401c400351010810000b5160b100d060700c10200c070810841c200c03c41094070b8095400800500704610168000350003008c031050f0150782e040c0c90070218445601c40400b40c8180d0790052011035151010110802d02460b10403d801c81c690400618104941d80004c019110320040903180755098120a04031404107514602a03c20703541d0306202c3c5513100e0511030f498090a07102100400c0d0f075200e140f880d48440120100c5c0d420700f02c2d400180c0014080e03d440405070b00040450003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 843521573 1250 843520323 843520357
    0x5150702061e030403020706270e0a091a01030231020a14070c060912170903031c02040e01050a1203080603030d18020a09060b0703050a02031c0e060c0c0c06 69
    0x1075070001c42c01c003852086000e54003c1258034988940541400258041a40043e15500c8484110350509010100300c5000c08410022951603000000c001c1943c0c140003010f030302412940000d04200324428034140c9008480c184042800c07401c042940f100c41d60000408803841c2c0381906050070066001c0c1c04a880c490404019010454901a6842d40030180c1240c1c40d502695040c80150b078044202d07009001803080b10400c1540c180c582103030300792840c6488155000b002903540100c0e201401a07543c2c600f402c03d05510100d580034800b42c00783d0014041c00503002c400400004580c074007140d90314100c5031900282e0704c01c40c6864800712040700c0010030294040c8410408003141c80c11030310620b2144020207038100c51094003441000b981d00950b92140c1c28140c00c2c100140000002d4004540303400f54142003040d1348203400c0b8016404c40c0200d03504018200c201d4011103020b849981c024454601305c4009554080c4e0710320580002a015240101c2c0c0141d00810b61083d041c14010010b0000701c90071041c0c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 843522823 1250 843521573 843521617
    0xc10050306191205010608010e150402060405090c0a0f0201090b070807090f060e040b0307141c0519120f0203090607060b0907032a020303060918011a03070515070206 73
    0x64001d0601c1d071000c001500f454030b5030070900c0340070b1003411b002c2d00d00e80b0000d120080881580b50340c0d81c0d11140c207090b841400300380403800f1591081c00b01c4006002c041c00300071480c504003006201e20f03000511110b003c5808168031001880c41881880310b055071090304003105441c0c50008987d4040005c00d82024800080310128a60141c1c840d418018070040c0e07602e100050003501031005a0790b64070303105402588411409c0c03203110088564115607620946260309030405031816002c00101e195006030090003800b105195401d4800d61000700c00b80190702d0010981640d10f000c803040c0c6081002680140c00900581149103443c0000380140d5008020205000507442c000964500c41500d440010907620a04010354007400d10403000325030504025210026250032f000303512444014000c134480c0030514002a42804080c956640c040c4170310008100103e00d0213107018040214080c054031a1051041c000b0b0710345400f503403001c51030701481141c0d03040041c240e0902042e504a1000310301918018a6a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 843524073 1250 843522823 843522859
    0x3050f070c0b0d06050d051b06070605240d0b06010e04110309010510080703080a050d0f15170c01050d09031106040b01030b060109030206121503030406110d020c10050306 75
    0x10000c1c00a4405490343e41c1e40d000c02d10700454000751300240c014a00e040343c10001c2540410b00c1800c0e944000901d40a07500d03c40001001c521500a00a08c8a0b00e0401800401c005280d03420305410020b00c4100c071603441035403c0200001080400819080340140021081c1d44035044019148001620208122640ba544402c10390411519550160740d200300300444100300e10010750003012400003514251742141c4503840d0b140300360b110a000340f25000410152000141c0c1c481c8451066801040054000c0c81c6928415410b852252115145420400752003002c40442c04580d200e1050b10f07090302d01104046440007804143c81c090703051181600910b51100428040903115912405480c0e54541c19841c040000da24003812003030401c8201c140c02c0c00142c4481080b1202d00b14040b2103c074207541c03507540340d1000d503d051001c0c41c2c05020104000580355044110354180d8251001561545447c902e03080381e540c218aa40180c0c0107c030401c0c0c0c0c01e48607004800035500b11201604d0b071803800c0c8102800c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 843525179 1106 843524073 843524093
    0x51e13030803150a090c0201050903031608062803140a0c060e0d0210030c0801080a020105041205030c010203010f03051504020114160b09030a090e040b0403050f07 72
    0x1095900c0350900703104200a070010120501c4d252500300340006090a1100d00b07000d50300741004600768400c04000c3e01d10a159100e841042c074031032000c1c1102c0360705018281c0f80d0010000c8400809040200c005034206100d200158146540740d8942080d03002510303c500580ca4000011640c001001e50603a4021100d05142400c440d583c80c90001e003080a400d01c000354001c030901c008502064041d00001070308040c07500d841500c0d030303038629100e6290300c80c011000380080d10030041400f85015004984854501650031641000d01e01000035013243d0080c1c11400e0302c0da035240010020000c080140001400c04100042103d06050b4000fa040c2c106c1000050400e91001c030344050400d0840c40518400c54001204401e1810070b05d00c0c481d00d83d80b1800315400010514040421f0104202207020700465210507901d607281d4450b1000c86072a00f000e580080b08180c1001a00e0115000543e = true := by decide +kernel

theorem cover : BRFrame.Cov 843345323 843525179 := by
  have h0 := BRFrame.cov_init 843345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 843345323 ≤ n) (h2 : n < 843525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
