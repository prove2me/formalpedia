-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3520
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:53:54.271961+00:00
-- url     : https://prove2.me/submissions/34931dc9-30b7-456f-9660-c23ac7ecaf73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 632913669 ≤ n < 633093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 632914919 1250 632913669 632913683
    0x3070c150c050a0311160b04060c060204030206040b04031a280b1f0f14161a0916080a2a030c09061a040b040e0c0f030f070e030316 58
    0x46a400045030031816030740014203207000b00b6403d60141540001d143c50051200c074100d4140b100407444025100b0058820b07400c04030014403050141c1d52003030009c0b800c058041d80015040a4881d000110254460b42c0100602c0000080c01c00402c43c181a5207100385007080401007461420706c00560300a034078200050300031891040d9051050341786910004255001a04070041c0b901e4402c07900c00080c000303840050101e6091000b12090a1041c18008100c0088d03000881c20401107003a24070240840910448101110150518110681c14122849900309000405078a0607201c1c48114021954200e500c4581080450030003060301054508008d00000d0b4062101e4175404028214100041d000200009490301e00041c0c1d1174440c2d08048244c0d955500c5d00d00f424486000e041c10303284181d120b0303507030165401d00c02009681c4050158279441101c440364a450451240854026030703008450101001c694001886042a409011314461020690055140509040c2e4440d0b0b0003001d008010000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 632916169 1250 632914919 632914949
    0x1203032502031222050d03090203011a030312040812040c030204051003110909010f0e01050405060f2a09121f150e0c1207021b1009120f0b160e0303070c 67
    0x81c00412a0040554024050b06c151303c0c600817008006e00840b101c1030303200e0742c01d02200c04404444a5103045045600800a518000500d0090349003114000c20548103504c0c00d04c1030200c034002d581200c901c1203100307a5402451604601c100411a000908130740e81030100b1541c01c3c80004d0603040303002321500048820360700039901d9450203400f40602c041c12500d9141800b0702c0065407141508500c4c015807003401560151754401c4200181814226100e0001415054400304254550202580c54010341c00c0c1c031741c0c81d01c180c5802081303019101692908035540102001da804002c140100d800861007d03100380a054281d404a0810292501510310801d20f40c40105191488002c1100c1c0f86100e503603140d0000e45407461000c0e485000740050550000086441d80703034a403600001d43c3d1742045140c2c0b5900c020608115610810f0660003000310351200c0c6080c401408200e00d4540280306003143c40302141c0203c0d185a004100c0d40603a40e2007030083d4003c1c080d8034001880c079171141c0142c1d42d04044030300c02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 632917419 1250 632916169 632916211
    0x1c08010b0c0a1704030b010e060603040b040f0507030c031101020d021b0402040512010c0f1e030b01050c100507021915020a0909111b060f1512030325020312 69
    0x8110b45000e00520034403c019208000600c4a03002c0c0040b41d0040000c025207031f80e41c000c0f0200070074007294843d174010001c03c0000c3c000380c0b03028841c1c1d40080c041d0b980c1d02205641552014641010740e0800c2d10b00c0d044240c0100700700300311143c101e0201c800c00c1c40a01114cd030501d601070f41d01c1401402400c4480e404d00b807a0041c98550740d05030b43c0140002440b120100000d80301a5000700303503001c0c44500040b4265900d0b01c80b18003441384062000001c8600350034070051408214010100c800d181c90401c80104134058585008011821500c85426170000720790501e020060701d072402c464000344840d40040000030100300b00d140100310101400f40c025035514141c0c241180ca4512540154001030b25102d1401040d00c11030025000010341107085030010081007200310b0b078684080f5100c99600d540900024560f600e0030720001000a0098250344403501064000c1d4190340003140c83c805070703407090710b80883c449074940e411000848241c00a1441c1103100482c401c0801c0000300b0f2054040b224178180707a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 632918669 1250 632917419 632917423
    0x161d011d040203010b040e0106171504020f0304110a060f0c0825030c050d090302130e010209030f010b1c0c060c030c0b0a02030406050c090310110409060b0304051c08010b0c 76
    0x8000d1000303200310341c1e030742e11465a403440350032500543d41c60781619800800d40b503005190b0420882c6250358500c0881d501d10401180c461400412660025000d01460503900129006540528405c001243c18840c9480a2100b44e554035070280d0104031b4135082040003290010441e6040c00d42103505c00ba90340c022400c500040202904006850010200402d403d041c4c0c4158440c81140c0700b101502c810640c0301000301c0c5c1c0324800b030001941c40503d84400b600340c180c2a6000c50050032110002508040745480000d06203520000d0a0400b81d456500d6030216103400405174441740300d403400b03400324203c484e01c1d03541080c41180200c10034030104030b480000f8180541c8820a11a5100600b16001c0c40c0501c030381c901a4005503000c45011707041002142e0030840c00c80a550b00e03000d0160040c03a00d1709418140501400d9101e070700c020002340400000c1522607560003840041d24004410030380c3c0c2d05091400602e02881e19801d0702440860110400c01c49a110700c041d4112182c103050301c0d8a594400c0340c914 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 632919919 1250 632918669 632918717
    0x402030106080f06040b09010908040512010f05150102070506071a09030c1204050f010e220207140a050615011706220f0e03070b180304081203161d01 66
    0x3981503c101c0b044041204000035049208a01c03a071900c00e29500d81c00c0980d400d850361000024000002880300388180c0c1040d090320b0710154403e038000f14048104d6002182100c50940e442c040342c01d0304281740b0f9030719601003000000405003581c0240ca07021094075130705100c1c50b40381d03008980552164085a01f500081013900c0c2800403680c140d41d03540e1982a01038880d60f00900c203040c0510b5038004078050320740c0584808400828050000700521043d0814140620344003064214039640c01d10490380405c207100880020f842400c80100400149030411610703010000700760908030100b400008595980c403000c00084100712003200e000c5038864000044030040050303950310f10120b8042118144140540015041600c9607130100445422464500d03100d1103000c0002e0280399420700030580340e2440c24154601d5100c0f081c103981c1403a03107c403810b130b007000700320b000326024000040184124402c071600461302070b43d02c07810640d45517250b40c03c072980590300c00644507040c01081e420002844407034003595 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 632921169 1250 632919919 632919929
    0x251401110702090f04020d080a08040c0503030703091502010f141e15060f2215140f1b060108010204063b0a080a051608011e021809011206140712050402030106 70
    0x5441d0340036180002d00112b001c603401d81e040d00035024001414140441150307109074069554048050500701803800c4c0700301207a0513504640d43c03204803010442540c4689014500700300c004024505001c44406130121034001400c1414038010284010042130062400c2506d905a400c140c948944010f11400c0d0b0144e240001010310240d07a440903443e000c99010702c180d50780b4007a0700c440c40415800c1103c0406e0740c1c109040940008202c02410034601070058000e642080f1000f440e504441281c450400b1820b80c0600160f03900840d042c041950402c0c08806603100d0b8440c00840314005a20184683c0042d066100030440740f848800c1842e00c0341200d0310050070f84c403411108950701c2c503c2d05503038690401e540409007041441d004221180180101002d240702c04402550440310501f194009501201803000001c8584001015584588022034002d0902100d80c0510707440d00c5c1004000c0c0c52480e60ba02144061b80e400300020250445041c1d00c4c0014500070010f0140c0d120300c08240141840d80107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 632922419 1250 632921169 632921183
    0xc0c030c02060d1d0d11031b030706020a0801090b01050f0403020f01120516020622120504080d050408250605090a0e0406020a020f01060b0f251401110702090f04020d 73
    0x110804508504d10342c11101c100f044a007442003c1004480d00a041111580290010008507601034005240c040c140c001901c1920b1038010981e0754001281c2c4810742100110b1031000040040d1a40d52103009020542820514901000002c0c03a45c11403080d408001d1040214602c00c10ba164880c49540d95103044041003003207542418507060003885210841280144207030b40000364540c0000c41202c0c070040203524079448a1010340c0e40c3c400074401d1800d00c4c00c20040c040c48001100f500400030b4859a9a45407103c41ea40c41c10314803401d04240e6100780361182200080801e1003110b0018075520304031111031a1140d00c400780c0e035002600384c542c1075201810046203902840140003013607009240b81e24442c1c01700c1e070010a208210b5401c1e91483d101c3c00000580901c2006910800c01c0020810300c50410031811044070250f5007085880034012050f29070b501c03101ca000d42c019101748074002849c0302004a4074140b1041e68000303031039030f40000c082d80940004000850110740300c0b0403214039240d501100b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 632923669 1250 632922419 632922431
    0xc0519121802100e0303041502030c0a050c030705180408030903120a0c0e03032b14010f06032d050703020d090b180313030f03030b060307050c2404030e0a0b0d0e010c030c0c030c02060d 81
    0xdc015030380d0045c1142d018801d0095020003c1c0301c0c0b401d4501442108a071003185990f40e5075545405107503400040101a10f40006c200c030400c00b0a43e00c084922520010000182c0c0b41d2604000420115040380c0642c0603a2080011107042900714450f0320400442144001c0f1003502c035800314000d800c04003c0c050054500c0400414003100050304001034440d40da604021502003402259218041400c00b0300b10440f072140c0b08514054181c101540c0b0840c0b81c100946040700b030030303030040403110f00110584040284200b03100000031225010201000904019400d0401c11400003c440060340300082000b14075500e1802010700980040c2d5600c98000d0160b9100d107401940901103501815040ca100c0c001c1540300c40361505626042440c1c64551000030003e551a55400d5540031414032003240d008050300300004045c0c049074000e080b2400160070100d2030840200c8070509440c1038040c26000d0500301100a003029512250041c81c06400d0301d4490001051400400d4451080c1005003800c541000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 632924919 1250 632923669 632923673
    0x160e090c1009180b0411091f0302070b040602180402031b070c030b13031704120e12061906080a050303160324060f030c0519121802100e0303041502030c0a 68
    0x144c4040c60b04a01507a081c0310040a2811000c91032103000b909a0703000301291044503801120301c1c00041070340517a0400600e0003440b600c1d0f0350000c110031101101d9558000034041c0d103040004d0300ba42c0c10039000b0b035029400c0d420426910031403840e20726141c40780e005001c5010028000e0802114000719002114100c0c1805d0070292240e100c4c0000d03a0640100700c40c098940240544180c2d244d00c5180c200300824240b9107101002c81d513071006000350341d600038100041c080c54a0420700281c0d000d60740600e03c52001a1000c05c00c00c095400d1a0b00088554000705078900200c3c01c00310480354490810701c0c1045040e136690030700350010314080c01c0c0002803045041e00d6007550720384110064207940094454190080398840c040701500d00410703124000940601500d00c8070a0078500000c0d004205081c09030b208406078800c01e00312211070a000640d9488482c1ca5010340c140cc00c44010b141040d445d04601003201c49011980c0c9104a00c1954512607200740200304585c0b0900a4a41c0b005003403041e00d007004c3c0d0034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 632926169 1250 632924919 632924921
    0xb1504020f0406270b1e0c060108010506040b03010e030f0f12010618080f0a030509040204031a01140109060203030c07060603050a1a0604150e07090f0305160e090c100918 75
    0x405903880c18204c2800b10990303105020100d24003100d486174a52440c0c001d20003040b6000903440301d04458000c0c01800801e0514030b05002c6240a0080000000351502c0c14404200603200c1d0700034202e000c0d91400460400e44a40803044850003400c088240f82d40b60564035030b10804c1d00c00c291075104030f00c440c500007007a500c0d4000c01c2407200f6040130410044554030f900d4903e44603c02082d400e0010307400740710240d001a000d91b018002240005100504240d641e07102c1540240f550662144039042460050001c07d003a454070031340546080c0780c943c2ea04d60602c14065035030300c40941514800c1001184c8041005040e400c0302d000746500c4401d0b41c00000303403480d059542201d246020004282c02c0000104035040c41d02c0340c0071210703070100d0100c4800ca2030103400c84000700c40900003508103c034034800440c03a210300c40480c1e0001d61003040181240c0b042c2da0182e0341c0c407000036040320303241c01900418000c1c2550000341890354150f04403454000c2449004095a0b203001c598070600c1c02d926030110510b030041007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 632927419 1250 632926169 632926187
    0xa0c0503060709140904081e0705010f020a210207140d030507030b0117100e19111c1d1b0913024024030b1504020f0406 53
    0x800c0c0e08581440d202c08038159031555990088100c8551900c6428185143c07484c0401d8100e801003166a240041008034241c040014031840c07501e4041c006060010842c0c2441001c2001058020443c10070503000c0005003a2003005141810000038a01280701c00c807a10f0b4100c811150f4016009950415141c0c4000c1d1140c44480c003040201c0d00e03080005444034024000c004900c0300503580c0310105088000603901820001e03182e5840fa0803400d00205842400710440c0d8055442d848100700007100602068069440c030710044c904450303060069100c0c05522400f1902045c20800c00804c5512842c44a0000e10000d0420080d40b0301c2040f0000700c42c0c52107030000700d40e80075042e02c41000c0e0f03654090601d01d0080320450000d4000c400f0080c4001c40c6400301a840c0e040c2502a42c0d620010010f59994038148100d41c44407040399035986502c0c1d2000d50400841c56960b20586004c54051491030300d40c0c100c4050001d083c0740805041031101c41541d5110340c1107801c03d18125001d1a1944e44500c001009950 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 632928669 1250 632927419 632927429
    0x705033301030516200705030f0a051b030604020f1206070e04060e0c030c0717070309060314190c03020d0e030301030209010b0c030a0c03090302040507210b09041e02030a0c 76
    0x403070f26000ca181c54130a2280b0102051150b00c80358071517100c140c440e200700110400d00c070003d4091400081901e503014800c015446504100420340350b803403814400d0a1507100d10384040740c0601c40501c1e114945003c00c1c20365003e81c04882c0680d101a4420110308046800e061800e1179000b10802c010300c2641202006c040000251010401c907a211507000990110903200e00f48146024000a1400100c00008012040c828250108100e0124500d040e40b5040100300310040743c1020000e11455900d44540696034050f00a020034509052103101c1c0d941c0d040a0303504241c0d03030312040011041d40c000c1d01214200c0e00e08035001c000f00e40344004056180d41080c00304038800c0d20018000184005d000041d1040a0207a40282d80781075205078080c6d031814400c7c0780450500c1040c200000141e0b96601c5001c1c40307021592201e800c902c411801c400040303682c20b2750900200707141c1518041d641d2203028155501c10750200000580750344140340c250b800b00b901c1d0802907141c41000c2514082003101000300c01112 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 632929919 1250 632928669 632928671
    0xf02120106110304060503240a0e1509040b0a0905031920010203061302090409060903020c090606161103010f290d110906040f02130f051206070503330103 68
    0x501d5480e4100d881384214420340c0001101070000c110880216215401c0c081e4005180103403070b6031b070040484d0a16240350301c0a070310901c640c0108007580e40d46100091070900c04a40c4400707940b81c643e841d2103400c10042c040f0805650350703001c076504000041085030800c9000440064505044200042103502140400e6a1211164108005040050080c0c900420300240800780700601028128001c3d0480004190300c0381d100c03911040414100d208600089000f540a0017080c560130b42803010904028040e640107260801000900b01d20300c200d0441400c1e40221181c5540070a980028003400320a41c00941c2e0310302d4040c2001c1041840b008100103d03040c2c11408401580310402c01180c0c4030701110242080c0520542c030030040c60f101081680c007440060000070f0942d041200d00c022600410340e041600d4520040501840d420031180100070241281c007001c100042c03482140d101c810260030704040c0b100c0840400c1c0c2c4513010348001d81c03a41400c0c4c110080340302c503c0e001080280d110400118042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 632931169 1250 632929919 632929937
    0xc070512030703090f0b0304020d030210020304030c0b0609190c2a05120415050a050714070815060607020108041a070f1b0c05130b03030d0b030d08011d0a0f02120106 73
    0x46031500031750341c00c40d41003204141c1166039607024090004d10241085086006500d00708415540b80c0c07001d11f006900a0380c07400c041e006d5614001c2000a40580200c2c2328442580401c22000b0303280031200e030850740804000c07d2660307030100d05541d21000c0d5007104443c0464401051094400300b101196203602070821034403903440c6451000701d00c3c0300340c1c0540104448203002ca030b403601e40900e0041850b82c1581c40d00524054150f100c02414980d00b881345005e0b030b003007040100089035040249008003111050a103150741498000507135144143d030b80080c140010340740001e042c840b1410700d42401034010005a143c62500701c0008200c111007500c090b000c682d1a4400072001540b2249403240e49070f024540f06000b600309010800c05c004000d0001030020344407542004aa103003400500f000300103941021480c800d0721010142414041d01100f400c010341d950040200707c441e0303503100003801c01c00c460504aa444e40b00c0010040c00d5040042c4c1c544e2360002804088440301039800074100c1d1440e03500c100311 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 632932419 1250 632931169 632931179
    0x7020901051504090908040510021c0e0f0913080705010906110a2705060c01060f05010c1a04030203091c030210050114210604440c07051203070309 65
    0xba0005112204115241030000780804141c0d50311611006004100c4142410340e25000115010b41d900001c5c801a000b0110f1042c1c09120030b20a6180704c0280d04000c44590510f50100d0301c86200800448d2054000b003011554003070000d240c030703490b080c1c000621070307514031003410b001e4040e128031071040701c115203803d1000420410f24410b40d00000a070340d5500002e032902442a5001c50a1480004d080c00525880003980d5034400c0d0007050145842800030800a05c0c05010200480c002e5005074140040b54111600244803182d030040c414068840e25403050312141400ca1550045850440d0080f981e84250101485031400b031076400741c4241d00301c820b00c265540c108011f6445c28460410048015240140e042c50050076000e218038100b24030764410000140f10528101003038038280c501c202d9101c624800568400d02c114180d40103209511440f484407002c4c90714000c0d222101e50b00200011910ba04142e109002c1c05c40200030040200401c200f0907003406031254420304003100440c09401c80010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 632933669 1250 632932419 632932429
    0x303010b0c16051e041410030510060501141309140a230105210a03080106110316060b0f040905010e190f0b19050c0301170f0607030e0f030304080702090105 69
    0x19900080c00c0512901130703402070041d1101d00030781c20682c000d03102c05004900740040f201241c811511394111007181ca1031750038031364100311600078514041802d1100c10f22540c1d03000001007540024901c0c1c030070342c0e48030b040204050307210407600030780040f60034031202141c0780d0501080640a0f8070b14080030032044170702189452400503041a1200089205001040f036031070080d00d5a03d0856185ea041100122041c20480c20486212412008101c611300188422503100400c00103450341c00f0025031400350790100103c0c2241d002c00004140c82c6e200c581c100c2c03440e01d4010000040550161090119031a207117882d90107000d1600c2022154800d001613030401c58400341a04c071160340c0180700506980020703140e0082900d0b0003020907862074810440d4141c45641c0d44225440f400f4041c816503100d505100308050307446440e9a880c84680d20607503030300349110070100e00c298010300b090800280c2c540311118080e0414200c0002e444040c0408010007080c07180200040a0403442104c41e80c0740c40e038071402048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 632934919 1250 632933669 632933713
    0xf041409090102072607080316090503061e070302040302031006060e040902060712031e1406090106021f0b1801030b091f05100f170f060108030711040e0303010b0c 72
    0x5001585c102d41039400040ba402c85200c0e50441000d0782e24030b0b11401d515a44100d03401034030044400b03c0c0d46c040000c0a01c2c0d01032030100103064228007078815400c00c07080681420600e1204800d142d18000d01007210940240d044070300940d805030645424640a440d000c004241520401f0082803c84105510501c2c240c8034010485a0007840f4a0a0400c2900c81341c9610100506039000c0c143d40f448410003042100f0f02411002005400c04541c0300300700c004070b0036001c20103030030300d8081c48200380103024403900441c0c4244071002d8032100300f11444140404030301074000d400c00c0a81040e9004400c0c0200302060608a044e203001c1d0b903201c0710380d441e01450150703547c2e124901000c0340c0c1c0f00c42c134000d8900026904191307000440d8880a5040e07a803510401c07a10340c0c8c40c03035001103900c804112100201040c01c1c010a0f0904000038041c02540d80341034407a5440c1d103d0044010301c003003030752030062400c1da0321a03000384010b141c1c42040307036260768440c020004180d2003c0b200c002e50380f254180e0000401c5000c81d0003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 632936169 1250 632934919 632934923
    0xa021c0503090709110d15091820010f032f04170d050306060d0e0111030403020d08040b060d0218070f110601030510050c0c010c0f0f0905060307140f04140909010207 73
    0x1141ca040091841b03400148104e075020100040151400a1143c140e401410040000c0e0460360070b016035039140003203070004680d24644641c910b6407983c80c8141e8000c0b8041c4200c1405060114103c03c46001403881180b00804e0405003100c0510b60001c82c02c0e0840140058400c03010b80c2c1ca01c03403200746009035503841c17030190b183d40056001c000003441070074090040d0bd150200c03a100443c04000120a15094916035001c951140d0004420482071580c1007025403c60003560130001c5407410705464141c11320758014400c074003400c46540c554045484050040d0048203144090407980d0421240080004101c0c440320307000100ca1a441603110b000101d4402c1c122a44400140281040000c088000d4440200400c01e007010500581039414800c1c041c40918007480d42c1c6850780c008000002500000141442c1c0e42080281c11062046442e40009c07660042201e040440303504402c207003203440e28450510321a0b0701103400f050001e1001c414040f1103048403800c40c1c0626690392105011801c034000d420b40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 632937419 1250 632936169 632936201
    0x1092a050a1415160c050108091b0d0803040b0619061b0206070f0b060111161e03050715120c08040311030918010302090a06050d080a021c0503090709 66
    0x100b0008007001e03042d0004401000780840240341c480d0310740d00c1901d81000c0030441c4190380d40102042004249280310024010909240e0300a00341400d41070790320002903014130b4000030414a80400da5035050620010180c0c41404c0e60b55070319103442e001e040e0100c1510018040c42004203900e0600200d032580e041607408980e80c6541e120342e400f80c3c440704414983c400b660085401c000700c07008280201d41002640340680c0c100221820058001030543c4c4824034401c0d480e401c01d0aa030014581203ea0000481e20317415000600450100c90038000c052455200400900c203d150004440207100c603c101c3c02c90302510350791000304600018505490600b0003540010b01c000001900180c0519081011030b0224412a41401c50100105e07440401c61b82c00084008201d070010000c41c90b0944041d0b50100c2440e00502c122894680428103030098228000c204450205010300c00500c00c0101c40140b07800000041c050040c9070101a2403684180c1d001e00d01406803100114a140c000c0c0910b80140164081c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 632938669 1250 632937419 632937439
    0x2040b040b2409060301140a08070605182b03020606031c0c031707020102180d020607141914010b010206060a0b0703090807062a020603060906010201090501092a05 72
    0x10600d030b411640d034a114441044207020039526034031032601460190495007142420750256004005c041e003440e501c0a03071a07500c400300500809500c60107803888002ca101c18031280039818070004880040c80d0a0034400b4012031280c040c007000701d45155000b214007a4090b039a0b01e4a814043c591141701c05100f5040001c1780d00c019480040c85214140c4806001e0f24001450100300001d030034868006580041c0140e40118981e000c5000382c0c004240c2c045422246003071068070b1640400c103a4010840d010b0b0194111512890a452041c0040016604040502543c03c203142c6004001c0322080c0d40c01e8401c643c40c08d0075a190550002604600501c0d00400f0030300c0f01c1d0715204101805600c2018100c00b04030007110005084181085000701400e03464541c0c149042d080e4112200014050008408132241a090030025803240e00440303410200c227031044003a83c1c1d160301c010b0b4050320342131a00030403540c604080e000512110070800000190302c401c000301c2640302010561191180e0340904c65202507041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 632939919 1250 632938669 632938699
    0x406120905030f0906070c14120f0c06030903070c06080f010b070201080c0f090d1202061e1f03200906010e0105091c020a150f0c032102090a080a02040b040b 69
    0xb07010300a050f0380200480e2502030030381c0e02d0844504459209540032401c08d40c0c203032400e152000803d403140c3c05044c001d0000101440b403856981e49044c20325406030314008003240c0d42090a00444501c40d40014083c0512035640c0401862440e007103a40d0b2a00190707180012414101c00d004941400d0380594458007251510a40d000680c0c0c4003455200b40d912040190140f162101d00c580e807051070190700f6034011100a568040d040500040c5000180384174903500c0c2a0403040105200c3c1c0140c2c2d8045030107544030300c1d60380d1403220304c0182c1c03c003808800141c218980e1004a446032024683c1c41075a032a20340f81c82d15030040d1041c110008000d4042042840707544803508100c185e9152140c40031140701a4190241c0201d000c3c44016041754481d03410440b41368001a0700f00da4900608455841c1032021901581c6005102c445d1100d05400700c01d0440c04424596030300c6805480e85030000130150780c08140e9032500703d80d032882c814004070b00036400c050b086049407406114081e0001c4002c0d20028a5210075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 632941169 1250 632939919 632939947
    0xa03030b01120c0905040513030c0f050717030903010b1c0305160605040b150913030324090e1002131502030d0f0606170402062b020d02040612090503 66
    0x284003050420401140900c20b214042c01400103201c401d48801d04c445080c038041c8019202d009080f203090220503001302c00000d6100309a6048180c2028030910405281d01d0b00030f05156050b40711100906900000111606001c4020081010100c0080201110450512088800414102502c00525140400424000c1c002042e80707201508061085040c00d036600403c403507043e60305485803840001008980512070301901031180003110108070a243c178008400d02e40c508040b00504040d04d452030404040c00440303002d0625901c100d1a014a2030f12104100c0c000d01005200b40c0451203200345000c00c2201d10310031030705101c2455010440c1d007418921681c6410140c201240118481081143d01008643c1304800b030003180309102103480380c07400000424203529004459103540c00c00c03040c0302c0186d6800c42140d02001c124800108502e045884039142c600c0700c8a490103440d400010003000b081c0065000340155041500c03103019501c44291003108582c07100b00c0090181c3c0c404c220304904c0d01c140b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 632942419 1250 632941169 632941181
    0xd0b0a0e07301e060e100806090604030c0609020d11040c0503190e071e17010203090d1808031b060c0c07060c02210a1103120301030609020d1b090606030903020a0303 73
    0x28044090342020f81c030710f1100c1103500c20350020307070500a01c6040c0141700502c051b00f48000c08a03400205801c2c100b00995907100e003000b41005007886290380c3c488003001300300e41121010320380003001c032100040103060244000020003d824442c0d4a410301202295008001740c0b4098810100c3c030305198034020520400406217502d00e00d820748101400050f03920700d01c001000d044030000b012148024580b199990440c1d140d800d040d0030690044c401c0010203c0005083e0140e040d032440d00360000054499945c0001c542500b008006010016007000280b503281121080001910300303c56055444102c01e00060145820045c06a0088a000c0041e20311480c00d04044500050034200751100c40010031301b5919061a040074290003402002003840b0a9000030041c0840c10b8000d050910111198004284030501008013001d5961441c0c0701552110918664555884208900000c100807421400c603642c601c10f5200c15401d080000c109a8441e0080d00c0340294550000c09110801d65802c1e405408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 632943669 1250 632942419 632942441
    0x812070204061a0a020705011d0906060408010e010509280807050709020a0c060f0506010c14010b060307090f06091223031c2f0d0b0a0e0730 62
    0xd01c440000c1040c100903090600e071046480c040304c2e40c9003000c0e5000380c01c0010351343c051410b01c003030881c696003c0c84807034800c2d00c0b0742101100c0380d42c6103a0300c240c0000c3c034500413030700034001561030140314151403001540030f140240e540c90704542000018503078001603004d8802d441c2a0700c1c50344600070305c00291124060b007900361103030064030205516001d100003213030820b00748040060783c503140f00000d008030b92051804204030241c0a0205223015000640121110280202032056102004200300002c0d4031032511210028041d599905105c2c0c0010101c01507401110760b40a194080002d000380911400300c211004600c1ba80c4980304170b0744440031180280f04018880105e04a28401ca00105000512448041003d5100c0e855019141c480c11106540d40341b00e1a50030a40107600c0c05041070a4400f01207070880da00c0e90341c49084c9550000641002103800d44c008401c000089400b00915021034440e0250f039807041440c08003042c424500800d0720813900900c55140151108404030341e00300f030300c840c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 632944919 1250 632943669 632943671
    0x80a06051f03022b050f07021209010c080706140c03010315091b0303090611030405030709090305130e0103061119030b15071b17070b1803010e060109150812070204 72
    0xf61481001c092400c8400392955215500f001c3c4811031403c00d4402d0700c6d003007020052900300c0e500c2d181001965038082440d01680a000c0400c06203007a0f0300c161600204244d1104080e5100c0f441442d203274003c0d0101c81700e4152a9110100083d101016240503681241d8001500080c4503285a2151008004500f07081c2d801c0c0495802180412020300c210000861107030341e50300285440c02d40001c000106542140707e41350000c2204100950300003030082c00713554960380300064104442c039040c0c92070f12843c06820000c130102e40d8001a403a400801c5c45040b60300880d010320600400003150344043c071582001c2280d521050700110b50541c46688042e101750000740003440504848050000c554022550440c1c1d41050302183c05c080769100400074004000700484080c4416904558589031144c40c00703000e460b04da0125000c200b8000c51460202090005002001729880b00c1121a0b2603400034054480b00c0c500300b016020641c1c1800b080e50b03003180c4c0010060107402e000002c402c0d0383c5a200d00e00030b0380e0003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 632946169 1250 632944919 632944927
    0x350901060f1410170c031b0a0804060e0a170c0f190209100b191407051e030301050d120c080409020a030c09051e180708190203150d0501060b0316080a06051f0302 71
    0x8141c01750001c09000b6803c7e10303400b842b4138040c075060007a100b4400100c000d50304541c1141e40090a030b44600460450007024207a241d034504591a40ba110707490112a0942c41140300d41a01680b4811040002c20300039645200c139980c4050f07480e08000d0712840780307400d099801c1004042c024065034620303000ea4002e00d440b8450100039403140c0c0481c1c10100040e03800d5000031458600d122007010000b40969118000755084d907140200040c68100170401c043c0072000c3c03049241510f544610b40310b00700f40d40d112062903140e80d1221807400080d0000c420110100c0e29200601d600c4d14080e4500e4405c03600010070118030f074122441440070b41001c45c0b000a40165031074000040d03444541d080755100e5140c43d5105851450320351000c0c1c1c40324040b0391074852038510401c00d1080440444036520389840c1c040d659401d52484900d400703401014030f6400100321f85008414070640c11030314140340300c6040b003603a00d80c215078031079180780300c200c60070b44c8510b651140c101884c0300d20524101d5080c104000a43c20010b0030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 632947419 1250 632946169 632946211
    0x7091e03170903060a0b01141608040b0d050a1e2427150302010c0f050a060209030d1704061e020415350901060f1410170c03 55
    0x440002041d10001a03000072920915504003002031560095100d4814800c0000950005c0c0c400d210800380fa0310300c00000550610002010701c00000c659902142d82c5550782e07562110138046412241d01400f40b0303400c10000c01c0d0500c000e4001d4a0440c405480840c00d000a0701040e803005090340c00b1503804000018280e082010000c0300901c005050002c0c0550080360003051440c05109843c80c1408101c0c0ba008401182190b032070a40400d036542800c0401c5d801d085810800f00c40300001da40100b1030f201d500900000c000c4c098000d8211001d041d400c48200c010701160540c2c0b0180e00006000324000a6800100410200d8100018040c5900100002d41c41214403900aa034450b82084840c071815101240101d40e20026800a440030500401100341402015002d065628400c5103031883d030740000704884d81030a40c05800204070303118142c400799598034443d40302441d4044410f44a40c12040808141c17902919414030020314030440559542d03181562441d42d50006419214068241081600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 632948669 1250 632947419 632947433
    0x4050607110c04110c070e070503160522030303230406150b04030803010f0605091c080d060807050a0e040510050c0d02041d151809030702150a0f0807091e03 69
    0xc4c1c80b0900481e007981d814104050515140c840d620800c04200c100f401c0004a039400b1040c0c039081602050702c1200200c89010480b058080d0105c0000801c02440c00034078072072052505102140d01c070f03480c180410042080080700c08500302024031a0b8074041e20019002405c564000203d5161210b00408295190f07200c0302c106402a402c01c5074401e200000601807208002d1200008248500e0b04519006140f804070b40022081c012084103002546080c1c000c115000d800c1d82c51180703015108001c0144d8402a00355070f0452032094a018a440c0503000c154007051040e0342e0320031604503004040719204081000d005000061400c41c441d04180400c4089404900040006141c001340001180146120a2656200c09049031607540814041040c8a460300981d2000d01002480c141c072160352106142ca04503c00c8090095002840d460241e141049507005403203080d4699841c80c1e1030542440c810756201c842a40d200f008592a180708000c81c2c200b070b9440e03080d4504c2010504076401e0380d944e9248 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 632949919 1250 632948669 632948681
    0x9020a14160515070201380a09051003060e0f03091c0204050c2a101a0306090102210103050a140312010e160201020301050904140a05030d0c0306080604050607110c04 73
    0x2030351001e451044c80800c9070f0901804022181c05180400081600c08a030a00002e5128a00c001241c800381c4034500c940c0c400d61010020840108103000c0d5180c400d00450284045000071100640f80841c0300101c401d000508424031580d500c000c500e044031302c00c200407104107a11a540d1030485606182c10068a4a000e0f07203004002c80c200b1a925014904910440810511802d0508184501c604800000006181c40442c00030180005141207841c030030040f1115120507290b013621844003030110b4600154003c3c41041c11240008100345880c40840e54074000038031001e80b080d444601c00c1c90104a0501041d80f18604203022203103000c0d000c00d0b180200c202e09a1000e907001240c41c0030040d50803208d06000075955220300c02186103605140000341e0501000e0320140c4070420301c0300498424001040041205a040421130743c9403100303106140040c094a04a030300c0001d00f0001c0004620000003503840c001c680c044064011582c420740101c0c1c02111b1020880c42c0c900c80c160b00395042e521144030704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 632951169 1250 632949919 632949943
    0x12161e03050a0c3006110903070e0105040506120601210f12080a0207051b0303040b0c06040c0e010e1501021c080402210d0c0312020a05090a09020a141605 68
    0xf00f10300c0c5081c151080141c2c100240310b402440b0140603d07035010020440c0c440d200d600440000700d075012181c042840c1d01900e2240c42d014480c8540105030108054007a81c120364084030b042c80380343d540109000c03c1007404100c1124545c02a0010700019610a082000f8034894030241c0401c49507070707103034205041200c020644100089410000c0c0c03850780525007607804640d4200541ca001410744d0341c030741c2e500012040a0040f0004c1d0403001041e0390b00703000b110003c243c090005902c690354003150b507484400589080707130000c14a1000144058a8820090484ea40407045000d55607031100302c00300c0c402c0100b103128114003071030b500d20203c0b840b4100c00300c08103160f03a52180da480c5414414001a6000d03034580c140401441d0f440d010000e940007440e03011080040c502807940000502d025544c646200501403130310750000c1010b9408541c0000604000d2400325640000c2a607900c3c014003c0f88220642080021801e07100210110001c800078041c04502da504031068031003c1c1c40340b07400c210248280d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 632952419 1250 632951169 632951183
    0x81902120f09030c0a030c0c0503060106020d030501050102010b06040909030309021201090201030e0f06060126010b0325091202060405091609150c0b0403050d0e0c12161e03050a 78
    0xa0004120110001a6110b1242c0005626003515000200ea480c044c40c10b0080801440541a00801044040c444014000581100c05a584404c406511035a84104040000c0d24100002030698814092180c16981c041d240c0381c0340c2030500f60300101a100c1044254180354036a8001d0300141c58001100e44070f07044642c000502502c1610004098075440b40001c0500c0c2d0200080f0171409802199503600301c00b00342040380c60062090380c1e844640080b2031a0385007e002001c00040c0382e590100c002c51003008040740d0f03000e4400c01c004483c4594242c2d42121800035800c00c02c04e01100b401440103a440c0c44c0003d00d0303a030405a031907001590042048455090b140840c00d680880c450b080400e0002038460007a030108403a100203070045c0b0742c2c8040e034405007110000d80c000ca0145400f032002c580f0310320380f40641449800405500c441d6142c00e058980c0d801003400c00101c01c15403101048405081208071041c0b0070b024904605c680503640d460440c0311710105003420000000e101001425012489896 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 632953669 1250 632952419 632952421
    0xb0d050d02100c0503010f05010e12011a010e03030a0215070e040227180a0c12090b010620030d0b0307080328031802040e070b1204060507031b08190212 67
    0x2c40901501d120354940400e00a05000500c008070b02c42440c0c2c400d90348203281c085044404800022880700442044555135403030a0300c0000303510100116982203c5082e00c030100c081181c141455528802c1103107090050f0091032a410308503c0c0c6801c4103070410b400d881c2c0310500000810000b0126840f010140141003800f2900040c43e03000c000d071421045104407607048108081fa0110610180d00610502c0c1da2691554001c0100c0e000355404a1400989901001010014600907a0f071034030a000e1400410400b01c400d0380310a219190a5582c044c0c00ca010707504160744625240041c003034801950303038503004514010603c1d08041018100c244003080000082c07002090100c3c503070190f03100c0e2440030103041081011844201e58800c0c00c2043e030580d80044d0314514070484a007000090b410111081e200024000c1d0300c0300701440c1d828040c5000380010005070315440030075070844910303c42c41c00f801d00610070000482400b41200540c003c100e00c50260584e84412a840101e85c44010100140c41001e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 632954919 1250 632953669 632953693
    0x102030109200a0503040611040305011a04020c0703020609060717071101090b0a0c0c0506031501110a03080105102307110d150f091e120f080a0b0d050d02 68
    0x2008a0409000c0002050300101c0e440407110914440e100c103078004c2c00000400b1504101655000c5145204191505500d40742c0742d1501e503018140c0b04686407c08040101415a149803c0c0b00300c0380d420351450f00420b8028510780c2408a142c10111000ba44500140402004a400040c6072900110798404141d41ca8681c1e02c0d000340009070286e2420f0400107110014080e201014007240c1c0e020826050011040602e0302d4400481c2c0c00c150004c94212001105200708200e0350690254103001c01d0301c8440b1150300c00000d5555400700120040c00050078400108041c1c20080c072404241c219900e8242680740500c5500f4040d00c000e003040031204940003648809001c0c06074480f100254044601d001d0040c5242c6070344102040b41320024104582d981000107000940e6030101ea02c80d68044100c100a0322840b080c042c0b100144a8156280d00fa48900040322910803450490300150589a40d01c481e15a103110200400000e0b001c150003c2d030546904010a10400c50b485584880e5401003180403084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 632956169 1250 632954919 632954921
    0xb031006083d0f150603060e060312030c120118050a021216030207290105011e03090c081e0c0103090c050d0204060512010b100c020f0f01140c0102030109 68
    0x1c100c90140e80c180c0c61040d480e54000300e5124a6140900000c03202450b00740001850041440f01008451140790480d040564009803d00104485250b10100b20303241c0d65041c4110a11421071300c680d8190024440201c0e011041000b0f1a000003445114506010f60070380c20014099080c0c1000019014000a061413020a0701909034484d034a284107500f0040500c08444a440c2d000c0c15074031206903504050b1250610036415a9406500440385442c3c02c1004040010910440c24406400b0a80d40c2c0000c6a1940101180c00d90001106406062090380b0700c41180241880c40d81100d46100c0f5040c000b138030940402c07a102d07a07800e8603418100070030303420780c04180740015184141d8145418058a1004240741c034036098200d660568400303c0482c001d20001d0010701d0703a608500e51048690076414000c100540c466807446c003003620340e111401200c000c00c0c2c4400703080000003503011038410346849090130071407254001c480042c14810060740ca0603441c40303241e400103040740486a40c0400100301c0c40140e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 632957419 1250 632956169 632956183
    0xc04080d0c050d0e0915011e0908100203011203050726030604060501020c010207180605060c0318030303040b0a02070f050d0c020103140606030c0a050d1a01081b1902010b03100608 79
    0x1402c2913495006140041100700d00024542e440f40300000c00c2c80140350b40110a035044443c4032501049020b104610090003100c01340c000e8141d281f20341c11010f00e14489601c202c038140c071490700e162440c00105070340c2180d055000c440c0c101c9085584030f03902447e000c00a0b2051540c101c1c481d0043da2640790040500088820b13035402a411917100c0104240c139030340c011504406071140ca260342c2404074060307114400541043d502c140c1d0400700c0028140307101c45020019244007800107504a01c000486010144d0340c0c002550040c00d8200042d02082c4811465402044060f1044080f400e8003400e58031503606001586d004d64001c07443e00c1403a2011580c3c0b5110b003d50340508402202c1890600c103010507a00c0c0401440704091400019161103a54000c10503903803110321118080c813902c6c030b000d00e0784100804040c2c01140410358040116806443c0209070445401209142e641010031800900103c2c0b0000c011041c10740d540d0b0314484855440910070410307981c9882c20003003007040c07400c6c400c103241c110307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 632958669 1250 632957419 632957443
    0xb12041a0a0501050f0d111507022701081203181f02030a0f1a01050304033e0a03020d120623030d1103031515030406050718050901030b0c04080d0c05 66
    0x650402c1ca040021f51500b0011481c260940310781c070400300d908072401d89074800e0748000b035440710b41c03040c0d81000d444402071404a045002070000034143d0b61040b00c1e603901d055810810030545800d0001a10060f07280b1140c3e1064240c8908031848400030050740102c841480403c2c40341241c0000400c00c031052a40101c80c240c0d002d684041001c5420900c1a1140c01c01401c9003e04010000000c035091502c103880e00b2501d4060344181c0e112001030f6150402228006142419840100611000c0311100100d03482d1055901900038000e00b101542040b1400d140055a860386517035146000f1031440704202000b45520045044050b105960400301490465421009010001d12240c0800314a10100503a5000003010203c030040d010510001807855860f0310f10070300d1641c80403080000744591604000c0c0112082c2d03c1d011804c1d9405040b407074101c01607001d4250030180140040002412000c4400c0d0701007512010a41420340301c5d00e8090403c5421100400003459408901050040600a01003101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 632959919 1250 632958669 632958679
    0xe100e0a0309170c09090f010516020d030c02010608010f09050708010b0a090225060b0a08062701090807050f010b040504150b01030b13091502040b12041a0a0501050f 73
    0x4441960018120000c60044090883c00002e281a20810030400202507400041844005150030380c00d00d5914a10340d04030950781d60800380812400086c003059503030681c07500c0c1e0181c04102509101a4060b10200d1b50720411507598800000f003032202071140000071643d5000100301d003100d504120303141c4001900034040d564034085405a642c3e40d45030040b41250921000940c540800b4060004c070341400301458110020903c042604124441c0d10021402400f224040f001c161074484035540c400342105e003001b100340005151680141302c0b4494202d03c40c40c01002146840c8241e543c00300c0341e041002d08a8081d0300c0f00b180411991000c1c05005900101524100b0103480d10b41c541040003400c64840001c145d03070314480c40790680d1080d0800c2d82e2400c40607016034207659285015034001c0140b02026100105034000c0c0390702181407402128121094440c2c55410180c2c41b0208040f07045018000300c455404d200d51480038040b820b04298842c40f0300302000612036241c5414410703d02004503180d8891 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 632961169 1250 632959919 632959933
    0x90d02070f0501091503020c030304080304020301140402060d0209190f17010b100503061306030b0717131118040632010b0a09170c040e0a0f0209060406090e100e 71
    0x640d0b44001911308480160080c1d80c144440204103a00170f10a00701c40d40b145000000810081c030030a01c00940c001c61080c0d0081000299106061810201c20b5030001e610250030000c41c02c5c6108240c01810182c10002c2c2014620010700c10704414554842d401034416120f00c403010041c0503050000c01c4011035406001740281e0346040d00007851180d00061040a00c0404804a11681c98003641038000c5100c18038104030054a0b070074403000502003100d01d0000108102400004403003000c140c1c5000390095181d000c0030502c26a124000000b0302c3c0300581d00070b501c040c00f10025040c016061800f0718080c000016043e4075010511408614038070540c1551480c945015054250040046045440301054191101c000e583d045076070f0304a0341d20003a50f404002c6c24201d550400400d65802d495422642000100e04610110351140401c0401a0170010030040038070250034080c1e40c06500c2400140300080ba60b0310b0b2070a0b207088842c01c4001c100650300a44140ca82211644280c006000f410300041800c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 632962419 1250 632961169 632961179
    0x180518030703030f020f0a090807080706170702030910050c12210910060e0109050f09100e03070209040506041403030115140d0207030815040c050714070806090d02070f 74
    0x40e9101c0c42a0050416540d107070a0030040ca100d5042d11502900442d07202c0d507419404800034080c4402d80103c06050241c1c80c00001c0a06000131410212889912011280d2512241d43c0303c1004004041c1c40650108000e03d110329a01c24094451809072070b15556114030705a0f0f20b05240180c000655a82c0103000c10507544c0300301d0f1031301c507c0f20301d0550200e40c0e41950781d03150001800c0118868103001040d041c02c5010610300c01c00c0f607000f03060b1200c0c20010461a9a41400301c03140c0482500d00e120150092500400103200f290800440d4138107072000c407460140b480c0c4c0840d2070000200c03030a0b10540c202c1014001080411740381e12006032541c60046003154100b1a00c4200502c446800c0c0d8103101c060784032488400d10b0041500c1e54480755010464690200341405001004111244179001400700c14024061425104400c0103100310381d1101e040507041da032000d48904101ca0444003510842c40b0000b60090108034191080c10014054013483c5815400030380340210303503005810081009941480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 632963669 1250 632962419 632962423
    0x301030c080a110609010306080601120b100b0f0d0204180203010305390a05120d181401030b0f0a030320010e060c030c0c0706080402012c120309030106180518 70
    0x1443c0c108480e00d035541d03001d280c016402080994170040d0240a02da00001d400000c003105206d449016441060069642c155030601c0503400b070083e807011078824008543e0280c0030501070041c090032007100524080e1242604030448400d04d65441803541c0000c01401000780a000c00c041002c0144d0301800b81400910114580303221000700c50040e1200d0300600390702a03030ba104a00b4000e04004d032407171007844581600c440c0c54080d03800d091808030f199251040704078005610154102c45161010140c2c1c04240c4004502818940f0b5589502001c10510100c6650f81c050f0540000d40c403948600386228819400b03200c0c4d180c4500c00c1c0c81256403502003120a0401c02141041d4407024000d012035a83c7d54241c00c3c030700ca50143c00d070b44120b213104484d8040380c0f55800240d080e020f68001d80750b400d0101c1440c4e0784080760410316001e401d411700d104925070715142000c0d4441d03500c2410301c009403801c0010300008207017111060307845604007240700c040c0080c401c2042d10030b890b0090f8020100355240c0c14500481c503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 632964919 1250 632963669 632963693
    0xb0c0f130f050105071106162f0a0602060f06040b1e040b0a0b121305030a091a0403050309130e0109050331030803070309120810060801150507050708120301030c080a 73
    0x5401f882d80044e8002c8035024186803004000d0740314080380012286544828003a1003844210412170400b40172078520303858000c0002c411640250b008041a903a89a00102d9030200548000d0704103484681460481d655688008112080c21814603501c0120a040100380e840c065102405003102c0303c0140704a0702c526080b81d0b0401c88841404c0120303103440d00203156030b0401032005402404017103203107610b480e071007c01c440c2143c07070385118020058034005034030600e44101e210041295204110480103810f040403500c0f901d160f9007000280c8102c03030014107401e60342c00d24411111034000080c241400c405541c04640356207072202c0c81580ea0074a092122101e041c0d18080078004036070120000e0b0000c5d200303410030351500341d0280b101000c1c030034140d43c0501a04420356024216442c0303030a012490500c46d110343c40c100d801c013200340021142e46e210259542c0e4001d00054401d8051410301060011041240ea044d00c2c02104100e61b980d80345080540b4000d4840d00204100d4201341c024102180c0138404075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 632966169 1250 632964919 632964953
    0x41211030a110a290109050c09040c1431030507030b0406020c010f0501060806030a021c03090801020c0a0201120507020a0b0910141608010302030601030b0c0f130f05010507 76
    0x8190384452501074941803a000340103240034030b250490040548810300000c0042800034040c2c640c5e0340c992140c1c00030b0300e404491040251005000104d01803030250032401c00900c0c50308180581d81d0030194005007a4ac44122a00c61030812540203011041c144420082c2c281c103c000c69503900703400c50756410b03241d000c94132010f008155005c0c085814011250b04650740505c0c0c904c000c0101c410302d1501e9601508017442000085450000000c0321740c1004100000d0a541c010511240700d03640c0e100019030340c11b5051342a010045940da0205000d0f000744000c01141074403200030004051548001800441c05c1200c1e206143e0030b0070140820144c0000b08520704560008060030160345208200d45408520780722181010306200a0809811800202174002ca82e000c0302150714015011040c0d802610038800250550300c501c00400c081809a00d06640000000a0062611a080d6280d00311500302620100c04a140c1c044108640e0901c1c2c00d0b075500502003800c1860506000da160f0700340c1c6005131040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 632967419 1250 632966169 632966177
    0x1a01090b042402030c0102040f0e0c090d0201110309090108010605121b01030906020d020d050109060504060503070905070e15030609010609051f1103041d180a11010318030305041211030a 82
    0x7150502c54001c1c010340b03219007140d0000715252035a4610800c0c045d511803042c0d007005440300b030204182103081c200300e401002c00500382442d182c0003903004540d0107800c0581d00c4060300040c00440c1041d900c460076540206001c8002060050501c8200407498041c46c50010340c651140c01c1403441e81c5000e400c00d18120350309007000a201e20884c00d1441c082c2c400c004281204d9440010300c00c2a244030340d4012416191440400c00800e9207880130300c41140d0090107125815804140c00304000c445540002d03601220910b00b00760542c42d61408200c2100e0302800d1504d04e08404810410306003440e241080c0180468502014041e1030b05012501c02c00c010300500301140001d01c14060668029020706601090041c00c81e84d44075591042c480400300c01c1c08040c4e0500e1194804100f120001e404440d07030481020003e01007a409503603600031201d200301c0040d41403544442d982c000c070740f8a091151180a001c0d03140450580b80614007504400d90f1182d00c0340a0124035210264508000410b0351450700301820 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 632968669 1250 632967419 632967479
    0xb0d0506180705060a0329060d0b0a0b04080714030c100c02150a09050310020a0806061308010c0f3e0f0703060b091b0316121a01090b04 60
    0x301d0304100c40d90f005036822580c0000c0e8140003641c1a03114145544043c140c411040d01a105a150903240e1a03100c184d00840910000d030708002c80c1c0d401100c1d00100180500500c7d83d0300c94030317085150051362214071590091401004103043c81c2039048880d200460181c0411408040012001c00340c02400200b00800540301c1021074032a281d88803800e160112006488030220fa10081014040380140d034004d000b0302c00c014155004500a851010205803140d0050703a90b6a0f0600c000b41e000b039480c150501d284c2c8040003440030020310510000e00c10f560b6070a004807401000240141c01c0b902200c02d04815800c85655568204461040b908000043e03500f5040010b00c90284c40c000c40c0310641841c50040a20000402550350300040400c030007510500c0840c4e80350514001c030586d0f904808004d41ca8200f0000d88110310385800c4036130380c100a0030001012110f0804d0002240d50b0020b80103100e04011130b900b4095038204068200030980301c15203601d41418066200540321480b41c1c01103400754031007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 632969919 1250 632968669 632968711
    0xd050a020f0601271e0905070909080d0e1f0209010509190305010e070f0605070618060b0f0409020609060a03091a0411040203010b0702090c04050a090f0b0d0506 71
    0x700618440000840c01c8411550710740c030309541e0010341c0014200b0001081d4128031042d0b15540101e04000e0380c40c0c0788030b40c0e20f04906090307080079003a0b401e400c4484c0c0c058078001040c4003403140704540d6481e0080104a44504c4180740c100200d8038801c080a03250350000580102500da035101e00e40350700300c90510142c0c888540d040181c0d12402031500349a80b0902a005003120030704031111010440340207400030b0018003022030400e41c540500c1d00880603200124801070003a1401a4010103000380310344000205601c0f91030075903e04011000c4200c40302a110244a035251903d04100e0111247c100c5040109865a074005040340c8140c10240d4007070040481c103080d41d50700941c081584c6a4118100301140d03840320b81802501803045808803900c1e004400c2e40d00141c01d040c030a403816500620460b9207000443c2e001c111900d41c0c01040b100315500108004503050f141c1040740300c010224000042104030f41e6a44240940c0c008030032540c080c50840a180e00801c0300050800c1c3c11500c8890982c000fa1148 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 632971169 1250 632969919 632969923
    0x3110d150f1a010f170405030d0e0d090501022d03040b160b0f040b010308070c08120d0b0f0603061005210708100f140303040906030524090d050a02 65
    0x810906184145031007541c60049149800821011080e44610040a03400600540350080d41d0004540042d0340a940a151040c0c00c1c41d1613600903001d074044905091100b84070f1010342d0a04840000141c00c120086501242c00c40218005048240050b008210041c1508001001001c4c003041c4403c1e282c40101445c54021300440d0301810306201034a40c0d50059501004002c280840c044624031803030000201d80c0c2c900c40411501544c1d00c1044a00d4076407035030b182d030245608110000d0707410065000c00081d0911042201440108284404039220038003805003c003140e1001056500412020303200d00019500c0c0000c8030780c450b408860b51000344a102c00116031a005101600300f01080f9014402c8840281341c07240d134420000390b80c07400f1316a994032082c1c146c00d01c03491082820800a491040c0001d003845084d445d12002c024040320700b4981e560b2209015188182d2050780c0580040540c00d8002c00c020b801c480d2081911481c034180c0d42024109141d80e040f00a084408025011400306402803003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 632972419 1250 632971169 632971193
    0x20906040e010905180105070c151b0806032a1c060906092f0f030c2d0105071e0c12060f05151c020a0b0301170d03020403110d 56
    0x141e04a01d602541c0c44000d410001d00301514031000940300071403052100310050049600c40c1041c0d540d602c0d07603e51540d940c9000400c00002c01c0c0e03a00c0780c40740d01655500c01d201c5201541242d0303d85d40c5401504042d42403604018001d8811040c000c02c42d4000f044c88176005c4e68a86401c8002d039801f1240251603258646c9002c40400002c0019041c00c15a405010003a080b4041c6c1c2400b86003a074501d1070019103a0503543c850b044141c0810512a07903904c44a00e0a204420b207052400303000e844607507408074002071061502d02c01428040380c0c124500b451155040000400d0300031b081c240035207032048640b501d02c0c605490450120782051603080c15020840807062280003001c0c0d04904551354030b280c0c80c1140181c40c1110b289108145000e0006a420800c42d00081d85924003500074900c0c04840c5412000804c0e0307080d03050b03070003c1c2c08900c0020481078081c01513009101600d030ae00c802d4041c0f03554090601d080c0300300e40300801d40188004c0c408644041800c0c6201e00044405030002186440d2120882e06 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 632973669 1250 632972419 632972429
    0xf08030109090c0b04080a0f0507080a0501051006030b06030f150d1401110306060409050a0204240305010b03040c15020a02030d050c06060402180603070e210f0f030d02090604 77
    0x11010000281d040c080360000c803101071184a05912a035150440000140281e2141c06040d078081000030313021a00d080403100c0c1c03181c05070003605c8143c0d440f003010300d142c04055a0104c9050b0340d01d00030405076030303c500e0010010304160b02e018040b41c0d0180b000034510380000381850800004090206103402c816252200b007031580548003c1c59800c241c07c101c907045280c1d800480c0d1650030903a0804011141004070791043d40014007450915003042c541000510004010443c1282d08000104d1039102400000c1d0441d000e102034010a202d6450009050b100103a1082c8070b02c40043c41400006102c081044e03069600c07000e0a84003558040320103e180001149001c0d42500070740713203100c4500fa8040c00400d940004441160401d840c3c0d01c050008030b2143d03503069428070225003214551480c0c254025a008a45450480d04c031595240001e91040100c500704042c3e50804100003403103200a000f814403901c5404007a01d10300c04615442a103d00c116089000411341c00500c02060340d88d81000d0741e01070300b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 632974919 1250 632973669 632973683
    0x10b09011119030f1706011e09030803040f140f10090302010b120d170103200613080a02040b011b03140c07171204030804361406011b0209040f 63
    0x502c443c103000c0c241c2050808848001603004503200880c0d500d0320031140c000d10b01a580c010905c1e0342c0c40030a0342100715200c0c11f4020440720103800408a1040d20286006502601100d6903240712490191344008030100107440d56000240c41c003441510208a42c80042c0024401050043c29407800320300512404518540c4003040342c40045070000000f4a0500c05c00054480058845588655051060b400d1000a02d148100000c6131004000c05440c200740d078030054840c42c00c0c800700109003d2090141d070410b42103507110f4951030f000d62403d8083e40d942e9102c03c1c00c0c821083d001c113a50030350b802d0801c410050140586c1e040c4032a58102c0e000e048800c0a1009020750780410340303071001041c0302c1038200511810381c41200c118070000b04c0c40b01d0440d01140d0340680118546481e00003241540320403c4080c0c0307081811a040500c11030545c482c080c000e80c10b01800040e8040d00d503c1c0c644a41840502107034108100c04034070030140600d8244005400c5e80403144180700d40c4d80e5140604c1d4000701e01d50700070400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 632976169 1250 632974919 632974963
    0x11a0a030b0c0d0216140f0a0b0408220303051908060f0f0303310f0e0a0c180803030f0703150603270b040c051503130c23120303010b090111 62
    0x8080702241444000c0d591b6410348040d1440d04407625134030510010302407c0c07520b203800400c0000d0000c40007031624428030440440e1500e5020b1221028400949c130a40200c0d4002a000401e000c91001310b80c0186064106030f041410000040741c002040c005416000c2c0c114031121500c0c84d90100305613020701000405840d40d03510000d0b9040b402e941c54150080303107060351944c041003d4040705400300544135803810300d000f07594641c0280303806000c02c00f500782c052008080d813102c11501040c46101c05010890000c50703481c105502007010031034000780070004052400200b4884a02400c1c1024111070151a01080c408140c2900c2c00d680100604040001700da4141002c082203444c0c19214803850241200840c0035940d0014031403550718410a90300b01400800008054240f40325584564038000d04110300059102c0b44185a000031030755054850180f54480540d00b0b00d001c1a28030004a5103901075815540341c498803582c1401106c00082c14440d000110342003d01c0104489484100000070307200e04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 632977419 1250 632976169 632976173
    0x1051e0a0902031005071d1807080709030b04060606020c12030406182c090c0105071709040f06050f190b0a14040902030601080603150103030e010c0b09011a0a030b0c0d0216 76
    0x182058011f042c0001400d882224001854120000741581c20140e2040d18982d840040464110b50024809811301c0070060020000c621810344051045102d0b000002d02e06050803406854086020a018482c490521001e9545140401034400b00c034100d013840b10340e03045120300c5829010010f410030007140008404054442d0080d10b0543c40a40e0f403403903a128503407100386e00c4d0794640100000381404108100706010000f4020510310301a0062400000c3c01c0007180c7c400101a1100340e0b525045054452000340290700d003003400101d0346841211210401c4480c5890303100f8990b2680300d1400c0e440d1020900c400d5981c010400c42c04607003000541107642e507407034000c810020b400541d6180e00240660001604030b06000811082210066003005081d83ca10369040720300303070031400440341000220400c10002407540c0307140900801d00300e8000b1801c0030801103c411082070101c082e911521404800708040f030300b0f1154550b0410a214401c5594881a02c1c94001030710990600c00f00c804500c09040342 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 632978669 1250 632977419 632977427
    0xa020705061804230c03040f150906051006080f0a020715060906060c0503090d030203090a0f1505040317030c04030b09150610020c0f18010b070501051e0a090203100507 74
    0x40c8042040b0380411072001303c541c0c00da0200390b4078103916a01c00c107020042501101c4c840059544148607a4030b005101c002caa07207600045290743c1c1070018060312402004100130312800f44c0c5502085000f425002e051070b080004003000d00c003428145484070326401003003a580058040b1004d4036040302e1444200d070515400100140b440e0300c541c50f032640ca03241c004154248154004c8030400d8204000314200803c40081000700c2c00080c1045040d0302c410000c480700c03070702c6009051004096444400c032502c0d18004030200041880181241046820401800082c003008145c50465a8401e0a13586958903038400c04240d01c9541c001500c0046840100500c41100280c90a5405481640000300e501c9280c140444000801504009a004454100d40504201c600c02000300380003420b2f0002c0042032003007014080300070780010010910002d864002e010003402201e030040c4032019081030f6000c1c0c4030204080a5030251089902d161503031030322419598100311210450340d81040400050610210142c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 632979919 1250 632978669 632978707
    0xc1d040f110c0709061527030606080709110c030a08190515120705010f0302070f060204030b01060f050a09030b09010e070f06020f121b0f03070305030f01210201050a02070506 77
    0x10742c2800d01501245510032008131506c203060035102d0610681c00342c406400340303006030002c07e80c951505480c0040424258010f0400800146014080c074030304000f180300c00e80302c0c40c0352040c054100410800004500010032140b01720500d20b04a081d0b602d82200d14110035900c5c0c128041c0260030705090201d81c40c03081e014035015041c102c2c0c00c60031101040307a411b611180701f84134003800714403a8640380501a02a8005003070051140504082009555541c0070803038109410680303a40340d4040040c070115810815403200441c00c0d0614908013803030500020400305e601d0000a1101d0986000300305c0041d401d4114203894103056090700d91181e02c820000f6031a0f441c52240314010f200c1c0240302c4160f160080381142080034041e00c128079001c1d142c03280700b03c9582e80705410600c92007080c050701c01c8504144040d001c018860380c1e40580c0c030b04180028180e25101a08500041c0080725443ca084000142028034480d60a0034507685841d005102641400301544c062a0461301c006003d0f507910310164070813 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 632981169 1250 632979919 632979929
    0x312050307090509041a0a0f020f0a09052b150c030b09010504022701020a0f0309060e060309060703050606042105100509072904030609060c1d040f110c07 68
    0x41d840c0b02d941c600801450042c00c0d40e015000c05041118040311001c00848103034041c0c10300c903001c14495029040c0b03000300c0c2c1c007100b12100c0145010030301d011002c3d0300452070401010200d0301344071201181c4104072102c52001c41080408070328202c0c130508104409012040c00ca0b40c00400f0460300301003020140181810460f003074401c40008001080e40d183c14401d65400301748070400340200b00c684103e189090a400c440c050705601c034000b00e480001c0d100241000d0180e219995582005181482c0a000e85607020706e101e00c10f2200b80200a82d101e00020035170340c403050b0340c175000c940340c0c5606002c40c0303561103103030046043c40d5403071040c42211320700040c500d01d100d5202e6011501d0140411004a04481c01501c1d0704480340c01c100c50400110f96900e100c0940301040100745001d41c1d40080142c41250300946c4216803003a11064400f062081c1d80c0320b03010701c05903d814294400300420f01000c50101d0400355085c0304541d200c50200d0088103660020420280d1864103a0303458040d001040d96402c3c180c850 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 632982419 1250 632981169 632981177
    0x12050a02030a0605040c230904090c0603110708071b08060720010c0e09180601150e03010e0d0c051c08240607020402250c1409010b070f0c0312050307 66
    0x20000d5281085e11407103c02014681e6030000e50340d04104803010540030216030308802d01e0140112900b623682d40c85410ac001d84038009070b040d03aa11346031014041d00c180300300030321448806002c8100410b02c0c243c1101c1050741d126040c85206289203581c07401001c1e66030031100b100e1244e10200003445d60400e420307618218600301c0000d249200e18611034240c4802500c4d12000034003445d050070803410445d09041d00140c00da006480425022001c652900c0000d9006a001013581c203d103503402500f00e4402409880b0903002840f9001c0e00c1c140490755038906120280800116803800002e0020900c54100e503030303582644610041400c26001400601c0966076039904008a5a9801c11150b680700d150301c03050800b03411241009115002c200083d0000801426148151811620341c1c0e066441c2c80380d01d044c41107400b005194107141072400110340328005240141e1380b100051209500c0c01068810266022408599002e461b00d40700c9106226a0320040403200c0c810100c070169504100030314456041962 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 632983669 1250 632982419 632982431
    0x80105070e0a0f14031c081503060403210e0f0d110708070e040218071101110406080118090803011d060a03150c1b0804030b01081c0f12050a02030a 65
    0x10400c02d540590348116140441419000c00070142c40c4450041c0c1d000005096070342241081854100b111300c441020300004040c4004c02000185046140060940640040c0100c0c901550090f00d002c0e8003121320210080580421100c141351034000e01d208121038070642d688200d408034010b075076202c03192a003400314500e082e0011a610f4001082e40c00c17a41b2100080210703500d0000c7c200066580540f0680e002030240c0341c44003004040d810082d009200640d00c2500ba680c2c04c0b100c2030b00f1180328500c25500c407802007204100c038650181149065417120800c2d030402c140b0802122005119001c0014a5400040f00000700c1c1140d00f14164601081d4005a0b92166944030401010561070b020040240c01b00c05922030b00450b0a91041d01c11034001d00700110400b04030061808001c4010600300c1d41d5440014080c010402480425030042400c400244ee58512183c000b900e23407003245104c00304000c0c050702a0420b1520680c01c60294001d1903c0c100414100107000310040e40c400c0310507040c140d0a01c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 632984919 1250 632983669 632983697
    0x80f0f040e090102090a031b09021b0f060106090513091a01090c02030301150507170f0a030e0f12070614190b01020c0609150705010c0507020a0e0412050d1508010507 73
    0x8005c4402400e0001c2c2500322140c1956103c20b040b01c403c003000d4420841d00b43c8041621440d502c01810040c214810712641c040034003482c107280c131221944819054005900400401d500a00401c080e188200e601c0f4a2650b1221215801070040c0c03d8050488a09242d400203035148900800d4141d0721486e509200c0c2d0300c1c806806a03581e200038410380343d8000840c5503d8407030320301c1107000d801e03801d10036800a0558a0a10502c00690300290708074000c3e00e2000484040554151148945c8600040701070400019548807590720f840d11400c0300040058000b502e00100700d22030b4003440f01828010542e40117802d2019092203003411180d90001000d1503c5400000341d8000500d0807030000c00102000c1c98034600b201840728201740d40204004001f07040c0000c1c800150300780200e02c612112a0b48050300d0745058010405a01d106502c24904001c4920600012960001032100390250314144155a0240740d11100002e203122101101c1a402144010503113010641106015002d80e5403000181d98441d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 632986169 1250 632984919 632984921
    0x70b1801110a0f020a06140a14040807141c0e01030f29120303040b1609060c060b010917160b0408070e0709050d050706020601090b01050313080f0f040e0901 69
    0x20300d070448698042c4800c8254610401c2880081e071100e00c141c0b1055151a9641da00b40c0d019424850001071844080094000a510540b00c0c0c1048200c2002030710b0610340c442510f1480303800710280100036070030240c030118a0100542c1501c15a500107620081c0e030007580c0200603004a03100346000908184000004800d140a01045c1820a003014280000c0140d11111440c0026005941102c0b04641c4406042c0d003c2c4051842036000d81841601440d200740b13442c00805c0f58a0044091040c1c4840c14803600390320030400240c1907442500024180e02d0000140c2d400785541c2d008075450511060340d5440301e100400c01c3c46640b91154849400291122108203550003203000d402030f43c5c0c0c00844204840d0807400e01755a08038080741071070054152602c02240d42041080001c0d221644144010017003540c0c10001c0d1401044070040401c0485904000203140f48405040c2c20b0104010700001002d00040600700e64108003070b42c90f600d039560000c6078520100d4105100c1e116a20051000080c560001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 632987419 1250 632986169 632986181
    0x5060109060e0d06060f0603060302100f020a080c01140c0903070e280209040905031312170a0e030609070e10080d0530010e06040b03030913020f070b1801 68
    0x441c0c4501c5000038200051240f4450609010345070300c3c3c1c5403400001c94219540c83d80e000350030780307a03000300d0b00c0ca095005101c081121001078204001065900b41041e0344c1c0403844d9004a40d1090502c0d65901c00c0318002405813201d107900d8007010781034806004c07140d40000018421400d00303800f0b564200340e865500f080c0e03551045806045002000c03818195901d000103c00c203100f19038041c0142054401c5000ca01101c1c03602d007084030345a000142010703401310300c045210001e160f008181c042480c010780e0340c000d200c2c1011101062a030408115203450902802e4003d201c0b6a0150403640e0a2900410b8640e0750041407080c401c1c415515004142c420400300360b0042911922002010640044081160203500205a1015031040344540c0071071300c425210000c00111440612002079418880002c82c18800980310740c0c440c0e4508401c50003542c9000c13003540d50b120070444110b8043e018500f0020003922800b072003414a1440000c684041256400704a80500c0000030070704070003402d59800c0d07801c80c1c1c3c1e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 632988669 1250 632987419 632987429
    0x10305120a14370e0409020621040b09010615030902010e3606033f03070908030c0703021311160c08030f16020627010206090c01091517180105060109 66
    0x1d441020111820113030400c0310090702c0605602e1501087c107101d500b0300c1e05817201031270500220b00c040c41b091240f1400b4654010342114003c00c00b40346403400c244441210b20244d8400e0544070324110301568015400c0091070076000d0030100101105400c00d47d01c6c80040c0d040e900803110100b00041c0c2280b2415030712441001c0240043c901c10b10183d0720190381c207058103001220984807151401c01988540d040318540d21b02c0349095030700c0303050105c4050807044080d0010038480d4014081411041c00009991007207940550b010b0034038143d1551b4450141203403690001c00b06c2d400049203504017042c12810000c00e40501845e0020a80b103440d00303500ca104008201c201c0f0341049c060f0342e000300301400700c034100d80e40b004140030700e051824105c06152403080e848203060440e10414038145540c040c01000c1c1c0c01a2043c0c0904060070380040060000199801414241540243c440c0c000c1401084610204c240382c014018080c9000d1000314000758030884041925400c000c0401c0384d9500810105050326 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 632989919 1250 632988669 632988677
    0x3010c0203160206031f030302060405060a09020d17090d031101060b1606150504050703020d0c09050117090a1e11040603021e0d0b090c0315010305120a1437 69
    0x1a050b020000c1c0303504003908041c0c2c44812054100111000441148002c62080d00036002c642f400342040e5003003010040c6013009403410047d002005a58000c841d8400c240d2100d0803203120401c000f5600000d000740c89007a0b0300441c28100f05801d01d80c01071507a040c84400d0750001e2006603200d50410140340100702c1c05030001c0740c00c90218400102c1a0700146003e0140003000604603607982c1c001026520141c0e90313240400e40c0040d1020680313402c1d003d040012585820715000103450580000c0c1006c0c5100d03038074000417102e41d010a40e2a8024000d03140c0141d00320040020b0369110b4a140340203207807046411500383e020354400810134101401104103e980050a105c900040f4804c000c0c610600d015a03907601c0b0000c0c22040f80000d46281c19107024481100c018170b44002d903141814540405d488101c001c104c40d0100400c0060030020321154102100840e40d5106c180341c010542e01c44d03000400b0720ba0880f501203068603086094a0301019900f0f56400204500b100c00401c00cdc92550400ca2100001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 632991169 1250 632989919 632989957
    0x52808010c2109080f040305190503090d24051806060d0209220804080c03031305010f05070c08030a0e2202090d0b09010c0201150e06220c08010503010c0203 69
    0x1140b00201240c48498622408940020541e86003083c5510050905e858140040b07000c1c41882001c0042420064185503c1820303030544e030320740383c2c1e403401035150142c4a03900d134014080421041034010803640f012400400c03140c5a41e0724240001d46022107006282c11406100760916100c0000d180d402020301800c61402181140c080c03168501d0024980c01110f000580052030324000000300c540402d004600041d203c1d401c08145a0a050403000024865130040c0f14103000100d403141040112102400d112088100c1c0d0303d4240d8080c090400003030402c1c2048400007a403414007000800040d41c803540d50303500754003420082000583c9015002004040002038510f8100c41c0c640c0241040f00e401440107209003040d0f5140101e595003155900f41c00d0751a007009044140e024080c0502c030020054000e00801d040c00461b4030100070080080e440703090b9a11580c148025a241c5018a00003000c00910256100c4240034140d00740030b00c0345d64020b40c80c01189009440c408030648032040c1400740b02c2491 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 632992419 1250 632991169 632991197
    0x501050c18010c080d0903050c1c03110702211207081321060c031d150c0c0607031e0203091606031e0f15080d0810050603010b030907052808010c 64
    0x405001c201201803040410030127941c5001044085041e144040c41107080749108200281528240c1c030305a660002e0502100d401030741c5010314040c0c800c1c111144801940d49004685142c1000ca051001441d02d00050784014003021000900307001d41c0071000007005540d5103520302126911480342500004900c81450b00107021500003044034101850017044500c0400c0c0050022000c4040302c00d45a031100c01111418050a00c4c500d5101100c0340b25907082c2804901c10b10707201c04004164000301591641d904c00205200507a100c048159424115140e140850b0055641e1602c00c0500c07007a56440200010134510a025856a11590703a004503490000142c07110003038141c0180d256511911280d4500c0d4100d03d030020080101641c3c0d000b4080450708510180035944060301103d134490803143c007484640c8810003103d0464116240c0075a40342d645454247c24000d194001550280a404042150380301c80300301d4520300c1f80c42c00d139a90304080d503034408207080724290355a4402140c0100e5400d18 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 632993669 1250 632992419 632992421
    0x30503090a080430030c0212070308070804061707200a02030a0614010f050a0b0307050c07170d03020c0604020d023c0102010203100306180501050c18010c080d 70
    0x5008803010044410545103039444000e9600150480385100d4084070441e8001c0c1030401c030300c0b00c640d020301498001c840c9040d01c00030514801030402a00550752503500b10343c1403004000550040d03070841051501d81401e0f1900b11480e501c5489100b00041110000701c0c007581082009030300886264035001c010382401034640c403051442c88801001401929080c4003d0707107080c802c0d509032500c101030010300d1000d0140a20302c95001070700009409029044107105981740d40380e0880684409000c40da4903503650000440e460305c0344070b03641c5215001e801d50014511030614040621402123000b52003a007500c0c0c0700100e040303024030903502901c3c0c0c4c0034101250260508080ea2808240054200416110140004002500c03c4000740842c03c083e01c4c240d00301d081d105c030203130600500c00740b00940c03070b40c1030401084c48000c0d29404041c11540c0d407511080942c2c0d440103413030112141c1c0a0700074000d07440d0080000d40c003a000600001244110916070341c0203503105840c80078104c0c0d84619100e080210200e8404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 632994919 1250 632993669 632993671
    0x3a02060609180c030312010e0f07050f0f16030c0b07050c03070b04030e091003050c090405100c1209110406080a170904061d060411161403070b010f150509010c030503 73
    0xd0b4207070140e60810140c0761024030081c0b071b4046142180c40f140303501d011802445030740010b1000358103095082c140489180d00074210380392200c412040741d445007602c5445120174411214000481184102c075071041682040300c0c0d005a40c000e499a50a66a441e207081c2e40300e1190b03d01c0551180c00c20051039002600c60501513800c81d00030320f029100507000c1f101050a02034140c50940003415030503020000c10404202c22440b82805944038419404d0a0750395a030380307030784007000d68015a444121541055110b8100d204007140b51803424000c0c0d48560411340803014032520064012030800034082002c07500052142951980a550984a441282c0d000c642a8102d4401c0c107034010740fa44000208816200301020139403040880b03051722414070200308021a541c103440405501d030248001200b2100e095401d004540d0064002040d44211034a00e909510448200800525000300040380d511100c0000000f521031565900d400c1c020801c506480c580210894a800981070061002c00288110051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 632996169 1250 632994919 632994961
    0xa0504090207081b160504110a1b050304141f050f0304030509090408030a05090703110f0a03050d030e0f06042d020907020c030c0a0b0a113a02060609 66
    0x280741051800b140c400c210508a00d541c00076a4480c0294405e42030b51034203400010841150200f18810460021600e14001c030a520703c10302006034000241150450151030703e4541c803405a039912078070f505032902e501d4600c8003100d000d410154041718480c240914030700c1c2d00003420780350b440c1003000f9a6600030042d80000d10071002c02c28140b100050301d07100c480025009903c0707111555103038601000c01900711000204100e4483d4000c600800206038482d03496650f02009682405207104000301085071404180d0004090344030b040c1aa1454540c19888142402d800c407003954610102d906c0c14554800066030043d20000b8103c0d072101d488440e140c1507200100c611b2080680301469078002034200740741100e0f5100507030400000c0300d01502d001e2080d100403440c11100c2c10b0726a42003c1005825014001082080c003003d00c1c05034640440811510001101a03a124014040301c0014a59010724a40c00040e05d00d144143c18800300d8000f04250b1b200300c20180500c0f80c07558403442c0554180c0008004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 632997419 1250 632996169 632996183
    0x6041a07021603030e10030b0d0b0603120d090506010b0a0e040225050c1f050d050402010201060302030a1401050c04080d0e010909020409020318030309061305151f09020a0504090207 80
    0x12a18201000c407202078021802902c440d041c2451550602039400b0361441b0483c01c2504c0c22000c02d0050341c9034a5207078003280d003243c0c1d4140e0550321340380420324204c00c0080b421303c1e400300032418680000350758016240c09403040d401d54030aa41d90322501d00f0750b400b85c01d01d0310003c41d20285000450b400e00b80d01401c00307810780300681d10189002c840c03580035800a0020a5519400c0007a10741d000c3e082051407a03080c401058007135043e1540c00c007070050141c0182c1480c403000315120170202d4150381c402d4008034040c5400034166000c6820a280c26002c841d00c88507520800e509080004d407011013a40143c60460700c0305e6020307202001005c401151542220060365044c0519040c011a11305a50f20240015181f01000141e403420840e4000c070080100072101c4482e6801001000f01c6070034041a8503401c4a4002d40e0061298424580301307042000200c6030100101b42e10302041144c1e082e900c0c01811440452203ca4841603c96610000340d11a401900001c030b84100001c100340c5003550300908850303004d626 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 632998669 1250 632997419 632997433
    0x303051e18070b0c03040902090d02060408100b030d1d1810290a0c060605030a0b0a0e0d021e010b0301090c061812080c0f010e0105011706041a0702 65
    0x32144861281980c0e1861581403040700d40c250000c04100c9100607000072141c0604000201800c16907a12650081c040c00c1038010842204503140d44140b1203403207078001c100310748550712080c0b195900d038036035065054200d01f4141c8050035070601081c3c00e102c10741c007640c03040c00801c1c003203070380b0505030b0302c08503c4a03008842100052030f04143c000f200d82c010408840500c60041c5803603072482e540d0328007001c60591655104810000c1011000488081d074029050000c1d1356025414483c0c0106959441140c03d40180d001034030400c800c081c1028812000c200d010010b0000e59010199205804a18040580c0c05800c80d07001c05001d100d04400103200420000c1003004000011a081d203a900404403921104404140001c5800030050b180000008040481851400c04200100049010040e00301c4000007680d1340d88400500000014420101c002c1c40401d504c032080703e0007007400744a0020f030070218112031a8461004030303c007402140c00010301800d110b01080040c6a001c8064001c00552007045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 632999919 1250 632998669 632998711
    0x906050903602512060305010b01120c17130c03050604021525023606010314220c061d0409021309050321100e1003030305 54
    0x900d01028607a120028038001940c4074000701d40700c00c50b8010002e035415040030810900c0c16400b490030090340e001214503c0c0c1c950780c24180d41c200c03d0300d0000072502d82081804002e004054000f2500450700780c0e00c903100700d0024410325080701c010b158403000040b8580d00c0c04081c1ca5141c208103810010b044071403c1c6035455507171008026540d540c412203540c1c000404100952401d40c50100e0700e50b40c10340d0b8141c41c2c560000e075622100b00e110502180080c400701c10079015522040325444111045aa840c400480701c100288e480010002003141504080c00001d4101e510a00450030b0485100d1100e29440d25052006105180c0b6a070181505206030100e20340400e40c0101074500805c2d564594001d0784e203002d000000c40c030b9100e4260784d00841c18401400c0058451114404030300e8803101c1e000644000b1840c2c01c905601c81c0c00c0b950032030b142c0241442003484845041250041d10f082440c030302c0540ea106548903003400e04450303501c0303031841c01c0400f000800d0094102c3c582c0b1480010307140c4042d084074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 633001169 1250 632999919 633000013
    0x91a0a0503060d0c05040e15071701120c09060803070203160f03020d260c07080114070f030e060106031a0901030305030c030405030d0c0306050315010b04181e0506010906050903 78
    0x11807007c1e407065001c1900004510300000c00d690b04615949440c0c903c2220302c480c01c0e86c00d100b06204481d0803d00800007078061100080705031028203240d120074000103070b8411620341c3d241c00c104070a034464041c0c100d201e940c0150a641c070341d080b10510000b89145501d582c0802036011501031081d03e8001c0d1541c4414004078a0000f0a0480012003100c56142c1d0140d480385072034645241c20800040e8501401c0d603084084000b007440d8440d00600d443c07950b000314001d00300e01401802070f0006a078880c1100110708181c00d50801e15852444903014021002240c0412444c0c200a220180204504001081d1698400402980d004d0300480031070f0300e07068805600074110b0340440c0e0010700103540c404091025280911900078100c0204411244c0c55041038801d102c80d108078880d56030700201e1141c0c00002c0e40380c1c54000d11205108500c071050004081d043d0600030300070484034940047c070601d0001c50000c2c020400c0c0c0e10103460103401803415040b03c40d202c00c4640b8503c00540b00d1f0b10075102c00201030900d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 633002419 1250 633001169 633001181
    0x10902060c011401080f030d2408071701151518030b0f06031c1211070b0106030e030c151512101a010c06180b0106091a0a0503060d0c0504 61
    0x801c000103000000290741038501c00041c0c2201c0300c16080007045204460000080d074040c0418034000050000f00c03401000303101c0c40c0012103840075a170000702c00601c21300c1c0418a0000c072a40c14840c01c9042e401e065441d400c9039010300754203c0030118904144424480e101100e901c6400c20700f010884610b142c2544030b12082c0503402150244262401c000b0b00000c51350341103801420a0300146810030100710307220011900c0b58050000c001d180300705007065034029000a2a41c00d1410b00480c1c0d0f03001e050415901c103007800d0207498086402c00c031140c401a00000101c545200c0080b01510039917000070710840c20001e02403c441d035400400c0c030a48500b60b956203074110107050708500806145003069400c8040d0392060301c81d1401c2e104126500c6800d07980116401242a512090000c0c1d5081d1611204144241100020381801c19140020502c030b0380005210041e00c41c2e00b41510045001c100d80c0071001c2c4140c104034800254240082031036802e090790000402c900c00d40c83c11450ba40c480c4045070032946 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 633003669 1250 633002419 633002437
    0xa0504171606090b03070c02040b1005030f131a0403050d020c03070c2304050a0e0109030504090b150a03050612010f060f0e0411060708090901151b0c06030e01090206 73
    0xc1124014039000718408214002d041904001400b646840c44403020b60200901c1074040c030000c0c0100b0411940d82c3c0d0700003040c90000905d24aa07041001000a15541045401c001601603035008034000303242e01a82201c105034024030484850a410640711406500500121b042c010203205550101c2c0650015212070034071000110344542c19804c040318148000c0d4800110540582c0e00d4011711103d003001c031081c00c1030aa030080780715107500c4500d0004240340140d94a9651820113144101648000144222661180203020209070b440c20401c0180540703000b241926030400001041074040d4210700c1c1c5c4580010014035400500d0701d1424203692124083c4451581e81c0c4c0c0d01808028418810040541201c0c50003112234a0180e40b00003180c181c0340802885108040b995a003000489030441d205220042d00e0550b46580d2003c02d490158104507d102c0401d401101c40808004885410980c264000c1841d0180720715050b0190001d108140402c1d00c15525686c0b540e025072140340003800240c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 633004919 1250 633003669 633003673
    0xa290d021002190803040308100f0510020f1509100e19050c10030516050403021315090f020306011e080a15080303010b040807080a080a030b0609030d0207030b0703090c03080a050417 80
    0x71406e8a001801344000421380301c0c1540c001c3c6014000100a00c07051410398005a0f00c00482c0068004240e140c03400c2507001c1040d1b88252024000b0f160440c1c00300e18003500012045800d4100d00ca01e428044c0c600e22501940ca41c0e07c0000070800414200c200101418050803d40e10189620004100190110f40000340400d0b00c070b806103c1080140e044690f0b031641e03149005400c15003144c0c00207512800f64201c03280b19540740c54003004802014007000004049100c0300f0094103076103810300c0c8060f410496444c1e0100d2003118081c59030b00c10303130080045412415230343c00c1c06582d6204001001051502c40344105c510610802240c03025017040214080d00300d0020f90303922185000c4140d0b00d1701895802200b901d4001805820005007400140c0d420704a007070501052014121307000c2190744c01404659541032060311244144580c020502005603800340356400650303070740c2e80b20070303421381d0000715005041a8402104201207003402004d030000e21300900d00380c0e107403d0783c45a80c100040080b0502080d16 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 633006169 1250 633004919 633004921
    0x702060c2b0c09090c17070314040f0b07030504080913020903030a110d02070b040e0a09080a080406051f090b120304260d0905090709050402030a290d021002190803 72
    0x1a60070641040080244031000e11405d0b890150040c0007104090310903010030099000f03d50140e0180d00481d114400f9400d11280e0f0346800d05000b80400d912007002e50703510406102143c480c5110780202803040b038020203001c0c64004071605010503c640f41d02081003140d0b0a20010616079410310080003060302c0c61b42c4042083e00005002030900d07142c0031013407007954080e4504000ea0315501c000c3c3c030115030601800c1c15003992000e000300080c1001090003030620701c0014612241715040103d460055003c4d140410450341d0713485041380c81c6813452a10002c0301483e140d08024806054004003030742c0c600a40f0051000412100b224615000341e000b98a050034100765610300f0a40e100100c901540c85100145484880d000c0c0140c076154803800782a0054010390001074481c1d004451543c01420701820855030b034a40380f49008010a140381140381e802e41d2001e1140c8c00a00c44904200c60084000d11991411015608101083c0b5070801c82409501402060750240b4405082c0c840629008400042d0381e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 633007419 1250 633006169 633006191
    0x48090105101205010927031b06060e0f010602161a1804020309010e0d05072609030a050c0109090912180e0103030c021309050d0e0114190e01080702060c2b 68
    0x41d4a0101c08000006c8950807000c00441d1340301d4003801507c01c4e18403130394041701786608114000c4d0006401051800c460003050180104817640010b0494510380d09403100503114201950b10500c56100c0d1290380c000318402c00501c1ea0a8400408000464419040e0864401d03004142607820454868140b650349004100808400b4403034480c064a144ca00b5600c0c141c0f255440e0618001c05204907074240d202252200c2c40110600220350241b00010110707103000010b07241c00e683d02e401c0d084205001490b00400000c412146005080d546a03202001c0300e0015813858048a0850343c07262007000d0f80684600015816034484c1110780a18007943d01c81c0503414460042c4901d0001e440c001d03480141c80c000c403040c0456070214440c1c001416601d0700c920b20314a0180120740e60b1a460040000c07040c4001102c3c16044a1040340c48a0132120792a00d01c0403003c024010740c1e40c61400c481c4200560010400100780303025680046c10200b91044284250161140074031005114084008910542e1007440341a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 633008669 1250 633007419 633007451
    0xa15150f140103111204060b0f06130528030809010504031203060503070e160e1f03050402030c0909030a0c02131a1f051b480901051012050109 63
    0x130380b031075514030f03052404401040c0e180e03134081c0003480a0203845e9520398040305a650813421609019005000b01d40b40ca00d10100c00310002c100d40705007441005d005205600c424500074542e1850502c0d1040d86074018a16121000381d40e01220015041040030030000c00024008403403e504155290340001d041402c1c001410b140604580020342c0300a43c0c07204000800b1a04c80c801c0ca10710810780b81010b512010440407804041084c810181140104c4034011b9000340d055214030712943c0224112800d040c50181030194079101501c00900d00d030420040221340f2030160011041032840500fa44440c11002c0c03c80f003007110295080f200c0d8035810001c0561440c0b90402d40700c07141008648254102a51040b405410f5108510000388500b86002c1d43c0605010140903007002440800d298140c1454414003904c00181600c1060000078918602c0b20302da900c00c003000070010741003d4007940183e420041003000703116910410701c0070030448101d21001204107001d618002d000c001800710f10f038a06611000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 633009919 1250 633008669 633008681
    0x12230a2405060f06090301060e01080a03200606090403050f0d0e0607090806060d02040f1803140909070c050a120e030d0e090a0203060307090524030a15150f140103 72
    0x10350603414a001d1003150fa4600d00301ca00242821514281d41e0210203011034054a4643d00c4255420704042c000926104085441446680300317070f50399120154950824000e441030080d003920203901c5400000c02e10704200b10100d03041400390600500b0617680702100240c5921061003800d103280c80c0c1e114450202010040d5039000707140340c144540ba80d801c040d5410f50301c02004040500c29a02340d0104010354445900c1503000b0140c41c0c0045c0504004110420f01400746a0411000114800002c845001020303055071480c03400185050010340b9600e80454000310280c0003a20703d40118003841000440c00f403912111360407641c0fa0003000c0000001014141a4580c0d040c400380402642524129502c83c0086684108403840060700c903114040401d141c14110f4100c0c2148501d4042403101c0500c0d131100441050590102043c82d0400d0401410780301c1d98008001001000080004502c040c025007140103e00036110301003425659a402e103182d422b1702a030004062440502c850305195170f06000c1c01c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 633011169 1250 633009919 633009983
    0x605012d11010f06050f0f0d060b040f090c0302100507110103050403050c06070810090e030f180a030b1b04080307151b051324110c0a0612050105040612230a 69
    0x4503500ea507142008c9901100d00e1a0020043c59543c14902c10356035641c0d00c0700d002c0380103088041290041500c0e00b00b0091916000503407150040c00204051948554101c6003025030040c86c10408014000040d00134283c050004c8050100c144000715096a0410080780b290301703590341e000d406081c903040c10519107059410907061141800305d583d030703aa0000012105803128038801c0c10369411900720f120b000e80d03640710411a070003c3c0e804030010902400200181c00380504000c900034101796158003099034801d610036100d8603001480050089031800c801494100b07210800403034443d5100d95540c0c3d618590062400205502140e00302c01d41d801d0b26260400f50408101d602440e18a01c0d80740d180b6180300044d07031006c01040b003030118000d00042c40044040c00c806844120525290203003d04842045000a030034241f80c1400001e181c81e084c003580044400300e0120498201c4280c81c1c0350103401040e41e01c407024108a546418011600300104c4107024003428003000e5850020020aa5050741d0a0203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 633012419 1250 633011169 633011179
    0x1e02030a1406010e0a2c0108070806060604060c030f0e06030a090611070c150c08040e01090e010c080703182913020901050621040302100605012d11010f06050f 70
    0x1c80700702c45d201d10301004144c0302c0c00324440f02409031450500c800d00d040614421005500000000342001d0001440f070b05032209a010349907196121424422180038511808000812036001c0c50f001c01c0c040c45c0c03118103210a529042102c00c01d800040317941d030380c010f031030900083d43c1d0741092409200091041c2d04c0010034241d5001d25080703154036070300818001d031700801000f40d00504e04011081e000d0a0401c0e038070340c3c0c8400140e44035590765407941408042407091740840d6003803064405c645501071050400f0100aa00d511926859440c0d0440050218113942001140810311a001007070010440e4034031144410b8400c41602c03206a00f00d4441200a0030400204007440300310001665150f01d02419510f0134ec1d070700c60b19108420341507040c0d241c140c1c150300945810402400103150b40440c5481071404401818001c013a0780c1c000441d6200442d050420322030b002c2002e0007903000500c149400002110f8076018540f0b8041ca4900ba08440150300403012055840108000e80d040c9200f0320014944100d903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 633013669 1250 633012419 633012437
    0xf0e1b0f06030f0402121e16050102061b0903070513051e0c0a08041509030e0915060906130e0705070507171509120a0908010b0607030f031e02030a140601 68
    0x3a030f03080703000d0142c0003d11540551032008803022040001c00308101c602d40303180c510380d02c0c0045442d40303590b0320901045509440b100003045070350000584a026091101d21440e00d0401c00c81c041045401142810b549405041c00000741c2c0da44043c00420f007a18403640001e00c41c10101c20b00d0707001052441d114003004607000200841c0c0003200f404e480c0300b03103042e003400c01031a1785501d041a525450490042503840c900140300040c10760040200140c2e2005680f9603066841d02001d13000c0101c1c2054440b40e004d4001c02040c0644c0c2041005007001c20445801412060b4031001d0245005008481140000e40085808010b00074201704040060400c4410b5543d107884840100391109094a141c0900f02d4203180441c61019081020b51301c03416065100d2a1120200f00c4003e1045c00c06116946096080c00c140780900d15112040300c0110341e042d29101060845600180c0c00340058050001c424030350304100e41c00c0204640000c0d44941901140001e101c100100d0209400d4400340c901410810021 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 633014919 1250 633013669 633013681
    0x60f0501030e1b130c020303070f02010506150d020c1906060f0b0301060509031608010b1e0d0209071e0c0212012913020c010203092e0f0e1b0f0603 65
    0x1060740503c80d01142c090300c141c000e000300403c2c280b04000d6039a40b0f4a91a0000300c003482c0340d000c8041c40c000c100c1e0740c0d039400754581d0300d41c012808e0714010741c1c9e400d500002e560b14050b1045071090003440d04221b42d00015050001030b15041d804c02c070058414010689103e108002003011600c55038024094100305405206c1c00c05421818502050203440240903000480d11b08642c5e00304940c4000c410040c15000d905c80d10f411410b4080c0c60b050114500500e0303007002544a00c2d00000e26142c004202034410b6649038455020010b084802070551b409001282c02a41f041c02040748481e81aa49103132940684200c1d684103200b00290381c150764442c1a450400d0543c0206071000310001180f50044005810314105800169076140c40a4034451140c80002c0c030780346a800640285114034001c0e802e8a40f00d40308910102d180ca102c8201e80040f42901420100034044954840304214210324000640d12900d111420b140000d4424008840710040e18498403c0c64a8405401e072410f00f45d8940742141081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 633016169 1250 633014919 633014923
    0xf0613110f01030b0901031101140304020f010f110f030310060f020615060c0a060b030606100e010804030903150f0507181203170a02040e07050a05030601080c040506040306060f0501030e 82
    0x351180d206a0244465200d180c0c841c0d000300c0806907008000c6206946d42e0700d800081f0260b00c3d41c465001c07401241d4449036940488080c0c900c00c0350003600034401c000c0301900444039141c50b01c9000041c0f045104404035440c03000c22000804500c0c0304019941d80c02e21074003245089205500c2a03040000c0c4050000c01d280e03000c2082600251400c100109440b1044009070603400742070300c0d40540380300e810070b880c0074000e0f180c018240004040d0f040d20b001d511200e00744000ba20304100d1701d60200707941d140c00c1901d40d40f00d078615a9001d80240340c402c4a8949a680d0411102c15145400d0b0010392036455940c3c4d0100c441c030580341c21514508083c00906a01d0101c10208500c078420821719030010080601031600800049040003004c005250031481d0484081e4003d40090007803405100c020000981128058800c4840c00c031502c2d240c203401c503a41e0318011507040c1801445600c0044061000150680760307507010340080c500c00d80d004035506003005803010700d80c61603900242c101800c1c585d2104d059100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 633017419 1250 633016169 633016193
    0x1318080a031103040302151009020c0303100504050f190906020d05150108090d26090a051207020127091b030b241303150207030f090833090f0613 64
    0x4110301d90841c0b41c3d034060300c0409801e08c42d4440c1810500015406101c000040011417042070005038820000352200240011103500701e41074038098044001140f1408071150166021010b482008107460409607201030503604131550b003410080d10b40c1c05008032a224800100c0d248a000e107407650203407400f051010790b15841c0301102d105012004611564206241c3e03d4124444c44c1c0c1e001e004c026003041503986a035020000c9040d24240602c2c42c0b01e203200365000084414031501613583c0c403400e40c145104400650050000d4001da80c1c401500055106c080f4000c05058540c84110703520070034040b4030040c044e82c41d5103400e9441000102c100066a6210a0f20381d0098040102240d07150744040d09604101911900068a6046684403265041c18142c0081401d01e1003030b66080c4c901c2c10665003d8500c0710071809501c1403a080140914030040c0c092000c08210b103010703964800140382c0c51a440b030361400142c1794000c150300454601e28010008100307880d0040c02d490ba19000040c032946500342041c0c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 633018669 1250 633017419 633017443
    0x110114011e030210080609012102040209030a0b150f0108010b030c031e04151404110f01020106030c030602372d080f07030e060103021318080a031103040302 69
    0x800150303040c1c00c1c041042078078002d968050490620303541c0070300005d0a10f00c81200c0551007009940001714105510482c8100c50700c8441c7c214218a25503542040007075009a00a10740610a0581d0100802d40020015000f040351a201c070310b00f108004140160318481856440c140001d13400100071864a110459a000000e60180f6440e44c440801241d039007c60500000e004004040a02c803d0200d005503500300c07000c0d88281000440901065105402e4089a02420140481002070400d0402c3c241202e884001480006692900c0340d54131407030445140c0081c0c44299001c505001c282805640b000c0e8190701c018ac504003407014120311f41113141001c204820800c02206115a02d80c0c03680000c1e0315001201c004408050380324500003d00310401110081e0406043c0710102e82c0c440d02a2196010200510b0054190340e0b0030354081c0040c08564820f81c055440e690801020018222551540c010b07100c0c3c1d00c0c40c3c1e56501c0801d4000d041e50407560201c864010304201b0710000940000c1c207113105035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 633019919 1250 633018669 633018689
    0x9021309091103030307031e0504330218030105010b070c1203030f05130203010c0e0d1e02030712050c09060a03020d05121b100e0d081801060b070311011401 69
    0x441460002c02010305080500c0d0140f001005011380103800d42c1280c80c02019051800440c40d1181c0d180d8016201c1c16034010b0040040c09a800d49200544a85441c918074a00c01041b461440d21040204992004c2c8424003405000c2e1681403281c502030050364010190050f0482c104501038540405843c040d10550300c00500b13601800c002c0500a401c078410404501d84100301c1880c00740c07500c1007003480d45a0100d10a510381040001514017449108030825405400881d02d03a94907070314060710f00807440c00c500c800801200d80e000142d50400070703d000351020303800c4020030300e940b458254501500c0002070341c86950000104540d64a074101d410303040743d030116104405840c0701e05256040c40781720310212040d944006804c140014150380b100d1001d0b803920080301c41442102001d14101c5107513102d01c1d0401e810208a03a26464410040c3d00d800101594038401030011300340003542101d0859012a8144901003510000d00d600b20440c00700030071845e07009205030715070248201d800680c1401007103011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 633021169 1250 633019919 633019931
    0x9080f0c060a1b06050402042306040e073c0503030910180b1305010804120309050708060f0f0a021201060f170a06080f070312140c030a0e0a09021309 66
    0x42c1c840d4602608981c408000740110f60804c0c207203440500000c8034168003403810289202c0101200d07080f61038140c41c241c0f560038000d032200c80412020b0100241035891910a0143c08111007900d000d07074819050203140d100e004d613405042d0301c000c05148940503600c840003000040000f520048120780d107a050841e28103c0071206290180c544005202804c01031424108011582c20f0803400100b20049140c402d552445540d8001114100030440c0c00a182c1c100c4488401c1e0a113010741c0103848000d101d0030aa42c05183c440c4a424900310080302c000b5041c190344000e0107107048064440c1608010104800d500c1c2107982e19403100c03101c20612410082003200e00030004450b1140c100c070341d84030f04101507070699410011820405050716006040040c00f880340e508000c7d4900041000840e90b1100020b841c2080c0703241c090358580d0220700e15141000b010005884000340c2480241000606034442c1c6504c44080d02c248995000c07580c11006400303104004903c04054006080000c03621407100c00f00f24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 633022419 1250 633021169 633021187
    0x80f0402010f050d0e0a050f07060e12010b1e0f061612050408031201030b01060e13270f0b100b040905060d0501060e07030e1b0d0203011b050a09080f0c06 68
    0x44d10405908007003c52411020042d0410042030310014603000d2800c0b030704031351203250180c0c2c0c984801e44074000c04502c4603820080281090400010b41c10b82140001600081c01c1b000b1800040c1001e2066512140028840201d46402140c12545138800d0f90001e0034614007040350038030034080f604003900c10025440950720040c454021a00640304a50075a51208100491030030800740a02040350940d070804008580e1500c20000031154500c01030414106d40b25626200d0000d000031200108010485400011405481d1189400540c4900c0011101c9642c90402c042480c80c040d20303031601c0505d000c0d002c1200706d4181c01503409840400500040a480b46000188061b800740801800e5508000d0000b4141282c90655413040d1151707102441080c0040c003c6c03503100c112905c400d420f4281c0703601d8403103028103051010000d00d9101030000519905031900d81d0f00003082d00c030b09001c00282c0c0010268200d90f4824581d03c01449040014040c00031080202500e850105070071501882002c1842c1c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 633023669 1250 633022419 633022427
    0x60306041a060d140a020a140c1911040b0d111c0512030106080919200a03050c010201110301150e1305101409152404090b01020d080f0402010f 63
    0x700c807020040810341d845040c40c2051001d40b01c0400d2000264510038009800b800e014000c5802c03818095540d0480442142024203842d0400c041d10202c074880c460403040b030110343c18240341034107000e00b000616001c043d408000640300b02d0880380d070150540300c941344001104881e5841050404803107001d80d1000e000034a0b00d43c00540d0744042c2062181e030721600746000000e402141a17a1041c4d54582c05a511a07140390741d80c000160041400d100c1892440d00440c1680e002500e0010307028803002103249404000a034505003035082030701d0701c0d00081c0c13103a4069a02442400c0214060707041d09030842d8942070301503000c09403000995081c031032581490b49035a940c10100803120180117004014a01300b42d8010122140b03640a4044040c030071501d007480610749503030784510a001003101360001c10801c01c14020b00744141c1c0c1c0b1660754040407404800104d02040050006405d041c000091b20300c0500c4002171420040103400c1c401c0c440100144486544104440b5601540a080c40182c0c0c134902d60080f9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 633024919 1250 633023669 633023711
    0xc050f0301270201030501060504060203040e070908011b120902030c0603040f05060f06130212070c020a080a1104050a0203010501120b0619080a1a060403030c020d17030a150506030604 81
    0x208080c400410555a40b00c0040c4907285024003c0e40c0800c002d80e02c620043d2041d1103580603610160b882440200100c0c40e501d01d400d684207020303140042e04595640307072035400e40f852988400c03214194525511000342e806400f4070079910300e00c1418403400d0105d0300441c1e100c0100c0c0040c2b0b4012940000000c0038455055003070028140d2041c05c50341303645000c14201daa0f00c2003c0d81c881d403003418030618a0000c41150f00030344488828103110b40c0d1085d1038a80d41aa20070340f01d43c41c12a0010700003140002c0d203c41c00e010000c44680941c01c000c1c480a503c81c10041241d00041200105070f10500c014001640e211140d0424141660b00004e010301d807c40c0011030b1800b5620110030014581190b03400c90a60104140340100000031080c4225860130b0000c2c0d070f80034400c800550f000f070320600c82000070034410317001c90b0031260010b00503840c0c0807010380324030111068035501101e03020780000500c100589140f040d5444903050308202d541850a11002441034480a4507903849162124400070102070640c00c4c00d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 633026169 1250 633024919 633024941
    0x312060b0f1e0729070f0e0307050915030f010216080d09020a0f0302011d150901031506021e0703020307050405041110020609010b01110309101b15050705070c050f0301 74
    0x3035150262813800c05070b80d5815485005031207401440300d800032154810150b004686035221449031000007641180e03100b160488041d40741c411401d0000c0c01e80c031844001406070903200541c000b041e0a54040c589082d000c001142c1c80c6070710401020a40f444036042c00815035601c5030000740d591700502030b00c03006840b4030003029600c8209200300140a040d402c40000c1101e100781c0310043c400000800410007440c4d60b100c800d400200e00f00145a05407a11002800028014100090094101d0346070a00721840d98101f90003603840180e400b000e5400200d0340d0100416000d000340074483c2140c1c0880c2d1600300502c01e00380103903220000310302000040c00071010103540161102074401c8800c000203555810584400300c16500e0001085401d511610011402500040056140c41800002d1142d5000e0317558004042202100d807505485910307210b10407a503030040349801c01ca00d0039100380004481d405040c00080c0002000504005200c00d40001d01721a01281d003e42c078012000301180c0034100f6200740e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 633027419 1250 633026169 633026227
    0x1090e07090c0302070c0b090a0303030b060708030907050a080610120606030b1e060d020f1003091217010e070c031202041214010c080415050402041b0c0312060b0f 72
    0x911041c290f416400b030035010780514240c0c0e240d40e59072019a18a8801e91741070a0304009200c6061001c20b001e07402140f181c00700507128911b40a01038a80990681080d60314030f61540201314100801d2601d41c460001420903000a001c5d0703403d0104000000c0ca002e40f0a10050004541112041c0103543d4030240c002d5403c40400b2a5503c0c21005002050070104d4441c0e840e91159004295070317013003000003c02129409040c6440000a01302000400e0840703c44a904050310b411303c1c01c001907402c03030b0100843c500ca5240d00340b160032a0707a0f10701181d17a4140c121040c2c12507010100031546c0da016050a40e0160181000304036002015000000303403042c2d4200070000c904401c0c0010801104850701c0b903690404000810003130040d45003c495038a41582c001c1e010b950100250600d4004035841560000d01c0104001804800341a038020f0310040d2965007404144940244000d0680005280300400090322041210354141008500a40a8211402c1c804400481c3d40c051884881000090200350f401c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 633028669 1250 633027419 633027431
    0x6030307020406150f02010606020d0806240a0e03030a093507030c0801090209062b0b09011a1309060e100c09060c02011d0303072a05060408030301090e0709 69
    0xf04c0404100b59103030408002200c4404042c051403044c49a64283c803110703409090003400381d0364116400d840213008581c3c03086800c0c1840307654041350041c100c1d800340341e103203026110b0584a80180200c81241180ca01a4104000c000c1403181d00041c410181c4d8200d0191103498031440c0d81c9071410034603c420344030b48401030000d1b415680100085413011207124020803800d0a8640d45454203803100707440000d40084400010440500d40a000062072042c444272078801032000d642403260b80583c0507019662200c4120a02c000c1110a005013103058000840403207004e041040480d100c0c10b4401d08151010b0f42c4c1d50701480c10810560402200410004100c50442200103880300c020a0903108a0001c10042c68002820a0240d540040d2954050311140300101c0d00300d08451008044504195040c0410041080000e204120340c02c644074007204801c8407071605021200040381c954024900c00c00050108002c0f40800004407415aa04076401188450640481a15007182500410b10040c00c183b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 633029919 1250 633028669 633028679
    0x10e010302011d03100522170903031903050601120e071502070806100602011d0303060d0602040e0f0a0b01110c1309080f0a170103030c0f0203030d1e051503070e06030307020406 78
    0x904118050141c2d5407541c80904c44214058a1f901d0718024001c1c454422006410318403460343d00070701820f40018050742d2820420506001c0d500001c1543c04002c2070f07844040c446d955912444807030b1007050b112410048602d402a6007659500340d0310400c699940460000040a442400094018054031048540e1828486c1c0146200d0390340d401848010342ca850720700404501c403c036425112810b00d034042c600e1a00c4040c02d004050b0480c01003500c1e20b507020400000c031611200c400c9446002d4421180050341426142ea0043e5100f81c200307103042065098549000c40c0b001306407a42c0307410f0205c403040960030341d080c00480900706040c0e01502124000c15950b070002d010b1002403602c04141e030313550b204442001c0c081031b8600800b800702400017203150031381600040c091156504680c1c0010200c0f410403041c8480c4009a903c0340614404400100015108000d2140529504682d40310621024400d191001ca561307003050f8030907002c0020191001c50701c1034406000310356403d80c000e0024010a03442d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 633031169 1250 633029919 633029921
    0x30c060b0f0307081c170f040f080c0307031d060409050402030f0a1a0105030d090b030702070b0c010c0e0609180411040507030c08100501050a030e011e090b010e010e010302011d0310 80
    0x820307148a0300c5c003944000a140c80d80309440d03054620503509400701060b29154500100c407440100110ba000301607552035000304820402410843c14801d00a6580f0129480d0040c034100008010200444102d8003803520740e640c1c4002c0d60f080d90313600d02000a1590300c07400000d1806032812000788690041d4012482440210003650034190100840e0a0699a890060664401c0440019000550261018821b9896202c000c5404c030038144100c60b1215160b15028185610407140c001e040e0795121055107540e0b80042542d0300d502c100311981420100b044011a5400044551108540e400900001c1c00c02c10920010190800090000c001c0d51500311400740080c00f40341c0050000c10178003400a03880300b07841111391041c0c0f039040c1d55150407c0104401580503140010010302555224031041c02610310030902000385090990020400184500b001a11628103030132119040c41c210005200c001ca0006030541165420710302507140b03142d505000c0402e1f00700011899418001c4070880b61075034036a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 633032419 1250 633031169 633031183
    0x3030603080301300201020d0c0f050f060601020f280203120307050304020f03030a020c040c030b030a0b0406060b28090519060e041a09040503070f08030a0513030c060b0f030708 78
    0x50140b4000c401189950055443c0e0580180203005a1158000b5611039109d024184411840350040c214001410358940b0700303000d4110f41504540e80400108040ba6071b04008200e222030145c8007912003180900d015004004d680e182c5c102c80e00000000301c00464804101c1c24200c1c00701601850340341d00700031130018070940c81603030240c2c03003590b07070f050081381a1034003004481004095400030302d800c0d034888050102404074a15040180b5903038034410101c2e6141400541021845120745042a2800d0b143c8101240e005402441406600b0700c21010350034200c080d07030f200902d10a0b14100791400d285d501210603103a40d400840d00019240c03100c2006500c0f220904003a1400e03503c510803c58100701c00d200442c2c411a420611094401441111900348004000d4000b0f000f00b003900e282c07800c40c0c0c680702192034411000701c694030b60020800c0705007030640c0b0400b078001c031803240a00c07403076851614020440c03008050007604e040c3d540e0710031803106d58800708000884000641a200220760b0b030a80980c4540d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 633033669 1250 633032419 633032459
    0x13090603031409010f031e020a03090b010e01030206030106050c120c030c1213050f120105070203030f1303171314160f0509010b0d090c0e0105030c0117060d03030603080301 76
    0x9450940102c0c0184001a07030620401a5a031117481c20101004034083c00c14215881108000800f103910911454001444003821b192008220860249040c4130528816405050050080001440140d80300c10482c0d0454000c1d03d400740e11042080240303030525444615003000c0e40c100040c80001c6003000310141000c6071203442500d02c50400440e44c4200ca00c100d5001040f10034010700284800e180904940341c01c03080c0030301380030b1076074001341002c2d8210342c4141c481b500960b00c0482048114580b142045600c040c83c6030040c185000980c0e070240c0b4031b00d0340c421182c0d446007401000030180700600515a11441c1c020040800301900781c400651030f000200d0344080d01c4050701101084400920624600315400070b0001040384c0c1c60304204100302c0e0807001041a45c43c0d2613556540101c2c105c05603038409041c0003500304900c0e5151104240c5881d1101c10a2410b01c10f4134103500b02c80003002c0d107089a100340b044d600d01c607040d2100c0c54220300600e00303500700521009001c000811001c07038070160559801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 633034919 1250 633033669 633033677
    0x50705040516030c0905060406030c031e021e090f040c020c090f0a06050109030809011b060e161508041e02090405010606030501080f070515160f0b1005150a051309060303 75
    0x2030401e84084517a110903019254000a007040104503952090b0f02280c83d504c0d80d45400034500c416822400c410150524645915680200f0101a580130700407562002840c805510340c0703420204c03030200f040080c000740c120784030f01d6860141401a50091151010400005005498600c0c08801d9410541c0d8140e070551121403030301d0301c0828154000c1841c08140c80e04429280d06100885004607a054105c80c0c0c8003500002c40054407002402d01c1c01024840c4144401030400072440c0d580d5400d03400c0440d408800034503000e0b8034426801c2c0d004584c903900141c10245144443d00100f0440c0c13050400c20340000d40002800741000141300040d4803c0080d61682d540030311a590740d0305800eaa403034100c6a0780d014103800240b0100841d03d45104000b99488802d122142041050a078032940449044000d4403406c1c4450034a00400c8910168554401842082c0341d1015040c20007045031403810310a401c0a100b400254501b40c00d0142c01034444055110107414442c03600c0d00c102c00058440c52000710086 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 633036169 1250 633034919 633034931
    0x1050f0708010909030903021221071e0b0f04140a050303010e010602030903030406111609020702033021010312020f01140a0504150501141f08040f05070504051603 72
    0x1140c40d01942c55905d40590f201c5044038196002c201c010400c0c05002c5645105503250820040b26160b4241d11001c101c1d12070a850b0290380c180302000e0800100818404104400b9040002d0044283c241e00540348280c540c400d0b980d40c0ca0a1a442c2c0ca0300300111100380b0032400100304200c03001000310305940115001c0e0030141da0b10541a6038a005080415505400a0000f4040c3c144140b000607040240301c0e08803203104410301405841c0d04015000040000d40004221065007010000007000141c103083c1c00c0300348110114211b042080e410800301d6030303034000148404850300030002d2003200402d405110b1900c2d65039282c1029500f4200c48490094064084000284030040c822142d501c0c460010159280d40c0700d4040728003e04d0002e000b20382a220300c041480e1100e10501c0340b5030207048441482c6014115002c10843c3c01c90b0010130120610446c2c001c4401c1c59640085d203290041d030b0100101194806034a0841d08000b06500f100390400d01d0f0504114000074025441c9810000c81c0c0c80070012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 633037419 1250 633036169 633036179
    0x5010f0911090108030a110c0d0b16230a140d0204030308240f031920060711040213080f060106120c0906050f13090501031e030903170c01050f070801 66
    0x42c1d9024401c000080d0414001c440074103000c0e059029045e017a88055a260500c490300044150003102c90503100c04034600301f080741c5110010b03a086440c8125040c44110301035407040358502e10784868100c1c03040001c04102403c01c80e002d011500d0300d00421240e50303916800c6407007501c00250041d03c01600080c44190104000144110842c80c0100040e0381c6c0301210b041c460140140c0409a241c8150984035000c0311080c0b6091072800d500d03040b403088007050641c0c03d098441030388002144100c644070700703001c1081c2d800081d108070710740300d5002d02500c1c0580c98022681c07114409000e154006142400784c5d152500e83c40301d000c62000d06031a03468846044200030324006408442141e0103171804a02c21150601c10980030300082d0130b010031030041d118034000100343c009202482c2035000c180328989070030060082012440010900c100040700800640075640c500410300002880050226540403107440c480c40c0610302162089414140203002d5401e04c490050080c0008940e4071001030000400860703 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 633038669 1250 633037419 633037429
    0x5040f0b0d20010f080a021b030309060604060807180f020403121107060e030c010e0303160302071809080406120209270604020a051804090c030f06230109020a0c05010f0911 76
    0x1c40b03134000780e0701c1e03820b030b90b42e1003103c08001e50250400c0b8292906040101000d05010002103200c3c04504c40038060300d0500c10103000a481581d0080c0c04650020355040c81600858403603265188044a00070034142c02c0e09900000078441c81e00040d280c910b281905507042a00f0044406801070110700b01d491340c036911a000c0300c5040d1202100f542c150064124044550300c00d105084401d00d0041c10740b85092003080d01401c4a00242000310b0140c2c015a4041141000340d5030320403050b82d5420b4046c0029621641e856110784034602401040c8054800c03002130300c641c40d0307040c0e41d4080320180c4400d0781c3d000c00c1007000c12412a0304100781085034500d00054141c4c00c0a000b92405a01c19850b0b01e0f06080030042c0d5002500c1003482c64542003991041e00102143c5007a141d01c00950240310700015000c420b05049090300e0713a480c05600368100c2000e4480d00303071401c006030034111549402d00680750040041c04a4075201040b001a0036903007080c2c102c031110352040e406a45c08a03c4ae0043c4017500407640d00f423107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 633039919 1250 633038669 633038687
    0x41401060c050c1e010e0a170a0201120b01081305070b0f0d0c0c050613060212070806031204030c051c12031a03070810020f0c030705102405040f0b0d2001 68
    0x213500c00d0008142c000d254003800f110800c02000512403508951070740c0c5680320141030741c1d401c180c840d48101031401c00d42d60480c0305100740011401003403011000742000030b0081180030702240c1249030801d040320103100702404110081c104550541d03585400040b0020101d821028401c0c407600e01c3c014000029500403040620b2039940403001e000e407070b50741d1101c1c840346003c000d03401e0326103540811050380c1c0070080d905400e104031200d469030807050928a05140c9408008006005c0102040209001140b4114109400c0700d20032590500101504d006020700e90100190041ca50800c41d40340026041d01358001e00410441c00c1c000b1545a20700900f00756542c1000d2080c0392003a04420814242140303e80c00070112040040d600ca4a40450b002c400da1440d880181d0540707441c0c02c80660181407000e24002c44940c45901e860700490700e10f81d418801740e89917040c450244919550000c05d46402182d03009003c01c00b50080c4001c10b44c0e103660410500d01d00480400003451005a040074010758010321660f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 633041169 1250 633039919 633039949
    0x3130b04050f1f061e0b1e1c050105120c04021b0a03020a02030c010c0b18030c0307030302030106080c030727050d080c070f0605040308070203030d050c0c2e0b041401060c050c 77
    0x40b201171490301c5804c918691203200f121304851130307020000203400341a038010044102292202481c90181195400c101c0318103070001c9108049950b1031120380c0c04000760080c0c12580460700142d540d850f59000001d050041e501d003011030701500c1045800c0c541c011400d6070246000f50140c1c0c04944c002d20045500348048103000b04840041b0020465580350300c1001d2108803110000c5910385030344030440c1d03807658010100031000a034001006000c011b501c480043d4202c070008104a08504000201602d4100c24411980c0e96aa40c001c060785e45111402185000340b0300a00411162482402c4c0600c16901c002c094107440d01c41d0520016038140982d150f2012116184d40b00c0f8280390441e03540381445c3d8030004050f40d061200707200c28020103444d4426140502d944040056a0364020014241044c91510100d840700e40190400c100901c0071401e03d032800c0446000010b800d20703044000400810900f51507200c11080c100010800d160842c0300c08401070b01030f200302c030380c1c1070598400c0021021405902d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 633042419 1250 633041169 633041219
    0x3030e0309060d151a031602070b090405101a070605060d1e0c090606050d0b0103050103080d0b1305040b06090916150e0924030303130b04050f1f06 65
    0x241c0b4034000700b02d610441540304805203030034900e6503601920804990705c0c680001ca0070000414803501e490f540c50603650703010a600203401d0f2a403a160601c450b50040ca16254012a00d84000641400b8920300c5a4060301031806440303035a41c0842d04c4807000c2e03007000c241104e0991406002c500d242c40c140030400c10440d07220500c546c80054130280400206260501100e45480282d0042800e1074140220005002240e0b10320b601c038160500008103a50002014a06041c50320b0010f1010800000860780c049828030b00200340c1980d490041070901810700e04e0210324500d44230500003000303600310565000e074004a807806101d03103444002648511902010080c200d01c0900e003002004030503121700c00c2d001d00608003003585c0181d14022501928040314a85440000210380e400c20000e05a01034000320000d1b00214154980030404043e64600b4500c05010003503440c000904100302000080d00c08941e01003a9055010749510300d90526509540d501410f50600e40c000ca03c0205225804040012005d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 633043669 1250 633042419 633042427
    0x111201030602070510090f030806060703120c1b060b0a15090e0406020403061a0306010b1204060e0f10060e0a0e1b030f03040b120c0f070b0a0b0a0305060403030e030906 74
    0x55944002c1d401000100e80c1c80c000c13000c4c0358411100318406c0c45072143c02403100d405117491a28004200c00b200070143c5114080c28407507034002c294003003035000c4e00030200d590000305065000001c1d2307100c500000461a6000010018008100d16600000402441568200030303c948400c0c181c140c0d40402071011700041d000900802600d01140750264000e40034100040c40c181c0ca9848003001d5408000003c00180d22030010f0004505080103000d004200881e00e0b1400d00b02c801c038914401c120007500c0500030588549a0400c142d00c280140410b10100384120b6484000358210030024003a81d101c1c1401e10000700e4000380b290113860280041c0251000c0c05400300f030381c075402c120b8480d042048641d50940304030503010350790741130410043c000b0b40200562940c46098002400a01400043c49070180031000d100080a0540c0d84064442c030980c082c030403007100d0741d401d14400001c000c06040035500143c0341500006121b00482e4560245000c0e9505020314101d800139140d0307900c0358101c0d03160841c0c0208 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 633044919 1250 633043669 633043673
    0xc081302010323041109060d2604060f140a0c060f0f06060e030601080c100503090f030d02070201180506190905040207032a08030c0a0c14010f11120103 67
    0x14020109103105050005105000c1c040907040083c00d1042007a80f4a207010038001440785404420f148040c1c102e0706880189000d4001c50780000002c1d02c01481c1180c8034144c51864001070701c4c1203903090014501c10b41c9450f52101c0c02090a40300c04681008590030b10241c00010064904442d10705406466180c1c0000ca03a0b6100402409102d1455180c156558604013440c4400e0003004000c0c0080e68480b21320018000415007081410b038401600c41c2e012465420700ca40340c00c59041c41110030350030007a80343e554500c410350030013400d041503450381d000c00103158001d06c54a0303000d4800c81d4002e80c0c50b58084295142c0d10135108030340307006481d4415400e010140d10039a051000d8221455186051402c0c5607456000c2000d0760450202280400d10640c64030905002c00c2c02c1c5564188c200c1601120340700603039100d954051201074003c3e15010b13000a80502524020905a465254800740e14486600c013070a40b00d0007003124500613200c950a082100350618088c0043c3c8140802d0030144c034520764656 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 633046169 1250 633044919 633044941
    0x3030c0703120e0102090a08060907050105070804090c051c050601020c060c0c0a230904030507020d0f021908060108120909130b0f0a0f020f07060506031c110706030c08 74
    0x928200c040000b9800c094031242000c1c011043d01c1054440007503101c1e010170003044002d9034290044000b0b54012020025800c40c00a4054100c80c02800c0140da607555a050100c00b504c0b80e504050741141c00d0000c0c014242d54807200074800112a103070075a2810b514850380c40203451040d03d40707034016032114400d2022898100020402d01b106802102c01e9104210040358000c082c0340c5c00311407040340ea0040c0540111180313000d8802d0751011200c0001c24079003541c020b09603001d2854044d001d01c1000d00100d00704100801004c100e00e8009025a880381130300e00b0303034000410860107058414060300303000144801c030014400480016110700242840441010f01c5090200101041011911075110b1000300707032402030743e40c000c10710101c05c21080d281c15503140c0281c4000302c01880c07140d4410090036100c0c0415806841e1007940c84400480e064803101e0010340340402e4517840308540140c2c8110b03480c0700b58120110030300c183c0000c42901c1c5019039524040d000c0b2802565002c2c04039060742c001540803624 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 633047419 1250 633046169 633046177
    0x40c050c0313030201024b01060e06040c0503040201080408220b1914070201050c071505041707030b0604090f021c110a0302090f0a09050d08060315010b0a0f030b120d08011703030c 79
    0x628107d805090302003800c86003507a01e50340c440e4481e1030f40841441034600705401000c5052a0b030f4107082e451402c055000038590350f0000e00282c90b6083c04101050700e4a1207440300700710002c0154030401c030691140820000ba40c4480d0fa40b07000400e440c1c1c5004074140c018200d2052060603025541c0c20910540c005490582c480d202000c0300703001707005011403d00301180301303a64000c01681c0e815499a0a2594100036420000d11240b03099014000400001310840c4520ba40400141d03000710b00c03001309103007006045448000096011002d44841c40f240300c0032082c07000c05640550405248000c0382828403000981600000e03402c42c000c480081c1d500c6c00003185450300706102290000311a112502e0300360600100500d20300c0000c148100740311403407504011003d00319088200050301949050340c514503611480ca41202889110100d10900600943c002069a040642040100c0d00d1800c521915035130f04141041c0840e40c0140003140c00c4000f41c40100350541d201340210700d9512101c11003169904 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 633048669 1250 633047419 633047533
    0x5010b0f0a0c12051207050306030706030b010c020307060e03010605042007020109080a080a0e091003150b060c030301030303050106020f0709050415090614090d090302040c050c031303020102 84
    0x42d1400380100002d005440800d21503045a54080e240d65510362455010000a4400340030840d003401409880d035000b04900080b2209820002210083c01c0e0060f2440d2445501c0030f54075019000c00011081d422551740c011a210440007000040c0c2c5032400c0000701c84a2010003a02c0c045401c2030380c942e03200c0d0349000f00742d2302d401410300c81c5040c2c6c2d441802520f040e4074200200d60901000c5000001c0a8005114540d107080458000c00c0c9454011440341104d0611307c4040c1003180c01c4801c001d00340d101c0e07a01c444408071014201c03036600c17060200074907500d500a11084000910304000000e0080c40031030100b85591114018080305460011050f01804000d4400e0303c0b0701d040603000e0040b40505200b40e1940a1041c1d00102e44035032910700041d81640000c02c104000d82040398450034050740450b8400076254121000122000c040400325800c1c000c0d01d001c0304403403000084180c20410604400c20889100368216605500d14000e0300780b101d0b4810701203a001400c50039400c80800008030103c00041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 633049919 1250 633048669 633048677
    0x206010311032a040b010305190c120e1c03060f090e2b0206090f0d08130203121905090d120e270a05010326070b0c1c05010b0f0a 57
    0x80400c900030002d5030640300b21489500010f00301c1106400e0a004500074040e090804100c18a403003062001c569065009a101540e5501680d8002e14020420100300a01c1c580080000d202022843c41d45e4000b0094100300b00382c1005442c1502c54441d000ba04162050050b140c2c1d4081c2c500382018000d00b0600b00e010207035008a1a03060840b0714080c0301c002d000c402440c110003403a0f141d5400030f0305110b4080d00c42020b0341c008a010030007032100061900c55030856131415403040c1c3d842541c11801800301c4e0b80700a45c1405100f074145000849000680000e1a109100415100e000300080d541d5103c0c200000350007015000f00d8002203240607218103e20f0040e03080054030002c8540002e02d540c001141c10b0301400800d080b00b10030b05075a07002034940c0304100741d004120950650f22140d120040110811482c0b83c140704110585240c10f100740c07001c2541c402d188a4041c100180c4603101a00441410000d2041e030700605800d1103000c3c0180e0f41282d082c013005900d454440b041144447e0311040586085c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 633051169 1250 633049919 633049933
    0x9061e07020d030504031101020703031b02031e071a07030f03050a020702120718090b1f12030f0806010e090109020d02070203031204060b10141e0c0c1002030a020601031103 76
    0x5602c40b1119031107114843e60b1820b944a003107140007009220460030b43c0341190701504092001075008008480f002080e010b030400010b80c5440040d140c001c500c3c401050304030b103c10030140400000640c900c243d801c03036114008850320301244c05c1118000c01002034009846500c2d102d08080c029441141c03c50385440f03001d45407524580128000026124202590307a1103070408025954000d951100495034a20080c00700001945a0012521018201040078060700d9158880260f40312429001080500820003c640c020305000e403440c80807201c00b0780450800d41c0000d0280d80b0552010601280c028101c00040e400c11004000a4109030203049100e90300b081101e0150b9020806007002d900d1170741003811985410b14158059688644c60341c1c1c003401c0144880c0441e140c1000c0495080030782984615211071703003a0114503c11100b954405454000004c00c1c40303074204045200800442d065900364003046507000304a0350380c490154200c006820460051001401002c2d02d4401c50000400700c44403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 633052419 1250 633051169 633051173
    0xe19090c0504090f051603081e04080d030906060f05010206040311070803040f15080609040602030a09022710060203090405040212010e071a041805190501060507060608010209061e07 80
    0x100d0300d00f40d10550b110043d1441d8902005000c201c03907040340401044004045240d80d84201d483e001e64200042c0240311941c07030182c02207818060310020518201222040810a117000c5c0c001c0c510350744142c500c5414080007203000803d41d01d4070001c603030b810313401041559940d032403c0701c02828031840282d05010740900000c0f604802c0000e80050071508402000312072400352a04030140204141400384000d14040040598485402960041c2c00100c05681c80c0d59405291006001480009610000f200b000d401000100d841180b0800600725000105484424162740012114412000181d00070451f820890409810164210344041c040f544814111000c1c9030a40c0c0760b00c030660030f1a500c4100c04001150141c114080c0e000d0080d10030398031b80f80c200b500050707204086450403044030b52603101161070062650324488021001d03030420001c9586a400040103588031a109540d43d90501101207401030040c030898008184c010b00d818503119a410200d291005600700d02c01c0c0c100d5052200d0300c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 633053669 1250 633052419 633052421
    0x1b080c010318152406031b021513080f0a031415100909060e07090b12060603071e022109030604110109091103010312051c0e010e07080102130e19090c0504 68
    0x90900d48202c40391314680c20f222000b0100e0f94004210b1407a1000400f40c0c0b140190049001a400d201c07019071a10f20343d5450040c4000c851301710b4002840d014000911414070302c959000f40102407801d039014000744802950601c11850103940060241d0103d4044180320725003004440540e01702401c1030142e2560f00d40c0020308a540d10b0b8020056003003001d04110003168411702d0000070b0105011a507080c60041d013825060303690010065401080008081070000e0300480400111084c482d00952408141d110002c1d20f407000303600407210650300043c00007076880780c2d0401c2e219600005001080d40b50f941d81c031240110080008014188802c400b40420000e40034010b07400d003180c80700400c581c0c0394598641040941300407011103003007140c1400800098500280060074103228550049209045407541500401c1d0280282000b0710400c20300068801c01900903141d1419480e40220200381d40d0b01081c540043c0490310500e0124410300b59071181c0c09641d0095041c64010440010b070381e9200d01c0414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 633054919 1250 633053669 633053711
    0x6060a12270f0b06060301060909050c0904020d0902011b080f070807150b030c01031e09050c180a0612021003180b0403050c1e030f09030102071b080c01031815 70
    0x15415003168040b040c1030120340c1207102e400c4241503400900c3d40d81340110080185003c4c0c02404215070b240c00105094a513850240c03200180001d20466954801c24040b000900030344800700e0214100c000303181e081c0c004001401002c075410400c40c9141041080440e1455404240c0885140400f070042101142911900300c0d01d24220a10000380d5503202803c0500d4801c40c03850190415041480050100c100c4001d0440360480a03200815041d440c1e00c3c00c04d007801071030007007150811840001107100004210b407c9000d0008188204800c9458000c80c0441c40956100070790005a40c4000202003071082d030047c403111446543c0034006010980d0b500032812800e40c1c007a00000d00c0865000109402481080744004e402c468140c0c20405070315800392030380210412034100c0640851703140b085440039012550182e0f800580c1d404100090411010400e80301c1c0240c040030700c1280b200c2d0040e54040d220b403282003041c1c0200600c60300744039525100080701c80717112042c400340c55100b059000484e000b810 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 633056169 1250 633054919 633054923
    0x10207121712040605010e061c032001020d050606070209060607060207020303030c190e1e030f07080609120c03031504140c0309010b01180302061b070609060806060a1227 75
    0x102c00241001e0600b1002e882c010380000c081d000e00041400348985c0c44801503060744071080800380c100e60540c00c00340c030f0300c100752000401c900c084400349046850065005000203901c4590821050700ea02080c0803c5000380031009411000c3c7d1008144980b80100c081c0034861300ca600d000d841c00c8030340e5012905540059841c0391008101040701d40e007807401c801c03d481a600048c505078840b00d9112000458013200342030703005004c5905102c401401e842c2841010100c2c007031711003150a0303144d0380c1d03208550703401d401c56205602d4050350388040c00003441c2d0750403503544024100040d4110b40310f0070350801e4481c0035800c50700c1c1c1c4036940e10242d00b00211400210752144a114054a4607842c04140e1a82919104880d45c0e0411051a0716105000806040324046d681c041d62601c0c0c17242c9802d00c000300da03140b1882602410b4442d0101c00138009a01a90a0b81a00c00076503075203e09840e2034061240c1c0c0d00601041d84041140b5824003503007056144d00c841703652902c020240c024105040100b0300c0d095002c02c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 633057419 1250 633056169 633056197
    0x605070606060e09040201030c05070602070c051005040e010e190906090303060b0901090b0306011701270608100905030f040e010806070c03080a0504030212190306050f0102071217 79
    0x5440284900c510840340108070780e0030640350b401c2a58000803480c3ca0b008000a051582e260014045c05100300240d0340c032300b584008115543c01180c28414440b004601c103442c46202402c0b402c0071042d11540c10b903004c0b100c58517a104040c1e420140d01e50081d10f0014134900c401c02c0c0040041c500e1244a014910039607000c0c0340c00145140417170400401b581c05580114001c120100310280582e40e20035040401c868241c18500c0d1251900d000481c0c9100009101154010380c3c0300011503208442454419600350000e4801c00704540c0b018050250341a910401040340c00c030000c0700300c600756076402c030321549031081003542d1078000001b01c2c680b842d070052381115505010000050150b01410085c840d00041c240c100322022121542e0002d24145005060680c8079454002080815001f0041c8006c101d445a0b4071a85401598100001c8c042c07846082d407001a080440006090030140402840042e069000d041303070300d041542400050b40e50080488108190046c3c3c50072103d04d00d000340c803400380381c200c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 633058669 1250 633057419 633057427
    0x9110a14090a410411070b09030a08250804230c01090503070b03130f060603030806090f01030804060c150e0703020a0f06051903021b070510080907090b06130605 71
    0x48422844030350007181081c09011000f00e0400754220301e0084036014000c58012800b0700d6507240c604000e000d02a4003c06030303900c4400f4011002c0c0d000c000307086000020740d6075010658600080001e00802c0041e00300000400f281c5006d4013a210f60003880d03205000d4500ca1910190b07885003c043c491812121310915006107800482541e4802c0305032000300340c01c0b0001c051041c14502d1070162480b01400d944405240b00781900300300940c0b000707031140d402d4000c0001c204032540ca0a0140ca1f1501c121007003449080414009440000c00b06440e03416a900404058282400c040007926800e09450060b140310741549036140c5581590700400d0700d031801c0800601074141c50343c814403e0000450300044840c1c9094401480096030120a464440d42420803109a0402d603040c154000c2c4100b0030252084118492108910200040c3e03000c1150010b50307410b081c0251442e400c1315054000e44003034052b6048400308100c2445e29070414003c0850080840b441c28810b4600329040500960140000c120085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 633059919 1250 633058669 633058709
    0x3091e1c1410053301030b0a090c090f090507020c0405090a020d05071a190509010c0501052502070e1801180c030c063b0a030c08060109110a14090a 65
    0x41a103a0189524004e0080f18403100045554541c0741010294105030340d070181075035281d13910b0010300c2c0108140c1070100601c2c60002d50040c0284224081c40d00c5d0407020300c1c00025104220310400e4851306075503010348286051a82084068034010701142c41c10700c103100d241005a51683c0c82e03060ba840c490030040c8a268600412030001100c000c034406460342060000048038005004414008100742c030f0070560b55106a80103844a20071140043c2807907203014100034410805904c9110305008849000c0251004100300300c0e601d28a0b4040c1021280710400407c00301500b40a440d01c01501a80002c144c00309070148400d00c00d808900251080340f80c0c41c40800502001400200192241c0e25091242c2c0340c1e00303500c1424808240810070740c0120502034001014081c0c01c280c81d000403004040c90300180e5207052180d040f07005c5020321400c0f401080700000382c1c50811312500c49100340d140700d00ea082140110090305c05400101e04040000c2d0104007220075941d5860751030300585250034034100500894 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 633061169 1250 633059919 633059941
    0x90b0d0518060603070e04030c0b13151806020306031e150f1b03180d0e1305040f020d0c0b0d1d150c280203091e1c141005 54
    0x1e40850915041001806510740380450b240d81038402e0000044a06d44451a04590710314140c44040c041c041800b00703020340400300c90b0710122003902035101c20341c050000240100032a5005001c8545007514407a48000054250b0050365000d080203013941c0b8841c0c0d2656003d20b03800741d050b500d080c2541004003c8500204850300c40d5401840b04000a10140350081025401002d00c0c1e4071002e20880101c0015081d5064450300a02d04024109869584e0307084100035050014440c0300a1050800c5a46156286014851240b00c1da400c00307139545903620140c007407203808661260203407440003110328041120701c2c2031001050750141d0300b40c0028480c00c00f00c1c01c507201c80014640039205a0085040082c1d254425079400c0e401c40d0503540f005a07510310703804501521248968420300e01103501440e036400d19070040003801c0300140a80f61600e400034000d403100030000c1071f4490301e984110507850140c243c000c0d4035460100d0510a40036010302000d0320645918195a030300092081544950400c200c40d280 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 633062419 1250 633061169 633061201
    0x4031a071713030c050f1f36030c0b01031a01090203150909010b18011403070b1e251707020603011707030f0b0702120403021807090b0d05 61
    0x5200203031050400e41c242e01404031540d000501005105030541c8180315090061b0015000814201c40c186a803110601c11502405005031010515003920464603090b90020003c40e031000300c1d52000f190290840c4111503050f80107060f01008145240c0b440003501c07403c2824061402620f0702580c3c0000d002d0280003021058200004540c014001d000c2254003040381c1150b00e03a01158280700e1551130b10085401040400b0810713074088240d00040e4550f880c500307152410385026420f4284030f005c0a006065486201d84035568403003008200c14480c981c100b1051064100c004502c0d5803038038101c000e180c43c1100b00c070644045d000300100507000805c80d800b162040e10480c500e001d5030500c141600082d19074001449018484042d41603480d112400900100000e189d0040b01d4504041d03040c1007030007440b03008803040000f41c400e0b00c00b030b90124900301c0c0a0b0383c103ea40c0185806901444240d030000d1802000d4170f40c40502c0865074002c1031010780c400181c818461b460300002060302c0c12155403078013101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 633063669 1250 633062419 633062447
    0x4120c09020720040e032101050307031718090a0c03050109051005040b0f040c110d0e151305060c010c02101103040f03170a05070f02010c020304060c060204031a07 72
    0x220400807180062150554040a06007495160030412800e43c0410058807103c2244e40e55400001207940598281160503801001e030b41d2040c0e44140e8985061503aa80b81e18003000d0304205103031080d801c845c0224801018002103464dc0c020304841c00304d000c11a610400d41e6907140c0141c0700e584a07400d0301d03854403c4a004112002040c001c5041641e5100c820040e84d0042600850716018002140d45500998407000038000e402000b44800d80f002c0144032902040d1001442c0c013031003c1c0805003911580c1158210740300201a18201601e03041b04600642c00f40b4000501d400340100000f03490399401e0f000e005541184000880c03107a04800000f4200750304881c103086400e180030400031000400e0010703079500960010021100d051a41410b481140d40524448184010b0508101c02000c09070801d03802003c0503101c00364030001d4898281d082e521150750580041c1d02c14030041100038881d0200340b2260b0b008000040c030380381d02d0380c6621f18181207005800b040300c14080c00b80709072680e00c05a8802061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 633064919 1250 633063669 633063671
    0xa0b07170718090c0507050601120c0603090209060904052d070608010807030201030b010909061d0a18261809060613290c0106090e030703210e0304120c09 68
    0xb001c01c40b030006201c91030207070f0855590356070300308000540202c1c21510300e290408122030380d40d83c2d035074960402c0030204e02e4200d40c0c284642c103000640501a0140306841680100172060541e5200140045072000820540d00d42c810072880b803891401310020a60151540d000709240e440103030b0513903480c200b581ea1000c020002400c00401044030003003001c0b01901d0303091801040041c906001241d01b200140c02c607400f250310380b10000846402010300301581d08104141d030300c41691808205021214550aa200307080e14070f0000c5170020710194800740f01c00c20200d0709070a18070544107a40c2d0b500d4100c1d104503036034403050800c410180d00d84100c0c0c0b180d200504599540c9841c5a02c030001e406107000b03110b0342081c20100b10141514140212103580d030005081802502c41b40115002d82c0a03020500c02c034501c440c640851403030031030008000c40b01d4842e0075480703603442e54628080c0b50800402042a140c000b660341c1896030700260080c8010401010034031802540c2c05100d0410459007074042c0d200351219 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 633066169 1250 633064919 633064937
    0x1080a020609040e0111040b040602011103040f12050c01020c0307110616030e031c0c0b2406070602070c0f06090b0307080c090a050a06020304090b030105010501020604080c0a0b071707 81
    0x16a10074003140c0942005460102e034080d410503440b405003414405000c058017010030085008450980a03204480156000744414001d00c04606291b101c260390192068444009803004516101c207042646015480c0052a09807640b004900326004008800181c3d080001e0720018070040c0c8281c81601e00c3c045942d507181819043c010200010b00c02c0e0020284402403030002825602030000980354541350700d401c9454980110024400ca0030000c04413155911030cc04079103405500c602c05002c52045003003020741240341c1c40410865400009045078825000c001d40d0340001d204000c07401c0144050100b8200c11800c02001410714581908041240c03c001e208000d40305500941e03140d0043d1202c1c02d02e6941e240d1034400704c0c0280d02c40760021a00b00c400d2100014111350300100600444240030010400518902c00700350076036070203220f03480c01a44003c0c040f4022403401801010109816802c0b03c004801c1c83c4e41d032a001d01011200d040c0405c070b9020261070740300d0041015a42c44101840d1070801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 633067419 1250 633066169 633066173
    0x2130f090c0f0807020a02100c060c020c130b0d08070b01030308150a06030b121f0e030910080c07140307020f01110d140f0f0a1112070f0c051305060901080a 69
    0xc40c40021101d4002c001d02c3e440840c041a000303002c032048280d002341540214001d00c401c0a80400e821400c2190b0161034000801001480880d251690500080c444100c0300d1800171018081c0000e06401584041c00300217034000070391080011b1104520501505560f507145080280080c0d80060400f0501c0142015070b031410707595845108140c0300141030000315010f0182c049869404000c4036000144550380f42082d01000404031400c42c40854001404804400d10b090358890060071115078015840c80032003013115028450035544075200628440c2404801c0d2140045141e454410006075040020f00303a0960a0240000343c0f501c0080c20412401c1095040240d96000c00c1203400041001c1c50340e07500c080c45004011107007803200140d4481c0d10780d000c1c18402c0c106540070a1400300450010b901450b013011010505500b900c080300820f508003905908c0340c1c0d030105002503049420b11a4004049850b9540c6100885003415020000070a40f070030105105c20b01710706811007074a60340081c1c4d02c0c0700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 633068669 1250 633067419 633067427
    0x2e140f01020703030909020310050d03020106080f031309021b03070605090c0109030503070b060105193516171f0902030c04120f060c170a15030206071502130f090c 72
    0x104941c0c4000340103230350390f031034000d0302d0340c5110760b60403a942c0b01c1c2580d41242c2c103041d41500f1007801d44211360280e64400717800c01c000070760f640300b80c103003200012041c3c50003080b60b40340360303800b82041c860301c1500800d111003d40c080740e0031544046400c941266a8509005030b89404020036883c4d03500c00e0038015030690458884540e00d00a014008001c510000e0000d02c035644034505a5003400c20040490182c0d460421002e8424050b80c00880202450600c0385c140700b4980c00c0780710f5a0484d64041c10015602e07500e180c84100917101c1c2c104410b0010900526007484214603011b486005101c2850000451802d2410802003141d0b0001c1407050051060000d10410f0200b02c030200c5041e400b076a5260085458541141035000701c0c0646003e1601c038151300301d1a080850080131540c480700303400701a5101c201d01c908a401e00d43c00d4000e4508200d100344014180900202031180c000c00101920460044004007642d02000004031000c02e819000c01900162211076806401101018006138050383e200034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 633069919 1250 633068669 633068687
    0x12004060801151b0c030c0f0801050609070f230a0801050f01031b030c4103011208032a0a0e030309060901030513140102070201090e0405062e140f0102070303 70
    0x2000c0004008020340802c440c10840c0c1006581c043c01c01c2245641e10285001201809e22a00d40d0079428403000a01500e0010840c80c070858003501d030f01d856480852011594402d4421518402c005c2031040d00c2049503010018001018007541c0f084075960500782403000070b42c01c3d80151814076080050a5000c06004080d080010b4414a000501400040000c88001c04803510880d00c0c0c6030741008400c5e041c148410100340200c4144900000e00783c00c205030211600c024070038452030030a0b00b103100000451f40700085810416070041090a1087d05550004808001381154100f020001e003d040d442e400c4000b00c05156000c034051400d007042c12010038040d01c1010196410160b40d880000c04a00c8000c1140922a0300009429401c412540c0464001d42c491071040c0c0c0402d0540000081180840e044940f05541c010007a05c030a4075810143c1028007071811800c807141c24980900c1007824400125070340240312142005100044c00800e020401184828050454100076000c0c800f00340c011100c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 633071169 1250 633069919 633069947
    0x10080307031d06130801020309070605040b04092307090303080705040e191d01021c0b060a0f02240a0c03021201140f1012050708011a070501200406080115 68
    0x510070075100b04000384082c0b2403880700c0c0d10030850744480820303003241c1580a9840764202c4802c4500c0700e511001c003560103000346d00c81d1030b000c1c1d8800c01060140e018250000c01005030303659040041a41f44020203417401e034017103903080001200003c04100781940118040e0b000401070030a24a05410003401d9040104003c00c2070484c1c411804001c07100e80019070040c00d4146000318803600400c40d10074494041d42c0a0801880c074240109501040c0415500c540803611000a10907031811116000584100000441800550003603030814002c0b201c2c2c0038500715010000481240207842d01c0e01041c2d007120083c5009004061040c0710200180c40800d04c4a419591910000500d4811460000e0213060b030581d025a000301801101103861500051248106842030409012650703501c001219007540134447c6545c01401840b40c0c104207080c000060249600078030000c0752080c00c104031000c40c0c3d9201003042c00818000202000303126480400907002d1b08078413800e0082800d003908000c1002d1060b801c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 633072419 1250 633071169 633071207
    0x4090b0f040e1e0a0f120e0a050a0e04170a03061a0703090302130e0d050703120b091b0702031203061309021809030c0106030503042d0b0309070801141008030703 71
    0x75810f000942048003120155010f80f100022604525100800c0070350011080c001c100c2c100800308291400104440c107540d000b0305800289443c002c58036002e0000130f041502c003002c1c40c00c142140650040b000f0280c8150031340b00401c640346447c81001c0f96400c0f02d00b920010a00078000200060750010001c001c03250101c84111403012035010000043c21a102606854420218607269a0380c100e409045824041e454030069502c1c1401000159420721031400d502802c254002001d5200804941141c0501c00100c141021640d90100b45060150700000420200200c08c000740752034802c1025450441d0f2400500400041d580410031000d40069007600d0b0903c0000000c050b00c1080064540c0940004000e00c1101d42c0d900f800c54990b4040e0103584d802d0301114010990041d0303c0d450b1403801c50001c4155070805494040c080c1001e82010701402d8450080d2034001504070300c01d0040c031060307548000340c08030107040240303408251440d41d5110300c0b0b5980007070054101290700101800740141200c0d003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 633073669 1250 633072419 633072463
    0x100b0f0906060c100c080627070905030a0b0a1b02060c03070309050105041101022a042a03020d0b0906010f1227051501050d141204090b0f040e 63
    0x269040c042d040c0c0c1d41c0f203a0302c00c01d1103504072210244c0114158942644400602e61200801e11903240031a40031040290b207441000415103e5410f640390b0321100714a000d440047c0c948d00061b00700b015109007a84e20f900e207601400303090803079485041c0c60000000c2240e5030804d20000c0194540c000240803800414010002800c1c2c00d000390003076404183c0c091b008002c0b5241900d8800390340071074550304600501c00d1442e040760b072148a1510042000c0070f07401e0381c0c1003c2662000c1001520281d0882028008101c0d1000560300203440f50561914a5450140c4c448804407242c40490f0070307940b201c0340b0818000c814006140d81240b00c04041130741d82e01c2c10b983c0c00c3c0041c030ba5420140260702c02e00c80704103552400c000d0000401c011220011031141d400e07554200e201808200e0074043c0cc4c00780b96842810144500001066154005400c00b000c0301981d0003482a02820311803504941e1062034225110301c0b85200c05d01e00390321891502207041f202008450361180115075180c1080c0400707181103003121 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 633074919 1250 633073669 633073681
    0x5030f010e06100e07230408031209190b1815011a030601051c060806070f0e09010e07080415020d020a08060a180908040b030a090309060903050a0b0a0f0e030903100b0f09 75
    0x101c1d85086e8075014865181d0b5280e4070320a240c0e03240d00420b8418101107c0d4030101d022700802203980384042502c0b0810615100345501d60a80b014409403490140300e61032040604007450510203141044104080124650f03d400e0300c28034120307080c801d0340ca4906420420000759a802c24241c45a5000410382d8481c0c07041220150700040510350000310b464420748040042840d400aa5480680d010f41c0d98040d0101c8160203010150b002030041b402c200003044002201d0300d20074010309238418044d0482d03500b080e0f84071100303600b241c0c401c0510240d040d800040381083c09800250141d0040f07015907006140c1403030000302c1085214120850b8084030f8803050300d0301c1031011034800e40c1c000c0d00160001035924180030f9252002822041401c4010481c00e4500162050080303000c44205c941003005007e801410b80c3e50113a24078401032004a02e030b0341c1d46806d90341110852107030303800884060000315a500380f1141014030f400584001142030904291f4900043d40b60400118460081550707141c1040d01d8030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 633076169 1250 633074919 633074957
    0x30406051b100623091009091a0c091f140d0b09010e09010c0c050c040b01031113030c080f1009030516060203100515070201080c0405030f010e06100e07 67
    0x40c074901a80103050400106010aa40144040d007113811508500c4800c50751081c0103224100716203840d441c0c02d0703803541040b00c105242c01c4078403468480d0003080e00303030b1a15051205404105031540c816903080440d0407a041d0408141c1c40300c40e000da05070006a03900c1c500b40000c2903c102801d001c44002170105a03020704003101e030050900110000d0881c0e0f050f40c1c47c0e42d6404a05502264403801940c00d00e905200305502a00403145919007250141401c00980c50510002c0c000d050000c0f410540da0318a103009000143c0c01410f9482e1400f5001c1248510b141800c01074010b06400c91000768110441d1980c581c1c1c400034919041480c4000d010602243c40d04064405000b20502c00111306400511102000b590368000c62107402c81c0305142c80d1450304d0343c0500070f010305034402000504070104201c8002d980a13000499100007030504441c6041c0c0c0f18008603042090311021640107039101d0015410340b41c01442510751001200c130040803950725203241040f20600141026080c0008000c541c4104051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 633077419 1250 633076169 633076183
    0x4050a12031d06091209100e0a091b0e09010602070303033b300c010e01110403020a0812040315020d09030504050117040507051e0a060905090108030406051b 69
    0x42d10070001c1084102165920f03500211441003090050000ca107a44a03008019074445100c09011035201c940d149606995449928000c06d510000e901000036000220340078083c0005107040c1840b0000d100c010014142d215105c400e54884e180b5000148081c9900084000c03c40360180780100b134002480c0c04500400da0b0001c2d0f400c907880c2c092070310720300c1ea030501582e0000303280c0c2801e084615190745044104007440d60a40c59500b00f650081610060311802c0016180d07516982d00001080640c504000d4212948510048455140070504105601d031035404100100749800103441c030141c1404903103c143c03145020081040d0f04140c40d00340e046220f80d041d640140e000840c20064140c0a040151107a00310380320f40390000e0b040c4204140c5103500d0036a0300e4003d40d03104001301b042d981450100040004442c0a5490010f18080503c845a541c510310800a0000c1d884961040342803030140294010140c120140c280c0c400c01c000c009c01907004044070000b00d490070351500c180245041203420000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 633078669 1250 633077419 633077441
    0x130b070e011b0c0e0c04080703030507111e04061a030f071404060203040f0501030b01021c020c060318010e0604052e091b060309020a05100522080c0904050a1203 71
    0x8075609002c2c04103c1c034011644240d82148110000c20341d101e00c10503065204602650701107400503082080040d0240014201d40361192510a4442e041d1f0408103016641104842c452440c05041540060400d4841c03100030301030858882d2149c400301e0b004402644070143c1400072160500000a22441c86210188485000b106403141c1d600d80d00c2200968030780041c05461096030208100051642c003a1040100307211040e0040d1603a0b80350618259503110000084070194058441c4201480d900c040065129511181050381c121100d0840306084a2240201010a500410a02010800c005002c001c0200001d0f08200000c113030828000c01151a10b10038103402c1e0805404000b00305030b204030312800c4038900c10310010050344c82d2001c4054801008000e50441030302d190600c07860400004030b00c5140d4071402e140340b4092600e034420821480205a4100c10000341d201400001030030300585c191258212910310b0230382004d860b85a10703840b804800a10b950800006005028040d400c0352854103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 633079919 1250 633078669 633078707
    0xc010b0a030308330d060e070303050408071d010e0910050a02070201110309150c0a0f0302030309071a0405010516050304080c0306100b09130902040f06030b130b070e01 74
    0x281e03903490041c1403418103071003440c411002411031041302c072103824013140401c02071035221001c521100140300166000f04404d6480540b5114800030100e03040041030f0080d48a5603600b0b5549140c9034107181480d01c541c100c2d0750510fa1522420200704e0325070403640d05407084040c0c1c40f055034580700001071802d40340c00c1c01040110700303010401c00c0801c01075001d0040742e8003c0e214036407865503100302e1a45034403070580150750004031803641c08101c54491018040b104041070031a202529076440c3e1041030540c00c04103c00591001003048044801030200b24014500c404526410f080e801f001811503010f18001c031410864085100c005030b402d06a00402c81d02c0d0010700b074944d19034843c0c10722a00c1703480d4207911501920032100843d8800c8011100c00040b03883c817403006030500c500540ac200d400c91302c508030307140140e4403000c2ca0405680c2da44524088824178001c0000c0705451071030400342104000308100f50b5000701180020100c0c9c03100002c42e07441000c1d0300c1c2106044540c4ea0050311110b144000c5580b80d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 633081169 1250 633079919 633079939
    0xc0f19081608241909050a2103050603030405040506031509030a030e06130f0201020a080a120c0215010e0a0609050c03090c060717071703070216050307080606060c010b 74
    0x250540700c41d040c20794030300a040e01c04410641055000680480d1a105070600c80791000a84000c00c1c1451107100c0b0780c8140c00860500e030191601d9140c01a100c000340d1f4a8075025241202600c1101c141d00740c2000d4504007401503182c56800a41c80f03000e00d00c074803401151564001000f035581404400d149440e581c2c03285001d410981d050660301e401540500c00030902e403030700d441000751001842901c10542184000005251039680030300503021002c04a040d481070a549000056103c4042c021041d410740d52481e015902a44020944800c18030800c29908610101c1305003511540390b0358103584442101d0441510f0b200580e5000f032015a1113035011a281c03400b031141d0300d80e50200440c00780f01180c044a103d23244680800c0315038850020020321400c1c8032110740c6031364020000900180741c018003003451b4400c0030146082041e40201c4880d801600050139821400b4a060a00d81c0900001d41c014100541410309059880101502c200e10030039003c2415180858250404070194001509010305 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 633082419 1250 633081169 633081193
    0x30903170906130504050606180d0f05100f05010609080d2304060c0b01060809060103120507080c010e1618110d06081b0607030f0e010c0501050916080c0f1908 70
    0x50f1168020355216074100ba02203285882c0040c03e03244a040440c0210780c00c01d010310108155445400700c1100e40c22243c60540c00401c4091141012001d0040408100d8511408940c012104142c20600600145001c14000d0100000f008007c0e01140d050030b1080c1820f035007150455503d141c00000b2022800a40812015440820108943e00ca03401311030290342c848209a411030400c44101c2140e9004c1001000401c00c0800900a12a42810030500d005440e40342c00c4240e84c004060110169182d14641c1503403070080264001071101700c103079240624201015034010782c0f100b860a10340b290321a10362042c181d00c1d1600b1514490414142008855581c2e041386407120280381003040c02403581400d0000c1800c003002240c1c101d503031560ba6210440c0c45810155494042d80c00c506040100d900240800a4001d20503a8004c54a0a00807c62050b0803003c0c950580043d0f08051030a070000b001041498940c440e034010119400c071120141d101d640700004041a0341c0d0342c05001c0d00d22464a500c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 633083669 1250 633082419 633082447
    0x150904170c101109180703020f0301030b01061e0e040e07151106160c0209040f0f030503060f043c0f1b0e0102060402150d02071208060d030903170906 66
    0x10b00394031208061103078440e0041c0029641c01070b19916500540c02084107221648141680e0342d12031024180103003030140c48007081c22650400d070000c4440180d03040040c0a034540211607040c01c6540c1c001c40a41080e400c0030700818030b00620704800d02882c0c0301c04130390070780400500203900649443c0b90350722010704800c0c0b4000c01c04038400a6101060290300f021400c800c0c000c20101d20406440e868040d10661264203118844200800a91704139404100440018141c19203c003020790007030b07490329101d003050420815110101c180007840743e440d298504c5818030032015210009544808056066802d100c00d0a40031403040c0e214040300d505d40a400d80000c21a0b0380301202e9244208150142c0c0da500c001c05641800703000c508075001d030340007000040040c40c0492655003a07221170340e621810b203a8040340300816600004c0b000c48203c1c2c042440045e072180e002e0302859100d0400c442c0e20440704200d4030041c2036480b5600001d8007510300011000c040b0ba0855045031480040a0011a41c0b502400700c5e202e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 633084919 1250 633083669 633083683
    0x1030c050108040c0b0901030207140619021213060209060a03060f0e0415050c090301150920030a0903090f120605090d090504021b011509060608150904170c 69
    0x95924a1909010800e54451800240704542c0811182c80031414040d03405120382001e444141003540030010300b40010007824a903180344224030010145130030051124015440100a84420248103008545440350000c002c0ba0700410b9503e0392207c5461141020006880744582c11500403c0004e4a200801c2d4168020000c031100b00706481003554585101c0c1c01c0508041d10080c00b140804030341c00c5611042e40e4865600030302d041500624085981001c80c2c00c2d14204c0034a1180d900783e140c1c0411881d801401174101c00002d14503208254861244203240740e00000e01001042c2c0e9480c2e480104240c011141d0700060150100c100c084140d44614040c081c00e900f0f041110041e003040082410700b00c2c0015162051003064454a42d1b550406042c40003c4d00504110400a00c825401001c4001c00b840340805014030030014031481c508141c00107054400d00d0303204008101c858020850fa40a03519145403501c041180e03998030985460500c8100c0810582800b0242c2c80001110b0030400800130ba40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 633086169 1250 633084919 633084923
    0x1020d050f040302101b180e01061d150313030c021e10030605030c010509180f04020312090904060f1b02010c0314010510032406020705042f090a0e0f0103 68
    0xd56562019004c03203006e80300401d51540d070307140e4000001c0b40c010313014254507140b850511026440440d0b80c0d109580e0210b80c00c0e40544d01040341c0b401d00400388400006810710450342070b0f42080e514801005140d85a2200a00a94070300601400fa0703400c00d80300f0070025801d141c00402c1146000915040112680f900313210461040380d02c585022600c50007401440d04076480100601440980384005603103d07030040a85591040d07000403010140f4182519040c02842d216030361300c00701d1a02e48103061030100c2039841009180c105011a00c0c4507900d9100c040e520945c40300340032550f001d0000c650005072100081560030500c01b8615034600030360543c04a09403080300c0e9414401128141d5025000440c20301485400000748010508814001d8100f8841d6008901e2014081c2d800c0b417201c1c1c2c9960315a6000320005030005032081041380ba090244001a40400028030882800c0c00668003440088004140c0801000b00740d040c1c05a07203801200004001400000c1034501d0310300031141e80b0301024001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 633087419 1250 633086169 633086173
    0xc1e030105040f090515181b09060604210f02090f061302070b010b0721050913020f0d09140106060c060e010e06180c2d0102010e0a1401020d050f040302 67
    0x16001280c45401580c0207075401030054100c1004085e009030071b03c0001030441d5805500c0901070401100c080001042110b514000080004196402c000c54414040c040c43d2244c0020302040c0110015080b86286d0111202003079120882d4600d41303018560b08154001c2d5011050b40c003001a846007801101d40721ba802164079000d03001070070b42d40004901640d9000703031205a002c0e005000200722100100810b500400c849118000004e0141480300007403103e40c00005ea0110700c00809042500004200180c068015410000f051011f0681030299030303ca43d54083e122b00300001405504d40032441564111802840ba10343c44a4001d06108211002118824a020000700e8010f40622903240060300070000f400c89601c03003100d040700c0f5071040128903401c1c4c06508050132090361001c10260b580160496001900c00b807182c0f01c4600d100d0000c3c051410342e4140407400c1044000030400e001c6041d481036039000000b0030391009074020301405e8654800384e07140030280324090b410350101a1283e40b00b642 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 633088669 1250 633087419 633087431
    0x3050609010b0312090d08090a0b0d05070e09150d060c05070318060516080d05040605062e030e030c030a091517011a070b1006020714060307080c1e03010504 69
    0x9144d60741904900c004000942880501d040385807401c88541340740d020740c84240c01c01e040c03240010721800043e0b10881d0347c807900143e0301501c00440d000385a408445130a00500c4139103004042141148004c1004e04820404007601c030701a0b6800c031030850640e4001c00c04001c601c0110001400348c0e404494140d002c07c100e810b400d4040c602038040c00054810301e40e542e5003045080b02051031514043e207003c550002c02405000e0040f02e25105551040b80125004600da06018080c0035280c1e11904030820020009182804d4101d40d2036982314a40c1c155113400264080742881403411030240a42c00340e414000003030780e98580d650101c0f808068031030404007151b1543c20032006640c14001d1000c5079000d4400d41004001c00303805504c0448810304c2e0204040c2c0f40038642e603500759030b000b401c40c2c4091802c000c0b440107000c203a5041140b031000e0044148130000300b0403443c00141807030000400410402400000060101e281c00c825181481300c030907003003582c0414802c03c0c0c603120b4009015130350086107425 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 633089919 1250 633088669 633088691
    0x6121a01050f0720011223070203070602030a050414060405071403010b360708070507031106100f0f0303020c0f0109031a2a09040504291608091903020709060305060901 74
    0x22040f0180301c40b4015600a514007c0f01045420010080c141c0c1c0940c0810f03c0320740b011417094001588200d1106000103054130341880c2007901074010b11407003c2c883c0c0c0443e0800c000540d0014181c415642400105120803445100203805002c030600280d41015408007800e0b2507500749214800106658420516400c0055460400029040750700350300054005010445860250004224a0303010f480e00404210101d103140703103044401d55100d40301490700b000421151342c2c007024240240100103240c40c41540b446c2c41c001e5942c001000c10764402c20144181910a03070190300300400031a407240d4442c4041031380e10f100b58030741e400c00c0f56400c61041d0a883c00100003c0b4609910502c0c0810704142418021610140f00040c10010f0046031845e001601c0b8541141c0140e42e001080481e400801d07450f8a2705207403000f02d90301c8006103a0140805072082c40f40ca0b42d40401d2690f2810410380050201e1000c9040c103d28180c09075010b44800d515008001c418000081040c0b40305a00c110024840100c0031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 633091169 1250 633089919 633089921
    0xa060b010203130b070201090e150102100506030d05030606120412090509070c2405090c0a0b040e010509070c020d032a0c1401020c031606121a01050f07200112 70
    0xb074400040f10340c0300308405010f942c42e1000500542c0e40180340560f0b40d035449100d4044e8005055600c1c8400032a12520100d0700e41e81004400c20404250718280250b05089001c0f03652513108101c683e007840008030000306c00307860f09826206020040c0d141c2c00800d0416040a8450611402508000501014011507182410307080035024503896620750100c84001e403141c0d96800034084600c221060195200b20201c022801418050540080588850002c0c1d1080185154440d8040025004140810407a011b05085280d04554054401c40781d41d69621030115800d516a84000f540702707503001c0303082060580c418180c08903a0215202000c50385041c412002e5100340ca007100400810070003e044c00034515074211280c5051041c011606410403802c0001c0c00c2611040034012050a030002c1000710640c0615415542da0000c00c1c1000f0745000a46071055038081c441a041c1032010018402840d45404801ca030055a0401c403415680303100e48a2009440084100550000300001c003010102000307 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 633092419 1250 633091169 633091177
    0xb0d0825020906010309050313060e0310110703030902150706050604061205120912060f040b0115120c0e060d050702010c02010e0a060e0307080304080d0507090509130804170a060b010203 82
    0x2c06414103aa03842c3d00450180024100407521400240700751040c4000a100403400313804588c07591401601c0391401d1603c1c0c0049008008030f03142c24130325568001030762101203074a42030701880c0109181c0c0050020940249502003900385068001400e2014024242c0c0030b00e0003510121810702c03800b0340c0d410340c0040540141102501039000b00400a144890b40c00041540d0080a0001d0340c0d45a0304040b41802d00004440c05040d082400c800c0204002c1101c41d07050140809048030103203031002046c018a641c20100001d0350300e0f6a20101040c2d081e000c2c41c0078080311000285080d984008442c110b034013401c01a0f80c500055070030111052041030040c001c040d10008040c0003032071290015101d0002400c0005604840c1d03020030002a40820501002140300e2401100305a0f582d003000441c01003110001488101003201c010342c103002c00d58403001d189402c4101c0509905480e00c4900304940030b03106590110b0400003c41c04102503030032010138490320050051008112802d072840042e80c07280720f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 633093525 1106 633092419 633092423
    0x10c1d12012c060612030304171612080f0c0f070c080d02240601080c090a15090f0e04020d080d1103040b0f0702010606051c0b0d0825 59
    0x8030412001350044001d4a8109a2003444050642c6900020b04001c04481c1c0c3e1001d500481c03018001610f43c00c0302007a181c6011000f01c0d1401c0141b103441d001d07030200810f0003840003030751072103512010901c40c0111b94516460640c00245030381045c2d01240c1c00b181d149440742c4005c216801e081002c94024030b0103400900100c060300032200540c0d9085800c1802c548158402c011150341d211540ca03070801d0f1040b8450303443e6400480080c0c032020b20b60f006500d64100504407441b03043d50002c5203034111501540e00c150f40544540c06a202010300320340281d000142d00541d280042e140300014024841401000511800702008442c10782d402900e0594030307030781c9420074415205003241702c054121019000800006290010150a41c000c03a02008604101810618901c05d9960042544038500a203482c001d01010325010050340c00c41248200304110406090840c0040a40b000d11b00d55 = true := by decide +kernel

theorem cover : BRFrame.Cov 632913669 633093525 := by
  have h0 := BRFrame.cov_init 632913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 632913669 ≤ n) (h2 : n < 633093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
