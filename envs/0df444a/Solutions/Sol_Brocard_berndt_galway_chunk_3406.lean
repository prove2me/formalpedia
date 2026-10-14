-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3406
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:28.01998+00:00
-- url     : https://prove2.me/submissions/54f734ad-2703-4015-8959-df3b866487f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 612410071 ≤ n < 612589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 612411321 1250 612410071 612410089
    0x2070c0e0403050d110711040e06130f02030a050a0c14060901050a0e0a08010618112505010c02030d0605030321071101021809071701030f030e0306040507063b 70
    0x40007000e45050760f801050040d100082041600c0b40d010b41d01d0010f05001044122401c02803401d106030840000101c0e00c80bc0c0080301212188110351120078108140c021a29103070100a085626030f02500c002c406002d007102400c0020f10405a00f120812070302d0b0302091542c05800c04003410310a000c640c1d01c0003940542100140d1440103805010701f50b9803005118042c1c2094800c00d0703005a0305940d80d041b02c00e8180214000c9840c90010b0360715190302c1039548074482c1c65548400840e25503100392040050000c0c0502e00d84e503170040d8015a02d480580111104503030036540194404d500421405018200740d00c4d0304000c81090059591444d0340f4800150340103002c50b8110501540b00150940c4941c3c035018050281c030310309859882c40e5a450035800d44010049842c4031b1689072401c5c00400000c0d0b205800100000e03c01d180140760340d40c000021900e000410740e0100d91035048940e00f4080941d010f00860385014903083c0307101c20300c096240380d490002031070302d505000044000c2c80701040f07894600310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 612412571 1250 612411321 612411337
    0x30503060d1b03060c02010c0c11030102040f060509180f06120c2206060305040c172d010e1c0c1a09030a030605030a02090c1c0c050a021002070c0e040305 68
    0xb4903101c1c06402450515094540000c5078144c0c0f41000c038444c0d280c81441540c04910040c0c5401d417941d0301644034400e100c85280d041c290b0640d0200400f142c120103900c0d03e00018a281d4940c661603581c0f003000c21048600005034000148818410820744d41c08043c85c10b0b0f040881515035100c0240c1600300e02c1e041c07031200340070030f60030650b076170240c141c4003143c14450110b801c00a01d041240c65100d20045040c0d420580780078010720100703881030008803250030040740756200c500122030203d10b05105820411440140d24285480d80d19001001460280030768000035640d03802404090409102c2e50501100c4901c1d400b041102c10300340402085080780d5180c0c0d80841404064801d440c120505581d40d0740b0000c0c4420000e41420740c000340500f000908014065802030100950740c0c0c411508409940240f0803105420703418041d6016005803030320039802840348644e0b0300b903560100c2600291402d03005139000500c0520400140e0046111a4202810381d01e01c0640b040060f1140c0c102100c560040180b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 612413821 1250 612412571 612412583
    0x50406140118060801090f0212101503050f06040201050409020901091d0115050304030c080d0b0a0b0d2004092c0703020f092e0e150913030c030503060d 67
    0x10012071600180c00c52040b8494880d0410b000d202d45400280342601c81001c0300400002c00b41030948010f01c0d15100c0c080c03080031031008841a0621507203114060b43e4540c0107002142155a1050040c041d082c80311000c0200780100806050030240d00092440c4258880c1c0c015030b5a020aa030006688100b0314070000f00051011460101402140c0020f482d1080c03040c00b1911600241002105004806503071007583c01d601c8800c041d1003203895920503944003404554255a40c1c1c01c10003182d58805403400c0c00340c070031030380304944510345200420200d0300719481200045183c16a5900d02c00b0004040354241c82c2d40036004a9114030300c40d40504144c2a649403426408051150820000c90008503001128000c40380001c500000c0400d0000c0100700360b4545141485040c0707400400c1d03048043e0b4400b10129000c42111160759200380d4038041030181d1f43c0d408561912044040940340981d4519000407a80d644104580c01c90b0b903029000c0035070041c008040c814040700040166030758a44d901f14450b0080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 612415071 1250 612413821 612413861
    0xb07060f14011a0d1a101d04020a03140403020708060a0e10020906070804120c05060c060403110c06040b1909050a30050109060f020408070302011b30031e050406 71
    0x350543c80400704444425001d45040300755072a02520901c5071403031116a01440c00b107c0d0081100b400044d6004004013018151549860ba291030f1007158507620850081d40a420050300700b40c0a24201000908070b03a800504015000d4406400407580620f00c840d805001660740004402081c014059944050f01042c0702040c005420845649100100c0384204256143e0607164010070469000da4980907005074440c40000b00000e0140c502030108807218030880342490302d50700008800303034020b8101c1014004003040d0b0040c203a480b0184d440703220300142014480345051001041100b400e510403044401c0701881b00e4051500700fa0b900c4224100703d054880c645500c6030520724040c01180ca0700700c801a142059140840c0d400e40b003510300360b0791410054030000b8a1900110349001c541c80010200303406d1001038800251401c0040503909040705001010800840039500038103010410301000d240c10801c04074051781000b11006290314144000103813548607820000700900410307500c241c1c1c200c3d0f11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 612416321 1250 612415071 612415091
    0x111b0f0a030f02060c0403031202070f060c030606180308030f1902180f090c160203030c010906050f070518100c200a080f1207030c0c0b07060f14011a0d 67
    0x200b280b807864125075400b1030702c2c1034a0398141d1400301c1c401c0384801390005100c80701e035140084880d00182441d038041c00f10903507980925107400c400c4039540b02a050200c0e41c1d4034010401260000c84521380c1c0550644210003007860350700d481000703100090841121040c070310000760250501100c0c034410b0000d10031003151108194030020120f204a83c0030180b1444100b011001907181102041e07108030ba41c00501400e0581ea0202c0c00d0645180c02012a0f16020500000e51501000d22452590034041c240114003410308c40d052500b9201d01400050030850100301200c40103203c1015203040725420b5070071010481000c07000b02ea8582c02824014210614068070f8115104c142d04540b110540440d148540203075030b0b56110359a00398448520714103400903100d0a142c40c11040192403c2c90180c00c2c520384e038003015610b445504815400482040350045134803428410244074183c2003140c00182004810301c21811503041071014460300000d0708040182001002c81041599030b02ea82d080340600841e152 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 612417571 1250 612416321 612416327
    0x70b041b0b0f1c020a12020a0507080c07030201030c021606140405061b0106210209060418140c1206040f14010f02090f0a050604030f0f0807140d03111b0f0a03 70
    0x100e002e1908043d002d0110307040c0250700700d100f25415009541c55509840050780c0c2510007a4210301541d06c2481404d202044c04100f44900500511120710301a21980d0f00314030014040b229100c0358101190b00a5450326164000c10b44103c0c2135541502304003280c03c604c0f01c00c0341010700c140e411864005501103860700c58490050007080c10b2268440082c0000380d21015a003820403202c50941d2250051305e0072000150410001d016040b88000c1e001207801c0c5030010400030480c402481c112207441e01c00d40d404802d072038180726083c4c00d03500071100da841503082c00c84070982d2038201034005015524082c03181020440f01c0682e0004d4854103074000c0c4150740c0c0209030403000b500a044198001c10a5618404281c40c1144001c0300340c030402000300c1d0925045880ea01c00c180e0f9089011981c1c00a44174030600842c01e403002a0032007a100d1151800b9070a05601180d0400c0d1300450745c041454100031540700707202900700070b64191040c000d020070344000d401000b640c94020203085241e002d0103044652814158 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 612418821 1250 612417571 612417577
    0xf020d0b010801060509031b040209040c110d05070b06091305160311060307140c0a0b010b07110a0513020d060527010f08060601031a15030615070b041b0b0f 69
    0x802602c6040482c3e9a4050a8aa41c4108403e00d81d0540000d4000450700d80501800208181c003d80014200321a03000070604440c80f011045020500d5030400040764042008143c60404a51070031f207040107136903a9a01c00743d40d8040c0c480c03803045010100142e61800020b4121441c40d81200c00c0710442c68040d160403c00d10200c0c0816941c3c02148907800905040110490b0300800b5182e0307e840f107070621192070200d907030001920300348a401850038500c049521070100c20301805603e00b8550796050036181000a103145103440d00d00a240014081245a407101002c506058840707501680c0c1d4001c508a060003800140c10a07540f16014440321910003010315031440e00c0800700c806076030fa641d17214480000c6000707492281c2400e50784408002481175101e50000243c0350741041a407050480c13032100251180307118404a208801010007008150701d055140e01d8260390701628040d19019450312014901c01380144040c040202100c8924040306211b82624001c1c503179440b42940703030115020004041d034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 612420071 1250 612418821 612418841
    0x20d0b0105040c0809060708040c030606060f0e030d23132603070b04021306080312040c060e0901030b0408040e01080105330d050f0a050312090c0913060f020d 70
    0x540f030030b0000203006000d01031041c018841c0d08010040d9035100e140440351050000c00440c0c81508118000002501d03d0103404003914a985840d500604801001400c0c00300310403142d4443e5104042400703c450300913840d104034154440b028401ba000c1081004070714400c1d01c160001428510340002001140401c065420581500a004482800c03040746540c0e8055000083c000c41018030200e0018500704035094005602c01c0b602040c0d00d9500e4060307a09581140782c80c000251442d004010801803121a42c4010304800c1c01c00260410705040441c1a08005000c003c110845000c041024058001c00750b80c0103040703501141d800e5684400c0c0c50340c0640b0342520207078100d03980e0b0406554681014041c060780324122001102c2078404a108001c07a0031711030390f402e4956008059044003030789000c0c4841500c03603000c2d07802141d80c2e914218045d4410300300240403640c01d802c03448261040d50360b0f420b14103803c20950594070220100c0c5041c490700078542d01d910b80d03480c0b5100040080b9801a00e4220b07113000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 612421321 1250 612420071 612420079
    0x3050603071e0e0c040b0414150301060c050d080c0406080c0906070f0c091b031a1507170c070611010608030a090816050f0d03020f0703030203030f0901150311010c020d0b0105 77
    0x44e40302d8402c0b80d07a6074000e500404152900601c03041c8041500e847d0329250460004144204a001d454410742c003030344c4280c10000c0080c00c1046044148601003150791000440384c1342401403450443d201090714013807030164804102d465808a0b00960501c426680040c900400d190f035209403d142031003141281d600c6c11960105106000502c00303580d807040118a0b6039425201c00b4000038004200d000303205404098110303d000d8088040f0f40d484d142100345405140411060b44c1f6819820070b100301449502c08064418010001c0410b2031701d020481008664003410044842c0036001c6542d4054034141d042000c15100210740c90321029403040e8090304540d0100c01780c40b072401400020300c0340d07152680100340d000301c0100050f034107030f040501d0b01c494a82c4c0284140e030344003144420010f0404900f60700580060344040148241c04221541964002411034020130084030002c3da0030110201f288800303080c0c0001d0302c09084041e400b80b42030000855000b8140407029911f8982550020000c0c001c142c02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 612422571 1250 612421321 612421349
    0x5100e0306090f030304032106060210150f0e041a100f0506030f010b030c070515060306010501211e050907030312110403080703090b0a050d051005060a03050603071e 73
    0x1d50840468806100301a58014514680d42d9890654003295030b240c9000e0382403c440111899945035100ba800036103040d4bc058000080d140c030034041918000b02500140c0b01c0a4907080001d020a03040007012140b9200744488180e0b03481c1010311a5000c041891848071900f45c0070840d644518900310000d40744043c864007400360b22078003030141034001142c2d00300300700100728014400004200d020310b03400200250b07110b1404480d952418103148980c0f51004094040c14181f0070f851a083c4101805050b0030718005203007103885104a000c0552200040c2c1c0019507034881c0204840d03520b52005002035016038284544e042c10039000b80d803000c4d02d01c8150001150040c0b5881788004502a400f40c20030b211210604103829522207004603030181c0390031800d1042c60980000c40c00f0400024055464107500d46945580b9810700140945038000c0441d40b000a030b40000784040c2c0d0b11034003a910921003615000a0555035480030a180142c5600712501c06040d044100070048582442c0720240c604145903480307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 612423821 1250 612422571 612422581
    0xb0106080105090f070807180503070e010f09020f1225050304021206060307170304030c0e1b04240315230f0a0308031504020304141902010f030e0705100e0306 70
    0xa04c9010959114000503001c002182100d40324550000c40099000d01030040c81380d07201c1c0040e180c038480350b020660a100da440100190318500b00c00300b00a08844100b5031800100120f12811489062400d0200800c141c000c03850150200141c1d00d44041c050340300c1e40403c1c00b241d0002d4120f400440c0c0c1240700b00107012490800c80d00102d8181e004050180080250fa410003018150b120020b071125000c600c8103000c0080843d1848040074010031009400901d14105644001c178001c0110000841988040000f004030005d13135207030b9083d0182e8104070040141005030b000c4024140d055018035803c000c1e100003240041c110080c61070034076080884181022240c0e4107003c82c041c284000309500c081d1400c8100080340c003041c002d40d800031100d4102c2c0103808400c6e0000302243c005550540350002217944a08075030408006011a1705844524824000050b60000341484d0b58218010b04064482e8071642960200b00a00f40103844000c0124000703029009008051030152842c0500c40c1c858680411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 612425071 1250 612423821 612423841
    0x20d0e1603020307060c0f06052a0f04060507020d0f0302010f1401120b040317071d0d0b0402040b0d080f090306060d050a06020306011e0f0e061309180b010608010509 73
    0xc82102d5000e4080d10780d861030210240c3e064118404243d8210780400e040c000001c2661140c1da2264040803034204000b40b1325152402d800320a5400c503009000c0c10444110040300384030a4400700d40f02d03860459598046407002ca902c44101450040003400c03c0030a4804254041d04149000c200a800c1082034200d0341c0c4548052031800e101c0c07562240d265184d07100110380311140040d0711034040d00380200c2c0f9280f18141601810070841d025070002c1d422001a403003000201c800144400e4084a83c550324a80380d8942c075401c04d0020300024800d603518201e5502c02d40b290b415130281550000c031695280c00140c002644140d1011807128424047c00000544501c0d03c408520ba03041d8100b070041010180310740d288002980b0141150341442644800b10031101002041010220310940e1100b4a521040300003400f940c058156240c85800144003868282c072251240340101c0d54100408100012902440300b80b2412804c2d001d01901031040011078441d030001da603035040361029919001d480da104400c0c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 612426321 1250 612425071 612425113
    0x406030209010b1303020907050909010609080309120f030f120708190c1704030f090602030a170a060b0408061603020f12060111100c11010603050304210501020d0e 72
    0x80d0711108007001409070b01d107024084c000d180c0c2c01c902440e04554407500041c100b1171007181e9150001c4c0c0d00240c042c5c81403c0141d06180146028109680040c2c100030002c3d840b400b441c080f0754000c010549014003a01010028000c20388600310a07243d99030f84e01034004031030354485840003109250349401325480341d20a4401078801c0c80f64260905402d80c8808030709018000c03040c00001006080c40e554082d4082c1842c0b254007440c480c4d15440030362142d01c0000351000c00307140d01007415504140884004160400c21070750340c60342040101036030381c7e83d2110040c00800c1280c00c2444414408500890304a40c0000d040b0f0044a000b46102c01c0500d245130b00302d090b445280e07095640141c090100080c401c410307801541d08400d050403c1d00054110002080c54046106d14074607043d030319200c082d041d15403c0480343d407005007400000d000300d03400d50f201ca680c0c078481c91081200b0030605a100289401c10f403081c0254290740039000b9544c80c070402c0e040c80080d08104882907180e00441a464094440414407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 612427571 1250 612426321 612426323
    0x140904050a020d06020f1603180b0d0905030f130e090d1707200c04140c1b0709020a050415050702090105011101090c0f0303020705010807020309040903050f120411040603 75
    0x18500800558284400c0c042c1e10700f42111442d80030b0222118010340c0b98050700d40b486030b040c81c200c55040d5904004109090160485000c510416420b024000524080714080c13080400c002c528030f030031850728078610321a200580c1c44122000c80e40040b80d03c5003c6008003220f08040d0386080345c1c0c0364004400d03102c0c2e812041c00c4022940814a22030b2620308090226070180c924142403118009040c000c1007d101d00600054030384d0414258400d1500c0d05d0b2047c1ca00a0078140400d0b005072030280c2c124500d41c440c40502808216520a40000c400c00c1000b105010f02402503080d07443e07072030321000900b0075001802102d8444154410120145200b107050f544200d03002010814103074a0b00006507051071102840d46d005542b50f103811404184041c8050004102602c0811803091131414003c4c1000c1d900e40026040010401c14001c0c039650010907a040e403107040f01c0014482025240590b61441422003070700641102040b404100045044002d01c118024103001c88450040008c00c4100c1c0c045000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 612428821 1250 612427571 612427573
    0x7120b0a0c08150409020a050319150605090f0402120a032f0316020a0f180506030c0d170403150f1109011205130506010f080111090f22060b0414090405 67
    0x60f01c1c801403a082d0040810140003800034061141c4440c046400c0c9142c40b90360f07001ca03c0400900c0010040204030b003081074820000304200880c105800100b49001c040d0442c0030074aa40070100301959610b01401c0d500501120407140382d082a403501078501c20040c4800084d1f002c0300740741c80b5041c0c0c0101d18181c550720404405103281c0320061035241c4a40200a0081c0c0c2c0114900c100030070742d24180c00d044000b601041c14520034214504443c0700946500404a0703000b03412440c660300380e64070307130880c0c2c614450391085007824803000246507406140910303400604010004060309409014641c032203e140003e40800740b000244a42c081d071900e10031142c0007800154440056801c4440c1c030b80c4059009031140c84040c00c80b010548800386818800e0300705289400e1140701c00c0007200024030440381c6c101100802a8107008040c0e00180c3c410202c02101070050b905d4520351440c00051402c1041600240c4408004540d110518510710340c1213030061010100310900c0310940f034074103140658491380e4050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 612430071 1250 612428821 612428851
    0x181217060d0b180105070918061d0c0702040c090504051303050f09041b0302130603090c030605070c06090506090c0102010212070f1434020d060203070207120b0a0c08 73
    0x360325542d081c54020300000454981c0c4a485011850a0142a0207150903640e000c90342414100b8002116038010300e502d01451410008200d03802500c0c07040b0410241c0c07124041c1b400c2d680d00e1403d80d03452207030b240001c2d449441e140c2d07100c0c001900b00d0403c000b03a600a50702009240d513203200343c40384030380d040e40d014010640600c40f4a03200034404005180d10140504046111840c25482074a1100064004004030f900410355010080000c507c00d80202400d1070f060007440200e444510b000d0400d4040500482d480c0e800281546004510605510f40d0007181001241d226041513529201c4c01d5501400301c1c00b4206224501e584140250348454182d003404840e02c0d1580d1b9801d03a80c072003c2050403401d001c03000c4075403000541c0400107006140d5002502114010300f05210006082d0801e0701940a011002c5d8031b00b0140c0c446519200e801d603405130006903030362160720b401e030300e05405548075a400843c02c0d00140c3c00c1000080b11070f40141e1092a0a201e00c0d4071105058610007811651607509808207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 612431321 1250 612430071 612430073
    0x40f0e0f070c231006030302060c0414060306180f061c0812060f030f0318010302040b030a0b130606050405030d030209010c0b1f061805040c02031c181217060d 70
    0x2a4aa000c0c0b00403d20b004001c054282500b50034049414601da8a842e903803c030400c00e142c1c05200072940918040500e6240508007414021542d5030824060b00610f0040005042622515071101c042a0b00400710601e80c07410720b0500390036010844045019002c1c094588107201a5566122240d540c0102014204103035186001d149441c02418590b02c0910b0000230300700e9031410300000c9144000380700a103a8840c1803804100194011400060402d13104100800100900300c0550341c00c2413509201207010700310b01b000902a04042220301d544149440e030001070b4290014000c204540b030a409962182c04600400e50480c081c109541d400304188240e5000020412030085502802c0c2050628024030304440c18080110f82d500058041007466032141c02440580fa010f070010303c4203d40030720848040b60002500c9000e10040301121200061002041c13031056000441c41d40c0c00c030407403090049468100f4120301c410500345a0f001ca04040e08003a18900c030100128445e080113001003545000c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 612432571 1250 612431321 612431333
    0x106050a23220f02211b0309031b030f0304060e070807090606080c07020d2907030b19030c150507020301111b070b0a12020c070f061d09040210090902040f0e0f070c 72
    0x107040806ca40040d100b00400081c6081c05140a250004001c0d030b1103454984900c255490183c40e000d5660744180700e4140580b80c4034048a43c400d41c8202b000ca4100d401c11121031074641030b5000307503285004000c1c000c40c4c60306840d03018004071102c503034480d242a11000700d80b0405106405000e90080d10500d403402c04200201c203038400210002243c42c03180d17848000c5030b00e00502d050355410002030b25002924400e140c02a10008040050310b68042d00519540c0c40d6000c2141510900c0803114202884074101070060b001e540f035858000c0e0080c041c54001a040503090761101c80034801c0280c4500703001080a80c0025024140e980c81d00202e4900440c070708041d40d8407502c461207109200e40070000744c1c60303090090041c50010300340070034445112070503d6000340507100c18454401ea00021000e225070281d40d0350341c82a40040c1c0540b000c0481406c0c601c01240c1c2c1e0503081c1c000d020384a00014001508103800c0e0f07220011100b03512150075030f6440b0040c0c0401844025100b50740090032861943d404162 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 612433821 1250 612432571 612432637
    0x100b0a080c040c020a20090601031a0108061c06062103050d020f0906070507051201021e07030c05150403030b0612190e070305010911030106050a23220f02 68
    0x90035004950ba412981d60300d006c5101050819000b080101c181c084c07120381040e454080e0098800d003402e03c115106042c003241c004840001c020704006400300465a16228019400180d20648038000702c1d200c1c031424004080d12540c0b040e00b9803002d0000710380d0814a0f103240c220f85180d91603038945252010030300800000e034000072520900c0780c10800282000b50360b164001d1808500c01e4024010b480e1510b400c01c19082c81e05681c0311140d0b40100101c2030460b1803012441e14612441011903118005030508503103071810140010802e1040142101240c00e40f0000188100d01c2690107111840002080c072815008848000024081000110380510440440c0740700b580124880007980b001403607236291421141e40d00a030b030242d56075044c94092042a404209030804142c0081c0015031510000c20001416446555a640110101c43c03100741a005219110b204009040c003409013000d104100c582c03060f001201c03030045d103441e1400103811564000d41c0c504206e07500c140152410030024550400e5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 612435071 1250 612433821 612433841
    0x1c0f020f010507240b0d0311070b090d0303050c0c0109050a05061f050f1f052d0909040302031e03011e0608160c1b030b0709050904150b0a0602100b0a080c04 69
    0xd4541c110176501e45c50760b0500f405010300a0343d825a01d0030210400d242410300c0d541040fa8040c0b410003096255446a0a190301680d41c903190000d442e40d03500c0b60325500c50092095510b81c950800c59400144003000039080b444030f0003001a176040d03803644264018280b045600148440d90070560400a603e400301d00000d4001024028840020950000c11401060002000040f9002169030600c100365051a100d1458505041d40030030072201402c84c5060040012036840b6007000d40004041503c00e10541e07240c490b03403070300940c0340450502c0580c2454009008801044400710101c00c50b05140300c54400403690540c48051003615a811000c1020b00d5804801040c001102d5a100003e0071022080b82401401d100b00b00034103085140c059804000070744140c2c20050003480a21156403008005500700b9444501c030b0940c0c200a0b000328014091164103140d2000e2405400940315401103904000f001710300f5810400c0700160f40030008002014000e0b001c1a91104c0300902c51410b00340e00445140d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 612436321 1250 612435071 612435143
    0x2061b0a290f130203070f0801180506061009090f0b0f0f100e0d14010e15010f091d030703030e07050102300906030406060e0703180f021c0f020f010507 67
    0x621913004070340360151a40c01408102c403510800c200455080c4150218184501080c1202011a46411760349200c054003c910500c0800101c0c091240a054480020859a40c06120010914031548000e040c07162000b405170320140303d001c030300d8913081034101030a0342d000344a07418603070740400200e6004140411403038100103160000004150302c1d80e19101c2203003000001041000c1c1c80c10415041103401c03246140b180d50204010b22084d5078021501059070600e1708005000c20509000b11745241e03c00b01c030f40049020004885080c1980354001b03510980c3d000742141c0c6d055513107200481e900c0a0050714201150490407100b242d00813095a101c06c40c3c0e54180d10f070750031300944100090541d4019a021a80b55688040c00c0102c04c148000e2650312441500b410014518920030300300c038140c2030080040005009280c90300440d034490540000b04240040480712025491070701e0f10351455000700c203a1280040d50100c100da584140c0807602e4050b0b05c100b07030744802c4a61180001da8800000110030b00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 612437571 1250 612436321 612436351
    0x1b070f0602130e06100f09140102010f0c0f080609010605040e06030c030f0a05011a0f0f0d080a050d06081209010c050a0215030403120606140702061b0a290f 69
    0x2c41042c2071a510050405081910000c1c02c2980030490a1440644a2014425882c8112120541228072801201e0b9286020b480c00c043c1000102e00424013071117810070907841d2a15110071103078460300818501c003042c3c98603041612048100b1501c01170074400c20700010ba042005009001003160305940040014044802a420a400013400c012101d40d9800d00359000c5a0f2440500009000300e010350304200316443c813010801e074041081c0d1640c060100380203c400f2010703800036880d0f1615600d0205d412407492921502c1c04100201260b1140d90401d10141c10041e0200d09024003082002840300b00d01030141c038103040c0b6001982da4800b0074809542e01d0150300c01e42c1c0050b840f02c0d00c914010b03e4958001998a1a007407402401c1a500060180ca1041c43e00300107118068000407d03620120b41c06014584805d02840010b030036100d00e0113103071503c00f503510505c5403003080081c007440c220384284441c080c1c0c42808044040744102c1003410071003010310340c004941040c82041e045900400c1001030403078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 612438821 1250 612437571 612437587
    0x2011401060e06040b280507020f010503280c11031c05190615081503101a0307030f05150f190b100e030705032d071d040303051b070f0602 61
    0x801d422060b41645546e59642d04d18081451034566038000c4451410403506166054000c51103c0d20028034540c188040000030030401100d00c1c4002070686040d110070044483c92002000141502810420128080c0744030002440d4012056580307204030300030421244521400300030054480600f240005800d0300d44c10302c1e40b24119000d210041c00d1944180064640070080050124000500e1051302d158022070a101c11395002c03498581a010019010840c0c9000032007415405e8030050420b85c0c9441001000004c006104c004440824000c0c000e44da120707041180d804083d10301c11181c844400440c9400034520b10b61202a50340c646010040c0090448808004600d00c440e00c484502c0110f90350700394800c042c0c9820003c0c140503080a50180c5a05014400b27001c1909407418401c41084054407498544800c042240740001d120b5400142c110300340c0c2800c43c40c0e00881c107840030380000e801d0000081a042c0009040040710025104091500d81680c644a060484d1100101c910a07001c2284403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 612440071 1250 612438821 612438839
    0x60f0a0902060307051e0403032316300507031413090504020f04020c2d07270c0f030c031103390426010f02091002011401060e0604 58
    0x14130891150f15460354032080604264a00200d0b00803003024981e0800003800001d5104401c80344e600326131980b0007207a41103d00d04400c14003034010749514180140210009000c1c01142030b04cc03d0640300b90b800c0c0e04803204422701103a803502200c4803000c20020455440020301c0317000e1035044204030355081070501100748507101004900368401e0303815503102d10a1200f50f02d040c2604220300041100d046203807041e413076030450700c903d56812040d0171400c0c5a50141240c2e9400250501f00383c1801c01661046620b8000d0b00328010500b0a101d2404603100c0c0e1030816101c040d1003844a400c03a80e49a01070740084852003103003c0c01074028081c0c00c15480360041040c1c02d240360051401072a000140c100e2020090680c5140000da03201d181302401200c00f601c0c442d211040d0125015117a1000107040482da500d52411088415400f00d02c1c010340c6040030f60402c10101e540a0441450100c03110844120301c1e0800301e09841d070000c250014002e0fa280100401402050380792141e40c0c020b00b00350308041e038880c580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 612441321 1250 612440071 612440077
    0x30702070e01060c140609100218060408031209070e0402060f0d050a0b190e0109021303080c0c04050c030907090507090f0e0a060b030405030906030a090f1b0512060f0a090206 77
    0xc1c00890200512682040700c817a4580c155012203000820304d502c1c004511990341c41d91034418a41040d40010b00300c080d5260b400e020045a00041e0000f565075985140f915581d520100b02442d081d101840420210300c004200e4808845403500341c030085486580802c07801344d0100600c160034078000c004440c240d018500840d4890088550000b038829503100a00111a0758452185014410b458050241d5540003503070300e05445102030016180c40580c0c428041400322504041c2c43e003800424010b2800c1c80c00959120b0303180c0241c50a2045450350b201d0b0500030300060b10642c42981201e9428800f00d01c030390303110645c454118601010029902c0018010345401500902c120507945010000d1000e100c0c0a110010318110220a29500e400d4440326101e000340050913108480005c0840c6502419030481e80b445600070700a24020f412500d802103880d40c1c0a81c00c00340c1c0303054403100000c0504e07001d0303c02d00b601d030280c40181c60315139102c09150219031802048061601c2e41c4000d01d4001d078580c0e0003d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 612442571 1250 612441321 612441329
    0x105030a05030a08061309050d090807082805061302041b051903060b0a0302040e0f0603030d02090303090604080309040e0d0c02010311210a0f1a010804020109090e0a02190f0605030702070e01 84
    0x5410540f0b8410001440303cae00581003440188e00c555400c1102d22400200322681003a00d440701c50f06601c1e2701c42c05140c9680315201c054060b100b88802d1050041703884591020051007120100000c299800040a104161801800c0810010b1000010031507804542c0b1070740700207510b000100e60380c03207580b2500d86070440d079074640020b9400301e0700740003094a401d01d246c0c00c403a0301011002c60b440c2440000c2d6030391040c44a81c0e14000e40105118101e83c90070001d89849010080c070040d03d0b580c5550a103540c0750000041c142c89242040c09803809007902060341090f01c403443d81d81e80c10504081c0c005402400030380c181140c01141c100281d160300c15000001040210002c1c40800c9182402144803007640c9030250741520301840c0ca100c0c443e0300d01c140c84119040d03100a003015600c95644d800140c1c0d02006c00e501c02c3c1191030030480d03601c10700c1102051a52000b48211120078500c9a80b5100c0b02003540c15019200245065444c28842c1c0b9000e103001d503511071824812264119110701e40d201c20303124280d02c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 612443821 1250 612442571 612442573
    0x30519060f0501030206040317040f12031707080105240f03040302070f06050a030f180b0105010318020303030c1c0f152c090c03060c070b0105030a05030a0806130905 73
    0x41104002a5028450102501c51000e0201e541036400003011031045210007400d02d00c02030840544030742040c00b61001000000c40307501e0441c0d40d990400029241d00a400ca000516150401d03008031100c2d07400900038401643c510072141e00b440d080c4040601101c210700e1000384c43d2042c051800c82c0e658000c10b441215992903d480307042500c0c0183c034000c1103400900c0c7c403007071040060040d5070b440740548100e201145004214003600d4070020006020f0003034510070401d0150820030601800700d1103641241c500b030b0b8003040004840384000e451222a075100a5244e0010000706d1614a04040a0000e034568521280050100740c0d401808941c1c2100c210303035001d51030b0302c0350255800350440da1200518030319000d10a401c1c1030400039101c0c86a0071154400001559004c24000c000c10811148240c0d4090b089444a0a2510005a0503000250700b203901001590010501c0c0c140418035a40440d1f0041c01141000308540d425942e10360000d02c120340225119140d00d20100b4180505030a5902a0f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 612445071 1250 612443821 612443863
    0x501020706150b161b150c05101509150e0f01030302010605060c0a0209071803110f01020c0915040f0f0f050609070f20060f100608041211070305 64
    0x40d0400390020320035403100110fa0420300c9183c1c41c1c445001030f5002941d80c811054140810240c8020300321041c69044006001d02c2544091a045c0e000801115118003c404880014240d51501c0342501e51a4000c120900c41d00d08003044801c40641105614030003080c102001340b515003101e102210320444042e1110340b010001082419021700c40c034006040c0c190368603072404840800c06076845805500083c060000791000400d001e00c103080500145085103882403956949041039a0070803101c0c081c951156034001021003203507000151031501442c02602d034041543d200c640c02400c0c400d4007030803070b0b0b0031175110360a00d81d0b41130386071240041c3d00d03903901d400292504055040c4002c039440144038a01a140c0002842401038100d40401c41c800356500c0e00e184003498082c0c0201c148400d100c03503a0b1051081d8030034420718003031942101d8452400d000500d180780f651030704201e072403d038151005401d070711468004101e035030700c184400c4000c00c1900044490352aaa9600c841c5413030043c0c3e0a13074840060700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 612446321 1250 612445071 612445091
    0xa0e16030c0b0909061201060312032c0d0f0201060302060a0f0206070e0906040b04090812010510051305010804050f06010308030105120321090a0b1006170709061107030501020706 79
    0x50050784040c0a0ba20310b00303803c242c030394000314485000c040c05962150414071852500039901350090005181d00001c80b000a04500e000900074008502d64640400c050043c0c1014200000720700c2c500350a0004000c14003445801c000b5504103c00d02c4000c021952030703090210140c4c40d040000d0404404e943e50f21010000451002400c140c00501940e081120031040440160f40d80100ca139040b00c400c45001500c17001c400d0011b001002c4007c0001e2030354034081160f10540140c8d554450407183e083c0c581580481c0c000300101e415201c3d0260040315510360340e90600041d4428240d040e80076115104551a0295000950307242c203500340c1c4100d4170344100200501103810840c5001010000312002941041180e440782110510480744120800003100002a0b0843d81040340e60001600002442d0543c104101d2030303401e0b43c3d0030f0b0180e00045914a80b0041102008a410910a4259a458131515401c18804880321284034515141c0b6205642c40440411028401841d01038414032002410240c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 612447571 1250 612446321 612446333
    0x120c12120f07030209030705091009060b0306040509060c07061a030a140709060803040e070306030b01030311060606160308040201140c0319090501080411060f160311010c05070b0a0e1603 82
    0x41c03090b000c0600600000c1110349002800c1001d941080366030f000c06030750710405440c0f41c0c40f440d807040e41031505103000000e00301c0048008600071081942c05001960b159a0082e9440c0c5c0e05540075131152804002c4030000c120954080382d44002c05004004d4041c1900d40001e1032703c0d0328150262004841c01c400300e4003522081010304002c008488052040515000350680c0f603000340d11440340034030641400260791a10035400301d0065644a000b075082c558403410300616140c400194540e071403003003c004c1075291400205882100104454a4070910380c0c0350703821246c800c0043d01c101c0c14000400420051b100302800940303507090000000711b84030301c48030308011292024150280c0074080282020300c001e0b60b0000b80b182d07110390011551030030144414003084907442881d4525000340070100b40021032000e00b44090303880a02070341d2200414101803103d41c4c22a82002422008100704000c0d03203000807008a00158001c2032641c00064641410507004c0c103189100764001c26000e4480014410403107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 612448821 1250 612447571 612447601
    0x709030b161e0815100c0816080c0a1205041a0702012c1f09051e0d121805031f0603051507110106051e06070204090303060807050d05120c1212 63
    0x24084680c59800e030300e030b030b2405481b41c41c0c8403501918580000924181901d800c05055052aa01c00316a81e5103540707103000305440e148822411107480080f0600444454403403800d07107050ba50901103249010003560713140c020303d44c4044400c80c140407803040c0c950340703445040680608000c0480d41c2c004c5020511000c20039417121107030b22421102d19842d429202150f0111a040075a00103a450307052080b03116898241000306204850b5000300c0421030b09082055100368100a07021035102c924080c50000004a500005405481c0d015071003d02d903801c03040d10461814001b0000c07a43c00040080d1a500e8160800da4402003519022079040b003844003c07980205120b00d0003001c54000c214040c03c0c40300007429000030405030403c0c58005d0302000119038030542207404480e8010410081840c0629000d806030189115010060107060000549410082c88843da01075024000d810541c1b01680b49840301c0d080601030b01001d110b81802030501c8084100200304030840640c0446d41441d1201810851f90 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 612450071 1250 612448821 612448861
    0x90304080f03030c0a08040c0b181e13020a0302160609030e10020a0f020a0819140d05040e1e071106220201030509100204030c030b0709030b161e08 65
    0x2e40100200403100d1034080580d041c400300c0e840c11a035652a00d0030b000e00d601c08a43c00821110000064000c5140400c040405182c1c0e41510440d801c0d03010100481e581900c9450440c1d08496494214244050241e0050039136920781c3c1801130408040000c81c2c01d00581000c0708982403a59409104c003450b804c002e0381d81800204680011513110124070094581da01004005d150a01c1e04000c50b046540d181c0443e80500501e030200c608004041480d0002d20701c140310140d49040400070308401c0300b03c0101d141000f680c01c1c0e40f949e80c507051401e8100c00c3d4000d001807089030b400c240c200001d0051000f0030013403802a02e441c0c1c2c0b40040c207904034103010709000c40030701034100c8540711500000e00d00040c28404d407141902400d001038581c1c0c4000c615420044915901d40165100050100400c444503203540c0070f0364050001f1400aa4584030145c801c0240e600001c0d226010140006040c48140040d40c10810760a00d49110110403601002440c00c5400c121100820220410006640040c42000844c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 612451321 1250 612450071 612450073
    0x506040512090a14030a150c08100f140a0815100e060108130c032102070b0c031b010608030a122306010f0c14010606080106090f060c03020a0b090304080f 68
    0x25485400241c0380c6825100e1440e6406981c04c3c0102169814050318441940002d00742503044102c0700018010900701000b0f0020402c8480030900f018541181c6000380c984602071022030f2401e100b00c0340e80c081c21880e0465440804403602051a40062025143c02ca51a80801d812410300a242d80381e9510350390080f0020002c85000c010301a80d102032210b40007944541007103200c01ca1400c00300a80700c00e0f43c00103011301d580b0081003601d60501040303682290040381c0c2620f030b003e912040d2401c2a88100081d0196950080c04202caa2801c2c82a00d07803001d00b0040d00015800c0c0e0740e281010305680202c42e06101051001144568000740c6006441e40350828640310050010403940000203148050031140c10808074002c001341d024064200ea10380e064001c0c9207507501c0c09044440d940a84043c0c09003000141100000240c0c0314004c1c48001e041d52050041419441d0520f102100c050124031029002c520551984d0b001142461034101d0192010001443d503036401c040784d043c03034010250054855 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 612452571 1250 612451321 612451327
    0x706230d0e19030c060f0e0f0309010e09010e012d15030e010216080f0702180603010e0703050a030513050913111c110402041e150c08120613090506040512 68
    0x20307400f104ca800070350b030f2111000802c0f00b0003a0950000303003119440600680300b030f0450f54081444c004043e0800c1c00f03090365403420b400079000a12071001828894508254404401031203c86845080d99130101c1c144008803003000c3c07001c0c41d49100d110069101c2050050900070a403800c40e0301d801200c4111803908001d51500a801a4440002d400d10001500388100410345400600a5904980c41c4a0b001400391030340c00d0303030008400ca4150341550702602c250700e40190300304040c0021510b01e040b00d0300074000d0980c012040e01c5c241d9070380d8002c12107040000d00340d841c086081e98400e180c5900504e000c000442e408401441c0840da043c0798010214840c91360a900008240c440c15208481507078040e00500300c040c5c1c110046400f034055030b0815401d1890384540c032030f09500505600007c407010909503807a0824080000e48610803030043c040c0121004201440000c40c4054525400100240c42c0d01003413180b110318001181c9a401040350b50b90024010b00040c01410040c4038104048040003a03e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 612453821 1250 612452571 612452573
    0x2b080103050607030f060f06120506031207031d040905100c0905030a02011407080301030f0b07080105010503221202010f1109031c030b0409060902040e0f0706230d0e19 74
    0x582c80c50014001000c0584440106920162a13003220b8000c1000c0d00400a0060b2500e0020344050200c00180c5081444c0900080d614600082d950349000c1c44078480d40e1600c503050300d04a5a5548001700700ca660201c80140c00ca4544451043c036217030344e010f04040d04081d14841200e00643d0121400704040002c0350600384207940d80070883d401c1036a42400c0500400d00001c0510404c0d014104018201c0c1070007000020601000d00c001e5564540b01e1101c607035003607070b8031182901c905100380180f5001403010700000304020b904040b01d6145070601e8041e4a01c0030425a600042310040252410050f51141d50b05441c01c41d00d03004080320120038540240c01c041d03200001c2650b400304402d242101c00c7c400c41d80082641d00a5101d1003100801500c18041c82e8020f04218000d044008001ca0141d0b203000d005545682d0702041e28504069100d0241a400d40b400f039041324102c107840e80701c0b410420b040d03040780d4000c1d03e03010081c00004a001c80111781104da03182c0705420300103010b002c5a11541010b500c20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 612455071 1250 612453821 612453823
    0x9060a090b0c09010306090f02030615070305030f0a02070506040302242e080a050a0209011e05130b0d0c03171c0518030a0e0a0501171602010e2b08010305 68
    0xc1d07480302c08518000c2e141c20820004901910540e813140a80368605129850b820310305070001c0d4410201a208032524200e14917079039649201b1302c84040c0c0052018008103030000e541c01110390300101800d101609007042503d0381410308400b0380e011005640b140c4c42e580e180207208014440c4461603048044283c1c41d01020b903851201180d0000c118006d070141c110000b1600304a40300019100d12021074506040320b148c181d581d075801203403d0b0310407000c0e070700000b503204824a88034114210314a54580c60600e03020510120001515404038419101c040300341b09625005405515580218800c3c10102d2075824510001c1c1401c100103845a81c081010300210460360303980701804250003000003126601d614150403584c0030010010000d010000d8082030341540300c400900091030851b00c508840d43d580f8019a000c100d06210b1b0b149000c0401c00094415880d680101461b00030350002180e06070022040604010310180903550740d0b80100070b80f035101030203204400721050f610b0400078550750550b04e0b02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 612456321 1250 612455071 612455093
    0x13050102030f180d091403190804051e010c025103011a03040320030d0b030d020a0201030b030721030e0103020307080a05040c15020c1903030816091d09060a09 70
    0x45000e4001070781b040d8586040080400d440e080344401c02d5494000e182403400c0d94860300c221885020b191000d541c05060450407234200742c0c2c0584070700169144690a1020f0040c402c0c00c601d081440c28545400810700c50b0a4040103c41c14031016484070005000070001328400d2003020200101c00c0c0b00521251100301525800f103503085c600c103610796686217001c9484a907408040d10390228144c00302070340c403000000a0480c90804c010300b40300e580e20a0341407650340c07a51036072607a005070b01a0a051002d54003961200c803080d80007130309031070101c2e0301d590b2200d000e14400440c462050f0503010020b014180e0000c8404074208091905510318204400300a048000c040c00040b0300d50384c0c5002040400640e180020024a811101d800c1c00c00c82a85c400f948412003085024018819a03c0c0c841c1221414000303641a42d905807140c0c0d199440c0c1e003151144141c10000d070310082c04111000424450415000d01045031100407143c5524900f03a03080320308001e00503003040c2a607420001808001500c824030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 612457571 1250 612456321 612456329
    0x3040f121e0c080109080712110304090e010b0405070207030510020a090302041d010504030206090c0901080d0305060a090e03041d06030d030b0103111206010207120b07050313050102030f180d09 85
    0x9500c0705074100b4100558a4220355000e1a0550b20341170310201004040c501905815010b08a80308117500004010b44519054209556054108101c244650361031503002e041205007a10000841d54240702c00702e0200c45040d101d10001d60b02c141c0080040120030024181425409174080d8145100d900c00586001e1580c04001e200d10344075804900140c405004884c20310309804028001820681000394036021b050b90368000c82d0040890402d1541480140310341223070441d50090004403c504002c03002841e002c0d00c80b65001d0246030b40040c42e0006801141d10401c920b0001d07503a03c80c504546400c1c096110030343d0070b454101550070090a80d40104441030a14440d05012070440c0100700101c0080140b4501a114188040b486811800a5505040c4110300c04e07000c98072040d4a5a0b4140b0154180c03160007401d400c43c01c5d001481080c0710700003940c2c11000408101101401c15612642a604122410748151390400c007000001100d0310403c8500c4030350034000d84018540d2003c028500441c6001d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 612458821 1250 612457571 612457613
    0x31e0415051b0313050306070f02060c1b03210a0b060712020c0a090212070305130f170c01020a0e0111030409200a0c060c020d081305100e03040f12 65
    0x303414004285596001c5180791800040d83d95801502154a044c50041e000d840d003e40318000015080c1400780034401c1c4049800d400621082d95140c0b0652000c0c2d012180042c4100280c009240d20010104050011080c605210b40c1c841039440e421820600f6000304501e040740c2c200b0f0745803101502d40300c0803140360742d0b0400c880c160042a81e68050b07150002030546070350000300201c27001515811650182c24140841d140c00d40c40c3e61034400c02141941c1d0180c030040d84c0e45983d009210006952454045015403040315201001200b00381c1da01001d411103125126203075000100d41c0752440d840403000c507240b082401c00010007003099800980d84d0046001d50700d0010b5840755100c00000c80341146801d14100300941640d03d080d400f2004000c980c4148003100c03100d04000702c4a1038a800400c4510404030140c0c0c4401d080d40d00c058880881806140d01900c560242500021030342480303004200650f48008015070b03407a031130302025420800580e803212031001e100015150000d20041c2e0075400e01d0544c0c030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 612460071 1250 612458821 612458827
    0xd090608070215150a0f030206040b0715020706240e01060f02030904090807051b060319020d09030306050109091a0103020901020327010305060f0f0105030a020912031e041505 77
    0x72200340e10b0704009001d505910041c4204105001403c000c0c1511145025901c04501980d610b60140d03a008507800300a60040f004d02040c040c0c6051400034002d2580103143d40c0340c01c5e485840c008030480e80080c00580c3d01a40782d100168034500e29807414200c80c00701d00034a409641c030309401061403403018003440c41000744034030214500078404c0003501d020050041080041000e10302d04889154800c02c8212184d001c4c2003a0910410008100c00c1c1074104042c01300c0d891982d6000c00c681d100124584410034a81e82441503040103801c03031041d101841d100c0d84000a507181081c0c009480c07141c00358404d01e06e960811403512428031040c040410b010b2002c1c2070260b2101a2880140d080d4010f0544102440c40811000c411001c0d90b030400e03515480007038a0170031040e1601d0052149a02c4500d03610703900040d141c4d0303842002d544103600440d07000070348105c010700b070100050004103000d00c20b85511070141e0001c41d554543c00c05450031103403100b92245031640b825207420032050080c0c103141c4d001000d000e004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 612461321 1250 612460071 612460081
    0x20a12110703051516050a1d210a0308060d030507110609030d030f0f1803080411030d0305040b0a05040f0305090d0c180e161e2402060601020d090608 66
    0x104040c9002d140e22800f658a84510000120f5002c901101c2c20300500854604900419000350220b94803044981c0d9210990410b40d00c503100341002e0201c0240d0040940c1070480a042c0b0984c2401d194041e00e11b0162981888a080003800140090443d511516800c101807000940200880d02d40c0355102c851581c8480304100002c41d6402480820b94140c0078000100d8a1146d0651201d00e8254060000b00603c0a400e50102c0c102c03500e5140b003060801c08400030394080b90040c030200764440d1241c403150a613001d100c030111f802c14450b00038460200c1e8452007800304100e07402d0002580401c1c0c00380104030920b815102c026107180720000c00b4090050000e080803403500c03034440d00e180154008a05815060b60b400d004150f500d10728041d140c1030740c60100c510300d40040108248850064030800c041030701c3c0c2420148440e45d09007501d24400640c20b902d000400c41c440e040c09100000141c0c000d0b400c3c80b451820041e0401400500140c11034014684a6a00980210f400000e41c0c0507840e00e080e003603941c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 612462571 1250 612461321 612461323
    0x50c1002010501121401060b16030f14180d06020a2105040b0705070503090d0c0e0703110a031d060a05060a0e0f15030a140c012606060a1403010b07020a0501020a1211 73
    0x1039000304010309000a0400300c082c00207112707001041e109941d000e1010f201c015080710b0301c0884100d0342c88080300400c000140301010510801c000e4a0003491440c0107216503a4140880c0c1c00a490040807800c8000400e51250004020003101040000144028900781d6208004190010043e07810300c1004602c00c0248003040083d96540e0102a1450a001040c0e05004800710701c18468252161554400503030201e20034040c1c03001444141a01604000010405502078a02c079a006402c0c00303690302070201c1c4071200300800b900440304c24400081c00d040140c00d120703500d18540c02903060980c0c80d20900002d14a0706280b00d40c480d1400c00304c0b28105e00340800203802c1107940c0e00b000c0c18810b20354103a41450342011031b20004641098a480340302112000881652007044841c48520304c80301c0001540a0903c0d034014000200249084450075071b420099244071307042a00003031030500e00414000210308000f03500c072020302800d0000301941540c5958000080b80403240500030003046074000f84180308 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 612463821 1250 612462571 612462581
    0xc111f060b0c0d0513030f050604020a120b0601110c03030301030b090c03031e070303060806070806120f120307020a0c080703030e060910030b0a080708030304060510060507060e0c0409050c1002010501121401 91
    0x68441e04c0400c007d416402c002d036032041c065030240c0c0315012100000450040e109211031699503c2084811507640b500f0040d0b4010b041d40300042400c0c01007586180c250f5806000030340c047c520596140502d4200100c182d403428043e00007a9009034030403c403800f60b000282140c800420700302000c05a8a100b0391904401404943e44006010f20405060141058100380e0142c806c0a00759103002c0c0141c00e90a16654540020385405126001050a00c0e0f0300303e0300100850344801103004a841c0c411b4590740e11001c010050380a4001600118801c1c010998086805603070f040701164201d00b010702c00740014250352002201041450358038440306107030b61161903800004220072000d949170701e641c841c000b9071658400c8a040b61014a841d001485070420603c1d59000d8030344980e036150615401e82d503400e005041c8031194024078400c4415116059840f809011601c1d44100050400c94179002c080c0180c104200c4014819a4104001800110101407014130407030303089000b109400c840c001180c0c1c0141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 612465071 1250 612463821 612463823
    0x60f0a020f0c0f0c0105041a18030a0c1404051e060414090c01080a0204061428120c08060f040f020f0708040e070903150c111f060b0c0d051303 63
    0x207200840c00402c1e240e404111001a003400358162012030720721100448082c80740740590a800501c51903154502035112018000c81401010304800811030200002d00d400c40310b2608803008107072a501031150f81100005030f548003500751020720190030a283ca0310000609404c10440400c07040000403940d50b140d4008486501009901c030259042c041902c0c0d0300c0b1807004080c0c9022942c51004500c0c1c61078548212401c9440559500c0320601c01000307108450b510012282a02401480c0b02103114103250050200001407620388ac3e130000c08100c0400d00f07680035000d0b210240083c2100b040215110144032050f135403022140010001050224072000380521048070700200310205548080210020007407042d9060f0040c8075079107035940401220140074500004142d040a00110003808140703400c600302c20086400c0060fa80a90010309a2800b07420728409102c820210200306440c041c580702d071101a000001d211440c1120f0038a401c0d9681d000413603000100b1030300090141418003030b402c442001d5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 612466321 1250 612465071 612465097
    0x50711010c0212010605041a090105062107050d27120c320f03180a03060c080f060a030506011203021c1e0503011419270b0607020102060f0a02 63
    0x8000c105800c07034001c1c16140105030240303141030f01d0301c0c1c5c1c0300880d02c4c141403841c0c2d40140727000496800c0c8401d000306604900480713000c682c813503001c03101007501e581d903a0b51151003113994042c0c9581c0d2143c1d0020540b00d03240d498071a2274441940c15852041c69a001d90025900203455805007145000c04603030401c03030588007800c04145400100304105115040c00c031b41e6001c1111b400586042080143c1c3c0b20780383c004840c0c50f140d02c200051004281d05408070758079801c2c0180007140e4560b403030712107030b080d61070ba07204c0d400000d58204100315811624004258008405a40b10480c0c141143c3d80c2d01e948101c1030180c2c265178405010345000301842041000c51400c030b05c00c4e072400d4455a1190180c88201c60b0440c001c60f044e00c0c080007040c114418010780c1d0490318140520b5012502075001c0c0b003020008032028240700301201d580410020030a0038449444c000000d0081802d04200040c6c504403400c2c801c0300341c070884040080d100940e03030014086801030941100004240c94500c5801c00a2154052940d08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 612467571 1250 612466321 612466339
    0x621030705150603030a080f061c03390807081e0c0f010c0e0d02120613020f030a03141b190506090d0f1b0c12050f0d050711010c02 58
    0x3040004105216070507080c00d80d602d5203403211001c041d1030340100010200099140c0c00061840c14000c11004d400c0600601000032115a15044080d94005940251701090000306c0e90100c0d2041c641882541c0580238105101581d075800c801c031b000200001d0040e065502c04250501400070401c221021000c903100c44620f02c4010801a10180e004090b6084a0303004541303120301c0368038047c00f1f1050600c8181d55010180c01d01d0004100080740654001e03a04071342201c0740505800300400038103010b140301c241c1da1094403040d0300c104002c41c40003c46090007500000e07003040000341c000340100e060040f101d62854031a441002450600b402e006610f85d110b04c90704040d0010002c0071402001540e02802c156030180d0f130398403070741d65603250300b032280308001510204c178000a03600c5000d2003034000144120304811003089413105490414103402c411003070110304411800700141004240800d1084002601240c9485803018016026044000e4181d6844900c403000c0ca07131089034940034a42d402464120 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 612468821 1250 612467571 612467573
    0x12020301030308190b0d0f030c12081005060f040620030403030503150f0904060c020309060c01140702160302150c0d0f0813081e04030f0f0201030b040b060306210307 73
    0x120800c1d00b0313904001101c038611900d070140f9043d8020840c0200000c1c0815242c090f15507540c00000c010314400381c1c1005206000c40f0001040e4910040e4103c100e40c1c0d0b01d05d102d0420405541100c001a403000703115080400c0b4803e19404c030f000030b031006c40301541410403080551220345c46001501d42c01d4607032180000500442010f400c40c010b13500a100e001da01c0c214040610045c41851982e0349050360b400601c140c0017400095940d0480c0b00d8440c01c0c0d2064a09000303400c0086210354003c04410388160751036200e845600e80f80f055486030f001079036100800002948000414404156001c0a070280302d4110480e14207a440008a40d14988040101c2e06040d141c02c41c0140f040341424042d0000881c4000492241c02450f081c251003103070010017041c6080c180b049480501d1041a440324130140c810700002010900055000504c03500a6491100e0a100d9200040448140c40b080911030b510f0700c51034500315203aa405503a40300da41038450019049103410300f40e035403019210340125540320018000c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 612470071 1250 612468821 612468827
    0xc0111011e020f07080c03030a060e04052505040c09090c0201060b030c070c0b030103084503070803040806040b07021c030507020c040608100b0409030804021c06142a0f0a120203010303 81
    0x1621070a08409c0401805032949084010003405403000340903684212107000014103c2c000024280040c1100404001c0da00c101050503140b409640d0f8000c00c038a1042041801d2a600072000b11f10010310003080002d08000c5202011f00028000c480b101c0000300e0f41c0700400c0348034071845001c0c286207401a0384030f60f5071b4540007031150300c840101a440e002d80681002580c0180c60703108518070440100b10a0035082080d292920b0362140d4070183d01d131090340000900c50710280300404c050300180c0c1c0949410b1419003070100044001508480455002c030000103425000090084188207103898041026150000224a00a400305d0000d500a00c4c0580004545000082c07001207405078140501a075080202048215000640c0141c00b191103c00020300610b085808949804101c1c1c0720304411001070f44411080761005103000020000c0d80781848542c4489a0703124801d51544030840c801007940785100b085a0180d801510708821022039130140241c080c05600c1c0320080b0741d0a0440d00c03580e42c2d027002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 612471321 1250 612470071 612470077
    0xb1323010e011a1c020603010312080711030409020304051501150e010212030f04031e03050f090609101508030d02070201030b01110703030f030e0d020c0111011e020f07080c03 77
    0x40150341c039016400440310010300072901c021030080d82084040c0706250030700161404980602130150703464482d03007005a41e24005140614002d000c80c40d00c5c0f000c0f41101421048001e00004e080c0040c0074003010308114008112029601e0605000d6100d0702c9601d032a1349443c500012527400c50140c03000110780403181802e0144031207915035503a02d0101c1c03100016a10381412204030564418100f001a036845207810032560802c0c401c0c540322040040f0303400d100c08a0014454440c0c00280c4071002d2080820081c1d240c1500282000094074082c2008054196282009140f0701103982c4c4466250760303540600c2c945403000740b510b1000d80e42d503810307080c1c000402503000405c102d000c41e181c144401c0b01c6512176140322003040d40290081c881d2904548090700c5405000800404060316049444e500160501084071600c2060f002040000007003030000d402803002100b4040981e141481140c1d07a44542140c1c8041c9010000c80140d50b4003006a840b581c3c0d00c60020050300318000000c115990607170000003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 612472571 1250 612471321 612471383
    0x606010201050a020412081308061e0c04080a060b0f0d21020105101206020d021c05070509280b040b030106030605030102040b092101060f06030b04050601020a0b13 72
    0xb04002c0d66a030641c10101c0c000d030b018102012003149a194001505840101441c03000340750413003141036a40001e1454a40200c2c0c0341404984190000801d2184901c034142d044000c0301c3c031444c1020304004c140c07a6a00721408025240d5900c40b0219101c50302d649505a100540c080c0401e1607004942c2428852514540c0e04c2e04424440c0e403034501c5140c0c1c4184200f80c080d814140380300035005d250100141442d030403017200369043e580c02c00800d50035802c40e00c010b01a030b200f0b0024001c842a06100c159040301c1c002407440040c0b03c410003d044c85a694411001c50703000410103d4840e250380704403030702d62580340340e000190b05d00c0c800100401c0740128080590f04a030001d41c1d00b800102d0320b920502d400e074000e9102e258001201031040181d01d1402007074021030100146081d2002c5088906a83d0a680140e401039164100819092054540c98010f6450030b8078240c50602c074034103114000030340d00d0741034030b01c09481441300101243c040c078080180020b0041d045040c00741c40013280000401108901c000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 612473821 1250 612472571 612472573
    0x6091b09020a121107120207090903030912090609170a05010504060b030607050415051c06180b060702090f180703060c0f020d0f0302220f050f06030108070302040b0f090906060102 79
    0x91403c0185055003d001152080050502d04048080c1c0e2403007201c400b052540c0c010340c080c4c540b01042d510060b03c03030b00c190a8020f64012803241610304040154440382c45c00f40080000ca540c0a1103c20340203000d4108855091900150b486107240000e81801c044002c010055401d103401c1c803041c4021504145031071601141500c246440d00c070303004d6030107220f14800c410f07561a40c0f13401c100c42c1a01a401910008280c0d4480040703030b03446040f103070044424681100e00c0c408000c940c00c000f40c1c55284500482660280d900502e007002d42d03000a5102e40006100c5415000d83e480001c19294014441d0f0091400c8031048980c580c0d207a29103a40940912047c1708001951000d010031514800590040310340c0041e01c0b045800500050214040d40c4941082c2c40c50300091380c00100240c030900401c0c0010704d0750f0a10380c0c491a00b08000c10001c5c0721401419442500e0910040c09682c80100d401812a41d04580000b402c0803c0800300e5071590201118940c400c9003182000b03c0c07108085a490b1050700300764 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 612475071 1250 612473821 612473837
    0xf04050d05071212061d070f090b09040e0a150207030807030507050d0506190305012f040905040f060612030f050313080705031207020d020d1b06091b09020a 69
    0x118111501c0c081d82c00d0207003099046182100145020b00d519240b0040b01c40f04c08100c5c0c0b0b440f40980000c00b800b690b13a03c019103054400f00003e0a611004640c030300511071510085017840c1413a02c01c90b80c050110924404c6550b42c20002d00d8450800007000300c1d030b6002d1100074110140e203c0a600941065800b40c01040c52140099041440307072140904c0f42415071902070070700e0b10401d880001860001c3c0100c1d0410300d4100e41020f5038500741d000c20000c1d480f40002050003801c408440d03440034400000e000c20642644007540344149074100341d60a441d41c0000014042c0c0c0c031418004088a208200600a0ba16082d000304440802120b5892030b98000e445604090300d851344129078521040384c1d2011a85d481c4070709200040c218000070b20605010310100c0b41800305641c003142a5902c151130b0a030140e0321104120038656014440410341d051182010828103040c582500e642d81c0323100000030101565001d200b400c2002d2249a580008141e0f00c1b220036081d1264281e9000790f1080c034070040807070004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 612476321 1250 612475071 612475093
    0x403110d02011202030a0e032d03060a03030809120f0d050601090b250c0e0105031e0606060705010e0d020d031a030c010302070c0911070204060b0a020a2402030f0405 73
    0x2000d000511168103079200b40c0c010718410803060003504040c2039004070075240c0c4c14990381c0074800c2020b09114103c40d403108903031b401c5071210701110403088032028980110500401800e60341d211000c40449401d41400005688c130341880e42d0a045c140248034040300c0c0040303102c0c154294800c01404480d0801c0c02c04214030303103d0000548800180c0d104842041d0320070420303c440d00000c601e80c3c1c0303455442c911038444072088551321505126074a8100149a0054200401540c9010040948442c064030200b030301e1358034140c25164641400a2035240207050009a01040042c03d44c41a2981c149610982c0c1c40b0f50880c1c80003d40714180c1003400d1000a051200003401e180c4840005843e21030014010003000701c3d02c80040d406500441c0f01604e0148580c1c41c0044c1106d81809500604070b0703d40b03034041d540e22451042104031041c3c1d4005402c01c5109101e160380e01500003810b40c2ca0903030058410300403001117003641c0e90301c0c549110482680d2400031092150056107040e60703d001c0d034811015030340d540f01e207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 612477571 1250 612476321 612476329
    0x905060303160201230f091c1a07210606140c030301090c0509100807031802010c14031e0d0c030c051b1c050a0f08061302030915010b040311 62
    0x904a544242c04440100c11401507002c0c00d52201c02c601111014031001c0e403611740100700307074001003544034820800040401c491710f0b11084080307200c50415900701c03412003a915010400c41581e00312440b00340050021a0046028491100004051620482c20500156686c130054901481030300d02040302c500800c00b400f41c1da072095480400c00d100c021411a0b01c0d120b561800750003411001018058200310348803060722065154019850705d038135a040b035410240301c01800c450f80c1c4014103c000c810030444c10300503a03115545041ca203400c440800e0000c08544882ca0451003103000c2c5002148c5102c50003e400d45014000d00f0945921280c100080c0600c644151f05603051031080e440001d00400010030440c222584050345c85000004440c2000c051174040c581141e184081400410301c0451030740c00c0c0a44c0305000c018803903d01e00d0701d101070303051640101d5140c0030702c40c1100981c26000310016001f00e0040141907058440d00003202900c1d41c1d50076010b100b65005000507110717074003002c21610003410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 612478821 1250 612477571 612477577
    0x190e040f1d0c240702040e0a1a13110f030d030c0e090c0a0c05031e041404060f0b300405150f0105150913020306030c090103020f04090302071508010905060303 70
    0x8000f400d581070703103103c06150340d50540781c05807008100305091048001584480c80307001c00056061008042e040311070b06004540012001032503052204e840c1c100104103180e14000b40d651540b11003591441142d000000b59013010f15003800f901403080c1024004d085905400c003520814464480c0750ba808900070900000c14011100003c010b80200610b82c2aa071290080420b054041c0d015681415602c0e4031043c44640744500c060b001590219040c440201c0c0582c4e1620005401c0710108013403807801f4612100d01065104600c41d8080c003041480495071031080310900c4004008031420003004400b044085a00181c40c1561588100c0003603d103010495403d244c06403441000948041c1c0c40c14007086005441e01101e01c8984009104950047d00c800340d0345041c4146800c000758036468502c0c2403526000403469036610849660b0010400350300c0703060321400c504000f602d002c201d0b030711281403d070314100d101d0b03100600c0768400a1030207640562098905060300c0b000741c002d10090322814100765981c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 612480071 1250 612478821 612478843
    0xa05010201180215041a040509060d0b010b0a0905030604080a140a0c0f150203180c010230070203060a050a0f06050102100e010b0d0c08010e0d05190e040f1d 69
    0x92400202c200545444020344001040786119185410303150400b82810115041c98000365480106040c4820b20781300300c0d010350090060301c903c030007001750f074980d40300145061203586030400b00010103810007403003034802601802c0050126080e07403c1601d0301c11039940c8503035036100c0003a40f5680c2c90010010302c481281e1447d5519510141c0d045003945910200e0440c074441110700406000d050305c0060824009188100710441c00740041c0c0c3c4c0c503085802d0500c001c01004030b0441d0008001d0364004c208034040b640b50344812018801307000080141e0300c8242c0c45820700c040c3d0f00d4840d407400c0190707041d20b541000344907800c444014030030071000d251004155881401541d000d60012174051b03a44440580c40f8401c10348180001107140400034012038143c0922040540d40c0c21401e04043c030405c1024015125080740300c00040c42496100344006090780100000d04290300013400c002c00b0350500c1072140c0620078038020010400040142403250040c101c9000308140c00c010340143c004502d2020540002034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 612481321 1250 612480071 612480101
    0x30507261801170f04031707020706050309240a151d0603010912111e0d180302040c030506030c01080403080606130e040f2f0f04020d090c050a05010201 67
    0xc81c2403070640801d65059500c0c50400c042040d0341d6802d00d40c0da1111600908000100f603025082c1820000c121419034507080030b070303400201c0a0151042e400120a0700b250b80519009840f5100c04207031504200c8014034180c41001c04821242c2500e10b00520103000348440e0000f040b80c060f00d03502101e0a40350b50700c40c84000d0301d0003806140041e0003e154079940048014000a540b9445590b405071944001d0706107000611000d0103281e06d05000c210f007030341310340110080b08102d034200942c207035403140c5240b2802e0402c80300c0b06802c001030b4408030440001c0c40e4001c0c01400310300e03009840107008200469000d0305c41c0c0300728001c01d1080d5001e030310b200e8019901566028103a640d10303024044243c1c4004402c0c0348a000c1000e00140c0d40380304400b600c2c02140f080b00f10200c2c902c0c49080800300a01050700c0d510241100403030f01104a285402c0c06200c0c8001503030503100c90551140020000d020f07404401c13403403a0509080c0001c11160312040320640b4001c031003654150341c0740c0004a0884110134101814 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 612482571 1250 612481321 612481327
    0x1e0d0c0303020702120105090c010f110606240a0804111002060708150303030c0d240618080102032701200f04031506030b06010c03020d120609060303050726 69
    0xc40d100c0e800400340780d8000b400c410007202d0b1603c01d0070308444085521094a40112500480c01d40c0d2082e1080e4080c40c0c5803078500103504150f21015102c00b40030b01401e100710000007419a8050451031000803031003500b050240c440d00105006080b61100319002c071681c055004120a640c40c000300c006011910325801000d46680d000385c1a225640d024103030152600d400403540d88542e83c00c00046110f10b1b690306031143c860407450114000e5078441c0720551145918040351080800940c55000c0882c3c040d40307803030450415070707003070b48000038544d90041c0503603500010420010000e82c0d60503842048103030085848140c2d41c041d06038204c515210010040c02f0340c90760000005040d5201900c0c0f0400d0081c2d403d03103000d17604da680c440038007038604521032515103808080050040e40c2400b503600150a0804540c500c140e542e000303440301118201e4005005100f24032550780e4681d50700035000351004030705c208525034903410f0150144e0003200e003c45505400c00c501903500110b003402c20729103000b40030351203003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 612483821 1250 612482571 612482573
    0x50c090a06150306080d030509160807031b0308030a0b01090905070e090c09010c03051b01091b09061208220b070507080c0114070303090c140f01020105071b03051303051e0d0c 77
    0x501030250903e0003038801c0200112b2a0030795025480d0043c4100c40051012503c0d52910514401d003060300c0c80c1c031100e1400400c001050302401241d40c01111007400045020012005985405190704103003010340ca00010480443c2c2c1011200507000d108840420b96580e50780071900380f522501c0382c2507000581e42c0b051540064005c0003c5c3c0460400d850301c03071004204112180d4210b41c81d04005440c0303c50301420351000c0c00301e08035440e000b43c8000c04040c0585420701d820720b0986114008020321804000941d600303d030700c081403581101c820016004006954130703084107225070410001902c160183c2c410000d0200400182d40e007003110f041c1c60342d000e100041c50100529821508c019010705803501c0d8101e001807900e6003030384082c00e0300c0d01c80c42c5c0c00c52400005121030b03440030310022419a851700b410b1000741c9400c401490001d16400072401808181854211000c0c0640d601041c0e030140c89050100400c0710104000c0d4510382d000c10555103004581c40e207241c0c0c07000041e011a003c01ca014500c48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 612485071 1250 612483821 612483827
    0x2011b0e10050d0c0503071103040506040e180a0501050601020c09060a0e071101020c010c030b04050f0406020c030f121e010e04060b06070f050f160807050904050c090a06150306080d 80
    0x3203140c5203003415800d00078800064420740781c8010130a00041c038000201301090360040c47c10024040c83e1401582082d0070180810540e1040780103003010f1071205800940d000102512a070340c10410a420b40d01009400d16281340642803d941490150003180208401f504105086a11601006101d405101e10741a0307002d0034420083c100340c00704185c0e6110305841c82005d0006002c0031040b0000011902814000182121a8889558845c2d03044c030007403110080c140704020ba0010b030000c00040e540d9031050541ea10b5441142c03c4111220408520000e0014013005a18483e400c00022002d0b1502111300348010702c2424010a80140c0b01280030801181d450f45c40382880500103800340f450103110740c0b254425241c05e02c2c02240d00e83c2c0f2450101003c06811712032001d0f442c02c04a4648003160030018190f4032000700380101801400413200080038401c04001080e80c60b04060142052406e210b01c09002500680c010041c084804c8101130007200c0c030a00c1004200c0d0996400380115509040d021 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 612486321 1250 612485071 612485089
    0x11070c0918050c33090a0918030f1b0b0f060a05031b010c080c160807080a1401020f030c040f0e240d0212100f060b190c0c031202011b0e 60
    0x6075400c1d2007607551440031041c0c81c02c44c1080704400b40c01e41703c0d0f02c4041008400320107a00084034190805140c04014002c18007409a03e951500740b035081c0c4690020211070049815203018400801074021806009a580b0003501a1040d8000e0312441d5850a0034071030500160b00c10b03250994400d0443e800884509001d05e602c840f414903203010010504c1e00d44448a4100c0c40d44e8440d036401404c0201260700401d00d140000702181805003089500e044601500d851517a00054001300b4104112203c04100b98101e0341d0104550030001c0c0c507803c18402c40290307500140124551420700c0c02e804038000c8903241032940310f80f078021611010265141694129103903410075142e002803140c41036000590f11040641c032003864400050861141c00b046a0094440c66550701004614000d0107000200298007190581c804041c11400030b5681c42d00125454030030104003510101c3e4071007020040001c1301c0f03080f0607481d4041d402886041c211005840050300d24051045c007042c10499040c419080c50908 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 612487571 1250 612486321 612486349
    0x2060402150906070311010c0f021f060e091c09030f021036050a03080a0f0903060609150e1014030a0b15030706020303190b0411070c0918050c 63
    0x110b09000e01c40e0040740302d43d08103200450109880c2c002440400d03800b4401d04400c40c90b946003200035a41c11030700103900e1781d50311452031030b44810100144108402a803c224001e142c88096987c3da40340c1080401d407108021940340e00021030b901907040c0154403c49844080e2a0062148400c0c09015406c02601d0b020701d0070344009200b00041c044501c5580c0300b001a40a400714080146805d041da1880095102030f90401e502c101c1c030f4441c00384041490380055400060032801d04c0d40241c02044403d603114401580028240703800c2100c08a41c0b054203400c074500b00200d072151030b0302c0705495101d111007a183c01c40c0e4004071000f05140803c0b0458001c030841035150340107010313104d07524516159207400d00021114040091010340310400241420042c0d9402844148041c0d411810060304900c0b14126030800d409a883e18ac0e401001c00c2c4d070b03550b40042c2141c10702c40d00f41c0ea035a08091a2017410821070340311b1000d0f803d02e0a0414180f400f000300d244247c00e580b1001610780b607101c02041142940c10642d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 612488821 1250 612487571 612487609
    0x406050702010e030a0c080c01051608030411281a07112b02120d0912080d0903030515030102130b0706060503070b030108010e0316030e0123040305100c02060402 71
    0x20681101e444c1841400e8a1501178105001014208003880b89040c5004030181d042020420400c0440c48600500a0710142d00c008101c0e90b130b40f1542402801c40d042220401d030f0150044003a10141807494043c0c00801c582075200c0c5860503a03441080d03135000d0a0000442403040100041c00004d80041006a00c064000b080390042214071410b46a1a507160740c0c0c0c1d80b1048081049180a5241c0a00b140c030100303480310010001c1040f504002850020b00b807051b6408030820085007410032080d00255144070304140000c006010341c600b4020040c00e0103803410080c060fa42c074009406400e040c001c0b1200041c000041025181c0b42c58200d444c1d50344001c0c2e050b2482da0751468045615a02030041d000144098a041d40c0c5035418044c61508640c00b40707100d408260304c02c0050f0411016640f995500d40c0d601800c2c83d41c5c0b418480d03401603a4242002900b90225410340c0360fa91440f03a031040103001501d001d0b0040b40c01040d0241c0d4120216068941410003603800500007800518084440f2809031628103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 612490071 1250 612488821 612488837
    0x90106030b2d01060302042111060c030403021005070b0f04030f0516020a03050c010f0c0b010b07030e03101d010213150507081206040506040209090f060307080601030c080105010e0c040605070201 86
    0x4060240c0d0b410303003a0082c100080e000101008135040443d803038144850044a100c100b100e89a6455400600c00545180268004140088205000e000f1f6070000e507000b418107100054601d9004186500401c022260702d4420404140c004015400305031180d94192100c80504110003002d580c95000500055801c4440f0403006005840b05040c0d00000c41c49035004010081c0080d00150010b0106141d00c000c000700d52801d00d01080452030114115003055002e10707030714880c42c20304031001030303613000c0035505486500c0e04121380c081c280d804840040081e00100c4420343e1840550390a0f440341c2e520403035101d0904c07101800600401e4501203070000140c1031041c90540039584001032034120b5607142c80744e1040c0c84204001c509007401a15806102100c046203011958800907650400160000482c980c6000000e00140c80400403d8090040c001c00c07900c040da541c0c0360a0400711818041c1038125402c0c40000540107000c2c209090140b4081001c0508050030f004044401d070704804400e0307040081e94 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 612491321 1250 612490071 612490141
    0x303090a03031d0708010f0c0807140d090605150907020309030714010c05070b0a08060a0509160302040b0c030301050f04150b0f07080a260c090906030c10080708090106030b 76
    0x4c015480c01801040000b182c0e41c4122031030401103a41d034076246000c2c08500300401a880e46d008036402404420342c0c69054070303045640d032150010b000e440c000810051070f140071302c00c080c81c11100140c50b081003221100c840b540c5131601242c49014045103640c040c1d00108042c4155806600e03c3e0070b5071003061401102e100041d8803134500d0040c20303a11952038100005510507440d903100c68042d51004081c0e4800e49170502d00b401181410000811300c001c8000759610701368130079100390101c500400c1410083c988071111080c4a40d00d0340d000b0f11445224908107000300c00c10741041c1c028140311107440d440c41d51074207281000c00131540e07000614015140348100443c500080c414400f811030f82402d56140440d010400e4402d841d48403c0090b044180241c1b05d00b00240a40c841c0d04507200301005070352017866925007101191610300f941c42e10760380c084c0c5821a80c02680d0340c49161507100f160390340d495010b01d4480c0700c403507400c03143d05000c00742c0112450800180080340401c054043e4482d41c500c83c1840040d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 612492571 1250 612491321 612491323
    0x709020414130f1b02160614030603121c0612020d02090903070501090605090d1815020f030703170f04030c062a020f071a1e0c0709060e090303090a03031d 68
    0x24202508940841c1300b480a400583c104020721054031003034645c0c0b10031418108050075004080c00700b040030703c4001001440a0b02e080c400342c0191a483c1300d03a10384442200074000d8625181205c0320f074034180b03800c000148002a10f111482c1c1203070043c041b01d0148040f0780034007021900082c804000307448100980c000266007440340749000c0740664000507403420040c004038101303800c00c05004104000e000c4620084101003549004075030f01d1140c1091120b040840680c00c00d070300461650214080499800181500311080760507040312001000340700e0795108000303910528142c3c1d0141c00100203101d59000548103500c00030382c104960629110320145d200081c4003a80b050b064040050700200e4640c01d156000300b2450000d840180d0800c03c0d060031005d18541140550341507900b4500c5405071507040c881c032400440320344e4460b12087d9178100b5117507446640079003114850818150918400610f1000e070100980e03000350000000b030704006c615a141240509134210544c084070035072008240c440b0324 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 612493821 1250 612492571 612492581
    0xf03180e01140f104e11041508070504080607020a0b060609011d12030d0606140703050a030b03120d1a010206040b01031217090309030709020414130f 66
    0x38601c610141842c050300e051000010b01052182c0c05201d00b100ca0990407600004200f07541604208802d00840f03002172200080660503100310a1610118200015480d0841d40200400b98966040c0700807213a590702456180b259100d04940300400ea00c000388142e105480c040d40150032803601a08140e2909256400e1590030f960744405640310003d044200000a0b0b181607004800300e071f00b40d0800b942400082c002c80c8150100d0840121400d5890b001c590301c014501d41c104402004890b1210340b41c040301c40041030540207060108540c9048410101c3c0b2407411200d010340c0c140d442d1820000304841c15009001c080c008036506000e07401124490201d42c1d80a0668801d0501e408900800c0700039500300d56280707008a1a0440d0014020000070815140c9030f54116a407116018a40c1110124200d4a0884584520580d8052201409000e44001000e060b01440480a0701c4406580e0a54072080744143e2080c03101d070039100782d4071480b00d280000142d1284020b024012488861800031441151 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 612495071 1250 612493821 612493829
    0x4090e030a0201050a0618180609242306030a060203070918060308090613030f080912061918060c03020715060b03060409030318030801090f090f03180e01 68
    0x40d0010895000680d82401110740154400000f00134aa0500f040081c241d046401d00b41551520340034081000d004559a0070b00701074221104001014071441c24040f0742c01f40313031040400c4090301800c80c040418030b4400c81031110240e4442030040000e40031420300d08840140710079410f004001030a0041051340c00110722a18a981d07500844a06000100081030303020503258645501d01a020300000d03408108032140e110040328090344440006100b0641e6070102d410092a920102101c5803c0151242c040c0c0600700e0105d80d000c010340301c50302d90a0368a8a04480c0c601145d00900388d1040760071788560107210400b140000c2c1405000080d1034142c140d0740520400c0340007030350025180081c407007081621110040200b10a010041c0b030030501c5900c900000c0c00c0144503640c2c5101e04000c01d402544220f020300c10110704c1405142c06c0b400c020746580c07070074400c0c408018100000c0450340102c9200d031014451b409180c21b000314202c0c3d00c0c120703002c5620f15264001c0581c0c00c003001c04d40d000241c040c0c900034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 612496321 1250 612495071 612495073
    0x507020601150314040b13140c010305090f070308220f0302040c0203070b04061104090c030507020c030c01051603050c0a060b030c09040201083405031b0901080a0e0304090e 76
    0xd545000b10781c0704561100d00c101e0040619008582820b01d10340c0752078640083c0c000725401e645448280c4401d20200078102c00501c3e241400b01d00e034a1882c0701148414002c1805d880c200708580c1d964810780d445110700c0740c20120640005905100081d022405025410b181501d0600d0001c000f005034030b50030505070001e14201c002c81c4020000c40c5890700800001c4403152024501300901c0341d60354a42402c000d0030003440316498160307404034104c805056034028440420140120311101101030024002590341ea8014065001c050000c0d060004481d248508180d5506141044000c000c2031000600e480403000c01c10704100b4003100c4141048502100750007a0000100d078070000702014540307821030a4840c0502c4600e820080580e070046107165100e102c401160760f540220340314036070440300b11300483c1c1618a42e03d03582010300c0f1b9010b4081c5214040c811900c2c000390904c03070344044c0c80d40540d8080500169005002803c480d415400c00800040341800320b904140c0c640b41e044040c1c0b500003a0344c29003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 612497571 1250 612496321 612496333
    0x1f0e06090702030f0a0c060b100309060617100216060e06070210060b0301050120120409180506070f14030408031f0f060e03101424100e0303070501050702 68
    0x1a19003032198680158031400154a82103410b40c1e801110300522500c5000d1090184c0d00406229894100c2c2c212548020184144855440c030082d000300003a400a0ba00d6514143c00400c0301c01000990300c18480f54070b80280380c44000c04458a01951258001d070004400000aa00004001b800b03104440514100600428900303160001d181102c40051414102d05201c003c002014001048074150750f0b00f0310301a90350901092051120300c20700843c20015110b50310646590500d00d9003d082030300d200e407409001074000364180c4180301d008000d0150041c2c003e500403402e401e020301c0302010140b00c070b801c04140040c001811442150021141a100080e00104112030114007d507200b10b1034006803468000b0500b4448030b40006c0c0c01901a550520003504d170054601e9408015952890305403003401c0c41700b600c1d05e43c5200c0e6901000d903440d0a8035400d512041401e400b03a180c07159a901006040c0208650304014101c64a43c0d01d0032429415010401107080030540030700466120f010590003d1070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 612498821 1250 612497571 612497581
    0x140403020a03140304020f1003020c120a1704080430080909090d08010603050c1b0703020103180f02040f271e08120c0c16090c1409091f0e 61
    0x1c29060f00701034a40001e10104100001607813002d8203500903910aa861840d1802603140075002803249508508880c4101b4910810035440c040040078240b249941d0344968254044d88207076095020350f0700420107401480148414010003200b0b03580c5400200b966031880360f020000b00317010100c0000a45011400140031070707460428961303441d040045c0030001c24048040000041c424901030003100201034454000c203441c1d00002c410782d1500d004443d03c1e0340082041c003010a69038009440308070701090903c06914282d0f041000e0901015411003100048941e482c1c1c2008020104030546002c00e80d9529480c00d03c06201c0d800280740403540e50140d041c518030310b08160000001c40c0b55402600c1c40340326422800900c01900350b4400d001c00f140044101e0301c8150384500b403030099000d185d41c1417044840e10303500c2d40d410303120a100303c03480c01108100307030004940212840d4088031b9070148140c00400480c0c84030305007400c4113030344504041c5081442c0246c50350814640e9829620500803041c0c40c000f0b100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 612500071 1250 612498821 612498827
    0x30c0503061504032a050d11040903050408120d0e1f0b010c1e0c0e09100b0307120506160503060109060e130203010f0801060b0a231e041e081c03140403020a03 70
    0x170083d2404803450300c0b08000b00e07655003103c0640c80c2e04c481c0c003840c2c44500f140c0800d8000d00c15a4060901c40d426105104880f0714070703c0320394005950344e143c1b090500d020640c41c58004a8078500c400c1c480d13629454202080074400024001d00c02010b41081046220311012541551000701541d85200d09040c80715860705000b4542140b60300007e2a2403800014801d00080000d265510b00c1d4070a407010941c485030800007401c242c89544980600c02400c02c064042000100346244107915541d0a403201d00444203086956000480702035011a8058100303000c1c060060a03803c03944280245007161500d601c003151000d03a00203074042d610a8042480c140034115080c060440500466030040d03003402880000140405641d035040d1103409184200020315021040440f1100c03c00b0b040c940b60314211403010141507912510a901d80040c1028180e56060480c1e040002151540001400d41500c40c8800b410744050805c0208207266684805180e03031403041403201d20850081d0003406010300303103040103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 612501321 1250 612500071 612500153
    0x203010b0906012709020408151609030201050705010b0a06031a030307020d17071709100e090109050702010e0a08071b030510050c07080c0d0f030c050306150403 71
    0x1852168291200b0410785036800b03000c000c80c3c9208034000080c225059928446400220b0b044600700500019000ca00300d0000502c0200701c19403846050119558a1411649076a000307810b500050210030342000958810406081514009c0c80001241d040c03910004500c01003e03400040405e4640341007485054100c0d40907040008290065880e101042d80003517820110000010b01c000a43c3d10301c031080802c004180c03484154440104039000712400400b01e600e4012a5a1314400e2060341454103056210b007022600f110005012f1103416401c0c1000382000e0306000388004215941c0b5032480c01c901d8801c110504030701d07000e1010180c1d6030142e0b082c2004a4000c0c0100e51104200700607040002400000b040f00c9555100180080d842d2243d00c403032022840b81e1b4038080d240000c0403940d44040880411a203859112684400103002c15001050302a203801c440540040b410520005074642860488402c2c0e60101d2520a840e1130b44035a114690305000142401d00e04440c0e240303014a8910320400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 612502571 1250 612501321 612501341
    0x40e0f1b09010902070f0206031509100303050a111c05040e0901150303050a0504050d120f0212090904020a090c0f110a0f023307020f090702060402011b1509020301 72
    0x201034a2600c980020401030401889012038441d400200142030251010442242d0b0303600405c0a5a40c6c1400140d01c1c840300f42d07c0114522505010001c15051502c40d00f180040320b03410b846076420800c1200c0156503405201d4801c0302c2c54060310981081d8a00041010f640a8000b51601c0340c44909108000c900700a00400811943e854110485a800510480360045030b03410724040da80d500e404c1104481901540e4022604400d009000c0410003640d210b0030f142131822a0340b0b0980c2403014410481e84c582030200142c3d94203a0421401c41d0a0174460000369000340080d10901c61666038400c8841119569400300b0005908034100b011002e5000b2402e44c2020a03281c001c25208140e07481c0c0740f2400c1c03548074000744110982c075405040110f024281d04164041c650301b620201d19117400420440c0d012101c220320400810807584901c7c60a442254090f0025071300500c10360380d9550040d141204e410080c400300040c511000e500007104e00420700c51070005210041a02c61352071051609484e020300d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 612503821 1250 612502571 612502603
    0x50712150903020604080a050c01050a0906052404090201030b1002010c020f06040803010e06040905100c1403010b0301060c021503150901271d060411011b032c040e0f 73
    0x1c40c11002c41e90004000d0303002500324013030070380c0d41c11a024161070350312031090300031002d500b0b020070032003005030f103900180f1018001c00e0b0031310290342c03800c2000280344050060340e0700103400d0000306503131403c1c180d03c071810f0303107206040004140035030500240b0b00070280086040180c1d1034518900d0140d40c1400350390400c8004400601450a00e80d60701c6646000c14050627000981c01d20019003030340d071690448062290810309441c00f0910941055020b403684007084030120380c001154a03851318401d4112030417a00b26400c043d09503420035804591041005200f41d074400004160061000d144100960140079003580d001c00412072402441000b86050f03024081e441030440e0044070b1000e120a0a12444074650000510790301e141a07080b092480c00790000701244101000c12081052500718005040c0003600c581840d1107814407641c07001c1030313403850080c0051030300940070030a0722102c00314982c00031006180501d910f102070b020500300e031148586904503610407100502c101605018100da20759560b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 612505071 1250 612503821 612503831
    0x60603050f15040b040c0509040b01031101051305100513080c0a0605090612061309060b0405060607260712050a03110c121b011d010b0a1a03100305071215 68
    0x708041c2c0140301c000c00141c0208004000101042040c64996024010007844102e907800c06042c00341405100340401c0322488088542c0722969030003071003919040c7c0c0c0754521508480c1d08150038061411503c4180343d0034400c042c840040b0813401c0c40c02e80c1000c1c1104400802400c042070041101d00d8980d5841001400410040e00060b0b8884000300e504054141514454549540c2e0105a808025118403048640b071b0030514410414150044480e04800711030074407580d1030b40b1042006501c1400c5001b88428100401005600c0000300891845050b170600e050078600151036134103140c05a900070000141000600c0507d0b150140704002052801c09011070503c5041034985644500304140054401070100d040c0391040364919001198000071802440701d45913904640d0100500c02d09218103950a01c422080316042016078601100c64025924200c410282c06080450340080e20303109006284078000f00205004000901c000c0c080c00ca0050400c0c156818480b5000d00c0c03e03091460154201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 612506321 1250 612505071 612505093
    0x7120b010c02130902180a060302040e0f0d12020c03070c0504050a06050906130905010e07030521030601080403171914010b18031c0e0a21060b030109050703060603050f 74
    0x83c0401440180b158100081c0300c0000c0c0001102c4d800d4454525040c00c13665010412521800c2e0810011030344240c44c140500c45040c2d400644a41001907291020b0784046840f0b80d03030034410700b0710a0307010f6011103006181c514451041e90940e070118206407074003030383e018040202d0700b054803503580e21040b0342104115250401000404220001e0070252150b003881c0350b5520302e2000c0303a200f1401658080b000b0042d0001e00c1001646402e40c0344402d56580c050141c0b60444414603510400840c0080f1081900d50303071f6624010344000c0d001404c00e4041061080c1841c1d02c6950215056010310840b0f00b90069018015000d038003036583c24901d51001000d10310041060410002c241c81059142d070103019013103205031020a140c4800e00306121074003200c0390841080d140d084000d80e4446102601d250500d9501c40061012802814494019000b10400848003148056001c440035050080c00480e0400e40d03610742c6840c3c862540c00c103a50859842c0410020840200030014500c402c000c00b600c0004a2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 612507571 1250 612506321 612506329
    0x801080303190b0f090f040c210219030615080607030e0616050c16030b0a020712200d0e03010c030c08011202030111030906040b0105150901030f0f0507120b010c02 72
    0x3803a07403150421a1507203208601d50380c52546202e013071a0090140d181903d0711803010805000d00707980030f841d100584c0001003200ca1070342508002268a440d010b014001c401e5080c808650ba260749076035107035521307088007000007500c9001300c105201c2003410f5003c403641041400380c02c1060151401090601c0c1c80d035091103a0b000130032180c1d4810504941c908a032066942d01744e600d403258850b03030342c41401091b500404480120102100340c9020304a90b6010355035819040c4201d20614001605003411042c44500062140e04c01a03c0414101c40c9a100d0103204118a403820b1540d1580c000820441c8440b2151400e00340318000050105c0d107001d018405202e8000340180c001030081300f000c00000c41116040d0f440940080c1c2455441c107410559914000142e0740c9c807408240c5048500c00021400091203142c0155400c16402e100b01c0c400746041d40d8100151b0080440d41c0441015540b00d1041108050b0300d0310034603109008a032907061039105c5950100c03040b01e038150780c21414041608407001c05a25 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 612508821 1250 612507571 612507601
    0x1807030e1c1d031009050610050a14040902011e02070311041416170f180109050322030c17060a0623041517070812220e010609060801080303 62
    0x16000c0782c81958400c0d0308000c207050001c40060004407500b0665114104440003c80074810f04807080e40590194882c410007802400038826400264070906020034146030542c00a2076041c81410701000d51550354001200300229401c03800c8c0940c01c291410802e0140c64503000c04001c0c403c0350f0030000502110300250301c0907005030002c681180c00c4090714151030700508910310000020000740050f4a4030b0016003540e113500321000003050950f10140b40b158030b81400fa00d441c4a40c817002a606180b91100340e5040c0403141c0110319a04e081c072520000c0844c60000041c00176000f4100c2e0078004420300ca003124074142c030180c01c18906500d80303030080050161040c511005184150f00f2400f000880c000010082c1600704440e0140951020000452210400715140b6662091003a40c54680da00c09507035440c0c00070060610b0000b031041003c0c100004003840c402441c0017103d44d250320350585507030004a07040001d800c40c10225070400d03414052103420030002c03030040091000030b41c69031030102c0350551218 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 612510071 1250 612508821 612508847
    0x91a0a0906081519090c140d051f090218010c052509020408030a0e0a08060417071e05010b0618120106080703060e010b0a03080a03050c0d0e1f0b06040b07021807030e1c 74
    0x2343e5648040b848080b6050480c030f0f003558090903110107454880d01400c000358040502e181c880ea555400e002900d501425134001c0c40e6401c40085e0001514588003440403414030110300000c50301c0c1c00e0021440300801d201802c0a4100b450007140c851251b140050b10031000c03030180c3d0b44204528107040160810000d0091740c0070340e0056200660b0343e6181260009400b030f081c002041603820341340310006100f42c43d2101c100315011728000c0c45013482803000c0c00604d2098a032170000c001115031403100c06c4d003001181c120a000c21480001070312561060311a05018a90f0021034202d6201c9802c0103208000b400f801c02c001c00b0031116419424995a00c40c456072181c4411a014580c840001806603400380050b508041010803050100c000041d803080d4461414001c880350410400c10100c41c044114400c032140380d200901401d03c0d0500b84104000560007a00040380e2020402c0c0401144c40101c0902c40d01031446a00c000c20340d0350036483d0030703820041907640300e403500802064560a441e0307020300d12106403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 612511321 1250 612510071 612510097
    0x632180a050d12030218120d0210111e0708070c0e060307050109090e01090203120a080c1801110c04020d02041502010b060d0216080406091a0a0906081519090c14 71
    0x5c0c5030080d01d080c000000c8086c4072944810011004080c0500104451140765050760940e185072020000203000c0b100611549803040100707110844042c2c00507038402a440000c00362443c24440c442c2d44038044c0c1d9110500840789200800d104110000c81c00c0400d0380c009008402400ca01428440000c002d220544a412215629030340135244000d021f40c009985642c001e81581d01307260906d500800c1c40c0e40b04040c10000608101c0000d106601d02c24103a442002804000d01c0000e54010011184c0000346524250507000300e2140d01a15921403008100030440c5000158030b41c0d15044000e2800b110f040000c00035641002030104240c0d076507004032074140b011081d006031140c0d01602c2d41c04c003190f04200000c00300480000d0114141d6048502135040f19661105e031448480c641c605010b80e80203052000c00440d40201051141c5402400303520740c080b002c40006c5a14400000000e086100410a030144540c80900148000c04036030060300c50b03007a49400c0c50741561a40d40c1180700da41c0b007920080c0b04a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 612512571 1250 612511321 612511327
    0x2040209130905011b0905091b0f04060804021305040f140a0203120310060c050c0402031803070321150b0c0a02030a03021005100632180a050d120302 66
    0x145981c1e00c2203844800c81d080408004200031490030300d000b00080499100035000008040c1345542c4214036820a603400500303001c0168442c9101d1440000c6004d074034000000040c49103050403503007903010304000c2026a5800c1e2490400c1d005018201c4000e201003c4054141400c11004c100d80800b003080301c1e40c5c401518044595408081400c00000c0d100c0250b0601a104201148114050155016204403d68055003a03501e001c00c2e5000200640002d005400c028203100c0741d0310749a03010f07651241c05161022a80c1c03030b103424800e06543c003d0104070041460219614103411110584e2500b2010200080201d1122420030704590400c9110781f054001b40000d288003600014018101c0560b409070860f0740340d550704c2c0b9000c0c1d1035142480d61240c0461500c40043c0c0300510130003001e001c541c0c060b141d8855184500003d0702c11030310aa440c0c03011505a00c0d90070510341504400a2400c900245640c070290b8440004100080040e075010034411280c6086410110b09081480d1200911034100103907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 612513821 1250 612512571 612512587
    0x61a2d04020421060b090402031c0207050a030305070c080304231206010b030901050708070c0803070e06030a0f0b0312040b070c0902070609120c0b0619030f062c0307020402 76
    0x201034441c40d04900e401845850103801c0b42c0448032401d4064520404003400401780c00310602003210303c00c0382c0107541130b8802180984220b1510310b80841c41c0d901441624142502c60000c00c41d50a10f5a00841c001031002034a0028018035110040c040c0100d03401075450b084c80d0211210704900701111503040340b26019036070344080d40d80ca869228152020790035102c40e0342c5c2d240c40b2101d1b2074008860101003542000001041144035134802485a0440e0300c2e0443c03114a075440300802c0e9040144a10203104c103c0e80358540e6581c1d6140518810140c20b1404540400f0300402001640c11034170704070740650300c48d60403a00d83c0e8400600340e40685403508101c90300c40d4042d003002558403045a2000a41a200041030014003a1030381021030114020006082c0780626030307000715112504020080d00c00c0320000003054981c030b000d1000d2409594a80002c4a1498603a00c51702d0300039030304007001c440081d0386031043d0030007044019102140c810b25440d00489052032075903403030302c1e48104c070702c001c0c442d50740024002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 612515071 1250 612513821 612513829
    0x5011a1b1e07080a0312180501090b070f080f06092e0e0603030307080c0c0102070204051609050a0305031c290901090b030a02040c02010b030307061a2d 67
    0x55101094401c480e90790000c0320095000380281c0203076030120700a076000802c10b80000148000000c0e496503a180365112210583e500400d071029600c00c80303003a002003440208000340243d581030b600400c000c0f050b508220304040d00c06d8907152501d0003848110820095041e03525a10341d42d0002041c0c4130f01c0380f240d440c18100040e0410b0140f800300e00d43d5844226003070804004008005588003407031081c6d0740361074020805540c1e0200712541400602c0250020b600c0d400c2c0f2102511f034001c070400000d030900d1403540c0040d003505d0080310700c941c1741390030b642003050f601e07a0010030704e401484207076035503844141580c0b10141ca9100325406809450008540c50b421003410341c1c40f009610030707045900742000c4401e0303280810014100703503802d00c200e01001c00429654a148110011242e004000f04544007003642403101030f00340c20340c514040d07550790301390604603403000c0c4020003040b44640d0000032621003290b00055580310301c1d03510030b000d940d001307000b081311022201c8040c0c0058060300c11000460401c00020b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 612516321 1250 612515071 612515107
    0x40f0e030f090a030c03080304060c11250f030b060a0b0a0f0f17010b0703020706020d050d051e0426070312090c0f0605131a030f041509080909090105011a 68
    0x10100c106441d0008144454400610b012758843c0703d007030200c1c56103000c0440382d201004a42c001d02c0d801900c800591002c030742ca4900c03614104104031070072a07950b45074650001c4819520039174a101200c4200081840d008041c2c0029140b03042c189810118000303802003110515490781c0d004c0c00081d00e480d8420744d001d07581029044240540c030404940c3c44a940041c543c200880c22005841400360211303c2a0000c80c429030014107643c1e800707042048080440000c0c0c50007070035600c0c8040b00e41c489028042e10b2070200a1065000340005401e515034828245640400c1c9419140044018404080000d911080300448083d000b40301040d00102410b0006901460343d10000c900b2040c807100003402c58000020b0415610381c94040700038103076101464a2000d1602e503006c0040a01040001c2c2c0c1140da0b25040fa401c0350003038a0009604200305000c00445610000aaa8150000c41c0860f180d01d407402c40302ea8049a4000284115494403440481e001c44002c02074000c20340c041000b5a61b20600446 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 612517571 1250 612516321 612516323
    0x30a060b0f0c01050708010806130809060c070503070909020a030210020c040504060501150e0d03050a2006040b01140d0b09030904020304110f060406090b03060a0305011406040f0e030f090a03 84
    0x6aa03a610307000491260303072082100655650a000008a00b00c1c05108000e04136080c4402810141d5034241903221002c0c0c0071142114031000502000807a074440070f0252100c1404c07107004104e003908150416281c191190300400400382080030f5880142c8528107a10222607054482c3d45549085000130303400d09a01c0310766036402c18500400c01081c401d850f0803540c1240c0c0c007002c0e503000541d00c0b41d800b00c0c0d1844215490b1608074140c0209031001034030841c0140317104403003890700740f03240c0c0846541903c4004540611200382d512000a01080c04001d40403617005151001401c1e86a00d41d01022078003002d0b04980c05060040004005130034042c00340202d80319540c1c014400c540e40c0c90a850414402d0302102115800380788000d01c00b8100d070601400715004e41e0709980301c0a14087c0f420103242d0880c0d10090650f070b003100004d0302c00400180700340280f4013800030b0661004081d00c0c107032003400216014041c1402855080541402c6c2104003c002c40d40e40313844850039141e0300d030280d40118400d003601e0380c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 612518821 1250 612517571 612517589
    0xd0e04060806040b160e011b021f0306150903123f0506010212032202040e062e0306090f140601090b01260901060305030c010c0e150708030a06 63
    0x10001041130840c3c2d624482c00d01800c2106201203910b8085605020301841c05000c5098141544146038140091004541c8000d02403105000c000c201581910740c1c040030080482d03104c8105109111900d40f496190b0341003841c00756401880d50300c8014900c00045408000d00c101100c0c515025000a503074039004e050b50581001034814240004100c04902c504c00540b800e190102284541d803000c02c000301c65925490046041d900d03036800703080c403920f42d2041001c0c4980207440c0f180c0058445009542c0b01d184c1d4040982450314100314612441524130050040300c4440c07485d9181c0c0f1100302c520078406d13690420340028041c08540745c03986800007041c41c050f09001c0c03c00c001111000c0f000807124142c1c1d41c00d02c020f2192880b040015140c00172681c500100900f05034080030f40801e400c0d0301c890b501098a070001305055640740c50350303400d5a10080380d16865945541071502100c0e0032114074000040283d0b100d032200d1201500100c400d028102005014441c000013148904034190480300c0600310000b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 612520071 1250 612518821 612518833
    0xf0f04031e020c0a15080f090a050a0b04030e010f200a06090606180209060417011d010605010e150306010e06190207051e0a050103020f12011d010f080d0e040608 71
    0x1c0040c0d500c103440d1940341c0c40f815450030003080e440820346000500f0300c204c0e1500b1100c0d880300e04109003840030040400560b80f140090410100d14100022082c05000d01c1401c2450f04003410700804006035070018030305225a1251148005030311051050031b01004000c0c0803010700c0c2100416081c0000d212024040e0790900400c0001d1003020341c0110200c1e00a07001540740a01e00f080420140e015051001c1e50140c0140010032029110603440d0b0400e444100000514004a9800c07505405140740c80b40056035456906000a580143c03c41d00c02045c121210000500c0301240644a407000510b55410810200d004117007584403a0b003503a1020344224096a95160b003002c00940e140f25903c01c4603c960340c65850503505100c00c4050070b004440180450070074506003401500030707501960f1808400d0302c08100220b500d0a2041d0120f001e0004200c820b0192000b940700c03a00441411303009079180c80b070382103400c101c100d10000d003a0483d1111410440e20184842000900034412544000c1c250700400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 612521321 1250 612520071 612520127
    0x15020a320303010807361404050c09150a17030c062a0a050d1a04020d0605030c1f0c170a020f0106061803020111030705010e030307020f01050f0f0403 66
    0x70010394103840ea4001112101a40c0c4c0101e60b03413101c01c180031615904c0e41510324403c203805001c80b024598400d800003140c660981d070701605807004100c2e4140c800d90424551000940345c004404c41c6c02c10811030b401000009128002500d0801910034038017031201c0402c0400c464401842510b44244001069070107a19000007941e0700260310018080e613211900050000b0085003a066540344000381d40c5040c202030440b0b400e81c0c001e10341d10080c010b1030003103e09203604940c0d582c0010705d240c1d43c6598003c181d0354070341014185030101c41018180706100901c4803c81701d11502003401240200b034500b4800406003420302009076180005070500300303640060a00401500001c0fa184002111030080089980d10b001c00c95000a2550236030f104900001c0c000c101540c45020a0283c03621040241d0b80b8001039580c485007111540c000890054001008100d0400d0301448600301c0130994900074880c0749885007e010400c18000d03d104213401d0f800c0c020606241c0b1a1907403401588003851107015010203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 612522571 1250 612521321 612521323
    0xd080c0d1805030f19080403081f030507080109050606090f0610030207050102180f0306092d0f0a0201090b030603030d020a0509091f06090b030406020703050d060f0f15020a32 77
    0x1101701c2071031042400c601c0a5034240316901c0c0a100c2d5400d0780d66a2004e4841140c10440421a060400c411000e0902e010010580031700031000104040c1c0000a032400c1240340031807e2420003409184a180076000b0051803411041940da40305204070f9201d9200c0c180620154024054690043e00662010410310080c00c0741c0038684521520450320550b400f1322280801d0307070311a0125a003c2c1c030f90304000980ca0140603000003400107004420502002042c0c10f2100d0741c901980c5908241055203c10186401d5581140c800f801030880140000c1c6940340c0314000c00d030b403842682e030307160b00003540020060200351003101910b10b0000c004084d025a410070002d00340640c601250a08100341c400c42000075101d0180c0105421104615015400d650f11500c40c10000c0d000030070143c050290400c00e500e0009801d110303050143c85200b440d8000d042c1400f0150b0315052080c0c0151032030000e05c0b800ca00340d80340c0001c0c400c8021a40b003c1e000c583d240c104044091080341e0518001c0b14080111000a10000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 612523821 1250 612522571 612522577
    0x60e1002070605011706060a0e070c141005010515030403050a090806150f0d05060f100b0c0601150c03051c0e0109060912020c06120907050901080109050d080c0d1805030f 75
    0x2417190480b802c1004100482c0c80712003d80340c0941c0300300208000c2090540d000c901551221070384c04d01c07006c0b410780d54075881000e09454171000259000b8051000001c40540f2446024003400d0f25401040032700300885070280d01c4050005014010045611a110380c42055000c02810001060301c8032418080710b40d07016a01850080e5224001c1016103404608142000d0b02085401500074089030301d400d02040c2c0001404ac00d00030449070341410201ea81a440b100800f81082c80c003004042940c0750100e107211218080084a04000c000b2128030b01080c0c1c00003c4e00c00016416440404414100d001c24005040c1003031034402c01e500f803552820910000b94080128140035242c0700a01420064003240c54034504101158002c00500c0000000800810400e5000b00c00c0300403a9a000d8a9200046018400340d000003210ba45172051501040303811700c0440213020301e60415401c0e500380080c1107500c0e4029901c0e8a2006980c50075101284041040d00700e01894200080e240d691030140c00c0c1841640c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 612525071 1250 612523821 612523829
    0x181823040501050a0e0d0e06091903030e0d0b0f090f07090902151315020f0a110103140702070b07020103060b031f0e0601020c060c010b15030718080a060e100207060501 74
    0x35203028000358480b00e26000b40c028041d001d1016000c80c080c002c6c0306607540105842c0864105805001024503600c40039078200c1c00901880002e040380b0320b1490000c00284400080500491814515000240ca00c0c04030a4028602c00b60700b891680c0c4640e81d25160001402790031071a885600300028002005904c1680c45c94001e80f02008140da00070510b001030311075101a1090010300400c20800b00c144d407042d0411aa456205551301b8660003211300745083c44000d819103148800702c40c0c101c0300c0d41e01845200d100c582034103220207144c6400c3da0040c1d140c00b01445480140800043c03e1401c5a2090f8031400c00f60451060580d104d007007192503803944001c5c00142001e154102076010852001041c240d505c00c10341680246929071000d0244021500aa03080d50203070364a42400650307643e501c02142d0581025160000c2d1240352000c401400341009182c5002e00c1c0805070014481041d01192441d0441c2e0800404079615410342c088a00e404d0740b200b10181c40c00c0c800300d46901040101e4000074121 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 612526321 1250 612525071 612525073
    0x4060614010e06181c05100f0c0e060309070e01080d0e030a0c05040b0f060a0e0406090c05090607170c03092b020f04020f120609071818230405 63
    0x400d440c000152101d03549620403075402101070106518290303000030252034060000d850481403003c91111540c0f1400c00c2102118a5040a2540a110050b9105401140040010600c802402500042c0c4144141100c1500038040003000074200141000f840004060000001c2419030791411900d03150024100c1d00d50000d001a1240a001d00c0c0004480c3c1c102508a83c503c0c0a042c6080c0410000f44146480d06800c6000420080c0320340c1e031101e01030200220252104c00c03160484008010031200f103504003080340c230314090440070001d5100013036414a070015503540740c0d81d4040e424003108590003444050b00b0b2000c000384140144001001800d44410240c6841d2002d01d1f000034201103184856400c0c0d514031030204554405464120b07c0d6440c2050040c000514281580c01300e82201d901a0005500780381ca03213414421075007400c03068107078004a0ba2070001031100302a44e036481d4026403403141e50845071902c14a80140c24555100710843e000c1060309030303c04041e0b18811002c48504442c16103032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 612527571 1250 612526321 612526349
    0xb041b0602150f0712020d0f0c08191104061b0609080c0f07120f0f02041503050c06090346060b0a0b0405060d060b0706090203480306040606 62
    0x3c1c0341c08110110300502030394403803482249205800e100250410741084104035100c0c0c1c81440c2140c081d10410401c1e025a80e5041c031145002e90700d1040c003030901112140210710340340301c44102500d041e090303d042d1040d0f481c02c41c1d800714035440003000b82c0c800c0381c0c00608090300c0c1c04800740400c5403207001009a0900c01c0140c424600c130110a0300c2c6c40308100e04c0b030001c0300e4140c000758100044150b2840d4013142c0c4243e0388600c0c003903041d40229044440303446800704210403502e814814440208050702840e1000c0300c00c1864480c008011a443c0d503451f14004584045201c9a00100d00d12000d0a15a4040840030340203d2504800b8a0300810448101130f01c07498034080e031b0000c0754105642503008bc1d80000000e180f03440d03d40400c3c081980e02031554011900c1d51000c01080140600000303003860740c004c0101040c00707802d0340101030a0232030501c509141044124a0400d1011080400210001e14000280c4080107060003400d01485251865a4540181402c0000f0468281d2042c0c050b904e5082e04050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 612528821 1250 612527571 612527581
    0x1009050a240219030e04020d0606050a031109030d1107030b07030b0109060806030a15020c0708100b01091a07020a0b0a030e010e0d122d0b03160b070b041b060215 71
    0x20300da64440041c9180c440f2007140c00d1001c24003a084904910402800c01803800c85840c110000320b80f0305400c4030380010b400007115204a07500d40100012907010140c05480c104801c40000d9681c03592401c58001d00410003070021040c001484600019904044100400c0c038251303038002c3c0100a800c04c51404500b0300407020900911440c1c0c4a03100d04009002000300c400182c031600212200606881e010075001c0043d007140d9003007070108000428058000703046059007400c01b8400c0e644130740a81410030145680400c2207a842c05028940c2506002c0e900769156118000305100d0036840e0000e48182c50001170075101c6981c5035106030f1201155030020030403164194015525900382003a42c40011ba1301103d00d007030900042d031003180840440c541103180301d5100c550a60001c48002c010081d041c0d5201005c600c91f0805010541248050140c05441035041500d00402800f0b000300281103a403c0c40001001c21617040080300403040f04141a500c1150740b160003d607192510740c5450030303240c00f00f400b01e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 612530071 1250 612528821 612528823
    0x607090906060503040204111908100e060306150a0b1b0708070602150604090c08030d06121e0221070f0e0c04060f050909040c061b0206091009050a2402 67
    0x1042e2001d998801d4a1620766800300030240c00703200400300c0d40400400c50003034015920303c460f0022102c2030300d65100130719221a40d140064515403018071188a000c0c10486e450340c02040d810742c015907a40d00010803c407150085801038107690481c2d0825240000c02c400c503058131000800c990322100c81101c2080751110038a5031207210354421240903038404001410f01d2910550010742c0104c0290000032280d80b2900c0c0c03d0f40244940e4003a0860740c00c005100c0b200303c00c481c000c2c030019001e291484800c40301d00760384034085042a036013150600104a12804c0c2150389107020303807180c01c2c66000c3c203a5108000400d0301e6103a2040e8402c100f11020758150000781c104125108a10900b210316900381040c0c6810010360303c10039004100d20820801304214505680e070300c07070502d01503405002c1141000b4100302c0040d01e810701c580720301000b51100416140060b5614000c54968040a5500b09a9401c100b0f0050f40c1210340b90b001151702400c0c00002044029840f0354050300320341ca1600c1020020490074040e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 612531321 1250 612530071 612530081
    0x30105030d030e07092007060209030f060f01090e030c0709020912010b0a050f06071509020f030610090b01090504090b09060606030910181b050901060302040e0a050c1b06070909 78
    0x70304000e410003201000403601c240e00110300900141b6a2017001306a100c0c0225560340542c0c1c2c00c40d04a079010980a9850800b00a1541c00007001c1c0d00414150812100404c040d0704144301e041d01072900e030841607405010500070f644100d00c1d513404541c41162a0715600001c5c3d04010b40041c05030864500080090394140900e00380d5200180c1301c1d406041c1410103100010200301480307034211100300031220000b0422407040920541e40d03040040e49001b1362040000c4c0f1141c5103403480c403130f5120500b801802e131b501098490858425000004c2c101e8103480043c0e4404015500080d8400d18100075041404456200e0071f01c50028501a98419500d1808210b4980400e550480055100040da100d04126a50040482d08168400041c0510132960f03081282481403101d258100075800d400c01580c00c00507101409451541400c3d03092600300082c2030040c0000400c41d04049840d04003040d0010f03851421610080c2d10348034481c1070043e0450040d03541d03078400d413a82c40c0041e034891000200c0007054451 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 612532571 1250 612531321 612531341
    0x4050601080f19062310050405010b190c061d06040506010501140d09030309060207061a0603160c1103010c180506040506030a0b0a080709060608160e10020f12030105030d03 76
    0x12498201c06480c4c06004081108484050018141070a421820050700340c62140c54070a4403440082c1c03c000070b0005445040e0b1101b000d00380305000561a10230f614010a117000c089103400d984d001c00f541400c1020b008107500e8404030012600d58000ca0032000f01d612440307580074004031407059a8910044a20303000040c1c07080f07949102400501d80e00703142604a4075105000c1d181c04036840f16283c403040100da01c10340c421581d840e5102e403024800040c880300c1030b1031550300700c46540c254a05066440f002c00d00009450007003184086400c42041043d240312204004054000c00582003000d101819440d40c2c12201c58030f80e0072603030000400f460074008842c00e031000030709103030304685840d9031110140019052495000608a1011501c204c0401c001e00013000c1c000c6020410030314190000c1c101c403030040c28481d244400451810201d90b00109403071080c050584400003403a00d0804200d00f000c0800c04004901e00500c034068a0020f000303030296050b24412000d444500107410015400c480c5800c0c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 612533821 1250 612532571 612532603
    0x150b120a0b09150c0a090e07170a0b06030c090a0e18150403020a1401021b031c060302030c010e1f020a12020607021209040603060f2304050c0d0c030b04050601080f 72
    0x4005200126084d000d00054442806d050034a00c2d2102000c1c45100c01c222260310001303440c0c04d0b1900d801820300541e540c0003000d4030805c006400810b40883c0c0103200040c40001460400265502c3c1c0341c1320103038035400406400c100742100713081802588401c0546039130090518420300394481c020003402c0c030b0300340d00550f4103800600d80070101e961a950b4000b5403c44540042d582800b15903007045a1904003a420401d210146d59a04c0048100c5c140d02186042103420140c5030030401e01c016200040c0c105408802401c00b9410a00801c0025203a4102107440b000c4040340b0700d00750080141c00082084103184101d44c5240000a03ca104a0380c6000840740c04005901c45140419a441520000c141e1968050400304100340c603901c0c1c001c2510040c006007844a96118103149000000116a640e241e4802c18108182d081035215541d80b006103003071552050b1500e00e0103000b0085907031490001075a00082100d800d140504000342c0f41e007002d11034000c0c140502d1209000c0e9500114002c8000c41d0500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 612535071 1250 612533821 612533863
    0x31d0d0f0c06110a06051506120702061305070902030903130909020406060f0e040504210206060a080c0a03061a0a0b07021f20030d0509071706010b0304150b120a0b09 73
    0xd21100302400d4040c03e00e1f440400d400b4500d0169407218401041040e01646070300c4260300740404000d00d880c0004010903000980d5125200018a001c20024120f9081500c090384030b071240c85070181903203e034031144040051500400540c0c201c60f034202d101994000c0b00c0c02c110895a5200580390003055102003c000740409821001a1030254411130300b0078040c408080341c0c480080c2040d50422400b070707442005648040b00700111441c1c0440294054142e0b1030140980b1011107020a0640d1814007004010a4540e0f0311411901440c0c414007180340c40060104807281e540d6140c0c12101c1d0310150007a0b008822800006011480841d002094150700d40d8510b024960214182410304010b80c2d2443c141b40000c200540304806103006013030242c80e80d0800742105500d41680d00850000c0c80c501100c1582080c2e0041150044070405d8030f41c0a03400036200030740755010b08003250041c540354401c650310180201d14018495400500104014407a07640c50b0810f8540c0400d1340d550740e640710143d0311000c0011f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 612536321 1250 612535071 612535073
    0x3040c1203020a1707050105011208190507060204030804090507030603022d190f080a05032502031501092301170f0604052b0903031d0d0f0c06110a 65
    0x4114400405000b44103407000341040380c0d0340420668420b4044030712840e02044604c10b0150a10441d80107009444201d501c600d0181d441c01810b006200400030a29210803000700701500440841c3d101c5640502d0840d0348030b40701d103018101034000303015005400e403526002803261070192180c4401d80b0740040c000f5503031403800308030214806401560703420404d5580c0d110010641f42c100c0010401d111074210002007a007401c3c2000c2450690394800c8040c0d9004003004004540088101d0704158000541085c0d4003d40030300075602710924a000a4040c400d51412580c1a0803406246058803854241400303121400180c504030722040d082d41c8450100d5010042112541c06440581c01c60040d01c10780d0460000c0020760350800d81e00b124140d5658102a01c1e001500030400801d03100420307105c0f01074000b0804614010a000d402e40001814455402216192030300c00c03e510b101c1c09000142210703a91003091a0040a48201c03580448621201c080080307003c0d07010301c00c500d0040d8040d5000340928052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 612537571 1250 612536321 612536339
    0x1e0207170c2407060603060207060b01020d23040b03041112010b01051210030f050c0f0103090f0311030d0e030c12090303220e01080105042109050d32010c0503040c 72
    0x10340300d1410700c2c071820030500c0300160480c0246001580160001621044c1c54104103050f11010360040d0304540028050289072900290248404030703440b4032070002c00540d2084c0301d03403d01c916007011040d100040200300400c0700004400170a5903065440060030380c40d22411301e09941d5201180c42c0451000c0c4044c0b14548601070f00154081503004039800e0060341c175100c20404042c4100180c0b56900000101d0080c3c1c00d0400a552505100b1300c3c6c1001111900d4480701028204544000d0800a004988900005040003912076515102c4010070000c28910f100c1541d81e4001d20000d480707400340d8100382840c00360400a40b0041c4801801440c5442c01d408032142c80300700203400b40e010725014450080382102c058030480c0d020f03010400001405040134108041000c049940745100c034210f8400302070748d15500010b64000c69205584c4c0e02e0254909140200700446603481c2c0311499000080e80b07145c80c83d2941a0828417100710320003042000c11090040358540700407a40a00480940f41080020100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 612538821 1250 612537571 612537619
    0x50a06171b150a1d0a031a0105090c120414030d060f09060317070c090912030b030d020d031e11090a0801020306011e0216060801080c18060603071e0207170c 69
    0x283c035882c04984481c0c813800250702d031600e03600180c2d0316440c2d02074a900b000304900c42560250004803208640e5140010781c0404900c5102c0c0c00a0102110383d01180c10022070300a0325420307416400a50b07841303a0490f2052001005140f2541c40154228800003034040b50354810001682d400c2241e04040c08116850565240d0081c80d080b40c0020003020006002d190358803d03d40030f04c2c458103010081d0282d081c00241035030040d02c2898403e0308070b001881152500042c44581050086c200400c00001c042200e0740817030051200f0640703035803c04030f11004e8200c103980201201c3d0350440e548074410351070741002800c0780030485e011800700b0341ca440d100b16203c90b00c0b0031071480a0610320480d000d04c40ac06041c40042502c940c8444045202c0d480144090002400b0300e10034501c0940750b41190506640c14016003400c0030741054083c500020100e54074034070036100403520311029503007541450302d0868001c0d61080244103204a103035078428581d0000178041100c90300d0140c0100032400c0c90a52800c010002d035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 612540071 1250 612538821 612538847
    0x100212040b1b070c0501030c02011506180801090c06110607081f0b0d0504031128020414010608090d1403040210030b0d050a05160506030406050a06171b150a 69
    0xb0300d00e440a003140720210b070001c085152190510f9802c082c0340c03c0c0098107032800400000d05590400e030b0360320001c0401c255a041102c0d0340340303012141c4850f040c03c00007549290b90011300046d400c00e0018002e00c07030042401c01c2260301c40e0b030b41d07801b4401038030b0411511601c2c16034400f40014140400b08107030b411942d18000008000c26200d00c081941c80c1c100034515442106650020b640307a03010401415000001400003c03020000380c041a031584c80c4480ca01400c1070700441c191100500b01d04190348859200d1120860842d02c000703640c1d40c41e5400581900c01c1128550102e200b010084880144184a600001194000104d045031255420000041003110001d020556515143c40c910f0b900d031890316a448c1c2c00b460140208200394200103041c80810b0004101c040c000308003c1009440e400101da52043e0050000290f5494149000c0c0c09010701d98410581d94000ca071407131030080c402051030040301000c0881520100f82d101d06100035a41d0031407030185440800c0c05840e100c41d0081030740310007078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 612541321 1250 612540071 612540091
    0x6011a04032915030d020619050c0904090309290301050f010309060c2609060c0c0109060c0e041a030607030209010306030f0311060f1003031209061409100212040b 72
    0x104041c04010a1403180844035003120f000e1010b103400450409105100080d4800e102500c61881c003200081d00010a510f141080981d8400c002440b500709035060b40c015100050091040c54030500780280500e00798000c0c13011841ca1010a05030050700a031503610b0907a160854141160300e00350401c25000a4550f000e41451b46802c250360001c1c0b031900c1503c650701c00036119a80798070301204107900d42c40c14000d0300c00100b942e1003041c094500d400141e260303840144001c030142c1d50f80e982c603e014054111800014076003410000c0c0c15046070703000400c0c4200c2c55000d82c1c0c20014035914911907106e003050303030140030b4041c0c00403c0410101c9102c0d8005040c4a4410b05002c2030746581c994500301d01400484042d00012121071a5a010034028400c0c079400c640340d00d1445049080510345101a40c40510001b41401064030341d49080c20351541021035120340116041040c440c2e5994048a40038084501600b240180c8a00500d610041c3c42940d0b0000000103410301d83e0355440d039803402601800350007c640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 612542571 1250 612541321 612541373
    0x4020901030e060c040815060306010e061f0207090f0207020a090f020903031606060f03030e0603071b110f031506040c0e12010c0e0906060304200604060203070506011a0403 76
    0x4110001c0201c1d500130410199102d81d59460400c850317040100b4040340610202280080c000180e41c0024101d054406403507840c07010392100301c0003840c1e5045044460040c0c40325012440211900481c4410466001c0312062220120784980f0740c04a10503040003e6101c401440148490b44082d031180410600e0405d00510f48000c2c4d100081c40c5400c00d8441c0661410703040406000c200103401018010082c111074003003240e00395074000d0005000d44000038000c04000c4001046244540c00900c8007403848000e40c0c074020201d003040480c0c03a020f1204640a84c012a003500c8203030400143c0d00080d0100441c40c00d6240e218841000003410b410040c10042100c02600410796964200c0803800d100c805a00000e411414a0000f404001849038100e02c10a844005c0100396200c3c441100d90142d4051150803060035032108244240901451468110102180204400d42c0000003454101e00500441c1e00503a40c40305186c40d03505007810301c01802a418803041000800000c0c00d40250f98084200300a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 612543821 1250 612542571 612542591
    0x6230403051507212306010c0f030507060606020a021906020c010309080d14090c0f090601050304030921031403010b07080c0705060d020301031401090c05151c02030609010618050402090103 83
    0x16901c403900d1200c0a145e9684900702019000704801c06620301c0001440003031803402000103002410844000b52002031410300440c10507100d1001c5409056004404000060f102c0100960711411140200d00a0708204030560364010003002c0541150000e0b80241441c019480c0114054840444100e810740b50501c003054480f020b500840404981c6450b00c1056460401c00c100c0c80d026102c403050380540d0500480a250741c43e80150079511400070b0170401d1780c80c0c4442c94103c44401c0e50307520000c0c11800001018001c6009255005140c900036900e807030202c0f59040340d12845120a01c00c0c1c0151034000c11000c0700090002001e003076807800c00c40c103449206a807600801c0444d40600c0c118821a54008014000c11403100d035000000b40558000300b0041c2225603403055801c0050041c40c1c4943d02032900c4a07091401c520840d040c0590407240c1c03500c6e003945c141188019410075103210780b0070f8903880004614148114500c0f101449540a01684c46142c8001e0100a5010802241c10107403542c140c1e030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 612545071 1250 612543821 612543857
    0x203010b0f1e0a15031b0507030203030408070f0f080a020d0e09012d09020703030e190b0a09060f09030221041824050411070209040b130c06230403051507 68
    0x400804c4a900c3c0400c51b0610104030140d6684440041300c10f0000c1800720328042076002082d80d50040e8800001541c610306400d0103400d201803204000c1035070b803901c00481e0800c80106c000d040d001c02c141d004c0321146807960700b041da01c01300a0b00c0082d070000764410041107410a100300c3c0640303107800c0350151f8040c0900e60503e072059445a4001244480d00003070900d080541c18410441112030213005045e125103c1c400c088061a0320040140c800300401002ca1002007040e03005400107580500100220340c103900560002d803662460940150058642c11701404c04c0e0400030720f0b03203c056a1180c5281c82d0501c501340521b892400d01041205035107030b42000780c1203100c918503c42101100c0202d4045817411041105640000c42d1904400b80248802001078483c8000c59030860b034480800207495480e00405102c03000c42d100050030400078031100190b0a90821a02403002c407151103406c20480030496110820310503444001d040340d0103107a98510700114490b206800c40818078001c3c003031031a1110700c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 612546321 1250 612545071 612545099
    0x21c09140f03040608071b1202010f022b060b030a0f0605220506010e1008060d021518030d05120907050901060228050c011209060207030305040203010b0f1e0a 70
    0x140d26030740009014004607810005c4070f0b9200c205031410f91030038081c42c1952070907032515020082c1407003200214949100e000390015801c007c00710004645030303440c0030344c00d185403800103910038285e105060864114040600416043d5000342400030300d95180e0b400620f0040080d1021071301c000b44c3d02d5801082c60b5541c0c1413816810490404103004100d81a4040402c485002c0d00050503c0303480f0124844548500c0d0040362541d04c0750a014500d075590310301064911040940c002e6001e804e9180e000b850a030408080c04606070201c0c11703454400070039024955107003040c03131682c004110140701400980000c80710382d40e803000c0d14009880d03c06903941c0105540040030713009100540c012001c484c114500c1243d10950031501e14500f50034505007070302c1d0181c4401f5104192410402d804044126589041d0800407045905c00b10840d592012810020014441134804910035401d116003099149000c0c0000361030303940000d026081c5592149407010450600601d03ca40000701c0100010700710341c041e199 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 612547571 1250 612546321 612546343
    0x270302060d0b011214071d0a08010207050709020f07060b120609030a0f080105060307081f03050a0b1e060f0f1c030807050315010c020a030501050a06030c0504021c0914 74
    0x410082c030200d00141085600c8180e010b105443d00c00c0e040080c03a07a40411030b0f0010340307d042c00e0450285003820a450a81e051603010b400500c44038000a100303005500a00c8058090f0055605103612050000164420144007050540051280c00c020a60039442100d810f90001c0c00f0401544150050310b06003001140c41d043c003500b0201e1400d0010b90000c49a144018440c6040f5055604010024100780005804a020044402c0000d81d5102e60710704a080b110b0741410441c0e5045559260096032a041c0306001c42d00703600719001003195000b030740d2041c3e07200d02c103c0000a0016580e44051114804c0030154655001c1c2104116081544606440000180103950a001c1c1c030500e608000d005100040d003414100202001080320011500030f064030342d4003007443c0c09074210002d8000206a841d080c0c0018229500c2c00c4184441c5490b160f000000b1a40705031029150705a445040100728081c4000400311840410344030f48c00c42c09550701c1030101600c14a004d20071042d02080030b5260081ca841 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 612548821 1250 612547571 612547597
    0x30507090f1a09041437150b190f08130b0702101a0f060307050a110a061b020d0504061d0607080a0207060215240a08011815020301030327030206 64
    0x8148202440c946c005409038003107440c0c0d02100510136842c400c80e400c40d610006100c2a98417980403003465096801e000003454001d131400c2e00c0c7d500c20854a0b00c1c0005048140e004a450070003117588080c09403403514800c0119030b0750441201510380b10201d0050004002c10210700400c050495050340500c200c00110000320041c4aa8a00c15010700c000e035001142014443d62003130081100ba00c0c1d01000721502041a803400c4010b01d44904601e51404510701c5005090b1428440f0344c1a64800590100e111054243d084403541d140b1103034250356034401c3d802160006504207036480442c80c8031029801c40ea0030090000c2d4070b17042aa13191002039800903181c18005070040441004059410414081c101c0c84107501210f0381e0034011540f072040c201310718041481040100014445c0e40e6032940910007852a078000b8007504103842c001c1140741d4a0020b08640e24401440c900c0d0344801c0f24800e40341a00d40c903880c0d4141004140d035127080e03250022212500c02c0b80b001803012005881d81d501416281071089 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 612550071 1250 612548821 612548861
    0x9061d03120a080f01051c05240717010e0a020a02070305030d0207150e0a0611070209011401090806150d0507081506040501050f0a05040e011d0706030507090f1a0904 73
    0x16001405041c004d4480250780a00d80c0060006680d4040030344484850081010604021850003d041c80c5c00c04000c1d4101c06500c0d144916400c0c2c40c0f000e040d2081d001d0395550124420310b50301d41e00b0301306020b0040d40d51602c04c3d240010701d025202d6008000e200b01c86c1c0100c0c1c4001b640e99130b48030325540c03101c0d4580c015580c010403028104905480304d0804609a500280500380d0280b008640d2166515400f0b4441c6448074405030400b80b8039412160100d40140031340c4d40315a101c5d40e0342096081120103c50006107850400100040f020494500850011003485c0f003180038902007041030400400155168090b944000500400c1002603c80c1a070702c2c1c0810b80301072f140840070081100c005910041c001e80c0761000e1903031141c3d03d90b00c24801751401250f0000710303241400011030060400320a008011180210742c2803803907200250a408481d0a95010301c461340d9903490440302c00c0040d118404840340c85810500114240d00840001e283d890075009041c000328000082c19900703244029840d580d514 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 612551321 1250 612550071 612550087
    0x402132d050607080901030f11030907060219020315041a01091e0b0315070915210c2a0b010b071403040b07020111010b031f0b0901050109061d0312 65
    0x946a55801804102d455905201c00d03034a40c61907a21a034201c69040503590328400380b510680780d000d0741c800c0c1c1d10550030607141d2915840c000d50341c0c4a140914005031042d0f0140e408600c000c90841c9603001da0140141007220b0654105403403010000d1700031502490f035507260219146d40e00f59005e000301103182d40441c2c0b20006608810417045e20041c0d0703103160390810b50f28103000e88000500030f1100c4a170703008a00e031503035900c10100c2d0036a06503000303084a03059810080d14410b80c0940f95034152071103507540c003038211068113812007103840c1841550081002c100d00040004120044c801d0018480300e030f000d441071075a40c0d6000007008240c00004c010340000c2801c90501110b1650340c0754450481004510b4141020f200c40058050203800034100910082071602080080d044080c20030070150480e10300c03501d03000c1400d44d002c5142908951603490188015018600004964104c0d030041e11a940d00c641415012640c14032101c0280002050341003204a00781c504000c280b96500001044075220840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 612552571 1250 612551321 612551399
    0xa09171c0914060705310303080a0b100203070303060e060d0f060216120806010c05061803040515040501110102070c03080702040b0907090512010b1f021009240903020c040213 77
    0x1e4441e556079002212080a0000806c922000070b4036003500b00b40095548100f2004040e228845010742c000d28280e02c10032110341c000019050f000c0c46624107001c41522822440662041202c0d55544280d140141c900400d40111a0401d810b00498016240030f00d000e9240000707004101080302c4c07212045204640e40c2e41d1080f00a50402d1092800b080a241a40c0301d03182d4500d400b5001c124202c00c8482c1204058600700200d03402000082d0041c58450041c000900710f42d001403050343c0c08a4113504201c0c1c100401813084501d216804104090078a00319264541d09400010040b1303041951161002400c0d40c454003c2c0e0f218040356965600c4050400c02480b040443c07200c601182caa040c019405055038400f4622031a149201d0600c070051124180d04a207051383c070301c41c1c3c10a071034a058442c00034066031111080c00e40c2071820700301105031905100c0c03004882000a01400617003012010640a2034641c0041c0f4000c4001410301550f2a10f41d4004044e95041807a541c500c1c0800d00459603002d21 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 612553821 1250 612552571 612552607
    0x703060f1404031404050909010203010e0601020d050304060504151a040f090c14060f03010b04050307060504080d0e0f03032703010c090b0c12030a09171c0914060705 73
    0x1064090042010a107209010008090001000d2200a4850f80b40012040090b540100402000521541000c0034614001d50081c000e0791017441b842c00000b0469400001c1003107142d038540c0e68640ca10380e01c9444910080102074000c83c0e400052440755040086940182c0c480c0442500c00003e1122100040200300d640010000f42c4440c20031480c400403e6405540d40101c1c3c0c4190160001c00b9102400070f40c40b0b1245280e100111540480041034008681d00030308203803039043e003c84180c0350f2a254103a82c180030324843d01205034040c07200490740700e100303405400000344040e000c0024010b410002a042d50007001d071400d191000400d5410305100480d010151042003900204440c52040350010801c440e10301a5212841c000250301c8102c0004001c043c2e0544161075000391a8146202c0010285c080c60a040e181051180d50f40340c0890400400c9803c5a8020001c405000300c1d55130350f000280c28001c0c401e60b40011600ca1600710f203041030112620480d00359442c55900c5007000251030780c0c04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 612555071 1250 612553821 612553841
    0xe062202090a2615090304090209030f2433030f06070e090f0601080105060a0c0c0e071d300307061d0a0206030601032f0a030b151e040b0c070306 64
    0x8444d510030311a140401200700c034140d0f5100c040140c0e41d4518078000c44d01d010007500c091031092051054840400790210740c126140c4c80d000f034030200a81c44258100b0041c1466070104007004107032982ca144d40030050600c03442090b0300581914405002c81c0c03440b070b080001c103c3e229400301e8140c40c160141c52520704103555001900502820960030720400003401e80c001401028000c0c00c00049440b003483c080d000c000c0d94582d201c0006558603445079083c0d581c010003550584041401c01e502e158000704186020300d000c2c5400382c0b1400442d20400c588229250018038020300b0081c4080007058843d130148014160907010b03100208002c045551460b00e0414110f01030610394006803020001682c4c0c0d8000c42e43c10090920340441c01c43d42c11500e448044810140c8000005130544a2030400c00c89440075091714007981d18104042d002e00020302c076000038000100c210040082040b030241c80c130311415400070310400150450806495210348001130f44524150161035100400820820001d8001c08001c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 612556321 1250 612555071 612555103
    0xd11030c0a030503040911041e210203060c0306010c0503040f080f07060e150f180f040647070213060e0a1a13060e062202090a26 57
    0x5032035911456100d00a40c001c5074001a01e41c040e01c405e402c0c1c02d8041d18003070040200300c0141c010203c005c000a010861040c4054401d04001102180c100c100c10302d042b068003d00501542d0742c54546007003450740020044e0707060241210b00d04000c034800f00080e1020f0188011a40e1510341410081e92a213110841d0104856200000a00c081e513880480e030382c031f60281a24801410403d501044049018400c98801c42d8000408e81052440c0750012568244900360303100040312550100b48401d40d00c0c10f0081144040041c0010300c420030b41c0b8200340505010b0342184024000d40c20340e4076002c00c600c0300030030540d040d0081030890640c6010440081000784500007000540d00d8509440c41664004040c001e55a9542d6a82d4a440d12000b02607d54480e00070054481d65404600c00e400a2480c2d02414000b80344010003d00682804022202200180080244012030008104002c0e5202c2264250000300b0f0070070006a1003a0b9054041e5409005407112480d913048034200e41c68080c00740e80b44120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 612557571 1250 612556321 612556339
    0x80105010303050d0506040209090906060111060108071a0403020a180c020601060c24050712050c0f070b04030c0f030306170601062a0c0806060102100b060a0309050c0d11030c 77
    0x250400100c0c1c2c4c40948803440410266214000180280070341005250403d240004105441e000403400300d105910907200c2c1890403244a885590340d031024021034510303602005050000d45154a400c030902602c0c2d18140346026102e40c045100d580d031302e500c65980180d51034a01e0380314141e503001e6003142c042a480101072030362604400078400515214043c2c00700c04862640c6410203006c085002d000d0124020078403442c20000da0040010032007440f00c90504e860a000301d0010058241154000c1540100341c508001d21030711910b4082c02e0141c000c406108200c006080002c401c0950310b064103000380c8000512030b02d043c201c103140d85071444508400e6000b007001800040c0d0820803001650f14501c41d45d555803116019442d00c00542e5170009414003510a00c0090b2480c400162240305103030030b80c00d8401e83c1d903070325600b80281c1d0000d0740a01c2e0300110900042e10040d200390711600e000c5000b07808503008000c00d800480c00b6107020020075510340802c166503ca10307040c10081e0310545d03035065a210038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 612558821 1250 612557571 612557573
    0xa02060c090a0501120f0c05030613090b0403030b06070b0c131d0103082b02040f120b2206090609060606020a020a2603040e0426120901020f0a090509010801050103 72
    0x3220b105015241c10f2021400c500000e11156030703c2490701c284424402c002d568440100640030740c104071366031886104072080495403004036001c0d00e000c00d540a00e8000843d1903d80e02600503202401c1110f820050510a00c0d01041d00f10341203a003d80000842c240ea40d800c042c06020709400ca540001084080603440001ca0441c0c0c161001e04507904100c10fa6140c0c001180c5070500c10710564603414514102d40040d99020301154000e10807240e040803456072a543d200241c1041c4442d409020f810050307040d00250035206030b10341c0310740c04a2054040c0020b10040e580c40c08104c500d084403e41e007041c0c2c0d404804d410032803188221009400c250004102e540039070350028003021f00c240074503181e40340c000c1c2c031000e4510b002d1090300071100040d8058030344072031701c2d07500c800403500c030446003030314400c541c40d01d00e05003000048134117402c80d007411220310302c1c08c040c00150f64515440130304822880d65017045140721407240d990203894402020769a421844d0b241c401003111060701a08007060076498280100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 612560071 1250 612558821 612558829
    0x703030903030905120c09071101060e10080c0d030e13090609172a0f1f05150a090915020d0c080121170c070902040e0a060b030606090f04110a02060c09 67
    0x161a1b22084804190a0b038502008483c41c0c120004002525800c28102080c4251840c000500c600711038082d51501540e6070034041d5844a01d40409604006681ba125000c24402c0da4240c0c0002005491900170000002c0d1820440d00e4101041d204682d03584c0000e0104900001402c442038108040030707003420410118ac001d0b1815082240c81d0004542e0045005100180711902008079002c040d1400d242d5035500100001000c1e000c458150f038a40400a01e244600410031000400082d12050101d03051190050007442172030400d568200250038042d4081406000820f048510010081024001401c018120204c1a0842e0841c0302c00c04244110741c03014240030f41c141a0304074030f1101d201c2e2088440b80b2054461980035130442d0160403408104040d0507001042103030424528a0300c1590384180c02c0c81140c11500401c59070180070404078a25260917030107881007000050507207181c0301040002404940380343e41c1182e000c44010448a1807590140700551b8042102c100f580c0c0b600b02408001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 612561321 1250 612560071 612560083
    0x201110a0302030a1101060905010803031006030e120a0201020c0106080d030b0102031c020a05041a130b120703110d02120108010c170415182006041a0a11070303090303090512 77
    0x8441017000310b00d50418400002d400240c000c21801c001005907507100e10805849900c220b41000f2404001007000038410311038810101420180009040030000041030725555501c00d0780510119034080c824642620000e110b40740042c5212001441c1070b0316100c1000d41501c901030703281c5055410501010010345031760a5811641c040380c010060380c0e813000300c01c1170b03919001d150003d10040d60074003801a44c80342190b005010380720054400c8420b42d580c5001080781c80c811141081007a40410000c03e90395400b17908200e01008154041504048620242504a800c20443c1002e040541001004950000c0c030801410201500d048810b072000c0021054032128094002041296a00303c08101e05000d54807010840400038031320b02130090344c0d08254580c6a14900d44481c01c000c00451124a440d15a080b0382c210b0b0082101205509000280301426400603191031082c4118038a0481d02c400c001c0c48403501441c071903203400c1d50180c05c50500804202403078018038014501c4020390000704a0000d54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 612562571 1250 612561321 612561337
    0x90809121509030418090503210603160513050603190309030c080c01052b090f060b01030c0e090912031801111608030402040e0d110c03070302220204031b030201110a030203 76
    0xb04406d500da1404078a50311481444104100190840d01034400000500318090301040702190861141c026130072002c000b086c40340c02c8d80050071101401c0e410b40b1507044684d02c00c00c01030545035a04a407030f00641d40e0701240f40741140065840b038018810018035142010160044800a250301150200041c2040c170444000104d5103038240c040c6ea01e01041d400860b004900080002d20611400d8034010701c901500355422680305040800c1e070341642d4464441c0d10007090160b43c070b603850b00031014180580400d000d88510414080c0c0c06d0840f4481180500450181c0819001c0e0503c62030301c103c4450840b50000c2c6141303071003103007044200720051a0750202c507603207500040202d54a490700e1001400411001400c940a40a0310110001e050341040100b00014289000d485400031545c042545660302800000e500007544242c4440724407201000b481e17041c0e80c1550040c40e2a8a0740c036000007510385403040940c2c012500301c061085581c07000800345104000760082c03101d0a15640c000e5200c0c061030304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 612563821 1250 612562571 612562619
    0xa0e040609060c0e0a085a0f060f15060702040c0906110c01021b01030213030c0602190f0b190212040215030f0c0a03060b0c010204060e0a030c05040908091215090304 73
    0x5610940980c4004100300b80c01e00701c1c0d22901080b210300340b87c25000b5001030002c054054990061302c01c1001040e458400e602041200700c0c5035035040c4186215110303104c040d81d0091402d00120f00181c031395115921590f91651100e2040b01c1c90b01c2d40040c04c4000d0600d00310b24541120181055507600001d80401151940c0d400c001c256400d403004070001e004d40398001c0c89a566280c0c00005000e0000d2048082c4c62140e420f59803158aa10164192503003d46001080022025106e0300404c80000a0030741040c03003803080001524004001500366005140e180c080801d185081c00b04614100d6031b042d4001010921701c900710301c1c1c49940401072801c014103000d103080740002c00d010003600c01c1d0302c8440034000410b6400c0d121040c01030710034000d4000d8003403100401d030070310214040e5180c182203502c02c807a400f80d108403083d401d000070b2002820320300b0381c02c8444a100b8811515a59507146903042c0c404071032001011881c00c24030400c46c3c20b060180100645030010001403100e1600030511000154542e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 612565071 1250 612563821 612563893
    0x3060315020327030904021b0303042102120915070209010b0408010605010f0806120f01021c0b120607050706110a11060a0b011b0804090e060a0c030b0a0e040609060c0e0a08 76
    0xca140103d0b102d401501c40507408000304100400100e2492009041d052078071070cc080280c48802079903254442c007600c4061800a1007110014500415000c036050b0f001c81c0c41030b04080c2d9030390104500040a03000b0701b000c4030b000300d028010700000748600002003d092800841c604c020300f034040d010850107007070240200b1032140500a180f10402c140107403100240e00855907136844c1021040c0800890000640d03843c10301132900d490f40b520691035100d556815000d4205915950f0040c0c840342e2110604032421925070300f00d10340905400000c0c107207400a0341c44195450300d10b1148141440b2000302000c000d18a4165112207036680701c1c0d0300081140304103400c100c50f28200e052210480c080c9900080701d0304d04142c41e0441040c0c0100d11507010704a03154090100340f000b48026002c2d500c54488064012685c40c0082101412000c03407950400e008800000300e4003032a0300e440d000d0341c020094400200382811078510282c1440c01000c0010107130800608103110405c0e2040d403d5108000344160900c10350 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 612566321 1250 612565071 612565087
    0x2071a09071e080613030206072a03030203010905130c090e0f0303100611150c0906120a150905010b0d020c15070207050907050c0604030f0306031502032703090402 72
    0x100015005008022550880e81001c0c95000a10202c6401070508038014000416000c694001c0080245075154020344603079944c000080301c8401421031440c2c0c1c100f0400301003208a60035100302860407070083d0783c05031366503041c610780009982000d011640c5904603480a6404600428441ca054881034100032541000d200b0800d440d14001ca107040000380000820f100d503018511780ca0300110307070440d2a041810744200d07861603140d010620320392640269000c00911110000303402003541c18402030203e805c00d0031244000d454190200e4800806666808400609542d0030300080002c141d0203109100ba5810001c1524450140c01c0121002c0c0d500407540c0015047c05101300600c0040d0010301401a24001400070350b26801c0e482200e0151594a012490081c485d0089504400440c0028415a11256000c41d00290348612040c1095522701d0b022000554070400c440c0280d005410241e100d041c02c0302c0a401400050400c1643c0c280000b400d142c1700c10020080e00d8290300c048400613114062 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 612567571 1250 612566321 612566323
    0x50f04020307090e121c060b030702060406090c0b1308010f0915270804060f030515150c01020409020d060602030705060c0d0b090408121506071410062702071a09 71
    0xa0710400b50880201007450007094002d0782041c0c11b0718602c0002848802e580c1d01e0203805621045d2070384001604003000080c04a0981c0d046102d01e1031141c04a454025502e50b03d400c1c642d04818140c900600d201c0c070080105000c01d0007002d01442d41c00c4004c2100d001c0c1d0f50f803800b103c001009440300d64907486038961001200c20307060000004005241114241c1358034584500030764840c0c025440861300c1d244c40c0c0d50075984a40f0510788508601f03544c814684400000700501400696900075503104104404803030040300780040e01c001c004401c005615104000000d074151240340c2c000341e08660080c0310740170100c0c5001032100e801034045403400c1d0380c0f00a0414840007501c5a12131003078004000721700b070200700400341d00203080c1840c004024100640f55105400b43d00303000c000c07100b640800300b40090030218002e12660b150b00506001120501d0880d10111340580b005644080a450b1100322842010170b062a421820300d02aa40304510b0700840c2d0796140c0300302201130124001380344d0a8001900e0784138 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 612568821 1250 612567571 612567583
    0x9190c09080d08250203250f080717041401020705030d170403020a0b042012100b04150f0e010b1e090f1521090a12020a24050f04020307090e 62
    0xc6412a54507810074480000781d41d903440071110701c098059147c18000341800b800b04c0c20b9021544440002c01920345a1030318007440d00098415036010000100c9030480c0610140208010b102200c09030900031003140000e42403a1032940850300a4103c89040240694051855101e40385202e11b40c148680340c40c2001c034548541100c0c01445004040180006e221559000d42d0000b2059131001c039400310301e03001b80301001c0e40603000700030540c0c0180107070081d0900d540c100e0f24490074050030004800c00c1d0005015503c03a25a40212020070100a007840f400c10440c408034050b12019030502d2070114400b0119001654035001c0008120300403c0c00c010301d070b031105105c0380e8442008100d0b5224401040060f1020b500c6000c800e0840811840c0501080e003010501074414020f03600607029039190fa032035202e645600941980300f140039080200300002c0f410450001c0c00140350003403000500448099504032000a401c1c203001000d000100f00050358001020415588005404a58cc60f00c0d0024140b03808 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 612570071 1250 612568821 612568861
    0x90e19170d0606080a0b040e0a03030507051c06140118360c18120b100f17070515160c0b0c030705010b0a0308190203040509190c09080d08 61
    0x906240002640e21341c040211030003010f0250042000b568140f0030002241c050150900b1150030030842c2d480400d0095020b0350b1702650600f03001d454040405036420f15a5201c40807030f2622070b0f1304c2c4001d02c8902483c2180c000d41da4002e0900d05a5050780c64840c8107040c6003481814459000b42070100250101d2445900c00c000a030551611210b2600e000d010142c125400f000d0005018180440104141c500c407290032030b14420120307007000d0207a480d1b48a405600425101038070001c0341c0005030003504052400010010224005803440c0100903040c00c014803641f02c680315a0a0f41010110310b44208110398480010151344038a251a40c81c02d02c61f100502e511204558a003c0b8120151b42c202000070034480b80b260008220705100b81c0f041002c0075a0500010b000c600c000d1212402034071043e00311820315201c41c01141c1c02c050740c6400084003100c0450301881e0b68111244242c6211002c4e0140000703001e81402c0424000781040416983c40703509410b22010000d0910120f40407100c0080480710b05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 612571321 1250 612570071 612570097
    0x2030714061603030c11060c0a0509120604050307060608060c0409050601030902032e020a08130c090501061119110d140d050a08011401020c040509150907090e1917 72
    0x10340300b5418050000c281d04c0b555500484c1810700100380c5168003144161103001c4010001d4106240601c0460712074002102964001c81c00c41030304140008200300c8184220300c124000d541c0d410452a05209540d00340d0321860069000c2401c0c0715580001d00151020781d496481e0000346030f651040101d024103030510000e501401284c4401e540c0311501e18440c10700710a4074082c2c514807042c048680b07049210303c11140c8005000b007000f02c0c2184442212026086000714002e8455549858030340341140c8003a440403000c00d004020499612009104a4107030702103000700c01031800d5851701d5040e8030b0008104902d1180342c141e04020104105480181d68907081c00b42110018020080040c180b48c2c001484200400c402200010321003000242030108020180d01070000c102003441880b000e0140a0701035a554015030740ca070805032030880180c40c0300d00c08000060080514000ca810b027162510b100303407801c1d5000200180c1039001032408400480c0d600c1111003040e240403071f1b1802810b0040328140026 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 612572571 1250 612571321 612571357
    0x2070302062208060a0c050c120a2105150f03151f030b041b03050c3706140403020d0f0302030403050a0f1b0303080a0e03190306140d0203071406 64
    0x10fa4030f0004109101d051407030b00410038204620816a16801001408074242e0301c254002800742c140780000c1d1005554505100d10607207442c141b21408003411042d60329905030344404004088030408061804148191600c403264501c040c0480e442c1c900d07043c400c5840c6616100803a00c04003442c1d140806008103507807030200f4142c40303181c80a007200090b10300303881c03800c8060044c40034a03404418100032294440010011504603100380721400b5500007442c0108c04003000c64000507600c40c0e43c0000580c0065a01146103402d007180980801c07035820351007080c40c070103020038401621481072402d001608400301c4100e2151903c0d0480c95407166400060441c000c05482008010501004584007445030303da0320b890010078880403144044d980301c05400100000301040519001d0343c0070105580307076403046c1d900e40341d21405002e540e040d2147e00c15000a03a00da0040110480c0b0307910b19892001e041307411241100160b0000f03030761041180200502c5168450406c407031075960348100c8209541c0c58101d140c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 612573821 1250 612572571 612572579
    0x11120120390a0308041401050c1204020307051002060a0e1908070203101d151b03060f09010f031709010507080a2d021009031b0201020c21070f06020703020622 70
    0x3001000e4808951500d41000d0501c06d400041c0186031268003501030b42e0317061400e100310030700b06428082e0050380c05024018010413141c80c2c81481032444601c940040c60075040c48140340c011141031074000e2000d40c000f85600e1088104103900100520f0700400b44d152070f0034090000a06010602c18a610b99900d85121810043d514000c2c460074240d660080d180da08840110302400f1a604503100ca02541d100504158140c0342c0c00041d40d004000613004c41500128031000c00c040741c600382c000407545d0f50110030800c20845080466002c8140007800541071401800000e4401e00965800a08514000c070f2805401e91007021200c048502a0b10341300c0c6209142c01c0c501202e0884120450014003c0c90002d5400036030030701414603e11740c555a5002c0c225170209601c00308501c0680b0890444c01011251102990399244904402040c1c2e005c2c0304d0089040414903191901e80c0c4c7c031000c0d606222100c1001103e40101d4240c0c00c8980585e0810b035941c03a040d0007480c41141340b01d40114015030a110100f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 612575071 1250 612573821 612573827
    0xb150d1409160801050f06120a1403180103060302240c120a0305010b0307081503030403051e150405030301030803060d060207110405070518040911120120390a03 71
    0x22003000d0b16030114600310f521441d03000d0989404842d00e240c3d41c6800fa0110318242892905280303004080d105584181245a56403035504a9036081c5580c2940701044040600b03000e0074281e545044242800c0000d189582d0124134108800500c01003000c02e62000b0340e4070000303010100c5003070182c4030064685504d0700c0307004c0c0e44994115621000000303280c4000400d01013844001c0ba0b004910701c0d180d00081b681d941d0482d4411080462b5596018001407200000280c0204030405032040e55989000b035038207d89000619107100701c800380420000260906c00440e00c080301701ca05503504510312b0741d501d0303440401085403248022001003141d0710000b00c0e082400a03085044030032450458040c46a070729560001c03034241c00303000141c82d201140450600094a02544048030b12881040409004501140015201071580c04030b041680d445000750703070209408034201c0328000c143d840c445041803206400d5003800c442c02d40c03c90f80340c07a8600c00038141c1c1c880ca02401019007010030301252a244d060b4a401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 612576321 1250 612575071 612575083
    0xa021c02030a1a01090606050315060f3001061b02010201110a0305070314070e0d0f0b040c03110103021216020a0506070909050105030a020f01121503080315040b150d1409 75
    0xf02c102e0048100041200c4510740500411107805549403401c680f0389010700c020b16416441da07158040e4040201d03c1c00240307160040c0c001880031600e58032201820016401c05c409261a444564011401c0140b0040b5044540080711805800500c210300c540c1e0300c0142c1c010441c0d01c9200310928000706901605987c5504440d114180c80e5405106104081c2c151070700e407420030348100020a10304180c004840c20310064a21429024200351b1100c0e0703105440c0c0b08007004043c0c60175100383c140c50308144240f00d12402100002c100a2034210f01e0980a02992a132800c00540080c0c014259281c0d107101c060b2080200301e4080c1c0e00407050b510039040000740504010381610602e80200d0408000050503e408281845000c2c0c02810a18407110000011240032001360303904500240c0d02e02c984500c038a00f010401001d14407500c1d40e15070302e0800d0071030802c1c4207028065041c4203030700703118541c95151514076014218407091a001c2d07480b051155400405450340ea01030040d0100e4207000c000380d0203000503003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 612577571 1250 612576321 612576353
    0x80705121803010b09070807230c070305070b04060921020411031e01030c030b0601110d020105011a030405070306051b0d050f10030b011401031103070903021905030a021c02030a 78
    0x2040f0951408017807003c0803008689003408201c1903c0010300c15801440f918030380310509003c0320a9024110700c0700180d074120403c410415880b0600510800c242040b403036024180034440142401e01d003103070003000304003075001c3e40b41881080c0c07904000d50440f001c1c01e040c0013940200f040c440c003a10032405c02c043e070b00212000c40a006034600b114401104010310746041e40d4000c0e140312846130440e2140007110402811541c10000344000c20a42c1901c18884031030524860b50001c80e55500d44044c0c844505414103a40e5241141042480f00090000550004587e84402d0228042c0e41354a082c84103c182044102103403d800254200500c0203507002c0352241e20301104440385a150055203d5640a15000040c1880c011600500508c2c610040c040c1030450149000318818031004444400b5800548460020800050081c411481c10404d07a4002144076005801c040e8901400207980d90700342e040203070094500700204554003000e444440320554011303048540b1159580782140d403071490005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 612578821 1250 612577571 612577573
    0x60f051504060b1c0e0c09070f030605010306060e0f040609020705030304051504200f060a02030a030e0c060706230106090617060f0108130b0c0903100b0d080705121803 74
    0x2040d118140829103941079004c00862074860010101e8500421440038224028401ca44a942440d5a5919518410303101e550b184004038407400380240684079160131540c18541402c1052020310351203400592900400c45081d45e007000c520000c1001460326411000740b160000400c00c09112000000b0340c080ca22400441e1092001c003404000300365001d4400030a026816001c44680c642c41da0f050307135102d40b0024050583c00117203400041d655800300504038050382003c55080380003600361042d00c034444080006820014000400140603204110001744029034a000ba007948580c030305001502d186101642d010196111000a40f44640c1c40c0300d40c90005800d20b4a00f0b102584241030f26010700006000190405920001514185d60080511080024900c909008620000c0d50030340a030380e944468603a501d1031002414205411041641c24860900b81c00001075103030056030011040c0c1110034541c0b5030100e032500d181406c46822030715004100c0032a0310200410540100510184210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 612580071 1250 612578821 612578831
    0x10315081b010e0301090f080f0c1005012102010f12060302130203190b0612250809100915150b030708010f1202090718080601180c09120f060f051504 66
    0x150800d0300341c0f546c28900070404c03c100801d0074000383e4001c0140804c40500200d181c105180c03441803a24160b00040241031050310742c0010484044040d0030118135054440ca42c40c0103060a4002034141040034000070108440912000030280300da40c4141d0195071b004044510152000600703002940055440040f5521a0b10000080602c14030071000004009807101e800c000495030b143c441c0400c0144507441402000701c07400d071501c408410858400c2c0c215211038901c0d04101083c03515100c1b1a018404200d45040c001c400072a0300d880f101e0381040075001c03012440713070360b40c8503501600000c41d4840103184c40c0200074405519040500c0a05032050720b05500d114a58981c0c4445c00380e00381c200080d400002c0c0c1000704034904e00c40c00300100002d41001714910380c0740d9502096494060700b41c0c01100d003502c001403154070441c030354000c20180558510708124004d0a200d5400341103208214014004284842d411040160703503000011034100c000801c218070710309810300110354500008a944100c2c645 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 612581321 1250 612580071 612580097
    0x315050703050603030403050d0c030509060d0501080105060111070924230a12030c02060c0d0507060507092102010c230c01030203130b090118030215010609050906010315081b01 78
    0x5446c100e070340010090644150604095599980400c01030b410014100203005071030f100c0307000502c16000c000400058a603d0304020a08640c00a02007904101c0c01c3c0720403440840303001a40a00340e841c1c2500004405526222022580080045001d0407401040000a4041e01000c0c40306445405019032025080450b00700585031440340180c010218200031201c0100c1e210b48440441d992000d08034500d048288071409141040086050000610004942c800c000040c0030345600640c0ca0b05048105600300312106111b6501100084010105c01040b40f003560300c00d0f090300c4085a0046054020842400301540381011102204101c0e4821245809a03d5109100b00d0344075003541d141c0000a030000b0b540c1c0e29650131002c1c020004540d2110700d49085030078182410440c41d407198008040c11141000310180c0e20f14164000300a00107010340802003900c0b28801a0303801002440c0000740c00030344541c10558014142c00c00c00322132003910f0070600c200000681284045109880310120011b003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 612582571 1250 612581321 612581323
    0x80a030b011e030c03060f0f0f0902030c090607060207021906170705030114010e12060f012117070b09030a020f0f0304031403070b0a090c0e1b030603070315050703050603 75
    0x400c450842c07000075031025440b460f0311a91040c1201032051401054069030f13085000c3c0d000303109400035449108540c50822054104131140e0004220908042d81107280c20701c0047c110b800780c0d00c0760b6405444006240e0341001a164100c0b40d01720380c02840210801420040000180a00c3c021500802c00c415151201001e00d80d8446108641c0c03650342c1451a802c2030401c1803040242c034452410f0003654408003100d50b940c2040e4680c1d8001100c000c0550345031110104226090680c00400b81503070034516140c426072a0ba07070050713440c0d400c445051040c260790b60b107581d1035101e60140034100d103102d001404114031021009043e80881b990031190b03080c452341100e5850b0320070045e14101c10382c4200030400c006440c0c119540f45410b403031002e407401c0c0a101d80301c042c1c401d50105c0c3c82c500115234810002081004c592824405401d00902108107031400755480d501c0700c482068000f00b42d2001000240c01e03075030208009005164840b412a04200b244440103014101c10b0f128400400c0c2000c00146c0d01b410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 612583821 1250 612582571 612582587
    0x1a010b0910110f030d140106110d0507021201140103231b040608100b040606080405060609332b120e091513061a0309010216080a030b01 60
    0x80010301d20109212100000c1d103a000b02004100800e0103601089510b071203061001e0980018000800b00301c812000c101d4001081c0160050020b101d00d19401c06000342d000105181c1c956058100a07656800034000201c41c040701d208807801540c2030481d00150b101d07200a03e01d040324880c3d1400c54080704008120319640340c017285914980d0344200c100110b41603000385501c100480240000a44546038027080d41490184454a10416203440d0783c2707075050401d17102d280300400ba14a00000c4505040e034980d43c641c00058034103881021828007242c0301000300d548584103c0700d508003c0d500e000e0002c05000340e4215034000d051080384040c252031040c58009040900007240d1002d8804044410f43c0d50045020b4101c00038001c00c00043c0080e50a921420703080c0c6d02488000e00480d2410001c6410071a024544000d403091150403c0e500f001802c940e51203101c2288000e00310692243d6480e100b81e4020701554910b203035240141140d01c6e00f8048950001c007079052460350705024541c40300c0c00569801d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 612585071 1250 612583821 612583837
    0x11b06090210030e0a0308060d020a120b2d1b030a061d0717090a1704080f010c051c0e15040b07050c0309012f1c0315090b060f04031a010b 61
    0x60041c844170000207116614465110400a0150156040b19004218036810716002a02c604020080103400d100c070b0503001a60040f2075201c0704c424400c200704020700d0f51903500c03240c01c00c003c0540c02284000c0e800f03041d100340c1c0c0300341a90015180c2c6006021580640300d02d00c42c1c98041c0f10690808141c400400d010b0b588a6009a2280c0c50326901a4084020400004040c0084c0c4d01a10800c0000100200f2040c4480c0301d541c9900350320340d418401035034107124079010322010a80c941445e000a60360802c0079203d002c68229001400c0510050a000c041c02ea0003091480724061070b10003002d004618449940264082c000b40c40f03243c0c0d210b140950300c4c0d100d18060806140e0042c80f40c1c100c5503104d0003103002c1d54050440580e41c021407480c24601c10202060726802540c011340d0001c0742d54070003203200c0919925540381c14071050508000d1110210769902501c94045c2d1100520811901d4040c100d8446d00041c4294660340e903035904184a803c0c1e00042d074150089029400042c2c83c000800680780a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 612586321 1250 612585071 612585073
    0xa0503031809040c210201030c050309210c030d060303090e0106020c06070f1505070e1e2e0c030e0405190c0207050607080c060603030f0f09011b06090210030e 70
    0x1004851400100100c1345141c25200c041003800c4004c0070401c00307517002c501c0605402050700c005029684c4442c089020480240108003a81600180c10080c514031201002001003059114215030302c12070355081c04521000031404480d000b42d90080d42124080c2e0340c0e03050302c19110009545000d0303081c825640141d0100b00d64409500e05a002849400c0c13103192000c004881d1355541701c14003101c15400a41640d960003c001407513070460308030124180c0443e10500704c1c1e0700103d42d100303c606103c0040c90041c0d40b040030000300c05048516100c400d80505420702c00038100070000401500312542c044000400042e402280d609103805003034061810481070550340d034840c181210042200d4810002184100300e0001140d4032004020008030b070184013031343d5a4440c0c450350075141000107031540b80264010480440102c0042055a5004015001144e601c1d112440100e40300151400c403a03036030880d52200e2104012499105000c40b40c803d841d82e51a61f14030a10075412514034502124503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 612587571 1250 612586321 612586357
    0x30108070b0f09090103031d03010b0607030522080327090604092d1e020607030f020a0c0e09061006050417101a030712020105040909080d0504060b0a050303 69
    0x640001d0300e003481110421900702001440000c1031035134280d2084d000706036080808160501e200c07641560900d0b09078004e0052707089210101d60940b044000180404c01c010800301045140e400092035020030f40100400c0c50340d152252680c803640700820f0408001c0803c5915055401c0640c0341c0c0b6041000100003607030f1a03481105100c050100701000b203902110020740d400000308a40914984201070039102c00900b4032510f81a0600850a0840c0c40b003104080d098000580d10380c2d0842d2041c9906140883d030700c0140d140241d01d0141c1c40400142601c0703144101203114146050700500c9044403004980b180d0f11065900b02c0452460f00840d000103804200600074647d07800d1382c9103201c6c1400c0c1c003180d400d48518404442201c003c0403440c01030f002c6403132120310390f40b80401038400a80712001d00001410300390390010b001071180788910039040307807204800414040b0306019140e2a0348601418030403132420b0701d0075400078500015003901c0b4000c22080458542400400c1d2543c003440702d409004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 612588821 1250 612587571 612587579
    0x13021902330f07030e06090f0c090907030f05031c023106031a03030708070203070b160b04030c0501020304051516090b0d1d03130b030f04061a0301090308041703010807 74
    0x682c4a40c0180780034141074840740402d94140d420050944140d1801000d0040c10403558906403c000840036194851f80850040c0114180302180380301c1100ea0141c1040354405035480d000d410360081848082d035005140d11103031040042030300104040e82c6120044a2049a42200715414113003004c2e104e90070040c05003007440554000e030700c0104c84150b05205056844088400245503512030001160343e0040400c4103403c500b82040f0100240000b001104d040144003e02d1021840300214054028100d900101d0b007454003800109a407180c000000f03650700e140c1401c1083e946e100404403461207048205c006400c1e2080014031a02071145070381e902c22207a2902500010f25000b8401c800041c0351b44d41c20030003850900c0014101c035040c03014003568882c0003186695890b40c0d807e41c003103030340c903041003007003240c0311100500603680701e0f5018500040c50511140084030030b1080e40c007002d0b007542c40d000c80034080c150400040c0344200c3c40b401c42c4c603941c074003c040604940e0000b0320880c541a40400c0e8140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 612589928 1107 612588821 612588841
    0xb0406120212060f0c1e03010608090d03050105060702060d060b040806010e070e150d1508160b0a0903021c0807060e061003111302190233 61
    0xc0c0070f2483c085401c0071120000401e45840044001044140344a0183c040182d010702d07620807544a684824000d0241d03401900d04110b40d02c2290104015180319000c2c0505840d4060146418074203281e0901116801c6a03107819a00c0d9203445001c121045000054030003440040c0c0104010751420740f4500702c00001030000c500f0429201801950341c0c803888400c00e80f00d448000615a80c40414080340c000303084141c3e00850682e0707040c0c3d00247d843c200040304052070b8903404900034250b42d10941c00340f10b0710805446801050340d0250800140c50140b5001e102030b0840440541c0c558280e50340c1d045140d01c2284210381980d9216020681c400040104030382c000700711503103c1076841c119110001e59107049500148202a0710403070940d00c800d5a0181c0d0301103203462051001a80038444065141e04004d00b0821348891006140711420500503d4070641071212115003050f42c5a40c43c0381 = true := by decide +kernel

theorem cover : BRFrame.Cov 612410071 612589928 := by
  have h0 := BRFrame.cov_init 612410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 612410071 ≤ n) (h2 : n < 612589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
