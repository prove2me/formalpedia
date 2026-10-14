-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2992
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:20:59.573445+00:00
-- url     : https://prove2.me/submissions/cd1f93fd-f5cd-49d4-862f-248dbf2fd790

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 537949640 ≤ n < 538129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 537950890 1250 537949640 537949661
    0x150c290a060515031005090115080a140c070f06020f070c140a030305091c03053105040504031701030303090209160e040e011d0c03060702160b09010e030a15 69
    0x1400882d01e01004250090b48240c01c000700c0320030010000d405502c030103010000401c0060684078041d07954901c03100f800d11000155030005813072440032a580e175605000e0b0320003032004c1a41c0c07140c1a4072084070b003004c29445a1b03821074400000c0d030b54031800f044261010349040c0d1015404a0b98681e402d180a50b0312000ba0381110403007031340111082c14a9280c840100040c1c0781d15042c2a0741e00d0446000042c052103500182441c408529a058000c15074490040c1c043d111010300b0802d15004140e140c000302d41e180c843c846021a018200810a0b841c01742c0140360440d01900744128022411111061402c60982056011a403201d40050850803d50002503100d0f00c00c00f00d08120003010b081c020014000105a20321813038031510449514042903021402c0c02001c015030f410008135181000740c480c04291072140c481d010704800108182c2c00440c5c098482102001107416407801d125150740c8a401880f20941000b8070000f507462607842c1000f408080c1405034101c00c086038040ba140c80c0954800b4100b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 537952140 1250 537950890 537950911
    0x501140603060f150f0a050d050a0204110f0904110712050a020d082811040906030c091119020a14060a060b09010c02221d0613080301150c29 62
    0x4000541300030740703c42e2074803680844440440060401c0040d0b134240c06a000164488400a160020407000256a004480c4213030350a1000346000901c5107614002e0100c00807507000c08000b645681d162a43c00344188400c220710240c10b103001034986810710794114940e034000c00ea0000344040c0b91070f0104400c4c1c0d10007905150900c050f281940c0310141442c000a0080b0840d500c6c80c900c1c108119654103c042055842000182c0f62a40c400070400900303040e01c411340f19a503403c440851421958081c2078030f0b4138400c107942c1d40390515298a20001c00030000b140421030007582180000102040000038041400c0c0c40140801c0c01c03e82d03541c40c00c4400701c0c0e02c601c003885001c200301444c60340c00ca030032084000d0301241c190007400c028249a891510742035000c00481407900801030030700c80c82d089031035590440300c6084a00b6035079244058440b0b21140040902891070520042224041860001c0a192260720b000900001c050384c403442ca0200102071050726915960350452410840042140c0c0106141d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 537953390 1250 537952140 537952171
    0x1a0a0203070903030e0a0312050a140301050d0209041a0109020909091f020d020c070303170901050112060b04020705061503240a020f041502010605040524060a0c050114060306 77
    0x5002402d96802840020107000401602c0d04882ea41e91601c9001146c02c00b0440b00e00300a8035400901c00d43c04441086d0102e6900c8500140711004501500e061310006030020750000901d030200304000303e00078402c451211940c0503402e0b0400010805c2c81c001c4c21201405a1110000701c2048001032008080031420f07803007131103502c080785408243c5020248102c2d40050b642d12070001c2d140b001c2e228500c1b01000c184107185e000420184d2011894584092040c0800480d49070120b1060a0342d5003841191116504034440d41e012902550101e01000e20043c001441d091980e03440ca810a001151141c1191040c035281e06030a003002e015420344403100712a110000d40c81030f032841c2450304024100d020700a40c003150b804080e004003411030b00030b0071108074203424220051100038040d2240b0b00805010300d04000200306c40f0380c400241c801400b0f0340c0352042d00c006291002440003030703003103904008100656088410081442031180408401d10002000d4951070454103042c40c1c0039018000006003500034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 537954640 1250 537953390 537953401
    0x210409020a08061806100e01052a01060806010e0403050f0c0615030c010c02031b12060109020c160303021005070e192310030515090c0d050a0204050f06160c031a0a0203 74
    0x3c11b00c0b040d6403103428102c0170b00b00c42d180102c2e501d02500750510740980700500c1c500001580c185069039248814002803000079110045261141d40030b2151107031540c111030114001170301400207001070003800c0380d900c0c4c2030403d803001c01403918200f07561001e100f0303103076014011035424203102c2040f6140003070900d1402084190302183d03a405000861074030402c005d00ca0324034143e0794052440c541510341030485599507180c9482000035030040c1e805400d213102c2d4042240402e604080301604484e010b40180813610040d4150740090b00009201104100d000d01d89060f0a5460300c410000d5402c140b001c516116080080380741031400243c035001580203645500394103030380d43c01505105c045450f00d4081100e45030302c0ca11203560700c07041a401d680301c40100c0421030f28042107400f80c0400402403000307000c26115200d20004a12582c040d603600001c80c010106450b080441c02081150000c6080d070b1005c4100d6190740010718007642048030740d00c0d079007055221401102d00c222500410620030462450409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 537955890 1250 537954640 537954649
    0xd050723090f150a120c0e010e0907030b030105070507110f220b1008150d051c090306060830030412120c021606080405210409020a08061806 62
    0x80c121010b114000c03214503095540ca614070081014095034040c0341c0c654450030006055001c03420744190700145805050428244a0b006150007100b040e107444645000f440144242400c0040c031680900d03840e444140c8180d1024894180303d1441951059161056490011a460b1140714010712a00c040d000050040d504e40c0c0c101045540e4100501c01207000c103084907805011015072446d4840700b200c1440724440e0b00142c1a40c4155400b10a80d410740350750398200a8900422030002c2c00a6000181c24042041c6000f854100d0010b2030904481c61039032980c401e0150784044d00001034035008100b99600d01c1d0002249c0d9003003240594929030071491070039003030345483c040240701074010940070042a259900030110300b00c2080305074506010240340144040c0d6912000c2c1c85060101050385400644244920151405198404090040e610407010700541c0c9100c0c164a90050f28800c000014400c130091005082403100c83d224401d5900d04007040056000d0200768061074540140b08000a944e10b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 537957140 1250 537955890 537955897
    0x20d0c1d0f16180b030a0509030703120203090718060e0906010311040203130206120f0601111b0118090605012d0810051507060c0c0c1a0f0d050723 65
    0x4402c0d01107002e0107900c640854501c1c2031507140810b0161036074004146054040000c5100300034004040c801071300c0e0b139210725960b0311400c00094005040c0150504650065800540c0c001d007680e01110306c4161240f15815050302c0d010401508581c0d2404200580484d902c01030380d1014285015048941c9107444810b0070b070241c011414070030350340000050304c3e2189030303105001c040742c01030440703602c1c5e40711080b02543c00070055a1040d0024003960006c0c4956214981001009145030f0280044a0081542c981488004101241803107040c0c4501810000360300c003868000c02c008440452028a032800160164141d55546011000b24440d202d140146542e43e181200b603851902200355940e08400c1003409001d0b400242d0300c018810b0300d081c180083e180140961034010241003100c0c8200d25801d488507506828000d004c15400d40c001c200c00400400e000300f0803074a4920f91890125070402000e44d0f64010300e5100000c1c1c1c0d886042c03004181c2d11280050001c843ca0095454158440c025800c0901 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 537958390 1250 537957140 537957151
    0x18120c0302010f0903030b040f0218061804020f070614010e010608060d0c12051b090c0c0c03010c0c050d09031e05070902040905010302120705010e09090a020d0c1d0f 73
    0x42615940805100f5030002c0c2c038440492108000500061500a0140650200081c0b02e02d003070141c5c82d6260f003254402c445d003106805002c0d11a078140d00040c88015080000100c40d8455040049051912940020a1410107440d20980e41c0c82031444c00b80b045904403007000590a0b9010300600940f0400c04155042d945181040d640c240d0354400000c00c50220050004d0460115a00015040340c1708280e80404500ca076095691154401e150032038142030000072280e0180c0c1e00404039104000b400001c0c031340d10001e001a40e41c84217542c000300b402c1d11711041403080080c154041d8481030140078070607510301410f285007602c1c000e451500c2e609110740860741e448010389440210b600c00c01408000c1c000c01003844140a5480e1075491b66180000c0200b40f2099014a42c01d03a4481d02418010640a0959105071035800704d0030121002d101205000400e50001482400204005079032a940711858081c89112220000343c02c00d405404510580c0c1008182c1b055460188041003191040721540b20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 537959640 1250 537958390 537958397
    0x50906070209220311010f02190f021212070f110c0f1305010305030309070f0602120307110a26090d0206070503070c12020103060f030503180a0801060b030a1812 71
    0x98840d0916070340019080300f20b00406800c8140000d00300343d00202600528029440200320003a0a000c1007016480b40032198595030102401d60420940901d020500701040b5204403558030310100c0f5002c0c80c0360311481c103061400d0140010019555072200d082c00e40130840e8580560206031000c0c2150b941c019141d072141c480c03d601c0d00480e070181c844a0107080503003c0e0b140188101c0d41d40c1e09100f900c80c1d00a80b16030131240140d801c089030841c2c0030402c4800301c554541c0200b242600382e8503129481e81015010358100401c2c1c0550220303515003000144401c3c0e006462200000844914201c40d42d02311009085041c83c052080c58034558aa80048880a8042c0e8074284d07180401c0c50441d0035840340080003800e80110050104100f40028498000c20f4800e0b00c00300404c684900c05441080250b100040c89a8010000380307100210b06a81000708130b0014081000c0c9035290400e55084d00c80d10780080030180d8000c001c010070101075000b28851010700c14034140141469840c1c0f156009541c20003039051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 537960890 1250 537959640 537959659
    0x90f060703120504051c030603061404080307140d0e0105070807030e0d031e05040c0602060604050423160602160b04050105040e07020a0b04031e0e0105040504090206070c0308190509060702 83
    0x14000c042c03150000d403500150b5001640315506d007000c1c000f041140003d8404500c4d10703d8821600c0c04000040e0b0040b80c001c107100d420b582e180041215003840d030300104d284011003400710320740d031030254014403141c08032802c0045030614285800514801c4020804410142000c2a5102c800740106055102e05944e1a010030380380c951080460b418405044881c0c5803501d004200414030041200100c01d85441c0d60a4031456100d113000c00056410030b440160604160314010f031201e0121810102c4000010400d64290700101164285480c40780d0b800b01002d40c201c00181d070300f01343c105007025000c0d01c400304681e42401c0c2020002002401607000b0b100707030001c00c18003182d8294000c1001c12000307030b401554024145002c1c68020b14054588182e450f20f804016047c2680d90b0042900351089501a5541400c2900d00740c1004050030b1f03117107410f80e0044e03010840e14001c1040700200001442c020711400340d9a002c2100119210714040903400c0c00c2240c14805040d59a5a11003140c12154049510410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 537962140 1250 537960890 537960893
    0x303040f1e200d140312070e06180112090620070c0905041a0103060c08090309180a060b0c1e0a12050711030318040b040e03070209220503090f060703120504 69
    0xd80d000c19034050a2290b0b0014160138000c4000700400f0700c40c00b070094403010b907140c070001a280c40380003d1243d64000b006100301c00b820a0120100805008140340c84106400c0d040140411141c007481c06235101034035102070044081a0380da111440d44041c140562409040b92185010700001c0c0c080c8400c00c546480100d001c0c011f0038844403101800340d8000c0341a03543d51f4900200102214803c0c20049801c1e50002244880c010003a10b00f41d40e0082c080b2008189805a50084040c0040c044401c5075600d4030041500314a55000c0d11040141d000101845810b41032001c6044070704c03064140d0356070b01007400c000000b00700c240041c20380c3c00705c2c1c1019911102d0914000100f20000721910f909444007140704030203580c15064804c503031380c0d01f41d808000341a00e65050005948041c1c0c619040ea40c0100258001400d0865846520041e07030062050040c0513403050903920054070106558690000c2407036040c610302542c80c5e100a00d01107800a2030816680d0700a00307103410010084003060303a02c500080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 537963390 1250 537962140 537962149
    0x3041b0f180e010e0d0201060f050d080304020d061d0c030f0d1403041106370903080304060e011404030f0207051018030219081515210303040f1e20 65
    0x1813060000c13019a00b014041d013000034000d14081c8a50840311500320000241c82c01c0405040040340d4105690380e1950361a5020300040c0c500c00300742102d4040d56000f1040000c0032034a260071006007550701902682c0d0303d85080600e4118210754102c0c82d0b4000901200304150080d65199041002c54045a00c941c1c50f801c0500c1c002d0704040100e40c224400281c91154a902c0011456a44111b01071181c58200400c232402c060448510300c0d00e000c281488414000701c0c100b803014560240c07190b100420080745803000613080d2110946210300c1042c507007046c00b0805411a1030002d48200610041118030700e4003000a4050391001006824085c02d49040039401d401001c054000d16000b6144450200c4c40e8052500c5e0703d02e062042140790b007e440c001d1a00184807031015401071000340113201d41003038200108070407010f0b84500250f0b8800f07060042041c4080500c00765204074050f0807151840b41301410030406221312144910090829080f50030006050720240c1f0742948a9410401503d013012800709 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 537964640 1250 537963390 537963401
    0x312040512120f0301060f020c010806060d0213080c011209120807021006060503010807050402040f0306021b01050702060f07020a020102060c0d020f040f090c090b0d0c03060b03041b0f180e01 84
    0x2407003014000903002c10f0b0740040360086040f00d8003507481056444003200e00300d881f041c40e1030000303002862110100700d003454a24040c00d035000041e0f400628104401c0d0081c6c1200c10305a2080c0d6040d042400c0701d4200b5a0001c1050040b241000c00c14000c3c25416601d91111907001c402d02002d100500c4c0100b407040340b0801080e00d44070000601049199210840901070307400920501d4450b1003003100124080c1031500a90342113031410250141d00608580c0c820010350008075401c0d6800c5504090802c411100b40100742c003a0085e40c02605450500d00f90b04000321000800381e0095501c17500041c070060368005056507019002d00105030302c40c52190222800382c42101d40a00c082600031030041005001d03000d05508545000500f0416250000f200340c9240c3c8240c0b003043c5000005001210400d491a00700c01c000d82200d140000e602d82d21031140e0f132401e0700103850030782c1c2d8020302c0170900d00203108000ca010045c00003a44070a413030500e082c2c0c000c849034200960000c03100c0e44070100500400400d401c070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 537965890 1250 537964640 537964663
    0x1608030c0f030a05040b1e011a0c0d170f071b06020903120405090a0501080d03151809020f030f10200a0206070e090403050a0518060f090306060312040512 68
    0xb642d03410300c9042c02d4003400d02560140d4610b28104081100406980464986034003d4025003941360f1034000b52a64802011040f40d00c404000c108240410505015480c100d0b87d04e515031000107001040f0169003600010180c1503c08149414400410381100790f040c40c3c0c1c0c40c460001415403a0614210001e1f00a01c2004c2c0c1d01407080d140c016078015400f03000742050301c2e01581d1a040b5982c960b0350070340030b5803028447e00b01a40c010305114552603100e600704201860384442c5040003030b950f039203a0050743c442d0544440e20740c90361100782c1030462074041001c4102c41000c03001043c1ca104038044070785e1100241c0c407000c6155035079005904403001c00f030000240c0381d50001c42e88540315002c0d0134020b500c69204444000000d4903200d170b01400c0c0c0c0340c024012409103426554080c00d00b101c0e40000d40705c4d58444ca415480c115401c0c8512203d55440300700604418444c1c020f2281c65264440500d460180041c2000d03100390040c00550f41a8480300090320216507080350b085500b294884511810056107144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 537967140 1250 537965890 537965917
    0x3040221011d1b0108011707180605030c0d0506010501180306020f0a020706090f06051b060a0b0406050d0b0c090a17210a02060a0f0605030f0606010906051608030c 72
    0xd450300501030b00900544810006080e03908886103104100030080040081c2c030b01066002c00140281440141004070310802c641c22508481d845042071100e102c0340020407105240c49041c184814201803149030002401905e08a00110a85c1d0b2025100c04c1c050180741d0403c41c0700300c6400030303002d007000059000b140c028400310758a03058540c02c0c210326408a8032020242c0b1401070002a80e41c880e1581c03404884400744030700c0710681003c204a0b0f40d0351108068003040c05206458604150080c0040c43c0a60101180000e04480583c00e01040c0c54095210314410345108000d1400b0400e26401c180c3d010141e140405e5030f81c1130040008003820000e800003642054508a2080729080001307080d4107140142c110303101c09001b20703510342c04da40c0b091400910050f04034401142c2c440300b064119500c11089020049491031301c0384003180c170706510a2000107040c5e1029084c0301855070030096400207445980303021840c105c85064514452a044d110003003250500100194200302c2c0442643e260420201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 537968390 1250 537967140 537967151
    0x12102130911040504151202010f0306090c090509160e0f04110409060305010b06030132030d080115110d0f05120103080c120310032409050d230304022101 68
    0x580009054016000344c41c022481c0c81e507010a00b811040d801400c85080d5001600040d00701d900450703041c403e1843e010141922120042000b80703443c003d02c0701180840d964404914075000402c0100c1c0c0f40502170035181c0308520a14541c2d0b43c1d120001c1c01d8003a0f010703142c9178040110680850020007000e00340e49009035010030003041e00c01c0c480c7c0003442100e0051000303000c29250841040740e1440300307110742241c0c0180c0d940320500a11013800d889104461902440484201c140042030030075030780c1c0c00702c0c3c000140d07910018010407904401100c0746506901c0d006c1410544125002e580300f8040803d44180007440ea1580ca0151044040701da4816041c2d4409445503907924180c881e50304a0785c408017480c0107003020318000b000710900380c0e4400e080720000c200ca014616150710b040d49080c9084440c05c2e11041e5a1010354103401c3c0210010584548002c10403001081c4c2c0062400b0b0204100032880c850130038904289080031400e07246c020f501112030a0a50a4031140d04090943d01040c0203003075400c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 537969640 1250 537968390 537968411
    0x2a0c050f010c32030403030518030f09130b011b0c09020d06030b07080708060d050c0904030c020109083007050a06021909081207051e06150121021309 66
    0x1c15010100c080708045500c03404800d0803c07419100440d8008000007024000500402d00c00e400c1035400000c60b500100f405510303e9049419640301c27070700442e0255000039583c1d03450b0815110382100d0dc04440790411410f1904000207200804500340107404108440200c01880014403905004000c1244219618940c174041000502440e10003694140d20344000140c641c0c1c01030300080d00c40c0c1c00c95654115107550781130420102099055094560344144500100c440d00c50171348060055019450300c44040303041e440014401915a04180c51540000400c080c0020301103101d08e000200c41d60b0707100300d110350500d040b00c624040c2400203080c91040084000500c046070380140301e07458070311519011030f16240b001503402013210320410055510001203040ca445001c009401840d11030015203407400510420070003040d10600040c1d0b042d41040c818800d0850240c82c14001000007070800b40b2200320500c808403140005800c0000ea81a0000f40c4100c0d42d5171036000c948054071120074104100c4502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 537970890 1250 537969640 537969647
    0xa0b1f1509080309131112040b10120f0618020d201e13020906040e0106091a0a0e01092c07170a0c120e010e012a0c050f010c 55
    0x8040c248404188680400b00d60010040101d44510314090300000181c010341402c400209000303800c1d244218010300c6038000c51015002001c0c020381c0241c0c0603a1607410316181080800149600101c050907524141c0700c002020380b0b6600c540180c10420004244031301c03002c00100f042d041c034002907020311400c03695000c1041d60203400a4103198100e0148120038560244003920422114213444a06081c5400c14513183c900803054a004000d40d01505040d51039020800c0340e0007c0d00414840c140240040c8880c580c040c2d2100c0c0242015034201c0344c0842d074605110701038458014400300b001400031014003070780d02462045009003200203118901c11400f0201a1040400c01d440362a80c0c000c100c0883c000d40c1c17180c42c2041c800c0d4003100c8081825259021008020f140071030200e000d111906440c04d82009280c0704c1d24940e046600004100125001c40003130031500518203402205100710240c0d03548180540107222500200e00b070802080804c0d007041458400c45188400882d82004206c4440b1540b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 537972140 1250 537970890 537970919
    0x3020105040b090f0c060c160f031421090111030a0309050c0306060121090c0905041109010b0904020a0c230d080103150c0c170301061b050a0b1f 64
    0xa0100e2520310344400810540701c0c986144d2a4103654052001c00c501c40c03401a0041c244c1d9080d55003103a060142180104034400e140c1c2d0b00c050807400420030100140190000c440e030460741180e01070310300181074a030800c1c03402c42c0d00c00b8809958074021660011690192031190602e10252080301e803503e009000040142844000803501c502803040c0c1d010300c0b07040002c0c07541c1c003614058440c031001b4100300c000f450003024910054030501c4e0315400400c2c00300d0321807200f040c00b03802002c1e0302194903e428144000090100f00556001344240030040110301c1000c400e079014001c0032140540d445258a200300e40c90203c1400107840080102d401180340300c48410130391113a0348400182d800380042800151880f800034071000c5c10f03000c0020f894040c0084140d100300584107241c28040030001b1141c60b09400c4810b44855030359808000801400f11039008000f03031403c07172092540300009a080c0c0e03540c551030b100c240d0f0f8000d196102860108100e0407a09402806034403800b41c004407415502c1d046681d9010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 537973390 1250 537972140 537972143
    0x203071410020307050606120a08030c04030c0501020604050c1002010f0501081c02030705062a0c07170106030c180b100201051e060d020909031308030c1c02060c160b01030302010504 80
    0x40324003281c215050010041d61a2690040e01400345551004284001e180c9280c000341c1050040c00f0750080054205000786008440140c803107034135142589080b01c000d440c00c1d04030034150341c0300703404010001d04001901071040300e0650b20643d450304000c1043e40988940e1014661441c1400004580003000103244500d80240c51f041c00b034910b06c00b0b6016a120309c00c04002500300d80252000a0407119580c4004003201d01264658246003200c9040e54650703004400c20305003e400c010010883e00c88101210400302d0740c244020030007135145030f40d0102c0281c514405c0d41c242d04070880c007070707500c1c0109030b0700540f60010042c0c5004890388403480001e0081c4000c40700c1801b02410298245440c401d602c9a880c42104050400031746119103800b0002c100e08000d0000500b840108140812200e07e9800b48005061f1480215154504400102d003401c0c1a146441e8000485030104828103a0004007075401151031191039503215100000719081d00010300c0302610000310900000101581548110300c681d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 537974640 1250 537973390 537973399
    0x180c021009061a01050403020a23061605011b0207032301020c030a021b0d020906040e070609031707080f03100905040b0f150a0501050a23030403080c03060d060906020702030714 78
    0x14580c0c1e00045d00c0501071400040d40001c0766513030521000c1c00a4120f0740c544480026603071900010704d4005003141c1d015200f885004a001c102d0201001024081c401003010b03190740d4011031400600000350b4602e0390344005800e0040a0782c08040c40c810580c264607141318000001d65030f035980b1040155076540469209801071103404041c10000144030380c0d05440c42030060000869400603020800960009800c15a2040d074038502c01505800c10007203e0300908035600e500000c20f1a5050840e40314249181404089008000c5c590001d103813903040302e074a88a1641c00c11f4407600c90641308007002d40c5a80103683c0c5203103048c3c140000c1c000d40c1412148110800f403800e00031a80d9504000c14140e002c960119081444220144515030080300640a10100d41c070303080500c4007207540340c65940380c2840d02d07403101801e00000784400c0c954000c0c0c08550005008130300c5861810004003055441c400980080c0900d903842d20741c41e04004c41901194500d075001000c40762020b450b0140d0b10519401004010302c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 537975890 1250 537974640 537974681
    0x31b02010912090602120706150e1b1206091009020a090512010c09030350030103050c010e0120100b0a0e0c030c040b0705010b010201050f01180c02100906 68
    0x107551085460f0b1003602c040d036010f0002c40d0584c0c0e0240555801070441241d20b241c861b20300240c54451403c07400c00030400c0e07007105441420540d40700a100803034911304000e8840c0401c82c56000d8411241c501d60040d0003a00c0c414400e076150350070507520400301d8000050b01c3e0700000d1440599540004550165070b4101d5001e40740e083c605070307070174200d500301c01032080418000c51080000c00e0054902e51031a00c1c1c011002d800744180201031410300d4075038a130452460020802c01403446402202007800b80ba1880003202d00d19411500c42956480d03408003c02c2c10840e020400120592261003003c0b001c043c0c18812211220143e90072586501c100603140340250b241141818246c60f05141e0502152540c03140c160103610764034001c80b1507900c024644e8000080030031001415005010040c2426401080001034103400e01000a00356400503280015000191005000803000625826803071a4092000110307245084026802c0c4100100030480c4189012401005e11056403c01a11200d842114000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 537977140 1250 537975890 537975923
    0x10e0f090406050c0c10050a0b0a0e130f0b040f050f01021c0207060603050616030e0c0906040c021e0a0605010f0e070f050409020a031407020106030203030f0a031b020109 75
    0x18444444440a5400800c2401160114106901032a0021000c900c41d40c0382000c1030800c649440312202010441b6a50b8008014003601c180c0300c0c4030b041d4a0222030502e4443d2130b10b00000d4010701c01030000003001031620114800c1000494980c1c82d07059002c0c03807410300f520341414107400c1c5a40c0400250784c90301905150130304c0014180300f02e484441c42048201a0f00020a0000b8001c0d001620100c914a6566102101003141000788921410318600ca00c4c40a0441e510010144e13600d60750341264550083ca0492490f58070341d64a542d03c0b11056034000b4460f207070031000301d03d403201240c001b036035840c070f0f8200d0a07040a4000c120080071502070b801c280700d1031f40c0e54412003541da0814410541c4088129010481c02d0344070300444c06041c0c24034a842400c06483d149200100e074003480c06880130955400c060242848400d460642c84201c50000b04200ca20716004a82c80f442007a903810f54210300014013105082c085e034012407801c80d41002442208403010400703030082c0b10181c01070310540f44480c101c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 537978390 1250 537977140 537977149
    0xf0e10030609080307120903091401050d05104e200102010c051350191809050a0609022b06020a0509030d031d010603031b050703080c0a02010e 63
    0x540c7e5515646960007149080c80b0840c50409403044141081000c00168003100d04d28050640151080b43c1420000c1c0c1ca00f803005207010a100040140c0b8402c038070f08203006403c141d010b062201e40c1d8651800600046070040c0801c04104540041100b010b004401750a510424011070b210f400130b030020031031400c402d6804da55501802c4a04000d0782421201403124241250381680d980342c03492206264a10500c90411001400c0010203a59050365400c030b4842c000c00c0d0301034089080055500700051500c9042c010520400c6000f0350346601c14080301a01c40300c4c516481101c072a5080f209840c080130462414001419022005034480d2a07100044602032080d841c4090302060030161480c82d400003555150b001c1d4106070114010700038103008080d0306403020b02042207000c80b1035500107a494038220038172001030a0b0070810f2500d130f0b14001c400c4c400a41c20000c02c0c2420b075050030010002c0505860803528240c0d003500018506a00071620017074100000828820440c401d80301c0288044902c001d10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 537979640 1250 537978390 537978401
    0x3030b0f0307031511180307050402030106050313020109080f07230a030605060102031312120201020306030318030c04022101060509130e0a02090705070303060803040f0e1003060908030712 83
    0x560307040c2c2040c0c1d400c20015072088904546080082c1c000710350142290032030510351b0044100c0c403900b894824103c2d51075107800d10102d009004202c034114210f50401c0d000800301e00005010b00b01219925200c601960b009078144070040c8900c1084414081410440948a144511403a0090008031400710304c07031504a0303007400f50b080024200c0300e0400d107191500c1006d030601030172060560104101d02a44030503140d030090040c01010207400003442c0549032218810386201d0003001103910600900034641d8012007111100b14514810009800d452000241071400240180380c7c0140700080749100c01d0300700c00681a1a85551500780315036a40c411040c1c0385803040d596101d9106400c9102c0030500441548100342c2c20110f1000c50b10312140d03541c085840d240703056500e080820000302d641030400d5403500841015240f010003075400d151510040d01900f00311406200a21202e03c00055885c4281c070385110000d41c1c00003c01e100140c4141000308481e44103855000008008038000c0b0424681400745 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 537980890 1250 537979640 537979669
    0x21040513020703051c0b06030c0306010e011812080409150302100201050103030212030421120b010c1a0403050c011112010501020303040215090f04152d031104020403050d080403030b 80
    0x2030a2070018142d546504805175080c400080c10360701c8048040715101c901c060740c0314884420b0754903640d0500300300141c11910300c1411203041141120564030a1a0030f6903452040b140540c9190714014134a00e030030041405a030b08418001c03031034501d1001c1c07003000b10104081124003d0f103008004815440c1c04a082c2c0f2400d02010300580d0011032020100785070080219030060103500002589074503200c03c008c5203224244440c2c0019a119039041010015201c0c00d408940c00742805007801015540f80c0400004090301d50b0020440c4e51b000406050040b0100d0300c540c0c0740c07500204040c454045003200160082000c1c03610094a03a000490340b5400001145e0145400a0181d41024409001c0c040113a00000407260000001098074a058455000d81c407580080b8240c0c90010504214400c140c41841c0b80031203543c0d0b030050040f0040d0440000c8003030700b5039400c84035090a902e80000401c01901c01c0d98801030a5204620b0066100c640c81648039000c2e9100760307800c2c400c044c040c404001002d00c00005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 537982140 1250 537980890 537980897
    0x10030c05150405060a1413180c0815061b070321080a09021906051206030114041217130507080c030c0105090a0509041a01060f05030105100221040513020703 69
    0xb05004a1821801400345034825140241e140040d40c10310040940040c4052040e51004480500c03a5400b0300c507584600d400c0800301048140003034040141184005402ca14441b20f420139012503540b100f10840da40c10000c2d02061003952400d4a40c5a5110503601c400d445080208072200d0710904108641c451140e503d9641a02c50b840e41140c4600401190404980c071040311940d04005200c0d9005010083c1160344400d601e800310400d0b0001002c5006003810711a034500700304c202607101c8584111303802035005400d13a401400141819155000c5228400716048880c10400410203180717449030b030074a403280741658540c80da0f0703000d003540d580502e865181d03054001c07a8100d80b50307501c00c8000e00300c3c40710000c103040070030369440300401c1c110325040c1c0d000c0e2000b100020040761841c882024890041496244c07000410030b441d413008065010602580b88500151162200020f20030410716003d0b9114900000c0c600c0d51b109055400c0f9400341c880d541c0690705990040d68540410320903601c0396034050b00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 537983390 1250 537982140 537982147
    0x612010617160e01032d11030907030f05070b0f0a200709020a030b1003060f081f09050a051209040605030a020a0b0a140a05040609050d021f021510030c0515 69
    0xc2038032103091440016041517607445820844401205503032074881c000c1c0c007050084903606d85800058a00042c0e0350111010101306004e200c5000180b12000c49070448400180c0d5402440c0440c01d100241d40310402561000c110340d0320605520b0000d1842d030481e80c948540f403580740050040318603c1c3c10407000803034001e403504010b10704094000300540f109500d0700240007003045001841400c0c00c1100e510010741d44003400d01c40d203040004510b01070901c16005041c6010f1007580741d00f4080700200c5103003031151103039030705400c100342084a400f455074810142c48902d01d282400180c0d541140c40101d10403400c0c018001528140441c03241030302034000e0300c0d00404a003014100c1d00c03582c1c4890031800c20428440c031340006400310300c0c010b0410210103a4409584924241c0006d000d5055500320130b11501d141c90041d001a0303501213018240d40c51070300d06601d9092000344142d00700004c103c004441458081c1c208980c101c00600900c040d24030441d0050361f030644680900202004941048503894401c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 537984640 1250 537983390 537983431
    0xc0607090e1f05120c03011a0907140304020d020a0306090b090105070f1710050325060e210321041a0f040609110d0506070f0e0a030305090f0612010617 67
    0x3008801d1380700021004a40e504103109000c0b90860341d68000030000703d58060080c3c3d12038078050750411713081110b0345401a0350100851845070315210240000340311784220b030b2600086403284002e0b4801903401075070030411000c15041641c03c0f0101118484201c1d4607041c00105424002d59140d0351aa1540e92483c034007030b802c0c0c200c032218210090040d14016400302d0340003d4030781c0c040180580039104003d000c8030010a40c280d002d4a1000d5422403002d000c2205005051502e401c64400351840001410020700c4600d004054114890b11f468440d075842e00016281100c3e1540c2074242c02288518000010410b034001c043c0c2c1040c40a0b1184010f01350700101080c0491901e17009110701900036000030300c1e51400310300041d11502890000312000c2e0880410003031510741022000c0d81d800f0590070061444a038502c005041011a030000905102011a0000007a190241030581c1510042e09059a4160182c981e070386500003403141c0ca0016540c502661001481692024020703003040080c1480100b04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 537985890 1250 537984640 537984649
    0x80106020a0305030a0b040912031a063903120603070b37030501051801080304090e030f041d220b0a0207150c09050a0e060909030c0607090e1f05 64
    0x70340380c07041054803a81140c845503118450741e0720f000c1c400c0b243c200c441c150078270018050302c40400006041c200c2e0388481c8440c0e070b2035050407903400b1858500021000600c105a4225010124020200c0364102412221500c1000401401000583c4103822035980c2c4100425544041901814a54020600100e40d00d00b41800000c2d88c245001c00125443d01200074004c0112212804174100082e2104010002804c8c40704511110072144500c16080d517041244066070f92080d4403030164180c0d81e03142244200704060090380c00c0900e190b1101030783c4a550b0f1101d990001c1c03030106840302c4080340d5004503072909490002c1810b00143c4042d4034034001480d407039604400d50001c14034009950200108400240005410405000400030008806840c21001001090141c0249014980e448011f0241d131505815050f40000c045075840360650b9100305041c154002e2441d607550340c0c842c040500510315000041d8009a40d1000001800e50b500e1020700c011701c460503662504840390440f0113103e1800c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 537987140 1250 537985890 537985897
    0x712110d020903030d022215080402190b0f0a2a151103041b08030f0d0902011e02010b0312093307030e12061e100e01170d080106020a0305 61
    0x14010141c0b0304007170000300715006a9201001c400192010041503031132840b036560200d0081e1210b0182c807a50401d4a010140c071206000d403020340300b1194101110110491044081d0103401400701080c2c464100f1040413800e5001601d000c404204c5400205840381014580d107941c418411170051329070b00407500c03507590075001c482d0b103603071036641b42e0301e41001d40d00701d0000030350041d4401c1c400c54080c5000500301c90f6907643c0503005210550820003c034404d40d070500c0e00780d03048034000090000d01c0d07102500c0140c642d0895510458130010100220361b800c150107510504160505074291901c4118581c0101118410500382503030100340c0360900c402ca81ca5038040001c034641c40c00f014030150004030743c007080542c0056004a0028000300c02842d00c5061540d808a0103035218001010203050004070350b42d010326084030600c6441401000607424040001c820001040b4011070b0310301e2540c6078078034449a04060092600d00348038041041ca0190710a0305035904854440d0301078581d9031050b503021100340c0d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 537988390 1250 537987140 537987157
    0x803121b2b1107060b01051e03180a030504150203032e051e0112050105060909070c0206040312020c09190905070302031902130608060411040e060f0712110d02 70
    0x3220700c0c2501c0d0501c0e50500c501c0e8038081114400c0c544a41c0c0c28a4200241c0740302e0074107035040000601c028807076403201c520384c083c1c48891019820b0f180e5031a01520404514920b0b6400792130f21441a02c03070203040c0c000c0000c009580000d45000c180440100d400c5c3c0c0d41e44405e41e420010341d00c14a0a00b1038400c1c1442040100380c0050038500000b43da6907000801d5000c1d42d01c05808001e840c580c00c59400e43e04240b2220a8042041003406a0341c0341400046003405080c50440c014408480003c031054860240d454001d94000d11a944544d1241007140b10b24000c04889009407160031104101803810007038191003003145070039102d050300c041954240039210505048074180f052160100060307038148800315580c3c6003440d81d24002101c2d0f00400241030014484244800e262101c02e00000c1c9000c5071041d44690400b006041d540454000f040092050101c0306806000740c106009503035640c811207500440b055611446c48143c4900b0381012900541e00b4008030700340401401020410781d4001d4038410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 537989640 1250 537988390 537988447
    0x702030c1911091609050109030c050114071a0117010b1003110904060810060b070b060405071e031a01030e06130501140a0203040c090212040215040f0803121b 70
    0x10b440d000441c009200646a031191100c4154504a84507408002c000c018802407a005070303c00e207035803603107410400c450081504210491041121130244801180d01756a844072040c1c10406282d01b0840e000013083c0110100d02880400440980748140945002d0450051040310000c241140940040072000b840300b080c11005d016070006039480f442210300616101c400350422084003002d100448a60b6001059140c2c2d05000710b01c00f2901c2d01c944998401c00c1a18001201d85680c8000d403041600403c85101c140000704102481c00e5141d080000c0b1001019031004c00c0e96420360041d01584c0fa9541c00403d83c0d84120002120181348607007101324079015100014020b0070143d40703200380c0e01c0e04594120005800200344001c014900038140001d1000140441c02c00314a024805080d10001e00068030400604c8403100d041c8104500f1900203004084124145541da0156240c8940000701800c00b881d09020004110030000a000c01040c10780d100c20500c1c066071003038000c6542c0d90800301074014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 537990890 1250 537989640 537989663
    0x2060306041d01022701090e07050a0306051f09090612110d0b0403200102071502090307080105011223070308030711060103030806030607110303130302100609140702030c19 76
    0x10301d40b0030710082280d20002c10b0101c03582110441800300d0001105011030406c0310b140c004101c10701c0c03c0360000d5082101e91a00540e80c0d0312046084002d48001d401c41c5600500b20403020144040c0e69a1010071244281c8a0b2140c5541c0e4001c0721048507220b102e00c54076100d4039501c002c005080f0811200d00408020006440c004054503440c10b221022134044010810f078100c840d24103c01c0c103269100484040b0003d514001c2955600c0b401000f91810200f03a03260041480d4026a0341801910040e0000100810196a490142403074014400605079100000040840c1c02c0c602c0045148001000d00c04c01011541c1c5141d0310034038181d000421079400c0082005043c00d01440c14032031140214000d07990084541009070405051240140819090200410300502034002c0402600d078070090f1118025401d544174101030b1b0a01101500e141810340c0703031203c082084001c03540300350302446548641c00c4a44d51b07140410b999a10601d44072038a951f002a0080c2d801d2801080445081d600c5200803000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 537992140 1250 537990890 537990941
    0x21c05180a1d04050f0115050108070c05010c031a0a050d030516050a03020304061707020a020613090e030d06080607051c06150201090303150f05130612030504210206030604 76
    0x88410b0008a082c20b2250070006120601001700329040902c2c13582c000030410060091280354508506100d058140b040d1400000c030030601075601c15602d16000002400700008081e4003c00614120303070007882d5540026464801e40c09c207600136005443c0054012040c18409441c180e420360015010200503c06510034000020703814000c18070b11758841e400850701c0ba0f04007030b00030b040d88250301044080e40d803408082280307403070b8001110090540c050301c1c6681c0d219403618601c04281003e4100b02980c904003580140904400070007403504040d000010020192521059510380c0c406a4001000a209004040c40d08080800c800d100d443c6507580020103aa45558a000300b1b11035407250000343c2d544032411403c2c150903001e41d03030310b00b03e003c1000c100300d500f00031240d0b441551900580380140410142040f407081140d10601c0a804082160525200c7d41d18001340154050302076014544c00c0d04030f1401410380c030803900d03140f03a9a005284a0840c2d4a05041c4402017030b044c11000003c1e00400714480c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 537993390 1250 537992140 537992159
    0xb060408070e04110607082d0711180403090905070e0405071706091303030504060204030c0305060924070c0c0f09060509091203073903021c05180a 65
    0xa0082810100c1c515141c90039041c100b60001c00c40c05005e000d22810003200c03000610300411603c08241040644100c22860303400c800364511200136055100380001040000d10902240b0002003040455440e90400c4060540501030a019100200441c0c00c0802c1408080c00540109a0080840c03420a81d800840c000240c00e5032401d03615100070500d0458072a07007820a40d4811548800141d80c0d003085401d05510140003008011400703810035039201d01080c20441b080c0c040f44c0c000e54002003400200380d00c034103080f07440d9401950805800d20507600c0a030142040d02c0c201090750f80540c10140d0480d51454010b4031050f80045044501401c07089002c55007a071456540c01c09800c4100340000c1c1142020148100200c025262030704590280c40100583c030304580450b54000758902d4100030702402d90320f001040702141030310300ca402c911851410f000e0320400c40100007900d009600f200c0040d05255644251042c00b15894000900f0400031f02240b812007031501003e420029003030340001d07a0743ea007458 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 537994640 1250 537993390 537993403
    0x801062c130c1508070e131d03070b07110a02090601270905090d080402090a09020a0e09060403081e041205040905040c08070510080114180a0506011b08030103060b060408 75
    0x410344084182540f8215035888500746a22040030705026003441c103184000b45aa14030703d900c2200044c2c40320101507100ca103000b1540301c170b100300d041100e0700e0300f0080c50508450074044940c0d80005084c1302801c2e6221100049003000c05030090941007064885800442e41064141450910b19040141c2100f034101a030751040c0040403e09070000e0035050007000b290400c1440d80015080000c048203210150307541c00c0d6400e401c04540000060940c14903c04542003030346a0b408403954007480030400a4402d400b1a444c5d20480c400c0d80c9141199036140b200c2000a01c929491465042e0324000090000e5842002440c0e07800707450a20301c0c102030b0385161610540d0b404aa00f2114803500d18803c00c04d0007010044c000107844101c1c1c08000c589010080201101014031600c8482c0841c0d81d07d10040b51526443c104070300d02c90380450115440c2c001300402c003400c020f544541c0054028401c2509000a44048905503a40320b8071b140e2446c0d00c0e41c0c64100c003a1000008442d4030032030030000050501810001c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 537995890 1250 537994640 537994649
    0xc0c0a0f051c1b050118031109130506090a03090e04050322270f0203090604080d06030f060e100b010e091f08100e010b0604290c070801062c130c 64
    0x8482209007071000050104010080985586401b2201803000446000310803d0100040d10b942600395955044e50b6215244484003910328040c0c00300b4000280004030324440558000c4d112803001550700d4481c2002c2103001c98000e080764006102078400715500300070400d112800642e00c000340d6911800b2603c2c22042c2c10042e9004840315119103084856540960310300e01c1c19440b030031825881d004604a0f22a030380200f0080c19030000142000368080c0c20350000703000c5c5400481228418645141c00c034010245018145d007a48603a012561345d032034560060164111041c0c3d44c0c00b140700030344001d00442c0c000244c041d0700f40305e404259002c42c5207000f41240c00140502c500402c1400c0d600e45407142110781083c0241d03207076414400c2010045e00e81e1801c89040761804581c030a080401d00d08128500244802075030740310b600000d40b10110160024200e4150f03042c07500200901ca507503651702d0640040c1550344447c11050591880c0007040706441c02c130341c4511002d4001ca80c0b0346083d541c100c2c880c80207401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 537997140 1250 537995890 537995933
    0x71b1701091103012d14070302040501031803020705060d0b060a0302070209011409060904081b07050406080a02091501140d0603030e060c060c0f0705070b0c0c0a0f051c 74
    0x1e0024015402103007881980150300070070010300420b420031041035808082d4410030001c00320200d1910038075030040c40b06540c001d60700640c030300304640e0080107503115205041c0081d040031f1444d414074010300b0422203419031503001084821314184c00e010740358202c161380b0714120390788909031002c0c0d0312110001e00c1c02007030f5960010f94480982c4100141c101043c1c1000031b03010001130745c80c25182c9a01760203940000c030884044149586902d0440f4540c8075070a10441b0290403000250031034040001d011094034404c0714140003482e21145c4065460342d0307001000c6e601245079408205032185124020a200d030040c503003060365080b0341850024550206504900b1a5542c40082081c0f50b070040310310580840440341c180c41c1c0901112103039030b10348020701002c032649000140c070251850008112022254000150f031441555101004225042020280700380c4c020000380b4015807400e4a10a01600d44a02c90f4401e03131400c0c5000d0001c403500c0c070f5450800c2c004811035102d0105192961100c03410740c0800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 537998390 1250 537997140 537997151
    0x132901060206091b1309060c030612080406050d0f0e0c091b0f0703090b03012904060206160936020a050d090c12060506010e04020f0714030405061b070f0b071b1701 72
    0x11f4012700b259015840444800700c1c3d5004000020148070440b02114418903100380c0301c01c1c00054002c01420a0b038101c07a0392914100c4520710040380400c4c8400c0807030089696801035511580c52094104a000d001c01401c08204041504103d03a4070140c44043c1c080c0c5012171501d40c69500307034100780e802030f00714420103001c03800c2ca0600a84c880e4051000ca86d424808103081a252804c00307980d400e005098041001124440100f1440c421030b00d81c00100850100e0655101c550380300a10211030380c1c116840301c4603020740d41d02c05602443c002c5800c1c80031143e8032145070050800d600d100170403000c60221030284d0b1303140000403c1105030540c81043c07400b0b0400080e4500f8075000143c20034813480c0340140a94018031058080c42000e0302540e0026030000600c440281054a4260941c8181c3e0002613200c0e40214401880e901d0300c1d042805050380010866171242e8a55101d001041900c1c0714058072224200b248000181c4c00d000d401f181c07421041c2c00c0c0c04c4025128524491005400f0031510070756075540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 537999640 1250 537998390 537998411
    0x403140a0501150f09050615040605090109290c0f1623060922021201081b130b010e0411191b0209132901060206091b130906 55
    0x384280c000340c4107080e1810000500d45000020208440d05c1000511660303030000441c0e07922200488950000007200460307540ea19010041c02940000103140c1c00611014004a4010100120101e40280e800c642d41103010340030a4499455020041400041c005c91414410001e400c01ca420521a1810703c851189418484030001d044091040000d4400140c0c5d03901090343c4520044030540030081c2d900280100c3ca00980c0707449a40c040b19075580d01ca01c0002c036000070320b4501c0c088905852003041598080c1810404123100701d10410400e0f0f0b0300c02084414002c05041e1980300304c407c1d507410304012400c0c00100e00098201c0da0080030885440c10300080b03580034402c1c08044081c0c04103960038810411141c00c408200c0d07410429200034014070402000c40c44041c0c180f9650f42c0f01c181c1c0a1b049030010700420307000c590070402e82808040b88441600000c07583c0390010071200e01c034000000080003a40d0950f0701882e40c01c0c02d4605a0390b0070010291410740f4056043c022282400c0c010100403800c005207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 538000890 1250 537999640 537999643
    0x30804030605090d1e050906181008160509010905030d030c0f020a21050912010c0314040506040b06061e04050f060a090303032d0b0114031012080403140a05 69
    0x1816200e5541003902800401c1781c00002e0b20821000c0341d444408405007203041921280b00e8070790303019032140b000304a90120300c41842c100e10400742c06446036043c2d81200c0c07805550540e02070b15160502d041c004001a401351042d005440c14800526201c1c0b581036440c0b0200b42007031100049640081d85903411520b400303400151041d0341074101d01c02000802c02603150a0703219200f406203000e1010314005e25010180c40303002540d604600041c2082074095840d5100e0340244089850b80b00800c2c01d0000c6000d030000e02c0307120740c0e124640000c003030101a0740b25542d6614412004181c80e80c0541d051007486a002d0071303030000138040404013070f5541d5520b08042c2000307494804074a481d48a14000c000c0b00d030460340e01c415240100c0303625080c0403c01e01c007021401068151105104c1070401204681a41690010f405c00306682d07100b0389036054500107102070310480c0d00c411514061003880fa00c000700402100c3d002d04034041ca02440c01d5078105502c9503220a00201c8003881102c0d5a0300030b126080601c43c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 538002140 1250 538000890 538000901
    0x5060109080c060706110405030304060207090f0203012706081903030513080a0f0e0d06090201180323280c0e09100908160501022706032d010308040306 67
    0x20740300100700d0798400c080080d482e07100304000101196141d04160300164062000c2d5405000d0040580e51a00c0c0c40f00002583d401c41c83c070a480c0700c8e0341004040d0142418510032031303040c0d401003d102c8140c1c80d440f90024000d9081c00c80c02c800d11950301d18000406050070f01050801800380c1d444034420103070340c0c24001e09491000d0580d1800c145000f11b4080010010380844010444500b0980d00484c12074a00f600c8840b41c409055400c98800c401020412006911151446100740c035079030340d40170001300c2d1810745204601004000c031206036019904079620ba28007120030165501191303042a0441c60307050172646000400300302100c04c19444800c004003625110050296280800900d180603418660354140f480d0704e01c08415581d2400e41c0c14015424221612038440500403200f103406442c00034000d50214207115180ca400455296080308030125079481110010000d60858881090003400554180d11001c03400d61681030342244142060040b90007180074101c15034a6a1842c1040d00a840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 538003390 1250 538002140 538002149
    0x6250605061003020412142803140715020f04030609050c04050606120a051009020c2a131107020910080c0117040f2901170102070305041205070b03040605060109 71
    0x5006010a0103500d1000030303001c00694001c2861f21b240c07100fa40650b814031812200d041a101c280404040c03210031840184100f00348241c0e541d10300d8107a4000d07071428600400174010401e4090328080f011600365a0007a250150a041c0c5892030140d699079040d0480c0c0f4240e000321880c0d0084070b072824681c030b002e1045130b9101106803549883d040c9003a580746c100303080c020b090a402640c2da101140504000300c0c0c0260150611141c110b55076120a01169960322054815200c1007138005ca00036002186004560304148000e07107002640d981d442c003140054603001908401696090013001d000d691002001d038011b440c23030b200001600d42000005800e224454850710305200d040c0e106040c024a032540d255a10a4018100144412031840c0c07100c10a10452401c2ca44200c54003000c12400b125403409034101c2d4644900e024041e0204408607090b07000b0741c040507001c2001840108811151003401000082c0700c3c50030303240c030540c5914000140390007c0d5411f4465640d200f04001403540c1060601000d031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 538004640 1250 538003390 538003397
    0xc010e01060e040f171207020c040501061e030e0a1b08060a0216030e011404231207060809070b03042306040b0a180f0525060509062506050610 63
    0x5203030031303150102e0f44518964003d0680e06550816825200e20300705545800319010075a4a4a0074042002551140400c2065209900c0c006c0001213080c010041c1c1c1068581619004061504090f8160001c18101c01140d03420302070320380f1031000280181c00c00300d800492500410400303424103030000c0c9440c0c00240400e0304180304012001c00b905c20a07640c08003290303151500d50081c1d4500801242c45041d44128010800300204000c28030a40c2c00511018208480c03040d65440880a07003044203605251000c610241c002020900146105072105680848407504551040356544144e088941c0122015111a1411006420b20050000e810301180d29110004c0c101c0c1c0c24651070b1442c00910140202428556880c80711942002c0b1484041d8947c0c1c0000b00002e103842c81382410382d2190f0f1042c40c40c444c007a80c0d0f00c0e030301807400f4101c0350710006840040d40c5080c1044040c000384231440d0300248110800303070446120171200f441100342c030703050003480b401c03011940d818890244102c10542800403020b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 538005890 1250 538004640 538004669
    0x6010305010e1b06040e0402031f0b13090b0f0601170f101410050a0903081201050f0607030804020d0c0e0a06170712020f060c0f1b09070c150608030c010e0106 70
    0x60344e4401083d50207461025a14a01c1a100c0d44000381c41d2021480c2d15041003028286120a407180315423140d254a84141d03619428914180598011070b540d110008005035250408030344050a0ba91030b256100c00103040065500074816200820300030111906c40c1c04215880400c00440b451801013030003030813050718441045400780b0007d0b200a1856280c40100100132844001c010710880c8008001d64006c286e4540c2c0d00f40720714a90340b801c5c03400d010f4a401009604609030f07990414908490100360141e48141030f85d2696030802540008d801d04c2a284164020400314001d4001040b071405050100400541d43e8900100ca4a031407051088119483e0842c24040100c2c0d0400d00600034050380c1240d0100b4404d00c10000181e16010300f405412081c418100c0c189685a80000c0200d10b00c8413801401c907828540b5030811001d1a0110754030030004031244407590006030342c600007005140706c042d00481e0003510f403021546150080d150104ca20b81d107400491801450a1244101911103032200b000c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 538007140 1250 538005890 538005943
    0x1e0b061e010507030f200c090c07230a120f020606010f02070e0a200307080603011503030305190e0a0308011d04120207091104090b0d1119030506010305010e 69
    0x490080d010f0260600c00303811485590103200301c00d0064142d070100313040b4a1148070842056944c0c1c41030002c5030b009141c1000800c140440072404c0d1030056174018491201d400d000c00d09039005050542d0750021b1407051148031800140e0b00510143c0300d0015650700d020300c0441d240d0007454994080d18a5040c040384000b44d0352074030b40c08207200c1e06440807010326030425100c6031000801230a0100c0c41161410241051041e401c212100650040d4003603900c010407922650101400c943d800c948468000382c0715501040020700a030803003684049070005c10300c00c14010010b00d00585101642084298004194035401c05030003070314040c09000c015075a00100e07003001c6007900014802a202030051031580810820552007040603d001d045407039401d014140391800008403641242c0540d105031400c0000c9002142002140f003800d643d00400e004040d44100002e00560500b5004d00b0140003a16400210100c1c0e01082254000d41c41200001404080c080846080500081441c001040c08442c00d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 538008390 1250 538007140 538007147
    0x507060501271e1104030b1810180327060504050315100623040e070e0d11010e040b1518030d0504050112020c0d03062313091e0b061e01 60
    0x202554a20000013103050700140c40840c02e0045610052201080c04108108840c0140300e030080c105215007100c0360141056013400c00e41d81146a8911060801524200403d20642100981820241d401450404441070303000941c0c003070307801c072201203000080d0402540c2810000c00300036403459040b0303440034140003022103e9500d80d4850003003000781c030070303601c0c0300711860092010003a01e21403522aa40340d9403001420b610a208480700c0021a03220600c1d12114240719501d00d1915030b0004a40910044030001074412803038116000d80c000d656a0b20240098a071180c880f00360030401c00115803243c13000400502101008020140250000312114044c1600902510196002401e0251102010015901c020700a240701103150303205076582d042500e0380542c41031040d68814032884030f2070341c40e0315a40c240090440c184242c10064142d194032240c03643c0e520501902c0e100d10950015482c0f20090400310b1404000140c0391103440da41407104510785036203440003030301c1d04d0100b03504180880800079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 538009640 1250 538008390 538008431
    0x509030c040b040b030a05011b03060e061201110a081005120604150216080a1404080d110c090c13080705060a03050901092909070302100f050706050127 67
    0x50040b512400320100c1079455400248000d003001c2c040328850503203820040e01030700c010881031640500c024258028640329000340b034151a260310700c511071307515030000307000f907074462061412a155030b90020344400000007401012a81c110341e4a2140fa81440c060700c4411000d90791040e8030402185008122920010401a074040d420a1080740212401d40892000c0e100e00392031401c0010044441100704401200034049190340e070b988110186c071207211004150700c03450081d010994040d082d02d1002a00c035240403c455110b920544958014140c0031410300c2c941035a040007500c170049039050460030100c1c0a90003c203c6c5000420301e0300d140c00c0108105219080401d8201b51311540014041d07402500061819a40200f80f181000c020384040d40001c00d043e020f900440764200003250b4900d1000880c4001d0720340040841000304a80c1100344d4195101c90808411b0001c103110703050105c1e00e5031103094000e00e400714401000d07014a116680c20101e6803442c8104891802170008901040c10307085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 538010890 1250 538009640 538009663
    0xd05060a03050a0206030c0d0f0e1c0813080706020d09031e0c2d03020c010e090603030a23030405010902011202210601092d06020d0c0312110d09050d050903 69
    0x2c4551b661074294544002c1d1040d10104d00205040c411409051580e503400300c40c13098052001d84d817420400042110150b1040300401000801400100e02002c20102c40c22181e0340c4201c1d0350740d140c0807103640c44600380c4c0c1140d102141d46e15074a01180d000d158005403541c01c1100d14000e04d01a000b5482000340c000044184083d25016210b180e0258424503100030400c190038103481078100e2003441c60001e5031541380782c14180c000b034201b0740e00300c01a06004c90682e0050100501660500107000000c456000301008640c0c0d4488581501080c1c40c0340f040002c50159000300e0012a030560203000150071410006605202c042c410840001c0912000d000e4086419150000d0304046e11200012070300c10b44203401081090708c0000c1030700143e652003101c1600c2d9103110850000096039981c8160b84580e5600003510110701c2140407680000d00c0f0707040140400d03c1c034403400600c0c1c030003d4a01c11056000b9980190311282d880c20703448140a410001c9a16120682c40c0c0703540307802d1442c80400d445111082d003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 538012140 1250 538010890 538010899
    0x50307081512060a052202010504051302210f0c0301080c19090c11010506010e100e0319030305190b01020a031b0215070308070513120c0e0c0d05060a03050a02 70
    0x100d40c80c441e520542c10600000000e4100c501d80e040400c8201c00401080d1540710720189141503603111501d031030b101c1c00b01603601610740700d0030949498140841c95a052058201c410360800c0180160002030352108a200c0c480c042c0c0303420a143c00c0c0c2406000c0c490103000140303201c800b4801080502c80c0080c818106190036144210204103800c007003615226150400401d5174140a54155030a0348170307107117001c00c400500c000d010a88500f001500c881d001c00030516007002c1c01c0e100710248140510284035031560080c0440d04800343d41201c400300e000c4285c0003240000d880d43c041c0a0303c1884203601030400b03200e0780c10130041c050a0700700203550303071035508030041c10320103003a44e4501d0f08406080b447c2001d64000e095001150302c07102004101e5401900d0032070220720108007244405101d60305a0b12800002d900c244803207400c01e12441a54010700c03408031812580d0709800300c0d09a030b0080c0e01d0341c011000004100d48071034800e4900001d490009210500540c0345080420108400040d51702034070b031301501c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 538013390 1250 538012140 538012171
    0x1030b0a05061e0309010b1804170c03040b030711060702070806131401110913090f020913020d050706020706170f09071707030308010e04150e010b0d0605060a050105030708 76
    0x200158142c0300c0d16070b0411043e100803041007110b83c8190800d05448100319011500d8002d07418401d892030505441c0644808040489110040c1803030008205082024045909299803400044450b901c1141d03c10005020300d150412550001c201998108101e40050441c43d0b084c030805550354100181011042030700407080f02c044c0034292214811881c0301d04024030444412402c0003100c0d5003c5880503000c1c8140c1080f00900c05107a00c950b00c500303544556220302840c541d40030055000c1f00076100f02000125000c4a00041c1d68601015036030504c100041c0c200180340001c0a402d00c0e900354400d000340081041303031641c049101d0f00e40340d0340710f012210994034944929480f0361030200301d90050703903181c200340d14001001d0100060f42c2c0304030f912a9070f9000440e038903101314051140781500c00904d40c40e1944d02c0306c9840c03060342e0055040203840c00000641c14200e2800a503c0646c00c10302923a0b21580c800502c0054148400300202030134080c280245075003002c10b001030410500070500d654032170300b81 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 538014640 1250 538013390 538013407
    0x16110a05040b010e1005270306010f0602100c050d140402030705030d050d020a020708030f0403050c2b2a081005040308151c2102010c090501200d02030705060601030b0a0506 76
    0x1d4055900c40d41c02443e011208107c014005503440c014616024800d105a5000090b0500008196016284075034060601c0c0050b0245c04806407100c0c280f02410700c5801c1c01291404000c44c45070700c040401046c60440d49040a005250410741c86401c024000e07001f619000f148690450111382d9042e105120040e44d500aa41040b41040307c42e8000c00d0023030200141e002d007200224000740090b00c2c052425540e400603090208210000e014180444407038600da0b1441c400c0c109882c0c0520924000e00c6c0d400000c503415034540400101d030104100700d0304070a0f03405200460080120000c0d01090841c104417606250b2409444170710020640b00b683c140d054424045516004101860141c2c000e1541210003c203140860544581002c5040303074080c03035501101240c1c0305010350204500d40b61500c2145e14142001110705207020000b44d020042e0941c241c0c0c0c0303405003c00c4403404034007599005d5501c070b1074030740350081c01c0c0040580300604142c00c000314541c01c0d40c0c944440e1421250701315200c960380e8010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 538015890 1250 538014640 538014647
    0x19020d0f12060e090604120806090402130608010c1d0d08070b10090f050603010e120301090f1b180b0301050303030a0207021801080d02070602240402010516110a05040b010e10 77
    0x90f0b007143c002d03401c10b41c0510605442c0041d010b80181d205034002c1e079444d01c074108101d92003203003100c007103078804018800b003005401d00c1d0000c0700784010b550350041241da481e04451820b481d80c00c401c0ca00015050b4010509500074071070802c8054508940d036414000407615101028000c110003d06521009008558000c8a00407014000c048002c01840710f040800301c908010002128820702035401c10b901154070344400310b84041540e0308103081d0307421a420000148018090b29150000c8075586c0e0003000035004401d1044644420780e507941c0f041c0e100606204080302d00303081d4414401024140300500c4030782d4000c02980d03844942c040300142c4070041e07400050718112480c40c0290342201490000f00b4204c0011500545200440c1c00f00e5200079640e510881c3d550424000005a1001402d003066034107801c4042650083d005241c2103040000c04040700c02102e80607441240d5038000d40140807030380c1c1042111500100b800322820400b000391000041c1c48680507c07d5a8801c1078004c9800401d10700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 538017140 1250 538015890 538015901
    0xb07091a040b131e0311040504030c030f140408010515090403020a1e1506290315011701060503090606040b032e02070b091e070b030403020709020c0319020d0f12 71
    0x200d00c00001400c455400302c001c5031341041c04107a4030fa0920011500950400740a010300039a8580d90355400703074016407012540103030030001d0b80c1e003004041c1040c1e08031180c0c59009003000c2c1940500002d02418080000d001c1000842d201c180103012802c00c10010a402043c1410001c1d04a21f44259410000b910686461140350004040d101c09060508420070b0644c0100c0542e40e01c4d0b80d44c054844681016000641417042e658411404204002045000d1170b02c0001d40e91a0181410b44c00c54010300841603101009030481000183d007c010061510301c100034454216006540030422804884027090300c2d14411400b208102c140c03801e4000001ca80c00132500205c1c03003c0d050843d140c03c070381d241c44003001c4016901071240703100340c0021801c9036103c6c0030003001080001000f040f01610b03001085026410080c030a5055000d010740c0025540c401d40010201d059442c0c01440d074a0707800401070100f0840803480380341154864260666903642100c1c04001756a0a1309010140b81c00180d01c0da0301810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 538018390 1250 538017140 538017149
    0x608102c1c120204030f020901050301020f07110f03010c0f020c1f0f14040801020409050a0218010f2d11010903020c120307020409030507031b02060f0304110901030b07091a040b13 79
    0x41c40004d000043c06040c485200c030285c801c80e940c02030741e41d849003094241d0140100101505104101d44000601c02240149011b10060054180050700d03000213401c5400d08922440031030802e030f4020034410b50600c0f0742d04141008445d0514020400c01c140301e603104962858100740207580c0e07030a50b19580541e0340c030800201112002603907180c4503450030f40071750414440c050841341003001041e00c2104500030f86000380c9c02042e45e65039a990360b1004441c8031656414040a0109601039641c0048802d40c480c0d65052480500318882e01040304000c0615129802c541000c3c1d1421084000113a808a00c480c1a00c20858031705000d20715424440c0e09600c00c1d607034000e40c0b03e46400c604108058000c0c015003103a40c040d4640221000000b24000e0380603100c004c00952044042164a10615148001d140c10901072884c1600c620040808a0417004080e002030300d180342054100500103610926603409410600320072550091190300305000da00450103040c1b5400c1003c200208000c050034000c00050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 538019640 1250 538018390 538018427
    0x31d06010807060f0503090c091306060f031203052401020f0105090f0721030305040f050a030e09130b06121c1e0302030906070e040608102c1c 63
    0xd503510040c1a81d182c45500c20000800c80901000303503031900803070a69100e640200d020701103240e03500042000380e0341c006103409040b04c003050f8a07002181c8103201340405008480c001002d154203504200000d02015641a4205401c200030089140400c240c2b001ca04a08203101e00518006000140e0034a10b048031821210740ca490100300c0c485c2c4000400309545004901a5809280c0b00c1280124110091481101d1416140620800240b280c0d00c0240d10500520020319005002c0d507800d801c260310032400b5030001d20310a685a43c0d078504218666048024072078120b40c01c541d9541c0b007400040c00240340a1040020003100e4484120030b00c080c07110000003114032000800c0b42d440250001c0d81620420280c41030545800c0d140c94040e108403409049110010301c419520b10701708451043d01c0a0720b440d042904d0700000514000204003002c82030300e803100c01103900320121380482e402c2e10301c11448800191051100e80f1560f1004a01105281e000c0e4a48030050200c010040da0408540150304281 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 538020890 1250 538019640 538019653
    0x909060f10020a060b010c0b1f1a03150103060f0902030901020c0d09031a011413150b09151303030c030306051e040f0501060203180409021009030212010c020c01031d 73
    0x2000d82c0440d614508610400d03042001d0007520004540a0120f8640140390441142c0401d00c16040c5101c0d0580740108402520b201070f8840140800f504a0002c0b90310000102006101c00852040c5050380800e01c01e2070104400762500c1d04e004110a101d00c60828500e03400804503604110a404440a248491040700d003070090001c4000d106140910055824043d000384c01b10365481d40301c0455040320390585489003400c0a800070440d107840c018480a000f50ba4800c5290840c0c005140300f42c0040020036010394841039000180850345041483d00e122003401000340c41100c01c503040014080d02e80600e0f11182241e1207240c160014122600f080f6402000c04240c0e40d074203110092003010207841a50f06200c15010820350302c040e20028014500940c00070b1104900a242c4001d451400a03001007001c1010f4502d134001c542205030007101d400010710995018010341c01d041d070900c03c0740084840208002c10010030004e4480e505200a00d0403d034070786c41d408507150701c17115949540c071128030141c858 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 538022140 1250 538020890 538020919
    0x31e0f16090b061215120c03100c0c02151306031b05071707050d030c0f0e0f0120030a02010b061e130305030c0607021c05070b040c12030e0306060f060909060f 70
    0x9245c0e943e044500c80e9603c0e0100d085440c030080f440004100e4042c0041039501d500c011604044c0260605240800031445001400359507050121511088142c800c5da036202c00d6240400510302c1300c0c1d0014020f05040004200310420002000121130010b403402036155802c5140c506034441c0c54a080c075180810210b508401c0c0000410281400041c0b901c0401c407c20949009842c00e41c02c0c0164000031420050808460741090311f1103480c001814505407400c0b0780210354441c808220003809088581c0301048815030aa024440c0001102003180c0650070207221844240c0d407801c2c3c8001501000c44003003202042000c592403110040d46d804820749882c0c41d104050107590328811186003005201e03440c2580358914405d00ea1500000d801da5540e45404a0341e02c0d80e101c80e040c0079204681c0090400e4002440703041c0c0f03520b040134071403096482c001104d000404042c034000020302094410020715000421655601049848a181c1a5484045070342d51a00003980b2241c100350458110340042030801c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 538023390 1250 538022140 538022161
    0xb071b080a14010b1f0f0e040216050601050604081b010311160b010f06091a0c07060f03060605092206030605100306050f09032502031e0f16090b0612 66
    0x1101c005560b8020801045a80d0400003501030250120701c2040a00d26030310b441034071518a200102441781001010021f0040210303080fa4451994100701011000c080307401c000d001e11000d801410201c8005003090704090086840340802140c29010586991b50750105900a400c4000d100ca149020300c0c2e101c1050a41041680703e980a0840d1400810800072072400d5849000005940043e503400c90b4541c04e0440c084109030b540b8403110040c003010310280231004810003d4070082d010b15983e925440368043d0019059072080d802c070405007d000e2001c20401d4442c40454600424450003411690110981d890014802500082c05990425081028018a06000c001100e01c19181002195908010008410019249030712190010040d04001010003041644035600ca00b1207802115616800a1301e0b0130200c07001e5021303520341c40302e01042d00304042c84138078190414403000d030560800099a090203440c0703a004100c019a0741704103141141d190070041d18880300c4d100502d4032050030510000c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 538024640 1250 538023390 538023413
    0x2205070b0910020f03090f150a050702090709030b0609070c0c060e191a03090f010509010f060e060d0303020c0c04060311190f0e0403030b03010216060b0a0b071b080a 73
    0xd002c2d00d08111468112071002070151903048100e0003450400706000d0401c240c6c031108180c0282d00c40606407412104002120081403240705c10f4941c2c5546540c03600c1445010700009101d0030510480c842c040000c610050381240c1d1014044030428074666580c03d068964080000d400313044900100401314405401051200700d08a00700d851000b950507120100c9495280c5014400e0b100305a081c0c00110541c16402450300014640107542c2c00c00c904403000c900b1904225a034840720b0f03440d8180780407094568814030014086a10502042e46001808200c0351254200c004003015030000d07400110150a006100d2440001007090020541c1c03820428525145003c81c1c82c41054150700c0389082c4100c000204045034000351600342e56510b001d4014041c508020002e40034992544003809543c0d0f0300388001e05550b0082080c04140b03071141c0c14010102d4050700a644e0107120858014070110040030159104d04d548401c295610703041ea58503128905042d5444038200381b04e1b811052040000d0003000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 538025890 1250 538024640 538024657
    0xf09050303070e090c0c03160515040501060504110a02030a080604020d0c0c020901081c050706110a051305030613021309050703032703020d02010e0d0212070e0a0c082205070b 77
    0xd461a54645c2e1901190038442c80280301020303402000300c114900c14081c41e5004080c060416607010500040c5201c0c26004116030440c0e880e51740340020b0000c0c1c0b40502c15200f440060f0f075007481c00d0103001c2c10041e680c0d10507643c0040c2408021000251160750350780407280014280b5005100d88080503001404100d25007204034407441030600080303003c1200081c1c0414040805071044000b065030141a141588445415100c00c1c2d00c6d02201e0b09144805801400420030980d1103d60701c14a82072605022017458010510a82000e030501c1203c0c8541c1c40040b4803540c040b58400f00101c0c080142c01c0040c85484402010b0b0700501000105140c0c02c005600a2052100040640b4504418040242103c0c50100960010170140c114015500c03c05204107003c2c405401c0781907040749a000103294000001c482580e0b54045007050040151040e9000c0c2c00030315060083c4103103d040e60b0044c1040c000105480c0c400d00c07485045114424130741c0c081181041c0c001094170300756a180c1019034001c0d8401c903030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 538027140 1250 538025890 538025899
    0xc0c03010506060a0206061306081221060906120705040c210c080c0d1e06090b030105060607060c050403120903031e020d35010303030612150f09050303070e 69
    0x507241d402c0c04400c44d04503110b164013400300c940e603441c10048107100ca204805000c1b0350b06c080c04610100700700400742c440f411303000b8550707100c001c1c078805a8160b48003c1049520352092100f0b0140c40d480d403241182d00490300b1a80c3c080c0c0c414491401500d4840350f43c0c8501d0384203081101225103d40c010784540b12450350151041c90700100c09610720240c8060f0000880024020400141318068000c003400713000301c54100110303585540d1004040302004024808215950301c2204000c001c5d138901c41e40c00340b030009a00038881c0c0e2412100007045d80c012202d010345416120900d491417039214108442c00b45900c0411038003406540c10700100303c4a4a03000841c04502038444154448074402a1000c40c0c030025070052442206842d41110400050081800705940042003503464001c80b003c60700c0c000c51100300c1c0408030762450a0040954440723902c94010500325040040215444c28220310102c10725040108480982c011440002c24040c440030348180070100034041c0b060b51080420545000c101d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 538028390 1250 538027140 538027151
    0xb041e06031406130b06010912030e030105102102041b051305010e06071b150c120c0215070f0f060e010c08060303070f050c0a08100c0915080a0f020c0c0301 69
    0x11522a5103090075600da020f48101911a91300080481001c2d036445481032509080544e81e54450000b42405840114080b859500101d502070070244910b660218080000300145407908210310000001c4100c5000e614008440b80020340d140c5800000111840034120b83c034076100302200408035002000c0313152058004010000b090740c424002c00fa50048024500d5142c00340d41d643da1003d04043c00c0c15070030142c0c0100c20010355850041c030f514100945588604404450720701d0801024440141c03040b0601c03840e01c076010f000d030300e400d03d0b0780c0f01000c0010aa26510380030303420720a40180415000504280501801c1010824284c12103405964090001d001b40544000d0a0703400704022951186c01d90310034800800401c001c4094407007894081c1081d160b06030600400f01c4c95400060b04020700c158003285000003815524800c191001f15245840c42115041001840711b224050302c541003000710900114032034413019803000c0034880744900110359071041da4410a4458428208441c869480d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 538029640 1250 538028390 538028423
    0x7030e04060e0a050411030715110706090e040c0803030a0629160204020705031317070302010f0e010e0a081b010518090c120103032003070c06030b041e0603 69
    0x500a080680d40301c0c010180c142e41c0c030303d40c1c60002890010000d8400d08214042c0c058103132414015030300502180031140420640c0c01a028015088030b00100010354014001004800da000034114140c81001c1038000040d115400d0451107000b4036082020f0b00d000000c240305814426901290480300d002c25815844c070f0011092940e0039624503500c00c060881044035016508615010040641c40100010b09150003519a10710b190004078a407000800f03000c100f8013080c80c0c03005050501c0c1c8010002031122a0440c0d000800175100900580309100c0c034903000d18043d030700901c0076003050b0300007410911659a40d40a031030740d0f810256452540150990381c01107003d500c00d1040f110302c40000c0030744401c140e02e504107015602100400c0ba8603844010b11080c10041b0401a0a900035400380d130f45c1c00d40844800c0c08031800d64120181c00350840d801041807400107a00900000c04681890400080c480328400101d400380040300e510302c51244000740e1020458485078021400c0d81d020712203455001b20300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 538030890 1250 538029640 538029649
    0x90a0305070213060824060a05130e01060311030708061308030622050a0e03070302250e01120309050619110705040e0304090c0c0c030f02060405060f03071403060a0e040507170307030e 81
    0x581f03030242c200d082c0072414015800c1c00008004e40c043d49400020301c03109008901c5007100c103103070021030300b900081082c1c08861400304500700107050300070007411003400c0c0039202400c0704000840080848030003000150700c943d00c41400003010044448118404801070a09034000c00045807202c81c581c8c54140c42c0320b0144800026200d40c20b40c146c0040407820001003441e80e16011007491980403019051020801d07c040a0844c1d000700100901421110100c1c036002e03180050507045030307009007814041b40c5022001c07407a42c480340c00c01d1401c00ca2150701e2916025409d00034950885500141005880240031000000400c101e94019200700200801c19408a41d003451401000d40810034085041c004211303403400480d01b051000b001c4a140035035402c007040264010500041300990040304000d540e071f42010384041c00700e1241c0409803443ca06107000804100c114014111480c40a5001904200c003c00c40d00e001b804200107000c0781690820609a03a982c0704180440015011842447c214200b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 538032140 1250 538030890 538030963
    0x311120706052d04030503040306060b0307120e100513061a06120907120317070e031c0c050f0a02030708010e100c17071d0603090a03050702130608 65
    0x10655850f4540350039403049a800d10580700400b1000c100700307818102d5903000e050050009512800142d0344851950034043c0481d15a5030182039042e2003041040481c82d80500c9101f41c041262400040c01e83c00d6200c11803401046180004274245850144003900003e10003c0e0241849000140f00c4c0a002d01000d400b110b880ca60f215401c4507080c03240c2d1040c256088a4a644040b1910807601d809980d0035000302602102c1000703070003041d602042c5582042643da0300702d6020034103080500c20b07205002c0110740e41d0b603a0490100c0e5031600c4000c5966071580b08107210304943e504001100c252030440d1041d81c1c5c881c0402c0c241241709200b0114000303040b00041c0640c0c2d15404030100903240046060a100d4054014101c040c02080115004440c56003117100342039016a5541d540d00100d1500642c200c5d8900ca0041d07031191042030184200300452030000b0349012610fa051030506c0d100c03030031840807844800e58a184643c00078100a40400e441d080001c03101c1e03400100c050300200c0c02e480022105032004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 538033390 1250 538032140 538032149
    0xe0a0e0705211f05040b0604021804020d0603020a03150c020f03030411121f0509030c0a120504080d050a02062d091e0102030105031e0d080c0f0403111207 68
    0x2c80d0380982e12403504180c941d5280e200c1420050b01c04a10040c88100182e001440c4450083d03913507181030000f404100c000d51030340074005071421131404181503d44180110341018041c452500011b080131844c0d5250000c0004550180110841c1070300c0e8640744a1442c1281640301045103011901c94800c0d100145910005200e007024500d951160349451881c2d1041e0302a1a801007105204454569810030429004030621041c05404003104800c04080d00c0e0050502c542075030040c403000c0140303680403680840842d481003081d010860000300c15211400b942e845200d15019260900140c01d0308080241400303000d0f5400c0d660240e59140c4051300710000994a01c000c0034070034000c50043c6540c00380d400c0c1c1018100007180d21a1a041400e2015080c1d09000710007265004401008641020440484001d82038110010030100500210703a80b82083c407581800c200000010910140c2c0010846200601c8007030340e40e6840d622414000f01d0110340c100340e280102d06080c4420f40801d40496040d0aa8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 538034640 1250 538033390 538033399
    0x120f0e0c010e010c060b04020910030212091c051806040e09160b2b0c020703111206060603101d0105190605030c0703030609060f0f1d01060c030203090301060e0a0e0705 74
    0xa01300c4d00d0b10b000074403000b680140c0140d03003041003820320b945001841c1400049039402513511010070031450700e039080107007040c50554013503002c1d280710505110b1905441e080904d811929802c4045020420035208501180c202d00e0000340428007000c2c0e4050344e8415039441044411a450404228907a60704600ca0103403d850248012203880c041100e9001101d4220800c40610035003003503154080301c09207200303075001d80d200701001c10420140311180c80901200b19004a001c084400039182c880c18000d1040b41f050800100260404025200c4440504803125104030800c0103081c0c0c1e0300e5075003400e001c0c441c41900511014440440302d80400d500303030f03542e0781c0d82d25045488194a80c078031b580001500318241520382c8004604a011482440c006004060b800c00c0ca441c90015002c1030700203d9001803041c00d10040c3c003d104003500f45a900d0450700c0c186000620005142802c0f400d601802c3d490903459401c1010014044c03e40c0241c0c2ca01400031607000304a000d15510381142d80b501c0922541e40c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 538035890 1250 538034640 538034657
    0x7050d0c030e01120b1305090c1c0f05190c0f081b010503060d02090f01141c030c150f0f1107020102060c0c1c0f0e0901060206060907120f0e0c010e01 66
    0xc0c1c0d4825608045130b45251880400c002071044002800218811603000c1400e58a00130004c0944040052005a410a84900c1503074403655000311100c41021030054418440b405518013080400c004841e00c41d030902800c0c00c80000f041c50724004006840c42000d0181d80011070101d000800854603c11540030405500740034681c180055416800080002da4008d070620010f07000341c1c031030060540c800c1c144102d080015606001d41c108204103609121805089042c000c1007a5140a90890a03007a800d410610490300c25840c0094400ba02d058880f03c01606050301284004901d4001c20004110103200b80a030711030b08280c809041c060000045d00507404071010400416150004118a44002d01603940f03030616111a220030034000c17000807001070031400c90b4212042e40300481904560044500305125450980c000303640702405840d0900c02c0300784002195040740215186100380c1c404640a0100000030f881e0b00001f004001d001c00301174013400c4000a52980304051030f009031201611200c2c07a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 538037140 1250 538035890 538035917
    0x3030f0a1409012106050406091b050405031018293706050a08070e060402270f0324092d0c040204031103010f050c0a0509010915020307050d0c03 64
    0xd407400104140e04e0f95a4540010032136403564001c04001e00144000801c02ca40a015805602c480b103901d0a020482c0c21302041c040c590300414a41d5120382d481d1000f242d042c08085801e1031b080d034151303002031000b0300c00780082c0c000f1a045e401082002d103a030203014a16680c0c13440c0c810039504c540340d541c40114155050a03020b400003c1034048138040a40c500081d4280c0710710204040c034400d60410645d540c0802c030304100c15402c804000f503002405a4040d41000c0b040e503503e1031040c10342c0382182e104080005c03c200c895100e1500385002a0802811104407010044883e04141080400e0481908848000945800c8005000300403030740d03240b18104400724042c601d1104131083c94a02002e40c014140e0288042d41e907400580055070085031a15588034805081500312804801140c8246082c0b01c100900c12159000780d601100c0c00b070415680e10070b11000121004034158010004803000124000003495000020317008082c0301c2e40c102c0386d80e030400c0741040c5c1e5904040c0ca4000c0010303111280040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 538038390 1250 538037140 538037177
    0x30f0c03020708060a0203060913020319060e10020405130212040201050319020c06271b040b060d0e0d300b040504050a0b0105040b0f040b010c0203030f0a140901 71
    0x40450107841542e109586419601d801d04d8800d44540348816004420310010341303004084950403c0d0810b480d18900d405a5010079241e802c0030000c0303448030700003412040030312201340c0140e0883e140c0e08041d03d820058158002009400501550713028218140210441e942c0507c2140e000f25044900c001850341c803a4011116a0300090000300d508615622082d40c81c0810b0028118081418029000d1440c02640521540082c44541030301d2030300d95200317400e0704000440e80021103c43c10046544010b0400e000c5006001c003031040c02d030002000280d81000d800a03521030b000c01c296140c01d07902d14052010301151301c844c402000018130701240e900c1c1c80d1004a8004c4001529000310400308a19100c803000604a4101312001e031580d0304030340784800c100102c80d1031a80c05414212002c000e03500e8800082000354454100c0b01c1d00941e03a031004500141e001c0c592440d0080c1d030080850703950300703001f40071002c850b00110f90a00116149206414031071598106885a00e00181c0d10070034030184004052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 538039640 1250 538038390 538038407
    0x62d0403030b030703030305011d190c0e06070302031b010c050a030902030c040e0c180106050703180806040311010b090103030503061903141e010b0102070b0a030609020d060305060a09030f 83
    0x880038160b807039029078010b407801d004280085020351000207043d07150020614100000c0c000102c07030b0106800401203001d94102012400c504c1903000045e5a10100c403094500c21503c280c500c1d4018804607403501015030000050010207407074417080201141c1c90f14800e00361a140c2461901242d01407080c4900580700b42e119001990008044038182ea441e100810110f0320860303001034a85c0c000031004421420512214091824149100c03985507240c44401000750103034140080c208003041020220461442c0050f10150035143c00344c800500f0949000740454541d80502010341d42401d13101a605d01d012140c0c503040f60b8158480310326560b148030801010f81d2b0300307400400b40d40795a002c02002003003c42005001c3d140074000205000344040c94003014a8221581210541e1b04085060f16141d90100300301049406442200c0d8070743c00c030103000385c0190036550408405c3e43c0c80403501d0255048903811110485e4040c0c0141c440a0301c8840f0000e0075180481c1000e0040b0b00c55188a8950910541e2070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 538040890 1250 538039640 538039643
    0x402070506040f0f020a1203180501090530070303090906030203070905042915030c06070209100e0c07020109060807080408031017060618100b0a05071b0602062d04 72
    0x10444060801d60016600c030b81c481d00400c00c55003800347c80d90109500003002400c10f0002c00746c030b000000e18047c002401110341d4041c0c01c0c040e00202d03000070103411403100000000020524620100040705070b2140e1340e100c4074481034001844140001602c0003d0344121415240c019014103002070270215010082e00c4050310480d40310008100c0c0390100c0500314030005103181c4002d0002c905042042000e40004600d258251281d0800c1d6074400a07907585204503020f4642c103641c580b0380c650f11094101c4100000303038410a80502184104808007210070010010703135200b41c0f07404980584800c1c00b1a13030708008852200215128038042400b244450000d50760141101b140385040f0f648400f1420320711441d82e141c0c004175038050011b04c0a21f10f09044505024900550580102e01d0103c1074294041424450003c040c000020b00042a038407035402c442c0a141c0284d5014081c82c545201050780c481c043c460000103008500100f1320018071000528a0101102c104400841e00225202800c1102800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 538042140 1250 538040890 538040903
    0xb010818060c1c0507030506010806030c0105030109050402040e0d0203030a060b09130b0a0b120603010e0c061902012d0507020d05220f080a031b0210110a08190e0402070506040f 78
    0x3841500c84040380209442000aa43d007c0342900303141002401c03114016008600c2078020800340909a44c0c820f056a044421912020800e0340340d41c00498006c1c500b003403841616024045610b05c04940003c001d6000e00c14001080110380d542c1c3c02c1c0c14500c4d010b0145010b52010b00410007001d04007051b0400081c02c0c40003004480107540e96400b2100580c003590102c0c05151110301040010316003845014181c1030902c018000c406d5000000521500c24240d1403402ca048845074480034078402d41c8039400600031490761b6607100ca0881d5080f110100740201d1400402e0810300058001840440d40504246003a1107a50603c944512400c6000c210318510b0403401c0211080094881050081c02c4000d0803404058041c11a0b14140145078400240f4103100d0010f91021282c016100c04146601c26429407620340034035500c41380d0140c146000c816001d41032030700208008036248070170540e03166030806541325401c5000542050000768061104082d00540084000501180761000803100152180b81d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 538043390 1250 538042140 538042177
    0xd020103060b130501021516200a0303020c010b010c0510111315020f010603020904062d05180604050601090b03070305070609140603040b0106030b06070b0a0b010818060c 75
    0x1502c940068003c05210708120701c80c0341c03080005503014042c0e160034101c0680c03070b0f540500e48070520f07101c0d400c100040c103401c2080300c894000b240303080020000628091101501c3c0081e07041c0c10003e0194010000f040507a500e00300d22083c81e503015011103180b0301d60010141c091703013440e126038000600c00018840c861580400548445081c0318050320301501c0c80c2d030948242140705410080c54801040805651a85040010b001580c0d9038080142c1c09503100d140402c000203240c1804000b8121082a005000c6007800404024070003034005520682890103d11404819807806a50b507140a03513000e042c4c5c2d080310b0b00610400455810070321142c1c5000e002ca074042643e03552014505401e41d40000d0005040900a200e480c0310710000c10700700740003200c655040d414a41ca902c202c0c2c040c1031081d0010b0660310203010880d91545015210b0151b0400e613811039602c1c0c400103207405018140000c50010701c2c10400a0014100034500c18242d44141c0014101135540000b103410681c443d4400b07403400080c08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 538044640 1250 538043390 538043399
    0x109090f0905070803071b1a0a050c16140a03080306041515090e070507120c06110d02030603150c04150e04020a0f020d05090312070204020f0301030b040b06090f04020d02010306 78
    0xf040114002d025000c002d40d6070383c00c0b90506915001e411458064480c1c2e1440c4200103418204400f80d41104d07080007002d554555044c0142ca60b4495a000000580180700708140848002c108410841303100c0f01000b52044488802c00c00350345900c0c0001040d000c000d01c04541036060a5010000c4901c005604100c0b481d01c0751031485103460903100040020382d149030244030301b02001035196002066800d080342401100d56441030901d2440001307008101c0e0608088080c0005a00031421603d10007520940d6150112601e0029602c11100d1500038419080c0503c60501e440312400d21540000030094101410504c00360502d842032447c0710100304041d2080800c07a0344910003002c4e00c84490b12a030050b4260650040d0a04d03410b0786212041c8003091111f000d03c0d40300070600c000c480c0606c0c0441d59842e02203200280081c0580c500c016a07a2001000200422078140d0b28240551f014080100890782d4030403c020801c6e40c01c1303034000d20359005080450b0060510400c1c8039040d030301c1410049101e903100e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 538045890 1250 538044640 538044643
    0x6040306110d0e01090c0e0702071a04060206010f0b1204060204030b07030203040203010b1801150306170f07140d030c020f0d1b05040e03030609130f26090109090f0905 74
    0x71086441c0c4034001a210a00991512800b1104488100281300302800b070384072034582c001680300308003900c115000000c00203442440074001802038032008540e524540d00d81040c02d03420600414015100c0c600011a00b000101e0a00040b034220604041c0781032280b003408144100c0143c801ca40242d02400080009038110300014401e451540d0010b0301d92030203004140c250758030340e030b00c260080302038102c00c1c040100300703404840c1034855502084d4480c43c503c1500710300400641e0b10140609041d031110003c104c0740400c03a00340c4100404202c034185a21507080414100304482140c0d4000b4004400c100024019020201c4050000342446540140400440c0401c001c6020441e082200700c1d00e0b0600f070410882c0c4100140100b903400f0003600e44c03405d4105540b4400507113641d22909910002a814040c1d1040283c003036540580308480750b501e246050b1050600e44030340d2088208800c002c207060101c02c0c100742c40e070084050b91188001032800764100020302005a035070b03070303510340304d624880200342c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 538047140 1250 538045890 538045901
    0x20d050604060b040b040b01080f0601271a0a020312070516111f02070e131203050601080a0b0d030c03050f07080918011a21070305040213020f07030c0206040306 71
    0x780902083c032004090400044500e0120703180d00c01d519101c0000c2161340d11000703041e4004000061a2003d444980050b2449090b8085503040080e00e65000c800e054850460303602261082c02e1021403a00e840c407c58061070240d00c071034000583c4240302080300000368040454020142c0d040c40d5162080319103444800d40b4100743d00b61003080c808110300382182440c0100c1c001c1c841e032400c0c00d410139552081c0e000352204240d1040948030036004c404a440400310401c19899035510244c100c01e80801404041e026100403602076000c10369900004054040038000c0d0148200002c100420b02c01c1113540c00c0c3c40c4400418025001c11030284010f1070403107240f00c0101a168010340115403105442d8080040740c4100503880186280500c0c01080f800201e00410b408241e0004800c0c0e40305d184086400c2d5110154101542500c1c20100c2401400d60f05944030601450080e00c090b0381008012100101364032500300c69128022041055001091007117804280291000340400e203401d5880c2c50700d106544 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 538048390 1250 538047140 538047143
    0x706021201150210060b0f0708040905040c0e060114190c021207030b010504061520030d0504110102120a0c031202030f011d090d050306041508030a0906030b0604060309020d050604 79
    0x6100003240c00d40c0402c00b943d9048001355041c001c150a160035400c41d0b0060f4000d0380b03058003000c640c00c0c042185540649002c0d14a40404000a141a0412604028051084ac500c00410f000407516651245417540307403004548043c0d41c50050a22040c5c170f84508503201c3c3c1410440620034101c0140e6814103001d220066400007071800c0c4c3e05500f0414203418060380814819881d28400308000c6a203401c892110a40724105014900151519400802007103106e10780c15020009503004a0682c65210358065409464400309080d40c0c00010f981d0303000f078600b007040d600784d040c0312242c6107620a0240b64039503442490100341200070841500c06070380040e600c1186100c500c000612a81d0648003142c2c81c0d20700c412484584600301566003d4641c182c8281403810020000002600c9850315040500e0801c50946507503503150741d034544281c0b00e40160081000190300e100700003d515200c0d024103060310300c00504076440c0520306038042d0001c2c0240c0b20201e800c4842c400405010070401d109071449035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 538049640 1250 538048390 538048409
    0xc07020f12030a022e050934050402070c0e090f03030138030a0f0e0609010b0301150303020615030f0d021c050703050304200607030c050d020705090a020706021201 72
    0x1541c0780030000c0d040010f51540b140c0c00010708403030850905c031000c0f20000c00d840510320001b220380b12107224a04141005070030320348070455088051690b40c1920343e10b610701c0c992100c0c807410b1151070300d0801050780304140d00548130764801c507828401070070719030001504000654100d03072408803036003030a60071504240d008180d051000388207020049410414400d80000d2941c81984a030700740320b4110035600000e04028251070b03448420300741078100c0360f01041076191708104590316447e00e14202800f070200d891189000f9401e00840d4542c25440800303100940ba495000740103165599140501c549a4600c40709501d48a50041010404414050700e05002d08580c0070f0320b40c961074040500180d4001a003540e08006082003a08082507011094076000740e8008024010000044038211680c21020190340c0c1c0b01400048031010140c02c87c84000c90a44a042952519100b01c10140d0722201144038241c1c101c41e40e1000101c040206a0052034aa88562001070800d00390070200000500c0c01d802c400002c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 538050890 1250 538049640 538049647
    0x11116030611040b0301170c060c061e19020c03190807110703230c060d0f230105130e060c041d070509061806070c1503090b0c07020f1203 61
    0xa01281d4011400080180c8505034a010310340824401103210510a88006089108010924100500482102d141d001702000d407141840344003030b500c400d01500c00c0c0c6040c141c0c0c1980e85190340c050300040c510400311481000300040320045001d0113035014808010941c0400c02c03010000074039922100d0100310741c590354810340349005076018094519507290003034240d0045a0420002c3c0d5060b460075090100518180014180340c403140e454840e01c47e43d6aa840035010400101e5448150f0020900c801d40312010301c0311001d800402e000320348500c0074080d02441e15000600c09420b0410a40e00802e45906001070031402c0a8400c034100b180903034800c83d41810000d03003001320313003072444c00500d42001009004515017800700000d0864440e900320640071311030104141c2c0f0f10034140c0301c2038a448900544140c0d544e80035441d0414490345c1500407a040100c001d013140002c036100340324481c2c8a41e030007001050151a00344c1758031400d812002c4102e82c0f2504d0803401405a445660100d400800c034140150b86 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 538052140 1250 538050890 538050893
    0x204030b16030213030f020f090c03091605060a1803050a11040e0319180f12210914060f0c0a0311011512050f030a09180908120601111603 61
    0x1c0805100081c2003500600021400f090304516103002c40c0c0d0301100201c1c88004138804100186a0704901c15031080c00070041201c40c2c4c04010096101c0c03000b403000e881c4141c3d03d0400e44070b0450040d0048540000e03060103510011805100d15105c5c020100c070074240c400b0350f00c0d41c4030741c5010703280c140c215010286000d46010701d040c240036041440038030101a5081c000505400c1343c440c2e10255502e0f040081100c02e00e00d2015207285284003501040000100d500d4503a00b114003030700c003200000c42e2811424403107812004421f101c4c00001030550398074218500e1801c600020722849001d0101c2d4800700402a03a1070340d03117803c00248840b040320030140841c10250f0801400c081c803810b20404860741400c469020045581d50190199444116005540c006a043c6607140054414103885148400100c07145803a4000000908a44180025034600c55440c04454251900c1c20001000242c05012400d108143c0c40c0703015034021018075180012051801d0002c0c07030518042c440382d0103400c06600900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 538053390 1250 538052140 538052161
    0x204030519120c11040522061a03031306030b0604050406060e011805060a030f0f0501060207030b011a0304060c02010e03040b041a040506090105070501090b07050a020f060403140c0c040204030b 85
    0x141a51001c0c01c203d20048040d44608a0090001e100c0d00d200710750f508001401e0451140c0104031110300824901a502201c1c94054001c00319104030104607919041c107420315103000400c80e140c031100024003015140c5410f4065015004491540b98002018000851180c41742d2080d1001029607030b6540c2c0705c07500080000351414000c0e4420380b600d582402000d001c69252a8112400c03a48030340b80005003401540c01c1c08000700b00c55415081e82d14104400025000e90009035203050b0307030266040c805140d90329550892a4030303a1180341562504148005004115550701c0704441c100c0c14000450000100c66010b0700b140e210f034010451050000c07406000318064440042c070342c0d244550082d46001e0800001880034003e9200b09410050005580401c2080a420200646602c03d10511141c10001000fa2031508083c6040300140b00e44c007454188500c0c0060402d01454040d200c10898039201982c0c41090781c01040d12446510070041e14841d81d842d06e02c01480218040d940c8528107050030711080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 538054640 1250 538053390 538053413
    0xd050f1003020a06050702040902090103112701031101051306031a03030306030606040e10020d140f040c15090b04080102040503011b1b240501030c1d0a02030603010204030519 77
    0x9810850384110510050300c0348045003054820074100180c031111240b0000f405000f03241c4009400042a80000007040b103590068a00ca00e400c40300c520340c0d80c2199101100f02e9682e004480000040c860041010460100a1044400061601381e1900074407035882c508107074159000d03100103030381d03034212034901c03003100d0034411300104118095491424200c0010b03030707104c0018000d40d200e0740d500e0542e200c80080c1005541d501e800e01c2c0805544070441050f900004051800341c2e8000c85800c0c5001a42d9448c01c0e1090300e00c035550002a07604000d0800b4209413504041d5040741080c006021000704501c01c6a00c090002007030601e0002d070761380b41804249402d40b050f4500c0036002043e44035201c86036917045500c480c1401a2201200c12202c024241103a000000c01100c58482800b44030054420f46650081c6060343e0141c02c01c4083c860703451400f055070302c45852003583c2e203030b00120201da41c41901e40c00031038000341d00400240c240740d02d0352503050411010741130380d514010b1581d5412040000d0351440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 538055890 1250 538054640 538054651
    0xf060201150b0c010b0d0f06050c430f120905011b0312020f0c0c01050414210f060411010504060f03020703090b0309030703020609010b030a02090c0c030d050f 70
    0xe018021020741680d0540d5903a014151100304081582a42d000c42580f2552000c80003d05101da903894604020306d0110702c4450580b003840c107000c00160441854411030b0380c004848102010544060140404407030b00b110320481190161400c5d004200086e040b103070780c81c0c502681039094403a110b0320309040c0d1091450120030900800910030000c903070b0010b9a401071071010b43c0c441780101c070441c503003100c0c1011401c0100100b54030100c0e07810a082d030080080c00d20001100c0403612201d080000542d4240581d110310344c20940c00086440300707418008a00c0400381904c0c611940c4000036a04100d0a02041c1c0e00400c0b00c44d408001000144903140007981c106400a0820600e801e05000d801841024403074140c0c030601d500014080c0826115444071001803880410554503402d0410030305869a2105109500601c5001d0125084207410b00c100c1030303e10300003801400640c0c825400c4c403c024500400c03d0240440032b1246c044e540031f0500c001e1180002488001690746840e10301c502c0000005007a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 538057140 1250 538055890 538055893
    0x303181709034c15030302010e0732030a0b040b07140729010f06030b0f090406183806010c241401030218040b010e07030b040c090f0602 60
    0x140500c40a032441100030300c46400384103003034818841c400d04031070f9004811101d0311031500000f000a81862829982039074800e6000380301d03100081c2d4496130303280007078010a100c0030044c62048100d00104000600d0340ca00e402522101d0581c4000020b050844032442650517201100c1017100304041444043d0b803110356810009400030f8900c0924402d4042c01c02c004095400384155a10720f440500c1400c2d2038680f1642d6601680d40e1924201000c0c424070b41304020201c0d04002c20200d862030640c8407040b00e800c1c050185480c0b80d94944401003d880d8010304c1700e1200d50411001e00c04214500301e12045440351801400490b00c030100044090000c000704810301c0c6410505120441e80c0c42103c8424040d04845440ac016240710505492200c045406036101c40c9002041c0090209039200075040b01d0089486050700e4041f00c03402003d0b25402c48008142c10392040041c03049426504500350000c00a01d4001007641207a0041703011a80e10240c408041201500200704000d001604800688010310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 538058390 1250 538057140 538057183
    0x303090b070b042907020a021203090d08090a05060a031a1c0b04060b060409092d031413090b040e0c0a05040b0f03010c05131202010c030318170903 65
    0x4540044406000e0001031003204842055010044844d030303506035041010740c10000508007484080d580b441152070890184075000c0d00c400025030048190384401c0001703020454680181c1c1e0350954164401090f203036100542e1100413501d03858242c080c1c8103440342a00d00184210158089949036034500c0c00310f61143c0d844813400003100e803149540c0301603254072030a82d0071142c4551030090080e110082d0125000400130a001560960941140c04140d00400100d1103c07024218a44081d1040703c2618194900c0c0d008140b0009103e211000c0c11440d5481d04181042e00d40000124105800c0e0301038100c1c0c81d01c031031411060780340512440014021340001440c10000800214071111014441e99203e281d450b050345150f61502e00038041c8000008000708404040310001034840d410046080c00e0204c030800307004c04d0380c00030b111276281d02c1c54050f158650380c0601ca0f58104d01500d881103c0e240341104501d09800016805180c110316451000107294a52102d0300a240c030b40303055200000709070358200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 538059640 1250 538058390 538058393
    0x3040e010e011a0f040603051308190912050304270903050702013c0e03160f0f0503030d0f09170c010b04020f0708090102190501060501080108060907050111010906150303090b07 78
    0x18017141e04980640c10045600c3d03407005000c00208030601d001500200001031340c1c1c028001482100c90410800d07460b100e007074503142c000e0500ca054000343c00500d69441040b05021080c8040440e0040020318030401c04090100400c44059682a100c00c40101b43d01049010071580c00074662800305201c0d5852101c0a03400003103482e40c2a400c075280504800f50450b11581842c4180103000d2410400340440d800d0070749030071240d942103826125448200008800110300301c070641050074101c0e21300600550500001e048440002d0282102c20b80d9910750301c540010014100c04a4003044c4103184280c5502d4841d0003414500359000704001510079481040070b00c00250482042e1425250880440350710b902c0840c0050380391000609032140c20003424a0f00400300b0405411000503a40c0a0340c91800e04e9a81d50900303913035100203590041864210800c14040780d44110480d0080101400020a4a41c41f0341c80c0d0904807001d0942c00748601a0010f0180203054225100200600d01201034601d00b6410b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 538060890 1250 538059640 538059667
    0xc05130302100509030109110f09040f02060a03091e051603050a2909060a0f0515040e030904020a080f011d0403080718060507020f0915090903040e010e011a 69
    0x9400000d20410318031051040c918811410388140501c05002000003400c20305049520300d640d1100540320328200e031801c2506040422013540590340c03083c0f2400103202151308001d0250440078004082594659840d004181c007078005038544007694030308800040880c1002401d00003012345075121000390210800000d903001840d1a200c503009580c0c3c180580c01d4407590148455215040043e2411b080c00b4032200c0032700410818000d10850804102d00c00c200c59400c010b407141100c407121031201c2c0188603000c604042d08030b03103502c0000c44d003580c2c902024070000900700c0c0c024015070400541c11500f004604c000410210f805408900200c403810f40060a8114400030001c0c0b004003044240000701c1c512600441220b0998202c0a03031145140d80c542000030050381000308203078030800a003100120242000c0c0102c5005002d01801081c10031014018002888800341c100380403803008120000784080f491001c54040d0021000ba0141c651622006200c4e5815020030f078028403000b041401a085c21 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 538062140 1250 538060890 538060927
    0x6050a0602071206020f030c130914060415050301020a02030d1107050a140325021003060e0106050f070b090a050709020f190201090c030b1e010510180807030f060c05 73
    0x94210311100c030a115890000c010b4000c0169440406c0004020f0118800c40c29001d41020102130440c11500f66440c0f400500740d601400c1184c0540d00c0300400700c0e40c94100783d08030f00d46064040c01d0b041021981c2d0008207089074020000c100040e040440c02c003030149218000c0e1110310703241e21b003030500b8508562144e61f160010490000c001e11640352960141480a00940d1101c0890241d61442c08131b03c061900e483e040c600d4403c034880c4607002a081786490107481074000360360941c1190011603080400c150f42903070140c407082d8081403060000f08000f85a01e140c5600c686013540183c0180083d91a0003842e10b52590001c4100500604c26920140001c1094802c00c141c44407921880a00c41001030340108022413014181030011400441403001d83c10000d1f02910640d508072050354484066403401b14028010b066100b00c1100f900030280d80f049200e0800396032801c1c8030194075596815800d103402c0051340112035074600240f85000b84802c034071811100c4100d900b015441c10880070603c071350801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 538063390 1250 538062140 538062149
    0x2061b091203040605030115030213090b13050405010605040c1b0b040c12031d060a0c080f09030a21031a0907112a010921110402071506050a060207 65
    0x1100030a90304415a1180c0d000740c1c00e00842400e5036074490b25003500408a80c0240201d202d110134070b02113000d00701e200344200c2d4010f01e2050700301e102aa0610808001a02c1c000104d1544110760000d8042002c0ca58400c4d81d005a100700c3c00001c003641b42900b40015500c0300a10403051000c010a00b10480c0c1c002c10f9800119581311700304600710f0b5954a488581e20506401100c03c8180b05401a420150840d00c1003200f07417140000031007440000c00c2082050b1098071440c0000030b00380302e0303004001a40e98015003802a100700000d42401e00203401700b86422140e05082e180e2650039850740c100c144c40e01c440e54884e046039107001e20001c00040801940070103140d1001d40070300e0103040000d002c10300c55001c6c514040c3e030400940b03008011660140c01000c070011110102c001e50008080c80560240d85c80804540c00380440140e801e00b421a01c8980620b1032600703507661709060755440316a03500d600c000c00407544154198100f8080c007007281d801700c0c0c9540e00010b000d483c1240c428081c454000032010200c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 538064640 1250 538063390 538063441
    0x90a150e07090e07030b010e12070605031803220e0c0307050702040f0e1e15390d05090607050912030d0e0a021e010f2601030b01150206 60
    0x152149001101c02005a6101003040c0741a00f00740104143d06030441a0704220903a00c3c4a44c0122040c1041400180301940b8041342c0e010143c01c000d105d000d0b2010b554041c10300351901210300d4030425500e00b581e00058107440402c80422010445c003480c801400c014200300d0820101c01d141c14004800300b07202c040d02040600401140d80030071962941c01440c40e0001c91b140c203001c2d201c541203910380d8401018031a042d4013020309040f0300b140440007569100e84c6c0200400000161547c044110b840c00b201c4c545610f42c0c0da981c503034030115942c0206d451121054041c42c0700c0e82d5010300c0400c4c2c100b1250702030580789543d04001c0510482707a501a0546021321411101d4814080f80c0c0340b0071500e103214000c8100c580905000c500c184410340420b45c40e0300940251540a000c01c048a10760300300009031400b0a0102c1c150f03540700e2044a11950ba03402c0d0910682d1507402c4456403a580102860000b40d00854614000d20014400d44e10320300811960210725000400140c2020201240b881307a02003030701c8045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 538065890 1250 538064640 538064669
    0x21203060415030606050a060c050a0201030b0d08030c19052b021204110103050906011a0334110f03040b07020a030b0103050f010506090402060a0c1718090a15 70
    0x2a600c903444128200300050b000da80c0c2035901c0c074042000d07201c5407103041e119103010030001071598011000d0541c6107034098040d0200180340c0c0d0054006146920b1950381000045c081c10000030510342c001c600420300d0500007078454032505039114107408417000100c10840c0074003100300c0101108160000c08100580c2c0300880c051a400711720700a014030b100100f0f102c082c540a100c14002e002a410b182018280c1e000c0c041c41c1c1e0340c0d080e03056444400307100d00900119180d4000001d90071a1002d1900000e0207603080100c10540854407000380c902c0003002000003030320148001c2d041c0d000303040c0f4801c044042d0050445040170300c0c185500d80c000d83c407980d403a0145c00201d150440d619548410051036002509020303958403030400982d18909540040c20940c03070f29001c2003c1c0e1905038030b06807145074024449071a0008c0041c08980300c0c0c0400b04200c502da44205c00600d0041d42e1140500720025a00c0c21001840144d1404c00000c00e1014241c0c0601c94540043c0021001151540005580700307448450385 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 538067140 1250 538065890 538065901
    0xa0c17030f0c01021e0c06271009020f040902100f02150f1e0123310e0705090c090103200a090e0702120a11010f0504110a150c061506020a1a0601021203 67
    0xb1007120a8094440701e00840b414403427040300c0c603846018117074001c0c2d400101d00b0703280c3d130180011106075102c0650300071144007540d28602d129105540c141205481035032608051120710102c4004141e9220070820081230800202054291803042c4012003101e007030880e5450a00350314031040d41e1000880418036248a484041c0d2500d2120b9000c1c4004080c5402800b03140420b4641d02403031000402c0503850400510980d04040001e1403000c0d03803001840007515450340716620455502c101d82030360600d0b0300e900b05800031740105035812082d841d2007461107590300c4a0b94401845202580c0241c3e02a02c420030500024580c00218254041a40c3c8866a40d0300c0d00b40c401550b0503604140d1f0102d041d030820101c030351181d144da00311038083c0d4803680c510500522110b08110b074042d5580074150340c82a0111601400c14450071800400318082c1c42d00103a188500c0c0b000200b26003650300300d1409a40007820210800907080610000407201d0b9182d18914106440001c1d02c6105409140784c0301c10012010a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 538068390 1250 538067140 538067191
    0x30609120e132f0c0f071a0a030b0a0e090d1107120206070516030c080a020f0f04060b211e0406020315040c091401020a0c17030f0c01021e0c06 63
    0x40e00f4500066412544100e00407180c01c150f070003440e0346500781c00b81030600781d03003c04001000c0095499811700d024102c44407072038610f82070b008260344100f00764803002400000c0c0c4880722000050315200c5400e1080d490080e018914002030300e29044200840100464003005010945030103940380c07010003402405180c00082c2d441c8c000c685002d0014000d0100325084c00f004c003c50081140d1048030755061459854640c191078041c3e1800294220b0f43e18161702c1414508030511100d00c010003400010072a0700c58000c2c410a0700319401103c0000107035982e00981c4403c2c950a00d51180905800d10300c0c40d0f0750b200c0740814841c40508020121600400031a21f00340a0300422068000041c01c1040140052030000b040c0c840d8034807a0410480910300c60701003075440400c082c40c1840d0003008041003940b5041c10364140e0000d690201700180024010700f4840ca01d0b88004100b40c03482180050786400907003840c11100d20780c01c2d02074605108100200e42d030021010452030380c8602405120510131b1860300400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 538069640 1250 538068390 538068431
    0x5070203031201051003020a02100c2606040b060901090b070507090c02061609050102031605100c0908010507020c0f04230c120610090b070804030804030609120e13 72
    0x29803502011402e26680000c9162460481c0c000711041301c035803000000154100d20540306e1041c010380252020328041c0c146c5030000c0511900a160407645205454800259075010300420005401080107000e02c0e80341c41c3c003950284c00403ca03000c5142400c010b00190a1000c10f02c180560360801092040078448244403510061105007801d1082d003481010003900c2d05030031103142081882c50011012030f00c0c40391000000b600c006030000c2d4604011090417014201d40c52100316914410000311619994041c0103c901b056110b4840300402c9040c10246429120700030100300856104204540f005e5607142481c5404c0d40003640c000420703002c18900c0020380040d11060200800f117401c2072142020009000b02a401c0207040b088a00da220f480411032608031000e00b5400180f4505400e103c080010401011007510441c4020301c0d103680d03a994a03100350020781c0f054806560701c072250407d1003445806070140308500c1c036003081d2150032900001d61a040e100c50060210361f58002c80c103525400e49016 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 538070890 1250 538069640 538069643
    0x905012601270510090e0109050c0f0607170c0706030905071202060702030601030b06030c040608060106080c0d15060305090a023a050a020a0605070b0a020d02161103070b070804050d030507 83
    0x503c2245001e00342c0720101030300c0d4403460210034545844590401c2c818420f2950382a440f80140038419020010001c2e035451303544010364401c4007085401e00150100010004180108000b1074550017200b0009003000203a61085c0d051501344100d0300002040401e070102980d2902400b28010845030004c1065400303400e00c001c0d054841d250010090009083c5020300c1000c1c00c40486d640070788070340140010303551140325520880e400000148080c3e8007030900194441d122800d400c2c18011a0f809081c182c2c0e0700d020b040130301c1c00c0c881d8000340203880c0d05001d0702c0d5004158200401801c1d65550101e80282400100c080d42442c9148921105132001c60700240007540314031403003051302c0785400c01d40e84038014580201d22a800383ea4000440f140640305494005821140b016a41c0c0c0d18480c6603000780d4840148007a45680c204100c0300c60301a414491b02101780140d01401110303031040c05052410081d83c1020340d101c8810b00000c40000c2201c001c80741514002d64060700105140e01c0d061300c030790156640 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 538072140 1250 538070890 538070969
    0x2f0a030c091d0a060b071707050102120c070501061a07060b06040915090c0903030210180f060c170606040308161707050c1c0b04210905012601 63
    0x70040d9010b030880b4190701401a00600f0800c65a403100015010f1040f91802404130680b10100d0b00d0500a607030290080500500000d450044214214026100100c0303640c0b10b040d1002c030740203050000900c00c940c081d104160940c0c1c900d1101d08140c565038080c040000703002c15104d0240340d00f06c3c0c64800554004040641040c880940d10b00365810b04c54001d03001e100485da2801c614001c05a200390124000caa0b09074014212002d1400c1c40c0320007404200e00f859586040c000d5120300051080030b504040c0394011000010060f0030340000600100d80c0d80b020300e2170016020b01744095691201e085400720381d4030095240d520901400c1d88010760320071804c06000c24034544070b00c00720f0000f45001003158a1003001914004104041080f078088402140340c0c2d13844001e5030358440004e010306100c40e0014011190040403990085400321203440e01c444242c0081e806050402c101d5030040703120070131041c038083d203022441c0c2ea40e080e105007690140b05001c26600801c20345501d031040c000ba45000e0710a00322 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 538073390 1250 538072140 538072169
    0x2a090a0b1b011b110102070308070507110a03030c230c010309050f0102130f09020a1e0c0203060a1b020f032d0c06040201080123040e011e2f0a030c09 66
    0x124000e01080b40803140f01091300003011100c640e606200300c0302070580c19100c5c01036070707200e5035030440d0326801100d0100c4654080d204102203903521615003030000c3d172196844402d20300311460030810702c070803200340d622403030300740d401c00442c40a00400d26901906081c60001002c000031b00305140391000038944807085502c00280003001280d10300c1d03828151841141d1248040d66a03411110491190307401e004000b41203000d0501c407511102c0d0290001e503080e842d01145c1d2112a030002030400806644550b0302658540800e8180846a0300e0b81c800c2d440c007400030709035848261903010744030300c110942039845045075942ca0071021508500c0b0700303680544a9015464080300c00c0200d0b62040c00fa10207a0120b1854000098041304e24030015001664110107070240c05528414030020300750307218035400555201c01c41a0040404c1400980d601d0b000801e000c504082c0c06000c4820401001c0810a9021024914940144035032001c840030320f6541e1070b00062001503004200c80040c0344c0d4119010747d00010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 538074640 1250 538073390 538073411
    0x311011a0402130519051203040806070c020f1c05070506091509010c0f0605010e061c060b0103060536040201090303140f0a0f02070b130e0a0f052a090a0b1b01 70
    0x100e85d039000343c40b41079400c290304040700704803142c0d640034074410255594009000200c6507442a4450b4011034030207015548003105410000312668129104e641e00301d00203103c91010700408000084c028202035070280e00d440300100c04038480154144103a0040c49000800d0012640705446050941c2d0300b12a5481e41c1ca24a403030035030081c02c401c3c0708480030303080d40c2e8002c07a885140c86000700000e41c902c902c2144100c0e050743e486c42e010309005000103050540d03030f00c1d000030340341c90780340685060304c886540389821503411241215041c0314030000a030003000031307804220050740c100340f00720142c0340c1504100b1608920071815540612501c01500082c03040480d61623803040d04059030b10381100d103540030b41e003507562501c5040c201402000303403440c5440303149401004103121006100c0c0e082004040085410b500301140342d815981c0658016001c5d001e030007442445000e45621300c0c000c12200d100001c0c03810f1682c2002a0b40c54000340107511151400046c5c28103000200c08542c01003a1b284c500034400d0741c020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 538075890 1250 538074640 538074679
    0x1f060f06110309040c1d01181e0f060c0201030f1116050c040c17130312020a02160305060702070611120c0f0d09060e1f050a050c0312040311011a04021305 68
    0x30300c1003011b00010014240d0780650300800711000c07400c43d014881140c10b49410081d000420301d6884841d1581d03500e0354081954500c2c0f1001501a001c692101700441348948001012030700c1c826107503c040743c0361804120030394602d141100e400c0c03480206078a1020f00c03682802400d1907100d20781c160348540f50050b1081110382100e405c444c600400c1c0740c03945a139500d52200d0300b101d0081a0006000072003d411230340c1206559805002c150300e4510442e08501a4407681c034440a40a420684565100e04204803c070303070f1304001c0300000d0311161400b80e00440040c0e1604e6030743c103070001d400e141803000400c1d6a8504401009805540c1d420003089035042c0700030460103003540d2064003c0e100084c104520417881800c1a0a01e00e10000481c082401250b04283c1c046a0307d4100d00902030030000d007080040c940d08000c2001d411510321800e85140c0720f0a16190150151155240d4943d840e4140f5205160b041c01c0013a0142e103001099501580c3c85a4201420031030700d07007030b070080d59000d0003081d20f92034503044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 538077140 1250 538075890 538075907
    0x506030105210d1809020a08220c1e050303040f090c0c060203040b0709050f01020c040513052505040b03030316050417010f1a0d0f03201f060f06110309040c 69
    0xb04135001070003191a0000001a486110304c4040847c4000c00412070196100c040401810030414038450688607541c0c030003600c100d0680c48000e4000001040d28503012900b103041c4010b140c12401903203441d00d0b012840e03020201314803036022050f03aa4141c040c9c0c0b2a0003204139155070355201030119560b03c1e042c94003a840103010760b036400000300c101c0000300382400c00a04a40030075005030001c00c5205840310070800541001070050198918090030100012000c0040c0507a00c4d0050304a445140981340c0290304e5641554012486103040c00e04085890720b02000316600459a019012298466690103076564411a407003503040d54440c8505046401c0d041d032100d55181440c400c1401445900d010401d45604201016580400c01059410020300388405c010042c5110381400a0748803412400c40108081601c6a886203070083d0001c0f4684024401490b09000030341c0c40100701503420800440c034040c005004020500181102d01c58109400304191020707020003e00c01d010007401c07103000801c1c110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 538078390 1250 538077140 538077167
    0x180303021201050303030c040e101509030501140f071d10020a0c090e0303070f1101050708041407060503160c080f1c02090112050406090c03050c15040506030105210d 73
    0x304450002c43e00f0301e4003100326030064068801c000d0420b400c240a5004442008e090072180c038001402c0081e000e40b81240307035013600b0003540b210040e65117141001404d607491210b030342c00600c20380d80402c50034884841d40705130040b071246880e510040c0440e80d8550011500c03120158005c0c910300c0c1c04101030b940000d50140c0c403407141c12080082a526102c1c601a92902c59030904540c00c14800690840d1141c8108400c00c4490324024020b16841c03d050350840314207440020000344031004000c288843c80192002d02201c01c002081030b0351511034010a20702000e84441c4030310b0903c83c600883c00384a2855018441e0f0806403541d65040c0d036040908040d4030086102410f140300722a940380a1140f84207480b0042c00c1a120301e0b01c0192482c4102d4024000104104c0302640d44a01c01c0d40490f901180315800307540b01d14010600d8031000b00400001c0b420f0814070350f0344110700700014419620385809890440740103640c0404071500c107260100302c1c0d980740c03500d10000b4450544080769841e400342d03070200c0f43d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 538079640 1250 538078390 538078417
    0xf06160e03070f031103030f04090c0908060702060414030403052a19050f0a030b040b0601020c0f0f06030924060a060e09060d020f0a081006140a0b07050118030302 72
    0x80403030090546031681d5200754120001420740400109a0100014544850086c240c9152042101d800c55203900140c01c4050425030700d0080f40401038001446070007400740310740108550b29045600075960000108006c140003083d043c1a0f0101d28200156000345d6803050542d030541c01b115240c4036010340601c00e0000b5410070304c1208031290410b0060003030880c04001c40e080e102d50501f410310140748825920300b500044a220000045400800b060b4007442c4244000b10450410b04002440c0c0481c08900920a440d482c032144c24a0391400a0100300342d4090b0f41088d03c1399100315001b400c01c1220040c0040c629403076040351b4a00001031003c98031440040304c0c40800e0701d4442c0c83c02c0f20100c05e82429150060b482030042006890107003142c0c0d40903031000380034030581c0b560305c804164018040e82c01400d06903c49103041c520328426004400103040b000800c0060141e83c8000154540901c0c861045100000110300092080a401c01c0754511001c0c0c1204034107a1140ca0000c0c0290f11404494801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 538080890 1250 538079640 538079657
    0x30c10060311150409020a121d060f09120d0203040308240411070203060f01080f01090b0109021c0e0a0201031a09070f02010f050f041a010825051507150216060e0f0616 74
    0x2c004a6501042c045c1038600001c0203140d03120501903d00031005001100184610741c0c200e0455375120f4018904108401c102689074100b0f450064000321001e011460780103080300c1428840c0c40c01c0000306005080c11100868500094a0702c60151302c20460080d4050003100104440c0010041c145c038101c520392000c40d42081c0c00a007600d0300300d50101c0c01c003e10300a1010010000014540c014007410041c1100000a2500c1210000304807094850160318a8006d00e21480541da058814080b40d188030b240d8485889150200185071007000400c00300078000c0581070300a10307520035404007101001c808410402c6041c40341600f80840021602200c42d5070306a400040780d82101d5400398101e07403180d40103103200800d40324098000c0c280c1580c0b1003500c0140410000e41580d401c03940030100c03004a0141030f42c60441d400c0048001c445030b624949014010012208800c114560840750103821160024940816256440c1015140c80c0c1c1000c1034801c400501044050400340c0790103d29640e101d0450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 538082140 1250 538080890 538080911
    0x5010e0c0909011205100c0e03010e0f070312050c06010902030117030702030a02011115010b040305010e0d02060f10090f0510050102010606050313030302040b040305030c10060311150409020a12 85
    0x98038410407a041d6042400c00340104120443e960319505a0b03032040040d140f00044109040c0202c516021000d07000a15401d62025181020f02ca12400d880524003e80b1103042c0340801c066803040940b00080076034202480e026580d0b4446c0040d41ca0b01030490083d0394003940d4540e0740341c0180d0828041c28003940d43c2c600ca5400d9030100042140d10607135010b0040e01940d00d142d0015035205a00110f08003160040310300035091901c00700503c501800c04468260384490460600900f1101c3c0442100141d521003501c202800350000303034540e0300801c00780d1505125a42c6051048500c413403075014186203414900880c0103074084c0c0c5c1185110304071300b141a40c58117a48100480c02e1f00c0c5684140c00215804202003180c540700d44c101c60144c03501908025241903901d082154440c0c0c405c0e4419589500301184144a908081c824640040c245c40e100f404554251784490b4680d01444201f5446a00b0020652a6000c107031001d0710700500100d40c0031500e5001c0c3c584040c02e040c07034204900d0310305842c2581200307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 538083390 1250 538082140 538082161
    0xc07151130071a06040e01020d05041b0b04091a040e100b1012020313140a0c1a0306040b0301090c060e0414011a030703060b03010f0e090c03210702060d05010e 70
    0xe0360150031201e421049001043d21031a15000030380b07101d8000c0d40318810b41d102d01d50240000c115000365610006003628090500c5080c80d030846512025000342004100800c0750901d090781d00352405001e001803500d8201c00898000900000340a4025040102c8606020404107800a40401c02c5000f480780011640030081c40890f00500301010034480c0203080c803240442d0703014660110b02d03406551018086a11a201d403c04031010809580c4d00101c0350804101a814210380200102c2800d8140148038094070211804000c1c4110300941d030310704109a0540e002d40140d1003194006280e04201901c5100050220000100f01406242030802e201460740e014440c0130304880700041402c0c001e00042c0621920b941c80504403004140c0c07030b46404a07a20181c203004600070038228901c05007417071900b0603400b166600200740c2c000c81e400030078a061951f1000304080290021281546120003840158060700340a4010003a41044010864031241c08480e0f100505841c40c510449510341c2d242007000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 538084640 1250 538083390 538083397
    0x3130e060405180622230d08041109070c0c09020306030f06040503030c090d080406020a140604050606101107180605100509131103090c150c07151130 66
    0x1140c10b680310740000b54040141d455041d21504103500414948405c50701c40c18140b0a1100b2a03c12249051700c030071100000c1001801041d0201d400c0804191416440340c0d0408600d00d492a402440030341c0008410900c038410420b0505e82c4482d5601a2381e4a802c0746c08002d400858120b8041c1c421020410031544002520341c0c407455102e40158915038039103808035015084030413207070b40200c00f00c0064000140daa8019002800035a4010004403855080c444095038040c3d4400c496604021b0500011035800304860b540207500340d40c00c00700b55004940844004801c000044a28040c0180106001c0b00d840c0451801a4041c03800b0321000f0340b64001c008150369000342d00408200104a0001e184c2021407015800e8005480001800d08030015905081d500850711010340d5004003003420058a409140400b109402071610350400280e5091569640180c0c080cac0f40312641031070490781e02940300c2c54410340c0b244400000d90324281c01d10503526400545618680032a81d0454011aa0004100c0d054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 538085890 1250 538084640 538084681
    0x1050f01061407150c030b061606050c0a05031807080111040302130608030313020604120f05060702010c0507150b0604060525030c020415090216030813020109061103130e060405 78
    0x1c40d40c11101c0400b044e0010a4001c042d907040c152034440410b050f0707440801415440ca108680740f0140b00051902904070368005200101100d003d000740200d160f03000003134941c041c0c1b48000d0114695281070b045440e03c01c49500c10300c910f6091462402407291023502038070440b40309075021110300346c91079156001d43c2c0b07290061072040d40c02400090140303003a10803800c2500d4002703411203251036251383d0651550380c3c8001d000c1e10744206180307c1ca01000820880c3c1c5070700500c288020071000706030807070042140c402c6600180544113072900311040704143d0391204c601904010201e680d82c6a54500180c255084600e82294180301591504400c07210862800b0080da450b41c1d50300040d40542e402c000090000410903043d5203441103000c50410141e1005108225892a144008054514000340310200040012905022191a04d401030b40c022030004c003901c020b0309240c00380380d03039005080b4038501034050341d143c01085101d000a04107071001110f07401828107a07001d10081e60340c81c20950b01e03403941414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 538087140 1250 538085890 538085903
    0x708130b161403090d0f032307050d0c020102031e1213030f02070503060406021b010f060f050609150307110a03030902090906041502090609060f03070305010e01030f0f02040e01050f01061407 84
    0x30008001b50345d941c0a202a14802d051140c0003402000e0840e80e000d40e00c0040611503034000540301d05108040040300c0200189161964503101c0541c0001e44a00407070307010840244030311680c1015003030100281d419200030004806041e1030b24848040c0b620810740303416030115005400b070204a5201140c03d034103540000e002007440342c41d0b41e0365410095006110502180c0b0412512072800c040030300bd0b2034640181d100c00801c6041c1480214441481658403c40c41110100062400c03910f41080d03007015911540889034503a03803003260a440003001801003c80301e010b080076807420542c252b80061860390080d60034554076541c607075042c0ea031041c058501070320b0b02c0d05040035245880020340003090000005082c450400c25018007150440d04960011148110044100700c9915810305c6081e005100c800c181d2006540b464442074151141e065001d407900003600c00c010b066440b0ba40002d088040040001c000516200054200d035100c04c0c050400000c00e603000c2c3c0c000118071101a102c4071600951f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 538088390 1250 538087140 538087159
    0x3060f0d0816061d0a050105010f052803020607260a08040f05011506050c060703060302061e160609140303060f04050415050103080301140102070b0708130b16140309 73
    0x9003122071401c10b071081100c4442d19842141d0811079042180580c81c0c02035002410003000c186011801e44005030092030800240207002c1216a690710425040f40a0000003140301c07092a80781c00c03404103107540010703400c40d02c0010900104914a600d125145000d0440e1022221007180308803100d100720094900010344034804034000c20180440c0c101c0c40e911031000001c0c1103921580c8501c035094940d100a02007080031a19481300e80050000903800145407030b0030008681164006880d60050003c00a1840032096148440340d54580440d4100080d840010229800074501070020b002008011224100052034201640340d002060343d008860042c802c030a44502e50041c0401080018000d40f00211610001e024100151103128007850040308010365030340c1007001403400c4610021110307045500182e401c0003074550a01c01d90f2541544016a030f69188215132804006804681140e03803c50000664090300140604d50459180d110b0004503065040443c0c059450380504900e56400101e2031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 538089640 1250 538088390 538088407
    0xc0312020d0e0618010e0a0b010e150d061e050601080c130312030506090708040804030303050c070212010b01021006050303071e0c14012d080903071703060f0d08 71
    0x5402800240410540c009035910740b11068926105042c3c40300c00c0c05458242280c41410f5003030007640c50303912030140100a4982d06940e20302e200401480307000c02741d40b6140c7c003040901084e101c03001041003000b80080311842050034440c001b03041c685410307541a580e1941203958114140101480b90034142c41d13000895440707051600035644220b20341407012203140000300025403008040707000c1100d259800500d500c0c00788c0521083e0071300503001400b403080c01401c00002400102c01c803002c0d0796141c40c1c0810644c50704c0e622000e940c000d143d0b000794002010b5010031085a030541c00030f0f400807000d0342104c40c0c03002e0002c0088111203032401207640503001007002101140036600745c2c14141042080710040c551854650245421198200c540345003c0107200030340541e4041c100040c21818840f60860190040da03284540342aa4601c042c14064803000040c1c0854080c0292010560860864010004108152a443c0d4011031715207200e00c0d9448403445442c20080e070b0380e04801e40d004d10781c2898030441 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 538090890 1250 538089640 538089677
    0x603050f0610051e030c0403060605060f0f07020406080f100b1c110f0d06020a031406211903020c040f020f0708091f0c0201030f020c1b1f0f020106060c03 68
    0x2c4c41c0b0070040c1944004030008855411030042d0f104a000b00c50103605d6504500d051000e4a4060780014410b00081c003040c2d400801d40e0044039031300c013035400c0b0b010741c0d6500b0781c8040f8014160380d500141d00b50264140c131540350040807925081803000e60340208036201c000c80421210845018840034003550700340015000445184070300410a0004203103d1600c44100001511a444e604085400c90780100b002e59126405020f8120075034090b101f1030480b850000c02150411480080e46a040054000c10403040034081c0120584c04045032214080700d2202e0902071340e10040340441900841c500400440101c80c00e01c05c6e21002140d4001d50391070408241c954000581040d290558842030100246003c00324191074490140015101d00141602d2382c0009811120443d80c9070562074010442801003010100b440503d07044a0301c0090300c01004c401c040703051100d4081030020040c1118026101440e0007102d03444403c0790315402032000b1904c13200304440345992a407009000c030741220740550080d2107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 538092140 1250 538090890 538090897
    0xe0402030903040f030c061b0f0816021504030c1202031203070306090f06090f0b220b0d060e1e03120406020c0d0503010f0b19111011040603050f061005 67
    0x8a907001c82e41000d0300c4102000c40f80390329500032034405131341940420540341c0110449540d03945090349003000f0b441e40d0700c42c1544540580c40042601c0400514030300c2038032a131110000d0075074000d0644458035442e0441d2170115400750009854040980000080c0c6041d50580e002805030701a02034100e20121400109a90308050810003d0648441000c202802940b00301c41250b5038103680483e4141c640b18000044400709211800c0590500240140c01d840b04c0301e05501d0001e60a40000302604c0154500000346050101642e000c683e091129003400107980202c11121102400d8070501080040314080303502c42003605130560f0b003061141e1102c4182401034250300034080c3d00c3c050320380940702c9022805c041014410f040484c00200040c480098140c1078400640714500c8050301d030206441d4801c0746642c840101200b002650300041218020602c00e18003181e84001044c48440c00031203e00c40310760098080c0c000000e15140001d0b1021000620b6640030b00c1020704812402008504212a03030391 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 538093390 1250 538092140 538092151
    0x60705153301030c23120903091e010e090c07050c030f0d1409030d031505060406170c070804030803010302102d0917060103060e030702091311040216020f100e040203 73
    0x1101c1c201604442c00c014083c81261200f0b0340d0302a0f4030506102c1405404802824151007503002740852032264999100704211302a01c8042c42d081d40d004040125a03c200c21402070390000014001c0c800031440040c00b82c40800d20070000e980390000010141540e0b400001c0c808610365100325000203555000b480503100d40c03003050045924106294010034034000d001c0e4a9040020360f18400c1140380c800110096010f01402c94201f031a2902e0701d6001003c440c03600e8410705c0104511804202c407080a1000ca03001d0740d0b8440d01c025181d0781c1c1c9003401c00140d0402d100c160b0280c0d821040740c0d03040394421091400b080785585600182d0f0780c10411000301c211403145051050054214006c60b45829078850146026214401000b1940c15850550103444081e6030f02d20040e44240240b4005070307151010164008610040c0c03001051103420401e160149404070b0541040c4002510390a2006458160f0030031b030300a41d100c41c420421b9200f8020008031028a21000685907100030000c0c0c0b406400550300701 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 538094640 1250 538093390 538093397
    0x80c15040e07030b10021b06090d061503061401030b07090b07080702120f0f07080a050705010c030306050d0602041d0402060406200105070e09010f05030304030f02060705153301030c 80
    0x3d40440b001c901d1202c950498140964001d442c1fa40b2403c00034500301d01589425a00c95042054501c01304000c2c884400c4020156529070310112103a0000803141d10055401038000d1111100c0b854580902d14002c1c0400e03070f220568000000d0f0a140102d1180046625100a07186005c100d034640b0500c0c1d4100f60030490b0700002e84502c030a1000801c00031008080920009048030022031080745182c811640d110900070f802c00072104010132000b04200084400a08103c0c00c00c4c2c80d03624084008040c0c4e500090b500102423840c1c2d005000c000d80c0540705441103a0424601c10056805d21945100c0031600294042c0003000188001031003240b0098028200031120901114002c25203425900c04480440c000341014080e03131441e242ca80003290042c0008041c104180b400e00300441e0300c911642c0070281c0280b514181355400c5407506411107002d5600b020585014441c8000301c2d0001d602d00380c0d55101c42d813400b0030140d5003100101c4500f001501d200d00410844010074001940074100e41d94215007131 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 538095890 1250 538094640 538094651
    0x1404020706090c051311040e070903050105040614092a010c05010629030f1302010c1202062d0103020f030a050d030209040f0608030706050a021b07080c15040e0703 72
    0x240c5240150350360340c3c1c403920380035035142c1c11300c03092185c14a035090b100c6405505080d01ea20810908508603019104041c2545041d907035520402c2d00c00c8005584014180c0d0f203401c0402c0180441540240c1816565200842e000c1d2030303841405503119520320103088014074008260b606100c46200c81c120b1004e060422140c4501d05448540c21a0840e5101998450201c00300c000100101006425104690981d050941c10728000c00701489000402c1003110310507070401b9105581c0945415455035500c010209a6144207503c025110740302560f29070803070b104003000280540a00d4000c00c0c1da981045201002503807035a003c000e0003242484100c1e070180200126480400c00c203001c0c45040150580300941d89600500a100c112201c9420403e01c0524002c1c06001d200ca000c01112966900300c040800c8544070110950700038814412000c4005820404a0322541c0c03011641108945040c0306454008110606104490b40840c200800e00401080140b0035400b05400460b00220189000200c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 538097140 1250 538095890 538095893
    0xf03050a15080106030506010614030103060207051c0f0806060c03121801061e12030c080d1b0e04051e061003020408101a0d03021b01020a02130203180f0714040207 72
    0x801c1112608600410b946540e001c1c028401d0401000340100b40c940742000c2c0000005c1c81c075031420b0006000003804a500003496006015080015010514005071410300d1312000440c0075042c00b0111103000c0c0850320aa0010b151440c3c4181501d101c0e0211034040c0d4a401c0744200740ca442088018960040c070b184c20f103a000d40818007441100007800e00411070220184c0401003690024040341c3c04190501c1803140e02d580041d078000703258181030f944011120f0329140400101c002030500b44034041031140720710f040e001c03031507601c039400308884141030318204100d8860054004600c8880140006c0185e180000708503d82441041d0101c110b02524005042585507404641807008070002d082c030203a103540403c4102400141d41100f280d104442d17200304c21415940c0a03444a14074911306451446484100900e40d0080c80140c00c5980c0c020700080500108620090082d0001d076180032440d11b00141002841c03e00043d01a45082148028913810740740602d85034204100d00d070003e8000750280003610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 538098390 1250 538097140 538097171
    0x6040902070309080f0708070b18040e0304091a030a081b0f0109150b010206041106040e0a05090708071d0a020c0f1506011403060f0a030b0a140105060301060f03050a 73
    0x200440c401d595002c1064a412100d40c45e1040c01403610505800044040003441c000103543d10458006020841c2c4801d9025000040765000101203038009040a075600e4841d440840203109841c42c400c420071014a1208094103102c000851080d05a40405604800f007000b58001e840100d07000551910fa09412585280c01d18440904034903240c0e45482c0108100007900b1005010400c28141c1004074031190f10000750b55140180c4003030308000c004029551251940030440b00500213001c0005550b040201410005103000c44200040d0700940c0e1001c00c00120218071442107503e08580182a10a06013009480b07140240000302455420421003040c1882440000355048a94000e00006022203000c40305269004104504108404021903154030101d000e07650070400076036140410458880204400d100250000740407583c0800030840e800402d90012001540d510500340000d9903202d050003803d002c00e010311000305d00081001d52a80b8400d07400309921202251001c00c0240d034910002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 538099640 1250 538098390 538098397
    0xc070c060309050d050309060a2a09170c061905040f080309030f060907063f06050604030809010804020307030c06020304061e0e0607032f010f0c0206060f06040902 72
    0xa4007081d22496540300780a020b03c12205042a44d04025155240100c240d90325144000c0111618030b5440c2554010210070b1000b0b413010752100341c0c2148182c4000c50001d0304911140c800c6005554080552150f21140464401000003019202a04000c41110b003640b45140c0c2203840e104105044c00b000400b0900240018000d02400c07014695a80010044c181880000d0740400c0c031a511050600c0b04280c00060390004807601c41c5028003010b50070a0052030942d40040200c0b42c3c0103002200a0034a0070300f500105d082141c104001c00080390748605020050003503220150440c501481030010650143e813034075134450300c000c00b9513940c603450b55500b900000307081d00201c1c0113900210f030a0044682003e03600d00120301800900d0780d070400c0349900400c3d040c8003c3e0214001c01c002f08407401018020300344450400c2c0b081e5440175031268035811101070b000c007850041c0c6c402d608140c941c645440340d520810040c00b449501400041d6280c4080c04400b00d040f590958020708200800103036400c061015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 538100890 1250 538099640 538099649
    0xb03010617010e07080d12090804090b0a0e060f010c1b091b080105130207140111190c03140315040509010b040b0312030f221103010524090c070c 64
    0x120a0804034800040c2c01c451000e520751003c0d600150060080040c0081c00ea8003c00003440c1c600c4204240d100241d02074164403c004000c04404200451510200e030400b07904504150b901030305407507803240556000c44040d9038654010040603050021948500f240fa031030103003c1d495a5015070f803d030204c14052180780c2d0004017101d40c3c0c1c0180c04414815030f00c030700c501c0581a141103241d650400c000038107010424070071146003590003d1408100a1013800030f0145000c004001c20a681c049100040c0aa10002464040c800c07555000d0411a0050424401854165852000a9480c65075641d000c2e031002d01401d50048000d0503400c459507942c0070780d40c0702d90401400410103600c404c082c0020344407211900c0d0701c80d400c04d25800d803204460310f0a0366805000400c0b03114064a07441ea80c2c00503410743c1e410300044100120304500502174540c07460803a51409038000c01056440100c551442c05583c1003082620f42e41910944651030003402d225000503070030b598a071a1581550381c2280b00c80e6103522 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 538102140 1250 538100890 538100909
    0x12030c0a17070f1101020405090105130b091810020f0a0f0509030706050903010507080601120203150a0b0307080114100c060b04050f070206090303070e0111120307090f090207050c010c060b030106 86
    0x40040070f40d5100c0d82d131350803040d14070009500301402c0c6800520b201d41d05009a5001c0e2104001d0780b51a4403881d08807941c0c1c010060505026420001c28120242030300c140d02c102644200030880c0c100896520889041420191029041c07603019882262054a0813050f0003c0000a1101072116039092001d030340105000c0e00e855a481c041101410b09440d0001c1020b0288807001c010054603903040f1140d0400c40c4001c0c2c2c80140e0f00d036206100c03011100c4150b864242c0061002c074001c20901c00600041d40203803c2034582d490540c2e03803038131101018440c2003003030ba8006651141d0300310350600030300244c11024810307040400c0c2ca80c03001c004030703044032350440760210038072003280070b228100743c05211080d04540750b01d01551075458041409441060241400b50401c1103502412002d200248201c20303580b0100c05005d80c0d21306090b14000c000450600076041c90303441c8950f000810f0211031085a850903400b80103407100302c0000005603034500038500705403615515258441995a409e00c2210068a08400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 538103390 1250 538102140 538102157
    0x20408011508070609030320191a060f1306051203040302012c12030c0a030806030729030613091a060108040c051003090218160212030c0a1707 63
    0x901c078100140156104240542000030240030b20307039001e100c20080d260076082c10740b040c8032803148440a0705281e6140700700300d01804200400d238040c05990f18500070300403095600c041d42591001c00483d44199012039026807280c41c900801d0510f40800382e41c200e5140e6001821651740c10209441240401c0307a00758540000409104641e0800b4140a14104624140c0b02800510880c0098010401d960134801c8015000c0b1403e001d00c104100c41818407000182e41440e0041e140207440c40100381c80c910302c00e0052800c0414000e41d000340d81103c8661101075010f03511041ca66844d65980090440c41c2c004005c00c41c200c0a01c200383c098007403118481e5019034110080c0c0c80180e1100c200c0035146c4c1e0304100740e040510011424079403400301510012158072400c0c45ca0381c401034000340801e4070020340258444c94040c011800e40600345114030f9440e00a40d07199106d4171012600c0c0c090303160211201c0304060001c0349085245001400b031082c414107105480c079008000e2120a018116040000206d121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 538104640 1250 538103390 538103411
    0x70314041a07020f0613171602030c0f090a02030421020a05010c0309050a03270e01090605041506261f0f06020c040b130e0a0b090c0a06080403030603050102040801 72
    0xa580503907202200b48040e103130180c2044003050311042d0152003850600344602c003079000d1100d58440c00020041d50030a15650700c0c1c1084021100c0070b200c1205070702c2405041000d44581c01c04908044002038006c20503009680e64208080080d04042e00030b4450304200d2020444c0403d15568000004e60350f9002001c41c100c7c6842d00e0b40c01c0d29800200c4004060414040300c0c00241b0003d201009160b05007400140c03101589014040301d40340b00700d401000c01000d980020248540b00b002d5050700d0b0b0307410f0103201e642d450790b09110507194154140e1195407181c4208018192182c5010300d608060f60216072040000300c10905581c00c0250f501105a070012581d60900c401180300c0b0b43d004003035840c0b422004500d8080003940f030380300b00d0884502843c0c94550140e002d549120480d151100e059508200000c121039502d656620f8060307040b11405070400104800e41300c001884001d40400501c407524241c00c10b07104a40c9010060000ca01303140c0c40d4100840050400c1c00a00301600c1028000180d042c2a07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 538105890 1250 538104640 538104683
    0x6320906160c08030414030d230112150902150306012319020f0d0507030207090516050f121f0b0f03010501030e030f04080312090102120a0507031404 66
    0x141c2401c0320640384101004800e50081450b2040c19000a401c0d42c60b0342c0c690800b9200c1201031400048103000006000a9100442c3d001c0c100c00d03000d00c40a102c8101e2040d04c60900c7c00001e0003194182c000c84c1056030300040820104640d107541c10440496030000325400305a6180020b40c0240031080301108114055a1201005519103400ae500c03108042000c0c1420f1130030b20070f501622240e25481d240d52000c0310300801980121160910480300402c6000700004c000350000c6000318010700a545001519021070f00481b030103100300c3c4030303c44801700180100759280c1d403040c8540c1103034031005e00c0a50300c0c042811071081d1280305014112288840500390b000c2035045c0c590032130855114140120f145085440040d00d06440c800e00b80004c0031410660480d156014503c0251080d000018011640d464044080c00701c5220f82c40883d00c03a52541e00b000c900341d011301340d030300328807014200c002800c504a180c00c511313006280d60400007105144010030410086d03088406940c0c05520403845d003a030000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 538107140 1250 538105890 538105903
    0x50703020d0e060708060f04090203031c060501080103050309010c020d1a0402040c14070b040819051903060608060f011407030c05190b0705070516080a060f06080a063209 75
    0x200320003d00f0003454040c001500807000540410300481004005010719142d550114103c2900181280e071a680c804203088603007000d0505848815050540008180d4080d0000f1416254410003440c1021840c230011100150b824106036070080752003421401250381e0111075441800d40240c2a409460580180302c240c80500c050b030030400814001c00e090102000050307850655100c0c88049294407070b1f041407801801082c00300060340c0713462009030807007942180041040500503a04440e101c49a070340c0035000c40b02c20380319500c00f003080c00002890a00d4109500101c0d500141481942e1100401034007500fa081007804030045000c85204800f03100b8204401000c03200640e03500d42c1160b041d035984c44d4040300b014002c1d805010002c50036004220080c04841500f200c0c00c0c500c182c1c1c03d660b407402d40340c2c2d45140c0201968100d00e0a950304084800c1d50207464240c8140000500500c00c0301d0f03482100400d40d055600c42c0450380d003400940b88400c504101c0d100d0082901e185611820400f51541c20981c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 538108390 1250 538107140 538107161
    0xa0b010602031303150207050d090305010c08040f08280e241c0209030a11100c03020c1905030a12120b0112020318010c0f0f050c0601031212050703020d 67
    0x5205000007240d102450603000f05a0740d0000806004002003d0840064060740d10010001d00030304081d010700c00c1d4065110400c59000764021300407201e50307440641d4024400d8a028290301842c244600109042c0d10091421000c11100721012180602d5a48800002e0081b000d0000d10000d0980300ba602c0d1100d4003400a00c0e444101c0c1c500480490380e03201c868400c02d1005c43c0395200001d400200f40781141d060360400603008d02a038404198a18020701ca0f03802e102c041c0c5100380742101030715554600c1156000d1215a154004142146d580c60812005011503003a4550303d01c85044081045e860501000385080d208400e603140c64100c118000c0d01e008404906c00194928154180800b6030f8880e954500d030011008006960703032112011860130138890300818903d5800e10f05002c0802d07a01c1404149003003200d50b2401541e69030003104440c1c5100ba800c003500564400c070014404611396480142440506090a1610541c00d02c020816201c0881d01c0b507002c039601264642840321140103c00c47c81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 538109640 1250 538108390 538108393
    0x12150a0c0305150108042906100c020a061d04140a320a020f0c0714030d080c03090102041a0717031e220503070c170616200a0b010602 59
    0x1490200001000b03403203c081124100111140458240701c46013041e0101994004841054065000d8110050740410b44c1d80501580c00275080440c0144070340300c009000c1d0360041440440e5403400704103c0751062401c1890300e0603c50722a03100c055694600c40c00c01346003045040c000b03903480d0003209138003100c0c400054603001d050080c070512440c044011800c1c00d0207030030b0300011502d51500041c101c000d01901a60084175000082c0449008000040b10022645c00811000030021100c040c1a121030704034a070100030400050105814010f0100a1a80003491500046c201980e80e4011600695000400d040041d0002081800c0c044440500c00928035141c80c3ca6103141464003003002e0880032840c1398256400000b02085016000d00c0d4090311194416411400203522401c0c240c1d1a0391184004680c1c1c2d007500100020a025055003040c10b014100c00513100c00d40d62041c056446c100300c600240c080081d03104041e07400882c92075400c0a84c0c4200d1000700708104851502e1040450180c01c1142035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 538110890 1250 538109640 538109651
    0xa061505031e1e0303040c051e040e010207050102070b0f0c031b03040c0f0f050f090603030a05030919240e0d2102070b090d080705030c0912150a0c03 66
    0x80d40c5002481c601000c00d0040d450940300c40341c0310b041c3c0c10400c40c5040045140d00e000c0c2d10004088001000c2c40c000d034000c07000c00461558540070810700b08807201c400a0500380100d0360b0401450507030311041008440303100252a01e08903940f600d08a901035901100c0032001c09080c40b9080d8a1440003650082100942502d142440c02d03031021007240c1c14102c00200c4a0002c00582001060690711005100c1c6142c0c250703805032075107150003a14000740251401000801e03410003092030012102d50082402a01452a180301144102c0e42da5100a15138001d52160440318082280000b00b00303504140121103c1044440d00c05180f01d00c032880c140500141c50401c40c000c140b83c00c012442540855060410344981c035014402d8260880794000041c4400341b011070b181c020321078804d10b40c600c20b40421081e100301030a692001d03201d00348291026000036000f8000501030310903030001813a00e203000820b80640149540d011610b0071400c201594220400901132100021181c007a14200300c0c40d0742801d101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 538112140 1250 538110890 538110899
    0x9030905060f03010f1a16030203360105041d06120d0201060e06030318010503060409050714040b120d0318150e0c030f030d0203070905060a091e0b090d061b020a0615 73
    0x68501487e1340001c404c81120481e1001c0500802c125004002c0b00141d5120900e81b01c010440115010707400c1e0075090410001111256100d1003c54007551100139a0498401c2c0e099094800f1100050042d500100c1646412401074810806503403024407030b0307002103038186c145968000c0c020000352000e8040c0d0307c2807000c0c003111811004014034406d007e02c2d00e00d440e9a0703108005400340924000281582c0140700340410400d85c891450a4100c50940c1d05101101e20307070050100780503540c00040c0072508032803030002e64070307100341c1083e0040d01c41200440f4001c02162a40e00041d4480c00103103550980e90100840c3c2006c0c188984010417408030f020740480344007805000e4891107842075050749141d001000801113802817118402600c0081c0c6859264490f0220103420304400340901c003501c01d0803c14a210714110351040000340e0302c03110503a5051481890501102144481040305e509440b07a80c4100741c42c180100d041042110307076008120081007418110102c44c0c04030702020100d99000e03420f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 538113390 1250 538112140 538112189
    0x1b010e030d030504051f090c05011806052802011d03030907030f0c24020f030333060d2405150c0a0f080d0c09051309030905060f03010f 60
    0x5040c40c40e00c0c100403403180ea5501d403890800b40c880030f20a51078501e00c0564a040c412a0307124502c1f603403103040c1803403020352120015648582407426480c20074141e18000c0c080b480c03180c1c015045088058400c40410140380c11601c200003104070545005139510000da0400d0300b0b03540701c078056007101013000e9859810800403d60320b8201d030740400380090000e224000c080005024804005008002c48407007800782d108161140d80780c00c3c034400d1005115544000c0d1380040044101c0e0300400d0604000c204400503600000c003040b510404c0b240302c0c00d00700584908181c0b5980000c01880b9291500043e030504100368480b0501075202c0600e8046507280010302035a283d00c00302c4082240c1c1d14a50036201c4040e0b2b0740c1c10f840c25811190040003d02c1e0900b91100b0050307444041d15155803000803c0c000410f4102044412071050301c5400d521641e000004515400c850b840115528041d1500160b12610340340400c0c41c5600106011510383c00000042041030540000140945190b07000110300072194140031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 538114640 1250 538113390 538113403
    0x26121006050405040c09080d0305060907050a080f04050109051c0215040b0103060b12030d090201030e010c020a020114040e040807030305090d0804060b0414040f020913050601090f1d1b010e03 84
    0xf6001e16503c1c0d034400001c0e4051541040180040f070201d90010148800c01800780c441681c000c0e000d4940c4101180d030040c080d0702680c10010040ea44c141041e90b0369120b440c0000c070003910588065585060310000f1600601403050302c01e11421021028501c4607074002d00d44038040048206c1e100d851400c1c0300009030f8580c10581103a405c01d07004500318035288009240d8400d540c00c4182207100c0042d101c080d0001e80c0c0c00160841c3d000b603c040000e46030940e05282a0755076460400c0042c4c2141c604e1000642c0034030303502c4030500038042900d4201038644580100754078040c0e80a666280b8049482010907a06002d1180c0c01000c02c4040c01c1a03007172101c4054124a800fa00040545443d0b06d007203100d948450744203140d020107850b960380e0a8101030401d28040c06009030141c0c0103080c2030700040d151511411041c20100d6110380140a160711f0900702700e009080400c1e00170405600c49000c00001d08910904900c010120005000150f01c40c8101090030384a40c6145070600c010100c005007d5a80070a00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 538115890 1250 538114640 538114649
    0x1b21040506070e011d0d050705090f040b06040e0d110c03070e041709010503041e170d11180f04060f0308190e0a030b090a022805061201050d261210060504 68
    0x6e501291900e142060403d20150000c50b0494072820130855040d1452810034000c900505040500e0f80350751061105079640160740c002075070b0110725004961072050343c240000c5958541a92106182e01001074100040c40c0e1060401c4001c48003844103000580801c0d5070001440c4208600e06000440081c100d8013005002074002100749a421400301c950174040e084040d03100080c147d1105002c020050780f40c00420303131080c1151400342c45c080100a08001c1710480b01c85c010b50114026907040400518040b00c02032144c009460718000209011004420700155100d018003a460b18400c09200c40700f2440a0468810000d04509011594541004040c260380c1c124074592090b54138140307141c0c80c1c081402da0094003d000500149800d80c101c200b011107040c21b601c192407000d5a90010400280070b800e130310358a01401000100002d2501e404002c051600c5649480300502021507000307864164504090350094002403610720040c0d00f41904e40d4052921101454650b040c0f040080840c09035004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 538117140 1250 538115890 538115899
    0x5100609060e0a15021e0102120f340e0a03020f13060e010b07020306070c031b08090a06020c1e18041a04031713051c03110408030c070e1b21040506070e011d 69
    0x7003850130f194410be0a0101058030740c16065101d45101c21802e00071041071000008000b9a1100224034000a440c400c0f207400506039444c98048108110300782203850943c11456540d1880052080c18001000f40241421800903488200f1401418180a4000e00c0702c0d041000042d8140c0c0082c0c0c100114410300c080000b03942c0704690785450141c2030351007010b800703541c454800000001c24540c0040c0319010103000f51151041600f040b2851041c4901d0383d07050b2a03000e03100005070300600b0500c102e000c1d03015016150402d60003503c0c40e40030302c015605079021380004400c404a803145503102c5140319041300ca415500314010b006e0780c4a09031501c0e4001d00d801d94000151001004407440380c0c100600ca0a110008140e460341c0c2e9543c2c00303540741d011001c8104580210308000800060114109100b550390402daa84150740c28100040507510044401d500f402e03d485d000300d1003218982134144183c0c490b5005210034246000d02401840308980941d0401c5421034a01d5a07012907549c1d00d00c1086810345 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 538118390 1250 538117140 538117171
    0x6051c0809060903011805100c050f09060f03042d0b0633031b0f07080a120204030f140624120604051005100609060e0a15021e010212 59
    0x4000a09610902e0060f6906600f80854481c0700a000d50140461904c58030441d40140b1485140302c2c1980c090948240104005102c1c00d5803030002040108841880109224940302c000700440702541c0013503030f00f070b500b0244c40c5e83d070079150f14480b1600e208044000c4800d80c2e55602c0d241e03030f415403600009202030301a0301140000483e0f04035250004c51a43c9000075071800704c2c0e80d040d103501c02c00c1d04100e503440311500c210082007105903212000c40c2c034a54514481245030501c07035203991100d0f42c824600401001404c0b80304140d40303885031002c1e1005c1c500c50180001c2d80344060400c00f8940d512024502c200e6000300042c00f00113580d800c0c074071042202c9100c86880c180c15200005200307051000c05034846018060401040007404500341c800710811240401c00d03504e4940d401c3d04810705900604c0f010840b101070500c000f50040c1c45144641000910f0728400e162683c0c1000524940c2007a40800343c0d03c5050080704800c4847d08003210b0f010f102c0004c60501811070800842c00001030441c00d000303030805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 538119640 1250 538118390 538118407
    0x1812050c0a061a010e040501030f02091902032e0509060409050304050405180708030a02030403030813140d030c0507120503090a050604030c110103200d0603022206051c08 75
    0x1445038044980d04140204200d007100d40e16809503a01c140e21850000c0d4002c0c151707042e80d00d020302c00c40e81641d810100c1310006c4800d5509000c0600800760400e12440703440814004460098001140b040b0000c80320807070710103d0596031105052031054884c02240094130148081c0d119241880d0f0b2000003190086884074a605002d420b602c6103800c1180c0182c240750411a1354882d500d40d641c881b1241d8011141615030b9030607600c0c0c070f134001e000e60800140c004100410100b4070800c09280c010910300c1a0754100d408650b0b0710300c941812269000c180e80c01c0441e9005159426100d80034407510541401d03490074505a50704004041d01122041c18000007001050042104000c40b5442e43d0380b0900700d0b0500d08050a01500d003041444040314002c00240c0049495442030040b00f02c01890344109180b0360510f586007120640062440c40785180d681c00700040540e490800914885c0250906a04851003000300c99054072402d401c030340d00449034004690303d100065400401001c0d000844a5141c0e00403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 538120890 1250 538119640 538119643
    0x901021204061a0424060c03020c040f182012070306020d0617030c0606060c03030a0b0114130e0a0605010203030c1303060c050a020606040e0a020603060a09140a1812050c 75
    0x102c42d6540091400c0c01070545010548035508030400068960001c5d5940c45c3c00c102c2c0e640055400c000e0068000d41c0aa140a00301a0881c250f221810f1401081c3d20700c1c80d600d04180300e2040c04007136402c955105079500ca005400c66465035600d4054076000b8109484441160343c64a040c0700c0282040d44c0044c95a8046106501c0388019110700880c00400c50018444c0e55502d800a0400d9242400b450002c107076207182c11803c4a0022100802540c11584c40902000003003041403940b07414481814402c000707000300e1a0007070121050b00951500110b0a10900003114680140504469464040d040c401d50782c001059940c01003000345656600c888140070154040002d40c4020b0500d814540184052034000001d41400711702503084a0302e035500d41c0304100c1035640c3d409441845800030303441c080160818a004592110340540f084c0b41c07203a51881d800b012190361041079412100e2002c01c1c8208400303680070304020842d01061480140600b41c4070b10207401c0c4141007071403c2c0030000409040c003a00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 538122140 1250 538120890 538120931
    0x50a12170c03071b0509070e041e0c030903140705031c0f11121e010b0a03020f0301030506071101061a070213060e07030b03030711010f180605040608090102120406 72
    0xa90303068a0312464581307000300c40081a852800b200d6003540f113022420382070815200303110b06e4030740c0d44440c4007203060010f10008000020404800e00148825880005011f020300795410350356540000f120000c6040c0140380c11503e182104111344100036070004100000b058401808000003204000e400c00c60042d00108201c1c010510341e02e0804020300c0c2668141c2c000740030340707140d5405901104c1c0c1d01e021241480c80905c00303404141d14200d000600c0349541020141c100b900440c10014600010745400e040d244e0400d900807141540b0910400000a5206000758600d04241009010850504c1000b400d250401c142088449201240c0442550340f80c2d07041100020407002e08020440d00d9444400c04031a0072290700c1d021908095400c5020300740001110445508040e084540100e404011034500044690000400007200d52151140f00c4100e0321100510880d26400e80d03035442c085020b4042c03d40100a003201d039206001d00070706c0142c00c0d1903260303000354018400101004680202c1e00400c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 538123390 1250 538122140 538122157
    0x14040215160c060c06320901090204051906050303190c1505090d03110c070530100b04050103050606150f0c031c05040213090204090803040602070c050a1217 69
    0x10169200054240e04120010125409804140000d8140c03c10021041c0515031100006e205100c545810010191440603080516680040380b106402d80001e400ea41090361170143c105910204602101c3c0c0310310882c8000d010903005035042400c00c0d8451210301c954542e4a1061048024854080001d00c034580520090210003c000f14100504103564448070247d41401003458448a20319034940c000a50b0303660707801d0000410909090800740000f40c00c4071704468100403140444180c4031140900700043c41c100660007015200c0c92130012000741d41466000d140a203280000500c042640461419440744055652504100344640c51045074442d540a4410341a8081002105070401200600d4140000301160020050004040701200c0040e00e00a510031074460b00f6410403500341e04001c80d081d0004000055080c44c07030700c403015142c0c0100e404581e000c3d80040c00b60208035484a40c84041c05080d186481d61034209085c01c0301200321a400030300b40d1503006009880c08030b0418110303035020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 538124640 1250 538123390 538123403
    0x9040c0509011409030709020c0c10020607020d0504231906030c08010f260102070602030a0f1d0303060607020406081605150f071509021e041404021516 67
    0x862412000382260401c405040c00643d8480e0640400620241503070a040c00050250107041d00e0200044020340c041040d050880c010310050704000c1d82da00800002c80603039034000e00390358500030b14024100301210002c0c00c01d00100340003d00112441c1070710b41d126003040700c4c0309240228206000440300030007517800c1ca074244581503001c9585581a04030017002d6106407512420303640c80f401d15051820181c00780d00c0c0c0400c0800d403040005020302d064080d040c031a80e4001454202e15482da003080c0d901c102d6909600944030082850300c90b4507485000d20103060152524840c61450411580b41d21000c0c2c04a449120085040d8003556510352001d001040c1c41007c84910300c600f141171110261491003144c0c130909028401070350050200d401c84084203c241281d600d40303812076a41002d004030380074494200680d51720504c401a2140c842103525400304000c00c1040c05200000c1000f981c500410280400e402841031200585030305120402c401840d801030b603151100505a420381321600038014150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 538125890 1250 538124640 538124651
    0x5090c06180a03080a020708060c1206060c060f0601090602010c02060a050601090b070c0302030c03070f0e1801140604060f12020d0f08070f020a120f0303050c0d020a050d05010f0e0a090201050904 86
    0x411a80d01d0082c0445e451350703001d0703074405039688007141c0e194001190000c4079100c013004201c8003044115042c507441100140850f0501c3e0303400310b02d145012402c07601708030255000002c1c40455a003190f01c04009110602c02889842800c0f60700039110765010300b00103c8c0341d481d90042003c1e03a004074044005441151502d80d10354a4a04000011241c14801603001c0c6c000c640403203c0504000c100c02007030b0740000c106030507424940705489a060070000c0600ca0b0400070746410505d159001c1c010304880c1101313030010440340c0c102141040308484865114520b00316a440c400c100d03400c1300854072540180c044400b101240d80b40d0401040340c0039002c1c001012900c1c00520102001000700300f6100c1e1030b000b940c0018001d9210607003110b4113165007030060100c030204014040000d01c40d821955108000113101800e2401d00c0341c030300b010fa0f0071100c84d80300420804034800354901134030700c40d00e401800740d5004015203d191180595440d88060041550240c541c1d20910940e401481110b000e0000034004015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 538127140 1250 538125890 538125893
    0xb090117060120030715050f040b041a0f1b0415050304050304080303010e1b0a081602010b04060f0e0a060e07050708090303030c190f1227050307050f0105090c06180a03 74
    0x41303e600c00f8408882c81b2908a4140080004901c10244240040044900a51259120348aa200c4010300850b0707603102001314401d18070080400c05000b00345000100f160390804036481c01b003509400546c512904c605100410000d114561150700c02446400d08a0782d070784486c20044d0139403143d6089040c0c079120000001821004042c000b6201e010410080d101e1204c6200d1280c1003441610031042c0020a40004a0f000400c008191040500c5900001540e02100c0020400740d82046c1e2258100c000c0007001005010403014901740d01c40030040c07080040c1d900b00451042a040080c240070108540070604008200082c0d02f25940070342d00504480d2a842d2806044140d9403000070307880b04d501c180d41049151140102c5e010903070140310751201481e01102d413036404000e111407102c0710600590407901c80d82012480700603500690080c00615910043c900340030345006914501e680b040c0c1e142404020021001040c4081043c408036680744d42c50f1428812604440b10100c1200da00501d580390000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 538128390 1250 538127140 538127143
    0x807030b07020d0c0803061005090406151d03190203070b03010905010906080f06040209060625051606090303050f09131b0f0503042d06060f0b090117060120 69
    0x9100700c0141e801c0302c03a01c0c950003100311a020030340100202502c2d02840410b0035403500324901049040c4e82e00d485070421008800181c165031103a07020410b00642180340c04805603101c1d80c0003550107541070202c1e540243c01004a03681b280e0209020100f8107070303580c18004554060142e5002040b503144401d8595841e086440000c003c00e20507031030310918100e070004081d070010401030f91090401d005026159074a409000d00d03050010026540702c1420131418280c0381020a2210400e4810140440d46600d5440c01c3c03850540c44580900000707200c00001c00a039940008042e007135a40c1442c0407070b152010801040e02c1405540d80c040c1d8407801f030380120b8466500c0741e40030000b40074078444400c01d9016940401c0d170f40d400d040680000011400c0000901007607507188108950164440314440304160341031b0310b01c04298462011078845881c0c1008102c003a00e15107800d4003401440f17450524000c11440043c101401405c4806d80c80c101c5540000d049a00415100808181d414900030b1070b501d2140c0e80c0d0b03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 538129496 1106 538128390 538128413
    0xd0e07080a050102041419140a030b0103140601090b0109060309150204030309080708010b010e0d0606080607181502070e040501110f030402040b150405120304080703 73
    0x10310312010014100c40074003500c001602c5504000314110f40c1c2c03200009092003070808800e06000c06c02d0740304c031010858560f281c3c000f10405005020400400550b880900700a6a09000009005240c1c40c00c0440a40480594407203030f0301c60700d170313002221540ca4180d400100f040c202070050501035445620258050f044a04000507201c1061050b40e0180c3c00403000941d50071010849414200704040c0a06500c1e0001d21140c0c042000013454402400301036445000c0c007501e50b0091140c65031160000d0082441564418681038401804802e201d5001079925602d0309000601b0140c0c140060b0f9960b0300390342c0500044c5203803d0a9511480e030280099481c2e541e2810240103480c130380c5004000700c00c00d00e00f4003500c030310b03041c010001202c42104001e8099100c80301c3c42050001e04404980940d80b003142c5042c90742043c00119484e6010b650007210280c0f02d000c001009204004411 = true := by decide +kernel

theorem cover : BRFrame.Cov 537949640 538129496 := by
  have h0 := BRFrame.cov_init 537949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 537949640 ≤ n) (h2 : n < 538129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
