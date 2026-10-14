-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0416
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:42:18.373338+00:00
-- url     : https://prove2.me/submissions/d0600158-4c77-476f-992e-c057ba95cc20

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 74640289 ≤ n < 74820145 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 74641539 1250 74640289 74640299
    0xe06100b030115050c0703020a1d01060509100503090c030609240114061309020418150501022a0a080703031106011421061009060504050c0703030b0111060c1201 71
    0x206020a03c00c0c419200e001c0c40328000140d0095000d031050504407070031244425580d8000511901c00382d484000004980345d510702c51031240290035409800c240c188245400ca020002c0340d04480380394082400c00c800800031601c003080034882c0d4490344500400300c0d4400e0524403281034480c121003807802400c100301e841d02c007804602c40d031015040303541141c1107035400e201600620040e86c0c030080550f040480060004140103c051002d080a0424204803c000d0b40d134440c4803000b1038840f4141e0040070006e4440030031251b031b800108400a0311541040070840615540081d094034003090a65608c07206440c400710314100001114800c0b87d0290b03940c44598400d1280b40c3d5110300083c0030343e40405880b14404905401d19140755200034101c0802070384031800a05c0c203582004000d039401583c00c0c7e400002040070042030b0245001900c0c04417410001414004281d02080c400c081009040c5910390304041c2240c0e0255944104141300c04050303412601e4501e0117095290701c03549580250462034000131407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 74642789 1250 74641539 74641559
    0x180f0a2406030c020a06050403032016060f09020a140102060717011421010c1e05090d08040e04110301050a0605030c011206090e0714030114040b1302040e0610 70
    0xa03600340100360429109051007002c0b405086440b0341542544255000140000d001e480303075910075800381e07800207489015600b5120340c24116607100160002c05111070f01442e1191055400801e40c4800000b8000b050144100d018201c00d00d0041e503c400c00303220000d0741c2065029480369146007682626021380d07031010207a422003003405a1a100068a60042c130011080341e0350b25000100050800054042541030443e800282d07401418003651a40f40340d0100f6a00004051140543c1001c503040d00d8182080c01800f50042d0090030340b19480b0409010305011050003258040c1c52400002a000d18142c105110a00d10200040303009600e044009914200d49208000c00c2e00c1008001e4401c41642000440c0c01c03011034000c413401555212030004040d1140d120750b83c00e11446d440503080d914034100c40d9081102c04480014080c1e41442491a05050000380c141da00c15803026103000d940d228002d01050b0001203103002904585000e0702d40490b00c0d00007070998840c2c54500302c202641c0e51140b030300ea0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 74644039 1250 74642789 74642831
    0xa0b030105040501210f02010302070c061d030303071b0804080d18120803070302070203150114040e010b03060408220603060306050a0c0e040c03150b030f07050403030e01030b180f0a 80
    0x164040b1046095a00049440186135106c81c0149005030034601180c0701c45041015a9100c031011030121038400c12803401a80700e00301056002c8014604501e4682c2024243c80582c022401503800c014010b807041208900c240d8010f80a081e0031240400800c01c0081e181c0031300c581c01e03500f00d010003c030b00182c0001c0d03000f410ba541b19400b0010ba4255110b04401743c002e034000a0003281d00d0302580580000010601d147c0d039008000941940020494602c00d01c001c48002016003c84c5074140051801540c80014801c0d4001360300180341503542001d051900c403056003402010b9030245c0140740014646516810000507240240400c1040b0340768000064200d80d1500340180201e01040310300c010900c0c1640c0011001c0ea0242401f10f040d6020804100140c0710717542100d5100c180100900080c691030001150384000c090070003510302800c688000d40704016140707009041541721410203115440381c0141201344100202c004007581043e418080455130203c8100d4032880c40c003150206440348004101c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 74645289 1250 74644039 74644079
    0xf010f05100e010c02090411151e0c0307080309060106090b0310060806120105010e07030b0312040b1c0507022b0503010902030a14040503090f010f17060f0a0b030105040501 76
    0x81030003804402a500d9480408400741813005058520000d0b8440b078000e24426032051410500f20180081045290346a80c0b2803c07181800500220700361451451500d4028941d0301c015a8550b4000c0d842d603481d522803d0701c02400b0f90004000d1000c1074400244240c10f076140b50312180000d0346c441181da00c2ca0302003100e88030f41c4560140d0007003200034010746c49950400c4d0701a042c02400a0380c0682142921001c0c1d0043c541000044100040d036070341071185242420045002c1c042240342d6103004500c50007140914449580001028003014104d1080050031016141084c0070702d180501c4080e46910503008469176000400820b0300c000c00356400195402d04850f142c1c6810343c2d0030403e03800000d401c01401d130765a503a581d0814210804900c9170040c0301e1882440155038894619061119000003204124180841c400d0145002c0f504480c0ca8404c03417081a10b02565030703481c4030008005401d040001c40d00030300415004100b02200030011810b98100340d9042c44541d07a2144100400c1d000764141c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 74646539 1250 74645289 74645299
    0xc0503070506180f04020d020429040503070e0910110d2f0f070206070807060b0603040b04030804020a0e0115030e0c01020a021c15020405010f031a2106010602060f010f05 75
    0x3040440c82d01d030702d04d08400300c0040c2c00142007040926100040780e00613003140d410020000903401490042c000340e1682d8691980415040c28601340c0841ea07640074a000d810018030402000901203441084880d0101401100501007501c104030100d0441c1d10200c8100c1003241070141420180ea8141c90303202e400d078018000d00740c82d0208a0350441194011100c202e6003040208000d030f0150361150058041d460180d4415030b512651880c0c29811520049070182c000c00341401040003091204807410343c050342504106000da41c4c1c500c000740c1342c0e158a4011700402189840046002e00d0900d00d107980d0007005860400c0356002c42081659100100d21050f401a84540300d858010b0a00c0030071100c01d40c07d82c5080b00f0050f0110364a411781061000703142450144e001c02e0400556030300920b894010541030500700507a40313122030208080c6900c0c1074100d002e40c2001003107450020312498881001d941e1082582da4658440c00029260309065840503202140c0703030004a4001204140c00c0c080342c1d80181 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 74647789 1250 74646539 74646577
    0x901020f0a02031e07080304151205010807030201030b03011e050702071202030601061809020703020a1218090c02101b1103040806010e062b030201061409060603040615030c0503070506 81
    0x940d800c2130f0003410140d0040d000300400003420b4401000a0000340240118402403003480c18402080c10b442c82d1034554065040400400045201082404c15aa028640440d80741c0500c0c021a0240c0511043c1a1120044031441c81d5404220784c840c80c0680c03001e13802e60741e40d26500c6d100301781c0d500c1081c20080e5042e003254004000c00c1c1e0043e00c48100412040b181c0c84a51075440200c14200e070424401600540c100d080000200241101142c001c40b5042c1044909000c9048003410504034500420840966540d8516100b9008202442100e01c08400c01e11a403048440c00580c000780c9440c411002c03c81000980c92262340c0030041e138080d02c0e00d04009140c240e180222000071a40d0240081e07801081c80411921343c0509042803002030354003088103044a24891030000d08648243c1d021044044042d0420341603a903031003014507007201045030302c10f0310381d01c890904400503c0036000301d8203c420036410010400c036a01008400310f03041102507030031003665141032211501c03454002c5086440460 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 74649039 1250 74647789 74647813
    0x60203030a02030a2a020d08011211011b111005040e0705070201090e0a0509060f060105040501080907120b0403020f030702010519090b0f0904061202030d0c030e060f0901020f0a0203 80
    0x54043c550080b4464000308100d182004501c001c2403035041746000410440c43c03101003480d010444101020250718080506625281c1c400c0080320050b0001041c2d20000c03c1c41c220a60b2141c05221307044000003101c1113062000f450091001100c486195000e007031000100304041d40154141d800710742c47e0352417000d003583c3c5100d000c40d980d610880c1c08a052120443c000b0420f02821140c1d00d02c039081c0c01c0700000c0d0904101d02101d1030140001c02007040000580104002640d010b0700b540d00701c0d41d0a01b408039003912680c03d20f504050254101907014500b07682d0340c03c140041140d00f140114001d400f9a07a41910044100d501ea22440ca4080e02203541040407402440550f44548481c080d00d00d0304046054503591250000da1100c2c2e00d43d0b60308407002c1120146d924103071246000400705280b4160040e40183e0100340ca0340030400000c01440789540c8144149400b4140440083d50010529039440469000c4603415800c501180c87c0148601a014240880d00048041105070010002c000306a282 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 74650289 1250 74649039 74649041
    0x807090e01110307020721050303150f190603020c01020415030204030b0907030c030b04080c010c0305060406050d0213020a090b07030503010608010501030203150f0609130e0d050711040b0402162604060203030a 92
    0x1400607c82c03108084034a0003051050018500810070122084111140e050403c18094000c80d000713032195040480b1007003032048001e1003204a4150f8280580c41e82408100d281c0207015a9010841c0074428166a072061581030740100107481c42260090001d4440041165845500d80401050503120140500100320f02d0a00ea9034000d20400ca20303841c1c0046030741c4190a45140403104404a03881e4002e1044503d024041c1d03130094035058503d100300341074540003d8214050562a406081d41c00510050b60611985194001e040c100803400e607035400f5407800030040d80c000d210311380011366040004142e961003070084a014a00380344e00000480c816204100420a4048066034022000c0140c40b0031500d5025403103602c440e400d100002d00c0920005e23040e04240080d0b94a0040280800181c0300180e2808090740d240c210984000034800d501e403020400a20408640e00349650540000d83d0400c04100c40400584410211208008000006035600c074000c900443c401740c0c0080c0005501c942c25 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 74651539 1250 74650289 74650319
    0x1e171203070c08040b160b070e01080609060406210c0b0a020d0315090f0f11070506011505160615050312040b0706020403060204031a06060405090c030603070807090e011103070207 79
    0x12808a4036203035480311800103a5205843c0101641b09a14140007407007120b00380c1e01c7c2d10201a044c160f115541d4500002c0180000500c100c0c41000f841021610380d4070707194070003c0a48070b20010781141482e24a900f0000c10111034088508040c1e441005c10200000c005036005107131107800811300188112410742c05080038501c680125070030700b20005071035901c50241d9561141031000c009524455440b1380e0081d20280040b0060903103041000381c0014400040aa044440610003914412090102181c15109903101079843da03c040c078984080c00055489045402d4001d06081d2500d070b900c070281601c0b81401e1005000c100400d000070030021707141c14000d04141c0e2007614010700d401e80706d5031610202c0c3c0242d00160781d100300340454085641c42c2a584141c0000c4100c0c1d042d41130500e00710014244000c01811075242032301c040301203043e035101000704d100039115903002d544409841c2d4820400811091180f03d04541c205056070921406c070310101c07030140d4095805440c020f82029084150710300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 74652789 1250 74651539 74651543
    0x10c0807020d1104060f0602070b12041211100203151f0e030709020403080306031b030a080a0203190305060a060309110108040201020f010501120b0114030a1205041e171203070c 78
    0x111aa6a400c825139480c030616018040c0d00342981091406d11400a01d0610241c003e003102e07040c00c0200000a00304003d19562242e401140030100e040150741c21105661411318114851140003600801d89030503402440c440c1261012500b0340808035003c00c21000010b4003400031034000307006024101c0d840f940148006880242c119000f032070762203100b2022a8040d034003d0301c0200010007800221715040c0250906040040b2001d907618207031600081d20340d5504036006054000004649000703d0080c002e607128240b407400450341d80c081918000c1c0191801326080c3d032260b03210480c085034040c0a8032501e00d00319004030350100c3c4142160015502d20170b0150060f81984600c00b81092a96030074000c41c1d01a15070040130100c40300b024a010f080248040c0c02c4144668442d044401080c0c40c0003e02300b541e690004001300c084a107082050310b0520682c1c102d1614951060480300021a1740b1104030304640c000b00c61181d4600055401c5078981200002c01d154281080006c00d00b0036114119001e0068 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 74654039 1250 74652789 74652803
    0x9290d03111501031223040b07020406090218010908010e150417030901060f05010c050606090604020904020f03220c03030f0203041502060603010b030d02030a050c10050711010b010c0807020d 84
    0x26001000160400500342d00885804000503200401c0c0c0b680000007091140740700c082d202403901c000016101b207014600a451642e40c02094610a56845800050080c0b506040c110340c7c7d04030703c400a40c40c2c0d6003c2540305011030041800042c552405200f00342c0d811160a01400c0c0c8107a9100d6441244030014001717542d60700741200300040b0348070201c1c002c500031655000001442890f00b0a545110010390780120305122282d944034002c40e0011803900d90200045483c040141c0c0c0d4400041c000303008155081750014400b00d98510110342410081d80101d442041940d40300fa01484560078240c00740400074a070100b400b82c1000003901072040c1042c400c42e2030054905058441c2c0501d0020301015041c24010f03881001403240030f0030f0a00c520440e050068002d08820a842200a0b542c2d2040307440100400c800010502c400d228107000044030410304802c148070900309080001c01412500442c0101c5510b445c0341c140b415030183c000140130a620119440c18003181d5002c000007188407140a440407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 74655289 1250 74654039 74654053
    0x307140306040f0c2307080d0e070305030c07060e040905030a0f020307020d0f030e0108010605031504020403050d020d120b1305270d021203010e01090902060705030409290d0311 78
    0xa0480744c010031603036034816a101901d00d4180c9060007055022601680817208040000c8808500c0c80012100c036008180380200f083e002d0b203c822440c0172040d0b48060100e010201da0740c480c0380c2c1c2c0443c0040490340c0765a42c130300c0c5000d442010403007212006000104541d00400446c0f44013801490070b11507224a5005590418045401046c084104c0b40300031690f81c05a03056510405401a92403100c60100f841c018205604041014001d44000382000c400c0c0c454444814041c1d07543d40e01141d01540c3d02c01d00b55800c010300c240e0040d54641d5041c4012010503243c2080300710b90300b203612030040d1184004140300f9040902c1c080540c0180300c0034203000c0e0b000d160700c0480c8241d000e10308403000c0680c1101c4020407140d054400e00a0078030901240300d60305c0040c10801041a0340c04020142e05407500c002000940742204c3c800039601b4461000010302d1404007203000502480b1903801904890704108441c12003040d0b00858004800701d14580c2603100b0000750000010074071440082601900c0c0b941220740b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 74656539 1250 74655289 74655311
    0xe0c0d09021c15180507030303200403050c0306130305070813080a0b010e0702010603030914040905150a0b09070f0c24021b0604030906260a0c020f03030714030604 72
    0x3691052031425030312040b0300f50360340b40d10300301521a8140100340344800d54a0003486545040e1508060311002e01090344403880907185060804440f001d64101c428000d9641d81e8038a8410b07101d901040c03a240c071034040c403000900d2054441ca40d030f02c5002d600d6518a0300e07161480d40c1e421000e80285284105044041501203401a0f0401c41c01034414000c806429441d03144c0341a05110300d100409107021a41001d101300b0010740c1101105081c1c0e4180081c010301c100e20840820300602403018050140d00c070b503000b10050f50f440b241502d405807045403014014014009c050110300e210946e0a44000340000f07207520b003054400c0400c469901e1191203105008440754030f40c2d1414108401040c0c00e2280d00064184810001d0b9408050280d401ca002d0092b906e01030721b0241c2a025248981014484244000003c0d81c2c6400758000e20b450f03000c10119824141062240b000340034402101026105a841d14150001c002098a10940183d521142c101070440d00c800c0c0c0c650406409030b80c003d9110005940 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 74657789 1250 74656539 74656579
    0x60204060201020c0c040b03030f0c0a020913050c09070f1101060e070e04060512032b15031a09120c0c03030301030303020c120a1209140a0602040603060e0c0d0902 72
    0x100803903800961102031000c02d00d03003440140c2188510580c80d004500185490200030340f81404000690f6648071901c000c0d05c4c1d410040041c500075800303e82042003000883d101c035000003a0070b00410484a801c0d00b007109203e83c035101071701c01001040400d00d01444040c411100441c5400842001190315650fa4410400c1440161103030400700d0b24405200b80c040c1094441c407001048104c03110500c0c00e003000c50341605e170311070701880049040d4680882880c01c09858109171400c40c01c403c0400000701d003800d44c100d20b00f000b400111103c14882401d1103c226180818601880424020f404288840d03e81120980c1c44081c0050003030141c0c0b0a00c810035035051010314021402514050390ba603683c1c100040c1885810349a2600000d81809008011540280c181d689503c8a420014960015040602c201d03408000c080800303206441d0360343c040104c20340250085404586042c001951640800070800304200c850307111541043c03204070340001480d00592021800900708241e2941c10154800c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 74659039 1250 74657789 74657797
    0xc03070b0c011505150703170411040c0804030806060d29120304060206130809040905100501080c01020c0d080c030a09140402030402060d110412030c0203070501170118090602 77
    0x480800e8000c9030081c1866002e009100c40100103045240d02142024001106445101c01e40b41c940400803401d0020140a1442d0f03c055010398045c02409180614000004a0540b01c1d601d02590074500682c0155000782080d5001e198107440b100626558001840560340090684104607911545005104101c3c2c6e18203180c05502c2c80072840819584100b401181446210441019841004200495940810040d80019610005070a40b601c6400c043d6481c2c01420107155100f46841c1724003003044400203a481c01e000c0120b801303200749e07a07982002d9900d917281000035070b001da080719003040c2c1545015181d803011144112681410b10b240b01040c030340386821451031640030500c050340a01c001c11901d840020740301d00403a010b6186150960103c0d080b8020405001501f40e1a40040801c1c60f9034481920050b110705251491807030403d0500600301c491466069010340110799002c5400c2d440790018005d0110390301650306850f4602412000c100c40d14210340f0004035030313400f4030310002442030000b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 74660289 1250 74659039 74659049
    0x5041b081b040e18030406120b060418050a050f01120303050603160308030702060903090607060c0903050105070c110d050616020c0604180b0108100b0f120108061017061303020c0307 80
    0x3d4201d07240c083d82031a000700c1200240480c130f80c4280020003196601c4055040702c40380010011624522101c0490b00a0103030360000340e4507807c5515008480040740d80000d01c10180e0358010f00664481e482c0e40c0c20141c0003802a001c10108940d695800709009800154200001038111800b0480307031020104c441d03006410480c1d120000005101e911903041261580000007031015500d08410349000401d184541c2c07000070701e1b56840c0c60707040c00c1c461700a0104000650304100203000900e0034040080c08411001d400725046c84041c0769000480c1403181c01450b2441d48400144034235141c42010036031000f0100101c000318850f1000d000750381d441c1c10b0701500c0284012040c2d41c2002c4180e0b10601c0540e80c2c1d80040d0780c1003104200811416001d60300f01d10040b620704402e62562039400d4076584a00b0b200c2d00c00481b4003040284000135800c03400050480c4107150040c444081a138595001040442c0241140d0403160b0080002c0f0b014540e2107220620928841d0044070941c3c450400400d00341103c030307400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 74661539 1250 74660289 74660309
    0xc0609061418150402040f060b0d1103010812090604080703060f14040203060c0f0c010204030c030b10030809190806070305070906050a1e0c021302040f05041b081b04 73
    0x145031400702070700800c542040e01003000061010040016990b202048080741c603588002101190654881e80c1c800e44000d0307032058040c051683c40d01c0254095901000421603039a00c2c1031224407000b000b01c401e4a0580d60024044c0581d00660080c2110301d03000394404507484101080009044e40c41003007030b00000c1d886194003140b00c046000802c0d04498501d081e41c0c2c480c01e695000c001c016038022035100c0d4400c280c1f5440380d440b01c00341829441c560154a6038000c0c190300c0000c01100f031000001140d000c6171302c541d42d90005c0303558110a41501a0291000421600091190300e15900e025510070288091440760305811540c2c0b19111440c080c404c4d201c0c000071035541d50a00651030390240b000030142c2040e007091450b0551540d4001c000c2d00803500480f031031403043d284410041d84039681d56103d454000b046140395004540008000b980540714000503d10088000503150500e400b520382e02400052485000120b01101900c61000080071512007001c00b050304141521b0547c080c7c0060189555 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 74662789 1250 74661539 74661551
    0x106120302011e060501050928060c02030d0905030304090f020706020d0e01061a090d060902090906011503050408070b100b0c0703020406080f06011502070801050a0f050a0c020316030c060906 84
    0x7103d1604804001c40002c000c90600d07a0510076a40c010b000c9030b007846000d0751031240408841c031080c0e40e107507404010103141046030ba000141080d072010000c040306000301c0a072617216031001002e5420307034074500c14a90180c1080c0030800c041070b0306a2000649070910031000d894403c0b696140422603110b542c0030b080f900e13652546490714403001d10803113002d000c00282c0340c0300f0841c0c1c030503006406004070b0943d903200312040d0704090104001c90b040402c01c958050640d11b21400e0031001c1d903440d084240640c000b0380103030041d00c0204500c40d0050a0060742c0005071945041c03265156441030b00c1c001060600a00301074540003807185003c00041c10020003035009001510b08600c108000e0700c943d0b9102d1b84081d8044942d107180c40301c010444e241100c028550740c92070004503040503818003145600c0341030b581d4030301420007200500b00d8000d8513020f020500308015039943c441c1c01d0804c85020205580044e881400404d40807102400b40a034454001d0038480e051030119900c690589140c4201221030586a103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 74664039 1250 74662789 74662811
    0xc1c021006062102090a09020a020d21050408190203040503011109060301050f031002030921211f03051501061b080319020d050f070c17030603010612030201 69
    0x200800c180e41101960070302000b850034400910008001d03480c00340c105056041c032440f08900d039048400a41d0b014200d0401103565061400081d0080a070907000750140b0350481d000503208a002c201c44241035280e498103038250111500050030001d2040711205410440244400c00c42005d104089909038000e41c0d8660401e0300b85400c1d5010000c03440a41d14042c000d50410340c0d5114156815a82d041c1c904080c1c2420610000e8a0030340702c68441d580c15840003007800407011000c0b42c001c5403100740390b0031422100c000489401507413080314040d00c0b0003a281d201809540b0003000103d41c2044080c142d19504081140f906c00107103240d940115071035409901c140700c90b01202c100c207038018051401c00321540180c2d2004205411080003009240700750000004810044c05405e00940c0d100c094021501c0b5401c09001d0340080005403851b111210184002a0050f40701302140781e60580c1c0080e00d4601c189e03900843d03404680001e80781300d5041d5212080428100140c113003101956000358004201c0c81d00c21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 74665289 1250 74664039 74664043
    0xf0604060606090b180625020f0d020607030c0203070f0b07051b010f050d1404112b030305040c030b0f010f0603060b040e040c0b0a050901030e0f0c0d05030c1c02 71
    0x9034800b90900039901010400640250f05642d00f5110440040c070303000746000700241d044d01c140c61200c1d040b29420280d5451044a0301d45003641d1078400c0c1d4444d4000303040c0e1000c00c40d01120441c00207600100412440b00041d100d86081c104451003d81100c4c592519502c1c1a603099425800c009003204001c190903080c00390070010010000c0c13102005600482039840005c0500c240c20441405000d00051081c0c1004001d0340710075001d80500705030080078185407501c00406c0c1d09030b2640394070445400c4410080082089440120254900c07403c0000e101655410390181c20010410303030303843c00c0c0407000201048003c00064425041c8850b82042c560400000940351181e0303030444810540307404000c5c005012018102c038282ca46483c0b000302d850390740c0e24120803040000d400400c134020300070503c482d406030410042c1040c58826281800008101008266120440104408c00d81d11407070111200e400c0c25840a010b0a0041c02079924000400565501c0c11640e08061502c10340d8925414620301e81c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 74666539 1250 74665289 74665301
    0x30c070f03020d02210604080a030e062401030e0d05070201080108060609041e1703100915051c0b070e010e030f06150103090f2006030c07030518030f060406 69
    0xc895516040350031600801c15034002e88070000c1c000c0c0c410140d001c00e469051480303610420460012203106107006d203040400c035008a942c9401081c18451282c000344000706405100c0e8101a600c151301071003040307a1040303410629040700d040c15944c10540742c0b038600030b01c2149182d20b5551a4190350b200144001080d5510580c00700400b50007000522500d960ba40d01c406030081e0b080201224003c0d20b09400c40c030390402d440001801500307910b0f85100590305404c0607500ca0900380030f00126503559441c41074199074010001040c05401910309028500e041c1c000c01c4030510002d803031001018003e541d020f440a006540a001140040c007d080303166030b101072440c2c0c80381c0060740030740560507190000541e582c2018224116078928410841c0e4aa44030350701a890740707900311b41501500e02003070400707038048007541107805640c00c01150040070318100002100c0c013138801e0441c4103142403a59182212181c01c280461a551050000d000e901503404001038092403240c1c0010b0145810189007840440d41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 74667789 1250 74666539 74666549
    0x1018050307120209070807082703030907060318030c12140c0303010f060f0f0c080903070f080d020705090106050310092d0c021213080105010803070c060c0b0a0b041409030c07 77
    0x30030b810070461040c7c0e200034009e0f0022070303650010280f0442030754000300c903032413089980b6428070021080004419000503018102c80064404000211002c42c17040002d40c2070350070240100300755000300000078100f04640346e43c4e84c1040ca482000f800c0d08586c551002c0d40890100783d181d40c001b000500c2481146285240201a1420b01c2c003142d06207130b00040c00301c0110080340401d01005041e06007d002d030240c21180c03100802001c0e203060a840d0f0f4170240100e00d6074002c4c40c20310b10441c4060709645000144490690760001c1543c0c1c0c0381e03031a00d1000c840c00c3d840200081e07201003480400259403e503074010008460f0304200c001922441290380c3d0a003200c460340e2100d59403400d062008192503004030f0094401c80202c000640e9424202c814610aa001c0b544004413075841d000000030040d40100c00760039041d02c01d15940c02000d0395041c003241c0c103070030654000e000110004007140b102c1040c0d902000c52070b034024102250036945000094201c0c0001c4506800c160000290203800c80020701546000e00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 74669039 1250 74667789 74667797
    0x2d070f060c020c0901090f06030b0705040e09030c070e0c0d0f020c010b0108060a06050d0e0a030c020108010f08031603020a05060708060a05060f0f07020607061505010305010801020306101805030712020907 90
    0xe0407480014405020602c0742c0541c40384e4544580341c1c6091f154016501071750b007080882e100c2e0701b4a910001c1480d40035118542c1038280220200f81454008001c607019003030520004c0c000d036070500944490401d03001e4825900d07100200041d1245007414000c081e80c1510b1564016120301c030100c42d49003520561001113041042e01c0040022035074036101000d091701c0c003500c0c040f41c440300c409008100034500ca042907200e40c8180350314081010781c020711281080f4404e990b0160580d0b40c0740001c0802070050301800c0d0743c40e0020b0140150070b40500801c0a2807a0007441129840545c50300c549040800540c2d1110000c0c03281402c204590804402c0d4200409040d40c00301d11300292803801003040c0c000c0c00341c3d0358000e0b400010074809540d11001070310b5503d504000c041064101001c00da040c142d04d9407240902203400c02000082c1c02e1818400d8a10840002c0c280104080c40701038112055030551140d079504500c0d0b0180818140c400304041005040324110350243e804441c010000304110040c01c0800300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 74670289 1250 74669039 74669053
    0x4022a01020406121e0b13061e0b070503091009030b0f010501021608280206030114030606040b01021b2b020307050402042d0308070308040b100b2d070f060c02 70
    0x905c50b1000d07943c4807590303040400600c601c2c1000004800c0250080d0724555641440408a01c1c4c40680e01d02c0700c000c0c05000c0e03030a40c559030b0300c4105000e180540a8060890742050041040c3c5080c03440b480f1603032080710725106004a40329524407924980a66408408120303020050141d5601004144903500c5482258140c540c03a0001540e42c61100280542c4022001c2c00c1103180a070007a00540500e681c0108019200e60315034401c01d48500d00809414464822480451203c0c00c10b0300c5180d80d03441040e80a01801d502100380b1580c0035110b4000d1070342041d0721500114002803481140c000c945c119812110701c100e111700400d40341c0101504901d200380c0c41000100458041c80346103041d0300344880548180300c0e03130030541300c1c250100c0ca51000d008648001052400c0550062009110b035202e044024215152018818040003541c0207064942c442001002000301808003103101d8011003411140030440010481c0380c1c6a0440c40c0c08070dc40300b01c1840a0000c00040d4002c8802d1204244024031705 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 74671539 1250 74670289 74670311
    0xe0a05060a0806011211060904020a11150f2409130c09060e06010c0615030803010501080901110301050118080a030503061509010807030207050102090d0c14030c030c04022a0102040612 81
    0x10006100e08020000c02e0750440e00385e20b0f1f88a0400b03072041054001c00440d200c1441c600058141c002110a2007080e0040c5076140b907815200c950030500551648c100201c80780e988540c3c0499240c801e01c1032041e04185490584e01c159284100786200e082202c0341c0c090800391920f000040d0342c440b40c0110000c182080002d02124040c1c2a05517449242407903d900c10402e6800d10030014080d010180c59024520071011080c40314180c02903040712002c1c0d983d000150307103a0000d5403c0ba40340044103010348c04108010000c1d58454800407240381050460041d83c0c95a42c0c80c014a090502441103000c11000b10400400c0e1402090500c46074000294507440d111801d4002031041c038000b045842415804074140042c03000035810364110321005003550650b03010fa4182040442020b00c228000312140c010b0641540c2070201e86040382100c050000c183c50a066010807010750010402d0840034024129011254050040e8148100f00c407074000582d581d080038030051001c2c40900f0742480310741c104014410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 74672789 1250 74671539 74671559
    0x2011103090a0201080c13080d0e1008010510121416050c2d010203090c040f1e110906040b130e070c06090c080a0303060807060c0209040b0c040e0a05060a080601 71
    0x3010540c2440d00345c07050b41e02c403a035500740b90086540c8101003141c03402012460b1000000e40c02020040c9880e4040004441e40801000300340742c117081030003e0540001049503050030305000c42c030321090342804032201c61580c440300e0071501110800000510040280404030740e000d40d40d520301032651300c2c003076241c011507ea559070707107030350300c680d0004401c03003160342812202d5a80c10940a030788004c0000755a00e0410300381c2d40344d59513002650241700c0d924000d0480030391090b920646d961103c1c00460030064440240d02000200001140d240c5862410400421641d4413200104040d00a113000301d0341ba000c5801d445840403c80d9000b05180309401e80c10b2010300c0b42c100a840a19a80c0000007081181040c5021401400d03968411441841081240801c06805401c0b00041e07a140408580390f141e601c8008540c242d0041e01c4c081e4000e00c14002040c0840c41c290310b8240e006207000100c502d000d40d260400100c00c8003c4505500e103a0741c0b07d050005500e0b1140e01040204103070300c010402541403500c841 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 74674039 1250 74672789 74672803
    0x1090b01050903030319140103060c020c1f1103071703042f0906030a0222111201150201090f0303020309011d030910030e07030326161101020909040c060201110309 72
    0x10301600c0b006d08101e09a03050300400b80015400c2640d01c420b5a50385403c9000c3d04095100902501038000a0451404c0907400003e02c40c4004030000344468182009403400340c4000486402030001704142c9010504840e0320040704001944555920314050a1000c001d0344045251410040c081e04108282460300d140a44882c40895501181da00da000001c0c0c03608052000094103c40d81e200d442400746034007080380c0110303909280706100910700541500014401c540c041111819000d0050000040c50480781d440c01c0c0c0300c1c0c000007500b00c40c82e4a440c81c05580220040340085d40005c1003016180d1f00f8054100c2c1144070305003400b042c2d0207c0c284613032a40508002903004140d20101040c1c010b1094201101d80014602a07070116900d90500034082c01600c0a00d50207c4508a03050314001c003528503961003650205c1c45a280540310440c1110703007821906102c080383d0740a0000c0c030103075a41c580c800d0b40282c1c1704042d0740640d0382c501403010b801d50380112001608500184200544900080390b09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 74675289 1250 74674039 74674051
    0x1903050d050c0702130501060f0c051e0f010515011d03060606030a021612030b0a12030305040c05190503100c05090f120d050d14010303051206061c0501090b010509030303 75
    0x11440c1d640301c040c0303107001e07001c0c0200280d03002d50810504400e1a1551b848103040c0c0f13003e66507030b65192840c0c40041d9564070100d14000c00b903510444290301c46890001721240e4040c1e0300c0080e1000313500590189400d642040c4c404031080740c605c2d01101e4056030010746001280002030002142403000b10000303a101c030b00c0100a1809030500000141e1480c1d920345c11160450048150350508001605018803400c5503c100c401c00710b40b0701601181c1d40d2030b105044d0b104442030b92a4180c042c00c1035075000c8020742000740044075000c20031640440c0fa552404c18041c107000001543e032844502c2d101c2014a0949003030b23040ca500901d00214a0183c41d4800d0031a18510026564405135a6a007400308180c030702a2003440c006802041820000c1c2c9a2000003010a614105414480d5623611078551100010a100007000b003002000079200132200041200d81c4003c00070011424240c0c942101d181640203802004040c41e07480b8014826403145208a4013510307820728046007881c0e2043c0201c1e070303284005044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 74676539 1250 74675289 74675291
    0x17090d0c03121503060f1e0b0112051f0605032202030a170d060602030306130f0e030a0302040810020301050303070b101a0703022401090b0613060206091903050d 71
    0x34080c18503020703088850500c2002c16040029003014048020881c281d40030131914281055000c0c403000480d8010010000d4983c07590706804400c07409a100100100c400f0b44c3d0510841e06100440100c492161602c65131003804029003030200065040e00f00002070f00300340700b44170f002d20511581c0b030140810040444400402070361850540e00000c4e2404040440c0207280c5e50f800803901304080380c208050841c91340e52810a10041c0d45480c026600d83c001105d46070b8200b20180d0b544024590690494480440e803000000382c2c00303211107016411a4081c040c11004031750001010858a802001a42010886006c0842c25541440c0009440e8424500090140910200031644440c003d0742545e0082510020441182c0c110729441803454000c1b14042d8054002c3c170207019500401154806e0074009a01c01c0d0b41850383c24500844000c00785101c0c1103410001c203001402c60f15403d9100e07000508410740040c84103160034003220740341491404262081c2600804040e0000e40c000094403580d030307c82c0d48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 74677789 1250 74676539 74676557
    0x6150607080f040f030507090606080714120106030b030d02070819051213090b10140a0201020408100605120a050d051b031903060b04030803040602070206270117090d 73
    0xc100c901d900a6080007244030000141c001207a401d01c00c09101200e02c51006e854a09689615040848585200b07010105030403100240b086481030380301940d8240e00020700f43c2440c032098035101d03134403500340c110704082941ca03c26592607103001c00110311904128802000600c2c24490125101c000c003040b030f044507481c0e0881e800c0821100344000c010700c420342d1004170f4545015000d20b04000343c1c907105084607246816160b10850425803141d00d64407071591507203100b006c11004a14899031040d001202155402d0201094040090041d800c2482241c600850708a080c0401c000300c40090081305d03d440c0d44004030080025074040744401c00401c0c0c90500b1038683e905034903c55a03095580211398007d00000a01c44080104408444490081580c0c104102138440454003100c0c8164080580340e90300134400075002a80310340050404610291900f07013888503c2980031000f442c885501c0589030030032407018081d568820301101a255010025200c035041901c46e2680b21420b62a09404002e0040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 74679039 1250 74677789 74677793
    0xb01021b03010204030f0f0b1b03060111070911030f070203041d04051f0e1c0c020f0f090412080603061005010f021f02090f150a0c1b03030305071106150607 69
    0x241c19500110b400031b0404c074200c00070b45044a0401e03202013003150115501d9001c5941e10100c80c2c00c01c1303456600c40711802d18584502d401984c00d10700d6001020083d1003117000c085200700300c0f8054040c400c034075024104e840341090020b0418640c4000c090343c1c11540700303110401c084107440520341c2a2004e02d4000c1340141e112421300a003000c5003129222090082c0c26009171407444554002c1440c0c2a01009032100000c00002c65101c10103990031020004098160403c050314241e0460042d07442d00410356840301000030082220721208403002d65800003c2c103680d000194109110130361040048025010758641251281043c008500810741000b0044d5054000c070341c020000710300303650001940700742c03442100c0d01e0880203540448507a60050108040c81c0c5403034284140403d41100790341080c1c504108408008451004100600756080b41c40e12980d03001c1c100c2111022005036000b990702088514002e000501441e81070882c9442c01e070b1001007040781480e00030f0b00011804074102c3c3c3d110340e42e07003180c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 74680289 1250 74679039 74679041
    0x206040f08040807120201020c01020c010e19080d0f080903070308130302011e0c0f020703020907031e02040e040b060d2001030b090a0501140306040809131404030905040509010b01021b0301 83
    0xb60f00800d0443c8a11500400c0442d13001214001140c0300f64226420b00218500491319079040c120303c80d000c5840d1030302c512128601400703001032004107040c41500780c0755504040c41c90000000881d202140724040c00030b0b2a04e60210a082e8407a00f11401980f801b4030715540180002c10007081005103c079054030340010036100790405081c1d20060900b240e001519001d0580051040940c01400f14021181c1c401072140041007180440f900180f005c029544c4859050300900807030307400c1e40d59a4515042c103260030743d080e01c05080908030090720342c0c509240c1840c1c140d0340000080c0c0726604c1000041e031400000b408041d61400310102c4c00c5181032541d010440141c01070300403a4030440d40420100304114070410301c2c3c0d0255040740d0010120080004440c0141500c1f880169400b4001034403c105544a9091401501d102c1c1441041c001580000560341031034840c00580c0c0440020306050b40802492505000e03040d000b1042ca0001c01440fa10000080d664460b0f280d000c404d02918040c400ba4641d8007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 74681539 1250 74680289 74680297
    0x30610060e10050d091110020109030e090624070c060905030a0210180305060f0f060d0b0402130c120c0504050f0d020a03120809160509010519080f030702040b09070206040f08 77
    0x18040c824030441307210746400014580c001e03800501687d40300c561418502e20500800c600e487c0c15031200395400c43c1d51001d0080b0840000c0155820581c107214102d440e00000d9000c42003d0b001110032610340c0741905e050b800341c91065011004010b40c0c01c038140700b036581c089002050154101c8800f403100c16410300540b03140b007241800a030b5014252000000340070002c14024441d20b412000e00440d0359842c00d50f040207800c254ac05a412003a000c042e5000219401085034000c2d000414440500241c04017100a85400b04c1c030300c00004104954840b00d0100501036880c1040d20390421505090501e00469040c0c4d070031325045449601b480201d87d055481b0201807170081c1d90005901e441c07040b801c00c2c0c050300000040d91584014800c80d0802503400e0000040710055840040849400781d1030201008803140b8011241c50050300c04040000f941030003000148518003c84021315154070ba540108807c50785c0d201060b50041d8000780420000b06d5000c182140d00a50011f034003000c440260a1100c06402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 74682789 1250 74681539 74681557
    0x6080601080d11060705120403030603051009030e010c0302121605010204120b0c0705150406021b0601140102060405070e09030c06040506040b010b1903050601030207020a0b09030610060e1005 84
    0x28100041555100820342980019490b1076105000003007060565850764116200800140188403a000000d031904000c0d0304180640b4000c1082d07a180d48440d0700b0416242242c40006079201000410103400580d010704e07a040908260a140d400e0b034402035181c1d182c0e124803c61902000400554285a2140700f10045801000854443d61149081c050307160503180240d8034000d02c44000360282c2618412907014651000190104508140183e80c016401030400c60b2031a03024060110517a821001e01290b01c60158014070407540348c4180903520400303140c5c010341190071400c00c22001c00c20010320b80044407181e182c550500c1c1e456074211800c41c000c214010515002c0c880a10003405800a68a4001c0303004400e51b40080c0d0f81c0d600c001c0001d115000c000452500442c102c50902e500aa0086512600c1810051b286c030035a41d0000b0802e103801c3d0400680958081100f01c51407c04024a81d8030071400c88480d409281005005400381148101151050b090018075600241c400d00544100d44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 74684039 1250 74682789 74682793
    0x8160807050115080304060c060207020d200f011817030712020705010201060b071104090303021c091502070f0f0807060c021c18030201080402040e031c0e12030c0703030608 76
    0x31030700d0928040c106041c01e01940f0300340c2100100c1c0d0b0350b001004480c110b40c00d03500e0b841034a140d60b0307803507101a400400b020fa0780100411280000f099461420b02e814009403969000505660030810482192001d8401e0411504950f00d86070120386440600580307100081280f07509800c008114914480e000b80100b10342d100d802254903e5070009407034000e0300c0c070076000ad01c115600c80c2040d81c414011900068090b018180d0546100e0030300c3c0d4440e008842c00b900d0058a0201080c01c1d4142031990440c1192282e6a507044107420b00203400344940e1116112003096141c0413441c0c4480c50924103280740500b0a54000311240e04010068045035016a8029014000e8401810001c0d417500f0b10090a10b28081011703000501d1540309420056118800b040e480c1c0030315003140c0044840074401001260171594481c581e0360190703000c200ce0321900c06200c1c03084030707445c01880302001955242600314006520007480d16036001c4400c8180d0381c1c03100c1d0018540d616900f440c1400c4024004c01e81c801203180c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 74685289 1250 74684039 74684047
    0x5010f17010209061b0c06031312090807081b06030103020d03141204060603110a06080a0b01030e0109050105041a070e0402280509030706170a09080f120105040f050402030a081608 79
    0x40b1281d80345c022030b00a00d05040d141030380303441e40c18090b00303100c1240c0030480860b9142e0203200090802141c00412016443c0540c230301521440c40c14a4241950000c01e03040d4820f2078001c50a07102080d41c00f14200701a240d56041d545145e0200d1442c3e0b0039000c0c0201802044400305405090000580d0b80d601400100e0035160304050400300002d00160200355050700d4910041d0b04181442e504175002c07208980c0c1c13240c08950f5855000c1c401401c51095040c101912140c1040409809000f0074040d140118000502e6041c80d1074444020007100000e2100c101c002000c10013495000a8203040e1254165009a500c0d00c1c5128141400c0082079003403080206800f5685c1800c99000c0060721034154150116035040d40c6032003040c2c603200e40e08410b07102c901c0c2c802800076050281580000c20710b2841041c4050030031405200d07203442078010b200c5007080d440600004101900d8503000300d03201000c0c40c4104000500b05900480d0b1a0814090042d206c3c0e6000103d40102081c60f14040144940003082c658803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 74686539 1250 74685289 74685307
    0x3020307081603090801090c05040e12070809040506032406012007060e06070c050d030c08030a1b0801230604080706050304060506090112060e010b040501120302070905010f1701020906 81
    0x3110b41e1881034000900c4204042400f4205100386200c0340e030891556051203151104001c02b41c50501c6507408917010740e0080650076689030028180240c070404180b51120f0503034050008803030004013101c2c403071340c00590300340d681403880c000c2d039204460400803000050341c61000603a20564941200c286140e014000e081d4140b10200303800c0c058801540d5503c0c031150040341000a2030061160103401c00e03075021410041071420560401d0898464103083c1600045a00ca0303040380d4000300c500904681e00c0c2c88104016061040340605e1070380c200d0410100c154108883d6500c1200301c071101c0708a07505245c2c040021036a6140689006000b04011a44141c2d2a2203004003545c2003668129001818540400c0300c03440d02ca551941600d45903010558982d03c5500c500700a8411101200c0c42c5550b00d180d400b25030744840c01414040e100001c0110602c3e1700f49d250085c90601140d0002d0502e03842c1a0042c008040401501800c0707039480c0344000c51a42c003400c0418024400c082a440d4469400625288 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 74687789 1250 74686539 74686567
    0x3090d030305060918070b0318030c0d0e0301060e0105040c0909110405040f0b0f09181b01080907140d050106050405130210020307020303090103180b191a18040302030708 75
    0x4031a4405486001094403101c508015036405e03910002020f800107035003484410f8440001d50f9001d0409080031b9640801d1880342425540400301c0d800040d0003070341d01c40f21102d401c002100c440101c00d030300801c075940c90101c90b42d0365508180201317840b85407180c01144400c0d2054181c01c01038403000900300400074a204001c000390303200c0e2156500850030100f40051f20300d06803064098440003e0007010400109034100032080314010321242c00c44c1102e44c041c1001c0f8038100001e03aa0001c80040d0b49031461041e20000d00756500061a01103a58801c40381840340c8c0d10b80080040c1c11000a9a24003908800da1405501602c0c030354001c560028500000c03c00e20f00c2401422a202600a83c0c0781d1604203d134034002c0384c6038458410043c1d01039008022041003948a94008543c00500342e200452017101680c86140302c40342034400c0e8110002088010716121840d216000b510042d0310b826540c0d8451130380100702d0013038504801000394000e0030005030130706000303000b12120181e005035429501c900d08007a82e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 74689039 1250 74687789 74687791
    0x1e061b200301060927080403170c0a08030a050c0c0a03050a0903140d0f050307020303130c0302060a02010b0316030f08030901140103030c050c04050105060702090a060803070501050603010c090f03110303090d030305 94
    0x54480418001d02d030102620045217004e41a0300518181c1c0303030509507140c0d0b010b44009001c035249040403c101c085004034003400b05406d0340388a150800c1d60790400002030016208080c02d55603101408000020b04c070000094007a508643c9400c1444c4c881118080c25100744090340d0001c1d203da01e00307080054942c6000f10350003010804540303a003031518407410021559400211000005a442000071440141030f103000d441003a4030500d855500c20f9180d40c04134006070021800003001d40c1d101d0003409020f1405200150b1100859042c0d03007003e500c4d5480da218210110100500f403a40000301003403100780c00f90040c005040d10036100c540c2e1541e4034076000740360f14410725081d41c0c5401a01c464511628080c01124100d90000b0103260030100941c0811088100107070240c00d21070303690180000c05100030300c09454554000c00000500346000c030181820355429100c401c00304188a002484110b40715804401900c0c1c0003070701c44107650301c5070000c01d00d540305400703410703520480007810181019450f800503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 74690289 1250 74689039 74689061
    0x303070f062c0601060201020f0301092a0503063604050f0604031101050a060b0f0d140a090203010b0f03120703140304080d0b0904120f020c04061e061b2003010609 72
    0x8501070303a170f03411007213080f0b01603c0c0300c2c0420440104010001c00c40940c20410019003454007020440c0c0c0052138900ca81c0b45d041d07031220081030010040000d9860040c00d40c0d41420072503070078070300b0380a148080c1d110341103a01c40400e10100220700100c4c0a010007040054590030465045603401d003040d0602034200070701e160401e2901c0d800c1100041014044d40640c0d41110780f106c4e5401d00341904c0c1d074050856038102c20141580e031743c0c1c0c0b00a02076075009036500c0b0314040c4450410001c2d0029442c014503081d18070780da20140c00b42c002240654450340700000c914240c80b0840715100d86419440c503003254800740c60760411032410f0000c8144030a00c90f03400700500c2c00244401c1c00300035060440c424400c000070200c1d0003030564040c1440410b03126000d0410020710201c3c500c151403003103003402c000a04a030b0003600318000010340039825201200e545000500500101e0412440e0540302c1c64040030b035107440450040c02440002e80b404005404522004541c80340200203015594860080400610648c01d0f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 74691539 1250 74690289 74690293
    0x20a0801081209010f11030d0f0e0d020109050c09061503040501020a12090b0a0f060503010612021005040b031f0305011a0103200f090118121b050303070f062c 70
    0x2c4010000d10490f542d0040684a40b40403040152043d602e01e180300000f800240410081c81000340500e124a02541251900010750b940711015924540b405c0c0310080750640e031600411201040d000aa0224000011650410980d6900c2c0100307040e01d80b0352003079007000240442800100001074000c0e2060070308903550304203e14400864141980d0903060050130080c07140000c901080115000242e031b141444901180496856001c03e007121551750058082107805000d1808616200c907107c902c259903032910138182401c0c0312030200707184005080d4101420190b42c0007030040040074045d1006580010080007100141c20600c4500c042d00003126001130f180c80e440f021050780c5100030044405c00f4020207030504164030815110383d8801040d050520000b60019404400f5480107200508010071841d5280c059618020820450301d50303918031116001c060501841d20f002080d941040d4000e600c15400c09198200000100046803510280712414100c003003240f41c070000b2107007120b03401c401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 74692789 1250 74691539 74691553
    0x40812070512030c04060810180504020103020912060a11030f0703020c0705040c0c020406050a0b09060c1603030903060c0302161b030204020f0c06090d02060f190510140d050601150e04020a080108 86
    0x2881c2150040d2900940522966291035100400030690ac8103520a206040c010310744000d40d80015804070750101185400da02100411030380d0340301c0d80582800086011a128118101084522205d04005150008040e40403625502c1040b040110740001d020251042180300a0144000c04601400009038011402c084001401d41000e2540f803080b80c000102a9060484031010032810f43e0100c09004100d100d00c0807ca0312110068603140004c600c241c6400c0506450740c607100c4240ca60440c2c6000034144148a1403d400c10340713525507000750380d12065a0180505207008018108403a800181d00148080350110502c041c2c40002c07c00d42c1650300480306241c0c0c0e440b10b11541c50010140381e10050700003502107100894150307a0103800c0010346d100c0ba440703886000c0c0343c00c01f110f0b021209403082040540d82081140c441d500c1c00729400380301b0303141c422001106031102e542d00c51041c851359100080022020700050b100d05121403411500030403c0d551040380c81c80080182400f13020b01005070103411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 74694039 1250 74692789 74692801
    0x319121202030a050106030b010804020901120c0f060201020a0206250804030512150f0d0f060e100f060906050306101701061805060f060c0c010f0c050604060c020f0102040812070512030c040608 85
    0x407442b28071556000b445106a6828030840b00da1101e000d0b0320454001c03082da500030807001104d65007800909100d1703000503110700c00c080c0000d19007000648491100c030b40000511001c042c102031100368804481c2410403298880d03250403a072074811060fa01d40c1410685003400340000341d021803656031102c00ca50000300700780c054080008000d415100182150903408103035001540d203070010205100000107035540244401011015500e11003004802d050f5160b00501090106114480203000290001c212900d010369501c01251b006010301c2c0e40c86605990484008102508040043c0030260080e400c15201180700d040900425036206100f0a0312004922040c2421400d940802449900800c1021000d41c0151452815225200d04000400315540045101000305034040c520644000a8401c0396041c001d0134203d9001c01c50103603900410042210403000920224480b488400c00c6c0d50360704071450500e140001c01e039401e00108102004002da0f001981014004440c83c07900d84a039035607200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 74695289 1250 74694039 74694047
    0x4080d020f1e0a0f0309050307141305060102030a0e040b03070e0f070e012a061103040c05010f090302040b120609070807080111040e040f06290319121202030a050106030b01 76
    0x4000002a034001c3d040311001c00e00c0840000034440c024100300c80b569441d03002080c100180fa803c2180300d00c1d2030000c49246c608006842e0090800074000c100481d00304100000d40303234454800000c0821003500c0d0980229540c0d07a20504c201c140040483d40b2082e51010341c18800c041c104c2e11b10080c40040c900142c1e13058010042c00d43c54840c16034505043c9040725010b10013240c0c840f070703082038201080441100021748500c17035081c0025100046035200d142926240d0000161500070702e0400404012888800e6082032040d01501e5048801094000b03a40f8045050707541d071004e52800c0c61244c1d40522072000000315891080c1ca50082c16505210b43350001d903402d90f9205030314180c648000b0001040181402207416030817510a1540b200c3c410340c507441e0501901c588101508010409040c032022001c1c01100e2004066003d402078000f114062600c107800c144400000752486183c5019508228030580301c001141c45100030442d160300748102c512004100034000c0e000840e1820003e040c8941c0a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 74696539 1250 74695289 74695333
    0x605040b0f06070c0503030f04090b0a03030801050616060504080a02060f0402090f070c060c050301080106060306120f0807050106060e0f190b0c030702090103151104060807030c0504080d020f 84
    0x101425202401c1c04401c18081e8a621484041d14020b4070b5220202c1c013950144004d01e24101e072221104c1c3c5036030414206c98121184202414400e00c4290742c10000660000441d50440c0c9088030f4440e242d99403a1031030b070350100940348002c2c5520300e00400c110400c8011006002e4500e840e03401c6034051b03510300c40328420004050358080e61085010000801003030101400c143d20178040e00d00b201c121001c0c0c1c0c0e1038509a071f00d05803d02c80400e0012005001c524801d02c6040004c201d24901441042c0c90441c0d44030104083d030b10080d0592410303060302c0d010310008900310313280213520030000c0120543c0c0d41c50051884070b54108951151445580902c168949203401046c410040807204241034548191b41d003950303000440c003140c617010901c0311101682c3e4802010f0300075400f694040014004000e002402c440c8246641c0c40c1c0381310300b440140207140d0301c82c150740d91140d001d00b070018062980b01c070251003a000729401071940e842007076280d034004e641c086041c150806101381122804c148014103001c107816 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 74697789 1250 74696539 74696561
    0x15040b01061112130e0a1a0f0609040209010903150207060605040c081501020c1201020909130807060b0a05060a0c020102280f170309160e0c0f0d0b0907030f060504 72
    0x2200e050210190f0503181c0040059200070b20b101c40819545040e84d22107914202c0382e201005545401c4039480c0c2201e00c00c01449040101d4003000e6099610b00000c1d0a07002e9140c070b4074041c50340450448060f0340036a0f104005103401011500072001c0c2c0b0040354000c0d5000b048101c914904210002031300d41802e001c2c0c4202d22100d510340e01b04690343c4501d51459420220380d118118030520a14183c5074542844140103520301400141c0d0b2064003c040c01940c040243c0351001c4143c07a14441400700b0b1140041d6108071f58082000f16103948d460000903105540c540090b40c5c041c3c40018016403554110b4080000c45100780c0a880c0059500c0c1c1c00317035510f2201319400001410009c0e20078000aa1489940204240300300182900c11f24103c40802e01c903001158118180e50241000c1c0001032900000200100900941008285000143c1201e980121500380d5440b50b070104007420f0590702a0481000c400300a048102c2a1528500040140078241c4410000e40e10700080482c40303007131a02560048003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 74699039 1250 74697789 74697793
    0xf0605060403140a06021305011e050a0f030e1002220b0301050d020303070605070f02060c030c09010c05010f0509030d060506070b040f2102060601030c031a19050315040b010611 78
    0x1459038071103000a141c08403900d00e603030150643c44d0000a500c1e00c00f40151450350150090050b0620700090145420000c80a02010362800c1d02c0384da117a480011102e0802480c03a288c00700010518081d0050b0403180038080843c0100c08000004000c41d50292982c9104098508102c1075a00008038804030140242c203d4160f08100610441c14120705032130013140b010741120318020081e240c5a0849200780c9214000a42c403000300528180d0400c0307495003188803800e0807442c500b0710f41e00070001885101c1070a81800b02081040050100039171100d0f0003e444102e05001d18034210601e141c07241d002601d14442940707000b8000c00d0170305140066502640e808841040c2ca921180c95404100400c0c40003201c0c0c07801400070100c1e0152803c10b458880c20b103079030001c08017424401e001400786da5a03d2680c2041502c0d01d4444480001142c12800c100780c41a2820489010b0030044043e0101094108603014841c850f4591342c45000350001620940c003407481034040e07903200d0104403403003441c00c0d51488441d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 74700289 1250 74699039 74699047
    0xc100b010c1101051c14090705010503150d080906070605090601080d092d0605030109182003070803040e0405070515040b0c0304090509030a080a1506031a0a08030d0f060506 76
    0xe54007541c010144201e0600380c00c519020510072170070540e40a030304000000406101030040f502c0c800c10a2101a000c242091030861400c580050b00b81302d11000c003a4801d185011b5200305105021040381c0c00d442000c0c0c1020754500d141d003404d0b40a0b1805444145440c42410000564844e000ca40031400041c40c2da2058601450030040c032101090700101d814091411a01d0f07450581c01e600341c1c2c81c0083c00d5945400d9141e41c503200d10b810407180207103030300340e180c00202580ea400a06140e52100800403e424140410f01036a00440d2801d59a9009101c591000140104550780150b140b1841188100100e420540d1140c00b07000c214a4031151411401000340302c280005032008014015002c001c40c22641081d9032030142ca02030310b8050340d8000c11608000b4030010070f190f20414840d800746020360240800b0203112004014210360780710304420540c3d50701e600c00f4400c1e1f803456003d50032807000f0502ea0030310380c0762218103440340e0003498105207440c580903030341040780803034082c00f405c54400074401420 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 74701539 1250 74700289 74700323
    0x7060801151d0d0309080c0103060b0910200a0b0903040303050f0a020c040c170a060602070510050409050405071e0e040201030207060b0406030303061403030f0a0f02120c100b010c 79
    0x940a48141d1032524440c10202c0032980d2208981d61560034001c2c0c1d42c00f00c0e0f06182c10300c50350411108038051810541040790a0094a081d041140c486681c25030b407148811440c1c020442d013540302155007000425404004013032000d40004c0d01800745000f0218100c01e5151040d04580c0c6e40305611004020440520031000c102c40c0e0880503056004460060300c00c0644140001402c44001900031004070f502c2030071200d03240302e40b40c41d0756500040350003081100302c1c209440a5501e4946205242c0301c0d030101c14109403014858030646005010142052246060625100da11120035000700300100200780c4501821402c440312070401c51308510008025510b071900110040c2d40010b030300740c5603585c881080c0059615a4801d040c0190b012340c0c2c0000e00c050505400c104100042c142c00751080d8018804030034004140d00488011003084d0914624130310314035000742c0c1003812881e20342c100403101003140c0440c2400071900c03101c0e1044d00d0004005c0750500c14015581d081c0e4000002c1c00c0f9404001049032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 74702789 1250 74701539 74701547
    0xc030c1106011a04150201050703060510090b030a060b0c0706020f07030c0506090a03150f0c05090a050405180a0b06100906020303270f0f15010509040b1905070e030706080115 77
    0x40140b00c040005184c50340741d40c0c0404040058041c03060060799258200f14030154544203110107407004551051445604101c01000003005014030aa41240000070a80c4c10b19264848401003900081c1562207050894019441d40d02d58460000507021340b0458014081000c81c039102540d40c40240d810015091405004958002d07217061038000422810110100310440700c00c81d01d0f04a001c40106888104030400b0341070b110401c0e00b140a0110070b012030480340d52142401802d441054500280582e01c03c01403113241020180c0f0040036025805d1721105018030682c100b441071006458829400400d0803040751400c586109000058005001042d403e41e00142d0201d0000320104580d10000c00e040806802c00850f804124856480000d4080c10140c050100141d10300c91140c4d0424290700d4800480d002c0d0030010401060b20781114000b48012580302403c52200c641c48408110030b1a000308064080b4406407109882032244c2c41c00040e4643c4101e00303940c142c81c0b40034188072003032442c071806507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 74704039 1250 74702789 74702819
    0x3060c0c011107120e120c06090303040306020304080409060506160605330102060c0405030604030c151509050a11090f01090b0a030917070c050f030309130c030c110601 74
    0x348180d5210040c002c0d40d28685009070900e64026400da030716030400c4200281c8100b0081da42c0c01c1c0070381c03840c07016103d0021001c1003200c1203d000b56821551070b6150800a0300714440c42d04018800ca10110503c03080c0030240c800760003510022602004001d403114200131450145900d95408106041d149500140f0940c120301d400420346411108242c1e0740e401a1686059200381c03100741c0f104806202e620940c4e0401810741c0001060071064a05030408020948880303008001a040c004454840740c1000b45111283c488910494002c01c040c44400c40b200200b01154400c0d104c00f6410311000c21046201c80c42415090440e200d0b01c03900d40301c00303441480b420602040c0c0c07a506009100a000910040400080c60250440e030390002c1e00020078a06900035004211030008850428807a2100081000e042c21060348c0c030454480f15101012400240307548140d00c42036410440c21500c60300480c800313420110144a03d03860510072100d442c0d40407180007180f80103a00f00c5520450041102d46501643d003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 74705289 1250 74704039 74704057
    0xf031306090501050705091513050105300a0b0102060708040b09010e120a0f0809060712020c0d030f060602010b0a0519030206030903042102031b0102071205070807060302040503060c 80
    0x100741442a5110542114002c490900106000040035403c80c9411440701d40c142040412042c24654000c130300f004000014040e0f41c0c140000061080320036442c2c202a1070140b501440e41d60710b0340e45001240607550006440d1904a141420b40c155003a40c004030b0003611170101941c070390040f9525500c0d002034064028105200039561000000001070091180c038404a1403607500c41e40c0c543c1c41d42c0c0000c1454481c6100300c400c01c4542c1c002d00501da10041541c0303400c9003507442d2007007444032100c03d090000e00c60001d0341c1e0300c0c512031500030000a507050303040720003046103c0c0c1c810030245030b580d00143c1c203913540700b180c4a0303212841440c140f00398580f440542e0170001d41900c0d0600c40c03544a501040441c0c0c000c1d10764404a50010404001c074400d10810183c80140101d1500402c030016804a0b9542c01452541c001422006040c14602d034820040745008180b40c81009031110b0840c00c006465110900031891640514140400e1550290023140c00719100030340244220340e41c1180f0010b0700d030080b01c86 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 74706539 1250 74705289 74705291
    0x90605120f040c0f080601030b0a110406080a022502040501150c020111030d14040b06010201060e06010320030106122016050a060f02030f090a02030303061002070f03060c140f031306 80
    0x4040b45007189000304c800945041402046e065046040840e100b40c03005104c091001e08143e034143c490b401e140c040e241124050f0800340082d454402da104003030300503400340032440004241869240280e038100740080a0080d20100302c1a40c81c0e02600f00c009000e40c4400012a0a02a00d900194814000448941a031105a03410a042c06806100b5148400c0030300720950100e41c2400180100b41d0491038100034240001c000740c1c1d1424400030003440c0000c090a0600d0740d182c80300000c0d00d00030084120b00c020069040c079a291785910010f001c2403014241140914038003609428001461610440340240c10036443c0e0804521448507000030412500071980e50058040c180001541070040f991040082c1c48056100d152001d240c24000724014030100265111500d40c00150301e002c0708581d00010b00741c8050740707000803442c6d059141204580c0910038161401c0000000c2c050b10f5840941d40089a960320b0081640d84501050540140c8804451405c3e040000c80c2c0214001d07403011503d11302c0340700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 74707789 1250 74706539 74706563
    0x1110106140f042705070f23030a0b01061110050c03010302040213090f0204030201110102070c0e1b071202060c040e0c0904110c01051b07080d09020607020a080d090605120f04 77
    0x3815044e0003020161507050a0344d04142482082400c0c031940e40070f403121900307420785903252400542c00b0b418444060800b007001c0308040d2541d81c0713080c8a60701c219500520a20403c0d6074840004104006441419250b4043c0712079034909182940100f074007900720801d41a0441c0d0070343c1c08100003503000c14403035245c0301c01000340010f5624540c0110350310800841303001030b250784ca140000350408902c01d41d9104141d2040201c0c10006618421520a6902c481121780c4950f50f0301cbe44012202c140448400c410340c1d000f040c1981007204410402c04008407550030b0b00c8040d261500d40f0f664600031402100f0000402100103a0286040b902410440320000c00c085415104032207154541d03441010b00a409945030800c001003c02084410002d4680c0403215520f81011511688110f00444c0c45071054207455a000c9400d6560702c20585a560b40c004010310b0b0601c1c5d035234126907074614140e0b201601051105000160442c0600700b941c400d40000c541092803036031001d030520f08403540288100c801d00e032410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 74709039 1250 74707789 74707811
    0x507080c0115030b07080a060b070f0201030e010f1d030901140a0c0f031d030f0c01030504020423160c03050316180810060b0a0215040807060f060501110106140f04 72
    0x21140400840c055131100b0302500341030900504001c802803800740b09a00380340003000920203a108580d0043d8110003d5007600004d840100d001e0320b4400e40d00e8032607609048800800c40240d80c080801c0d402140d03c1c910140000ca071010b0b0712401008026404913580003424904820130354001c0040301424078150110100e80d0f55039034011606a241030b03000540310170102140513402d00d518851a034084005020311001c160390155101c00d0740444604050f02da03400b0500315292030300b0400c0c1d0b81104200c0a204901a003912014059048030b0f410391b056070080200446500403039000007100c0e01580d444d4a540d540b0380200c151082710f00120000c00c100c01d910074148403215032040b005040300300702520fa01c2c044a114030043d24529080a015000d08101c03000751150001001d800800020003c0402540c49003000f28640c050fa0501030030860400d9031001079100c5550080d8240c03202600c80065028010400e103003203980c00e0050719017a214420b00042d85207040545488002402000410704503948 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 74710289 1250 74709039 74709071
    0x90601050c030d020a031a19090908091e011205070503010506181003020415020304180e0f010f02040e0f0405061902090d0c030b01060f0503010509100308030405061909030507080c01 80
    0x32091750000a541c2c0d6000c900e030240403454015085030704841640200800c1c0b241d020011003607102c2c0380c012644d0398543c0e20400102400b0381d0100003000744101c80b000d0040c522490000090241140001c40c580110600d0b520188500c40c050a0b45a485070300310380c04c001c00d005455100420100b0303480082c03110301e0000d90341c100d400c101c403641d150380140c1c8075450f010304507184a40c42c000d080c055400c103000038000c0e10040032400c4100c0d00810000b03c4c00f1401c00c0707602c03810030f04400204111542490650144c007880c80e00100105e503280c0f08448401c1d40d0301d003d076840004040da001092900440003003403020b9142141c0a65000e07001c400185030407503240000e004408068002ca40d40e03108103504105000700514014014040c0c1d0411030300403500c442000740240703c140a0310384204c3e103070804654410305120840c800303142c7c400c880517500d00b4141001646c1c1c0d002100c28460520b0105010034000c3d86502990703001c1035154480c54205821690b9000540d0403038203105031250b42e6044601c0c424409 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 74711539 1250 74710289 74710297
    0xc0f16080c010f0b0415050d0f230703030807050c030a0c060b0a08060906070206070f1d062205030c0a0509060621150105070b0c07030c0813050a14090601050c030d02 73
    0x10b00c0c1000810404480070301080c0e680210028880c02c2d051507007001f1984031205180550340c0d02441250701100245000d0208010410190100e4000048801039a0000060b48011f4074066112155540c1d10382d541241d1034030901e000504190014009064014001c404400b8402d02c241c0000c20f81c10310403400714102c101d0513403120b0425803006050040b18a002c1c031007560020342610240a01d450102c42c0904840380700b5080908201c08440d040f0707880205c0317010920303c9660041c075481c1e86081840d001d03040740300c04c4400706910003410078000956103000190f078048007801800c0b00d202180752908020b10300c04000c24460b040182000f0543c0c0240c0208041d1403c01c0cac1c80d64102d8201c1c10641803810032414040340c036a06102302080b054000c01d40c50148640c2c02031814009968074038051504446144c4000001040a0404200456101c0c8909600001d9840c2541c10110700380e0744100a800d11050912090b401204000116039554803940041c0070070300404044a18218540308401c080f684 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 74712789 1250 74711539 74711561
    0x60702010c0314010311060a121a03010b0316090f06090219020d050306060405060a05070b040b07120614090711070b090901080a03020d0318021c0b0c0f16080c01 71
    0x1544044040710300d909441000d041c00e0003010003180c50740c10741d0b6030034010400c860b640714441e0f800820220b8400348103076a42e84241b84600c1051041c145000d0040596419100c55503100e5400c0c5000c0035014180081c03a000c15486103801301034103c0c6480500c030300921100c0c44500304075445100119140071540000d14011116030481c091548010138003e05020825080c4070406c9410420700032039554030070540e81965000c854040d500d40c10340a054616105041008112240410070041841484180c10b0311815680e1101038100e1820a590802c44103a130203030385424010407098003c6c9040c06e0607802d510007114100301c070401513404251480c102003507002c0c400014000541807083e00b0980380340750040203410014100d60f545960040e4039001d6071303041301007019503c008496241490345a12000c040c0c02404944a40c146440d00c003c5102c0082c100399224400030b001f00d40c000a181d01240d01100c501c0d42000c0c1046180d014800c03031442c41032000c0d01c001c1428011001054800c0c130507803a00c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 74714039 1250 74712789 74712791
    0x303030112060e071d07030225030801060c051009020d05070806060f0f0603240d03030e010b0d05070b030c0415051809060a031514042d0f080304110306070201 70
    0x2071042c80c0071016150141d81c40403940d0040041084180314000304905594442070100240d0394501034200c00a004200d98410480d0500c01007038451108041512005402503840200582e2640c0064a0502e00c0d400c0c0105203620072500910048829440041c94a100808011030087d254440300e01d0311085401401d41c40c0c0004007845018513200904030003121090352152038021900000500e01c0c00020040c0003030b9204202c0c130f130601c01da040781018030f2000000c004040800c51030500400030165450407070313215803901d4140c44061401d00309a9000c0703640080100029803d114801d003a642001d0316803014000c06000100b04402c2c0602110a41280d564505403100202e42040000840e8042070724081e08a59041c85410b81707a044d0080141c941141c0d1420300e408941583ca0000e11480003e4100a2504001d00c010411151040050f085611080301045648203c212003210020713000140094200e4171000c0015180402071640b00e80a0803c490514400780c005c01d0812100b101d0090061b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 74715289 1250 74714039 74714069
    0x509030a09150c03031505030f030408070f12080703140301030f020f04110a0c030c02100c0209010902030610030e0109020301090b180304050307030f0519080405090708090c1e03030301 81
    0xc0d540032800000034120a0644018008981000381aa940003007018003015191180104803214040f0341800812001d1704031060b48000760090364894101d0700071090303d80900f1400042c1c10b100200d2075070641c2e1910200300c02c41001e40e074030326080f90310009d0120305001120705401c410148407006140258056819098881c44910402408100350ba070054410761508020f00c0211040b80c1c1038072111300c0c440c01e002c5031034800c0b41000d1390032056400c4025403245c0c1144a81d131005030b120036410a858400c0e03541018990b00c52174000300742c2c00119919a00521591130001b65144640c0100b80c0d4201c6440001070420825000302c1d003511710040d800c1d07030300400890510a01010f10180180c00313a801801075402e050030715000039103580c1c4622014100c0c691200b401d20601000b03004817490400806884048501d02d460246021b40092180502c50058500000c010394019100207104224140282440c207102008100c2078442d00000d80e81007240c00a034068048e00e0400085010f481d04241c002c2c0341d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 74716539 1250 74715289 74715307
    0x207020f090f01031407031b060305010f150c02010c06050411090606070b0103020906040204082e0501181d0106060503060307060e0d12021011070204290f03030904050903 75
    0xa03102011249402032055000b0020a8516900302605490340312406a40c80c12031498000c3c40d1100c1c54001030302c400d9103440701e07081402012100718100d80c0d294070140020303030740d0b54049100e040c0d0500c0764940c1c0ca14070204c0384000512440d041f0400500c14101405c401f03e150700da61040790b01c1118203c50304801c2001c0040309151180310107500410481d0810b240000781e51360300c3e1603403106100003401030308142d000c2615603686070190b9024003044000c41e59407580d1204901311200c0d04030103199414400b01c002c00c4200300240039003410b89100340210030500600d0750240e40188001c010810041380d0b03405074140d0308202030040800500f03103a41d606403281458007c00d81080b01690044040c80140c541c035882c19146c5141b4005901d400034a02040b11010317500036810201c040b00689482850241411040c0c00414068982c0e180240d8042111013480d644003030b500d214070340c0400c408d00c411942d41c5d00c00d442c0034071031856211406819241460510b50110301511000e0b074155034540c00116410b01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 74717789 1250 74716539 74716549
    0x6010206180a0807050f0d08010303090801060b090108040f02060a02010b01030510060e010f09050306011212030c020309061e03040303060312020d0806012706020304170a1a13060609020702 83
    0x140003910400c0711010072010220080da21486040018900d2a01088a00502805000c98506007001c84e055840941010200900c0f01509010480c0810651200490102e50500c00e500980d52500c40181c82c08111f20f005560800e40240b0480d01303018140256001611014054603031518150008524020540005026500c1c02400022400e080150070480950700143c1d07010806030a00382010f55942d2a90101d800d1480d5030080f54141c42035400004110b280b09a6211074180288203c0c164145400800c078180c41c943c8004100592080c400300b00c562420000800004044650030030480e0710410454105820481e401e4011075910301003041400f854051305107840005101030645a5003414003d000f01001505036410003034600041d6810285461121160604ac010244455982c0d001e0007962039005006a81410345041e03442008090005010740160f40d000c0c000240051085002100101c0001d00e00030440c070034625503e02041e020300c14a07002d00900180940d031b998003401440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 74719039 1250 74717789 74717791
    0x60a05060f180a110f0405062101080d0e010f081f09050a0207030e0102031207030908120a09020f01020c01020604080c07050901030501090b0c090d02131e090c08030f0406050c03040b04090506010206 87
    0x728115130100f02d48403650f55040212026180121032007522600044107e500542c080c0c41d0301822107040400100d95404009403074100c540155484404500010004480d540510806000400e0707250300420500454004c0d48a201548410408103403a55034626809850003500d600e414150b002900c80c0c1455441801c1c40828107003800254a040340350b00c401a01e4520007040603042540d0b03a0580c40421000b1401c48041105a01d24003407a41400c84c9000028107400700201d1090343d02c0925071523103500124450845101c140c01a21880d82c3c1d5448041a513400544a10b03110f0150541c045096174844001ca40a10300820000404003650b00d040c001c4000c000d0040f0450000074044108940d4902101c80720003036050320b40418030042221203002070800d008070952100c0c5c180c08100200e14080c0c0c03002220380d000700384007200d455940500315182c0c4150b100d8640704100403c403d115042c0500c008120180c00c1004030303894a84c0c0c441e106506600107030081c8521540b110144010380d03a04101e49 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 74720289 1250 74719039 74719061
    0x1020a17070c03080106050d06030b01142409040f0b030a1a091603020d020d0605010603020d0605060304020102031204030c080d0603031206061e03060f0308030105180702060a05060f180a 82
    0x40b0581d4400d8901400354501440360394104800080c03076800300c0103690840c0d001140c0c0514103418558403500b20500c41e026104000b40a150f580e0403948207500c14445080004500481151400b04580140b101034401d80d0340c980a0070781c80e41008102500c04204942203d40901700c0d00000c01d071b070b07011449028034000d8815004e56101032144808881400c005500701d95040b01d511058011030710115103400a45040a0149854003000081e0660143c00410000201c841c081048640310820000c1d6801b068038068010b90007882601502220506403039000b5020f420203000d102c0c203035500c16003a0790011000301d69007511003c080040682210411800da880c2110a01505080002c0200700c0c1c1da18440000900360a06480403100d07020b82d1028015060003600322021030b440f400c1c082e003264020301c84c0078010030409400d10203041c4101c1d001c03802025190b0141542d0b890701d148160203000041c1c00303561301c07000003400d1720200e5480103040002d031543d201d4286824a014052081160142401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 74721539 1250 74720289 74720297
    0x6080108150105220f0606020303060a08030414090417040b07061a0d020405071421131e03050c0a03030509060705070812090c060408030706060b180f01020f01020a1707 74
    0x1805540e0302d0798010444001108450030403100700c034040101505c1074400340c034189482c12201090a91f804002988103400640e0081886951100940d5407417050384190844012294014055480c0c4000f000d90013600500d40d05021300c08207041ca0f8002c3d4000e500150048500080e10381c108542e5000351070031542d03482c03031451980c08030f140850000005414024407407a62600012030490003100100c000c0205d42c1c11183d15484080d8401c8684a4612807954442281d240020428001911300c41449a030003410880340c2e41e034036a0183d440c8501060200e007401000d00075400307200b41c00c02c001c0440a00a9401203120709240c00c0250800b00007600d03103410044108080c030003090030b1000300c45c00541d40e000702c000542d980e401e60b24100708a1810240e40030500050000d80280c000020b44404c5018000800032603965900c4642c41384648032804440c00302220108005242c100d4001c00a00c07810700603503401400e01141035089034885100100072410001c1d8a1034000c600c41c83d40c90340320f141810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 74722789 1250 74721539 74721541
    0x4050c090f01030e0f0f03030a0e0d050703050711060d051006020607020a03110a020d0807030e01091d060102100527060603071505070c06030b01030513080d021b03040608010815 78
    0x1080a0300c0c56840c0e982d061540310032005000e40030420013290340901e84400d4481c90421191480c0c0c6a5100703448400a26080c41b4900ba6103440100340145466029262a0328040d190780c1c1c1541e058200c400141d8546807403110b41e41444d111500181b9030105290400034a500d408940c0094008498108004652000c010000e13420f400243c203008658040c00e10100b54072210900601e01881c86500079007080407446040100b11412001c2c0000034469103402c0784c0c0f0140440116400c9034035204010007440510070781d80c1034075101c01072241c0060061050311000c9512105c0c000603200182d0320700601d0310003021001c2c100f8540d541c40c070345c2c03050f60740014000b81c3c2805070000341e60b005d81d0f02501a59140506640c00300c1070240c001c880c0082e6124014030b08080d66800c000d0018102c02c16410b0100703081070001805c2c90b210045142c3c00990168281d801c003680441070800075044280342068036242a0510b980c10381040010300014051561084041d6040500890030320002114640a00c00968 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 74724039 1250 74722789 74722807
    0x903060e071a0906130308090907030507020a0b04080d150f0f05091602100e01050a110c1b130603080304030207120b0103080306010507020d0b060a0f030507170a1b030204050c 77
    0x800b4200c10750382403240300307501c400c80c940c0028180d2095103030784642c05144041c00070400034104098081c0050490700540310740c0c0c500301d0660030368170212012401600240581000200c007400e803d90400d000c1e01445042800381051401102d8480c0c1d11b02d0074010f010031040203401b0361041e482026050f104250f9030901d05e000d01142100d0f401401180c2000620382003501032510820808503201c16818080c01251b44440a140c02002c0945001004030f05048683c070464a41e4421281e8010b01ca5000b48001801101c4882d0b02c4086020102e5020043d9412a05543c400d40203410107540121082c030b0b506d040502c0d010303281120940c41100030003099281d1401250702c40e1000750440360445c12060760b940e83e02e401210302d4802c140b4006d5000c10259544800d00c00399095551098070700f80c0e0542001a12074104154640342880010b00503481000280511034141c0b500305c0b04105200c0c200d03002141c65954200244840c55443d548644107079000b001545028018071b60083c441c56041707490b0101c92 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 74725289 1250 74724039 74724059
    0x2010e030405120f03070303051605070809010806040e030417060f04031b0201030f05131a1003170f0406120f020a0c03081312020120040501170907090203070903060e07 74
    0x14841d15201e03403d800481403189605001300110801c801c801d03a0fa41d0012450054002c001c2682d101c110020403910f442c1d04140108202c50129800000704ca0400200e000116041640104001e07007113a01c800002042c5d000410152018148034405e0031008003091540302d2804d03000501070030a1400c4d0380c050001107a0081d00307410b0b021038200d038103000070340090005030060964800400c1c1c0007440c1c80104100100810b403030504003807080104100010640c616689100c5017560710040c1c5102c4500100005969454855100400ca001702410301c580300241401035040780c0e0003c008254121000e40d4810160300c61300c50441a481021400c08105110081402e554081c009081c4080b0310045014042003446c1c0c0d80c036280d40b0031083d0b100f940360004024080c10b05101c4000c102c40d500b074030880001c4480d005072002d942060352528030b003052a00c09038904c40009880000780d406007003800b089a0300341d0b00042d071203031203146c482031041443d42c1f406508a4803030004507035140d0080101400301c1e40310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 74726539 1250 74725289 74725297
    0x5070c1a2811130806070207030b061908030309030a09060804120f030b030708030a0311180108131b0510022b030b030102180405011502030f03070c0210080a060602010e03 75
    0x5450301101c0c40703070300264000c0e0051040701c89068400c800840d4118060080c040d1801c00c1d5900314060301c5481d01e441d08280d03502c2c21503000040803c1c001000051040c10800410b10071284040007104200e83c4c3c481c0c00a0842c2d0058800102030b800c00182c01c480160005010001004645000c4141d882e10f0346801010442044644040041d01c0600d41c00071071083d0400400e000f0000c003654203d9503502591941c80d80b0405419011a00f060007202c01d203113401c01568208441920300001c11400f0400440b0348102c0145403d0000c2c1c4940d0400001c104031b801c2500707040030340307080c140c40701d034242400c0000c1c24031443d074103030215800303d0885103400200303420002e040c105102c0310311035191410905402800300d40c10665090741c03006ca4070004a5090007005c441d044801d0350f04000300d0340c91b00c002075005444101002d015034010000001c81e2500f0b0700c0219400a0107180446052406500044400e20b01d01441c0700040c0038001070110071044c80c403c58004040c02d00082144c007034894410f40d22400307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 74727789 1250 74726539 74726581
    0x80405040b01110a030503100b160b0702010209060d0c0c0b040503030910110a030b030c1201020306040513020a06050a030b04020c010209040c0305090a020d06090c0b07031d01090b03100905070c1a 86
    0x6c04004035004607000803051014028101c1040c3d210904010301916100c03454a05441c003e01c4000411307000c034011301c00c8910007072000d812640743c11480b11a03a405450610781304004c101d404e40b903440216003c0a003850041d8400c1010350355a00348164210314103000c1c50522040c0034600744600030070080040c11201c00d040b45040c0416070840d400b00107400c00103480d01c01c1380c020040b50250103018406600852050300111004c100503101d1002020106100c00c800940003040c400041c8203e23070198001d000114420b20300171848030091404a401c0c1d80189924043c240c2d004910400c0c1e500c2c150185031070b22030782c038075040000e403402c100c0040c0d841804020190150078081003210034840d0680106a189402c03207542c0320b01d20764401c400b84640d800564254001078001501448482803240150b200f001c3c141d5407244070600300507862001b51300203441440190100c1e2400210444c0a00855100c0c05003605c1d200b44004040c1088042c00228025240c11110b5080412110740801510010380b00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 74729039 1250 74727789 74727797
    0x705180f131505090901060905092409011116051902060405100509030114010302030d080f0609060d060504050d090b0f0a03050709091803030608010c0801090c0912080405040b01110a03 81
    0x3503039032101d042c6409040c0d004542c014203980108150a0415040181180c0060340c0401c0f0a5030742d6008141c44604070b09030a501d0031400c401801040c11500d11076900b00c0c2c2d41030000a2003180b100c1040300d043c0c0c4100041c580242c0c12100201c20b0110901c146030f405000d54180380d000342903d500040a52003117000d6284101c14128940950621070000e60b125110054000c0248400c0748215880d111001d200c201c2c440c0c07081501840c02d0303030f01c20700085000d9040c040a208164817000d04000410000920454120158090320f00108841d80101c5014a00031005000c140c00205c50080c001081d5800001c6400340400007030444504180c120303142c101c03180c50001129203802e4000c0b50990120350000400604124420348000940a03906006030310940701048469a102e00150a941b580c0f500900030440e1500100490482c5420400c0b00050030710b01500c81035180c0d0019815040031100507504507a0100d424020fa040c6440781e42d42156003402c0000c20351001e41d4030603585841c2e1510040401c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 74730289 1250 74729039 74729051
    0xe01020d17130609050106080c060c0c0103050c0c01021c0c09050303030415060803120703050f0105032e1401150201060302130b04090605040305030402040b15041e0803030705180f13 80
    0x760b03040c0500d007090030398445418484400300e404c210f07011700340d140909121401607105540c80d62501d20108d42c410580c040180020f41071031030064009000c0100548100202041070074060442813009080b0134250150034000c40d1010080070044030851304145040c4000c180040c80559400026240c5c020360041d440d403e1741410850020291a6a80c003002c0e8521021400403001c0c02e040750740790f00c2190a541c04000940d038405148205a8081c890540c0540010f40340f45200d0384480303038010320501001d13402c602c3c0d00000e00280301101d0305100240041f1110400521091902a20304142e410ba640300a1048900f9900041c801c400f51040c1e000c0d0640e502c01c440d0b5210b44030380d00642801c0b90004010411403409080141c070aa00031a002c1f8440c61a03c04410366525000030503402101e0143d01c0b1908141c2003214031080c60308402601c10040b52020000140d4001c1000118860142d5075182612285401300d8100f80c0c41c0e02900c0720340f0541c0702081d80501610f9510703030f100528101d01004511 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 74731539 1250 74730289 74730301
    0x201050c040b27030a0803150d0206070303020c1c02010e1009051c11030d050414010608120c0102270910050306190902041d07090b0d1103120c0d0e01020d17 69
    0xc252140182c3c1d8241c0225401c0c002032006100156105126111900980c0c40e121020404120100708000398002d10031700001e070111748030754040d207004103003001110b003c6106c400300102010040504080183e442c0c4281c000c41c040244400008440855024484940691344160300e4075119404052218162007580c60400c0c8104682c5450213080b00580342d035103080c1c20a40010304002c4a090324910b04440310707089103240500c5070b6422250400003401070700381034400e05000303075010400202f0291b4080c045884580c94241c1154014081c2104102008052006109540c40000c10700008080c6511041040d03440100e00e00e903000d42100304c00b4910452150804004201519001e5003040c0341c419890500d803011316030140a1350500c4201d40c01c02e9a035105140544280d54580d41d00300060300c8850b400200c4120210f008107100806560103d9103204041d4856000007598841079884540642c400b0340d00910105c20908003072010302128130000001914070000a81038072083c1c000c02c000a60 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 74732789 1250 74731539 74731597
    0x1020f06040b0702070b0c030a0f1803060f0605060309010603060b0108130206031b0a08070219051209040216051b0d030c230706030b030105010504061809030e0d0b070201050c040b 79
    0x5c003034038102000c00e840b110750f00504d82e43c90f000b44041c0d1000c1906140d84015860140003425002010070140807442400c56a82e040a450310608500b00c42d0744070348000c5416a41c1e04081c6100d0040b2a0000950b1440c5040403010350b00d0a815090500403060107200b102e4504030169011140c040e5600c50fa240c070740e0b031070400991036580321510f10b5401c007241071181c1c141e1103803609014481c80d50844d004000c001d41e171074480c00d507040001081c0f540310b00303486648185000050114481c009000506003000c1c4010064099082941114203800c10342080814050030b1002040258041e10310035202c030320a41d4098100017801c140941044418111030746a03000b51003d03c68101041c0d003c0d41c0d40345a41e000050060503411400520950a28001040ea0300307240c4185012115049004445d60b05401c00d030900829030084d003078081082c800040d80345600ca200480354024480c540e1314045180c6148020308480010744041c1082104000c104041c84400d02901d4101c80c0e07900c40c0b80ca4914407521004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 74734039 1250 74732789 74732803
    0x1030c140310020a08060f06041811070b0c0706150b0301090e070312020313140105070210050f030c0909090601150f11070e090607020604030c03030b010224060102010b01020f06040b0702 82
    0xc0000f8000500640442d911540d124000c24054458001428040082260700c0c06140a500070403100c2c840d1a4000480039080b43c0806450321100a282080da0303142c80c03c40900813210100007480020b5180204001c40c450381c00ca4142c10861991860304050805c1c00510040c410300c50165180c141c501c16076201882110025035009030f00c00c10281c9600c50184d140d412400e070705e01c09044c0541002940c03881c080865482400140e440c44e160140540c00c200080700e0111012040060603c606c0b018100100c0007507008010490a46171039105460800c000b0f000010b055000301e4000c03000411803501001003102440e80b5904020000c803408503001c945c2030000756054155482192000a0006040ca000e28060014401510126a500714041c1d075548409c0c3c0d4003c000030f01103d007100c0440e120341e01c19010614148141d4000086a0390034035812402c500c80300c0d504c042c5040a00c6515a024850b02c1c5000b2403c3c000b80c43c800482c168002e860305030043c03003d0710206441c8001070540e842032000c0b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 74735289 1250 74734039 74734063
    0xa0308070e04021303060f0c0305041218030b070903060c02030a021209040f02180a060f080106030f020c011a0a05040b0f0d020d050609030304050606090c22090903050d050109020301030c1403 84
    0x9200ea1680ea003000000b9041f801e2610070380ca49011803860b4102c1c42401014425504142d241e042d040595804941e001ea201d0410452001c2d000004030014841142e0140240c11a0741c640d260f0300d0030750401c2d00807078060322042d00c01d41d441006652411900400d40440f101c23680000f003a201d00c05c503000705024103c0c14103c003e0080c40010001c103300b580040d40c1000304001c1d180785030f00680300c82c82503a0140110300281c1c0441e4650340100180c42c400e400104004550820160504480d00c10180c2590b404994407042407206030440301c41401c1c403c0c110340c02007004440a004000d0404003027542d160141856501500901300c03e0b0043d520f43c00305200340c2c01d5004c02102c40e24500751014586075041138a0440d107034042c2c1404540c40740f800c160490301810901e505d0515244104e00b519001c1900c9220550101d0001032001800741d41501c50003440c1c0d030003502e41c0d42d5286190200d11048450581003040950701c18001030020030700a40216068031004100c1c0384200e0704150000e40f9000d100c8140d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 74736539 1250 74735289 74735317
    0x51507050d0c02011505040e07090e0703020904050d02250902090a030b010f080c060702130905010e030a0908010506091b0a0509040f0e010b032b0e030604050d110a0308070e0402 78
    0x303a50f41c15404060103294a9088280198840d000c01c029075501c0b0241d02c809a0041c5418800c074041c42e8080440803105c00121603941e6540d6011825541d0f04540642c2c13150007400c10304681d00e8041c407501c680451100c020351250300180340d03112605403140c040d55a43e241e011500d908030743c0b500c14407500555001211614a5070359184070742c90301100d46c000c80310a03003d0030170502040d0800c0c000307640031542c2c002c0103002151041092540240210b01080d501503480d60700c1c8030449c0c01c040c8002c020140403642d030b0180700b509140ca12800d43e10084d00c403500811605003000895220380460800040145203440e5039801c00c3c2008440500132440b1155025142c541d801401c1111035100c20100d8400100a00030191010f00b0140c4800c0180b114900012030711b445605405412000c542c1040001d041082d0284981d401003842e00d6011902212107600c02d81d164070603581c000c2c00300c00003c802640182032880321a83d009042400c00f402a1781403140d400f0209400c1e59450301520340d01c00001c60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 74737789 1250 74736539 74736551
    0x21090b01080601050109080304050307030803040501140a0b030c0d33020c07050103060501050a090e0915040b09210f03100306090b161107051003020c030a111504051507050d 76
    0x400c1d15141c141c288141404144002000250540e011042d2070450710000c015202051075600c400f03000d5840240202c685541c0c4084910480f058025894040c1502900004081c51000c00f4545092100c0f4851441b0381100c0400d00000341c110b01700c0700c005c94a01c0c000103143e2000c0c0404902c090718018400d854136400801c1c0d0503807848001841c172040740d0303091b80c051024960f240019121445900c40700c0d800101c1e5048103100c60345149058541000c07640b801c13150041508102c01d00b00303e200741d60131900b9140001c2881095034081150500070b800020000041012640103c20030b44968081c90029940200026015044c0649268000c540010b400c1c400400e0910f0241c00f0300030100c0d2103502d0003159292040000740314941459007010002e0081c4046401c207003c00c82281175a01d0b841341050b03003c1114003c501c1060020b00101c1e1503d4035603d182c2844c040d01981803001240e007007182c00d0101d10410011a1000440c4400300c4100e91303109925845140c01102c05100f5184100022401c02d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 74739039 1250 74737789 74737799
    0x1104020a03023109050c0d0c020c0303120a1104060206070c02030c0d030201021209011505191d010f0801020702060a0813120908101419020c12070b10050121090b01 72
    0x21840da207189011040c031100715840c1d1000504417842170303510551450040c000701d01d1000081d841031010401b14011103140c00e0201002a1465001b00c500c0070005080000b4841c0c002d800b400f45590012a58603840c1c10310342003080080d0b072100700501410070000f000000c401551001d000058151001904034140104281000fa0103035020305021181e005441000500305c8406120300c60034590310440c14100700f480e0030100030044c114004148100c212207040001c8035880044583e04500100003401c2e019031400e443c45038001d07101d50004849034010414040180c0c3c40e101241c3d02183d4600303115001d91103424041c003001d031902c40b000384100f4400042501c0107400104030800c9542401c12201c01140701c41c480030507a00388203020001148600f0110b01c0f441100d07542e418610700e880c0030041c10202c1903000b0b40d2038000203110350a41080300042c20001c1c00260f0640036806600c1100900d01c4914041c0000e00468803a4102c07800140220020f01c121105500207403902c0d40c0000300e011302542c4038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 74740289 1250 74739039 74739097
    0x3020309060f0402060a030c03060b0a0c02130b060d021b12042309010e06031603030305040c09050f0403030c1206030c050913030e04020703050c060f07030b0d1104020a0302 76
    0x644000c200ca115000010302000805508288103950280465082807a401820390203040c84c60188428144c60718400b280e590921005401c0104c807035039660312854103a00500000803a4480c0e008482420602000c000b5107a010031141c0c610386c0b0501c0141d480c5c10180003c504600c2e8501741010038003034540802169101480a0000e8940c2991f412030070100c000341014454000c0300b40c254002007408010008c2826880440358080000341c155881840022640ba113120f501d6001100841d940e1018041031290030340c0c0340800b074180c0100401143c00d0030b4601204408008200900f0103441d0920000036074883c9070202000440044140402912454846100920790291600620080c1c00140c24024403e00e401d850300c2d050b4a070020130b0241d402c288406035001040076001d1140c10018490042000c00003140700d00d0751100c040601e0704002d0801000d41e01c48800c981d200f0809441e240c0e01045068505040ca18012980183d0764208900160040e010b142401c0107082d413229010107480c20b43d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 74741539 1250 74740289 74740291
    0x30d0e0901050a08060604020306031c17070311090d060b0402040305061608040201120522150c0f090920030103030f0206071b0b100e010803090a05040209031911060a030203 76
    0x1280d0022007a80c032030062000c2140c0b1449481002d5109801050301c40c205640210340100024096400001444103c0092243d6002000e40011612601440c20801d00c2c01541e07080660361a0030302241001c501d20403800e0040c20b016034490305003103811004011a952000380c02003000380c0103640f181d03502d0800e16140ca108072120321104403001800d1502d14401d56000d441698146c40707149800305034032216001840020080110a008001003500031010100001d5285119038640c0c044003032051481d0b01501d040740400c009001b468621400250b8203c04c0c1788060350f4944000081c0280301c190049080803d40440041d1204000300105c01d1513800702100240c00307002e80072101c20f03442d03412080317510303a80e10020f440140027414401c00003d80c240e031045030010580b10074140ca090300da00182c2c0100200380d00005440d4800660034041d410110043d01c01000126004c50078100d0020120b6107640102c1901e03000041807501c19010041e82d242c03502c6074250b000d0025626001c2542000e402544 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 74742789 1250 74741539 74741567
    0x1090606080c1e0a020a06142d1513020a020a0302070f0e0403050c0c031b210312060310020c0106030303050109180b1e0c031f081911030d 61
    0x8140000240401c1d406400c607000710401120541c070f03507074014411005640102c607007102180900c0d104070000c03414901401c05d800c0080006100700c0d040580f01032520032500b540e030300d0f4200c1c406000600c0c0031801c485c019500c8440d200c51001e81c0201400001c82030203007031918800c51440410301c10002d6600103100100c0d24825022108001d0b03d40c0528240300c400707445010000c401c5c0000060010340325134050100b09940004039011800d41c0000241408002050106070402c103003c2400305242c149044910b024100e030512064081c0000c0103512442a4442d242c02041c407400880c0c0c06da1403c10102d42c6080c8401da0464894000c604664040c0000d84402d4001a0030b080001c10381b40098450040510a03c071222400140c4503941c0c0011440001c1456490320541400f4550348244244079503c6403590796011030b564030b40543d07500e20303031035085417403184c8100c0c1141c0600822500181504011001c04010042c82d84540b41103080100f035038030502d07018014000b80340441c40c0c0000709500484 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 74744039 1250 74742789 74742797
    0xc080d0305010e01180c031d010f050114010c0f0203070506030a020406021014070e01050f18030f1606050915040608091c0f180509040f0506090c0f1306090501090606 73
    0xa40d035001c83d40101e007070a014071100310412410501e01619141d00082640019041c040707804c8c03101000d1019102203050075101165103d150b0300c941c4440314461140508180070000028031101c10000304995880d8134014400310000e0a00300642d45d04100c0c0c180181385c01001640e6900d46124144060b4000d84988800b6101d80700c041011603940b400781001000d50071b45043e0a80d61560811104a03d051003e079041c80300410512198452010043c90143c2c0e115002c466419800018140f404000000b81c0380303a1703044005403c248036600380c1084101c0726580741180e251401080021040c8a4015085200c0807000500080031034105042e188188000703001e030388840000d01840550010044040301c0003071480d903c5995018014a17144158641041920840c3c64036240428000d0708251000c2c0d6100785440301841c1000020004194002030010181c80444500d40109810703030341c030740b0440d445800042903800004080741e00620080c49007000a100e80d582d40c4058400810050007140002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 74745289 1250 74744039 74744041
    0x115120b1f090e06030a201216080c040b030a02060a170130030503010b07060b0a030b040b090307051002091305010b030915060306010506210705090405070c031205060a030c080d0305 80
    0xe160100d030724540160801500207c500001c00c1d224000c0080c0e40d9950380c00b101c0340002c1032954101b08920109002c1511144000b14101940540f40c055045a618461400d1a911034031070380b0b020501309142681a075203d03880c1c2034500015280c404038440c40d0001002c0c20000040d0120700020345142d0400b042001a58101d00d13580041e0a902030401e000d00401c1040004004010254004040e01c5004802c00a40c03800c0340400100c00701466401a151080e8410502051005200c20b01d0341014180c002186402c410743e68007034991400e44820040700f1350100302c44440740c1f120b15026101161001040044e076840708842503064205a0b95942e091180404d5805102044041180542401402050707160f203044204070480d8040000c00c8589258000a0001104100c0501d0b00a0180c1e4440a40345c107005c0061100722440280340d4001c0102040c05a80442c0d007010403288242104480070a0396512400491001002c030341c4020103859500c4000212038102041c131030600d0306140e8090000e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 74746539 1250 74745289 74745301
    0x706050c0702040c050306010903020f060906040803220e0c03060f21010b0307030b04140a0507090b010e010804080d0e03090a030308160206010b0a03020d1d0a0501050115120b1f090e 80
    0xc3d46c0000c85199001c54621f2500b80050300c0c02400d08107100c600182800c1c900700021011450316042a40500c406902c0490305005000c4944034082440760764200d0307400740618054038200308540c041c0800d8004800040800d0094035102d1111250711005806d850a40c0031138515400350f040803903981610385d468000100300c42e20300851800200c80c1c018000080545503a00d6040e45807000017a101840c0c89003271f8842c4001142804504018900c50b400002c0540c04500003512100850901504226844080000090a070015211003c0348071900040c240070034100385144d48110a0076607842460380c1c03000000c1690000c04039106a800084501251101030400ea80d501020700035810f500c00103004070041a407003a8060802150f140d44007140119004040000300d11490f141d42c0c8640c2c01c02c9103400c1c00d0203000d0040c580106544460141c980c2070400005000e03045003000200615220b0316801141d9544107120f00030304c058010643d500010340f003c082c110544510500840c1d10060307000581c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 74747789 1250 74746539 74746547
    0x807150b0906130e031201030b01140904170a1133010b03130606050405040b06240301060c06060801061d010b0c0318041404060e0f0f150c0706050c0702040c 69
    0x101445000e8507844050304010743c01000f52010301681510761009001c0714040215141780700340210700408008180d541400300d20010301c01440c0c0c4050254102d0410f02000801e1780c600745440c1c1c1070842c0d921340c48400c1410200c440c00c0c03a1143e452058868540310918030107005001c0050320b021240c500180c075040e9401c07035020441c2403003103603401d04040c80001c50181e40040c1d0019402d22511001070350544a03c00a022500c2c11742d800c0e61040c0903603041007001d00702480600303030700b500030b0220100860011170b14480c01d21050040d0402c00840c7d032024410806036400c110064070394030b00288031541d2101d003104001210000c0100f0810116000040d41002d0f840840d00480301c100302440c0790100f001c1000d904060100d1041d0f4119a4544030290308441d0398007034500961180c0400700781d034003450304202e28000700304100703140c250000490392111010008454410f50510f031b03c21600c541d5803880c1480140941140036109506150810105003148c2c1c00518049200b101c0c00c014191485c2c200715 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 74749039 1250 74747789 74747791
    0xf01020a15021e0d0501031406040f031407150504050d0c05060f0402130905060907060906020c09040c080307030e1503010605120402060d0903050910050f0409180807150b09 76
    0x140545500c100410740c5000603070000e25426079804220743c0205034403d0908000da011301a000300260343c0d00014410405059500403c0002070401000141400e4071070300c138540c00c07401c0001e007403140005c8200322421192003541c585136080303138008205418404000e005044100c604603030b540079402401c24003a0042200010f60742d0404024002c9558000c0045034030341c00940700341ea010074451041400c011183c040d80c0c06292065000e400d9505107042c0b40b501e4010302d50410700921000410500c1429800503030b441e500c1c0022140344186440702c1c00d1480c1d500c041c5400c450024000003412505064001110581818054a860311380b076450790f024050a000c280982c01c005072040140c40b100403100070707070150081e0008011a00c2d00b003860030b1314000c071100c03424101e02007a8046061011b5280c481440d824454880c00c01c02e2922803e0141c4403170703d10a41c081e1006665540b03180711341440f0001c0940031100d07800921295100300500b0280c0907142508030140e030482c28000a0646030400308a02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 74750289 1250 74749039 74749043
    0xa1d06030f0106030f06050a03120809031903111303030215010f0e010306020a0e060307210b090c0307090b0a030203090d030c050f1813060503060a090c12020f040c02010b0f01020a 79
    0x407416420074900b103002c1c2c40c02d20806881c0d2501d03884041829541c05003000000c6200b05a142c0190072025000341c80e000380209020030f1a0414003121511a1343d040f0110406e0301c2c245800036034501038039880365403401a011140c0c0c140d6440140441015000034912590000320032444041d0381e42c0344c0d440910a0803500a103800300d08807000400c00070b04590090f0201c260203080421420322003001141d0345410803188600001c000814543c2c02400d04038080070109884c11082c01003071041e0000c24602d210151007400702041c0000050702aa101e50a1000070707081e01c5034190b0b500c848100c0002d000c0c1d001991440d20798000d4045801c1d40a0289c850030894800984030b050601e455a18044500d4001c10b01c14540611540000b030b40c01d5803402148041080640c20004403d410f040c10f2502d40b18004003951202844d2549a10100d1002c0c080502112140015a82d00e90043e03c041407100f4459000103070014100722016801a4042d044100c5014041d0b40c100890782000b0012a43c40c1d404001c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 74751539 1250 74750289 74750311
    0x3021203070519140124080c090711070f030602072003060402042313030f020304030c090f0b130608120f120702070f06030c02060703060b1b0f030a1d0603 68
    0x4036030b14685006412500035015200140e03d40c15800c004034251000c02070007904900000c0b11201c1c0b8403800121b42400b80c11128010700c8030b02d42040102d00070318005020f95050100540101062003000c101c20005404044004140302c3d580c0e2a10001940211030102c5000700141c58404482c0c0c244892a1500100140100455115074091000401d00c1001071650104200c04101d229188030305103a00501800c84a008204e1883c20300400d000d5a0a00402c2150000c2100300003041001801070700396251048001405043e48003c100141400c0625a03000200d0340101420303180e0581c4070500702d460107026940c400e0b401140712860361107020510411410107020700d8800d15544404541d021000d0300480c1da80580f03440c0740d400203555582c00480005d4039080e00b8285030741d05100d0260000203506007805420704103003180076180600048400c1a542d10150100340a4040040200507000a401c0d0f83d80ca00c4180c4004000911440c5510101207228020450a00305601141d10444035154 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 74752789 1250 74751539 74751553
    0x201090215030f13060b0d03020a0b010b09030303010303030b01030603170c0c010807050f0d180c0f0608010311010c0302071e0905090d1b030207030507060305090c01020a030806040207031206090501030212030705 93
    0x10340e046400741240019600e00380d5966814a0340c1e104c5007c00d211141c001e030000c1200d49540d207000c3c2c00410b4140c01a511810003031004841c1600e000040c0c0f419260325041c003041c1e12a800b40120b00070201d6510140c2880760980740e21184181d29001030280380c0d05c1c68141c540c007400b044019195507100ba5080c40008004001960f4480da4100140001800e10702c404156025410807504500020030019520100355250800c034842c01b049080009060509041c002076140d030726038038a2000040c04c050705108142c1c44202c10503209002c9003010341201c00340401c04080e000c0084854401c90300a4241702443d11001c150084000194038062071210b50b9025003002401d5122040d140c81e00c98210154071542034044001901808400041d2110b603600241620300b07a1440c600d01416202030721305541041c50b414011070703030229003646c0c4284252400f5948402c580750480b8105442240c80403154600328001c10000d4589d003001d41240d00031250001c40c0280000300c070741c50b4861003100034810f902c450307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 74754039 1250 74752789 74752801
    0x60406030f0207120201050609090604080405040504030e030601140f010207050607020d0212150f012702030c0706020c010501080c0604290706020a02010501030c06020102070c21020a060201090215030f 88
    0x1d002400160303015000035061000e40e640d594140039100010201607511042001402d04000e0308555001c50b10307a000301160704082d212000c00344500d00a4600031600c0f840010107142c0580d51250942e000641110902d42c0c1d214926621a0f1940450340e2040c3c00040554dc02988001040320585500030320f10b40c9001c00d10341c2081312540c5684403c982090141021044444040c080b00a1055168481604902d4000714109100f10140c0010b0401c40c0101200482444d4015600c217a00e403403051b0040e540d48a0300d04102c00c9020f01c80004043c2d9000003014404100190010b1b412a60020220b03225043d81500300700041c0a580640385407500c851001030b442c80c80c1081100480c03515142010701d441c50035103814003a0703401b8214002c007503034540700100200310b400ca030120000c10f4584001c5080004a0340c3c0c12404480030301c00d03074036207000f034115000c2a80d0034203601c0410144c1c02003004160540d01e80700603004e01940c001c1a846060051140c200f0b18521600320303441240030b4211410196121 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 74755289 1250 74754039 74754041
    0x7050a05130b09070309060b0103020c0c04050a1b11010e0a05030d050a1508011a06090f010e0613170c010c020906101101050c0702150921100f09060b0f06040603 71
    0x11000e80c0101d00d03119038800c4029241c4040071806804582d5010843c1d00050901009a454141c003607810141704009456422001044040407000b08a1b00850316841e004181c60150850500c00c103c50481520303440503071a04844407200c00c00b1607030000d0125049094205845400042c400f40494100b0010206c0e420140e612950b40a1180080080c0011000e0308003401d03000790b0303080500755070b549941c1c3d0b401030040780001548802088905d00e00d0015008086102141030107209414403c00f0b2031540c1d10f03a911203042d82e66107506480b6014a441d80c071082d0341403072282050360130314a010303101400c0e42e00c0d4401c2040541e80c3c2e07006406035060303484660510040c4414080d02001b004500d0b040c0c0159004280200b0307000e4529a081c042d202d01e103070f00402841c0c0039002c40102c83c8400404c24242c0a46425004000f0204020300b040c9078180c1c02021907040c21083c40d0794941c420314181915900058662100403260f001e136000b002681030311428009541b0401228907031100c02400200101807107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 74756539 1250 74755289 74755309
    0x7060c03050304050f061005040e0607090506070507030b1f06050a0c030f030f0e0d18180923240702120307030603060f0230010b160f0b0a0e07050a05 66
    0x1181c001c980601000822686c1000f4041d6510b001e5020f00e40400c10040c6450b000d0303801e4103c000000b80c0004d0810703280c05019000148a07550042741d01040034000e0107802e00c1071400558100c401c581d21442d01012046c40c420640304c04281050700b41ea00030132480d216906590420101d9120642c55024a442c00e50f0082c8072100000c1c101511680500f509015500403400403c05802c01000401400d801c05080c00f442c0fa00d2220b500840140c040011210414990503440c03202da00005006009007009000403e40011400200b0341054014a459200048480351a4803440021041c0301c03440700b01220281084d2203a00040e80a00c0a10840030360803002590016824100003624541c2d80e5a900240d03021250701e02c6a2075404201325007940b04c030402c110b0391440343c244000c4600c15980c01d40720b5508418028103120b1940810307030342a904d07070b864204150a90000e281014445041c03034040c0d02c0a0017243c80340d1603a41086071121a101c400a07051060782e40c010b00d2040f210781801c0c01e1240e4088 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 74757789 1250 74756539 74756543
    0x132c06040f0e0a0f030210020c07030f030302040b130501020105010608040201020604020f030304090c03050105030d02071203080a06050904140f06090a150f02030f040501240303030209040605030712060e07060c03050304 96
    0x10380c0d5540304208082c10804a10b00a12074000c40d1000e0b03e1071306001e8240700443d41140070040c010410745080f000c0c003042c0c01c0140c2c5e0348002440703514005810704038000d01640c2c110b41c03a0f0003000030740d0005c0ca03001c0084220895609a00074001682ca40c00d040b207a0070000e0b02c1c000c0c00741c1d00c1000400c00505c0d15401c0c2103000328002d41140e0502e03954803041410313520715008c101c012a540b10014880b5041c2849200e1f402c035451300041071090310700044500e10584051b0003804000310503020403400251f50300414000e040003072204869041a04007450741ca546814100d0a038411103000c021400404200188201c1d01e07035019001c0030900d40c4403122201c0590364882c4110781d031049500c1d0035004170703c00341d4001c80703191761074275400d190503e4901d013144d02d0b8010400014400c42c01403e80c1200c1082c121064030f925150141e140d00c01c2c140480d028008680000c6c3c3d2600950201040203084a03280c084918010a000d0040c140350f036a80540b034010a00607d0300068002483c000468010f000540c5c03c41c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 74759039 1250 74757789 74757791
    0x1030b100e0306090a05070e0c07020d0b07020c0a180c020a020a0305060708090105010e06040b04020c0703061e05010503120c0304030605100f0b09030703120c08132c06040f 76
    0x852018001403100c40d80c0e4906201084001e5003000c000d003810060b50350300c134801c1001024400569110303030390381f251703244a0050000022030018084d808240181c8840e203074050001d860030001460204003082048485900500c1616071528091400c8611541100c034942902410107001c22070002c0900440d000400035880b80c40c0c8106c00584801000d4002107010740b002c3c14090800c00c000504c27003040500a0b00690b810440140b0140810004140c0c00c00320803100090700c074808201003400b0340141003000d61580940e0400006000c03050304401e49121071642e0300710320340c5002c00350344040302d0003801800c0d0550f000ea020078003601c0d41c100041c00c42c1403400c01140d0502c0c0d42c82d518042590000c50300510b04c01d040c200100716110325031000c100030f400780802003801d20949801081d61405a80300c05030004100030003841006008189102c60b054002408645d00e40c0746a042d90750f0043c681c410382d88900d651550300b040360603801c110090b0203140c001d5507000c0c41d15180c00b000090b29200c40400015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 74760289 1250 74759039 74759051
    0x60d0210030917030402030705120d260f06030c0105040315330503060601030902100e121603020a0603090206160c0b040e061801080c01050c0709091b06020102070305180103 76
    0x403c0001522021804040d502070303640c0c2ca0700744141400c01116502c1390b4096640f0003103500301d110021528580058140c43d192203d45402d040407081c42031148100c1003200980024028040c41c500803c41c440e1409600700e949084031040111124030603444094114140600109041c9450350041c5640e00e140381010840c04580ba88540707803189042ca202003211032481400c00c100d04080c0107040d48400242810031a503140da4001c00c02c21034a03d40c900081220150300400c403984c0c0c154121003052103c0d030465510000e2000132116000f400d00040c0e2251103c0000010250b200c0d010390000d4030b07806400942406190312103244010160031085604032038036807021510140c1040a80300511243c3c07a030303001c1030411000703004030300c00002084501d2a218000501c0810b0313000914600b001400e182c035596a41b14491250700f008565000f80740c500d424102e142c0c09209100e000416010741031007080c00d0060352104147e00300c1c403400340000d0104200b417000352500b90000f40c850701e0701d20041c1408504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 74761539 1250 74760289 74760293
    0xc060e030a031d030114010303021005011401080604090b0a09020109050405010b0f0c01020f180f03010506030325020418020102060903181005130e01091d060604020705120403080403061103060d02100309 89
    0x7960403010707200480c203821b00010828194100140d45a40b4000b0074204410b5040c0039100144440750200e041c14000030384007290781502d550380804916500454000c02c0d5091069010b0044d140c48542030b80040c0401d03a0110f01c9242c184143d50485a90059107840c0541d113908280301c0b504901c0c402a480e5509000c40c0d0711039501100100348500c40884000300b480780d544104440341e01d1150440e40603a01d01810804942c50000880300c11082c00308000c030b5000888401444880c581440c0250014201442104280c1141c402420268400d800f60b40583d03480314221035480c0617003044403400d1010144a8036407400d00d0804c0c6404602c842c034115180480751031045000700690f81c84010445801d0004100340b0390791744128028940e41065125221825101665548001800b914400e5500049140c00c00070f0400071600300c5a402810036840d1a1380e82801201e68100b440156015401c04461042242407501264401c000c001e086030150b01440d020303c0b20b0402c0d14042da9082c142e54a0140c40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 74762789 1250 74761539 74761541
    0x1020703080d05100602010b030c0609040b04090609020103050f1b0a031b0206060a0b040308040b0f040e010b0c0715020604060903030e07030501150e07121a090702010203040c060e030a031d0301 85
    0x710050045001083d03505000781c02c1c048800316507100c1c008591402076945c1a650f40407c000381c0c444021180e568849030302c2d5001034010542080c44503800b40c9020b69020401131301d82c10081d5214000d880c01c0140e42d9075640342b8101100100e40300340d6051361545c2240a1241070501030100c030340c0d1038a000100002030a030404151000104160003503400b800c1013041c0303031400192510240828515a90030545542d0720b0400500581c0200b0040c0c00c1e02080c262401402002034400803c1c0f18007110095580da88401e9450b0b5000242c80c410901402c0408039070500d404000c140651096402041103030f803152110001490851421010140c68419107003000d4010801c2c003002d14003800c0002032146004004c1c5807101000e41c000207084c03907068104030b111500705944030044040a2000704408400601010f000002c50484680c40380032081845540382d4150301962041d44610081c08046480391415290004180103580e031583c0a100101e0000c0d1040510010009140c00b03603110080c603800000e4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 74764039 1250 74762789 74762797
    0x30c0c03030e0a0b0a0e04020c03090a0e1f06090501030c1701060e01080a0b0102031605030418020403060b12030a050904060b0f0a090e070c2a08010b04140c0702040504020102070308 80
    0x90001260309054440320325103002428020000920b005140900017900505414131a0a005110ba5400320f1080d4809000340211841f4410003400c80803855100c414003212803200307545140000d8047d400208021407450008819240542c9032491617529020044000c1c0c4040c0004504122000151010180035110450b018105d9070301d800ca90020051f000502844d8000d2400350600d05102014029076004800c640e866040304010300031200547c104a03103544030b140d00c0080015501800c540e200c0031558060002d5070b2140800340f1250303940b030003008594554151038001d00e0b0410400c500c04035009500074440144068408502c0c0c40d038840341f00d0f00c7c9410a541c0440716034000111540700310f40c040340210103032002c41034000803070515100041c8103420110f40140181d482c5c0c0103204c64058402103030384040f0b41d204030004449495100140c0640354420700b00780180d003840c0c2a0950b600032030313504c14441d803003600b00c2c07a091030311503001c00000d1301d00508140c0c154090a0400300210384850014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 74765289 1250 74764039 74764043
    0x71b051023092118011103040806100f05040509120903010b0d14010b0108010f0303050d06050303070501090b01080c0906060d0b15070302070e01050102100c09120303140f09060f04030c0c03 83
    0x14214604070811504011041281a40300c0d020f82080701c0c07008143c0c0081113095450f800e00e003055400140c24a600d103140b2454104030460b100b110b041049020105002000395900246502d40d07043d9240140030076a03400761000700341ca0308441e503110340480c4c030040038001242000b00041401d94a01c0040707600c0114180d0151040c50790702e03140c0480a002401203500f0b011003841c101c0c0079507260010050801015020040030043c000840d5110340c0e1283d0800006014000c0560303941d400d061410034000c104007641241c0c1e03142d0406c000900702d003002c40c0d00d10b4101c0000e0400066940da410802400e40d02c100b8440740e405076103c09003081a120030700c408408100c00404555140b50034180a032a21b892507009100040c03140300188078990380413642200020444101003500c0c52034150984500119412510355420340081c9141403542c1504102c1075186040600c1d4195220b4036034849034103604641a00e8560320150100c0c0700c2d8554032503030903401406880c100340300301e80658803021911816402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 74766539 1250 74765289 74765293
    0x1d0a150f180605090c04030b0601021c11060106020102040f06120608010606050c010e0601060e0d14030a020304060e0f1c1109042d0b070c140f06071b05102309 70
    0xc800c1e40d2222600c660000b4040071140c840d210326021118405900c81da0100405580110020030a5640200022419000b0000d82c0c84d13808a454180189960301c1404082c9840c81072500000c0e8a81c010710844058410036800c1c18000c90400070103907603907405500c1c00f000c4280e48034000101030500303102d500d010f0190399413074a9891050111b120700f0341e044601040c040d904480300400020360881c1c1d640015a05c00c2ea4440300c0020b6904181304500c40001c820b030f810340030024061a0140d0301200410980310a41c50f0754000684410a0101800c501c03000280c000c0564001d42c5c040320b40d010070f8050b000d03204944c0507a59040344804146e05a40aa50484400420709681d01c91a03059043c40c04802c99180c600382c0c0f08035003039214940c004070050318207018090708482490070700c8410807651206409040440d0a840c2d903004c2c01540d90407046078041c00154603403000844400001a0075150a03411070000c1c0100c01681300310300700620603149542051245003d0b07108900401c642c04506c240440d0b40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 74767789 1250 74766539 74766569
    0xa05040f0b0406091208070501060e06040e01050112030c0c090e07030c1d04080f160b060f030a03090902030c0403060c0c02090703090203030414010c0503031f1d0a150f 74
    0x41a03204891154100c441c0101051109010301d07a40881810200c8500c40b10f0040a1013060a00d000c15210300c0402800d15420980049240701d41d005072a800303018140d40410480002006160807640207004070407410418944002c04203200341142640c03103018031800b031605682e400d61001181d0b9001211140c07a00003a204006000f1604d035948000d002d00ea030030203003400703d031600c0e16141100180005d003241004101c1c1010004031302e0541d8410f41d00c03110025148055070422034680301c82100d802e40308080002e203211107400c0205141003420f9150311405049424214018065040280030f030407207090612000000c00c0c25030203a0288191903403116051601e0f14018488506402820a01894144400a80141c42c000212401c9440b482c1d00009010203200040350040c1c80ca06003e4200d200100500c1892990440d40e0003940d5007503400845507981e65030007180092207196254001c0f1300783c48e0029880181a070080e55400c0c910421200788a83c50b030320741f0040d4028980065401401c1c00e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 74769039 1250 74767789 74767799
    0x607032a0606060519030c0504150c06050901020c03160222140916120c09060f060e01020c06070f020f1e03060a02090616080c070b030601021608120903030c030a0504 73
    0x4410300d00500f64510703280f49084490702d414a54810401178442c10143d40e140090101480f1740b083c1c801420708a40d035a001144240801000c0072850340003601c8491130440811801e41051085416070241000a9410701c00c0c40850352090681005d000c0c1d821110b102c0389101005e4100034440c029002c030040c002a5210701d080c1c80300990600409415143d40b0001d402d507a1142640c5403101101c02a503401c2c00205000d1130070305c041c2880b9070b02224200c1d051440214140340c07402d1104007540d659544001e044400c01004aa442040005258101204102d40c0c008201c0f000c810129203400500b88040c2c1520700000700701c0c2010224100009140711f2070010066190500c102d0342c0116602d1070550802c0c0c8550009030692141c00c41410541c0564156582001003440507a20131a58000a0720740b460755920880007150310480c0d41500501400600c140c14061050420084e91803010040164107070302900103a00764050a0080e90620050150a920310b10070001048200c4c3d2503640c1c2a140c528003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 74770289 1250 74769039 74769041
    0xc0c030d080c030a14010b2203030203030a09060b06030403020309030d030c120b03151f0b030906160216060c06061d0a05060d080c010603050c01080103050d0302131d010311100804020607032a06 85
    0x182c625038002320340c020b030810109a00000b62500081c6000c800a0070072410b140040060800c28442a0005000310402045c103401001810100c40140c1c00e540790310408520031001c407400720f00a04003142c0c3c00d44140b607982c0e080c0e0748240381c01540030b0111595030065009880c0500750482d02041c070301040c1e51246180c4844010204000c00b05440b165045081c034800844e10780c6c4005126100e4541e6088150100d02d00c2049a41403680d4483c04030103080352030340d10040075400a120243c9105061a10001344000c4500880000042c010f026130800e4640b40301c120080e00c005005140d000366015003090104000d28024400c142c50b002c000203401d03103503180c03050500f0948c04d901418043c5130750040021880108400341807100d1440c0050b070310400c010070107030032003080d4005401d403c50300c1c06080c46001040600310305884c00703400b038608490340701d204000d4241c112843e000e0003e01d003400130900508101001d4880b807031281c00c0c404903008071069a09406680000c4007001914400d50207410700010b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 74771539 1250 74770289 74770327
    0x512030403080d0c090f06080405120313020d02031f0623010c0b040201050f0414191a090d0227060102010b0a1e0f09020c0c030d080c030a14010b 64
    0x15050285040c6440e40c0c07100125805520410007810b038491500590343e80c407500c180d0014003c00120181010341f200b9000342419130898040300c00b4440d50700c83e084440d0a180a1b05c1c8911004030b05111080c0d5241e0901c0085041e9480403600344c4611106221640d0441c0c03901044120864800030b88540303004100e0404502c3e6018080c201d0130421070600c0e0300e9030309ca09144440d80e003081400d106a251840101d401d482045200381d4180e1700031a01040049550310100c00800c0c08070741d030800000c1002c4a540001d0302c2c61040c0c2c164ad1100300984804401c2c0c0c400580000c200052038203203507442c40c0c1c0124889401c0303200840c08595400084a080c1c074075140810b40c20020a1008000e110440004118100800d01401004604107501c2040b400242d613261400b4022501c0002c600d1a51800120060f400840007580a0301400100010900340000c18007080c40c1076a807035000c640c8604d08034051036400500b50003c0203803600458840c0302d03048449240200310515099a40712000b042105607040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 74772789 1250 74771539 74771569
    0xf071a3f0f010302010503061504030206030c0d0c111b010201020c030c01020a0906140403030e131505012c120a05010e0309040f1404060b0409050708060709060203031303030f020705010203040b0105 87
    0x403030740d401400581da00ca400d5139445581500c10581980c585920110702d0b0266a000035400303080002044204420007001c0c190000d80f504007401038103e00f510941e14568050300381c821540c000d000c03807401d9010040f80006112010b0000618104408a0a0b41554080603c440701a900004d02c400c1aa81c0310100000402982c64005007445881d443e840c134504c1144409410081960215191540c5106540302c0744070024004000d107030400030881e820003a007031040d2800303c1c2e4000b030f46101e21000103011840c0c214100c0c180c2c0122101080070020314a074041d06040c1705104d15140702c80010024426009036007086030013540c5030440c0340b080006540110681035000c5080c0455800404524404d540d00254420f10101d000c503401004a0018210038001401e18401c10034005025000417a5282c000d014a40d1584401e0380c40e86000d0780e13240b20075140d102900d0004c9201c0004240719078055500c41e041e43d075001d031419611340c403050b09903001607405451503524200104003a103006800040422 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 74774039 1250 74772789 74772811
    0x30804091a120705090a0f05090106050a1203051204050307050307050114010501030b1819060603020910020f12130b0a0f030f0c0c0b0a060f0b0304050f071a3f 70
    0x4040342040750f1955584d11415005040500204081040d81d41116102880c80603041119280c100320030341c00382c0424400c0c94021074900c0400700304403200c6920540c3e004c1e010b483d464074129500070400910b501c010301c03c0e10103020500808000030002d00052600d58003c034001708101c1404074028950352010b030700c014145072408101600580710070000c7c0f4151f44442224030016903522076140400d114640d143d42006180c06c001040c100c0d0594040d0802d2481030b59a0711000000740d5060340d80300b200e4003540301154804d02c0c1c11540b8a031035400506088a80c0b15a0716002c0d50344030024262500700c8482c0d10f000c500107259803a00c081e814487c556201d0b14414042c0507403044100050301208454102030703d41050b40700000c1141c0300a4020f0350040100928000c02603035139062043d486d8000340c504451030b000d4000300c00c0390341030001660001c0d1603084492000801c40880300403140d42c82442007080203111003201c03102c0c490075111008401c419034079140070380080d402c2071301040d054002c01c1c1410703207 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 74775289 1250 74774039 74774059
    0x230a0c030c080303060a0603020903010f060b070b01090908070803041110030b100c0b0604020c0f030d090201140f030610110d110114010f03020d0f0f200405040f1b030804091a 77
    0x6640d5041c0e2070807c0301c105050040e5965031420200780504041080503000038140301e400240c40c800e810042c12880c1c007410400466036217034080d9209880388200e000e8002c0d0010b000c500c01040c2c280c4000c0d03402c00d12a9410091140b51080440c6a1800a040d060701180d900c500c500c1d61814221845a941ca09130700c3e00700311000c06582c42c0954440060503940c0201c0d40410480a0303110104100d440c003000040c1120348405e951814900601407404049000844410003512042905400e0f500f00260707003078419003159164028040348140442d481c808004482c50150031a090921031a16401402d1b560800d14079010902c41c4d0945001030750b81c14a8580c450010840408008198403d40e541101e020801c40c0d82d030b0a1148249003810800352160710b08c00300c0c0c9020051800001c00c86001100540c1105031044410041152002c0354054600e043c08262400015512001c880704611604061f2501545a40301c40382075070000e4014000d41c0c0d03a81c200f100c0005000100158031400211082c4501c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 74776539 1250 74775289 74775301
    0xa0c091212030c11011103010602070501020d05070b0a090b090a020f060702010e120f030301080a0507060908061b0c0d0e0307080604150c03060504020a05130b03060d230a0c030c080303 81
    0x1214628030090720030156616a52841c0a105100510280c1850002400180035138031101c1c031a03510030f10404002d489a104c0008195002188134005032001d41c81e80b078202900c2d500e90201280e001411020b08a039a800c40c8400104800f1416001e00300f404000c3c1420040c520622001140103150248a08802d111220060fa4001102d194a1000f544e41100401582d403070310740360054090416810b40404400803580060010740c0a1100e4081c2c01140d0b241c2e03940b902c050340c2020090180700b40903041413001500149060341e00852141035000d842e403a01c1c0e40d1003801800c1160004032140041c0e0030186440c032030300c0e00304401c0010f81302c0803000e05a1820141c0d01c0d591000700044e41a4001503c031510740c81d0b1305010364440b400912001e0020340d0340d042c03407501c01011580402c0c81d100344070303404540c0032031036000e6501628031070003025158030540e110680f03c084405e85001c00710705d1082070050210702c1100003880b130820814801e28450594608514082c0350f1802c1542004505500a00c10415 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 74777789 1250 74776539 74776553
    0x60f0a0e0a150f031403091206040506010f0e0105060a0908030f0711120c010f02010b04050f0916080d0c02190e160e011403090109050a0308070f021b040c05070b0a0c0912 75
    0x704603940a5000c1103900c10005c030301402d5020301c3e141140d0100b036804022824000c04510035220300e11600c1540d44030b85e245c148050341d85066000304403014844100510a5042000091113001e0150500c030700341d143e49100251039070340880c0407511030b0b46001c9488020041c50441001010030b04441058407500308407080c9a07911513022083c1d0402c20001400c00d5a00d000307601528846201410900c100c0c580781c01c6ca00240345056a00308041c0c400d4100c00401440c034a801c0c5000e03141584050000800c203900200d42c86600d040003a607022650024a00354230244680712001441042c10400807441c1904c0603070300c8211242c01c11824070404a003005c40680c0e00c41e40d40c924007482c2480d0191039844a4080500502d12540010003921921810105242c0c10001182c030800c5140d4581c105403152042c100d0319134041c8502e402041d1507100410f00c035031526412400b00b10b16203203043d508005035900c42044501d002d859070f40c2025608c0322080ba100c4e50040c5000003401200088119240207a580c2030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 74779039 1250 74777789 74777819
    0x9010f031806020703090803040303090303170603060105060918010f03020301060f032604080a2102070608040803090f0a03050909060904020105090405090f10150501110a0b060f0a0e0a15 82
    0x10302c8160300140e81c90405008a5445001e88503204c00c580c5c0f0340d901ca00d405040500305000a03004504600d86405421641c4040e0b548540c8000d0003420069103400244001a08602c00c4c255014401c01d640c090183c0d00250130a00a000706103007c10010b203140107040c2102c01719000038582c0e60010109101059405080f09001d80180c1178019030f0803d4850311b5400350080360800c003100d01500c00100b052010b50200321030386494602c135640301100c0210f010fa80e10340003403041901040040000602041488000d1517004d00380506844502c00c02200c00b038107104028000303c0c042000841c0c2c8413007a0420340e0311242e201c402981e03510340b241855000a88103000b03161110344101d45034000510304060a1080c403410420304800ca46071010714103808005004840da10840989e030380e850014196114101200304040d6500c0079000e03020003521840040b000061406401203116240458107485e54103904c3c008059002071548141070003d508020344100d6000b41c041c8448011080c8040c181c031213006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 74780289 1250 74779039 74779043
    0x1140a0c14030c2a0402030703020a1202130501050f041221030c1b0c093207081306231501030603080a1b06020309030c100509060a0c02100903030209010f0318 70
    0x2d007004e0440d00008007280d10002441e94100e0300200500000c0d82d0140c01521b1940140d454050726802c1000c5030320100c0c0580c0d82c1105120200c0203040119500500c002c00fa00326814407d02d1600d0344443c1e01d090a51140c840407100c0b44074102d00011007036548000d480f4682c500349814000c40b041c41074001e01003c0544214a100100035548908110b05415003000070310006100380a00b001300f617a010019111045031810182d056000d0b04101c410b2544040c2c0b064400382c940507450b8491050300011142c083c0002c0303440a42e05c0a092401c0f0700c6456640d81c402c40f0f00c1179481c03528541980a9050440310b25070352414541400c005200056840065a1810b01203281000f100040b010b0400301400f204000902064130000a01a20103030200040101005a108441000035800b540401321031041b00c1c08582070300102c0200385004103039000341078038002c0c610454000000d0401200b08980f8207031030480100754001903400b015600010081c071810303281d00303041040c41c00c0700b20040b100311617030080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 74781539 1250 74780289 74780323
    0x503160302040e040b250e01020c0d05060703090206040306090b06040b011d01081902030a020702030c0a180f0207050303090a020f0612040803070504080a0501050f0f0c1801140a0c14030c 82
    0x51000032254500c0d8803c0807005008200074103c98401703441d903140d5007c3c8034011300440c0740307500690825060880034158407500501c0c5030b5446202c110020001128102e91001003080b0000c08201140941d6070031a00410101d4401e0070300780b08100c1101d05000303034030307051000c1401004c403010f08001d2a01d017081020b0820007401e50300c3c103c940c080f4501111328001000d1020061004050840c1d0103040340a1003030f030868031740d41d8501041062860407441500c41604041680c011040c0b1540c0001150081e07611000d41881640e50760795040d43c004682c00c070007641c8a2620441035103014844075414040c1500e946240c405465000b8244900c0244090400303480000420041c607c510101c40003080c400c4243c8400713501c5c170f02d44140078103415650f01c04c0c00140d000100781082d043c0300c03900e4040e07141480c50b20314001a0503103004810100300002d0f41802404025009045903590040c80b110031990b4515903e03211502c6c1c11217000c031022a411030594001e000181aa40e4000b800640140010030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 74782789 1250 74781539 74781541
    0x204020c39031510050a17070b0405060d0903020309180a0b01031a040902030712030c031805130902041e0609050c0a0f11030d020706020301180b0112020a05040b04060503160302040e040b 82
    0xc040207a0750b964445c42d00524882030019102c100c4d42203c482c42001c02051300c158950328070400c0c4440c011802181e40c010010441c1c0941a801d9034411011640f290050740d0602280305c0020318440707454200b40341088100403c1041c1503849220710b048190007401d0070441401c0d8000d1a040040b6140300c40760140342ea4203203000642da41001861300030004e52242450380c1800c1d140050140b220b0707042c124041030b41400c43e449a4101c001540040e26000340c04400782203807451550010305500c0b9800c0ea0031507603440050301854801e00310b030180318100c0392000c1643c0340fa0500d90800c40c1c01c01400c4455003002404000300a90740040c510451100624088135006015070940e825482046141d0104904c009204801c100c25900610704075070400325400fa211911540030401e0701c417440a440d00003180d0341c14081c21801c40380d014112a80e01e03450300074200b648415281e0750340d9001e41c010b60040748000c403c0100f0040c00c20840d0080c80c41503e800e500306890540101d00106015000804101b80a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 74784039 1250 74782789 74782801
    0x150307030507081c0c030210050c0d0603030203040f0605040f0902031815040b0606030603060a020a0903051212010f12030e0111030a0c0312021c090204020c390315 72
    0x200003540d000416100c100795201c0405a961124214140602504140c40030500b40070b100440d81d040c0d01500940440301000301041d0080400504100d10b0140c203204103100c005262052601851080d001142e503141407902014422815500010400c90104000d106a6000c2082070040710060080541c590310741a100103100c089400c410003c502c2140301c010f039045111344010307000f10f008070200d00703013a2501414002d17035100c110384070342d015401040810b801001c2030f4010700c3c2103403552408149041e220340d1054201841e00e08095101c0c000800d0711281e02c0402004c4900412407110b051160034035040c0d0f0381881c581c07507500c050203120050400c0c070090390003036031640c04040c040019299070300e00d4510043c0c545003042c201035000940c40b24441c0c8441840e44200e5200d40e6514030000344c460044407a0101402c07a5820072608241c090000c5180303c802002010029030303160640e507a4400c010584445074500340b6002c001c003100311000040c0b00d0f8501207006c030107008d019001c83c3e616940344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 74785289 1250 74784039 74784043
    0x60708130312121503050604021018030506010305010c03090213020f0702130e21091212040308040608060307060509060a0306030804060c0510020901090b0a020124061e081503 77
    0x250300240107881d0580360302101c26800400303440d03031082d0721000700400107040c0c03400e154500503808000c2c40387c1d00180c00b0a000d86421490814244c0700761504d030882500034040703405441001c0d40129101e60000005000700305003805040c0c0d40c10760b6841d040040040d1a00090011408070f101051a02e50001d400d00408a520b0121000c0700e40243c040c20b1100d81d80840c2030010100119440c2c4c1502a480d140c0107002e00d05203100800f00d101c01034a41c00c000703107030041101daa40c00d5000d01031288129140c86010155041c013400040d8003e656040d03c85291004c00783c2006001012244241c00c043c2b0103003c1160454181c3d4000202621710f2620390480d024280d00400140d00301404c40d920211300003a4041c1d02c44d04403c0001d01c20420b031085007000340c00010070381c0201100c07170b4003140d0700c04c1060015081ea94040d00f0906c120348008070300c24003032243d880b07802d0b5051021212a46c41d40038080c00250340000c030300000ca0800c9104c0c503600c0d05058a004008440107041100d1011009074801030650741 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 74786539 1250 74785289 74785327
    0x1b010f050c01090305180904080319020702090403020706021b09010e15030a0606090c05130504051b0a030504020a050607050c01050f040f090c11160302090414010c020607030e0c060708 81
    0x14002000402d4040c04c01500c1a080368581e44040d00303111411004c6401c0444050340a158042c00c110b04680300d05680c00307009108074800c0c00816a09209503005079642080c014000c5000f6005006200c1c14080000d00b00301d070b443d440751145501c0c0d012036545a2100d40e1240c0c112466002d00d00707940d4031425014018402001c11740b5a251194003994018002a07500c001c0c00c98031013900c00c01c19120340d450203072554080c10001d108014110b041c2003255092076000705900030328501510b07900305c442098009154109002d0078001950f5182007200314202080b8460191000f00c404030700f014043da07a815034654070741107154100300b000324041032844181003c1d180544103007035490704001c2c0c403508984010007040070740300e00040f90307c0700c048580703d0045074000450030603500c0d4042c00c60560f0240119004054012100642602c201d440802c80030710401501300c0c041d40c0940700c2410000300040c26a0b407040d0702810705820042c0040055a2800103c80d90141d0268445071140100b240040b000c00b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 74787789 1250 74786539 74786557
    0xf010903080d06240915020c0607080304020405010515180a0b0406050306040b0d05030a180509010b030f07020105070c11040f060807060f020309130207060f0e010e010605031b010f05 80
    0x4000300c0d001070181540c1c1c206100380e0b9440301c0d591008980f54060050f400390004d40c1400454034142c42400b9110400c800d032990043c00d070046621401d2148041041584404410b07a9100f40c08002d210452900d0b0080c0e40c014402255550041081c110003900e41707100304075002c120650708152240490f00c0c2e00700c0400007400d5040a59441b990350701000340c40b40d881100c101c1c1c46145000d0003c00245828042414a0394001c0000c41c2013141c0c0070340076103c900c8080300b074985400b286140064160f0313070042d91034043d000301030a141d201d0038400b20000c2e180c4000307070804082d039040c0320800040641c000705920b8030310340100024009103080404103006111101b44c5a800c64100345000c6212400012004101c0c0d16668409404403a41c0d40f0407603d03402800d030f44c030341e002042c1c040004103e0307070980181030801e00481c0c0019a56080114150803a248481c500e03205945861502118080a204480c000c00080c2d000d04000d201840611480c060810549810f00180d00b90b101e5489100e03500340c603611b81d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 74789039 1250 74787789 74787803
    0x170d0c0b0f071e02160f0308040303111002071101030b01140901030207020d0b070201051605030721021201060e0f0301060b0703030e15090c130b01020c060901120207080702040506010801030803060f010903 90
    0x103552009480c5c0c48001c82c8502c494031075100004a00c0c041c1d0040004590300720607590308140c116507040f26882601c00350241c0d984140c43d207100440703d903440141301c01403143c48000c005406190000d000da6540b0001c40341131103081940e00d01c0ba00010022512200c10074a1b0050790303aa000d1000071500442d122015012082100c00c014000707405501c1503025082031420700c0b2038007040503011640d603c4100da21070001060f20700d1541d0b25a00343c801e6000380107502d440141c06d100001030007246802090303104400042646403982494204103000711107010054000b07003c0d6904040e00a0f51a206004c0c0041c201640c80e1482507414005210712500842280c43d80340c424148a070166030740b44106802c851181c41034049400c503d6090784a034035608030713060f0094198481180204050390b040f68010f1414461b40c022900040407c42c401454440c0c0306a4456445030614018013040f564020500c5050241c2e280c01840410001015254006002c90702080c0d070000701c0f1700407600764240c3d61004200c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 74790289 1250 74789039 74789087
    0x4030f1107030606120c080a150902180412030e070807210b010f0e06090106020d1101020f0a20060603060a0e070504020d05040201111c08090106050a170d0c0b0f07 72
    0x3501e085c42404078024500c00d1803403602c900f8025151004950000c20b9183c01030030301c0d10040240e42008076290300060200c0c0142c600700c4010000003000b1507040303840d60818160020003139014820081c0d000d260400030f0105c14100a1140c0c2e03225113a0045a090b01941c0000c0054241050345981c1f12940c880d1814002c4e5950f1542081c1c20401d900444c2c400b450210009006c030300f4603101c203904030788440d03000704000318100c4000d031200c603c030760f0b0382c4400c07075408020703140d050400072004122a40c0c42e6070b0b81a45144c00e031805541c5110680303040b4011074001b101400000d99000406a80058002d9400500c03210440c8885142c011607502c4a6042800441d020420410a03445184210300030380350680360b40803005c50701d901e0b025401408844820040c444403ca0f5205658640e882804030f000081c0c8241c9860000f500902164000100341c00501100740a110041c4000003005006040c10180c1c02c04681c1c0b040c4452200403c00303080747e81c05100040507d8481c1c040700c00e004240c40050400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 74791539 1250 74790289 74790299
    0x9080f0408010c0507020603010e04030c0b07020c03070b07081b0c030601030b04110f060301090b18040803010f0f080601050616061409070501140f0a0c050f06150904030f1107030606 80
    0x9400c284100400c0303520308800091120700a03c12190100d0380200306070b00c0d607820700c4284111414041c0044e0100204503e00500003064010f82900408071900105401000c01007058501203403900003200359001445075400240c1d441d4180d880485071604120b40345e142800c40503260504090310280d0500c100b00000081c8a03400026500070781c0502d500511000f0720380140040d86040348201a0031107010001080700050650081c868518000e110345003071030a484d54007040080c01d6506035914140000104841108c0c03012200040c18200100520302d440c0c40b40842d03d40d1414800d19002d1071000800d1500083c0c05071016020640c840745c100981c18075040291f1103443d00b120110054421800e010403c2d600881c00801c1e120315010030b003443d005910300c0280e42d42d04032084070800d011400b900070002038814005c3d5100c460070300004000d640303060701030b00411b0603034010020700a0039024140800b00c1e0b80b29141c41c4810040d03041c000b1007480c0b031101040c60005aa440645100d180038000f1407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 74792789 1250 74791539 74791567
    0x30b1801140106141603030b0d02090a020c0613030c0b07030e01020c1605041109060c07050904030e190e0a0509120406021b0406060c15020d020a08070215060d03120908 74
    0x106946007503891040c510302d40040c683c3e5a20415170912501403a2100920000b48030b41c1200c00c07038a001401c07100c8803581ca0b03800b04041c02d4042e141241d08680102d8041454002040f40313507405809020b101900c031712540c9000d0a01d8180b0744000e008044040c00140381c0c94000e400020300100d21800840d40c0b0f1a02e107600d15240c0c00480ca8641c0c1d480072612000410345000d0059484144140540c5840c0144a60810059500c03c03a00480c4600422100058030350707a051505100740d00036280c2c2080400004208485003c03000b10119032001d01070003e02003200070008555005626400000d01500c03889000361408144000f4948106000540031859a90200c2c0380c03001c03005030312840c00384840f0801c104410340d030450090600060405510001003024100c1c1000110844900103140c0540d556010060740d008111200102d0140c070284003006604100381444050300d16079680e80c41c10400c000031040301800c5009001c20109c2001a40e0001c1319502050009074030400040e5a52400050a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 74794039 1250 74792789 74792791
    0xd0b061903050d080604020c1e0a02030f0d0305011505030708040c08060c040611061501050d06080d0302090f04050c032a03090f0d020f0309130f050a061518030b180114 74
    0x2c00003c0d5200c01041440c2014008e582d490203c0304003a08400352450750741a00300781000c50401c4540b00d00240e11000d601e09201d01c04007402c082001e850700508444c40a0180d07001039000004290542048a0b01c41c0d0f03002d400d80f0f4100c0c0451030070f00d0054642d4100030a103950700340c20464080c0903600a112005090800034003ca0306581c0300c0701c49070a03030040f0103900c0f00401c4604101940c5080344401c695881440100b1400b10300c900000703400c5032500705880c9007810000144000c00d40c00151240c003460800305107141101c0480d018480c0d494220520800e0380005002541440fa0001d00314031405030400340040100e012010075a100d103001e0200c5030350b891001051507130601076402c845544a101040549591b47c200d0700031490701408006010400344803284215103181d50310050882c495070b80c0680360203500342420100c2d80c107007413808010103043c010304408240444600c0c44a1080d0071040c13034800b240d4102c000013500e50780b940c03042c00031a00d2161540c0015460a50440c525a1111149d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 74795289 1250 74794039 74794063
    0x5070c050105070503191802010c020118060504090b090910020d0b0312030708010f030b070c11040509010c0806010203090a090906061706041106030c03160302090612010e0c030103020d0b06190305 86
    0x42d030b07000c0000d860700c5022900d07c86c8400300580d040c440d5880140d4001c03420640f0b00e92040c981020464070341d01c544181e806540d0810000514005810003001c070300e0740100c1442803c06c07552050f140c00c1141401d6611640008401962a004510300c0180c01070b5500503840f4210103025540c11480040f00d000590b0700468019010400305070000c940810f1401c402e81c1030f0b0344c2c0140e498101c0c0c0c0303415100759078413003086c0001c8442c03c0c1d41403d0300700d180d19103002e02806100c3c41000842d0140c60345001400100c80101201e04541c414821036400f0740c3e6146240b81111002e00000928502e6800c00c04068000c641010b4074009024030315410090000600381e204601034101c5d40c0115451360100303c01848183d0714003803410000e202181102000401d0b1211000c06401c00610702029030f0045100c0350841100414030010200041000404289140ea401100c0010a41c990741c11540040d05460300b1100140180c029080052040d4484500c09100c00807a5200c2c4450b081d92441c040c0d039211540c80751 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 74796539 1250 74795289 74795311
    0x9060609140403020a0b04082502030f0c032a180a0609060302060307031d0f0304060201050f091903020304030204360b01090e0a0206030a0204050a12050601030605070c050105070503 80
    0x3212190306681c241890041c0d5040c1e0142048040741c4d01d441d1004a0040d10a5130b890104105249203680306144918032a942c2c51104482011a401098181425100720622580040c0703034149066401250003a03698406c2038603040c8802000d10003c503c0301c004191203400c0f5041e06d5000c010720b0348000d2082d1107005200300c01d120f42c030b072074101400980720355100c0250044000d0022810300c0b4080d400101548848244100a050318044960314100b08900e031003445800005007030100036428010705500640c01e0417080340340d05150300903e59414102015030031200442044100701131007403003102c000310b170010000d101000411200745094401c0d43d940b0045402c165031080781c982d40300303600655411b0704841c032000203a182000a001501c1c030140311032003a004003560000140c0c0e80c213020f14043d02c1895001602c03241418244417111601d6000369031190151f010400005100140c200c0c1540c1d888140480c080d1100d440949180081c0b8038010125400d1000f00040e00364820060752040c02c0d2850 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 74797789 1250 74796539 74796551
    0x1050d06090813051507020904080708091302130f05030607051e030c0d0506042c010b040207050c090c070506011a0403020d030e131112062806120e0303060f0a080109060609 76
    0x10325106c0c070b6030001d40025004000a010801d80009010700314004e40e2510f260111820004080010000c03948810540c003080010b8444007080343c1c07502030504450050111420400000c1e91180002c0c942d0040000000b500d0f45072a410000d1000303c0147c80016649a0900500c05615a008403a881403800d203082e0000f84140707841c2c0103c1125202c0307003451004045204000f50324558080200009079903c0780c64002171a102c0c2d1000303002c3c05014401030117200c8480c43c10071011840240003859102c20500c0100040750020500504403a891211400c07000030610340c0c0656401164006036102c42c00c140d18509040c1c100da00220302c03a00071154010640c54104003481150211700c12502d0201d800d01c0400c2c11000c9510b001c90300410300800d03480b8065501e0f0f158452141d04030400740304081d1a0a07041180d80e800401055408000c10300c20710482d0388a45900b5a2400000c0c0b41c5841030919000700078140e25440b01e000d028040100091201070700c1c0707040450242402d84542508946841d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 74799039 1250 74797789 74797819
    0x6121317180f041803030b090703050403050d0c090f080a050709020406090b09040204050d151a06070b1e070e010915020304032415090c020d020601050d0609081305 72
    0x10303048820701d152044003003030607030711400030310590006042e61140c1040d522104c51044048020802400354030030780d404600c4586250601c4a001000703040d945c03e05050006000001e5080700c259081c03020031607800154408440307822240c0b02d140741c3c0000d0400c1c01d46440850340010100388614a14090001c450780720303a4860b10041288950711a10b80003407540981800350304101c0c4014480703290010009420161543d0000b41c507a800c80b032003200c80302520603403039a4803140d500030034130040400d01c1000d811550b10f0313021852512443c01d00504000d1488005401228a0903100100d120a01c1c4000c0c06c0d803030a8100a4490540e400a80c3d000c41c8000745c00160205400c182002500c1007503001d5400c0915540d04c1e0b14141e404500c07440d103500a0030030390603080e00710352080800c2188007900390801e8a1900342d4202c12a101e888045d41150480b128001441c0d80008805045510a40e03445540d8902ea08020300103000c04003004000140c00103100341c01e01c42011143c42541c00403103014440014507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 74800289 1250 74799039 74799083
    0x2010f08060603161e0302090a1a040b09060c010c0207060306080303040c0e0601021009030801052b1203020c1b030705030a030f030b0f032a040c0518061213 69
    0x201d541c01e900c00c40c104001180500940030480e180a880e0401c0d000b5070410b01064030044c5130010032000066408502840c2c14034200080d10300a04005540600c901407182d00a00d181c440c0b40140c094600c0f00140e419170548a070011201440c20038002000b1a8254401c025107490f014802d2000290610781d000c0741400000c42204d000790390015041c07420501e020100c0ca1000c2000305150f05501805004990f000424012040c0d058460380d242026581881d0400040c40c01c0b080590746040424143c040340c0c566440e1854803071a800000740c08105101d800110040c1c03103105900b0b04c0501403842c0c00203070380d01c02c0d0042c04980c810403001d607201c403070b2902c081c0340c0c0d54442e0100c0940003806ea0b403403690b4403e000b0b502085a8100150400d242807031104007091070060030703010881d82e00da0100c54403171412803038400100041504980501207409540001019401061040184106007140341c3d1000ea03281c0e0112000220031000810440c03601120701c14000c19850004d50700580c0d903071341e016062451 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 74801539 1250 74800289 74800291
    0x40813051914220e070503030301060512010e06060a03090804090204030b10081203041b0f0b030a0f0204060c021e21060603150f0601120e01020711061e13030803011202010f08 77
    0x41d0020390120948540f501c80b000d801540a21540b901803000d0100b10703034809000a6001e02042e44629503500710500204191000503405801d0070703d02d44c0b080c02400d81c1c51000310390b1210694903001c1444041d6081013459440303664481d0b507980d440051f0000030003402c202e0170361080c03810800705800325650300c2040c0d40ba50b2a802d175800c0c090b07404000090020b40d1032494035a1415404030400031082d151601404c00071540d0f0001d0800e41004820803c12050780e029940c84c05946000940c1480d14118001e4400700000500078800c410314488034011900316200d001959400800070614400d640008010342c800c19134210210f40a0000040d50900f40060369401c1c015048481e401103a071a400c658003501000f40c501410081303440c281c032028205034064030a54440000c00140d5808107440c000380039a180341e440a005d4a002c3c0f1104403000c0b40c1c0502228070038218000359035030b03400f171400301820001c8580009108820100010072160000a03103000e495100f82c0f00c1c8010a03007407040603519050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 74802789 1250 74801539 74801569
    0x4031808070812120103140102120f0603160605041a070c0603020909100b07060203041103070602160905100b07020a080303010b0d14040b01050f04150810060608070206040813051914 80
    0x1300401003002130a0026021303c034110300c0000505013241107402c141e11000564000c0c4040c1c100100307101040c43c051096440580880c200c84012916106001c0c00328046d40c85080c91500c1c01c03000c0e40300e50b000040111a821940035482c13242d026150200a4002e40006c01480c4c010729940f40020b480c2105074400809850352a101d071400c02c0e040350341d40c1010394002001100d100203004114a0282c90030040b47c1c02400d002d8001c1c1c85c0f5448081961810b1162682c03142103a1411320040c0151900c01030701240c01d44145d5681113958121900101e008400298041001403000100000b00ca0303010702c01900e50303040c1201d010f00c443d003403889088800304003d03200038040c2c50382800100310a1a104c1c04030784405202810104020106054810800f038050f0300a01107034025003000a0000018824040540480c1c00d00b0105401c0c107420007540c0d0480200f005022010001701d400856148001410003030400a100704d00130b0494001d0612000601e00ca0001c3d03219071400172101c00d1070880da000b400f0316 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 74804039 1250 74802789 74802817
    0x60a0609060501080124091e05011202180907020a02060a080106090b0a02150402010e030d0c05010b0607030f0e03030d0e011509050c090d0c080312090607021f0504031808070812 78
    0x100c510507040364260b08004040180a24800c0019908c4140c07188101c004440410481400d884c0c4400075081c42112403420703502610400510744944c040c1c0445160518080e0381c100f0391070303452441c140e10340520502c0180d0b003d81c001c1590003a507544213400505896255403110350441d030790080e11065011f0410510301580020050941c40e0002502e43c503445401450321449180600000c0f038104075080240d44001805012881e041c030009008030204070009803202e42c94124252002400340b0340034583c00b0700f00030f0b0f82e40590170f05503002c00540f0840303451201c0070004040d114104c207000301580c5100c200100f01e03034540050204c80318400d080c450148560a0352508840c0e508101c4a104100c10881c0c42c1586c0500202c0d80308000c01c0500b820403046c007040034030350030020062850400300800c81e0301158070070340c0715440240c0340d410224214900848086100d032160702d001e849d030a00c800040c0034003001e1000d0004030310b00c0c0045d506048078429400e8a10307070100d0310001c01180c400d00039614504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 74805289 1250 74804039 74804069
    0x19060e0c0706020a0c02040e03070203070f031e030201090203010c09030b060301060305030a0e010c050304090b090a050103020109180b030d0801170f0613141609060e1611070503060a06090605010801 87
    0x8a802e81e002084e01901d1854465080d81d220303800242140c0e0344648409003503002261170800c5080806c020f20240c442c29000d00142842d40d946c0b140003444038a484451f4502d000318a03002c050003504111001d0b507004000b4407001114a400605141040c8802e0f40d4583d001408900e850a041c8200c1e000d40c1d40020195142000e5901d0660380d4000d000740e458104981c803454100850800d0014001034024103001151520b000010402511005071468003d240fa0074010030050382c100c503281040f01d81008090305100702402591000f40388280301944c05028145094250300e0744206000e043c0c520000c1e00d400c0407151020740c1d80c0c1e00c031070700355680145034000740115180721a408040c11100e449213071541b052600302e000c0706013003000c220003d4400b20300709041070040c0212806108082c010003250300d905494410301508009483c003000800380240445c55070f085000512600029280142c11540c50341400302d4540003e100794400d03401380914200d008140c40d0700c14403405041f5620741003c1031072 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 74806539 1250 74805289 74805293
    0xc120308060f01050c0609010e010c0203120106120b040f05040302060c040e0402060d0e030423120c0405190603110406120206072a0602010e060702121204050c0919060e0c07 76
    0x541003842c54142c1446010312811003d2142004254810750041c000802c48101c43d0b003809082d1448144210300b176400921603262810072a41415045400d5450328411511400001d10001e11414007800d401a00f41640c401468134603401460246101e42e0171141107a41e485400360107405140140f42401e2502070105d0058680364000d818500d010520010301140040310907031460f401070b408602d000c40c00c9102d0046040310010010090f000a0b102c15100b0340c4074508403920b80e889148514461a916000b140d8966501e40e11000c0500010008020850322401c025011510f540415031060342080300100328070407820820500194081c04150905c0026030705e89202500706e402000b040900510a024a08080c1a0680040c20f01d078000252031036051386801d0524000504050956001401c10110004082c046600382841c90079060f903107840d149410b90401000c901f0f4160320501c0e5105000050180c032942d170011969010007040310b2603641640300c0100c2803c9a000300d10308400c1c4242d40c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 74807789 1250 74806539 74806549
    0x30206071106070525060909020307140310050405160c170705010c091e050f040c03020408060403050c07210305160b0405010c02071208070f03020321040c12030806 72
    0x1061486540c841048645280120b01550403920080d511076106402030a4040c10001804040c603503900303800c0300d02c03d04006010b004042e492080906440d0300000180c00c0c144906030002034540142019907a03030624102601076181e036801500e106600e00030105140340000c9451000c0c660709921030007961f100c951600800308849a254125010080100c400001c10030720601c58550001e03194201518100300d06074964031041841d182c54038440c00d03c140142e0b0b407001001c1e1a40b02040f50040380302c0c00d000000710007a020300ea00541c05441090103002c2013680020140022009140c100e40328507540703104180e0043c4c490450110351021031052000403d103ea802081241404200d43c1c00c00e00042d960b0182e0700f80c089034141d590341d5494480e80710160381408003c00600d210b08000c3e2540794151a484818032428034018003540203000c00c601018001c1c415615a680a4a903003400e2002c19200c6800103041114100c569000c40c1201180d4414514200c460140c0c0503a10500b00b0355903541442 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 74809039 1250 74807789 74807797
    0x5060c07150e060a0b060306031b04020403080c06010302040c0212041208071a070216030203030d05070e06040801020702150a080402040911030f070806060a0e0a0f0f020c0d0215060604030206 84
    0x1841d440c072501801c0035925040d010740030601c0c12a030010141d034a0a80c0d181011a21040d01107807141c002002440003da40000750b01d801082d01c8207082d186000d20800050003489190310050110700046060301d501c03400410154103c900a440c144200c424151040762600c0140c6502c1050110500c8144030114151680d04c9400707204045892a003201510380003101241c1c0841c00000c51003440800c00c04550500c50101140d14940c0035810207411030b400242c99002e6a0f01c100d1485070f65600052110784aa00304c1c406a104c090107080da5917403181c400501035841814241d01941900034404641d03ca65802c0b5004c210151350361152a031519404c00000e408251002c2d074105030070023000f0845507001e00591182c010f50300c0050420a19042c260b07420600c004150358420802400e0812846039220740b041e030701c003070104030000f5040303c5170203000010101e00d45d002c04118408524404213070800140703940010880d400712900c000d0350300c0e518a80a04204d41b5281c00110501c010001410020068 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 74810289 1250 74809039 74809043
    0x20a0509011805130c030f02120f03160f02100203071a0f06040911040203010902130b040e2703070b15120304090b0d02090901090b070c03020a14100501030b1602030705060c07 77
    0x10072880a111748507040c810442d40c00540d4405103494114085140c0003041d20400c44010001c1e155040e0414101030321ba0248003000c10a075103e818100040180000c0203100103503005007280f15000412030700a41e26000514101e031101000d80c40800d2802d00403407041c3c403446400090244599510040c80040c0c1400d00c0125203500d00020011007036580c0340041d60207807580c4000140c68849981d40c0c4261100c290f03000b42c0d910041007100344014100c00c655540c0c0400d500445002000c4884400c01007040ba11000d95960b01010800c082080544c601d00f500400d19840b000d0076251600301008501c0b241d0784820226a0f10400c0204000c1c2003640000814034401032048803605540d401003102d5250840e45040f550359142240c034100301058424680040d05407400400049050b60301035500d11882c000a4080c040902c00c0c900218020030030464a854440014011941d480c585006142c3c016517400d0554140380c864003070803501c004183c0d02c8031904040144400d86900001e4400f0340d00100741 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 74811539 1250 74810289 74810311
    0xe07080103051c1e050307090902040302090403050c1507030f0b03011404031206050a0807030302211e090d0b0601020609030a0909020a0318050c030d0c1208060301180f020a0509011805 81
    0x10490341501351034440c141c0c070001074560350756902d40f090f4003d20704100c0750003240c1d07054070510007440540c40344000d641e03000c0c0d41030070314070f43d14200340d501a441e1a48606080103030107217007400c02c402c45615421554070000580414040400c24001b014243c44120401000388044c500c00100403a104421050301840e075501c0020710640c58001003400581c03075030409540c55010032010010141d042112800203003549640444449610020b81d04a105070aa180004140c240c1400e800c0c0140700200c076003030754005107403000600903442c240c40341c12401c84045001d401001d0019a40d42c0303000c000c0769072104065035031150aa0038106480c1c001d4005111075070400d9541c0c0c00085214079805803491205000d80f00a061200601c1e04251074044a410004100300265101e440002c03003045a05014190b10704007990035583c2d50020a0052120407002908181c1598600307051048524032080c41070700a641c24181d03592030703500b071040c0171000307115141004184100d01140b8000c1039001580040512803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 74812789 1250 74811539 74811557
    0xd05030901030c030b0a06020c031005010e19060b2110050d0209040c080303040302030403121805040f0f021602150307020c01230f03180a020f0f0103060f08070e07080103051c 77
    0x40441c0d60801c1c07c2c1c03c0070b005039025940c40500740c0380c01c2040301e0409401c90810303c465070400e40740e0410818042c0c404043c1809031030045a01a969401c8800608550481c4c3d41d19401900c2808920800d2004200200f4400c0404146a54031004040d41a148003900d03030441292640c1c02d006a4160040003a0f4109800010114a00601f0f10043d8016402640107545071400c1d401c10404c1a4560002e0f00b041c0300314882c00301401f2450030071010032500d00315000240022410102000f8180855042c0180d520009245c03440c20807451816481a0007a26020403000c01c11080d00352520069501401580c00149115400e62081800d15605265203140c01002c0c02035214003a40f5811012203400696004420003c105c075a1035072030f002e00d01d0f44030010496460585c0104203121400020240540541c42c040c000c01e034026005200148000c61a2015907980c4070103850b255a00c034025043c2c245c0381e0300c020900c500e22401d1403d050b260484040c04040c86502c45a00000301c000c6400d07424040590307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 74814039 1250 74812789 74812811
    0xc26010501200f07060c1401090308070c05030c0f07060905010206040c0905071b11090c030417090307050604080f0607300f05090d0f020106080c060306040b0a0303030f06050d05030901030c03 84
    0x4c0603804c020035143e04e501d9402203991404d00102c01884200c6115685800408004a540204029080001c605281002a8050600a045210301d07541c48105124050441341180d10000d00003003203814958400441c20745130380049846001c1500c014101e006003d20500181071306503c42c41c0c00000c1418051089045001041d150301e689042c00d80703110851a4044015003030980300680e014143e041101d14614041c3d4816003d80da1101100303010000106005000f900d08028441c0509802028152100d0369400d1103541c495018001c070004c2d004c0e200220b075039a401008440700c41040101404150b00082c1891100c0d10194640c2c0181d0b0361b122507242c8140b113071502c20180202000300240120168003000600500482c1846404581c5440710403c5540c070301042ca607040e840100c40403a070f40e4a811002a01800b440046240d01c408180000001c250b0542e00951054681160510200359200c0070403003c0b00c01c039030001e4115041008012120340c07080d07004504800050400140c0d040700701d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 74815289 1250 74814039 74814043
    0xb030c031006030b100308071121060a0f0e030706090201050915070201020f0309010c031b05030c1506010212030a05040606030c090207140615220c26010501200f 71
    0x1903100c9201d180c0da00001c1c000c0c0441605107590211200c82c81720807035440c540d10f450441c8145c2e00060a08a41c04550112540c0c0303000c3d0004800101c03021907004d0080103410705032190b0041e00c04180c03491a15180001b21a000e0183d03010071030302d0002071400c280e45c83c0c0b03070500070b005102d00490401a0800c007044d940d5540001004c00e00a43c50b14840e2500410b2002a2411455a080701c1d81030b4010b00a40510341c4e0b01154000c48035505180a0b070400b0180e407100d460183c0c100c0001032a600021902e079410903c0001e400f82c0140d9440005400c035104d1000681c3c8902c0c0d0496071140300302080001030352945068001c1074101d8400c00340010340ca9600d403162100c0007080d4000c41c0045800107a800144401402d03541e05040311500a4100c508100108994190041008134082c0e800751070301c0c6502c10f86000d012101030b0304c4090b0602a511a100c00181160301070f00100c44c82c004440840c0c03030000210003410703043c0e84040c2c44a841c20860800310070000d41243c4081c0850b80b041c402400404482 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 74816539 1250 74815289 74815303
    0x4050603071e0c1509020607050312090717151515032a030109090f0501050708010333051909080a0318170702060c060f06010906050406020a060b030c03 67
    0x18aa0316001e01440101c007244268580b8107001e003c100c030460005010031044206656419031315080010b05002920200d4054001c2c4038014003903010100c1d000d001c8107003018120b44500b5000040c0c90600c1d84400c03040200007140001c08026620001c2e02004550040c440c4a400400030754030355007060b00800000c2e52818030707000c5030b07034480d031011082c0456491580c4400c120356074001c0ea584807001c207031071203800030b80014803501100326141e00805080c000d50070f881c5100aa0000004e114a240050001d45000020302c0100d0310004070402a0042c0c0540215143c070b051103070010f03240c09034150040ca402500000c0c05400c512034a600022840f80c0d8103100f45c940740d600c03d0100c15114050f0100c00390454006007400c0c0005003208032114005100f5803c4254889150078906848041e1b078000710742d10b8081d810080106124841c240303e00f04c81040304d028483c030300990714141000e444040848a60107907124030405a40241c035614002403013604220490180036007121000c00b2a040020300e0409 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 74817789 1250 74816539 74816551
    0x120f0e0a050106170703050c04020703030b060f040e060402090f04090201210b03010c03060602060c070804030204050109050a0f0c0c0f0614010f14061e1303080c010c1b050606060a0504050603 84
    0x2541e07440400c481c1548400f04c0002501d000c0c050500c00c0d01d0350315503e0300e444410001d1b52045a00094842c00c160180d0300800300e040c07015003050342760110700c10369001c2c0703031320901486c946c0b145204009025441d10b40201d502d0014094540400d010b00182484003030451340c4802c9060041292902007032a91000c041800c05d1500400880c0001c54001490700311100f0741e0402c0d040600340b00c0140b01c1e41c1d40000c2c0c4190008543c0c640b5985d04d02150810715410300803608001d5000d030404000007a1313550340742c01480c025018400b00f0054000400102d0085401c2228a480860203c241003004151034684480341e09010340f00104011040b44180f11001409030040455180c00340780502541c80c040110003c0d003002550014034200c000e8a138500c910098024454003039000044111440700e00c4081840250740c0072030455101c0395003031011070103018070345080340c001401c3c1820507007a0310307803501c2c10000c0903009005004540c0360b0320240080d691250302c404d414080204000101500e4000045103d00303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 74819039 1250 74817789 74817791
    0x209010c1524260d0f05070606120302060f040b0105041107060e0106080601090207150c020c1005180406050603070807050c1501050a14010806061e04030f060b0d03120f0e0a0501 78
    0x14200100751800b072406003201d075451114006500d1400c01c0000b05034003150b5a6003405c006003107407170700b00315043c0c46000c1c4020002030400c0303000509840f0030a15110140e02c03e80170348060307903120640460002001c84014201421413401040581010f9201075420301d514541d0318504480b58481e20143d1342144203a2889030b6481900b045030100c144840740c0944014081940340842d1358540c0e07260071203440504001070741e0f114403825080b0b0017080060302d043c00203030000c1070311200d40f8000352194101403100784080046d01901f60b514505841240c1c04d0320801000c203420364440d40c0b01144da55400030719032414400100725550300c0d00c0c410441a158410119280030b20fa42c14441402540e010541c012202c11146c4030703c402c6e081ea00484125848203054540c142c8511603680b6506100c1c141101c41d4a034002d00140100601041100000309075014120501c4412408014002e00c03181c41038000c2c001a074900040240c0c070900d600045006a10080041140e00c094103419003411442c2200722a03076 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 74820145 1106 74819039 74819111
    0x60106180909050601050f04110409150f0b04050102010f020403030206060907140f0d0c050c06010e04170307051902060712200705070314010209010c15 67
    0xa00c26410107106007406418420f491354070a0003100c1c080c0491811350304050400d0302458002c0d0705040044c901d03152400358400010f0462030000b64400161010000710008410030035409440344d031640555413840c280002e03007195103141003c11181d0040c00f04101003034010506d00d60200c029581c036081582c0350402201c0d1001801c1c80c0c426060300c08984a221201c005025040030321044c5020455090700080680313041c0a100d0f82c0a05517400100184080740d10200c685070000c2c4a00305055058000c003140480641040f101803001403008180c85644008080859a840072107001800c5c050503e81c0000f004080c0320020090410b80b181070040803440780040400c108100d2603401900e8810324030749540c4802941c401982c0c1d00001079000d20440a040c82141c60b2810141c44160712102e0720354a000c0080c80d0145604400d9507610009152042040d0021264918a00201c01d41d = true := by decide +kernel

theorem cover : BRFrame.Cov 74640289 74820145 := by
  have h0 := BRFrame.cov_init 74640289
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 74640289 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 74640289 ≤ n) (h2 : n < 74820145) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
