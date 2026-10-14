-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:33:42.70099+00:00
-- url     : https://prove2.me/submissions/0add7396-6d6d-4f28-809c-0d9d274fbffc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 551079136 ≤ n < 551258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 551080386 1250 551079136 551079143
    0x31209031603081312110d18061b0f08030a0b1f30090c050618010e210a12030b0906042307030b0406050a0608131502070b09160501020d110a 62
    0x6404c2900c5c201940002841050341840095440030840490b0555084041d00d002c403016070322400c024840f00c1d210703003144407411041040d00e030810601500c6100300005c06205c15140341800000b0403282c51414000e03045070071003e841c460070072507043e4406220191310f0040d2500308910110307050580e84205135203c0c045072086024061008000c00c000d070040c031050408581044d00b603000000c69145c9001540d051003c2a0b032010f60b43c0c1d2044004540c110300c0703c6035090348084045104a444000409104014144c0b040100b00040440c2040404942c141202004160500003140c0903922001c64039130300003909460102d54601c0b10b01d02c000303420001130082800300044070704012410746c1c16005002003c0c4256403c2281030744a03030034030020001c03a02901d000314014001181d01d07403d40d03148003241580201c00f03204070644201741c41c0c010b90380301000035180102c4080500042c12030510900b410001c4c4181503d149600d40400030351201401d8a14405001050411140c0000284860700c0990784c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 551081636 1250 551080386 551080403
    0x1205190b07080603240a14040819020102040e010b0a020609240402060c0a0b010f0e0f01031101020708070b1c060f0b0c10050117150f011401140c0312090316030813 72
    0x4503800720100c80c0200721b422800c01c074141400440b00300c0c0301c200c14600580c0c000071403902c3d1070b104903203024108160040f02c0c01150f60070007002400d1010440f206001c3c0107074021890391112000802071030140c0180010f01036070007143c4019200c00b500d2091800d020704400781d9010503901e900001d01c8a00400258103818017465569504110890034240c5c1030321100d0161000050300c074618014020f100f00e40150035400640010b0021440c01000b041813200144100c400c666111911a030401806074403100151001180c00c03c610340100c01c45120515060b01c04210042c540401c1c9610000f5902c1094100e150010710442840c106004040d10070415000901c11540e4030011607541e000750020389145070203003e1440c242c44200b03100c06400781105d50040c850756401c2000c65040d800030781c20002e041c0045a00903484200090025191070001c41c806162150440c48031b6407082c01c0010118155500100300c010040500841c0b80c106403500351802405e107039a0102980001c8100c904060300c00301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 551082886 1250 551081636 551081683
    0x80d0f051c1407020a050c13150305030c0f0102091e271b0a0f03240e070801050604060215180f07060e0103020c0604080a090f1205190b07080603 64
    0x20603a4200040b04100828803952643e29054102e03152108641d004007a5001803a006005141c61100b640303280304400c0703000405051000c02081c1000f09640115910740001ca01200e58400a20070582c00750b002d0f00c005d5203030001c03080c00a1741042d141982607a490394681a81c0d4200e44840c0e480603c0600914000002c10840c640200201c3d80c044a03460110202c504212003c0045075055848003c01b80c0c50b00c90750303050800c009401401001c3c0a441e00000d0f849411401c0004018600005001c0c000c9407404034244001c00910f5400141c001074042c42041004001316a1300056002c02056105c00c0d16010340c560384d4403003890356252004000584280300c20b10464810100b000422111070f03071a10700101c4056030040d000e0b030044510f0000c0c903411540c0001c0118191000500d030f408150302d402035506880701c4401d0031402c020340010000101580a8104004040224140b4130034003903031800186406650350200c2d1305c0020119400c10426401095458804001900340c2080150ba601e00d080f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 551084136 1250 551082886 551082937
    0x30203130303170c0906090907111b0307050a122004110c0d1b020906190303090303080703020f1b011b02032a030f0f0c06010608010e10080d0f05 64
    0x40c4205400009070002100440d90003800e1208417441d041d8003600c0507041c170550404220401c54003d00000520600389680c94440605000a5140c0c0f130645940b010241140c9007410b14000150300b22a00030a0b260400340300220014180d420880c3e40300303140310040701203a10442c00342e50070f41c4001c90f0002d051588200030848840c01401c002c5628100702c41c8034240034407080b01c3c076014503403403030703040220800213032015081450701c09900a070040c107d1350441041504d41c3d002e0101c02d51054001030345402007882015485a07110b078000c1031900e0194188511007617003c0e00c030f00c074030100c2c0300b803010a001d00c2c401412003c1d045105481d03110914038070710401c140f201a4aa03407048000f808004e90728016200844440070b810940403448400460a201411a41064662102d00c58100d803880a001c65a0410f5007080041c0c003074213071aa01d082c61940b40000701c414044010302110030b5421412014402e4030000960b04406a00c2132509035070303030400d0400070781d40c2d40f0948252030110032440769200b007607 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 551085386 1250 551084136 551084147
    0x706060503031c0e010c050d0b01260f0c0f030a05040230010f0e030f0a1715040b010c030c0308070315140f01020303040c030615081e0d09050306040f030203130303 72
    0x1803c0c6500401d01808001410aa00700c40010b07001002080003031284040300002c0d54480f5810745010f0404110001381540d2044020241c010000210003d00b4208140d1140303142d009500001e003103642c1410520700d094044464040100008069aa20303800941590303900301c807201d041040d510f40c0344003003440115103102c1038108031100c442541c200728020041c5c561501c5110245985a0080d60900100540044d00b81e80941e003c40200f04182c0c2040e003154000e4512980680d030510b440410280e50a020700c016a604034800c64180894181e414000c00e4101d600042460f901d85402041987d40500940043c50348151034007401810000100b40d2424402566480180032200000c441c80c0c0c80004a960744070031035004180401b00002080000c446400c640001d2281c1c0480b00040b80e210b03c0568030b8464503940c2584094504810310058020611159aa00b5590716007140d420b0b0071306000c41e17075400000c1d10003488890f00005403004c0c14400d205641d003d044107140c3d0801c80d60340c0e0600928 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 551086636 1250 551085386 551085427
    0xa0312050613140a1a0a1e03212a02101e081f06170709150201050a1109030706141201120b01060509150a2102120907060c08070606050303 61
    0x11514100030340081c1000030040d0b4210100041914101c2400c0c000c0700c804905d601c070340034503400c3c090301f0740400010100b0010015040080320080303020440e03c01c009040c5032042c83c1c50b210015401500c4e01100d050381041d2804a41c0542c0d01c006081c0035441d00302c882091180001b4241e0b0540e0400310042ea9011030501c0c0526a10580442000d600f6248000c1c51201c92040d000440c04051007035056411444449900000d9030030709190311a034940e1a001c007400005070740710050f596181084140396092058000c0b80d050ba0400d14104022000840e030341e5121030050b9828820302243c841c4600e5418000c49442c68569100c04482d541c0d40e40580c0c18019440d9030445501a20f44004103030b0130310450544080034002090f5401f40c01e900c0b00c0c03031161035208241c070004100c6070417040351068a202c40c0c031001c00c81e004800181d940308980603002c40500c02800032002c070b81200b80d00700845a07009401a1302c1c80d4024203516079810551400d24000e100365800f40c4e402d408003081401e1640145803c012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 551087886 1250 551086636 551086651
    0x60c0703030e0f091602030c0d0509011d01080604090618060203090607180e0705072f03010218010e060d060e04140a030807141b0a11030a031205061314 67
    0x5102c031160010800c400000030500c036088400d440004152181d94420349074810014010350f494103076601030480c100140c4400000c0856000905862a540d00030b480012190f1a15940d98950301c42e100001c00007003001c1e141d948160b0b280c035003000034041039a110201c44035082c5003038408041c842c030340400a0f40081360a040703d4001c410000f46058002d10074101511a030100703281c02a41071400d580480b040c042e05144c00c101d402d00c400f03070024040c921100082003100030450101c482641912090104215070a4041d0340140582c030703007042c51800902c1c4085800d0801950601c20301c1c011810764010441e035503514901b001c100142c3d001c00c0344501c500540c0a094070300640a852414207585e080f00383c0004000a20780700001e000e1921641d0080c1803805030143d04c1d031902000036015001d0308030f40c600211040d0030130103204040140001c801385180702d095010703156400783c1d514054024040b0410300031005071117400007241d0b941c03155030380520100c0e0100100710b4401a40d1001d0f80800044414a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 551089136 1250 551087886 551087897
    0x120105010e1807030609060b1314010b07081c09050a0b0403080f15040e010612240506030a06020c070b1803072102010c06090b160f0302030c1207020c060c070303 71
    0x250312451168020381494a022004003103ea02e103a68034001412940c034107907011035860102c0c1d00d041c2d40743d00700c0e02240d841e80d0b0710103e81d0702000c0009051140041c4d0110300c81d06010002d860000380194180e0320f0400b0b00d4a015082c0d51584684900949030241c2c3c01807442c00317144d001e40100301c85010501c0c0294000d07694440d20f941c034a0700c0ca01001c3c0702940c44002074441e410700307100540341580000c2d28101d400720000c0351a503951151a6180780d00403000f2110340e0500585191007100100800449601b4000e040c0024100b1002007501d8080461020317190540000365540304103400c000e000001d15851051030f40e94a11010f01c1100c919040c42c030107101c1e00841c400090f60b028814070448410f00c0c4801002045085640103461001c840c02c03040351415240c0c100c0c00080340a01c004944141c6030100c503091198540785005091070b6006030b107030381410b206100780104200510701313580038212482a40b45035a11005070a034540000d05004942c000d40018500c51010740c003007120000c40c0d2080c0c031003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 551090386 1250 551089136 551089141
    0xc07260d080708131e02040f0203010b1c0614090406240618080d0e030f0105011202030d02060106090e190606120b1816091d012310080c09120105010e 66
    0x4000c200d55180360044d10300c40303260b110f880e15440050041704440d0720041000844481c0c100185e402d030f030000da000c4d0700210004548048002020003040c1d2041803004c9081101d5030030b01c50b4460708110200070b100d0250380e00e080020308000169000c001008074402c03d501d0007600301511812402c03618080d000c001026101c44501144a1900401c1910101c06c080c01c5810511801120301c0b10f42101c603036503d4412089401000f4100f80304035070183c1300d030b1403081c1c00041c954010b16140c58111540722046504c0f00d401006283d9204e800481520036052110806071510b5629150a000782c1c2d9018071702c50700e003030800184103400441000c40440c0d410000e001e051924810042001600d5610800081c6d60f0800070306145402c1c1110440004582001e034049a1a481c00711024140080d140c540102408014004145042000401c4104e43e1400316906041c00380400c1440e03d5803c2003000f40310030000800c0d4944110001c0e00c10144010f8100f0610a0707060300414049c03d030a10980c0c4112014401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 551091636 1250 551090386 551090401
    0xf011407090608070e0105030c0409050a0204030219060801030b040201030209030d092d1e0305100e0114160305060109320d020315040c030602180a0501050c07260d080708 75
    0x82081c4110f0135031303c550300707140752010040d101540000c01404410200b08000305d032400942c4a81401480c81141c0140c40761b09510600985200b01141703504100c00d011010001c440d44085514152580030f81c2c1844140c82e0743c130058002c1e00404c000d03140c1c103015141c2d400840680c0402560120f424921406420b0400110713200d502004c10820700d0071038a84184248488202071000103071049441101240c2c0039525190b0702d04010b0b09503808103542e5160a00c120001509000c0c2c60814002101d2814060400400e41080c48400307007121018140c9a03000140d1707981c0901c0c4050000c0680220030442c62201d4a164404007080f100c100318003070a2240c1441c0582484641405650760180c010018051030040441082d01c1c024012280c171074110310084000341c80b03030001e0520007420007180b5096001590801c41085036582040d0b04010f014003c58070103200c00140c3c0000c450035a00b201601580724202a198180050241c102d544107400201027041d0780440018860000d6558881d07850b120280c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 551092886 1250 551091636 551091647
    0x70602040f03050c1f231b100c090e0601031503051e1b01020307030810051c0b060103050c03220816020907020f121b0a060b0a05010806090103030804050f0114070906 73
    0xc00000010f940700c0074220004e4100070040740726170700d07221b1032908103001000e0a481d411700c9481400500d4020030401c214a40d0340c0c0c058181c0350512400c150307008a08041c460954010001c00a50425480d40130344400c00503914844c0780a141c200061700e590b000c030740c26043c0c240c407404107100000b841408082a00b04412145110310b0030700590142d80b40c06d49640f4211210840030304115960b5904501c0007071590b0b142e905c0110007100c03041e411030400d510ba082c29090842c0c01000641031500742410407840c1280c1c0c20072607512104031000002c00d06582d440720070305070200c1800208840700010355030402c59400135010712890320845138240b25666100d0304a0b21030341200500036441c0d010a140421f5800c8050240c004d250002c0442107000b501441c14a1074880c11100a032006076845100c0949810b0260722000038000c01c0c20501d1460602c0004910b079a04144006404c01031a00041010018280602e5610841140c02400700c0100c1c40f502c0c50340c0c0e40050318201c0102d0f014007070000f00b10f070044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 551094136 1250 551092886 551092939
    0x6150c030d020c030d0903020717010b01090303050d0204050a120501060b070b0708040311160611030406050403110102010b0901090b130b13090201091a0c100b060d02070602040f03050c 81
    0x110003650038019a1001400603401184818a040c0818041a46400f610340324410310180282e00916150f0b10300300940c0001195600314010380d90402000c40c02c240d8004040b20f080703951500c0c1040e074507407103610290000d00442d08890b5220034a030000003102044803280c8440c080c00b0b03000801001c1d6071002208054450218010001c0030084006641c29001ba4003080e131250280c00c0046000844030030290401140d0400302c11403010700d410034002260b0003000701c45024440707001985010b00700344018142d070140d44401042705840444480c02030b4804e40015180da0406860310240d541c4492044010303094905003d4042e44822950190480c000c1c080c803c0c0142c0050003003000c00c03d1109107500900150700c020390500401c1d520018520b4103511418035070f644100406500e810b01110140e003012100c44103000982e0515280c02090754907241115480082400c0040c1e4803d801e00e0410083e0180360301c40a02c0000c0c0c0900041800400b0031000c0003907404441c80010071082500e45000950358 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 551095386 1250 551094136 551094157
    0x70b2d160807050106031515080133080d0923011d03010b03060717090a0c06080916061d01030e06070e1309051c170a020702060706090305030615 64
    0x90302000c602081d8803070000e200c41401400003044054990301c0300a540300951409030049039850088a82071036150815801030003481e0001c2c080c00042030f8030b8014400325a826083c41644104844108551386070001c03008207000c10503916075a070500c80c09811000380d445030b0703c001e80d0710506200d0420f40d103164610b0b4140c0c058540071095182d00c0310007c00e0003040541160150b50710524802556070800806100704074641c0c0c1d6011285840c18443c078085405041c0c09540e911000c241c6000903100c5c0a01015500d0a00d000341d065079400101e076141292131200d100400d946d00d400440c4190344440400d18105107075054124a211410046080320381c040c0c404202a0410303c08542071520a04417410b100c2d034007c128020b0050b0440b40070003180d40e002011102c42c0d00c1078050941c01540007843d07d4440e0300604000c0301d011000c91180ca07516400406040e003159000030b0701c0c4c00f15074500c02550341e00c64001c030f01080405c4c1039213405440756005032403140c070030021400d43c4c0785040f200008403148000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 551096636 1250 551095386 551095417
    0x910020f1501150507080c06010b0408070b16020402030912040815090307031e0c0206030a0c03180f031b05030706050f0109180b060103110f0706050a062105070b2d 72
    0x14045044130b140e0081c800840303090390300304003079200b010080100c80d004e402c60f280320f44d0b82d907842e00c03651510f07181c810703840b013840074000340500071321500c4180b00c0940080e0182c40150366a0b4801ca00d40d0308002100f44280c080c15008600480c070202c0008a46294941d070065840303450b150003c64550302c1c0160702c0700070000b0b1000141403c510b2020710100b003000c500c0d4100740c0507020060740084c007150400c0f034104500c0ba43d25100b11081e5945401030114900320f40607071142140c065207528500300c800480207028041c90142158600921041c860810790b0414240d0b03885051a02e4580050801900c407d545143c1d40300000c202c0303420610a02c124603404107400314494045940d2034406190081c251414141c1e06c072261001441944010a00c982e00380344400d50361611403820204480001d0501c1030003600d403034170901c88610540e003500b22a10b142000b89455491701d18040d4075007020364222004050020602c14809191207460f01c4441e00a40464260031441c0300d82c60046010b400307604507400d00b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 551097886 1250 551096636 551096669
    0x103050f0103022116031b050103020906030c0f040306090317010512100b120703030809070b07020a03033605120604080a050703030e1f0f060e01051003020910020f1501 74
    0x41c1d41c1c00c11300b405850018141e480140c0c1d21102c240e0010100d600a0b0740740105035480c80c202d40104180c900240409007421424140c2501c003140c564000105134000314100002c5402c451040d42003590010369000101740150815441c0062100c5c01c010a60010b0040c0c400003c22300f4035150f0302140000c0741d14001411003c2c03448203844064802501101e070400c00c244802c1c00c62840901442c409140a5240c030741702030426070841c1e40780038180d034401da644801c03e0100000695810750948112605813400404026540c00710308480c5000703402000f1502c0a12401440700080e5030a520201e0300f0442e440c0220700c280c2c40a854640d40c0c12100240b80c003108100246c0c80901a50140034801c0c080d00d00001d8241d4910031031858410f100f400c8104005100c2625004034209000f291302c100c218032000c2c031030b161910001d2200c118042c003415100d2502400d9002d806c1d0b200ba416652900801060b160448204071806510b800408a140103180070312a403603081d04610320b40701812140205071203e11131 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 551099136 1250 551097886 551097919
    0xd020304060914070537030b010303110105060102030d09020301020d1b02070503061006110709020d0626100b04110d050915010e150a1d06130608070506181203090103050f010302 78
    0x801c0d41132802001d030009000c020403180101300034100690302c500700100c2d23554154207028040c1603007039100c44007a07030424081000599011007030b5035155410301004914a081480028060700032410300305601d52600c4201306c030225088010030400020364090302c6a142d01c0d0010b068641201b101c400c11194040001004107511074814000b0302020003040d601c601d91602c40d6641a03a001004600200c1c0d00c4d0703502486000510300c409520084c40a10f001e1100c03141e01c100c0d94071007982c1c50040d09110b40e5460568203940f11504185034014400d00d11b1691120004503040003800240c5507040c1611074a021488004e80b402d4045043e00c0801c101481e4594817868240d8194103103c04490f082202c903035000655680c1c0000d11100c03010b0320111803820340380681c140310180c0720b0150301260f03070390503c2010080070030f001c40d80c0300540d03c05945080e80d4213200e4040c09001e0101310f41050700700c221000c2040310380e040031001e058041c0e0309070707000c0c051a141c1c40082e110001c802c0c000a0752201d14100f1010b02c9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 551100386 1250 551099136 551099179
    0xe2d010207050a21080315030d0503090d23040612180b0417071a0f0f150d050f0d0c1103010902011d010e150a140f0304080f0d0203040609140705 64
    0xc502041d80c020256020030354910745550026500a5181002402564008d250502c00125468030b11314290341145050a600e0342c0d5200702c0800c400501c84140c01821401030096501433880d031950004585d6190f03228002040e07440427221200c040c500d00a95168403030108400c0c0c00016401208921454030341c1e86a840359100b401c1c011a20b0110204a40000070f180c1012803c400400f0101264603407600d04414850303003000070030544200f030740801000881c0441c140200720b06402a070f10056a040c0500d001d0f4500414024502d51512074503c004500d207034886040074400703100c1d010b4204112400018103003603400c03040b03009000c5a500441c02a031506800101c01e8003200501d440800e146070703c0c01285285985188820320703000002205110160040c10b074400b89108061014a042c1c43c10380c0d400d449000192005200c11000138105180700c0303298007940d20122100c00110f5990400d0f2a00d200202003510084440034072588040c01400d4022030b02c041200c5005d04580709070410700c0300c4c100c02d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 551101636 1250 551100386 551100419
    0x8070507021503060f0f0102070603090c051f020d0e180a1b09060f08011a030603030409061206111c020d1517060112030e010f0e2d010207050a 63
    0x1006424803103680540d540c6005a101d411035212060b50380d0030001c05000e0400b003c01800c85c0100030004030301d078169900103001d204036009440c00003040c500c28a00103019541540c000d40e8010300180401071402d001200c03c0c103203400d06e81c00b100d00c55070b1500c00550750281c400010b0307035000000169a43d094030207108000c0d40451400000100010b812110805200c9003100f200c0019a81e07610a0000a4020445410086450a00e402ea42d85000785494521002c40d502242e4030304c3c0400429034503281001560007409103403100703010720b5440700ac0410451009800644a203424803120b4503010884104581c0b00c610b00c0501d503807406035a896100081e50250b83c428128550b40c41c0c00d0700b400c1009503280400b500f4610100092840c1d0034008c41c0c946081a001081000040d2946000182e0091026002e030002800c110301024060b84060fa0b0100e85072100c00d070041e050721040c80d241805592451180403182010903140808240126551107590181c0d03500505807040a00200040d10480711 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 551102886 1250 551101636 551101651
    0x9050f06060d08030411011209060c0206011e0306020d020f0307030504171c1a10030b04050109020406120c030f06060206060102120a0905040902060d110c010e060609040b09120f07031e020d08 84
    0x80c140c020740b048d20040720031003101580d0344d6030746407118a08203506001040c018031f04240c1c0c0d10728034411004001d00c0c4035405e110050442e40e0009000703101600b50b4054a021244c0f010358607032130346090b2901501500e030454048500e103403205080f0b9140b111480039145e4000d041c40074030b4280d6020740c07001401040744582604d40b0a03500c7c40038460680e03503040a00144c404540d40800c5400084050006450040e0404000c642c0144014042c540d48180341040e8096045c801040e191110300c030a400400000c20410b5002d41420f0000c500d01c1c1e000100f990041c032081e42203c4d0030b0400e240c0721000d1805489040c0000079012031040080b45810b400003108240003c000741c1c0340424410500c01165019982d040300280007044400c8921028811020310382d00d0070000d0f1105141110000302154030061000304247c40c48000f0441a020402c01030400278840750507259200b142031602c1c41d25030014001140021501d02c1300c4112280b4480700c004a140041d001041150000035042d41d20900041440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 551104136 1250 551102886 551102897
    0x8090904030c060203070f03061a0702060d06030c030b070f0c05071a22030c170d050304290613060b0417030c0d18081603020907020c0409050f06060d0803041101 71
    0x50b804039405100640c051002e90315a944112211513029080da02030390f002c5402241a8034014600c000342000310350405078102d55865491002c288144000c1c0707230540001e446425640008010442000c0506008007460303183d2404200607503004481d02800d429004205411949082006403400d52580e0139050007074511a06003941d04681488219440c12101288500a0000c00900c44250b0b48000076225103041c0c0030001c590805282ea555038107901103020424004005824800d4803e0003100d45a018440390380c4170403a0120002020b042541c1d0300744142901c0100d002d07800302131712491080720921480c490034280f1b030420050000c075044001a401d40400c10099202001c14004491800d605440e403070403a054401613208840140c0e00100d5071071340311650070748200d10300040034000c0384d5046802035215903851908038105a049190719070002d0030704400200f00640802c0150804034132004440b402c0d6110350401c4031440219202500303c21042001ca0080b0b80c9040b41c0d01c04018040c1004d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 551105386 1250 551104136 551104157
    0xd0f0201051c020c0d0f05070507050d0c05030d03090303051509011707170a12030204142110021809010e0406020d18030206090c060c0304060521010f080105090105040809090403 78
    0xb003090340d1164100e056203401214a504855810010381d0310b951006e403034228181203c4d03544465a0b90564081c4a105180d420120800c10a4460403480035100c0076007a645003151000000c0c000c2c1510b082c04401017418840021010a80408040340c00d41c0d0003004e003d0164a04820044841c1d411a00b000c40c900881501040c101418401d41021003085001003000f10601e0030700ca4060805a0702401c1014010042046203208000303610800c5082125800c2c201d0007059100902d40414401c1d0b4030a5006000422907142100c1d07000d03091075000c280b0720b0554140c8100401202007000d002e082016104034011030080342d150340c0a089003841079100003c0c00420100e8416007440d240c103003180164010010415154030500074905114010750b074240c103000854030382c0b507241e0103203000e80c80402401241c0c1183da2100030451246c140d2145000c9012542c44107102381051042d0700a4030310640c01c11012601e00401403007814411900320b42181c3c00d1880b540d00304400004090400c1c0d08008072b0510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 551106636 1250 551105386 551105437
    0x2040b0a03050f0a030215010e07111e0d031a0d080304080f03011220010918060924230f060c010c0509040b0603100303030b0319060b09060d0f020105 66
    0x1c2c0002c1c0f0311a900500000b1036903e0000c1ca1b01c07100756003010104030060010881501050340480c1c101c075590421501030b80b00005c2482c900f5071842e0401c0032162003403418801c1c40c400403032032003c801c0107070398180081014545168810040d00c624160010384840100c03000c20040005190803e22070441503182003848204c50510f40c100703811461a00e170b5030721020702c2080000042141d9240d40052180c4034000c0400000e00035010500c90900301000c0c5801c100c01c50041580310101822200d9010051b03d0714505c80e00540b14103c80e030f0100d48809900004c00c9200c5203001c88020301c40004240b255404100090024280c0180c0c01039400880912000d8040d4800307003d01da503800300c0e40e52401c2e114040c800802065420003c900c5000322001c10070b000c0ca070701c0700161002c140c1c2d8250501003104280707500403d242c90200c0701c41c002100480110314081240d55001480d030404200e03400c0c0c0482d1240001c125041d260303610010115400c0c0003200005500500180110040d885807a0542142c0b118 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 551107886 1250 551106636 551106643
    0xc05060714060106120f33030506010b0702210318010c0f030309110409080f18100503150105090102030d0b06090d11100822020a0302040c111c02030702040b0a0305 72
    0x8002c2e50104c1e04c24100b01064080d5440384a41360b0500786c80901505e01000c0380d00c007002680c40300041007400031000b4980d0b07424100024078001c55004c41220041e60f900e807104c1c003040d0480b500c100d00c1400c100c41805004900d840189a8500ba9030000e0f6182826210704403c44d0901c1c04501c605024217034807a0404100f8410318082194081e032004104050035250034403190510740412481649080701603000314010109a0f41c4100c0403c00c001c0d03543d1030350b9121b01141c0d41e4070013200703500503040400c003d0b41c00d0707000000d1400395080c0491801c154003140c006440c24010070503900c4c0140e000b407040101080721030700560200780014080515001501c40480c60140d6020800d95a404910009500314101480f00b00c41c4c40ca560700d880ba020f400e0140d458000d550118041020744411880030340c0655417241d000a0003117500410801003540000e20180c9054a0407003120724901501140c6002d03892420060003400806502551800680f03a08010040c9181c1c64065040a5010b502100040042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 551109136 1250 551107886 551107889
    0x9210b09060601030f020f0a0c021504080d030c020133090e0a0209060607082209020304060b01020c0118170115080c031902090f0601110d081605070c050607140601 72
    0x50024202034070b0100000350513a009020307402d049510401c001c81c038108030042a58814131130341c5851400070309140000394800c04c80480600140e140040c00080f1820700052035200c80c66180c6040c45003c3e12400c0070382c00c80300c902440300640070f0020808035200d180746000b801c0e00d0031482c0812001c0c43e01c2d602d002c001c50303010154a0010360300c1001a0800d5240c1112429441030381215a14a032080aa80b0001c06004246450b8040c40c1741d48140800101c00c6600503024010032101151645071030700b4240f001d085c400c40c3c0c4034054000c0c00b03511096035108650100d0800305200401c11042c0c501140e030084100c02d0012a044c070355941d4411014181d98070713840001801030000514244003940105401d040041c9802154510884510320058644c00e0207154040309012441413650307034100060703c50030154011510f10f8081c041200c540a40c100c1002c81c0101342d511317020340c4810040f990654071807299a0010f015491000c60803c83c0f403801300f0081001c02d2140403406000c030800c0c1205858008203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 551110386 1250 551109136 551109151
    0x70201110105090f1018020f0112050c090a0b090d15091b061713060b040204030b0f010906080f0a140a05060a020408010510032f060a0c120e0109210b 66
    0x5050401240100038221000b05c880404115038240e010382c58520000601000b802580062280703403141c0e0050102802480c4151024410340c0761000040c4880c1c4d2000d02c000384507590b44080424001620f0050350480703070000c0e100041008c960780301c803460018005c0191100315110b0070403a000841241c1c2410105098950809078142041c0f006401d040d80000c84020701000c0a00700842001b0640c1074440c140c1d0010400035000c080c0398045400b901c26a00080e02c0c9928803c18041c682040d880f810303048a00c4103d04220040e143c0b014251600c1100444065582c490320202003ca134000f000042e050190b0070880f0000d101da40d984905000003154035216155000c501007015507401e00807030703070f001c84140c0c1e40c61507c508599482401341035010b840340141c814820140f00c9010441d004503442c0d000181116203803d0b110030300420f440d200c00c004603176403202005900081c0c1e0048040b90038500e0140c5942d20000d0a1242116407805640c440185d1783c1180341000c0f011913954002c91b800341a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 551111636 1250 551110386 551110393
    0x10608070b03160804030f120204230901060503011a1305040e030304050c09240409140106030201031d120a031512140708030904020f090303220b1603030207020111010509 75
    0x91903084560b803c0d0100503e03d080c80315000402001a0f0b210b80ca440c140161410300306803207400034100030024051a008601c20341e242500443d690448541c038104040e00c12916a0300507a21480e040310207000c00e110308002c181010001782c40025a0718081d01d00c1c00302150b1242505e80da42c50006003507401c4222114a036800000500045c800700740900e00c0032400c2611090b0b10750810f00c2e141042c9020390795a42d80070700741c0c6007511107060b65a9040908259005202d0f82010742032042100e000f13005a00c01280420314024503141300001440f0390702814081140a003c00c404000b89603202d5038042e180340d070300b0160394048c0c81d000080b1443c000b0028025004203c880700c180f42c50925801344a4032000340f9254801e4008126040c4c3c00002c44005010503200581c40d203400046050803070144030f400a906000100e4141192081817004601c2c847c80203c1c021415940d41026080074483c1c127000e03a90213100f0108010209000760001d110191061524405408000400714212401074441c1c140313580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 551112886 1250 551111636 551111641
    0x3110d020d020306121c0302180307030b090c0d0f0803070c08040803070c050418020415030501051806071b1113050a05010302040b060a020a02100201150806042d0212010608070b03 79
    0xa00102220401d0340c417a0041216861005880402c4c0101000100c03c0580000e9000f00c49440a03000d2154550058100e50701c03d61686001a200c3c581151003104a00c80c1e880388041c9403030318070081c330011a00f0280c0782460040540f10392580c0e80c0028500c0091003428841080050003c0000304028203405010350740f14007442c6045003130014664082881a814540030004440d8000c0303200c0001ca5044400080000801d8a2100280111360025210703520700401c0200b046d4a040119644034142d8003910700326a19000c0035102990850a0900010842e4284400040860682c986e90650081c00b00c0c1c0703100c0c50a240a03095981c22281d459405d5201c800420460401d4014540481403c481d26800c0c1103116200956900c01d450000c0e101c3d0310307100c0da0850391034001c2d0703c94a8541d00b66021030705402d890f0f20100c5c5c0c0e130b00c1c03080c0d0b8120b508640c2c0030a002c600f0b01c114628081d070031414200c0403000c10754540030843d01d920b00c0c0050710055541e5010001c0c440d44100895801403503408000381d04c13807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 551114136 1250 551112886 551112889
    0x150b0313050f160e060429031c080a0b0102070f1406040504020f0a1d2407060c0903291f170a02040509010c0e130e010507090503100606090603110d020d020306 70
    0x3404e02414040c042c070b05059038090201240100c80c035a0304a1140741035180720245c00040d2070041062003a41e00d01d00c0c0c1591f00040a580206440e2090406040070311001d81c404004903903a40030740c89590405002080c09200504215100c1c1440c40c0c0d005050900302501d440000d0100c2e80450304043c204200000e1002103c2d030440c0c25140b21601d0b5084200368080d426011400c000c1202900c240781c10701c4080c0612143c1ca4450540c0e0080303810490801c0010f440880103003001e640d1380815200441e402034112a03503542d50401034400690082103503419211b00626142200c0c1080c42d0280c2590b01240214418202e48114815400424014451403125006010450388041d01c5000c80340d04141c10000000c3d0040d118880c0c1e0300c5e065070303002c1086482510308401401d454840503c039500b00420301c0300703c90b030021030402528030881c19180d00c0008020080300302d80da0740c81450b01040c3ca0500c200b0549005c0d50205c11034801c005410340c54881a0315601c0d0423039021600003c00f8942c08424403d01d0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 551115386 1250 551114136 551114159
    0x11b0803131104090507140d060603050105011d04030f1412040308070f050403051504030c050a0501090b070f0e09130c2301020f15180a03020a0303150b0313050f16 72
    0x700507241001301c6429512180d45554007405083c213003201a1000c9030300e40d01c0d0400341004c0982c100b50100304c02601d03450407501a0130b00b84111184849144032284401288401250184e981516007541251a02000b580c6101a00b44503042819081c0120f10304030b051065070302e00c22031007541d070300c0000d161000700071b44403210f0782c4404404c200003071005000244d8002019a4040155101540682c0e0b880c80d0460380d94030b1401d0300070319501072a201241003190540100e090b00c1c3c42030744e405400b5510214102c6120140e80298400205000180358247c100b14800c590000841720b20300c6110001526980c07c00070496108441200464415080c079003003c58040d014142c1c24406452040b4114a125985100c02e401c001c0481011078007280040041030803840d15454070700305507401d1120504000c1e440354039890043d0b022a0501041f071202d211f41110300c00699484060751400c41e16080000b010407052110100c0d054810000413003480308040100d074800d080000252400d09040c10b820341c16 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 551116636 1250 551115386 551115413
    0x90506070207182a02060105030d110607080405010b1c05060a230a0f11031803040b0403061d06010b070515011211041401063902011b080313 62
    0x215000b0079014003100c081c440406034807410502e40401c00d00e40c080010051504d140d2503140083d04094400c4004ca500031800740e040356000c40980d00e8a1401900903203000035602c5180b03032290071100010780004c0c0251200d5030030a02035800080d0525020000c40c5d102036803c2554000450702106180070050b041101d640e1080020409002c0c084191401d51245140a6800b1000040711030000c4ca80c0d400c030380e11522940b10000c0050201a5621060000b00da00503a40e80c6102c4031404032150881100004541c22500c40c0040c1c03c1c513151460711040010942007540508003aa842000203454104103c0c0340d01030880d0380c51042d80c44034140f41c0103203460031716000d05c8a10f4a111004001d650060039000c56015000008003144401d0340c00050010007820090243c1d40a0b4140007099040e8090340da40c210f01550503c0414011128104205400309000c48000401f802c168001c010f51041880c40c40e41021051080d207980d02c030340d448404c103410860b8500d03a8210110026400d220804c240f008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 551117886 1250 551116636 551116651
    0x1050424030b062706120f0910020d06060f0212031b040302182e0302150c0f0c011b020603011419060507061a03060a020a0215100806010b0f030115030e010906090506 73
    0x145003806100038001b203858003c00c032950741c500d100c0000e40844000d20019203d000703460411560381000c181088024241e5001d030711700085000100d1103803540005000c20328030b4940e40c00c1c0c07070460356100200f11000258401c1115000e200380000001070f1120401d6090b01c1322042445500c9181201c0c402139004000c629010300044115058900400166000c3d42540e030180c4500d213210a9400174a10184a091000c8200344a10324001015800c0800c070352410f84026a516090318032400d540b05800c01d810711000e940100708000400071130502c0d03003650103010000b07060008907044940d454503950b5001e43c0144046000056014104180c0e842003503101c58003402c403080c00c25049001301e680c540006011040c0182d000a001c08010f000308041e000c581c5965604501618001d01c400084003404e200b24070b0984940f000105c0c00c800b5210645040ca10295003440c1140c1c40d02100303c414040b0403441c01c0915a440358a0b4454082c20700418421500071000030035290140d152180c50490010701c80c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 551119136 1250 551117886 551117899
    0x10050d060b0316180507170406050105010e1e06130f090203100b120a0b01120608030c010f02311203180b030c0d15150207080c01050424030b0627 64
    0xa1020240c0001c0104d2501d005550009941da5601025100110700c1580e414156548034104401c001c050b400c5281a1a4281c0c3c450844200c280144618000881081c0292919031501490141000705c05401860724280400c905580d80d12071000420240740c002c500c2c2c03250000200712008200c509203500038252005910b1400303004140601da622005850030080355103540d0742d00c145a2082c8008201d20507040c4080102036a40c5103820b599a100400a6005508181b00c00041d08801e01c240c0d4a040e1a800800104045010003980d8074074220426099041080001050908000002d03051140c829150241c5c039201c80c030310f241d06503c00380d48100d41c3c0801c03c00400801031030035815900f9410400b6030104440000b441c40b5201c421071030300500034028000c0300c2c1d480040d40c00101c030011116030000340c0e00c00302c50000045400b44103038000c01d0503800d00540029003480c070303003550540100d00c0c03071070005190030554001500541c043c4065000502c007000c80d104030855200c40f0001c0414049410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 551120386 1250 551119136 551119139
    0x12c122a0a0b01030f0f08041815080703020d0510110301090e0c010e1203070b0405030319150e040819020106050f2707091706070f0507031710050d060b0316 69
    0x2c100c64000140002440440803055038400c001c0d200005010141e44084540c0c0c40b00e882c0c690300721f0a03200281a01d8910341c01c011900f5804522a2801403c3c3c9408401501e8414196024090300c00c48481782211684036001a208000056200b4503042c00c1c000140b256895240c54000c0301a90003c03000c80400b074102d10103030318950707030001001d41920000307503031850a00c0c103545661800d6002d00b140203421030840404201c02c102d0f01000171485460750304140e601c45034804010000b15404000d18295004082c1d80a01c0308058100550303a00c10703c40c50040303280c2198840003a4140304004800e90140c5c0d12080180150300d004d18000481060a40d42441c1441c50166a8803410070840c0a908004402c0400300d15424400c040c0c5501600310030125198841141a0140c0c2c2c950302250003c0005400d014221031903407003031044558103a003565412210034000c11119102030340c0a007001c0302d0145d5000000030240c0310f08e4101d40d00070f4003c260008100c80100241070510340c0500f8004445c140c071040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 551121636 1250 551120386 551120393
    0x1207080d022a1609180206120105040e07060203070314041e090c030b0607110a0e010b030108120711120c130204090b0301060b0a030e191211012c122a0a 67
    0xb038400c2203c0401c04080b40e940d11016400c00711812005c0065004200000d070241103150029205040f9401a2020030002ca0001001038588502d409a800160010482c85000c20300c260014026800c03105101890695a2101c551048200c110b00c240a4171780700a040007644218401d61243e120641028015a81c0080c001900b078403074804002c1640c085c0c82d2a00e20942c854450300c101070910302c01d046544e540c5a481281540c0c209109000c200d21404c0c0340d903c246020f0600741d4002513441410350350503445510030043c0040540030881200c2c820001010303c0e55492190048d803041070f811006039181d040403001d6064402c408119402030303051440811080202d0390032200200c2d541c0c07800094115a160000b81029462601c4c1004400d08044c840140648051060200603442d200d003e042c40011601c107007030b0748241816a05050411000c040209070402485210300c50780010b071800f081c6000d0000e00d05800011410400300610004c41160480040c003c1401c01c07900d4000344801403a80c3d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 551122886 1250 551121636 551121673
    0x1030b011e0c050a170c010b01090b0a20010203070f021b030a200402030a0b0418020108160504090c02071e0e040816060c110c09091207080d022a 64
    0x104642000141402c18081c004203020a880343c075404405000c140c894600100403a401c1041011440d51a06290700901e40c0208000400c81e2103c00141d42040b0384104240c41c031070f00c8916060180301022a10780740c0701c1d4080c4015485483c1903140d569041c00c00f00c000034581217040000500b0b89030601540b101d55680010380c210580d9000720024015039a148040c81d010042d43d012513040b03400441480013410f426008001d61400549040004510420800301c69039146c0c81d02030b01040c0350700b010420100a1304200f81300c10790366041c0249020340d6407a010b402c86a84000700d200580240e0701c20f00c20400c00070304100214010001d02402c031340c207045d1403c00f006c03805000180381c00b5001502051065607a94200111703500040304001c510800c60014026007140d082181e03d038000d0410015862034103e0f5120301401c0448001c0a038401c000d00f204450703600c458000d8a40703030000e1000b0010150740780000c004440181c02101c01030840c5002d9150a4400d1a43c161216003254503815400312100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 551124136 1250 551122886 551122937
    0x1060207061202210402030a0f03090303081608180307020307090905070807031101031508061017210702011704050d02070b03070e010f090f0608060f0a0303021b130606020c01030b01 80
    0xb90b032013000035203461002134a00003420300000d180e24000c00c032000526421282c80e00c100c9006e6214a80e40d40e5443c51040c003c00100c00000e808241d0050203c4d81031b244090344940600442c0c81164a0b04a09400003450034003a03900c80402c00342c80c2d0000d0383c10803009000c030700002c0821900610a2905541e20a1200000741684904050303840c552070f08010a012550740081c40120251812070030b0600c0c5d4142c0114140c0201c80e9048034400b0100c8e83e2500008980003900d080c41c0060001034903030901d000c200ea000400590402880d1070749102061010346085002c1c3d440344008003041d0000c020007a007003180e15844984a460144200520982c12030081c0004040910308440d43c03441c80380e403c4e500040650046d00c1c103801c0c60600400c4041d0401c0000d0f004e4038088034081440700201003040f510028500004005820118540410040c002c0030004056001440c4118421042540000700e0718240d100000580c0300c020302c1501c40d41c16100b0408002000c0c038043c2820818010504907140c40b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 551125386 1250 551124136 551124187
    0xf0304090b180c1e0915090a060809070501080a02040503030a0c1a0411040e0106031e0c08070510111c3c0e120a0f03020f07080c010e030309040501060207061202 71
    0x700609102c0c2200d50344101d642004c0006e110100080101360f950030590041304105000c2c5503602d0000c60760501806119200702000002040000c1c01c000045440140107051080034540034000030460796030500240010309026901c240c02d44215041c08481907000c5502000761005a03014040410014410410405802d55010420041d009119401005070381d001400242c120b8410780056061009150f016a000d0300c0f0490300305448014241d00c800c3c140c4162680400c0d17620007000940c0c080c0005266402000b800e490921180c10003014981400c060b1100008680e80c154590a0101c0003034204034441184915440e11069108110200c0b4816030660601c0a40740e00d9500710750303610003220f80803140d0b942503e0799488546808480c00c040000f044016006002200740700400011b0b0030421611003800914076000d1102c010f5501000704080343c1d41600080000c84e481e9141d60040d02c4c020100303035005060340d0385000d100070a901c0400d04d20708081401005024011090007418560f60b03941c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 551126636 1250 551125386 551125417
    0x1e040809030a050703060f0b030c09040204090203120f07031e0e09060411041e0608090318011421060103020918070903020306040c05090a05060108070c050f0304090b180c 75
    0x340006072500d40b100c14000c0142c422001d0100410649400a140000510030144441800c0004068941c403014142d41d0f0080c001c0400200507150540050340d00750b00240540e0581d03500e04d0030443c02680710300b1000b0064180090100201944100c130504040e1156081950010f40107500401c4c8101c0c10100c03501c540c400b08080b5101d80e503664000e605001300c4161241e65030740da441c05244200004907040034580303103031b940010f505405800b10620813400b04010303601d4181c403505a4010301ca0400c80547c10020106c2020b900e8101c403d00400241c01c1700002241003100c0d00e2041d81e00100002c02c41410036005100714025629041d94000c60b031f40c2c1800100081342d40d048001c40e0b6482981e03001a60520580b4107100070700a5070001c80c815107000b640c52488aa8540c030505c802e8400654020b030000b0381c0f00001400d0719100f005840c0d4118030500c203944905244075105440c542040d0030028006a460095198920f00f0402c110290382030050365018500e481d103142c081ea130091b0090305c0b80056 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 551127886 1250 551126636 551126647
    0x2030604030c11031b03150105060d0207060209180a0c0f0215150a0e103003170109060f0e0114060a1b030309110901030b0601030209030705180f1e0408 67
    0x101200c800d02c15800b004c0e0480d11002c100240802c4003012030088030b40a030280660000d0030003022118941650b102400243c5884021001c40c0000e42c07080300260350480d0300348401c1303030700717941c2c86640c0c4000940020100b4000c4c100040004102c1e1050b811450510001980d4203400a40110b00030400b110f590351202c5499a80ca02508006407048000c503a00c07409121000c50f0700b804c50754809019a441c0d4854211658584034035925110030301c60a0080e0903641c0c245c0e0104128002e200005d40c0c0d05c245044414101401300b045000c2c042a040814080d8840354240003030105081000c2c01000c010380d085c021945410103a20180c08e101c04140d0088100103100501d0754043c041c01c41c11b10405e0039504102d02c1481c2801001049200411a00001c0728422040315241408400d410f80740c11524510051312841c1c0190001d42c013805582d90140210b0718001450345e034800100403001c909400200042c0b411148405403164010249540c4202d901380b00501c5403403005105078071a5003d8041c80e03495 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 551129136 1250 551127886 551127893
    0x22020103090209010b0c07060f0e090604090606030602091201090803060904050a0c0b0a0809030a0f03050a0915090201110a03020a02010509041e0e010e070506030f220605060a1202030604030c 84
    0x7080c01c00c074083d400100100000030345111400c014a48031003203005803030449407915021500c051841c49410300141c5204d2482c1201d1620703100d11504014002d200003958600c07583c1c0da005075116079209449250b0701040564450919032a222450340302d240007040418410391f03502c0c4041c017020f40200d00842c2c62800060070800304100c600710194102140092466440004020719800034101d1000580001c002c00c1e001d0400105650100c126612501955402d5060480080400401000b106a12103c00c4c502040d21001169040c80c0b101030301250080c01d60002500e844d04880540d030140c0e10202121001c42d40c08103200e0115642481c00e15a652018130008010300b42008403e500ca440712106148c90010030fa01c1042043d60b00c4000b4007100904000c59601c8218034890a0f40140b400c000180000f40c02010303542d40f01a03030460900002821601900c03140c0460002141c0b496516001d0056502c0c2142011008100c183c0400c2c80a1a81da400b003511b0340409400201400103840556080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 551130386 1250 551129136 551129141
    0x1091515180605030a06020a09060c0305070b19230c0310170a08041509050102011a091f0e011815030305070c0504050c091e06030117120d0608060a0522020103 70
    0x1040021308031403020506083c08402540640d40d00c10108501c1400050840d01030200ba020a42d05500d41070b05202d07942e00ca42c001d10000800311304d1507d0210f0701d81d100610082c85000580c051001070504054101c1d14800900c11006d0182840703682d0910801c400c3d0b803e00d2401c00141c8032001c2c6000e10807a0210204c07403401264410081285130702040214052540c0401c8001c03609059650200c443c3da00c0380160b089030021000c185404900c402d4015003400e1200c6041d40240500b483c00c210076116000b007210300540d40c3c1000800407014070042049070030300c4121202c1c80e90271800c2000f040002c0784040741403c40d144001000d0090100300c03074080c410b04000344401000042c0c814491440d0030602d04503150702c0800c2582c0b240003580b81c44640407103800180c40c12540301510740e502c1c590800001c108040243e20404200313100300c1e00400009190030010303001c201e10348900440c0d41d0341840c41160a086004090114080c0b41c51b081080104c0c2c40f4054011500707140000000072039031400101e02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 551131636 1250 551130386 551130389
    0xf07060c0f1502070b1b250209180601080312070804020d3002010b0f060c07090f050114010e0a03080904110403050303040b061c06020d0e0f010915151806 68
    0x4440410114411816080e8008044c51407250304103519035a211042000d0030072040c1c1c004005c00c0c0b414403242d00c4240400001400c11a010240384021141980c0080e010320800c0303031840843c2c440804912031710102000824090400b8401450070110105200010420001c02c50707820008288042819911408442c59000d6004200c242102031071115124500c500d02c40c841c4031a02000241104003803040c81001b12140d002042491100c10f031504005e0f0a0308801c2da45c11480c014000700041c000710602c50028500d02e0250041f41561412000b0800020801c05450511071440d501c1455a522805aa011b90703500c20301494907621000003040c0141041c2e1030b2140c90003400030340803051007030001c0a188664400c0700f03810641e584600a124108261560060300c0d055090b1410b00080c246401800301e000404d607001400801c0c1c15691854a140c0164802480c1d6480b9030070320034061100c2c488001c410b24400d00340214103a50b4000c040305021403203480c0911112265021500340250400c80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 551132886 1250 551131636 551131643
    0xc080c120c0c012409060f0e061f0810060f05030f1503030a08040c080d23070c030305281209050a0602032d0103030f110f0601080307050601080f07060c0f 68
    0x103d03031072020b1a000851100a00384c04140c0c10000001003407070740742c005c441c02d4401170b203040c08881340707043c04580d41c040025120541c00038124201d81c503501d04280e46200c900006c1e5981119a0a107048146403040498200004002c00101a40a041c0e0031004881e0031110a5651941907600e28058581e00c000a096042e0325000001d071204055900c03990b440d01032402003a40080069036100c01c00d954100d00d0400801081c03103060705511079800030304600b401480c8011410b241c501d156075405042209500110701141001c2641002c01c6111a03a2228002141c0ba800610004c2d80c68090301c003134420200031390510b803650410801c01030140800008190b101c1da00755200e09080c9030003020b402542d007001c1c1803803c1100000621000111040703040702d8140c0c6070601c0070390319590200d42d210440e1203c482d451184426180e0060400c000b0700b0300909808000e1a103079503491515a041807811f0b444000c150340300078128510801e021074090708956040c200103050712514640414260212640075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 551134136 1250 551132886 551132891
    0x30e01181b1e14150a020d020c030703020117070c08042402010e0c120a05010c0c1203050106090b0306190303200a02030d051315030207020f0d0b04152405040c080c120c0c01 76
    0x40c5171141c1c0000d140d040a103656020345056442d10b80600d41d071601d951001a0005403400e04156001c18120300c0c160304822240f9003200c0c9400340d511248000e60081c3d00100c10f4010311080e100e40c42245601500c8034080903c0207200741c201100407543d540502c40d070110320411020000b440e130300c0b10402142c000150305c10000c0c4205d002c1d40c0000b9008940ea05000e4940500714901c1b01000c601c0f0744079150607220217450f00c0c0032a50402c0c0044201c0d40009086a80000001802c94a00c81998503040015403195a0301140418000c40016001003aaa401030199001c1c82c54cc2005990116036490342c25a98078105480c2c200f0a41003540f480607a42c8411f0f5007510020340d12180c0d540c590000c02c020350081c1c1e04281c0f40d080c0309050100501140002030311021009010a00041c1c5d0f6a00312070b8818003007800461050494480841e1000c41c1c0d28104040c2ca103000c10070419805c041c041d000140050303003002041031030048801a118414001c4040c555200b800014640c0c00e400c03002d840040341c9004c000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 551135386 1250 551134136 551134147
    0x210060e010f0803030108060f1803272d0a030b10241b0203071e081203071202070204110d022116030e01181b1e1415 52
    0x491040580078010342c07015044410002c50030040000c1107074100c401c80c1c0300a00b0a603907404016202c0c0e103005040d41e28080c081881540d00070300200064442d19600120544d50840c01021000d5850652040b980c001d41280036002204840d52000a6000c0412580204541e0805e000a01c03102007513000103203d030401c0b40a200752408144000e034180c400070541030011200c0d00000f00182c48030580c0c1103000403c20f203841c540c048400819829054405002c40e4181c1d6221858202c1c3e01801c200c03520301c9844002010842c5010801c188080042e907030902600e9400c140d80c004280d01200903040e00e609400080d40d40864840750702c031209004c21103c6c07440c1c5612070201d9a00296005801c200515608401c4040d0040544110b480c01a20081000d0b1218005035034190050b00b40892080c0e401d558600071064132140c40c407150310020380b080109592601c0496111941680b4230f400140a6150303800301075010281580d0400c0a40301d0380740340818035500b20000125001d52810b2110907404002c0784 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 551136636 1250 551135386 551135399
    0x4060209030601170c0103140114040e030c0c13090803040b10080a1103010509010b01020c0d140109050a020111070617092a0a080f0a111201021801080a09050607050901021006 77
    0x84c9030603c2000c2003918502e080c0400110151480c0410401e50080840010011458070030000f01c4c0b01388000c0d001081d0501800901070450f0011034030360000b0f800c00b00b1203021a2a1140c001004c6408295003003242c29160b4603080200c1c000144010207061144d004500c0b041d9038001319600604503201101c030001d03000d01d0200c40142c1210020340c0690300348804605030103410701030340e0403026041e4001e000c0500c01c0b000b082a03016145600355400740d916428413080705403e011392590980554000c007414410742c130004000d0740c1751804c5202e180e080444180049507000001451a4041c40c0303540180b912035450305400e12100c544115081c1310400c8130a042c41c1044008071480320b00440c1c49a980c6aa17403c0c003d6107a0340c01c00307022011030b0080c18a0900141820500185441e4054440c0f01080b00c0803c44500726404203403003010348401e00058140c250b07801354013184d0001c8000d00074001100b0650710240d6551000e85801c0c00d200b0040350080540c0d00c200303d40c0c64400c1c0c04100a1064956801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 551137886 1250 551136636 551136659
    0x40b13020a09210201020a020603070e15131a0301060c0206041e0f0f030305030a0c1701030b2226160602030109050a02090d110d0605012403060609050103020304060209030601 77
    0x1150303d02d81c0300e500010400140034020003100d22601a0060008400c1550812089900c000c0c0f01c202072010440499041d07880f01e0b0318403d40c1c96030380b0b203200d552403801c442c1020078281c1036403280d13000488240c2031440c4d1440c1c10301905d046070b01904046510000c0c4d440011081d0003141c20810581c2001c0d0800d950452200c840d0604030b0b0413849220200d15150b03071110600507028003028000c504104081502c224641d40106560009817504441421124126030b0303da1101fa482651a182d1103001c1c040b034084111400c0e0b400c17403500305842840050640d1140340410102c12030340e0030803141e0088124003442230340c112184802e22884c00d072410342803840c154000b50000c0c041c0103079251924000401c3c4c141c441c03084a08080e4024049841040030795030350070000c500c078244150095851305c0104005080c5000c2c01d03019049035500c61a4481c41000210f00f1110541c0710a800c06040410400c10309412165101c10ba0b01c1c2887d02690301d03600c6041c80d1000e40704001c0c0032900f511940c400010b401303c214 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 551139136 1250 551137886 551137889
    0x2030c03041203060501050a1209050d081f2d170a0c0f030c0b0c0304080303070507050f0d080c0d06030f050d090e060a090902120109120e030615040b13020a09 70
    0x2032400219055202d4000c404441403801100c4c0810801c00100c45d046000e000c0359403984640100224041101e941c1d1700d4100b468400700240459889001d022191780b1401c03200c40304128980c10501264074000d40320448051005800c580c0191080c500c1c104861242115405844690404a0200441108665a22034242e800c1c4d8080818000c0881c0380c1c1ca07020500000c5a4002c0c2c22880418140034090a16900c0235442e03401500c803c00000424200500c00380d031060600f07442d41c9464524504108d4109210200d03036403e59080100420386080c1c204104030307084007414403455140c80032051142c000b03146c00c2c0c0018082202002d062010030100143e039598240003640c076030364200c0d602d51642030f6109041d1000c0b540464080014040c01031140c2c05061914001489a880706142d013440030b0855914a900742d0340e4442c4049041b05030354002c2d0990070300400c01d400404581c030701155002809100315038003622803512001188c0031980c42001c502c50185000b0f00c21941e40c102d07107001800500746ca = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 551140386 1250 551139136 551139143
    0x1d0114281e020106120615030f0812340c020306010308030106030e03040f0b07060605220c02030c0613030c020a17070f030218101a0d0f0e0a0b07020a0602030c0304 72
    0x440c0d00101600784180200c0c82103d080020007003c0311041e0f506e5002415480c1071038507101a9589000005c110842d404e0142580500d161503070760400300b14400d03107000006008800b014111110a000404020f40500d40d41c9030400d012503208612413000c8400035000300d401f946c0341c483c050021051144100c011170403940d25460030007040110152147d12805140b0a8080b042c1d401403080081080190052a4081c8190000907909485038001505000342080c0100200a580c08110200c400ea210340040d0100c540029400d002080800984e1141c0060840036a40015641607041501414111410942c01411411103d03240d400d07000c08032009120612144c4140000001c910407007660441c141c1e42c000c2d190383c881509884c0410352121000d84261404043c2a40004400405501d403000c0740c494105401d0b5901c5d1180d0410b41135a003088044025549059018220700070005030024100c3d030b000f00040501e036500d64081c3e040c40301c1030001406140c00042000310700d4150200540c03080d0b10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 551141636 1250 551140386 551140427
    0x2a0301061d0619081b18100e15040c021005010e06130e1c08071b032c040204080f1002030903070210020a05150403080703110d020d021b010902011d011428 68
    0xe000c40b4003006240c05841130304050720749100900c01c0d490030580e01c50b8010420028014843c03002401300b01100d807048841e03401a00000004804800b59006460040a41c05c2c840d084364100000051940400142d038031f00c41e25914400200c080e4818400507000c003407510103480b0281445e8802820101040f5403c80c00180c3c80051f00403407414580b00c400c80c441e050740e5400004a40841c0d034100c0740005580203543c4441c0510b82000981d10f9000a00c06005000090711500c03880030251071820520114102506006004000700c800000054481c42e0b5012118060390015443c030690034042d0681000c0e005002c0d140313440b080022004a03071401181710b555001d0a1f55240340044045458628000155100030080e44c1242c3e480e5801602e980d4a51440c0149001c2c1015064280500c880d2640403071651505807400940da080310110800045440c1400080038160000a104507180e000700300200d100820381d901e03c8000c0c0310b418605001044a00642981c04040142c40000008c112004108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 551142886 1250 551141636 551141659
    0x32301150507050303061003150305010614012d090306020c03030106090e0601020a0201030e0705120607080c041202010c030c050a1103061e04080c2a0301061d0619081b 74
    0x6100e241200c042c290018040e40c190f881d1101000490aa500d03c194100b5480361b22001c03000300d10340d0810009510540002410070325000c103c801c201c06040c4000c1c10320105486200070304c0700c0c14001c40c9040f40c030302884400c01994440709880b0030340346130400f0704510300c0030406d004640400401141a41d41c0c9868039000c040e85c0c0c03115a00707076200031102d1600581280e11148010b5004c1c1d000000e1050001c0c042d19010b50f10b440c007041c900102170002803203980c48501405003031a0898220b64109070780c01ea0051410b07081c518111031561059100a04210600c0c90520502d0306c100742c0840c005600a0684505a44605110107030f86400701803144a800341c417002c502c17050301d403407036603a1084160200721800da40c50b6100d14905410440c260359803801514850a800a1810a24141511510000301042a11000341401c50b25180c0100200c168452024150480502441940040300b01c0d4110600c001a0080c400540d04540c007107107440c0300d00c205004074002d010b140e954038001e0940304586041d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 551144136 1250 551142886 551142929
    0x30201080604060b0d0c050c010e011406030d02061605040b070303020702090c04081906140708070206010f030b151503150111012f04051c05010c0f140a032301 70
    0x90b001442000413048040000c642c2070109500044081303034050502c41c0c20501d030909001c0c203507400500100c010380d5444c43c051000172003d800d00ca0300940141c0060004044003c400782da1490050b080c02805c80701c010960350020b01c03a90450f4040c0001d2940340e03486100506d406006908034043c200e10811220000480c120010415070341100c804c0350051005545003984108000b81c3e82c40190f9170107440301c115000010700305440e2409048660740d4541a8070300080c0003410482c0603004400315a03114241000400e44440310b642d04440800c0c81032455002c41400980200e00d54005072500341c00100400040311200624032410138000c0e290310828103586450b160803149403c1080895400d0001e041011454400c1c102a100c000341300264a0161a100081c2a2106084500309400b824081c2c090802c9028000c8141082440c202400c0b5415000380c007410309024224007135004403002c5200b804092103900103e102440d0025034030300e007092401c00445200d41c00d0080012811410040c191784 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 551145386 1250 551144136 551144141
    0xf14060610030e070b03040b1006110307060c1211030a0c050415030203070c0b01090b0111010218060a05071e020a0b1309021c0f0b03060a0b01020a260403030504030201080604 77
    0x18800c01005141000c101c200140d008142d0061240032520420300c01041e0307280040d00540c0158000c80a000d55031606040006a00d03034103800039402c005801804510b8000004241ca1140e544498045102181e000c011250268a20206000c42d03085c05081040010040c2c0114082c007002c0e64184200050312009071a94410f5100b05850303102e0b4001000d400d10b2003640915040b020303e1801031402d244540f40c07034000e0f0600707070403490000d0b90b558451780e555038124601c200b840c0c1951000707500b0300e0b1460354403150340e1900c8120540104000a80b049201c0c0c861404c407a60151301100c20200e41c1c0c60921301d02c42c180d0452000b01e000b02d0b61102e01007810b5407890103840c0070801082600c80f03c203080c545007002a40200655a4004246111075030024403d800352a8140e81194000a03105010804041c035007080a0005510b1074034010720307035500da40e008c608540003541003010501009600e800b05080107500001881c49080301240200030140d0000040040b603000340d036540410340b100400c03c000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 551146636 1250 551145386 551145391
    0x30a1d0c01120507051b070807090605090a0c11240606040308030703020901030204090606180e010f030b090f15092503020d05010f0203100305070e0f070c0f020a030f1406 75
    0x4182400c1d80ba540d0107501d81c100552110032450064108005004c0c424600702c40020803d03103503045105c1c1849420400c01490b0002c00c000304080c0030882c40e10340400d010310000b80c4054280c03620f070001d451480b40503103200481011084110f0302d44000a9501c0c02c3c1040315204c040c0350141030500441c0c400e00d0285d040d00e05598000c2c03003c0780746807180310f400d5000390b00c00444541810f40074080040c0c00c080c0c0b481018010041500c40f88800d01007046500300030502c6400019888031301200600c425442d03540c0e044140c907446010036800b511508003407840c003002c4480e000c0c0c0341d1003102c1243d50100044100c0c0c500507040d00d012030720403010055011164200c204001124001c980f0340c1000940781c044d94078501180100300002c0d800c01c11038180003d0b0f900440b816148a01e034084d08100300841080448010000c0111041c100d051008503000301980141001081201d1054004280001c251032110103550003001c06e80141d84d00d181c40464126030725400e40721500215031885400b54042000b52 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 551147886 1250 551146636 551146639
    0x2918011514030c04121e0303020301081006031101050906070804261903050a0c15020408070f0b030403080c04230405161709070f14030d0207180903050906030a1d0c 72
    0x5042070304000455004195003242920940b80d411901c4480180d2003041040087c042d0390050394035818046254545024007032041ca94a01e0082d0800209064804130380c4040401d1818903990382840c4000b9440b801524400f5018240c005400541c442750382001c5030341150348404402c0c5041c201d85000b0340340d1380c0c2140c010302904d601c40c1c0e0342e0000030301c00c80003000801a14200b103c85609a0344403104000c8842400b20741403580045c05200f5004104207400081c50f03002d0a0620b50382c140300d50403a49000c09400202881200d5010482c19011001590301403c401044820010402078241e02202074440043d03025130315200c08207501c80000c000401c540085619141d40f10709043d955402021002042800035010b400d001096407000e903100d001c02401e5800384a002c082da40b400301400c00c00c51280c11025917110307135001c1103903110180a00c001c9824240b00061842d4041c10705480c40d20038980650b078040d80c0002048403800041d481140150215012400502402044d40c2d64a0300700700c1005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 551149136 1250 551147886 551147911
    0xf0c08090d030b061603021513030e0d0602040e161d030c0f190e100602070e040303020c0319111005150906040b0d05030a0e0301291801151403 63
    0x3210030718000e400c0f07000703606005818245014040610781e184101c5800701240103030001c8090f00c5802040080258001c04101c2c00b13081c40c1080b84e500030f0700003503106280078040c2c8010042e54040c00b010f9419940200340c69180c10250385000300c50150800c4a562840e400300e0200300ca804400c0b14a140c04160405000d0000c00c0d0312070b2070a0400c205448c0c0800b04542c4042d1000c000a4030010710154400180751104100c0f6130b03030402c2e681014020b49160051001c65004400801c1002c0900315801d030084c1c0c143c00d0060742c507072402c000076055100e0340440c2c0341c0c0c01140b900c08092440d8054a02540750f00440c0a48502501080400b400d0300e0040e46c803801001103039401d440c06440e2038038a054006000a0001a0491207540450341e80c180080040d46c0c2900003103000c071887d681204044185000c00c600800c402443d6040e00c0c1901d420010704580c1e52144517540007407949030b1000d40c02c0010078084c1000382661b9036000c0304101d110046400000100140303503200c8840100703410740340152504001c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 551150386 1250 551149136 551149153
    0xa03060b0f0f0913020d06050f040e0c0108130c06050408010b0907022d0a0b18010603031209080903010f020a020c1503010909020616120e060309060106052a010f0c0809 74
    0x810341580040f642154860002031210344029814802003408550301c0c10701084403840d20041291801800c8962401542059508188440c0104060469070001d003000900784d120080d144005116080000780140c40b03094002ca20503400c2000b0308111040c0500078400c06002c04140041000261481740250340056030f0507419080725800d21030a60580442a442001c604510502d80b14140b1020f54094003000180710f08882c4040044454285a130007d00100780b656070020800c40e034041c064a005665545d403002004070503812580340c800c00800074040e103540c0740c10000003944045034600152040c0300102b046410180207410755495001040c5007940c0c0ba01428001511802804980c8000100816680c01c11042000f440240c00381c121820b10132035000300036000908881d0054401e00082c010499629000105581541c111f0b16150341c0755a20f0301041e465000f03541e000d400144055054100740c80c0c8c81580144103005800c4414004206d0000701905d110200b80d5900c45240c000304038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 551151636 1250 551150386 551150407
    0x70c0c03050106050a06021b1002150c04170f0a03050313021f09081209061e07080304020306012102040e12040314101104061d0901030605100b03060a170f030f0a03060b0f 75
    0x1907409c030b2803031702d0050301d0000852003508014114210f441044440020070103001405d90f8031010b0b4600101540100080c180e01034011380e4a5445090007401c005000000884801c00c88180141d1581d024054240c0c040640d02648001020403858000161aa0000080c4200002040094200784581241c600b0400d142800704541c0706001d0012102c5c0416500000700c0c50b0302005110a074000c410a40d200d0803c3d104044c01c028041c0d0243c2800b40d61403a1409c40e503c0040311401d40c2c01e074125000500c3d07600c400119420125950354900c407900001c980003003800021a00c1c1c26086070080b0503200c03404911040001107c50300f02c1c02c030085400c140014008030780128840100c8143e2140c5d550201000080060001070003608100d82c000c0e02d4030140411089210307008030191842d5101c1034118648030001c00c02c0c45040e4400d10903408085040d200c003155090041c40205002c16013034a90702c1b07421070921011a4858410000064074010300014404c403c042a46e9601e0100c100d4140b400c83c1841 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 551152886 1250 551151636 551151649
    0x60e011a090a09050610030c06020c0114032502010b030601051903021302120705091c0201210e01020c1608070320040b030f0c15120708070c0c03050106050a06021b 72
    0x10000b802c4560340d200d6507000b240c0204219803184c0000d61551007034908501e0b0001040c5078a910100543d03003d528010b0f41e0760b03080084403001c01c11444420340c507030361030440701c500000440040f0255550b0b01a00e006410b80d064008095146080c0c04540841e45d9075000d000310b0320529504401e44007118001840149440980c000050400400150920101e210404141c4206680c40c50200e000058405021704145104524821501c1c2400c40001c9960f000a4044010201c0000c800c1200c10340030320000c000303680301224400c80c000c001c54981c818004955603808100d80c0000c01803080d4980041c50480004041040e254842100030941c3c06d506c51072940000c02c01d034119401501d4000c169440d403001c000012002402c00d00414088203c00240110300c401303508101e81c0400c0402c00e0040200d500c94001d40c01c15100d14103011680d42d09141100d9102d6110801858402589800814080150003c5c4145c407000c581842040d6524501aa556000d41202d450000e50801e02c003001880d00d41c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 551154136 1250 551152886 551152891
    0x6150702060a0c03091d160206360703060506190614300115050403050a0803041a0103060204030201030b18070c03140f18010c0803010e0601030207080d09060e011a09 73
    0xc5c109240002e0705d071102d030303104558100d00641006100104000450107074030440c21800d0154005000d06040010fa00c000e03c1544089042070043d0100e2005659511803140303980c0388094806507042a80c507490303d817018007425242107200702e0000030380e051422604011001180d000341c44108101e2820500003543d900320004015414540c6400440c0d031800440036626100b03049201c800e05581030010b5225103d003004c00e103800704201800280b002032400039403584016040140b09403aa500c614041c01014140c0d6180303040344904900010400c0300b60b401410076a4400d8800f07000c800c1c165414040c022140c001a60140201d81001c03807034680c010300d82c00d20031500a24051045c4114a20002d0040c0e102801000341d40b1701c00540360b03c1e00303104d207003004240d102c092038481081e07400e940324000315001c103024044000c035041c404039a06a0103507044601481c0d104445a440c0d030050b0240d4070080490481c1034a07040d052440b520300d5441c0c10705c105070300251250381ca0b00202c1c01000c00c1c45840d2000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 551155386 1250 551154136 551154143
    0x2202040b07080c0106080f0a08030c2505010f020f0403020f0d021207030302011803020303010b130807030308011409060319020105070c03051c0807120903020c0d060506150702060a0c 80
    0x204408100014144000c140c458000c00c815036030b400c40c2c040c0c1c441c04c40f0101c0d4440c0d032464124010b08000550081100f04005420026aa40740c0d114003042012500c98103000c090f2000c0341d001c0c0c000450f06040550000c1f90302500c004c1054641c01e0250400b130788500d000704215075800300800d2006140c5042480701010018110709030303a0455501041e07099418260a030b481c0c1c0c3c0300c01c0040042540c240280c100c688040230528205095a035006552400107014035030702082c1c082061803009810321284002001400202c401107642ca090180c0050002e01847d06103841c45400a405400e141e81c400b4000d14000d0300401490501000d48040b0720240b0b04201c0c10004104541000300300204209000340d80500044c00c1070b040d620140260b5225150907030402d000d400c10030011055081443c0e0100c0e00e11942001c42e440c41d01c0c4ca030880c1002c82e03024100b9400310f840410b11090040c25840b8510403503095440c3c640e4010452403464407802000e0000758003140400103010700f2449048119006480b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 551156636 1250 551155386 551155391
    0x9030c1906090b0718060509150703021203040c0e0a0b010c1103161e080604120311190906030f09080409150b04030f2009270313030203100b22 63
    0x41c0d40d95525150f803043d036042000560501e9050341d2080350752000001001309080c80c034034260107000840e06501c20404402691307640851001c0926009100c1c42042480403c041ca0390303031600707141240020b0014007800414124100c0060340d01502d5100e100701c0964145c43d9801d070503040342d035201040c00200f1006030309401501c6c6803406001c20007402d0340c050407199030700720065180101010b10440705984201d900381e000805100100e55091010300b00350304146804111f960341400c90038001d100785880981c0d07900c103454128400d00d0b4040360301010f903085682c060021420790031109060704c400e202c0207404050100003c101404140d8045030580441c014040d03189aa64908401c0c01d030403651007554600b1207050580b04002c051074a655100d03820b007a81c02c002d541004003082d15a2001417110010f04100561801d61034014104542002030032411030f50344010500d079141c044141c0d84000ca00030720410a00000d0045030307001d01c0101d031202420604a25512003040c0401940080c03000d9401c95 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 551157886 1250 551156636 551156651
    0x10204050a031103120301051503061518120303010515180d0803010807091104090207050c0406140909030c2e090f0201180602030a0507020303090301180b09030c1906 73
    0xc031044010030085001d0400c000503e520ba00a060908000300106054044e0410041c0240d540302c404054040803000b02d00b540300e554071400b255003034800302d0141071160000b04004011400c0383c03989001203c005d0b220580350914142c0920303540d0200380a81540803c06803012414200080060b12602c0c02c4409040c560050070408105c4031400780c074040d03030b68a00000040c010701000b00224402844030340c2040140d4402210b411106000b980140e49516400040c0c00081c0181003199103003204c8000e0003080b58543d0303004010500304c418034441e0302070340b03520001541b0748401009884010403c18042d0034003d1000003003030310059000800c100e4101403200b01281c070404605c03401c0c01c10782c42080b094a140c01c0074000506030b40400c5040e40c588021964041c4a0340b5804425100380392080d0030195111003c0b071000a085005080659401d581307082184d0300e69900641c41d041c48540100845c610341e0b00d4040c611b50300c0e0301c9071800c403c0743c580c840c0010510441401c41c824a9040c007c100018440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 551159136 1250 551157886 551157889
    0x10c1d270106020303010e010806011203030e010f0e0f120c070603180b0109050a0e0f120310171e031303260a030c0f031a09420a03051e01020405 64
    0x6140a0b081580142e00c044014003c0001c04580180500041d40082000d580341038006100a8400c140060406403917010041c0604001d40040c8112200c0420a205c404400241281d0f00d0210180b0312019110326124680c40a990b6001c803000c2c00e0806024041c41402c0540c1600509003c0364900721042e03d074031840c1c02240781e030f041060107400c1000010850381000c02402c81699015494488943c0040c1c0d08000c00301c400203940d030401079040b8081526551060414607160005620220780140c0349015080d000e0404580030030200c00c2020740c0521059018038403030b624020036815015404c4601c6044c0f000c20f0b00104040000d6150700800d01c0110510b210840e0150810088000461b4a41c214055880e420007114060540e00d40350401c085040b00c031546240186082c1c02c1c42c01220070303001140e0403620b10210340b00c030b10300915080701e081401c440303650b000321803a00c0403200700040c1402e01c0e120b903250440c1c6000032070f50814024010030360300000384801c0b007030180541d600310f43d400c11000409 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 551160386 1250 551159136 551159209
    0x807080309030c06060a0b07141e1f020c070306050613020a03090308010501030c05040911041706010905091606050309070509010b0a08090c03190302010b13060305010c1d 75
    0x20356151001d036480f070341c02140072894050043c04a6108489001050090121450544010715040306003050707140041d16025040907005801071403c101d41e0000107183c01000125580001d01003402110001d1441c0d13071800480c02003824850050308a400e00300045485500f1881d0003600003864000300860b09200d110481e4003480e03c01000c04e484810702e0381451341210700c50b401082d0a0909000168102c1c000510f50300c44c41c007640214a50700c078441041d8031004070544010f40103007450305441d0980150312a5a5000c24030170205103504007000582c1c12900032a5280310170502404545406042c06d90641d1540c100600b248014884c804000031160f8419071f44a00070034604030344e255110300c0d42c48001c000003401030000080703601155181d90162030024401c2e002383c0f00703140ca080313148441e450201e000d081200030080c0d0240e070700850460b904015500480841c1c3c491802003090103003804054440f5040c01d0340d1440d010f08000c4a44c6c105062105810791907610000384100485008a040040b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 551161636 1250 551160386 551160391
    0x6012111191d0702031e091809060c0c0604020d0213090b07030b010c050a0813080105010f06110109150f020904020f070b10080c0411123d1208070803 66
    0x2501941c00002c126203444540c801d1161101e90320410766a24020801940d28030030503007065203904601044071440c1030400242d600070b40e0002c0c1040401070131000300035140b810079280255103000c2d076000f00c1c1c011542d50b0112008082140301030529640e1b10b800300841100d910b041a41c00501088544c45210394034410300201da80f05032030001060030108001001c50f84058203035070600204810b03d1001ca100081c030800000c4e880601d0507918200a1040c2448444a5010030f1056080c603001050011390b41441c201980c0183e981c0c030039031080036000035003031300c00c0c00002400703d000b4841260282c0c0c90907044108464401c0d4030140c0f4003407110020a04aa104549000d00c0703090104a4800700f01d040c9008941102c0580300460340c1d01e00b0502060b0310750154000d814411503a0301c0c1d0740d95550b4021404d580b400c40c0e90201c01862458484107250303a600d590b101146183d11003007125a071540301d81071240c0030116481001080c2c5420003406c070155145e800c0040d40c03204814444500080d007010300451 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 551162886 1250 551161636 551161669
    0x30f030f050903030a030c080612060426030a090302061e19020906130513020307050a0305060a3606060c02010e061e04090e0109150513080d0e06060306012111 70
    0x1c140c44030f5040102380e0040a030040748140140071449059520001d2080d800c90742180300101d019403c102c03228242c8a034015842e0b0b4042011007040b0b510451903100e254150300a800b0344501e80c0d80c044034550351005c0710041c140e903ca8031368040741c0a5040b04010190b078a40102c070040c684615100068142d800000200c00c01602420003072045007007070304150320040c2d100702056043d42403204018005000c0c000000d41059610340c006001c0350344458800c001000a0803252180d040c031020201984400e00c41003c4c0c07045211090040b05003007510404007114141c0d038480f4120007542c2d0044500c01110302d2640da00c40c80506c0304a030800300183c0280810410110b84540ea14500f885c0d10023650300d01c900148141e45406400b102055030b852130380d24150341c840800a032580c0d4a1070030f000a0700d0810300c041d080c49000700303640910881ea640314504190340031080300c01655480c5c0402d42d895409011302c0c41c0103460301000790142405c0500b0201158403600f024900420154013080800d120f609900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 551164136 1250 551162886 551162891
    0x2505100f060f0f05060a0f03110a0822030905011101110a050301060f050304020a05040207050a0506090d020f1f2a030b0a050d030c0b10030503070b01140a030f030f050903030a03 78
    0x100294842d8002850051246181c1c461600d80782000003030031030084217203060901c8110380201c80c1e0544640d000b900072441100141d42c58500c0c01d14000d100f0142181c06105810280d400d180084191050362240c040c2e0503a10b41103810300b004011180110b94039410602c9640781c903006032070f00700d6440142400c06000e90f07400b512503240c2070000780307142c0ba201a51024040300700140405030b1105001c26040d520b099401580e6a600d5141607403910b07642110161181c0507207400d000420801107203081c19424103a01b128040d00c1d8941006484a00341c201848102d58140c221020342d003d06e8100303404070201c80410200c0004540800c1000c04030b604403a10000340e40703c0101a0342d00e0100d030b540018080c2a1400342d08640a41d4000c0c5c400f1903a1000908814209030019080719030501c0540051540320042d41d403581d07107514140348200c00c01c0c06600d0105598010340c051a08002d4850002c5039081001c003291842a0b450a842000d88500c450040180800c04a005520204000c113080c00690790300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 551165386 1250 551164136 551164139
    0xf02030f0c1605181315150306060b0c03030a0c0c020d03022b0503040201201e100b011407060b0a0e0a0b060301060f050c010f0e1b03032505100f06 65
    0x2042000d00660300054412101c8032400903c40700a0615a54404000418048580c220b0304000c01e01b00e00154035080c0d06d0b814025201152421855080116803164405014240e115520020180202c0504001c940c3c1706100081e1941000e80100703800c203c190600d4400030000b60080303058070301d0700c5c20150f015a00101c040514203044132080d0025103104070340c6d041c1c803945c128001003a91002920203810485101280034241d00c0c1c44010190b851020000c0b80c100c00b2008510b840c103240c1040515000c0e01416003540c840c84114028810a0801651080005540440201c1040e00060f40644006a81d94041050b80c0c6881007070030003500403031042c14031b00c1c9460100c4d94180ca00f07194801e40a2401800108241d60b00000316900c0076280d401c2241c0c9038842034100c0f40c010050443e44034100341c00c15011901c480c1000c00c0d2503109000c1901d03c3e030728070100b090034150740c1c0c4641c0620081c0c0c4844415611890030042c048003010f940300728141d80b003155000d06460103079540c02001c0c80f1420791300c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 551166636 1250 551165386 551165413
    0xa030b0414150411101404080a052503020d050f0a080702031c08010b0a02010e01061d090a08040b0a020c0d11010e010903050601092403060f1109030a030f02030f0c 72
    0x1e60750032058036180b1101514013966a1000c082d408400309001d0181019042c0c110b90161480fa02d203001c4405c0d0380c80e02c0c0d030765402d003182d91442c001c881500c440c054170301013103126080e8441100b080602481d041d85030624560900c81002200b6000741c0c1c0718001c000d0300c2c002114047c480c00c1406401080400d484e00c04034010941481425415002d540701560103100000b80c03c2003002c0e0441c0c980140003502e80300007070000c1c1e024000c00409416254a0218041990038071511030540020080000d9051030b580d03003100507510174801c40040c00c0e10700280010448844140001c0c0b82d0002948141c5081c80320315404118040d8a004e130888403a194101c219090396800604a4009a400d04e80705001c14034580343c41da11682c041c042d100160761186a1a0722007880e030042018410708941c4200010350b2399041c881c000b00306400070760000f20304108944420364204400d45181d14001405400c8244840d5015100013640303980003011f50105010b108110150300024144440c2e081010b001e44821215 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 551167886 1250 551166636 551166643
    0x8040b09180405150a2403260403061a090708010e090a0b15010309080a050304061d0c100306050d1a0105010212070b070504030c180506010302090d08090a030b0414 72
    0x9018410341c10040040001041c030000c0c4d002d010381118425880c803501c5140400010b001008110118900c07802c0041c00440300141e500c10840780140c10080c10591005601c803c40f2560300310000d01c0041c140805d00c0454019404107410380c01302c07581d1035180c00e180e0022502c01541265040040346080b03004000c0344280e2a02e40d544028070348044c000009543c1d07108040081c2c0a0300301d0004207a03004042d03003e6402036000700e203c42d4100007044c5e1201510725004046034405c85040b500342d400c050b0000c8202daa01c25101003040c0b020406001510a1070341401038580d00715450340d08050300d034070000a40d503c0b421810b0324200d01443d0042500410701c020801c3c011410b0307104604540c41503507411054004001640c500035072141c0b170640240c40702d20040b1b505025070b4002a0040e690380c100058032000181c07118860348455402030000c0c0c1e40c2c2d07800541c100d006422549030060045050800094264030040c8040c0c0b03001446491480d48a44407803a05040864089500c20786504524148103003c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 551169136 1250 551167886 551167909
    0x170a050d050f04060305061903120f0201050403081305150901150b2506061508070201050f07050a120f020408010504020109140a051c02030604050c01090501020303270a08040b09 78
    0x103003022441c00b80d20340300120062041e44507020070140c0d1440800c1d03c650752041c0032240100c00c40d90301c0d18042d803681040d03020b10142a02440201d80b084c405e11402500602032030f881260940c5034441c50750354185200030100b030401400c0320700380079412081d80340e80120f1880c140544242c000006642880200d60051034500d5084444000c80074000d100310120b040300c07552071240b03030030290000200551414401409150f081403120506200000c00c482d82c0c0052440e102d40e20981c000d122646480420410b00d10055642d4000110204081c00e0341a00606000c03007032181414001502c0382e95008280c0498115420405240c0d4541e002e000956a1040c0140083c0980300f02103455003d059001a10a40492107005d0285468101d10352601d912120780852141c0c001c2c040d10b8191800d443c1054403648541107050200d80ca031100803880b540f000003600e2080e102e4000c0e00503000200b008a0b951161400d0105070180b240100c0d0f0030008108030054001040701c054480d0f1181c0692081080c0c1c0040c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 551170386 1250 551169136 551169163
    0xc010f050f0d0b120d1d241b151006091d1504090507170102120f1008070b04050406060f0c0308100909030809010b0d0b0103110a170a05 60
    0xc0c0025041c21011030100c0304030952180000400200c04004502c0001d84101d111410b40903040301c5030aa01d8000e48007001c0800741c100402c2e043c032245801c004444143c0a103410543d0684501c00da5142d040400402807060420408905540340140c241c1ca80b4001c1180c45c2c00a148100a0205104500480101402150514140503820911042c9450030584404007140b2095008201c003030b5561b031001c43c194200500705211344609800e0a5554540038071515480115007001c01980300018820780b03d40108601c511070503074460310301c04804c4c0d00d40a1320b84c1140101803040007070a654200701d02da004140050320349490b01d2502d800c03c800c841080d0300590910087c0850050030b5039100b416081f4580e8035003001e51040e10341d912242c2800a1035080340a40c0351900700c10000345900511480d01c80e022583c000c0c40b2420145003482605030000a00800b41c0c000000144000366408070300c21040070001e03003003616440d6035012a18640f1a10211007031903401c20001241404010303c40440108407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 551171636 1250 551170386 551170397
    0x30c030c070608011503020307230c07050a1815090203090a03030b030a03050307050a02010e01020409091112030702010f02010b1c14010e06070c0309080f013318090b01080c010f 78
    0x1612282d170844500c8900340004040d400070001e8009406000c0071085810741d540f40c0d95480448144a094076441503113410380728425000005090700d08458150281c520f0b0fa442807200181071001031016000c00c118405001d41200c10210303143d4000e10103984903594210040500b41a1410050110784814a40c14041c1e0400cae01d03c0408660807200302c942010356031a105551700d12803c402c034014200c4c02010032040d400080d0001d0006140e400c9903c0050040940400c948510803c111900d000d009101c90240c10601c509009580a4850301e48a050030b0700020518100701f10005038011034540b091400300c0e10000d8000c1c148400b00f01350010305071082000f04081654828a2030399080020f00351001c02c10040d050404042c41119918000c008841c01c84416000828550b800382c4001e080300c020010385010803241488003100074842078220b0240c81e038034403818103801401071910390300c0d4460802c3c0c85402a0f0001414121014024040e84c000751840040c4400018088080e00500204002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 551172886 1250 551171636 551171639
    0x90a0e0307020d021c0506190b0a0611031303061b0305060f0907020a020a031127040609020402041502011d010603030816020f070e04022b02040f0608030c030c07060801 74
    0x48000220354415404481d64006a04188002441c82000c0c00b21090320403031940021040010020f10103004245d403080c40c688a036140710003802103a82410038168440410403081280c00d015004402c2820301c501c09403440d00321a01c43c000026401940300304e49060307864469610030700304801008000c3d821441c0500c480c4c00c103007000540c0ca11711803480f0f030b205805100108020078020405109510b038050240b0031000d64a0a000211422120b5114002c02d040000804100710903250104650041c10340403c00c0d88035a217036000107000f40041280c109078208804660303d02400d03201c1c5002c1d00340781d0003c1002882200c020101c402c0c490035401151381054001e000107500994525488040781c400484001d0032614120315001c00381d9241c16076402412800304048441c0840c5900c130b80c0c0242c403110102c03400b00c3c2843d40c3d44540550703c103805107a0b84441400501c3c2c1034206030000041c001c00070440382e480303030501420f40c0d201d000640a103600c002030000e081c0c401402200010600d504107001150b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 551174136 1250 551172886 551172911
    0x20306010537080402030d02060f0c03101a212202061908160807080f1f08030a03110901200102190c1a240a030213050402090a 56
    0xc0c01098881c02004040b9103107081d0b1440800d9070600003560490000e035100340c00c058060042c040a55040c3c3c020701a8480c40103005000040c0d4038082d00d12403e2802e85607aa0104642c90351f000a840d000d0610f20b040300020340b09159080108030800701c00803041c0e0340c44600c44060b0401118422040030740c0a214200130441910b01080c200c50150290403544040452000942c43d100795216145282c1c550b18141411641c000302d0706114034500c4081103490041d001007681d0404044401c0d0001070403602c0050b00191b03030030681680107400035124450160328a06460b00500944e0800115603001207181d4000e241d050040448074040110100d1a04612000007449250704207800c51130010001c0400c0c01c0d20310709504071038503542188082c0402d204a828010b007036041c11903081d159105044071120154460030801030045801a42e02c40d03d210054012511140c4142c200a42c08181140d0000158807050460002a1100a4005400d01d06841080580c010142004080c03d00d04001d00411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 551175386 1250 551174136 551174147
    0x70c050a090525020c1912050601180e03091c0506010e09010b010302070f110114030a050402010e040b0a051507051203071701060f2f06040c0911030112050c0303030910050a02030601 80
    0x41704020740b1040c402046926101d03003030200b43c2e0700402071822440890014003901140341d9040e00e480401d000c00b4440d80c42c1c030140588000e090b2180b90768008024400803868880c0002c0c07440d000c2035540d10111007041d11840d06110007603020365030154068040005148085c0b0640b100321409090840c140340458451200c4e00c0048200140f00c00500c040c0b48046170f018071440c40302c0d035000540403562032410102d0180a0401514201d0104144581440291030a401f9a991500d009440c0214051402c1c1c03c00410f041d03444c0c1c142d01e030010100144004100180400d2042d1044180300e00d0356414207500c0103003140840b00050000703444503801071240540c000e000c810b8103c51031034520039020400d40240b40c0c0d074080c1c01c0c001b07200b05481070070a10b14190125210388100d0003800c0310120306543d0400301c1e0544045851010044904100501864440c0099603d40c1401002121007600c401c1000c40c3c03641e40180d030400c0ca02e0b449003030713072242c0d4494030b026036503012440500660850400742c002800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 551176636 1250 551175386 551175403
    0xe03120a0b0d020d050d03050f040807020409060b040e0618010c0807030b0a092915090111030904090c030c0609120f0f05070b040515120c070c050a09052502 69
    0x21040d1103401c1c4001950324421110540e0b600100021884c003014500181c2ea11050401d590200b824400080c03038080c01d0700305184c4120303004400e8514004a07582000010820407030102e668544d241100710007502c0b13a00c01c0060030140b45000704940e00300001e2542040c50f50300343c403081d1607060007090681684c0c0040b84603044081803d0118141150f07400044615400b83c04c0010b031241303040200400104101a9a020008000c00c0b0610440300e00040c4040b8030f140500344089d485007005200c0c2d4a502c0b800803820104519425642071201c0400010705403400182c003501c1c1c002d00f40d00d0500038030540b040540020f00399803d19503201454503140c8100c644500e90050000719440d01d4210500c0198501d405000b5800006d40d10616260300f444c4025400500816002c4c0380400b0b44001050398503821a50000c0f00740507844031030b58492401c14102d038000c52003200e21411460001815445c1e030b0b043c2c0b0f00544611680452213150201c1c2e580c0004000303c9801081c2a070f000448000c2c990081513280 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 551177886 1250 551176636 551176651
    0x12090a030b07230d0b01020f1c0e0d03030603120302071205070f150524060409022109010902011e080105100516050f160e010e0a2306040e0312 63
    0x603503070068143c8403802600950842c00840c101c00c0000036440c0b2000707100d4445041c0302000034007502c200480e503400b20700000b01d0303c65014031144003400c04060403060483c049450291410720341100425224081d080045002c60f4890704103200700720000e041403042c0550340c94114203203411510795068056201c0241c4062200c001120400d0002411800c840070360800c2ea0003c0e490880f6040600030311003241d035050a4601099041040d59071102c00145101009052038141801c11044038002e40c4a0f0501c03129540d600082ca1400340b040c403c800388074604150002460300607a00000d44090b11400c05045205c0524850210320b80d0170560243c107450b01543c0d10840b640706d605054a60340f048881803030000c68011021340c1003250002d551002441c140301507a0403424a00c80a01d40701c40c2501a160b0300d020100c00500041c5842c21080b64081104040814084032103100301d40800b46030801c03a0380e039482000400025007414043e1004284640c0001c51900740790b80d8501032607580151010f03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 551179136 1250 551177886 551177903
    0x8030109061e051e0621060a03170306180a09060b09010819030509040e0304151e0c060609050a0510080304270e1905010c090510080714190212090a03 66
    0x1000441c00e19410007031800d00c003070312055444404201c0c01564204160302c64040751101c5000550031f050150813441280e80c8400820783c04400b10081102b99000102015045002e0000214042c0c8101070f00030f010300c3c1c40903400642d11045041c0402500c4903404281e025502071001007204110000340c0542204a01104041d2012140340c01c0b1064851050002d82c410f04100300d480320800c0101c0100101c034420b00d0380c0d05418000c42070580d50390692889400c2d402030104542d1240b14082e1401084061281c540001c0d0142c60b001e61008071001511071410306603030b80c0d0803c030500d9440892034001d01542d1004500b014602580b1012000304041d50b50904103648220610101442d005100c40303800782d10684e0650501040d25035a0b0341e0034020162801d41c03c00403180003581c0680f00440940780c0141501068414424041d240c810018106808000b40113000902e2021400007411041715a070859042d00c0c4c0074414002e217040924044140503a41c200903200320707075031110000740c110703548032002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 551180386 1250 551179136 551179159
    0x60a12060b010903081306080f0f06061b0607050a030b03060114040f140a0c09060c02090a020c0f0706020706020d0315050d0203070e090a060614030a06050a09080708030109061e05 79
    0x12a101c08840e4030080141001046c001980030081c24030000783c503800d60ba1030000356a281d000c600701500c1554240050b40d901d502148490078500d000300400500c000054005100c5009103600d080c6e02180ca540000d0804104500322660602034000d0307000d07088000f002103504084508e140341070154004c0d8419a07860919850366001034014046529414004105500e031030164640070340420705079400040e40340400420540e004108103c0da0a8015021081c0d5940b07440f5440003d5102c440c0c220762510035944416880300d41040b509019102a5001d04505490900064640029000c12009042c02c240c41c51a031044015940812103008403034070440811180046070824070710340c00c140301307450001c0d04000c04c854001492845551041c0e10070000c6959400c01c010381c1d243d80030319080c0c0c0354021442c80c01c04240d55800c40d68021680241c005031500e1240c3c0c5401890b44120012541300780040300402c2090b415120702d10082c000b0203c06001308076000d903001d9110150780603507840741c01000721 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 551181636 1250 551180386 551180389
    0x30801060e0a0506030c030711030c0703030c150903020705090a0e0a060c1e091404020f0d05180703060f0e0f0a1202101a04050c1305090405191a060a12060b 69
    0x2c0400500f80a0304c40d41e642d0a003d012070006900480e40800450054001c004241c0c50010072034041096a9010b40580c50955a00701c849001401d01910340280084044100440900c90b00c01c10314402d4006000b03803442c10040c440d445500070030003d40140b0b08144101c9a460200f2868859540b00b500040d01c410303280c509807031400c02c00d02c42640d1492001002d10a01b6003203d959008c2c0d81441d1400e220b001d112004003c180e114041170f40700c4910007440080726400c00c54001036008030940ca10340c074140328200b50043c0342070340c10342c02580c2c1d10751601c000d4070400761039220f419038429105024103a50b00407054030684e80c118400d801002d950140c001002024400d02a0040d070054403c0c0078440700128204030501c08211103a0725220354036140124941402200840304807003604000520007600e480c04008180340000c000365400d00a05040d5640407610503900d6801510030210301d5800e0329904488411981d00800f082d0040158140c144800b0904c4980d00620030f621580c00f01d4204c1e401e10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 551182886 1250 551181636 551181649
    0x90f130519181b09020301080f1c090e0901060b031905060f060403120306050904210f08060d03021005041a15030a11061612030b060f040b0a02160602070f050d030801060e 75
    0x5000d130100c94130100c00480c2810020482000c500f0940c41200e0300040780c01012100000415804000f01e0341c40c4904100c1c28903c5c05020364068510400024160381e16001c0141c1c5500c02c907503111800f140c80c881c81420025500c102e541012090380c1c1c00440e458002c0100d1303550308c180e010140000f140d00c940401140e01c250801006400003604600c40750401d444e0418035000d030a40c02e041c0c031802c81d01d06112420312551503c08075829540e95502107480700c006125240c171800b5026021401002e100301010040c50085c0b5002c0d0703115603178181103070100e2624544546409006c0c50b0001e031130301c60b181c51a66030004200c004a0f8206070280002c0c4c01240004140d031007103180c4070059070710181e280d41c10700080109800c40c1d254282c500380031210641c000c121b6548640203642c200c001301404248807494102001e003444d452a40102c840402e40769140011500c6281c1c410300040c0d00c01802480385a5144412500400094440b990074264030354024101c05c905000b10002c120309403001d42e4031aa1041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 551184136 1250 551182886 551182889
    0x6030c150d0905070f080318122103040c050102060f160e1012050a0e120304020609090a0b011d01120c120e0102090907020a03080c090f130519181b 65
    0x40340300b006805081e181494840c0164070659854a45580e00064802c0000c411102c02d51403000e8071030604055041042460039101c4800c413491f12a107100348a10302d00380c070703503c5480d4000215029124034192801450640e0540c01550464000a0900c8081d0403154002c94002950031000e51200204900490318a0500603c00364442d4290100d1800c03180c1004d107001825111030000d04c001da46050401060303810b05459400c056001c8442c8202c8609200c1c00381d40c01c00e01c010076980c5040c001000060360800c0070746078000826a80e8842000f191380205e0100c4a0a00078952440392010b8540040d00b0000c4901807100e2281d100d01070f000c12544070f07a10f241c1c1445041001001b42c02c0800003001d00039000160304d5030140c0071000c00f1502c56800001c00607189a41a0b44690340c50350758a90404080c2c000e4204a40c10407190740281c802569603400100d90140c400700c0000c3e50b0302e402840707013000103001e0441c0c911091504042410100d054600c1c001841d1300564105c080001c009600c00304030496 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 551185386 1250 551184136 551184157
    0x60e040606140915060913020705160503030901032a210b0d060b010c051207020103060b030105061c020403081b0d0c02090a0b030a0f0b040c0b0f0a0806010210050406020a09080606030c15 82
    0x46107c01c0c1c00a01c15406080314601400c100c403000c00c000210441e180b4624020700d945580144013000707256120307412011604103001004045000080e07000010610308090441c00300d0070307901c0303c00118595131014446074030300d401c01449980014800b0071420004084003a01c50380e01ca84022036564098060001e03460380c4001203440f0030f00c00006400c4c1640120b01c0880c0002d0038801c0001d02000103400b5281a12001406286448519010305000d0101c801d00035071400d400340800000f00c0c031610701604c10322202d4044036588507401065030b403c1040c1c0807804801d01c415010301d140581c03110110701c1d6102590080000c0c50750529800a890101c501d80e004100c2d8140e41200e000300300a40142c903004612030f08890808644644000550b805203010b006828071081c81110f1141d4420030925820a006006031081090740da403040e0140c0d2011a004d541482d0001004402c140d48000c0c001c004104074809461503042c5140001e89901e00c9104591117441543d103040581c2094a0888991706030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 551186636 1250 551185386 551185399
    0x20c030903060403090f060809030a030e0a050f060703060603020c0a1401180f0506070c1a06060f121006020d02030904091e0b01050102060708161202040801060e0406061409150609 79
    0xe003440c0007054010303103020300c07410b40c8006c0800141d22400781c14600d008840c0c40d0b001e542028101001100144000303400340302a8811446928082a024410b203d40000c1b18400b030192860034100107000d48003240d219108140c410040b1180101000c00d0320907186500424480504041c1a94039000d0840400e6009044202810701003c111950360700300145d505c030704c09441c00e41d580d001050358010700c060400740c0030002c42c864402c280540400d000e9031101c0014000f03420a003140c0d01e0f030700b110b4004074050115140d0860510441c482a000010000e154503c0103100745480054029100e0181501c000d01607900e40741d001040100a54080302840110051278880d0403003400d143c80245428070959000d0f024040109410034820000d062007100d40e01d0421404051029044070040b41c0711a0f40001c041d400e10000ca06e480c400c3c000c860081c040e414200500b402c15092a00803203d059002c840180808043c5d12401c1d1201c480d15039102d01c2408a00c00012210804a00c03140700c0c1410240c2d1081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 551187886 1250 551186636 551186641
    0x8090307080705100509011b03051e070201091413020306060f0c0604032a080304020d020a2601050906061201021306032405030304051c060603111206070f03020c03090306 75
    0x500280400441c3e1040300c031300a642202c1142580d40d0701c145104a40000d6048900700800c441c01c0c121045441c0c40780ca002c0c1d1400364404071108240c14000c1d10300c404910001901c40956901c400c401000d410b080c1114800c1c4c0740b010001420b0440b040350030749136483e000300005402f903071010f00f40e41c0e0f10480d070800f1541d1500504c2d44e8a0325400111402c40c007141040c0e202400c8020801d070007a011320b841c92086c908001c10340c3c03250051030b00001c1c01242d001d50103020041c0141c0fa040c0549008080700c8490002800c03030981e60350b002303019000034151071780e241c0001c108520b0301c000b130583d421403000c0d501213900c0c00c5695941030180c81981a0140d94988401c000610340b58960b01c954000c2c200007061032201d0080c40140d4400b45854403c1c1541a81b042c0018031003403038101c100b03444c012100005800040714903a116000d40301c2070340c010380d0b1220346124180201c2c104002d50019281221004d4812454041c02c0a00325040006850301050707404a21094046c004000722000c1e040002c086643e980f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 551189136 1250 551187886 551187899
    0xe090105040c30060b040e0d020f0f0618070801090503040e06042306060412060e0f030a0c0b0615030a0501030210020d080103081e04060509010f0801080307020d08090307 75
    0x306016607086402000e200d41c001001a2091014030a1492406281c400e8200c401c1d070360110000205001d42c0d055660380c210b00d0042e62548a040c2c0c0c0c01c0c1d1400003600034007800344006814400c98244051164101910800410001140455001d0400c08561a030750341c100144030300d4191541c00041041d880e05880e030f8140100080500100d820121408881341e64140600054651100202c0d8503054803aa505012104440c0420b81c080400f61800381000d50326551000300a000d15000c3c0c8140c1e07551030b500000c18005011000002103400b0045140a90711300c001410301e58002e0014202e28803280214909039078101021015001e800d802d5a220b0500c0084031000342400e1100300e01c00c900b00c0d503900480038000302c0c3d00c0000c04040d80f944807043e071031516411010f6005172031186200780f41040445c04403600801400103001c16a45554803010f018002400d141302d1050180240101d130401003010707403400022a01c400390306444214a101d00c030f1038070021034007400c1c40d925410f015109011428 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 551190386 1250 551189136 551189141
    0x150c0c0f080309120708033705071b060f05010e01030215030a090602070b0609010f06020c13060308040b18090f0103060f1b11012301061d03030a0e040b040e0c01030e070e0901 77
    0xd4600230300200340007a9104408000610740400200da002050040302071200a01e51003540c2c0320007242005450f040501030404800b061a00046030056a03441140581200600c502405482807a08800c0c29504680000700764449880110130314810000000381004c040350042c5c20001d0b0b2150056403030704010302c5c002034401c4007225520b00403082d040000509580c0b00340c5100485d08550094002840198240f03c448090b403881c00c59096101da100000203036030f80c80200024a0342110054861491090071080c81c6140101d8074403d60035207003030152414194001d2411207920000001e5a011040426030180202000c0400f031031103008408016941c0010071642c0303c14808000308180d60048140d0303040c2002042c0501c500402170f2005000c0140036074004450411454808440c032007807500001c0c0345500404000b00010700b01d00d12000c0b2810f290140b440200c2c030854043c003e046e0002c8810390707104207000c0294101512500248000b000a110350000303082c40b041d60001a00c1c0c8081054003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 551191636 1250 551190386 551190391
    0x1403040e1008060f040c0909170a03020a091202030c0126010b040617010312110304031506090f0c0f03050606160b22030909150b0304150c0c0f08030912070803 70
    0x100b90045030300080e141e50b4206a014031655020740940302c0581445005d000078607000d00f0480b1341c001600d034815403c00421000d0a0408000c2d60051b0b968001903000130026201c51340f20641c0d0b00c0c40d144031b40f0010390780440d00202003c0d082c6007000060b462010180f00030102e0f40319600751741c80f040001090140da217070002d00a858085c0c48000740c07407104401c1000300314000d2001800c6200d00d10844070742c06100750380c4042c00c4259503080340e00705912511000141c0c0c001070080040c0f1555000b040160390303503d000320408290689400c10959034100c1001d440660082800d201b0140d94800140710740c1d40303642c292581d01c580b6040c220410192440c0102c0c40c40790a8810440c0701000e038a81101c800202400404041c0d0304d50360300361b5003520f400c1c0d1000203000c0120310303580b19940402003c20f2999200010794440c41c000e185980e4007042e0a940e03601184e40d035015080070042c1002502010488461201c0c0c00c1e940d215068655940e0399911032814020b0f4440040c450490000300c02092041403000f660 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 551192886 1250 551191636 551191649
    0x40b120412050702031b0f120105040b01060906021b190801050417040315090503040312080f0a1116020301023708160c0201020c031c0e0f01020a1403040e10 69
    0x40101c034004100b5552800388020003903040d80004101781d120700d0b011900c2e03801d00c080500410b0307404600b540000c1103047e402030034400607907407202080280160300103080c0c0100464140444030070b0400317800a48458444c203c0b400441014200501180c450b120f90342e0414000101c1802610348a4142901a00d81920705450301c0c0080c855025241c6a00d07421202141d901030640d442208081250f0340140400c000e0a44aa00050000001203101c00781c48842559007a0340e400f00624040b0014540c048015180825841ca00610101210130090848154542e8500c104100f02c1042c0b00080c060711500840c1005248a000e10300d0350250303862500b081e00110340035048a002054102291441012151958500c681a41784a00280900441d000e054010320544212030108004245409031055551851420340b144400001d90b01105503810100e04660951904401d072000035560b101c8800040c1403941e240c40c0c0300000711810011240104510b05901c101454440c0301943c81d60803910801c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 551194136 1250 551192886 551192903
    0x12070602061f0315090b1006020610031e240b0a1e05060903150103030810060c020a060522090903110d1e170a020d0b01020d020303011a040b1204 64
    0x1e0140403101c8042025a00740701041c04a0380c0c95a00c505500e11210b070813041039076540f0310300b0780049000c01031024890321100003944445850030340c0091a18100070083d80d01c1c400640020700010f94500c06140d1034100b5444101e0170304845041c10490101550000c0230103150300c5102680140603500300d100340903402c03584107200c550f582d107044041c1540e62a0891440c05000350501041c42c00d00054204404050215000845020140d000f01c04003a08250003098040c1c082054030b1004e220001c0c09480203203401c2c860041c05a0110f80f5444207030155100b80030012a11054440344400d2600c4d04400700145110f6181d03840040c42c001b801c002a0a500045000c44001c0503d01c000804101c1c08185075519441540307200240c1d1001a01c0041080400c0180354001108002d0045298014865003000507906d504203031f0120200c400807481e20341590030980e681c102d00380d00441a2411119844251030000c0d079241000907091145412002c20203602060382c01c1600c52802c110340c41248100e502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 551195386 1250 551194136 551194141
    0xf22060f022404060f09060f061203020a020603150a0f030506160c030f030e10050118090314132409050306100302010c290412030b010e09151207060206 67
    0x22a01c8600404241100c8442d01c490300150440c0c1031041c43e4814011000081c900d03a100b00c64500703030b800b100c0b800d0381c40071f03110444c9195503c0640704e800010160038019007110071080da0040e4860030040c0c0085d00c100700103c00503480189007001008480c0000704040c0406466500c1c503020319181d0b000030360796032151800203549500d0007041082c0007481910790411207043ca0350110342c1c0c0f088668012040503115038468035082c60401c1056848100752901045940c100500304c850005401c004800d100d080030302d15408a50040380340b06075030031140005951a11100858036910b00c203a400700001504401d0800101902c4401e82c1c560b01c9060303a29011891368900826682d400c05642c024a0003034a0f440800c01503004100705099030b840351142e59044900040c54559500d141e403d0402011074a6040008201d8081000c00c90303040b0074102040b41007202070000b8200b694039030100e800f80c0013041c041000b11007411010030194070000c00000014056100e000e0716603945104000140c07041d0400f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 551196636 1250 551195386 551195417
    0x1e01031202100902090f0709090e03090310060515070c120b150414131401020a0c030f1404030b07030e060c090f0a0305030f16120504030b0114150f2206 67
    0x9180580c0e800800e45c5d01d540d1503000340340f40807602c0540b40c01c060155003e00024659818083c4440c8240f0800c00745d0b443e410608181420075520300c605e040307843c2c1b616105020aa5400c40b403109031340b2550500d10340350300705450074905201e415080110366190082e0410304001a002c0c01c1403240320203140070311224615800780001c0d42c158800c070301c500d204031200050348940c03020300c030040d03e0f07005200b05130b41007156403461401c99001c17095240000d00304410260034140c00ca070340c90401084e00e00c1c0c042034401403a0b160074014051400000c10440e00391010401c0b03944a9080301041110041c15181e860900c482660055400758050070300903110780507043c500e0301d82001c4803001c50703402c000a07510b002d058000340c4040358030100c1e5079051690402240700106644818010014140380c0320250782d941075041008001b40144d001001e644004003001d00c040d01e41c2c0da070b16840344051280d040d40b41c500c0740c82001c0b444d00030780081d0342125510155024035081744014401c1200e400b81c550a039221910340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 551197886 1250 551196636 551196641
    0x6050f1e180f03060103080f04051e21070315090515100602120d020a09080a0b01030b010504060302030a02010c060f021219090228030b04030f11071206051e0103120210 74
    0x30940c3d05400260040012813140c200821190401107412450540c40e100090000d40c40c048a18010f440c1c0492082500c0c00c01080c0701161400400081080802413210f0701d0381d43d034646c003000740b03c865034981003008645190809000c5946c00340503501c0d0544140c5128010020445840f402070420f01d0002405900200f4845840e82242c0c0d006c919100d84610300401230b62250311305000b0400c20748400a00c40c0c41c01e004955100e842850841b100754510300b4110604803041c0c000c103204500d0140300b0401030360009031500b401039081c24540040111800c154005244800701c03004054000540d855085880d01484c51180b500d0104031100d0315141d1207407000b103c1001c20001d4000c801c640083c1440d8030a0550150718200101512a0039503e9640709045144141c400700c0209001c90303002d107595a0864004914100c0e00300042210601d808003a90890714095805405030381e9520200d024031044007011941d00c058011403034100d50350380c80e000c8d0041081d00c801070010300924102107078005090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 551199136 1250 551197886 551197909
    0x1902040f080f0c1c0b2d0a0b19090e010b0915240f030a020f070b0a0e060432030a050408151006120f0c1107090e030406050f1e18 57
    0x120003010003046140d403001700c01c01020701910329841101d210100070b46681140246c03080c010b074500c0c01e07150401c00c0c1c02d941030300c0388488014801d420003150754403039920780d092550858200321408110580c0074107840780109100003000c0d4100416608002d1000060500d040102030152018420102901031941c048080e0312041c08505104000e00340c00e0b88071107405903410034803a00005160042c11100d0300c0003540300540032642c1c1c0c00c500701005446c60003482401240c0d00c2500141119203003540d90401404154400c1082c4481041c901c0c101c0c0d11060b00e2200180c0c00c0c2c420480c0c0c1d50700d005810280c1107800911031002e03140714510f135120030440f100750440d025104101d40010003d044c00b5042d01c1030000542c0c43e1120380e030303038031122650707050a80a00b100141980c0c07140321008c4201a03049040c00959045190310034204609030810020000845003210200e24101e51201d10b124100d904a1107001104844c04541450381c10b66010b0003401015254103548004500d202c420013070002e0840344 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 551200386 1250 551199136 551199169
    0x708100b1201050f011701090617030306090718080601030c0906080a08120615270103180210020a080a0215060109030b06010f1101110c010e01060e1902040f080f0c 72
    0x401c00104424200042c0c4980000814107140000070f844445013100410300340e000b0300e5041d8460804200c506242c0480d990025103c40c040c510b03500e001d1010500300900504144100800c2c8079083d01007902c076055001c0500076200581e60556581c0c00c041c0b1080044c1d0040390307001850300c4c40000da905000214444081d0340700c01c0c40303418280c60f00c0c00d2140740c1000402031307504040356024507242144620000e000c2901d00f04076203030000380303881044e84036050044e6020b41803500c0e10b110021514084140e01107000d038111601030f60540d544d41c04a044c401580802801c0b40d0f008140c5401c215004241180a50b00b2651a0851907a844004544c240d50780e1001811621000c0c02248407941708a650504000b00e034286001100003220540d800c544608080c1041c407c003300d801e514841c000c0c001d0310a400f02000090007110300b0050707a01c100c0c407000b420281c014805210783c030005071000d4041e14001d020020408070141d40d50b5210329203030313055a103204985000d0508070014610b44480c03400000c0c00b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 551201636 1250 551200386 551200417
    0xb01080f0a110d1d120a17061c03080108061e0a0209121e060609060603130f08031509070309030906122901091202090f1801050708100b 60
    0x124038804400038418042e070030340305042c01c003c0d00514180d2800f07034030b2400e03084500801aa2015019642c10414036004040c0d81800c104110700010768005941f43c3c5001e101d440840707141c1c80d10400103030b11034200c3c1c145109940e81d5580345400d1640006c410350403036005800f0345455a80c5c0c501c0390000d1110130700c00f1071805840b18011804042c1668081d110918000d48900101001c0d40350b86e620306502c10042508480c80c2042503060309609001d4a0742060045e10b25469070b0825900007442c1e4000200582c2c3d81d0000140e0580c10b1161100c80d0640342c036045018075a80e420b03c0040075204000d5582c10901403540040440e8030140304e841a040d80c1c68150b5a0629043d0406508a521a004c4108000055100c41000749005d0341c849407482c40100110409285502e40800503000c07403031a80c80f440928030b001c44030a001d031701c903032440541c40070100343c90b850030b50340c0d0300070840c400d04800410809561816041104c1d00741c0099410340a03a0703c0c91070780f02d0030542d9011a04d00c148101840c0310034115 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 551202886 1250 551201636 551201641
    0xf010920030a1814010f0b060f0c2b08060315040308060102160f150f0509090a1b0801050306060604030c0e0a0e030a09140a030816080d020a120b01080f 67
    0x84011010303582107444840081501548400540b0002c3e11001041e98042024504200d0100092240310390110544070140001ca191100003a03907406140c8580c0034051000820031001c1005002d0300340211581c2641c4d01c0c1008100d80144013810070a003c0c0408250004085403540c0f41c0040c0001d10366600326100c006a41d1582d41c00c031100d150180065041d44240804812401c0e001c810329000f9101c203601529100b46014ac4022070411110150400d00c03043c0500003084541c031008991094200f40c1c1c3c013007103507120800090700401c3d1076000f01815014072182c40160036400440c81d4101ca80850803242c81d5218807040010a10451000400c50540b0b06010020b0000c0300b40d281383c1c0315070a1600020050900640241140e00083d106800200803d6050003c0f10145840840c40c40c000d071240142c581c25690340b501144030380f1451074105001000c45504200207001140c0b902603002004dd074580d212400080c1c032009480d95205000c81c2400c8040065510642c0c02030b109200d400d021500300d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 551204136 1250 551202886 551202941
    0x20702091906050607060902031227130c020a1a01080d110c030604030206100f0b0f030912220e07020a02010f05071a010602010e06091f06031a0f0109 66
    0x40c003080006501c80c645640000440c1e90b01c5102406050740120310104082010340304050a2001113000030117050401d000c4003240d0f1013940d03590986003d26050000c40100b030b10000030601c030144000c1071045c03400c2000382821540d0216980528038803607a40780b40050303514502c0c19a07582003402142c480b64002c1d4a4042918800c04100d05050311076801e542c41000614040703070070b108040790150090b074400c1090052103880d46481d2402801c1d41c046061841341440c610b40001e10440c000e0b844082e40100218180c00b40a20a403191149481040b56a8501a00e00c103082c841c9407240074840518050701c0000c101000000a074861a0036134080e10801d1100d500640c0c07804c000c0c54a8000708002070281000141d00c600f140d0005070498000070b50950b1411034001c0c2550300c11200a580d03a04180705020301c020000580d65203800011355511460301c0d10a00120081c0601c0d4005048484d1001030484084103101c9544e000e0100d28294040507030704c6c3c0c8080d1007500d86520b006c942c1a1809070707040e03820 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 551205386 1250 551204136 551204161
    0x903021b1302070804090204030609020a090c09060c110306040b0714070c0603021c0c0512090d1d120709051501020f1203040c0302120f0c27070504050a1d010902070209 74
    0x540d1013100000c1c01c0c6030701c0f43c1d6071074202d030419002122080e60301c2201c00c05500c2c1100340840104400701c028811030403545001002e0b10401d1041105001c2030303c02c440d007002455552000c0045020f0111021440c150811a071840001e070b94800103e003000d00e14000000ca080200c43d492504002d40b81c0900d07141a80c11802035100458641040368664030603000780819010b4080c01c0001551201d8950011400102c660701000d401c1c0055540800c20741700343c4039000401149550076200243c490008840081103419440c582401528043d1280c003059202c00740d4801d41c0141b00052212200060317040042e4ae544407040d800409070f42c024410f80f84602290001907a02502c1542800e003ea95694086140c80c0305090240c1456005260300d0092000304011001d0780e0401201d019127200c81c8044034040c42c45c03e4201000d9006e50079000115054020421a4002c02000d8640ca600541d10090500c0030340103804065600c49902c1c000095040060003500d100f00c1d0001c1c01d2000d40e48030b60340b40005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 551206636 1250 551205386 551205397
    0x201210207081207080c04260c0d03020703050f01020c0316030c140114150109030303021b0601180c09060e060a0201060b0a050c0c090403080c1e07060903021b1302 72
    0x10015020001600001c00200150105074a03c903190001070a003840080d00711000205402141e0800b0b12040256007203000d820002104050002e05a921401901e10300b00112185015000901c0c01540d00c1015400511901141e004030103551501c0f003240f000340d00380e21503a02c004156500c1407102514030f220401602c42e0340761007400c0007481b0164640d51800c610200c00c03044d0445035907491a0118000c402284580e1005044040d1030403041c154001034801e0702207020180801d076020500d442140f180d803416a00040c4041c08444003503940300076151486000904881c450780c10040a450443c2c02440650142c4500707403140c20707041d504c00003400325642242d02d46008641d00c4100000d1441e490000403c0031480a5030350f580c2c0d130b40040d20443c0c50001500010f9008005050402000c260700020380754200c0103003401c444d6550000d10750103000c03a04080803110131203800904d00007004000c0c0c1c85500180c2c4241c00f6a030128103041c2d005041074800010340746d048040d00c0c2102502d04050f500506 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 551207886 1250 551206636 551206697
    0x120610081b130b0d0f110f0a0c0c120215040302030c090718080f07080c06090607080f04140f0909060c0c071e0e09060403050403120e030102120103030f0c0201 70
    0x1402c00034400d0210300380000e00d91100c500e41c6000105000410124058424240380e0140d00348a01d0f008101451490f00c1601d2001103d1000403540071411071081c810344201a4010560300100c649850310341d12182840c50702203200c0e4044003041408034440a00381c4040302e40080c080e09984d180c9000340a10b1240c0100340030100001d03186260464905050010080c011540081a441480441d6140360080c02d8000034a16884100d280103d90b4a00040703540b210030940da040c1e1504c640d131501290340d0203461002c1c20b01413808980801c612503441c00030b07c0100d104482e0901e000144105000880344243c4d01150543c10007030000742958118002094202d01080c12158000d96403c0402e14080078005403107842c50240c0020041a0b400ca10941d030000744410103030401d81019900500688100c1c800100440d519802c8071070107a001c2c500000341d240c00a40255500c0b429400d0400d410002400f04a0100b515002845169441100b0303103000150306031602184a071500d2404c440394000c03000c020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 551209136 1250 551207886 551207941
    0x30b01030f02120103020a05030102180f060903071215020304110409050c030a0c051005040b0a111011030f01140607030e0d1707031b12080405071a12061008 69
    0x45200071a5100074a40c1025456851185505501c1000040d02180c0d00840c420303030040c0442e00082c1c1e2009007a10b000031007140d069a60703180c10300110700a0b00401d07a600b5454061003e00054026200c107034814142c0c89500b1207584030b50355001c950120b0100303442c041c10001c4040070940761030a003a40107040d0f080c0190b007106e001504640c00246407400c0760344121981107036078508120b54144841e50b50f1200f1341d1800c1140c20103040007100190350090300030f1700303003008121001c50700082d100340103090b8400d1150505000500106401c15610380c02035404800c69801c08000280b0300001148101030003000030b04031391920404d51011140313501d41c00c01e0550300402828060000502c00a410041045000c0406803900340c0f6081c043c000c00c900d103c5000914010b510b0060004134941015183e035201410000b800b40ca640c01d00d02d14048040c0c120252a210541d0f0349901242070034050141880e556101250701d55400302032010341d120140d80c90012580c110040b0f025251040100c060340e0007800e036103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 551210386 1250 551209136 551209151
    0x1e070b04141201110406021b01021c0c0605160e040501030b06040b03030c0304170d080c0d1119030e0106141e060d090308040b06010806102001020d0c0206060d050d030b0103 76
    0x106070840c3c58203481c0a440080c001707010408190103000b10030801c001819402040408100040d40b205a0001c205d101c2030752041032140101c0c040ea6048a0040d0044400c001a1030f242e110041c03840024803107800880c140814180c203516040c0100743c16294812039044441c1c50744000d100107810541c0700c0540c9800180034000c5124000c1014100070311180001c0e44103010f81d600f8050410f80b02402101c00c01018804100c0d5040e0354a00710307039069021820001c1c61303019645c80704032240244450a103643e88160b1100302825071540218030010a00c2008220081c0d40d20701000551145110a07a0044c02221410b81104c54009014814001c06001185004000b88031501110301c1c03020304402042520051206010b190300c4429072084003820b14149504100740007480300c03c4010840e1040141c6505008800900540c0400200584034002d640ba507461031078120181ca02550700c00014860b803000105545404100c521031150400c0c0540440701e45c10000314040c0c550000220305040d1150301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 551211636 1250 551210386 551210419
    0x90b1e030a051e09030906090406091a041b02061f030215070b06010311070b04020a1203020307060e0a020114210f1602120a0e0a0302040504051e070b0414 68
    0x940c4501d0311144005141d142c020040241c1021030344490007074070501403c00c1031103040001240c80c05402195410b41707070030680b00040c025100c1c58000c00721440c01c2400001901d485043c941c00d0061085600340003101c1100d45150010307011402c0c400060b40441c010403545061100c6c20f001c02e0a030b4010180e032054a90700498150a003507040c40245040000d010424408012003841c0c0206c000d00e81801003101c0f0074240900b0b03004c2c3d00d0b40540407a0b42d08000ca002c550355411454000e180043d030400d01005a0704000c0e46a8001d40700a4450f1410b04800f00b420201c00b00302032081950503110b60144452803004651a50812000360010f0110328107004a01c60202916910500704d200503042c144c540800380c03049502580590300150b40c0860412030044400c0010385030340c040b031854044105854240081c40400940d40041d42091404042c0b005001000c190f105404020034032000c542d0f1030a4140700e6840c8100d224000d50102c3c1070100340220000d07024182d090305001080d0f042c0044a010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 551212886 1250 551211636 551211697
    0x708160e0d0804091e14060a0e0604090b01091a0a03020123091c33020a17040c03020108070207060c0b0a02071403090a0b0708090f1302030907140301050403090b 71
    0x140305c20340c0f040703444480c48030041030040090740300b20254014814100302000c1200c5d03103154014412010b400000040342a1540e42c0400912a0440030425003560b44245040c010484402d0000843c0c5520100c1101820014612001ca940c103075540b040b45181200040c012170302121282d05041d50402c400940c40da5611501545518510030042420300c46203401d03080701c0214211120101240d12081074000640c422622240107020009a81d943c0125002c0303c039006007031103000024101405020074004400944004d580c401c2e00c455225448015069030b90b65018462500050781c0b014922000031140c994090300000800f401600740610343d80c503030183d08205c1c01018580d50004c5040d5826151803c4960001c09180b46450302d0aa80c5445c2d0340304610601c2d0f0501c1c040d0380c64008420751502e40700700d11142c0c01ca0170700d021512801c210800988a269a103c0c40021185450750340032140303010b1050b58042c41d4140c480b400c013036240941e4038009402050350801414a2259060f05980740e90 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 551214136 1250 551212886 551212901
    0x2010513030f053a0e01110105180c09041e0311100c0305013203150a0b100e0102100504080c1f05091501060c020a0902120708160e0d080409 62
    0x3580030f4a800c0d290002d0302400340b94954403c0c4403841915600d500c2c4014510b80844503614185017000b002030386840180d420441b03072408a51650310303040400c058038040c05038404d21800e01f030084e06d685228a508110a03480155405080d000054940480c1c00341094010021075200717040003801c1803520050242800b109107600d040c080d80720301c201101180d0611446001d00000030540741070308a106010b03946842d03010403442e44401da69011003c580e504105041300781107101d4819083d07140c80c0b0034420107415800c06035070243c0004455032140e1405807008007000c1074103034010702180301000070181c041c25011f88281c4074040b0410101c0855041405070301002001c9035a40102100203200d202c0403100d008100c825540c1210b10040208111510700c5811114640740600b4403640074000928205800c0e07001e8860540f0006102d040c441c8070815551241a55454040312640c031250701d903403403540483c0214000ba01c0c0c42c54030a6685041038581c0801c60050881e2810651070700040781c04c44000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 551215386 1250 551214136 551214143
    0x90111031302030601170c040f1d030414041a0f01090521070f0506120907050d060b1008040804051e030d0206010812040b030f13120503060f0f0d02010513030f 70
    0x7014a980035800d04100d114010442c918442410442c2400038584590742026041e00c102d0303c071180d24403808401c0c0c00c035100300e0711014403c480803084541071581d00c1d8040c1c0301d14160320080303000b5900ca42c0340c6407144000444841c80c240040da070442c010007507403208001009052100101d03000c19581c50320038a50340129109021001c0c1422015000d6142c85050b9111080d600d10200e418000c0362030307807810b03554100c2200801100301c4d03e8403842c0324206400ea40040350401555070b0380900340540f9802402c0b1121084d50708a401d45821601181c031180c00311400b8008a40811040026082c840c4008011601da001034000c003424280000342060500040400141d101340014080e0a409104c03048192492010310b03480c05281c141c2e00b01050200901c54054600e186002541d03a801e1002d25848841d1b00010300c0f51940288407001c2e000350020b0b64800d02071040003459200c0f90400c601d101442c0900184038a5414829500440f101d610500c0140044901c000002000641400031120028807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 551216636 1250 551215386 551215411
    0xf06050a0f2a08040212060403081501021903110a06021206032406010339020601050103112a0a0606060315260106150801050a06020f1509011103 64
    0x2521650000391400107406002c00c241c0d0031841440400108011200d5114030b0608042541c1c86000240030100121400141401a42c041004150b407105545128828040c0000001c64843c4012030340c4904d696582c01401b0040000100424041c002c000c0f08409050701300d510184082d621501641c10040001c0d030307003500c50300034050b90746010f1280300038410b4000d94910900d0803005040b6401d45d0041d184505142da079031000d10b4582800c1c50300001a1050b40d66940321215801049000c03a42c610303404c0ca0040c051800045001c2d0b1081c0901c400f204400040d0b03904100c000300401001008494000310f01c018485c0d10007010490038881420a5400380d803002400c0f6240c160040d045d550904d0401540f80640d80c0c09100d4500128001c41051043c0200d1240c100c00b03c08a042c01811603400440c039941d2500c10006420358454400743c181c9009840d62034103503581c0e0783d0903039695503403a9107a000350700004038420350302d004482c00e6540491010000700d0024020140b00380241e105640f036002506 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 551217886 1250 551216636 551216651
    0xf2d040c170c192706151b0201020a2010050408070b0f0d111804140103110d02030f0d021204030c1502011113090506090606030a020f04030c06090f0e0c0304020105070f06050a 77
    0x8001c0d1154200400c0c040b4025a00c03d0a4100020702d600c500e1240503038080c9030800c00c0347c1964801c00c103601605500030b0603c003501c048040100140002240101d02c210304440328031400c10710400568044500c114003c101590502510340e025400103c40904a170700b007402082c0c00c50885005003002c1c1404030031402d40d0303188024904040908560003c50080741822040100b01c10ba400c0b8243c11285c01404040c20900b000c030006034032400290340658188254181030105000108180c0030040c203a4088a0444401f000d00f0301440c0203034400544980e1149030704102080120700f0581c04075001d0f10001030710010b009518182500200d40390900444000010700c13130710405100e01034219800311462007103850808006403203488001e1142c0000c54000c51003201403c0101c080d2400b070b69114039940303107540d1100d030b00404c21845031007407880b0001d2008001902042001c101c07030103400300c00b211500d9650b07aa001900c140d8080c000403500180061820400300c3d54500c5a64000c1d03d10001c003040300c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 551219136 1250 551217886 551217959
    0x180a03032001110901081e040b150103230907030b070e1309020307050f0406031a07140c060103020613080d0305190b0303030f2d040c170c19 62
    0x1201c03401c0c07118186a242514904042c00b02c01d00343e544030361007441c1915940c2e58401041105290a0400352000346034102444100920007040380d2183c02444c0f40004008060f200450076610360f21800c03404155041a1403d90803440100503030720040d60701c11213600c6a900d0b651202d4608040b80e22030300040889000450030300e0161a1992079800c0c030a0113004c4160a900080c2d00d0301007500c605480f40c1d44407541e207000c0d0b89558006200864000d15902403000c5c51042c10f8800540456016002402090f001104054030b9400d0714842c05a0034018280d580c01d603400d00440c2e07400062100e10080c421140000c00c01c2040004040300c5986640c08103d03414180700c0303800c4404291038090141400c1c08a100981d84001040d03e0348525041903401e5980c0b1520f05a50340c540300c1024040704262009500725030010300550484c007480c851030400ea034080d0380b0000d901c070000b07044038107201642281c400c5c19a030b4030306400700c2010940400003e10038581e682c0c01500034007009006a40c00d0b0700103101402d408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 551220386 1250 551219136 551219177
    0x3090323010605090606120619060815010507080a03050a0b0604060c120203250f020307080a140a0803010e0709050a06090e0108031201051005130f080c040b060a05180a0303 76
    0x20082aa103441381c0307081540018269002d0314950240510b80e03100080d0050307a0714191820b40003100340100c00425156180203107030050840d402d80181c8008407000d0b240c3c0d4030410440368165002600d5608100218501b00c1c0540400f0b81109111a00e4600c4140140d60300c0b030003040141410b48030304081c64907510b00040c0c8100d02c0d03610942035400c00d110006411380c900300d40324910382404002040c49121403a10131005800c486c000303074052040d0707400464001c0001681e000000c1c092407250303000005e06034945030349440b48038004007410810701c01000f4801607060a0740d0412854100510140d8995020071820180782d40b0031400600d51040410803d052015194090680903026510740807827901140c402e200103125484c0a61084040e600c0c03013502c10310a407001481140324032000c0b01c1d500c0000c101b280440780265416130040c5c1007003034002e01c1c29101c1c0c9012440043e040600b0030001c500180c1c0c15030010b070302e0000384000c1d0a200354603659a103500031014510035250300c0a5849207009601c079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 551221636 1250 551220386 551220389
    0x60f0614010815010c03050c010c0905030601120f031d030a061a03012f1b06040309080102070201090303260405100606080f13060608190203060a1413030903230106 72
    0x5100b050b1090000125030384404501c99902030814030140c54913840c007100e0764816241c60f1034255180c170301c0f4160290303840004601112003c9040b145143d0b00d0b1100011070190780d00f4006c050360380c0002401c0019004004520040e4540340e000b074a81d40b440000b00c0d0610001200450300145c3d104212101c4c403c0900350310304e144405400030021601d4000d007a45c503901d945030b80d010700801c000f0005d80d0020400ca0031101d20b441d1180030346400c9031083c20816070752342080e1001c80c00305000c81130102d1a00c00503c291036071540c05954070060300b40340d40c90648030130071a403019103151020802680c0200c440005200c0c02135214a0040081d810b036290036004485039900240100110001445030213101400c14903000750380e08040c0e251074441854000028003043e44207444500600001c51415054056520703000790003079069400766038401030540101c5014080d0781070180d80c140702060f441150b1120381849c2501c02c2c02c1070b04403540c890300c07511500c5100c1d0505102309a1200035011411100380034050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 551222886 1250 551221636 551221639
    0x3020d1505101802030a1d070305240f060616032a02030318010306031e0c0603022b45080f0304170309030c0f0a0302031e07060f0614 59
    0x2c076401c0440401d445400e840c030401070940c01101040303d0008a51295203425101c0202142d011000814552100013030b1009841c40c2c040d284000e010407270b0703103441034268041080030710245684201c0e8071502c100c006800a600b026040c8140029804c0c002440c0f19018001c0c0c4400141501c40944508102c640c81d02040316648000990030058030004155607069002180a042e02c0000c200102c0081c5100d600c050302c0f0001d004141125900101e18046d14603000e220542c940a0b12401d0507001d82c4074100280a584503480c1e40c0000712a00c030010256080703140c072008a180022180e03620178000700d000b07649003c0b030002c01106585080189403c0c0b180325005042129407001d50319240340c01d01440084403500040007001a08210311440111048031381d1542d0240c503402c1070f048a0796250041d119548840c441d4842d091042140010f01c0110150701d81d00540c07a0045900c280007449156160080c1c0c9090180700c1d02c8000307899402900da0481a0000003d0fa81d440e208102c048054a0440103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 551224136 1250 551222886 551222911
    0xe0a09060501210e0d0c060c17070e0315150109120201050403060f020c070305100b031b2101020f0d18030c02040c0504030807050f150c0a080c0403020d1505 69
    0x800c03190360807221403e2024640b045042004541810b140e010b800100707020b5641c1d004035003e442c0d0142d049446440310380d0041c0c00400801c2d4040406032500080100d49103200b00c0ca0340001414948242518120584040d003030b034840c0401245170010110055882202514100302c042566591002408c40246061200302e03c8031895500064030070f101c1e90101070215600e41c04041201c406a030121801603071b9000458401540d40c2c1031064446103107030040d00c0b800c5c0c10304118000c030b03140000d6401382040c00d403076110210740c1c44c41d41003114510b8000010b1114005e11402000005002e10240100001200300c0d1907461804054460480f00303050302c0820360461200380900460ba00c220090442da07419a00091150a100c03015100c9000e0382c0c0c0003d128880006626007040400300d100100c40740c0390000ca60740c0712080786074091540c1007195140300740c0c24244074460b60b441c880d41c9a5070300600090401d51030691240c010410990341c6007002c0c0c4e4070b10f4460114803000c115034402c00c1d03880300782e5507401d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 551225386 1250 551224136 551224139
    0xf04170301032012030a0914040b03122512140a1b08040801180204060b0703052d2208160905101d0405011a0d03030e15070e0a0906 58
    0x400d070403190070901c0c03124070401c50341c032515558651049103166004d01d0340031240c8031b034101e80008144203a103001b81e40380610b549002040c0d600b003a01942d441c4143c010080c3c0011082e007072410a01e82c000302c0f600b101c4c0809000601f200b81d86000501c2d41d1080c09080782c1d100c00404103030003804100c0402c1514960000800c684041c0340d0340030300586c6400075200003c1d2244401ea080ca10854040d5801040300c13940392801040882c032014507a509032610a580500441c3d80c4c585450040340035452024001c01d000300704100d10b801f55200c1040111020840304812540d00345c1900304030341c100c940d5828141c103445044070310102c6010b04107002131030914000d004a41142c408080e901401d4415200c00540b41d4010400800d00c00d9401000340c480004004c21140d04403000d0580c80205440640c1c0d01c0d4641401c96042070842020404d100c071018040ea030490380242e0f0228014101c00c00d07602c00b01c0c068040140e0307400314502c0a160040071651340e0701110303c1031101002280c1413154411311201e45071400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 551226636 1250 551225386 551225393
    0x804030f11091302060c0a0b0a020a17070804170f0f030a0f0e07060f030e0d0207030209010e0c0f09210f120c060114030307050a03030212070c0f0b0a09020402030f0417030103 77
    0x3031040d0f24980c19102242c0b61012404410701d40490070b00d00900c107041102c100032030400700d5400b60002c107a890341c0d411414911050500004942035401400003078000340024081001500b07012440031801c68080e14001c4441303d41a150740265145070300a100020511900000f80d000d950503d401e011000c00401510303036121a03403944644201e000384031810040710134041c001da000206070741c500e030256007010190040003921603040d80000c0f44100d088000210b00d481d900c240491041d80d54807000e62134000281d4480745030b41c102c50500fa900040b950b0300c102000608030390000c23400c10080003e00300b40740341c3c0900310b04080500a00640703406003807000d450746980c0014141c0c115800c00380680c2000c420240824114440d5020250013882801140780405030b059008088000c840c56184103240c0352982d040f01c05681c0d021018003e207212400c150003189218002c00c0c0c1100c2002c00000703040a055000c2070603604100c561170b600c142044100428401040442201107003d250b03c14070315811a42c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 551227886 1250 551226636 551226661
    0x50f0a0e0601020a14030901170705030703092904051b130c090b040609030516030f020907050d091401050106020607021c140c031308010213050f0d0804030f1109 71
    0xc00d480210001002240c0d559000b4042d41001030f4108116190510352080740741c1d9654055000303035001030701219508203c41411213015008080340e030740d070a00d95110702004034090842002c040d80d1140854042da000d407000e0082c41c074009800092001580c7c0340a0030000d00f810054a485080b00280a0781158541d84511241b134000610080c000b84001c12090210f070800d4075030b000013919030707000200415410703000005070301102d00c80e10840d0401c064007002044508103d02c402440e80640f40c3c08103005261a88086501c1000c13890700a0034214030402c0034054a141180c01e1340c1440883e01ca807072840d082802207a0150095000508280c1001580250345220212031a40351505d26444001e01e5845047d40c00707130b01914090301544806c580800c0c03946a0380450f429244040d181c06002030482010f0080e54041484032081ca00000e16200901081150003480c00358010250b004000000700301c2d10240000d036000c1c1001036030003101440e19040390b200c03950f0ba0394421000241000402e11700e00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 551229136 1250 551227886 551227889
    0x14010b07032d0816020a020f04091511040f090504030e0607050703020d0b150f10030e0102040503070e1e150105160b0f07090909081e04080f030a09050f0a 68
    0x601d421002c81c40401c001c107490616409400001c00701c2c80e1100102c1c50340c8151401c0c01a901030003001800350409205a03590008036000942120f82c01402c030800d8507282c0d000c0f80300940517a8240c2c80503a51100324100302d441e050440c03014414081401e0209010b800480b0740503016002042000f030130262409080101c800c20010f1141e5030002d5540704208041c00440001c580c05403100c800d04500e032800c4070b0120000c561074080d80740c6c07000384528245400f12018600001c0076088945d4a402c081c42140508412140a115036400b04000a19610204082d000422588001b00402e052101c0c1c00c2c03000364000042e071004004480301f403117484100400102e044500c03d09000d50749254410300305031a81c3e2811009840c0c0b040c4a4101300c2e00750a0030101a2091085558103201243c880040100719910104098086141400032514001c1503e074801400d4100720038640c14980c0d0317801d00301d03d0034460400c024440c4c1c10114001c03403070503000700380103020780011140b11850314810b4001c00e0b03041d0102d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 551230386 1250 551229136 551229143
    0x608060f01090c210902040b06190503100503060a0c0e060f0f090a030f0c150c0c0905100b0d0b2e080c040510081e13120504090c030e0114010b07 64
    0x440c52074004003400b407070400e030341049000d40c0a990b02132048120002400e03030010980c003481c10030305492002c1c50000212600c0189810010440340c085034003ca0f41504010300303201502604410202d011f03941080500c2c8500c0c7c4000c404120b40c071620034000c20f080b186403506401003005211684c80451743c0005d5a0b2410340ba410b2503515022110002100c4002540c0040d045150802040c070a0203905401103040c1d0b2100002d000812203004011143c2e4146004017421180c0408e805002d50700e001d8001541001c0000300036000c0b42d07298811800250b200801c021b910540c0c1704109009806d0035029846040c50305401094442490746046d0b40d14203540006200300041c06000603820184034044c1c1e4054440a010000305000300d4001a0080105440d07003950040345012170b80f500601c5204240c85280a0344241000d504260381e201c850590706d9403110240081440f0206a00245109032244280e003030b40d0118001028001d0903086420310301c1b2500681c0f007400c00510100f8056001c032035900e5030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 551231636 1250 551230386 551230391
    0x62c01052e150327060501050604051c0602040e0709090b1005030a0213210302070506030903190302070f06091e12050d02040509041a0906040b010603050c07050d0807030608060f0109 80
    0x8101d0200d0040005105940d040300101c00b0b072012002d80190341c41303000b80c422002081140d8859041090741d008520030698005105200320899200c003152a4a4003032103580050704094844030680700c42e400c201c0c2c008001070b046c6402000001100d018403449901c050f641c189804940b40f00080a510000f000c46008540004101d4032000010803100010170010702d82c461050134810782007502868035a02900144201032006c5414542402240c1c01000008015407a000301000780402e8095407811701c1041c180c0c02e2202002141056049500d43e40c4220b40c00111202249000b4200d09250342c14024900001c60448000076240e8207865107404144c1011600c800034000c81f10068410380d007009400082020900080100014401c410300100311030022490f51850340700c9a40d0a8111800f030820000c400041008900903800301d41c00404a0300d00514000705600e64905d410401d424990018503803200700200140d05204440160a544001c1d2407603007000100e01049880600580100a5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 551232886 1250 551231636 551231669
    0x403080f07030b1507021c150c0201020c0304033c020907050901090915270b01020d050306100507051b090c0922020c07080a060c0c02010804062c01052e 67
    0x547c0c10443c10031681c4d030181d2020071000c8519180c5110158410300c40805401c1c40c21210346140180251064071002c08000e60501e07103943c440700700b10141d08008a19800c003c090003104107541c542031403c005943d980c00224171006105102d07076100014044004c0103014400180c20b0381e440030401049602d403140214074044540002c1036600425800005805e1404142403c89000304041114140c644101008030b40016401a42c030798242d1800300000408c10000a030240ca04119514100e0141385013590a00e84d031507848514040b08403044200422040c112203810b880c08481d00350780011001c05407410403022902017041951200207900b40034642001020940b0020b60542d0a0310036140100d801d420341d1205203d0b117555801c001550900d0800780d40090340b50041071030000c481c1e810780d24010035039560780b1168001c18280881d4207296100691003025030a1154210700c00c030310014000070340340c00c005ca00c9001040000300145001c04d0010b038039039404100c1710711107800c50388900040010b2a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 551234136 1250 551232886 551232889
    0x30d0e0d11030c040906060f0e07050307120623040c09120803060d0f031707020a0309060c050c090a0c080a090201090b21040c0302011701080d110102120403080f07030b150702 77
    0x10103085050300641752007a10300074000c1b00d80001089410018406000d1603c2e01800000d0003022030307151012450800100720b070184100300300b02c90065400e00c0060480d45907454030920740440001210342a910304030500c0e441c5014819403102080d241000001c10345004480751105c011020080c01c410310110019043e0307250408218049030344003030b80701001c850614028100d180d00c1c404204010400704005416240000340140f0f035580c158450224071480c1c04001c803443e0040da041100c0741d000e64450241c11740c44050b481d5009064070ba0021604003140d41009140b50002400e4543d40c0c0e0901200300d000d030b42c02140030000d803110710343c0495507071100000380322500100304190940d6090301e1013000288100030a442c002c1da03100b41e803402901c0c9122000d950544074207018100e05508074515074042c00d40603500909061021038000760400891312218108100110b8040c0d01003003071002007169010424103411350040c1d190070708009200094020039160000421905410400000d412055 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 551235386 1250 551234136 551234143
    0x3120d1e06030b0f06060304060b060909090c010e0103060f120c0b070614092109210d1403040f030c060605032506020a021f030204081605030d0e0d1103 67
    0x44018400c0d06048044448280000c0240740700070303600c00c03403140d0102d0b4800f0003011865000305002000b0b43d06580711078413400f0081c500900e195510503000c000045040c0c4030701e0345040c4103034820f2014001c003921500001d0302c840e000b052628100361408a0901581060740655000d694940d024008070702c0041c03a042d001030050360050b6442c45008160309042005580001044272884020b10143d0b80f18600110f581f2a01f60b44680315000300c0b2000d042942103c0300c041e0411135801030058a44020703440014112042c0c0800040f0b07640c100f003d404031420340096611080c480c100b0300342d0741b451030030303031950107a8500c5d01310000d04000c1c10940301c0302400f441d500410054030005040d109404c010700144101d260b0172120411040c24a0b080004401c0d00101c2c9125105401900030003900c10711000614600940c10704007001e0603401d020100d40c0010800c0102440015046a034442d00d090604244c50083c0c0b00003103508000c02c5007418906070f00c4401d035200c0c11980c030058440041104a001a08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 551236636 1250 551235386 551235401
    0x41503020702061605070f2102061c051807030c1e030602030702030a1d18060a0305070312030e01060f260d050418020408060606030405150c040e0f0603120d 69
    0x10302c00b03404101d8404d031001c4004910703070040c4208112081143e9075015030b000681648502843c1006000c132282c014061901c060502601c010462490452010318074200031034164038004040b81c0d42d8042103119042551004841c0742c1a40c01804c401c1d165a44102228880c1d004001c3d04820b401d00c950f1410001551810107075030300007415500c030b1030800d030000c0d41d070340140b5000d0b0001030740f5600040203000001401561202c3c054100d800d50146038181c0c104000c40a081c45400075200702000020030400e11040000d0351144880055040310744500900b90307404841c2c01d42d0641d14041e4200801104da18002044403008687da040300304080a601c48442d960340384650b1140203407034145803225031000041081c0c60303580003080d941e82510209241240224060b0641d154002d00c04910309240400c050341d40a031040d0101c0c0d20100750700542154128068518032407045003c24180300c544044a82c1940c00b40440900200e1460508002a40e811b0341c405c0c03188400e08005040413541400307800c50f01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 551237886 1250 551236636 551236639
    0x24030212070e0f070806010c0203100923030406141215191e0b0319052205010f0f0c120e1005040f030f440a0507110a08041503020702 59
    0xe21850106081460f072801140d0b8180050304190000d103c40d0700034001d0202c141d4010780200010030390040b42c4402402d08242c150b801e03560050404140710f800400201c0307103142c940095511640342c404080c1148403142c044c603214000601600505040c0441501d0703204188060542d0030150307083c0410680d22000c06a205041c0a40d8030119003081c01c0752000300c4c488800c8803c4075480c4d03a5070310400001e00040d00c001042c1c182c46081001c18801c140c00480d0400388151034041056110b284142da00500034030300f10f81c5651111100c2c400f1030310318404c081e40383c2c0301e24100340074821b00103200411080c40942c1103000141c4c4c070034040048900070401858084030300c0c0400c1080d400e080c148040c0384100200120300040070b410003100664842c200c0104034000780c145404000890220509140d0000c00700c0c4a03490700003040e444070320800345204a00602c00b9031800152410401401070049103110303602e100c294402075410300051002400c6404584c0399403401c21030090b0b0f0340000c070082d10506d80c019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 551239136 1250 551237886 551237909
    0x2307060f150e01060f05030105130e0706080421020a0b070207092c0c090109270614090607170604060305030a11010b01081501032f0703032403021207 66
    0x10398081d10800c0550103460303900e84401d80e241c1c2d1310002190030926280b131010002d034050004024a09100100070020700d29560040364002c86032580b58a01007030b5500c0000011460350501c404c3c031584201c1441401c6402c00c5403003000464580117503544000040080140c5074200c00584443d10a020721005010051401d022800042d80700c552001d03269010045900ca80c0416550303250f43c005a41d0581c020050039001583c2e1038418980c0080001c4201e0303041c00041154042c1084082c0c000c4603482c24420440024150811527040905d4100145004069400b050500000c603800c0407601000802c1302090100a503186808240540000c0d400204503110218442d080250440320610a8054880003002401e1040004491180b001d480c3d1282c001c800602a442ca544640c01c10400c240c61400707425010507141191014500041032540344110000c944034007016494003d804070003c10031185000088007800e02d100303800452000900c1860075081e010b460200c10f1251200800014441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 551240386 1250 551239136 551239151
    0x13060e010b210f040206130308031003050c0d02010504140d05070311011211070b04050f061f05040501030804090c090305151b2802010b031603030801062307060f 71
    0x780310054006001d10031850480c4200810000385107080c10744a081c2d0042c10b2078803511a5003d10180341d20000035040000841c000200100f225100154002e0404030003210b05940395091240c00c00b90150300491003500b030180d4503000b50381e0202c02d40c0c05558416003400d00000180d0300060340e8442c003040050180c028010000b040c081004c090b503440e0340d03080c1c9a03844091b956010100880d181c00000856400c000e00080012030b40a185c02c42d800b0b840340044400d040b01010b2000d18000080780c600e084454807a4010100c044001c50f20b10060a00b924180065411a51042010300542c042d1a15103a40d90744d034140054401c0c0f128500460700601030700c0715201c48050004540d03404485032540c90040801d1a104ca5a00004503810700032002c00070040d0745544001d9904010001e25400215900d54842135182d40d01400200080d45044605014013850f6250241210405074008410f11801600c1c000b0741042e0150025060090000066510691032400c00300800070743c1c0010700082e01c0d0186 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 551241636 1250 551240386 551240399
    0x1060f02150a022b0b010e0306041a0c0d051312170112020609060f0d060f050f120c030706030501031e030906050304030903060f020c0f010510091107020904150b0f0108010513060e01 80
    0x160043c0d174400e0341c840c603140c2d6601c000e00d80e81701003d96000b441d042c54161250318009607600f40c1500801e82e00000d615020803921564191a0241d40304554048104004000c01400811103416840b8606001010495040c803442c0135030414813a15110351032003902c0c03500b10359071401110020742c0f00404407501d58060182c0601c0b20b40000a42131200c4d441c291010400101a091a104480c0c0080c0710703d012000035814024074000320022140382d44140c02c100001907400f03205600240203565800180c540c5142444c000d040e01601c4050a070284030058800460780c0048a4402d8070158145189d59454900d030031a5104034139400544014540581d600d01d002c42600241510100d4600301c4135224a50901c0c0c508a6034240d680e0749a20500050800c000d050340e41168540249280d1582d0410b141038011950281044904440d07641000c0b5181d000c070b40c0a40715410409334150f038824404100b0700000b0306101e80600465104100018007102d8059040d0401e83c044c005541c03084d00380d56542d16 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 551242886 1250 551241636 551241641
    0x1b050a120c120e0f060d090206031302011206080a02010c1103100914070b030a0902040e0a0303201c02090f040f060f0b0c0a080a170103030801060f02150a022b 70
    0x10100c51031400702c941c80c030071544941440540154001c10304054010038a003040301d140e020001020126840c5c454100c00360788c55501a5120f40000400024561200c0c40010000101e40c40d59804003860314000740418000020b00c940d4243d820301703080b03d48050a081c1456400340d03c194a42d458418000030400c469080d8101c0d90310b013032044184007161032840400350349810f02e40c041c4200b401c500388006113868106811180c44180090b00004500c0c117000441400c1401071181a0046501c443ca060240306c440b88041144c00f03c0c0708103043c1030104c0c0801c8101242024441c845481750042003a00d03141d0b4848080c513001c0d0307a00404c00c0041201021000d00900a14403900903009549200040c07031507422000c441c0300748070507809050700c4c8101c1d039034100710b03030b000100d8040400802c03242c040705115080554501850080c0c803003640941c58030200400c0035880721104411500481c0d110007a0000180b0206c0c1c01c40080704d1301503180e0102e000751320909503c0000c1c40d9410784001d00625203012155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 551244136 1250 551242886 551242907
    0x12020328030f1706061b070b07050d111504020f091f05102114040b060a0b09030d0e0310020d020c010e01060308180f120d020c030d1b050a12 62
    0xd0700c4145001c41550382c1664031001406402c40c0303265140300096042e2400f04000d0205064840c1080180d50010b0f8181d031402c1403c0d0000240d242c00000d028003401010000280c0282c6503182c015203020490210580382c082010a003240d52071120089000c55403100c1440e0011070780601140441d2078940c40c10000606000c200f05041c18210001041d581441d00070342d07140380e246032110300808513003040c81600d500c203031058038140c55503480e4140d408040304040c0070300607402054a91300e40d0410b03504000990a442e400040d16000410604032640c901045503c01100e01d424030035014450980800d00308800607503822602c52002440b0034040510341d020f0106800a840208002c46003000c86a0807240340b80000343c0010024003030520742d950a002c0f55466020b000e05611480c0c080760000c1141d1824108907181c064220805082c00950f04109480304800100c0c014a0030f510200c00260400325844400f40c010070034000c000042c401d04000c2c02080c0c940c0404407900c82c421070701d002054511907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 551245386 1250 551244136 551244143
    0x80901180f0311010b0d0f05070b0318060105100905100905040f060e090c3003070303020c1b090c07080f070c0f080102120a02090d0203121804060e0112020328 70
    0x3032401c0206650b20510400f0f141700d0b005891208400030369116010007169242c001c07545482042c4000c10310300c6130280a14040c140c640d041c800d04600c500304007410000140c0045003d00600700c104d00e00141d21044d1300382180c60a903102d070400795001908480000e8031303401190b009410005030511425040e0b1000c8201e80d40d0b5442c100f425100c0084071515094200200c0354001c0c4081071040700004001c40803007030300c0c0c10181603c580e00c110071681800d5401c51841500072030b50204032041d0520080c401c40921901926017104071003c00350026140700c801070880e8061840c04130380f24040100c02001c4a450b0b0100c400c1007520344400b45412031410005024201c0c10701c0f02101c0000f2204014001d644a000300550040d4803a031700c10311180020b420400d900381d13006141c5001c44000da02c00b4401e00300d640140400e8107030754000400c0c84034000da1130040b4081c061307480c0003c2007081c8524241e010b419035408600c148803003c0f560001914103a003c2c007600ca6003007604600e448841c0310311503072110590312 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 551246636 1250 551245386 551245397
    0x9040501180f140a0c020a120203130509090a0b0601030902040f020d0605010f02062202180f13030519030e032808010e34030b03070b040f0303080901180f03 69
    0x140c28008000d803042412448125039085010842c01300403a00215442c940c2407044440d04501c9480d07400d008103c04040d000075800c0000c101c00e103111041c40c8000907200c1035603545000d0a0040e0140e594100001e80641485c1088000c00c006070312a81080030031035002070040c491250800b07440002940005d800528507480c00314005019400380400c01c00c07101c000e4020304020fa485400e590141c018010000b20100c009118002c01030741e8a00c3e409001304103a09440c10103241c40314444400c0100541206060040c91248100083d809000c5030031018440d20003400350780810000341d005c0d00c8004089880b501006c10340c1403450801000c041c5030030500312070041220f00310341c000740c5154900380205c3d9504100d180002c1c11481030304000306408545190600030f5110380c00c10000d1943c005046402c00240c071044540042c0c0b80400c0000c01070b1900d80382891609141200d008041d0042d0f01c4002c081c80388010008111400070360203208410390004645115400390f240c4141505020300d011400b003030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 551247886 1250 551246636 551246651
    0x601080705032208030c091011030703230403050604110f060313030c050d0e0f091509150406030303020d0f05010b03150409050f0307020307060509031b060904050118 73
    0x1845464200c0c01045241c58003840c0d52100d284000c1c414126500005501c468900c402c1d0003d908000258410310f0060589511698805c04000d04402c1640d070740d408000c0b5070f501030794000034080100c0741004d030300d414800c28544004400e8201e4403951158540d040401040000500c04046032051065109140200f412042e480030000f40d0702080710259080709050001a411240c02c4151613107140c084e0504c2148000650368140c07400c403500d039000740002d002a0417200141010303205039400a204072041c070118540b1400540f0700300e4107800310030321580082c0c1c04546009070300c224001c0181760242080c0301ca10340700d0a0150207035102c0ea190f8a80546454262041c8480c0740c41313628117a503848206246141c030385401c40f09011003c045070ba40d0241d5503603100b20000f442006016a2003011401440c3c541d11240100340c08c1c50203e92002c0140b100401c18000255408510214456000412986001103010100e5800e0042c038079500d4100d85043c00200e0300c040390391003a20005003480014410305 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 551249136 1250 551247886 551247889
    0x51b061b1e010e070f060507082b06050f030c090402151207031e0c090b03070302090904050d020609070f06050a120c0309020f220e0f1c020c0405010303020604062f04050906 76
    0x305014443d5000180040c85400000f0745100010591400d0013084080b8000204413102203007100c000a2440542e038be20300421060404520301125200100d002c0c004203444200030904204000744001e01c51414440c40640c20403082c4140c2d0f500e0301b08040003031032501c0c1216000d00202104050004200c9009604500c02031080c081c25500c40596a1100c01513480c09401100329003016004209140c3c00b80100f01d4580c4502c040e652245000d800104000000340fa406424994040c02900e1944c00400c03007030206c2c1e00c80e01c4402048421520300255240c200f02801c445250203082080e8540381481d6405c40d1040c1e0607000401746134000c5a10003140ca0040040201035400c6085070501c017106200b1500111655501c00c9020b504080192011070790b030a2900c0e13003050f640b40c40840d060411001101121a4100008032007141d059030f04111a50441d20040d40e100c400800c024001034803034107460700d182403042841050b142080c210359490080c040da44000c9411500542d40245030711400282103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 551250386 1250 551249136 551249159
    0x601050a06120507030e0f01150506130611012304020108070915050702310e0c01050d020c0c040608100f06050d0f0c1a07051b061b1e010e07 62
    0x440d40c09460b030484015004605101030080140110203250b43d032032000014480601480c1541d03130003200000fa0303c2e8614450b1034064a0707260012800b500e8280844491400c4940c0d4040545c6ca0ba41000310310107409440e007901410b41c0c19041500a0340c802003014411182d102c9550055200b620740c000075a03590071040f9020001c5100d1001900c00118443c0340b02c0e4022001040341c4e030b00190045141200c0e10b18901d20085580c412500ca01b01d140c1860b0415403803500c1107100d85500403001e08420050030000030458040c41c1e0086a01c00e600040c1c1c107a4104040000d0b0080c450041d00074050240d031104142c0d00d45a500c807034820a5810201004004413180c4280d80a440f40100001c550050544036006a44034404080700d00c000f0b02100490001401203001c03a0818100800550b500d941d86045030424889400c10b00c002140705182d24660b0380c4143c2607500741c101015600b4691803481d06903074500540307d040b60342d09012041c42801c8002064110a00074402c02088902c01680c2e80f154000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 551251636 1250 551250386 551250389
    0x15110406110a12180302121e0304050f060d1b020c1306080616121107141c110106050a08030d14010f090f0f020c0f01050a200702010c0b16020601050a 66
    0x80c1c0f45030040c002e41c1c0c4a0142c4035507891503c5100780e00110301d4a036800701d18843e07995101c031411548024002d04180412070b4440002c061035001442c1030628090103ea41c0740c030140c111512400c408615001e280c20150300811072105003d400c3c8040014a48000e5100e1310b600128030300580c00002c1201450065000e41c60441c0c2c040c074000c040a6503203120101d0351243d60003180d010800181c03880514000c183c01280803109440301ca49984905600c1c003031858540c500c0090340582c102c481c00c1c54044070f5560000071420f5084c2000032100304080f4000b801030005801c02980001001c4010801d41d1001010b003403808071142c0108600340301c9129000c80c0789405d00c125501901c3c0b594061007078902ca501f00c0303c44110043c00116402045940c900140d03004000280c00b0b0341c0c840340040d043c03080c0134007800e0f4000700140c4080202c030035054a0800329680000840c00441c1002030207008691084100d40c007000d80100b4080c000d4100b001d012a07003001c0307040310f840062061741d0001c10203103081b040340750 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 551252886 1250 551251636 551251643
    0x902010f140702150712020d02070e0906070f020106210b0a0b0604121a040318060306050a05041a03060709151b15110408071e030f0f15110406110a 65
    0x42c1030020315420042c3d65032189003e0000110184116000244a035404e0003410070950080c10071506150002842c000b2203a000303155401c092010b104048201144454201001d0314105001c00e001a0060380541099800030f0b400b100804860501200d00f502c100010030b2003541400b00c3c5444292290090f90700c40061141d00c01c50400c03007008410b041000c03004049101d4162192840c0000c516500900b0084505078081407845284000c8507980e0941800a44280c1c1001c0000078100408a105100e2600503e4003803a942d1405c0c2a05000c05104001281002021107070a4542024010030144951242207182c5d524104024107083c020786060102e41201000e1300145005a1030703041c020740303020211000d42a6107440d0300c2c17800c00d0860014070207404050002c4c401d00745408181c550b081000711507510b04000d00c240c1400010300d0800c044c030440381c00010a440e54031050801d10228107403040854501840c100755507401c03c04903006001121407a80b10800c0e0500981202038403100da011008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 551254136 1250 551252886 551252927
    0xf091104050d140d050c060703050f0c1b0601060c05100207150f020705010908190305010509040210020f0a210f09091d031c1d10200703030902010f 65
    0x140601d08012100c4181c0b203004000c0d841c45510001c480300d0400040d008058002a40000c5140001c9030410520fa0801001c0c9410441c0d46410307506404448006003180140c3c50000411100c88035002554032460007900341600c0d881c1d40d40d40b0001d8055804451304940a000d0f080700c84280c2883d52007507c995540007075140c111031485400c140010911841040802e5900303200600125001344115480107110380b503c0d59413140d1242c01e0038401110110b40800b09410540180300315240c0c1c1c1103003900140c3c1507807903840584000070240c1c01c01558500c000000d01c1035040040c00d0090039503041104980400c0d010240d007a0034074049456102c44003610010814034074042044003000d41c1f146101d410041181c0c003202c4401005142182c0c408510314001d954910003214130401075201d04109035072500d00c0c240e0070000e16588242c0703440c030080b02909000e41d81e2541035024540f02002c0750f1a444500c0300559640410302c0c025004210000050f80040c9000023000e59650060407241c230706c4a0b107803252 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 551255386 1250 551254136 551254139
    0x7140c33030402120312060405131a0408160809130204080d1d0a0e1602030a0f030b0319120f180e0a0b04060b0c06070c080702090405070308040902040f091104 70
    0x314100740d0015000326000a10320400c240240b1003440074080e2180d885094440604058042105580c0050031366049801c012540c203000a09610204682807800c1142a0881d60f45080102280c041d0340705030f15100801418501c20400d19200410300c4c19070480c3c0744034011850341c034180c00324040ea010b007069552150044007031301030240300c60203130901520401004061511020075400c0707555a21143e86549554188401440940070042d2642035510046040450b8800010b0084242424050906940d008007035031a890500100c0340301218500d50b5141190300d45044101c8800c00c550305000a404c000044c009a4442d08000665401d4258000062070800c28074646d10000501035980b81551403540c1c0e1069141c1b80124801460b2046c0205c1e01c986a01d500e03107040a800034040c40411407030209045c0000c504030103458180d5010b0320706400b02da881303190540c034245032500083e001d8034011a00080140c219001803058400c0e84000c120519546d1f0210b000ba1400b07034918000c0ca6905000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 551256636 1250 551255386 551255479
    0xf0312010509040501090827030f030f07300e090106050409020d0b12010b0a060302030403230d15080c03071203030e21090a120b04150207140c 63
    0x560021301070000014500019074911039075074401c1c06c241000c0903002c2c207914101d0700100d894902c00b0505402800e4403071024607210f40c40f44612a1040d0103840c0c0860100180b00e8164400541c0c40c000403d40611903400d20041e80e1105901b81955000401d0006200503500b8580400b5040f00c3c140e450305410075040090341c034065045011000284d90f0360f81c420f6411a13891840104d01469640000034409a114060048a00780c9410113810325004005010000713a2040206032908000c09804000c100c1c00f03030ba0701006101d0300002044450601c1303140c4940d11904050001110f400a04880d1701207262410325450301c0a038403c03545280101d00a1802183c040c0e0040d901c040300b08000d840f0382e1040c140c1c03900c071150501075010300280b0000c2081c0d034290501c00d03500c50140c801e8410380000302d4036075a15002c42c00401000206560781801d83c8040401440e015a240a680310120040741031000da6076a40d9514080c2c1142c0c4103c0708820440040440a0b8540c602c01c1403c8a4a24440d20060b9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 551257886 1250 551256636 551256649
    0xb100e010806030307290c0301061b030905031b2b0803100509010608040c0b03010b0d092d0606120819170c09040b03030a05071e05010513050f03120105 67
    0xd0285403d80010070407100050200341c483d000d2000d1902170540500d0007658064202100245503003180c400030401840150f8200401500c0501011100c9034480031500e002c0b52488020350080d038040c810782c1104602c8600201c640d8042e00020b48244180c5481c03035540001f030001c03414ad211141003292401c0e40110f00141c000f1035105401500c040d003039941d580082901241d003640960f0001d00241c8c14171082000054500b00140801500706082d5410b2408a00c0c0301d11524440b00340207595010320604005510254907119419010310f490b44c0289440d01d0900b401d51104122243c0b450f00102060110302180302425441c6c1028503a801d0111000042c0c3d03024611a40302014499000c2c1030411030620405902e00c6480000403d43c0c44100d48000d0000b0354501100052003900181f0401910316070207010780300102d4014001c09214036800d02500480703080488044e00765420201007261001044034240c2e5400c0c0f140303003103401000414030400c2c0c07a4000c0d0759003120040c03481c1c2c00401062800c41d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 551258992 1106 551257886 551257891
    0x140405030307080129070501112a0120031008011d1603120e0f04020a08040b070c0b070503191a01120e0c060c120c070302040b100e0108 60
    0x8294030012817154030040c402e01c000124010050150035048900c036030411031511580d850310901240000c41c0c40a200c814034001c40c0d408a0705a10052107411805000861601d0795031170b03040100165076102501070b01c0c4034a0707516004a0714103030a220b05903244047d81140410111080c15450500040f10410711a01403041010000b00344001011300031410320307103003130005010342000250301418000f481d103400c40c2c03022480085050b0450304160041d8000c030302414003560b031481c0c212503034040036000405241651020a441034003d0010311342007061041040344085c9034142980882e080800c0c81c12040e000e24404d00010350300100c0560203071516100901c040c4a0115055139a10021201c0300d0083c00700052480d11400248500c002d07100d429488180d5440c503c0f00c00c030755608018001644aa85804880e890f24500005008a505050b40314201c85444a40064407d840c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 551079136 551258992 := by
  have h0 := BRFrame.cov_init 551079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 551079136 ≤ n) (h2 : n < 551258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
