-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2692
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:27:55.576803+00:00
-- url     : https://prove2.me/submissions/810fba73-edfb-476c-ae99-f3692bd2dd72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 483992805 ≤ n < 484172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 483994055 1250 483992805 483992813
    0xf0c0904080c010f110403020301050a0203090607080c0918041e0b06040c02070513050105011101020702100e010e0315060a060e030705010f12090605010906080d08060103051003050f0105040b061c 86
    0x182100c100c00b002950782c0c10003508000814420f00b0b403442c20301c9032010b80350fa14500405003180d000912040e030311401001080380c464400b00351a41d101c41c10307082c85c41c03094490130810a024000c0841e078503080380c40c618843e050143c0c5201c0710391080348650780c002d400e1001440754002160811000415403907544001ca08145000c0d00201381e01400e41c8101d400c11542c1310006801116095189200301c2e81d40d50052025507800b055000b9050a0b0f00c0096140c2181c41d40820005070001e1518000c0000c0960508170396071062200061a0400404941c000d806802c425000100141d0b0076511070000c40a001422038014162004000c5008001d061094034080c01510300c1e030b48074000c5404010b040020412840c03001d02c41c1c1035215000d06000980d541c107051000c400c45046030050b10290b40714845001d07025038443c5100c0d40c003000a180114254440032442001e50009e900028002d000b101c1048441d882d055004034071560140b01c0310041911002c040c001392081d030300d00040030700e6481d445200c042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 483995305 1250 483994055 483994057
    0x5161203200c06120f090a03091203050712020d030b0d170d0212130510050f0403032705060f0709050306010618170f010b010801051806061b0f0f0c090408 68
    0x40c11031101511100a0450001803c0f80c0c0700061243e241d55910042c05004c0c4941d00f019076100c3d03546001040038800315180500110507621420b00040da40c0e88401c410180f00704162164264001e80b520500b05480c1030103912070102030003803000240340c00852521440c00941890500e41c12070000d0482d072850740c0c001c00c55548a2050142481c3d001c0000d0743c00e00740300321070b10f13442429000e07a04a180380072450000d00344170b140e09a08028508180030700c1400010109199001039060800041d1400c84a100d461038000900a910b03960aa900000c401d0040114090384507441110000d0039030381d00c8000950707640d100382c01540d170075600150041c40504c4c0100600048043d0305694842400d81d5402c4068060403030030b02621039504a08000c1d410a5000d00600007000005d0800b03007507a60500c00420903000e104252083c0784058034001c40c0d49900e51100300d41589441c40404208410564101035689240d41c1541119201c0c0da4588281100e0204280c030110070018043e001648036a280c00c601 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 483996555 1250 483995305 483995357
    0x506030c0f0c0706080c07111e0a1503051b03010512070e07050901030c0908030306011833021c03090515010905100509010f0e040c0f0305161203 64
    0x89103508100070070304140104064540420140300900800342040c0c801045003e0180111511400c18011040011911743c680e09450718140c0b099000c1000ca0320807d00a10403503e0a550054040140031034100d00026190711040050b40341031106454000080490450142c0300250aa01c148014002c503d4a0003401101108080440d1205902c0c2c40382c1609100041e10340101203007001031001c1c2a96014013802c0c0840c0d0040c00c00d0b981213131a040400340c80740310040c122410888a80d440d02107410200020001800005800c100039224440e0402021994516902a40100280381402051001500b13050b03105594540d12451007074000290060003024004031054000d10070556080b0701c0141c5041d00034425400003241a043c54440303005c40110b2504107500400c40d0034010300602b25004803020840703108083c810764640e00e905122800c070101d2b0b00261045c45010100009114000800110300300f0b00c00000342049035113000348004c40c100310ba40100410890310a660b14000c070240b00480c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 483997805 1250 483996555 483996571
    0x2108010825030b0c120c0a1d03120f0d02031303030605060c0d03021e0706050412030e06040b151e03010b012a0302011e021207020703020a0b0f0d02070609020f060f04050603 76
    0x81481505e400040700c2800448800607031200114020300030580c4030200c0c400102d1040c2d100c441640e550000303c0d48030042411250090040003400c00c096448c0c01048652421545100719203909000c03840c07503503491107080160000703401c090f0045100c1ca4030b1400c941021a40a00510b00c0c0600014207a019404c00e14042510301c10b0b04091011415100e001041301ca840f030400000e0a1030680344c41100b000313138040c2d07031810146403c40380f11020600280705900580c00c281c0f00740c41d0b96250f11100729000095403100b500308a0440600c00b09900c1200110f44681c1c0031402800610099001150239414103c1050035892000b1903481e110240c00c540c109426000744004501440402601d80c0c20b003500c00040c0d440568001064030800d202140010340081d0360307101404903503141d41c00240414849000d001200d00d00058480c000d40f40c03410481d000300b08406025511072105007401c000030700140406900801c2000d511220915002080b07030320500f52840120304007070401050040d0342e000104000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 483999055 1250 483997805 483997807
    0x150e01020c040f140c09100810031e05070605130504020a0c0b0c09041406301e0c010f021009030e15041502030c192108010825030b0c 59
    0x10400e0707103a80c06002d0f1028440d0380081544c01034400f22220040004007044c1e400c020a0014100ca0b90f500d021110040c1220700e080c0c0001d40320081c001500d0394441c0d000415210500c001400d00c46441541d454090740540300742d038211960742e5007c0d60244aa80f061034901345541d141440f040c913083c0c0c040c060141d210702e4011200c3e211a40e5514801d90280c40c2c00310021008200c0070003e1a00340070380095188002200d164904002000c500344c0800b01d400701d440a4401103000ba00a0030303900341d40400c1c0c00c041c1e0441d8050b130344449440c8450913000880403034600034015140300740c1d4000d500040400d52594002c014402c1c035400f0038001440c9801c4210b0820071480b1007092165112102605600c0784208010703176540c07408c140000e642c1c01c0b021442055400c140800045024082600c4c2c48003c0740b04074008142d043c900d854001c10a051039009408040c0329412503030540d1155443e0705031034041d000c5440b500c01007a00c0e0035008203218003011401e10002810700c00984e82011080d0000c0c3c00034412 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 484000305 1250 483999055 483999073
    0x715051306020303010f080102040e07030e0a0804030605040c05010c120f200d0206070918021c0525090e0c0903030c030c0102181509010e01021f05190501150e0102 72
    0xc0e0218090780c81400180c1c004401031058003c4c80c1c1c403480003055440021860f2901d491170385465442c00030604400c0c1035684074000d181c81c07018070803288040d50004039030703949907101e2600000414050320140e40e14540504040381d41c1d40915590891035800c0590545135030307159901181c940280509003020808104009111301440000e04030112014101501d04046080d1000340782900060181080080b00c0004208116071503400c03a400c622812805641c9003042c100b11100004e40c4500910341600d00010011f442c0710214100c0c44803001e20b10107a00c41e4801d0032048518014034059540d0301c42c65580440c8040b01c4040c01803140490140c2560305214095000e2802c42d002020407910a0b500051404240116001e00b010320a0045030405102c40c000d00c1405090301032049894148400b07580e00c0c40460307000700070030a80300c5c01c031071005d805807640c84c00d020001c3c2106039005292a1076644030074400e07071090300580741a210a04401601340280c80800c0303502c1100b00245605602604000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 484001555 1250 484000305 484000327
    0x5060d0305270a0620011103040312060e04080d05280e0a0c03050d020607022109010923120102120402100504050a1409070f020309150903030d060602120c071505 71
    0xc03031000301107641700c070342007000c080c0b04a07070321012003d010784400e0b41340000c44011401e103607080e01d070420b0301443c1142c902d45a406145c4018007858203c1d6007462044010803040080e400018403280464200074801038031960801c1008081c02c070406c1d40c035145a60348500c0005895070146200180f20022600b40d6052600d401c0920300b03680e001955988c101d00300c0000c030302da0104015900326403144020013148400d0500d07036104c0310442d030110300c0c040d40000f03100c0d40c5680304070901d001400c0e24200214500106601c580300b08a082d03032841d40105900040344162079010301c281c1c0c034280da80180072405691507908102440314503030b2401c1c041c080144400f06060300c603107088001600720064501c2c108900c8004001c84040010400c404012070035800300d524581c00300c1a5817012400781c4400d418103240e0786000b40140658040c6a4151002186038068200b141d00440c003140c0c001d80990701c0b0b102d4641d03050104c900c80e50301d07581d02079032003100200500c0310050218008a0500c1c50058244081044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 484002805 1250 484001555 484001569
    0x306090609051b060702010302070302010e061801150e010e040314070b0403030e2103100b0f0406030c050c06010510110a0b06100203040617060a051201050a05060d030527 75
    0xa42910580d64030680304080110810145400c4400404210014014400001d10700c0c40380f948000e0405170003180050405000750003101046011400380c400d140b6203000c4800b000340f1198039052080d030a0a00c0041141000071016058859400d0602c0e45a820704420222003040a00114100000f41e201d51020201341c80140c003090307119200c0f0440c03038241814001c081d140e80d0689101d20341c0081d0f808804800e80904e01c141002140000c10b40c03241e03116210012421910b81c810406480c0014403191001c400c10000c0050310020785040241c44c44942c0103c80a004d00100746d0211b038844030040c0b0407840c0c580007040c0142002c0c500440c81c0c401022245050403210b00e401c135030740324090041c07260614000036038445a88451005606191070141c000b030480010b9459042a0f0580001180d89500d0784c0f07410601602c009896a030040c882500424000d120403a2820030369031800010485914000040c80c40310394065480c5030a000c0201c40f10540c02c0c110088540e45040500d00007017244c2c548003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 484004055 1250 484002805 484002821
    0x80303010e040606050f210c1314090703020d060203150d060c0f14070318080d020f0f0307022d0a140301050c04080a14030c03030a0204081603021c0206040306 70
    0x9241c038422410249020b005582d91504007034819a1511420695a16541e00f2000900300600744e0341082d0078070b5407500d41084d0202150350303000140c1810b41c07801c442c500e42000c13400c1d908500d03021002d40d584204843d150701103800000d6001e0a40002c03400440d200350007940e082000c90304801c4c920034209001484004804108442c4261644a120b00881e00080701440b040c03114181209011a005851521881103802c001d00303020328034000910072001d600c50311000d058120308030f44500410400103903039000a200e1145203881000c0d410008100040705035445a540070300401c160403031101d508070002003216080c0205203a0150248074079660f005d03814008000e081c003c00e56030f0064106060035030340c0c010421800b9810400003089200c10024008a045800074210402100221403950440c802c1c036040440d188004000d000d00e08e6503650051048403030b980e0480b148801514410515808d4610010758000041030590142402c9401d050742d42c141300070000c4d0314058403680c80303400b10b8010f5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 484005305 1250 484004055 484004069
    0x18081804090c09140c041e180509060108030702101b02030a110f0d0b06040504080d02040f0e0601030516050d1409070303030e030c1c1b0308070915140a0908030301 72
    0x816007003100f085035100b2400070790a10b81050b520303898100031460b03062141d44aa040d03545000d21240c4221800800344202818540420107c10b0110090302c1010b840240c429900070f010341c2c8000078a0200c00021104610b5000d0070101c1b0500400e401070b140d80d000340c201c51001c800030100901c01a581031205038680d601c184c081e242225620700501c83c6920078410540c0c02a916801e9440c080303500310040d030b90b01c04811039000c941562a03140c8040d0f81d0040e6040384484500204000c07440d44272054291b03080c5d88084071a2492540d80c40011016100d00b555240410100d211401c00018407550007000320340075405001c1454004001000564602200c8100039500f0410041c410168540943d180e0041100011418010101c10154543d43c01c015010704498441c100620610f000d01c400da18514030f0003175003800d81c00c81824040e2107941f08461140000340c02800c00314500c1031005e205079900740c0d16681c003010241e001c0914550f5511101321141840202d550028019001f0802076021b0460 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 484006555 1250 484005305 484005323
    0xa091a040b10030c03080d020708030907030203061617100b07030e1003092d06020a0819020301061409130203010b040f1401050f1b011802030601091808180409 70
    0xd810324409541e030103040d082000d81090002c00101d0301e012680b030103482e0000c1c540d565828500402070024400c404006150000200030031030864004900c12003103c0c025800e580f080c3d964039034500002110314030b4a40104040c420303d01c4905034401e121a038000e58400c6c5820f402ca440c1c06200c84603810100c0201c00049262102c40329a04010040c40040c072002d05040c030003a40d2940c5c2d64001c20940081201005082c1000c920a4510421112800d29048001150382c4c480080c8002e00c1b00708201c41e0904840c41001c4140301c200c040d0720889040390703540d60f14521074902c9481c0c1c10b0303e80e074022502c040d03101c80b80c6a0b005002d4181c41c40210700808514255558940c60800c5402c0510260b80c0324509140703080003e0305842c0d8101c0c048482401ca81c1c0c110590b20104841da00214207089a000540381d8642902c2c0403d04054044590324280220101c0350320b40c1c1c1e03a109403429202010b0909038101014401d41d800509140007402c860003000c0500c0c0e942c0b030950300220301200d05100b000c0e200450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 484007805 1250 484006555 484006561
    0x170703020705030a1208070e060a051818071d10020a02030f01020307051c0207060c0818060c0405010c0309090903120515010804110406030209240a1d0a091a 69
    0x14040101c1c400405042d07014283c8104075441d0b0581c0c0c500911202d20510004000042c5505d100780c007075010794500101103d4495070b0070000103007148c1000340509800200c070145444286844180d0f19942950006404455607a40178126641d00c1e07035181d111040ca4100c020811160b40b402c1000300900d5556005100d80c0318075004043c903101c001c1207541d480364410414046e0032580038080300c0d100704407031201c002c03803d59241c5500024840d101001e040c5919010001080c1b0342e000903114018500c040c2100120070198803c0e40d01c3d00b02c2525240b0754030808000800403940503041d5a914980242031a4054907510038101702a124140002c4000900401c070080c41c07070255200b00e5800c92409401c10845003030900c00a0003402011340040cbc58800f861b80c0300300b03a030382d01c980041000d1580601045080d080c05002002c208650341041202f610075499141c070182404503000c000c07201190f03803800b01445840d2186040310005855030600070744600c1c460000c1224814008140d4070301c90119600d41c0303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 484009055 1250 484007805 484007807
    0x11030906030108101b0203031f0305010f0c080a110412080f0a030608161d060a1802070c050d0f060f020706090f15050907030803090c030610090c020c060417010603170703 75
    0x120340b800f20b000701c04071945c4004401e59000094030303400300100200c666080214846200307010003542c4021b14941c20900b0501d061140e0343c1040f000307648580c907914120388840300c40d203055a803181100c00c9002c2c000e010400c203410944004041241c00750700c65510f030142e2000c0344002540a10b0303441001c203807260002c01002c10200a40103024049040002000d400c5c21b07001c030041c07550561524034640d900b0012a00075030b0340034100c0c1d00404413143d0100d4440481d400b841c01941151605681c0f2440c440720008441c241703c0c0d41c14401c65800019070b42c48445075500c65005001e4070400c0c20903240e091041c040002c1961250389180780c01032270001e036010500c1c030300003104009000c4006a0581030009205c2d0040c400180d072800d4030742c41b0b01714644a5440c120750328503281d00088056854420b40060000c218100c100344425198101024801c0401101043c0c1e51746400c1038a0580090042008001d502c01204240030503628500000c5007050741c90311015941045500c0e00580c100c0000f135044201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 484010305 1250 484009055 484009061
    0x30606080703050c0d0b06220c020106061107060801060c030201090503030a061e0807151b08030106021005060d030507060b1e030d0c0f0210140a03020a120b0f011103090603010810 79
    0x282202c40746040c86869803a54900480501707c903009040d003a40f060208c401c0c21000c00c1c0d241203081c00c200030441404500034045d24492148202041803030702c100880d0345010507108141c4e040382e02c86182c5a440c001c011980380c03a09810a40c01c5543e2401240c2c0004c0b001e100850081c1c8a40354040303102c6090466503071002070000c1650465a00f9090108288100031407100301711440d443d81c00070a03640d0204161040440c440400300704080000c84bc00401c00f210010b54143c904940c2150f01440c43c00240c103003129025526654404500403c4d080007904c07481c000c100700381c420f010114408001c2d03030208070328140d038801c0124009808140d0080a00b0304100c55203620700a49001020010140c88018000d40c0110300a401420215654610140900038142c0c0a00503020210764404100d00c1c010000d4210140c02030010b075140c84501040b1032907004881041c20005c24500101005000640e10b41c41506403511440c0000c1c0030003045555110090b60007008914064440d4140a00a030011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 484011555 1250 484010305 484010323
    0x3030e09061008010308090406050d0b09160f050f120d020604050d0504060e0f04020c0d020f06010e01060e130e1605030d0201020f030a0203060117070c061103240a03060608070305 79
    0xa02114000d01496940c0b03c4200d42c11660400055a03503103201070f01050142c1855049240c000e03e40c1d03c641802c010701c3e402a6413068078603605030740c62290448080460f00d071581c4140c01800010b00c400b07015618104000c190741c22001410b1000b058000ca5100d814600003c2c800342c0960040e00400051000c20301100750050365900e8400d14181c101840500302c0500900300d02c0c018101101d1141d007a4031607504a816604040c0700700e0b80280000a4001d60340c51800440c0354a6004e95800040c80004c03080e8524140e40071a296510403250420500002d44280401d04d80c1e16a100c060180b41c070101071203402000911880d102c0c154a0410040c03610740301e40c1e0b0f1aa01c04580c4108281454a6403040c1501d4000640c507801594035100e120040340c04400d184000e500001d662001e0203074040c1c100741c2200c21284201414805003d1030311200d211070004645c0f807010042072480030340000d14406610640e032840240410705941d00c0340c4900b02240c01e40e81044402d54408042130003030007010030032611 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 484012805 1250 484011555 484011559
    0x1106281d0d03110f0c030903010e031e070809010509030109061107032d14070b0f1609080d030f090b040c030309090b100806130509070501091a071101090f03030e0906 73
    0x101650f2011000c0700284500c1c2c4e0100301e80c5501040e184030000c0184216406048018001d000c5404080f92840d01c030391200840200c213941c40308a203100300042c5400e881000ba0043c403401d051040742c80042d51182c0c840d50301c1d69030556032103100d040058100e100c0d20460343c044240080d00c603841894050303c2000400460301e0021607204a01c1c01180310900128175600461a151080c1d0392541566182c40c004c030f0300c0c000d10007001c440c100b145020141810a10856010009072421407038103500b99a0319180c0d001c0c9040302e8102c034441e0380d60f40b80603403c81c90301001e1203607001030341d80b445032107541c40d6a0041d01d04849104c80480208249644209540d0142404020812100c61080005210642d90b04008010301c003004ac00500c807a0380b0752822135042c2040510500480c035160fa000c03601c1f074543d405803d01242e680c0c00042001d4180100001080e81450849850500c032a120b09200703085100f02c0d0360402581460101d152902422901c0065220340c50310200c01d0f42c07040c20003d4542c0001d214074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 484014055 1250 484012805 484012811
    0x90411090103180f0809150a030510060e0d08212403060f06150409020a0c0c090b060313020a030f0b07020607080402011e141204050106061106281d0d03 67
    0x80c004c03a07001c8246412403580810040e41d1604141c02041c8000e054495038001d0710030225902000a8045e0800340c07084c80c0403840300c0340e0191500005d680c11361101e4a410703000345101c20024000b41103040100947d070900c4a9101c0343d500b8800c04a06189801c4501c51410180352042031405100040c00e1107514008a001c1d12485ca043c0280e40321440f001441240f14030b424520780c030404018030048070042d008110b4159980e41101c2405045049600c000b200c582c1e0000c800000c108000b0703c203034101c40800901e1623203180c0380d5003074050001d2801102640d203c4154080000040d4000b9601d0703005a10403c8410303450720700000e01908000c0f00520380307070a0006001c1004010307a840ba6030516250030b6164800c00c4d88030303100c03400c0b12440c04204402c0c0c205c50000400c1282042c021114900c40c074400e000a00200d40c40310811100a4420400e6014550000c40450014032036400710354103002d8200380f1500b6000144580c01c2c01d4400440d2003450805c109201c0108100c020300c1031070010b055600307042c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 484015305 1250 484014055 484014101
    0x1a060307050d03081003020a0314062202040f0e060103150b011b140f0303010803071b06140711090c0406080a0902011d13060e01060915050304080f090411090103 71
    0xb00b010003900341002000c0001810000c0c4001050003c03581c0510380251103070704807944030f01c0c082a41c2c0311001c039804400c1c4541c80000b040354503603c0c445404106484081360354054154244806000c405507998091900c030b5601c40c0860004200322030080d80a10340415040b540c059600342140e040c252418104140b541e2041c0707a203502c1808a80b00c4079032203440d070000c00a000d542641400c244241c241c03e24040000005080e55001025104050203413400301040c034606032501010a006204200124140b0302000550f40c407050050003200d40540000c54a0600c2d0a00107140c805040381c046451100104081c45442c1c0c0c00503030b450f4000099076003040001d03000d40000c1c1541181040030200d0081201e0301020f1622402408891100382c40001e0000070380310014003150b14000d00032000020389240d030000301050001040305600c22151991031854640361500d054075405403080a81652081092820380c0d25584540305910350034220468980c8948400102510f090500e42c04e29a9483c10b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 484016555 1250 484015305 484015309
    0x11b02070f05130905100b0112150501230309100501120209041401060305030c010606030b0102031e0901090816180e03030a0c030b09100609051509010e0f06071a06030705 75
    0x3001064600842c2c2c55200c4155802403c0e001d440805002440d502801401045054480c0c200d0b60940d54262940c01c2c01031140800b0004440b0012141000074100740da0411007540103405154403030341405c0d882d0b803403c043c2c0c003002c0c0e03041e610660b40c03001a41d21031500c100c510320103403289501503e0440d0500302502250707000034828880191000c2e198200003d40382c044210250700500045038070a00b6641c88201e40d000041c000d044503c1201d01003410802c0e511080e61000c001c031150490008a070000e00040c5910a07000b94000120150605c5600c04011914510400a90039003854840140b0f500c542003103500f80ea85003940a0060b0300d181000045050b00c10080240c07a03000d2150b05d4006450a81690101e01070180310f0061508081400240090705901034000d00030740700c1c20740f9816085a0703242c00303200016415412411541006200c1d402d250762084011005080c00144207400c104260000078455a010201c100c1b500c1030122141d004071030b403411603079620080c1180901314a0340780c900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 484017805 1250 484016555 484016579
    0x10e010906080a120e220b0301050103020d0f170409051801020a0509190f0b03070807020a031b03020f01111201120c0e04080c0d080708090109110609120f011b0207 72
    0x100600003d00c840302c44151500c18107891405d498001c10b0081154003501170042c400340c14165842c522800c0c02c03000801d038101402540c1c1240d501400c010000314440d1200d00c01e480403402e0031100c0c44407401d001c46403003c83c03101800181ca24140e00295504018040b801801c1d00300c00401c209034012721440d450a0307006403c0c0d40c081d0405031078440107505004024402240c941c1c010300306071103162002080c201c1d11040035501c500385a44800070305844000003640d0f51110224014001207030840025007031480d0f02841d01403544640115002110100c2c0f0907404d69141000e001c202d20380108800d514101c442c9502d90040c1204252102d00d4449612080c1a8038580e018100b4004a410045010440c07080200e948254603581900e030301502c80440103190781e500f03661f0400040d03c1800407a480d1007041c402d0402042e44100d035540d50541c1c003c140507154020002c403540c4016959250b0504060a1001070303c01c1d0070041c0005407515015610700d4040c01001701c8002154441d0f6014071074985410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 484019055 1250 484017805 484017823
    0x11b050c0120011803020d1704080702030f061801060e0c04300303020a031d0c09221406310f330902090610030905070e010e01090608 59
    0xc6001e07442a09400c03680c00d1400500300810a40b5841d04e0040d00612402c1e403582090343d48640e09540d50f103651914105c504220440102e0800032910020a002030402d07001025806d03c05003c0e140a0a0507450030341c2405421650081d46800d8103011001d900401c1c440d41c005010041014081030a1845544505008074054000d0068812456590410b0b842062031800c4654500c1c00840100510b0b00030041d420200140000c641021115043d006440c03140000e10700c4071030000d004008031141000381e04100070f8069025101900c410f00c10b01c0c882d0041c1920380b980143c03a07040c0b100000342042807400384010403a50100801c1c040140e0400c004524039001000345c4c100d916102ca00d1414840d00a000d0818024680380180e100884199071410310342800d204070340d07541e180001115114505665883ca030082d8003144a00020700a464954440c0c1f064030b22a15000030007000942e80e16180100e01e80110446001300001080080840d90308540502043c80040c440e040c03820300055501c181c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 484020305 1250 484019055 484019057
    0x106060201021204140a0203120a122a05090d0507050310110a0f1404080d08060111030a180302090903041505041a09010c05031303051c02032d0304060b011b050c01 72
    0x2089507214500e81000f000340c6e9550020195445041c4100c0d240fa055803208180b500810000060360000e007040e4030640b040038522001020412030100800507010202450000c107002040c03000c08a19101c15105814142c440c0380141010760922007018134010701c803040d14181c242810b40e9220041c84e26400d81d40080c06c241880242d108503041c09460500032207035080ba60300d41c045400680ca560000d03020700b01d01601e0322088402d0b25000c3c011034645a80c9102d00407650b00c200300083c0384611402016003628550030700c0044460302c0713070f0001d403a1050549181042e035102060501116080b407036542d0706c1002c00e0400300d04c5c10f841e01d14203441c0442d1100d445010440081010032099020301c204418040c2c0c01000d0301d95074456a140c0d001030318814002a00c0600c51401642ca90317040511000750b4050860b0019801c010440e603404102860901c01d121124104007040401c01c2d580b00091030150b403050034045804a244c9000400e051000003418004200359120500442c03808515244210381c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 484021555 1250 484020305 484020323
    0x14030103030509131b05030a182604091d0d030e0a02040e030904050a150603110301090c120509010c0e09240d02091024020303151c03030b030106060201021204 70
    0x100c00f44000017068009091001000368119090032213900800462007600381800400c01c007401000444050452608010840b0340200c00d01e5502c4c00300002c04400202c0c6080c0c0440c0b4054840d5041c01c01e45e641220300005140035032214803021142408240c0100e200b507c0e04100003e40c0c0c0390003982c2c9916400c4041d010701d07540da84050180d14244110341e4002c078050700a2005040003e100d00c001c2010780030908a2030107521022400611074014003d421038504a00c80c1164201241000104140400e1a080c040c02003980400e4081c1030260134400c90901d00002600306014402078250750714500009c0c4140c08103001c0150002d1204419404403d80c513540c2d80a0412000c00f003070240c0e0500c48041c0d400660b402c20403148840802100051714400103444040f0076042080c003603140f070794040030300c050381041c000500e4107803c0d14680e144d041350082054101ca24001a24440103221a0b02a4002603c5408550700350409008650080c0030502c0210700c0c200d0102c151410010300540300400d00f0300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 484022805 1250 484021555 484021579
    0x140405010804230a02040608010216021905190503010f02120412030204080a050a063b01090611030a0b090114041a090c030907050118030305031f090c14030103030509 73
    0xc04078540d400108080c1e0700c4500b00c102c43c0d11690703903103020160b0100d1045083c444046445441802035507440e024035030f00c81c0c0e802c048907802c109000321a004005c0c80e556030344c040050260358141d060411207141540d9800a641450b0906081d1241301d820782c14014010800c010003601c030294400d5000d44c002001d0706203002c00e46000c070082e02c5507a0180e0282c1c818919800144200860081a064400d00041190107482e0306041c005c0d03002452982400100000c00c0c99584038422401d100d103214400001032003144590710035040700c010501c01c41501d03802004100310b02044d4814100c104508070341107001589002c1c500c1c83d400340c803544103600039503c0e520b40400d805040c2c54910340402004000c0381340781c584540d00a119400031649208544220303c4c00007801d5000745210601e250103c10800591030a6860644c0d81d60f00140c2143d00009803d400c090548040320280b101501400001144100c9a0b14000b23028020959a400c0c50540420040000a402070121140320324240ca010351115 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 484024055 1250 484022805 484022813
    0x1b190c240507150e0304080c0108130f12020c0405150111010e060a0209060715020306011701080c010503130b07021c09150311070602070b0103062a051813060e0601140405010804 78
    0x4400c1340b204010358880030401141c01e1001099410386001d003a80c800c500c640e61000d4102c074038030075010301804040041d40c0000104031010040180f030b907145d004403100d18480501040c101c1d081160034144148054840e2141580d0100310380c030503c010345000380540b2a000e9100364541e0700c06051003401c80c1d40001c40048680f555810b842020b0b400c966031440303949400c40b03258080d600480e01d0034001036044c10109000910701a40e41d0580e00b69800074180d0300d40401c01942c141d030000c0c1060000c10303c100405400120321600b1148125103a85c00b0b00801d00c000c1c08512045c3d40008548014420340c18421702c048000ca42000041013a54500800c195000811000403441943d9010303000f40c0c0000b8a00051145251009048900c9a24200071b100003103980072020101e8180314140c1d80e0800b0511a040e1885075000e03201c0d1628007800d08500d00e03003c900181c503c07491048009003c9446803020001401c200c3d2481c0e03405402801c00e02620748000174130390078034030139401014103100310540410148 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 484025305 1250 484024055 484024061
    0x804030905100e0603090106050102060c072103020405210606011d0906010c05120304260304020909030f0c1b04180312021201060215100501051b190c24050715 70
    0x2000203451540c0d06d0822080c440d01801040c01410b0151003404c0c0400c1c00001d800301100c0d081908102c504000007800303440302500c18480c090034004c150702031101240b19500c900f0b81c4082e07550440d030360b40702c0455840790403402c1010045c004e6040c0603410700341049110f004c1d0502803941d802210140f0940c0d95020041c2d400700c40b00b50001e072a5202d075140d50342104c20000000c0d40524001c210b0504000900455506143c0d02844902903400d0140302140040c00d0951901d030300600d582007524204902c08004003c5900b20b40501221030b071044240394540424a002480d01c7c11040c0c8003400354901330b045181903541007520040812030000d002260b290400d90503103022070002d441120803541e65010080d0788a00180b40c40020017003100c040b48002201d000b02004540b41a12954100009296040c40d04940460b42e0a9030f0b01501c5148402900941d01c10340c40b291103225003000b4141403904c548201440554400502690300700740c0081030b9084000c0e00c0c1d00590198142048204030860ba80c05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 484026555 1250 484025305 484025327
    0x1e0714180f0a1226031f05040510170106171e0c030712060f0c050a02010c020f06010b071403070c0f060305040803241005031b031504090c1205010b10080403090510 72
    0x301a4012050144c02005005800c0b1246e0450f140e45128030741342c6003080111101540e0308000003114600c200107000c0a03000115401503c84000129650780301c01c2460000121640b015998009090000b859206801500c00707007070340c400007003030168802d9020a0ba2030342c41c0e0080030030b819a900c505400300812030300080d400c07a110180502500e0355007040a0129045885c0c050055404d2a0700f0100f81c07407000845000401e14400140710503482c21510607229030180205036143c070020408181c0d1040208002c040e0684120f06007500c09240082c00002100c070341c2c0181c0d0030103007003c0c20b1101160035401620b0700003481c0c190310542440c07401a03220100d4100019a07401c001110310100c2d41c00d8000000d5440b480420700b503111452a000d01109841c88110741c0820b60a030764140c0c2264500303199015800051040c640420041d480c1d040105461203005411070300b980d10b031404072035a42401c195070b2500b414941840d40840c2010741d800351407e4290b000e050700486020248100083c880c41c05654 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 484027805 1250 484026555 484026623
    0x50303060f0a21020f0405061e032b0906020304030c030b130f0303050a05011413020f09030601080109060c0903030509040f020405120601090b091e0714180f0a12 71
    0x15403d2107800c10307000c880c503501c0081e0710482043d602080c140c1028002e40d842521700601c95981284c461850750f0400345100c3c010f94061080d40c43c0000b40c20100b4500342050b070640801c1043c6a6001c1000402c03c020a821100071508244402c0000428003590101501d034041609072466952401260b0240c144940103010442c04500d450181030705a484240135060580d41809560303265124002a50a0200200e400001c4241d030f10b400b43e0045e5000e08085e00208090074940701c0e0500c00240381c01400e8020700d4203650754a60032020402d452090640c69000344c2480b0300d201d8550744000d440b80c044c0416441c0036585500500030ba20505504983c0a08401420040c6103c041700302c0d80d41e551024041d4140c1d0358540050400310349401c0b0009031141c3c1c000c225904142c034103128080b88104014244006004150401291000194010b44020b0010070101c0c24290328030000c000c1d2101000b41c0c0c441c0070b4601900148070008115030050315076904000d000343c800030683c106002140c0d0f180b03003600b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 484029055 1250 484027805 484027829
    0x602030a0806032107031e0e040b0f03071d0a060b0f0901030e0d17090303220c12080726160203030708040b0a0f020f0717031c1b0c050303060f0a 64
    0x980701c14a64068900240291f40308420110201441d8014401c440511000728100076020001c40c03030590040c05030b5480c0a0580d4040c40b11030f0001c0303031400d8100d405c258200d80744c0901400d200c0c24000503440e80088030795030a002851030040d0703040c0c0a224103504280ba401002455060b180d0081d00041c42200503030044070380101903a07600030500d602c0e1090000f001e030040b001050326240000240c82c016079160070350b007141c205010460200200b0140303007219446400980011100581d51002c8502406501c2c01c07a038030141c91174810210354081c2c0050071048094000d01042c10409070580c0d07a20301d404032a80341403034640d000081c9540150a00108001c40009010442e07215542c05081d03040c1e4140c032480803141e803440d004d90701c0b54440755120302583e01912080145686412040c200c0990700d0741580c0c601050504128407a19842d0891407215454961914820b00c03002c550501c010780030310301003500041a9841640f284800b424480c03280d1040a482e41d040c0e0b8031013074200d00604c2003540388 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 484030305 1250 484029055 484029103
    0x30105370f18111615020c0115081603330e01050106050304200a080a0c060e030712060f0605060a020c0a050108040206030402040903030f2f040602030a080603 70
    0x14009a18040c050100281c2004540d8503010790030703010f68a00d50035018901800d06041c0a24005600e000794000c0d00d0302601000c1116040c1c0483c030041280b6001c1a00104503081550961004064158000e000c6644064841c90140000a84110640c2c1d8040200d00142050000740148407038440704819021450440c2401c50300f0035580151000341200c8000d0010360f0360341d1070984d030301d0004540c0544000904101c0f0004a5201c850041d4600001004100b040c1d8503484501d00d0941305801c02c42e000d003441c1d84244182e58000074186480344040b0000e2140302c2c20f20020003100c0c061120300800c21911249100000c800b20340212019043c09041c2c940c540c140316400079a101c001c00b00c1a80601e0880c0c002264a511a070422442190003600e80e600c0e648903682400000c00d0304004c00d030205a91400c0407540480b050048103110444a581400c41505000c6910740d0301c2c8941c418220754060400041020715000310079180b105140d030500d010707140d072200302080c00c05840e10b41032007a8003110104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 484031555 1250 484030305 484030319
    0xf010509090a02190e21190503040308040b0c06010b0901120213120302100f09030f08060109050405011d01050d0c0302090c160b070f020d050d020703030f0c05070b07030203010537 79
    0x203140141c84112030580400c801854004001e507108408500d8a03001010047c2c6104c520341000c0002600c1a41100d01d019035171f864402c120f03000340c0c024011600001a103912020f008004280c0900025034001d85056800d90018014400211040038100e4001ca01100300d001401d11031790090003a115102020782940c60300949803da24424060041d142140c0740f05500c08a1241d82d450035450b403120380f03865084039030a40c1c4c61034000308454104030801c80702141c80e4540c0d000f01802440d10400e10b01030074511341503034440050160001c47c06034000d201183c0115840101c101d00326074055403181c030310b601e42c0016448548216180e00c03240e440c52080d01420040928210391094420786e03a00032240340a80300880c0c0300c4844a05880000c2c400f4820b90041004030740c01030030424030134100012001c100e250354106440c1e80c000c1d40b00200d00082040c0040c0140c9140465001d82103140c1140341d981490005a10500c1244216480e14070000c00800c50118958085902d14510001c2550460795218 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 484032805 1250 484031555 484031567
    0x30e0a0b0a1e0501060c0f1b0b1e090a0308072303040512060402011d0102010216050c010806011b06022a0604021009030503090906030c06030f01050108060f010509090a0219 76
    0x462401021010b59030b003079806000e8400e05043c0c88241e52050002662034540545041007200d043e00e0304510841c22500750008100d01d40018a21b24900c00d44440e0f100b1b01402c000c1d0759550800504150800c003401c0d140e9100303001c1206480d030006000703803500c90500f0311404840709800d141d4041c0400d00841c0c0c01418000000e401207450840c1d00304041e80400041940760402030310001d0120300802240e00c0c01c81ca010340300605058040c40014244a5449807400c00507019200907101c9030820b00c00d00c00e60703507071044120390711040a0812150807804645c848010540019014119650104c1c00000e4017025905082483d50715140e00c2e00c42a81d001907141d03e070301094404030300c6500301610615400d070046001c641140e4111001d10300b0200b402c0103100c1500b40c01001d03143d040c00b49214040d03c965541d00907602600680300100040d60410740050031020020f8041841445422481c075a0341e83d124049034014001038a07490000d40383d0300b1480c402f900900042c41401c410001c14082e1041d4401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 484034055 1250 484032805 484032821
    0x3160807051003020408151005220504020312071a010b160807080f030906070801090e0705040e1c050a030c1704031b0203030315040f020a080c0309030c06010e010330030e0a0b0a 78
    0x80c8d1405c0c525945000f00802c0c0325011800101d0001018160010407401f6408540c0c4a800a015200f0320004e1480166090388008030480340e41a40da00382d41001176150581a01420500f9101c924040c02c0c00d90004158089980060205000003600b81c00c211113882580c2400700c030207884c50f40303d060158070b1320780321441181e00700c0000d00380c440002180d50450042201005098016240701c506000034807014000140101c0c04a12a50300584016642c1030044101c56105946881d01c1e50007000303008050303a50020b290300401c0381d511800c55091708804110342d04aa07050921000004066092880e14584070301e01a5150101204000b21000d02c5441300e102030308110380810103039011521000c120b028985110000441c072800066941040388011a00b180d088400c40e41480e00300f000a0303241420903005001a004c0ba00010001c0021824442521170103078810b14848000101e4020148142c1001150400d900c41d01d00e01c2c04a0414003034201d2158100304040d686240450001001c3d1442c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 484035305 1250 484034055 484034071
    0x302070506070f2a05030d14100509180a05100608012004030209091006090b011106071706010e030a0813050a03030206010e0c1b0c0316080705100302040815 69
    0x60006007030b16104690b61100722620340c591003141184003002c4440e401d0707201c00d48011015403c2d403c6000c1241003010b0300040c20003560102c1e44208540c02c500c1c9040004c0c00080d26240b41541c1800780da0349400110f5403024515641c0f06001414520302858140c01610180042c0101c6038040c8070401150440c0e025235244d00001d000c0460006851101489a914207041e015002d21003440140303007000d1115084244401100c20103031f00740a0110403204981d00c115002d659801e14400203503000002d00040b078a894010b442d0364901040c01910140068200015401905002481e268000d9040c5070020701c01030201e840007025441c04007030300ea220784501c400304e0780700302d00000b007610340b405001003602da2541c00380845034070300307404c0c5c071070018000e0b11141040030107000c10300c0d0781d42c0104240c4041a40c1c8000420720744016400341401c0c80c0c1f0f154400d854200c020361082c0207400c00000d0480c1115000e54640403075080d541c500f10005e000316007006440303006003901e071600350407080500b034064824 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 484036555 1250 484035305 484035313
    0x7020d0b0a05010e01080f19050109080d09200f010804031116090e030c0d030207060209090a021b010b0d0b100b040b0706060f150c1b0603020a03180b06090406060f030303020705 78
    0x312043d403647c410003803000c0c0066a10a0001c28041c01c0010200003031300d4403560010404050660f00c00c0487d41010204448c90342da04c0e07511005000054014520f008030b1510f0701e0350b9100100004c2a04464a820340b00c1c1801004000703e401c040c410400400380a04010940d200c0040748a45003600c9071041c440c85150710305101050030243c0e400301c12941403c03000c60041014074100700c025400b0350041b01050358100d03403e0000458070f440303d0780080c0c840e01348040010f9892888001c40c1000341c00001d22184aa0f140030030f0000f1945071101d10b003509075041a001038181e07603001d000840009954000d24040c807008a40054807018010107000c41d00e2043c441400203944075112540001082c0c41080e101c0781c1442000a451401406032144890003240054820b0038041074509085543c5d5101d5400264005000c810f201d03450b10504000700e15192031000302d21820340b03400380a0100588040d2003110b4030804202080015400600105182602e6180703466072414050000c0d00f14440550392805 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 484037805 1250 484036555 484036559
    0x51b16110604060f0813051506090a05091b120a0f0c0e0405060105101808100609020702031c170c0d050703021201062703060e0f0601061407020d0b0a05010e01 70
    0x14012060b141503034025910006a40903c441c100c54203000030f40030500302e8052485410100741c1c20f1010055031010345070300030024103200d41409640240244840122841c010500c00c907284041046900c03440c403d0514110b0030b8107500001c41000d00e001e000c0384684504403012040001009803422154022100700a2003945c074126003000001c1118000c01503088080180304903d0f0a10100707041001d58904161950119181c411401400750410102035000c1c0c603902c040600340307000381c41c007a0a00c503009604010040c3d010946d1850180e50301e84916103ca090240401d100c0c0b00c0083d01100200303811401400e00c0e5038000040e901000210300d60f54103190008003194007a000b00c40c4005443c0800140f141c0c60540c04417203402602c0c44110680d003050040107008a01c00c046030700a940101800105c03541002825441c00c00c0038030307101c080c1d0f03084180100074554106110031411441084d21540d94160ba00c0007991101032210014500444c01043c0a00780702c096101c01d050b51400c110012140c2d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 484039055 1250 484037805 484037809
    0x106080705030c040306110f0706050a0b010914060d150906140406061b14010e06010503011b1407061104061e08060303270307080318040915051b1611 66
    0x403000f01d4621600200401040002070b00580c000541410b002c0c103240d007010b450710714203840d641c4003001c196030542c3c9032818405005410710a01c08071010908241505924180059030a406005092803003018040351081c2c8000d12604201e640c485110964034000b03448001000c002c20441c000c0092840d811000c5000c00d04151103a181610b00070744a01076041e1500f020103081c542c43d80c20465603104008440b084000d0709001d9041800900009171411703604001c14142100d901c0c80e0042e41911911000d286500c0d004103960501d8611920341d15607079111030800e5409841c00001c809401000054001101c5500821012280c074002d0301384134903001003a1048030b1140c1e056480c075038190010016215040c995503114100c05400381800d039585104140020f0070705659900059440d0000118401c3c005071919004500000c112020002c640d41e60f00c800e0079a003004181100c0b2143e03604081092030794107400c10410132072665081a61494500701c407080d00c40030140101c4000b0054140e404540c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 484040305 1250 484039055 484039057
    0x703050409051e0a090f021306181512030201020910030f0b030715050a121a12150403030c0e0d0303021e310308042304091502030601170406050106080705 68
    0x180c0c10902e002c3c058440c0003001008120042c41103444050401c2c0d02001038540880011694144600004840b40303085146203e1440040004021910f03003c40760030012030805132078050f1044c240854150800602d000c1e402403140c003580c143d12054030014489810b0741600005450794054a040c070170180381d0f0080c5551002b407070140030080440e01010b0340703816100310083e281c42c0c2801c1c078042c1e0307042c0b01000851040300d0f840c4120707507070742d98a8600090351340c10549010bc4000c00c0e07440c0180382152012019500301074015000400b019118000c0c0d0900c180b04940d880c21881e4001c2054180d05030501e0050001e40c80441030032002da110410443d0401310100c182c549070312440f5a140c0154004414900e500f081c1c580c56200d0f03080d0034890110204801c0f0b0301070406440962004903c0c15203202e00058410079860030503101e40d040800f261b0020340c0c0340440f00740c0c010800e003026072651200d80060b1a10207890300c031800d484101c002040705202081e0031542c100d0700107458143c07081d00d41c180d0407103007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 484041555 1250 484040305 484040341
    0x90f0d030e0402130506031008010b090405061902040b0a0806010306270506030a050a11090115021905010209030d02150603030f1206060d1b0e090907061407020402070305040905 78
    0x124a581c1c150507410b04040c0c0007012400300c02c01e2503407480c98442c80010342e1500b0940b94a02c185000b40c00510007e0401d110b00b02c83e503036003158880c6407860603590711644c82c000100b05801140140441c02000c61458058401034803000110399110414000014852241194080e000901f0039600165001d5851985658005100040002c4030554100e8401404014004641500c03801440d100418018403450001d030348103c0107051020401420086104010703041140b99242842074410f285800040a0b00c50081e050032903a0014001e0416a009001e03000f4070a8250040c0c0204c14992540030822001e0030302c4594401700c03d40c80b004181540d07401410144941000200f058519503000389070156440080100801d190910619200c0c1c1920755410422040909445500c00300a4208000350409241510041080e15020441d2030303031200c00f407044106118090560b940c161081d0421100b1203600a4030942d55007907135250040c0309070b10500c5100092450b1601050824980603024a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 484042805 1250 484041555 484041557
    0x1005060301081203060d05010612061b08010509091509030909011a04030201110f01020f0319140a09020301110403031e0302031b0901051c0c0306120c0e04020d0f08090f0d03 76
    0x1a0f04080011114150b6001500d4694050750f00300682e00065030900032100542048060081c0240c04c915021040c1c60420001d1000080e51142c5400550350200c00e03181110422903042840340c940300b0501d0304124040d1503260341d152410040196886c000001030001706016240800540e0fa2900e8030b468041d0b50641c81c041e001805c11040016621032203554883d103000328141c40c40881e80303c204600326481841e82840451010041281e05d1061240e4414000c000302e1051041001040c421a00804010032080342140d0700c02d089400d540f025400100c00703620910312950340b41d8903410084d10741b60f001454146c01d1241902c04904207446070090324021008090058006410201ca9400b02e401c40807009040010902000718400b1035150401920f10008100180d144425034000317040e9491a04000c0d2410410941003002440d04a802c03801c4440420040b10389480b23510000d4042c0c81001d9001c0c0c14424071030203000c240300c5200000c0025100450301c030500305080200780701014100c4070001e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 484044055 1250 484042805 484042813
    0x108060a031b0803030124030b28080303011403060601020f0d031116030309050709150515040e1f0608040302102004030606032a031e0206070b100506030108 69
    0x7400007a06030b05000d07070554206401501c50340060302d980c00c26032000c6400d21452604000019420200c03002c0150320b03103001d00000c81c0201c081020140199046002420341c0800744a80f18030641d202c0010300200790903241d5a5940d641c060341d820901d00307413091090141002281c42d56000090112903000348001800300c2800f050019802014404099500c000d010021903114040304441401110711a84002404003114101076140c842c00d0340004a6041c80c1019815038a20300c08028005c5071400c544c165510031880c135a43c03030580101d50000782d20b5035200090105640c1c0c01450300da00365856440d02a51195101c00c116082030080d0350280150700940c00e5419001003d4000701100c0d400407003103a5100c00d926580703c00641c4a5801660400d82d5180e00348200078003030405031307a1414102000945900c4d1241e00c40c0b2201d0240c4002004500f41000404d440101c00708080302d42134006120035118001820a03c0600301c040f180c40d102d1903060840803c075441c0120680e4180d407102c800034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 484045305 1250 484044055 484044059
    0x52a0a0b04030306170a0c08120702040b0d0b0112060c031a0d0507170f07090501300606091d060c04170a020907020d02060915041e150203150108060a 66
    0x1244103a0090030541c2090f40300c81c0c021480303819030403100070940e0340340380207200a51041c101000115203542144400e9084445010403464001c826900325680496000a42d907000344001180c1458695000302144042800000d10510000782c7c0b210040c041d40c010720558207500c10460440c2d500611244022002c0c5501c0c00080c18601e2505220b540300b10308031000d01e6120744548410300040c500e0f0b5410fa9002110b601000c08081c0704120050124000c18003965062480302044060a601087d070002c58103131900b814081c6000146041c1608107004008254589c6440e03400b500d071450345002d5200901041400c0002c0001d04135105406610420381400d04101e008840c680d01d58402ca045485280038880140c0e450618150154049030000c09224000701c101a04104005101c08a81d400c00052201c1081418071160703401a40705a249050360030403403010820022215008c1c0c0650750390500d01c507aa0849078011400784150411100d08074103c00011100c441c821074029400c004041c4003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 484046555 1250 484045305 484045313
    0x71d010308090d0f051b01030e030304020108040519260a090315020d1509050c070c0312030f020a080105010801090603050a0f0327030b060a06080601140f0a052a0a 72
    0x103804003940042400d00007050036213504c80b201c4510b04041e19103810030b00c2482d4005e07080c56038841d0030041c207003014041000304680243d2a4080104040c0c10b120210300001c0400009020b206007038000c085500b0905240c6027004200355288903200d11119002c092840511056642920740b0f05403199540304031182190781d14480101000c2404001540034818149407505c140a61001c2c3c8507142c11081c506481c10800106580c40505980b103070403420003210300400c101c080440b05a940040c0540c00745104840110700078120159100301480c80410700909060380041c265048a400b60f07101102a604c1e6580c40088030400d10000b810b0b6030150906500140d0750480c04080b0304d00a082000c0c1c0082541c0648032030038801d1041c0d40350181007200c00c0c41000f10200101b0340000090b81c1d04e010381070805e58003614140024210a051042143c1003031a00081c0c1011a040042d821002c943c450f811100c01801d0354101811140300d40095943c9580e82c0064684140403046603200141811290360f26 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 484047805 1250 484046555 484046557
    0x51018030c060b040c08040501051506030c0307021905100617150901142d041101030518010f0c111603080703030b030703081902061b0a051209030c071d010308 70
    0x1801c4a4403500c620030f1040c0c541d03580c410400141e000da114902503203030501e889821540d00801d0607100c550480310001e01902e50702c0c2620f5006034140141aaaa01c95107010b1303180101c00c5e0401a42010520540c4040080102c0c442140311100c5406200701500d036965000c002c1402400094541d004c0b24120f804a01c500004540104e10107000140545d000c20a0784a12502281d90400340050a0f00c15994071b1980881d0302224038240070240031a0401d50381d10074019803548000c60400d52120013045000702003101c1002c601d0b20880c000c101d1110405941c1000e0480c0e10a200c0c04a048050b08107100440401c5141c4a009002e10050a0302d06564404255401c01e0900750101907031400c0c80c4040361400c101110107180142001500c8a00140d482100c01c0c0720311400000b19040f00081c80400c0340c0680d0540101c404088100361a0340c0e28060845460203980c05c034610381070b08801882502c3c28048010120f210b01072040d02c900386d840310480e5241070842d502c101c0144201c800104040342c0b440c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 484049055 1250 484047805 484047827
    0x1d0a050105030d03110903010609020a12060509131e050f07060e060304171b01051501210e010f05010f030209070c03080f0606090d11040e0c0105030a020c010902030f070305101803 79
    0x4889400c01b180300e8007003421104039811203403000d80d00050015540e40c01c00326040803100c1d0380e001400500e08200208000d4040078050310700e10504844400200040151603558803410004504507101003410505d942e89022300c0c1e840c099000340d07071022031940d1040350b44000002c03000d0076183c13940d11f0355a26001c003d960013003009540314090002c82034070f0a110b82078030240101000041200e0400c1890016607400708000581800790b40e07008070800c035242d03802a81156045030b400190b88404280054003402c00c20a040d401c46140c03c00206500340ca03460404140e900a884408140d5140c40c41038401070000e280150100d1961000101070404005100750301080240002d401d000c0800302044000030400c0d0f0460312114006a0129a401c00b44500b1008400520081501a81400c00a080d510000d840008800d8000038101c00010013504200300003a0f000d01250942c40d00481e0154032040e0b2808100e900340241002007019403440d00440b4102c504407100e040b0102c2c4590340564803031f0140303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 484050305 1250 484049055 484049081
    0x20c09090f06190501051e091909050f0706030c120b0f040c0e040509030906070f260d0f02040e0105012d022407050301050d08070c1d0a050105030d03 66
    0x301030445802907007403101900400d003644082110030b210200d04401d1354016001540680c051450f11a02240840b03c1d81e20215401d9444101a0700c0e0355040920f5003101c214500401c604168105042000016007410020b4031078003a030340807580f584421025252a144905e0000d0030030b001008031222540e104244a05004007205a00ca04200128040e5003001407070002081c840764155101e0300785401003507444509a00510302c1c1c9400540011020300400308060a8441580000d10030070440808161031000c0d240b2074541c0400513030310018603603441481c1305d40026080c62019410850035000b42c906031003100200404583c200001140c0c1c42e031041107002d240040c0b6000241d200d81c034680c640c2011440c0ba501522051701e0341944804004a81d400c140c2c900c154040811031001d0b40401540e041d11021900601c07600c901e810049058014100090300d415000d110005001c2010b64007400491403250365110300d5500c001d60481251001d02c562601742d000042a000f401e4841e80c0003401a00c0c00c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 484051555 1250 484050305 484050313
    0x9080118140c04180b06120303150102030702060705060405070e090a020402030c120720060c031f0e0112030908030c0705010503070306080714042403030c1119030b0105010906020c0909 81
    0xe84006019580e01c1400d9400f00300d040605003085c05002c2e82450361104c400e81c0d541f004412100d8440e40d603444024084240300b08089420900c61381f0900858100c645c000344810b03201c4e542418840d4848100746c2c0d0271541d6101d072400025807030f0790320804c81d8480c400c418040c142542654007448060360001740741c3c1e030100c0404c0107090307030b9051070700c40080c090140c560760b80c00e800a00400650f0071320703110006c0040c5540314804011070160b000080725070040d2480d242c001d41108140480440d60070540010100044ca5000411201e000c6004000190b020340e590704140d55644060949a208079000e0a225401015080c050365010301c1c01941c11032034500d0b0004080303a0700e0600fa401d001a0b60000311000e2190b5004d55964a014041c1b4201d00c01e003200c0d000c5039030f021189028044030300303880001e040c81003198041d020b02807d06032801ca242e90280c541c0301d00000100c2c0f0b00c4400201400b080f2181c1030076000205641d48101c40c410103440060f001004014011000c0150385d0760010000155442 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 484052805 1250 484051555 484051573
    0x40603020d06050906062b050304050607081215010c0f150e1f05010f151808061b040503120c03091005030a050105090c09190506030c0a0908011814 65
    0x4400c420140071070302580c1c00040d00e0500b03100560a002004d001d0622400d04107968440c01e4084040030300420031a040120312165492030503500754003a540c0900c0e4490804980c40301402039003801007840d01a840995407182e40c0e5031004400c1400c401704642d000400b07403501907000414500038100c166005013840c4184100d110048420380b185080805e2554002211810504140c00d40c0082d2186540d10705010035070500d00d075050300d921a03205505110603601894030385039009200c141328000150925000700b81d207440f25140c0c0c0751010b1720b0080700e611907205040b02c146201416074040d0740300207020303292000140704020500d80001c10510098041003180f4070156803240200c0c240320b060350315440d40b01c0c070b070440103803041b03520590000740038141c039604101802c0800c404840c50300d03004807502d00500c4000001559644240e4112540050002051000e010a050003511601c00c07681c0d80d1480300c94403a224582a6031821003400342c1c03940054001c0d80000e0601c1d0503003801042d85001c5507084a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 484054055 1250 484052805 484052809
    0x7061d070603020c06061c080a1701030605091c1b020109050303040e1008060f0711100608030915130911070c060315080c030d080603010e062e080d080604060302 71
    0x10310264480004a540010010b484501c103200b10780d804034081741c03404800301240500005120541c2d000802c3e09200040d540c40d0103000745210b07681d0304160540024550384900d040310003840300341c0380503545110310303035500c01e0f00302070f0110f0100481c04036500c446800c0c40c3c5140741c21160340b0018080341400380d100d90216150718104003410003881540c4440c00a400d080200404640b20740d08002c1294003c0810490302c10302c0501b13480e4000c1d8552034046140c1c050300303201c1c0741031890b81c024598206082c02c800103004d08000001d030072a0300c001c03211003251401c1050015800d105202c0c00c28001001c10104000782da0841d4843c0b43e68410304031281e4904406681c540320183c00c0b5400c107501081d5500d01e5500b90712109400304c006400d000c8002c0c10f00300002c00010750f80c1c2115007446c108201d040f20005440b91000c1d000184552700300d10403103540d41440c202c014070303403034034680c2c820350803d403044e41d102070070700c07940514004c440130034020381b4100c000804122055080100101d41240e101c5400100507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 484055305 1250 484054055 484054063
    0x1520030702130203011401050403050a1101030b060c1b030a0506060904060e0d030207030906090302090402210307050c130b09130303110715141509060a0b160302070e070507061d 78
    0x80002800016605e40c10300081e21107204054104c541007060a100038400100c002445499181d001403200c0050103001c80100c0c007400010b416145c0000002ca2880b50340c2000085400100c14007503440c511950441d02810740c0e40009070b2028140e0362042000c5a49410050708094110340034150228100a9207480986000c46201003c40000e5000401005069220f4100b0001d480d96180020310780345076030001480f00d070014102a200340c081c0040c40e4070444551410074014080e503020340751581540d0918a48480304040c081c0d008020030085140000b015124050a500c0010a0114242c032140704002611085800c110145659400008401c2e500c0c440a488241d20400601d001c620ba0507031104280d842840c05c15085050100c00d02c0461030009111368001030381a21204c02c103a4800f000681a01034503841313000381841c0010ba24440801f0703403910300e000c0341c0a80c0888041c2075480a450803440d0b0100ca454002850030320501c030005074aa001101c940400c442d140f02c544440030195410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 484056555 1250 484055305 484055329
    0x509221b080907090c140c16080c1801260c180601030c0306081c090b0a0315121106070f020a0803030a0c020604050c0d0507230108011520030702 64
    0x4241d00c0340412210b010100302032000b0b010b4054040c003e403201c201c0c0240220700501000311181c0000304548006050400048075042c501c03822441080b5035a24031591501c86889859008018410903042220016414181201c90308001000c4108090a40c9901131900c4003480322103020700050400940e13210075600c00300312000c3d107100220707041c10300002d021103001404003800d040c10f010003084010030114141c08110071350489403010444500088a14480607088401283d80c0400c100303040940c513520590910550000401d082d40c1c44400c05107860705902d04c02083c5d6145441270307144904114015215061050310718070055900c07540010a083e0305a0026119a4800701c1080000880c902a040180380703980080d21450401da166640c641a480c02c44d00d0180030410004420410104001d000800c3d601c640000300c08201c001011142c4504403ca50010340c0c40d5001152881b1803805410208a064507101e415420364481c09080011110f1aa0f00c036000900441025898410350190 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 484057805 1250 484056555 484056557
    0x14010e07051611181b092b171201050105091f0c03021009110415081f06061704060902130e0303061e0105030a0509011803030507020105070509221b 65
    0xc1141c0b080024010401306140c07004144404120610803004a143c10084005501e030031020b40d2090580041010f01200a681c0e00400d00c80e03818013220941d4141d500441170f88503c1d440d0b0b2640d20b1100c034107800e41c052020f51034424810640100801d40c090b6000304100c2c0300c06000840701490805000b603001401d0301e400070100d01030804110030594103018030001c842504104106030089a250200c030b0042c0b26000601a59803080e01c3c2c104035072802089401003282d58101c0320030000c0e25084002018081981a0f05036007440400704410380540d040340c82401b2050749580040c0d0340c580720007000d030144c800d05981210744d070040d41505101d18003981071600007140c0110b41da42805020f0102c0343c00f2600d00710320001c00c015400062680d100c41140e070011317807001c4d0105043d22022105401801c0c840781214010710b011042c0c074100f68145d00050300c03a10841c0c008114941d035120080e100743c4200c08185601c0900403003503111581c040404013a07000008440002e4038003842c160b0004110047d48440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 484059055 1250 484057805 484057823
    0x91509150103032007080309090c04050a0b0703090b09010516030e04020a030e070914040201110111030703050106020d081006030c03020409020c070f09020f030f04051c2114010e070516 81
    0x4010700c21403115284d11039001001800402d1a107012540c4030301586203814820304150000c5084868400d05917000303050000c110303020b07240e070740d8012003480e034000402103001c034900040004521130000c06860440384103031a01ca01d000c80b00801c0142e46002c01e0400c07000e00c81c481d031480b605500c2c3d80c4040c00110113143c0b000241c0910150440780303803c6665010b0f407400c50a00020003205426003000d80c1d00700d64282014403000c1140003002c2d015000c00360b400e140e401c80100030404681d40c5038003c541200c140d41c090b036002040e2048211030a13541210b034030720b550203003020401543c1d20a03030014000f8512444c0050030141c0f42c00780701040e40d024146203d03c40c0e002281c02e209890603c14850000c00400e00214940402038002c8181800004c00030342603011000300040c04c0c482c0a00201c010590207491801d828020660b002d400040703400c62420044c103026540403520f8189128036074001c0e03181291403006a02c0d00c00109801800104607004100c1d0520031196402c41000002d500c01d440b441d480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 484060305 1250 484059055 484059077
    0x140319110111040305070303140d020a1d0f03151e040602090405010b04030b01050d030c1208011e060503180718050403020d030908120705091003150e09150915010303 73
    0x2060a44401042d1503081e240200020800030710002102c104881d4142480c070a038031068810041c40380200d0003a81c001c94000901a081c10b988401124502001e9409120803940018140072050280d52006900350340a50100c100c00600c009a80e5444100c40000c1141c0303000500302809408400c2d941164059008107100e41a0b2170240561405800071a5070075080914548401031010010300c6100e015a801400007c02c2c940304100056119030804580740d40c41182d1040240603c0f000d20078249080c4c020001c4030603103070601d12203108441641d0b50391801c54441c4101141d41c1c000648041800c0c0c85100400903a06d1604102070b06412840782d0001454945818080d05160461107940201483c01104034005030254040d81da5500d001c1403600c400da40d80d030105aa4070701c07c500c56650701c20146100c0d45070003135054000705102142a00702c104100e070f940034100400c0ca000c0e20907901c107810542c2c1541800481c502e400d41c0c0099030310100d620640d444015900c40e09003c1c1c00c141d00040e9140b4075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 484061555 1250 484060305 484060337
    0x5040219060c0b0f06130c12050f09060106050a17060f0a0b041509060f0c060b090a0f0e011401120305040f15020610060503011202060c0f030703110f0a140319 70
    0x101d5a8404c03c8500344a50618290340004d2541d0408104d03100040d64650b01045618400d42e83e0302c030301e0124174400f00124203001c0c000c2c2400d41021109004540302c5c2c0400071801c1441001961204040c9454840502d0f0074041c2a0706010b000070100354015100d0007104145a0390444c8210040c58011421942c1d181820407140841144005940501c5141c803030800c0740d0390b4040095020310080c0d1130101300744240c3d86040c0024240a901c016405082ca0b0244550210145c3c0134000c80d04034010100681420140c9072030aa0b03001c0d1021800b50942c40c001001850b9551004600042c424546240f0300360711488019140d003e983c100c01030301022803100ca12550313010412144c000042c89501783c0e4031032410800800a200501030880c9142d5189112000c548610055030079921082e826103051400d2103c240d9500d4101c42029400911101c40c1a00061004182000144902c00c081c0581450f05c0c0c0303501402c510004501742c1503110412403a110401d10200e500090b620b04c2e074564200c0f000b01c01c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 484062805 1250 484061555 484061573
    0xf0f130c0519020a150f0e0d09140103180f050a05030c010903031a0d0615030602040b0d0510030c05150702030d08060102060106050c0613081219230a05040219060c 72
    0x9000740c25584000c44c0c01011600f041203800403c40c0c481c10105951b0400b62100e0050014a5954401403284448040b40d0a41000d200c10039101d03035920b0f500316420703094011416070320340312905807510542c03d040801107180b80420303003280740c005d008941c07408180e9500d07580342d2303130050500000a9641e1800601019818011183d00007030ba400c800ea80300d414071000820000c00b0002c0104241d079038948008940081401e0840215080310046440782d0b0b0701c8055551079405512080031a42c985400545804180100070043d6900041f240e43e001d418034091120200001c41c21002401082c84182c0059a0800c281022080c1e02c0d91004600d00b0608006880c00106802c0b4909000c0c4c14000d60501d0080040c01680c40003149026004c11501390814042074402c105010b14900303502800c02c001464032042c580588003440e201001201008170340c1c0c940ca4131a401900800b4401400030072074a5941390041c9800038002807170724544080b2840340d071035103d030264090b00203e80c0e0503141c0c106202c0aa4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 484064055 1250 484062805 484062847
    0x13060e0612060a0504050c0a090914010603150209130e0a0b01090e0307020f0d02120f070506070b01030b100506210a0e120a210b0f0a050f0f130c05 65
    0x2881a104903048039541989410004011103442c03135403400080d051002c01c001800a07aa000342411030740703940320b200ca82e0217800c440b4000d590b0f00200c00c01264100360305116280032203810207494904000c501c09040c010354010000281e00407224140c24044c0495440b400f5544111940280b500e000c06181072050368405901803a0101e00d400c0600300b103404048210388203030754110b440001900b000000201205004078000e500102094849401a40001008400703040c4030b808441015655200308000c81c8902c4d04000c2c200c0c8035030001000040c020034400d64000da03000000707201003615540821015044804014000740b0800303d0050003681e41d152458210440d0320b020300a565003445920750340d00303c4600c20450704000080000d10390b481030314414032040d2030821014070075080349503100251900380082489007104000398040303031a00700030740030449401802544000c00605c0401041c0c20b040022030b60400c440c4030852500d04941c1c42603280c258140d40390140c03520703808034600122240340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 484065305 1250 484064055 484064059
    0x31406070504151106070e09010b0f07111c0803070306120203030f071b0305060609070507150f0e03160c0e04032c041505091029070213060e06 63
    0x110288003030654098100d90036540e05019079404510110320407a43d011000c161000c00d40150418442d902d035000080020b1a40212a21566030f62209500c502c10b100f000407803442030008001410000e0f11000203109000402811031800b4002e05c00981c403404458a41241d01d001d002041001060b050f101341c0000d0000c1c1c003050300006a03c0e6010030766038469803c080074400c0c80072131703850108803140d10402c0319941000101c0c40d080d6501d01c1c249607529001d6482c5407044100310000303400756105900b503e003c941c111007010810810301d00500018060480c1411019450700d84103000f004080000b480c05054200070b4854403091814200281c1200f0340009952005040a00c03000c039602c645e00310450419004020f00d09130b0f40c148403880e00502c07445000c0c1c2250230315001c8102d104401440908940c015035204450341d881d1740d4907900407c242e002e0411a00120341956240d0005409861507010b03a40c040b02c1c0c540304654000070742104e11280c0111605441d204240618a400c03441c050f0400301c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 484066555 1250 484065305 484065313
    0x30e030405010909020d110d060503010b0d02010806240a08010807050409020607110103200306011815110f120403050111040f0e040f0209070c0b0603150103080a170a060314 76
    0x70300000800b111481c0c031407160255004203d14000c0d50055100d544013080064055aa0341c00e0710300f40b10040d048070721800340710b546026410340e03c6041c10b00d88107080d0741d8140c0da200302d55540d0404014600d203420b156008030141032414000c01c080004002c1080c5801a11404a190314004056182202c250006401030b0300b003985d40b40041c0c5682e0165041180c1c4644401200b42e0302e140101d000b448601c0c0b055281c14245114404070540d903100441c007440d800e0713a462030216183d240e018507a804921038003c0f818542d806600543d4800c941d100140391580081c3c600c04044c50003924034192240c0a40d845140c4001020800c0007400d20890b420960030001d0305062625102a40882110a11400b8105000600002c00f0030020701254031007141e0007480400c6074140801c00802020100004461040c603032408141c01d480e00268480207031054500201d500d03070842e90344d01903030303000704001800380042e48800001c00064440c04500c584540f00000404900e035061100d000e0324a07900034940385d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 484067805 1250 484066555 484066559
    0x1205130807150f020a05150106030f061503020c0c090702060f071d120a050a0804170a11040c050d051e0708060a0510050409391b02010e03061303030e0304 68
    0x300766100401d802d08181402d03c041d0920080c2641404410300c00100706005400100d030382c4143e0102c1c91810f03520641e60800407a055400f40d0400c44032103014180380011060f1912903564403039001404c400b601082034840c608801b8012849464046d900070015800078410005103000400038264010200e141c1940745041d0000010385103502160105d009003031040c81009243c01c208401c19a0320303404811126640c031141445010340e0014040d011b02411b40c10028600e1000024610b91100d030414288801e0f04102c8040000038550340c401142404000c3c0002003582da014440e5a2040d0342219044090001d40c405224840030010810018030900c031082c0002511011440380076200c0c1030b26a01400c1d1003211054030380d07000766070254900c45d003040448840140c0348450000202e00c4904005c03000c481910000513241045030060700001ca0010703180c01c03c4080005000421801810081300812000b4042806c110044030703160825400020010700305a071502c1000d41001c00c0c00e0280d81018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 484069055 1250 484067805 484067819
    0x3090108070216150e0613140102010b0303161410090209060d0b04030c06021e090f0d03020a0323030c07050c01020f1e120403052410150306031205130807 68
    0xf40c2d0754010400b60046240800c400180038500d81881c1c100d00420650729407401189195070b81c2114000d81c1f0b440f920081019002d03500500032035241d448021701950030920074a00744149000c0110041d144d0031100705155103083c005020150810f0008600410050090300610001140240c1018000d15002c407206020030204084150055450b29100038180ba0a04098001e4014500b1000c0c614131540c00100c2c030504034000501a40d00107403203204401c20300c1410400402318004010300560003001c0c82e040000d20508204000d600d083c100c1c6580c003c2c41001191598000b1520100ca988000581d003090290030012001a84000d00c0101000e412a54895440d100480e207031560303100d1f09640401a01105000d00304582100c00c8000e0744a96490504565841603041e9050080c0400e002403441a00613200b91481002111032084160746414410300f80040f0303440150040542d1820003200050450442940149240d62003645940545040c40307403c800f5a0300420301540100c2d402c025030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 484070305 1250 484069055 484069093
    0x50706020111040f171c2a0b0c0a09080d0905040b03010603030915110105040305190e0619020307170409150e0601030b030f0d050d050a0209010e090c04090e030901080702 75
    0xb8401441070b240e4540140c1c02c119160180020300c80308109607146c8003080055100c9000d403400c1915100340b800c41c2c103114640d400002c20640700500913000e650b000440504008004041d45c0d001e604d8260300c190394804e807190900f983c03424140c00268040604212604d071034010361400040c101d008010007483c40d64050b102c400f05114140c8003481920344111003074010b4204450070030891f0001d00035881d15240003001e550059440d01c1c51608007625645179184291211150080302901d41c1345409181205042040c0c111401d010442c401040320200254a00900900a126250501c0d444070304018559040d0b0702c0c1c204c035069103452480c0d41001000c12000110740c10600030f082c0090080d04440c04a070802203509402d4081c1c0c41002c41c10401c03e58040001c100c80717050b20b442040380c3c6e124405500240d01c250314074a800100300000e0001c9600c0c0180304680c000e0843c1c0ca400b4682541d581c080c0f802d980c14801503110319040490903070700365600a13042a0344414540301419003085076071200351007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 484071555 1250 484070305 484070309
    0x11e14040210050d0e0a0201030e07030c0308280c11011110050618041202012a11010608010f15080c011d0a031401090c05060a0c0627050706020111040f 67
    0x701c0c00d4090500c0d42c403039000b0402c40b00300310001e80c414001415040001c03aa200c0b1000e0b4100c0c0001c1c82c100048a000c0c0780852050280c1e0382c020481e241041c5180c0310410260000142425000000c405010b61141c10801111130300700e0710b4039020510116401c010b5040500740114a05100861111905e07900000c03c0c0e04c07001c185641c100103071a440701d0006c0348805110800c00c40c03540009009000a001414898640d4402198024008440014040a1a0042c5030280000c00e0340d0703c081300e510140120100c05518440360b0000a5059a42024600b910000f5100c0d4100d16510300c00d400580c42100c01c090007501c0301e203004203402c016000000b0810200128180e5065a81a00140b51507880210b03140055030000c1c4058210700e6403005084c020a101e60ac1201d10b030b0710346040000c140c180703001070b558004041d0700c500070001910b4803420b01620b0101b01c0c501101d0742c01b0180c0018200704c19949400540548005c3c42c2160801c040a800c69504050304d82c0340c01014801040b4000d0050304000c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 484072805 1250 484071555 484071559
    0x30b0a120b0a020a0504091d0609060f0912031617130302070803031612020903070603060e07030b09060d020d0b01060305180a0f06020f120405210c0601090905120a02011e140402 78
    0x60444412145203c640c8c141e48410801e80907a07401d0002d01980000d100f4024424101e034543c450701c44800450303440030001d1084c12141c10604c00200c800c01101e116100c000340c039003003146045400c03800001ca003800846142282d030b19800c11030000e160741007080801030700c00d21005500d0b600b00888a8941030700100040c00400c50b02010f014469155501940c0d24104044e0841c2d095035240e803005000b80c8400d01894045612030000200c03000e00c40d00800034401c078080d0004509441d80010f10810750300d01201030342c10070303940541040000c002c410824005e2500390744c0040c09060800030042510f0310441000d01541c0200e80c040c021804c0480d801d5015135101c1001a51099441000d07022409803400045030140a00c00704001c0c42000b189809403410fa02c1d8608001c0080021009c516000e1051798403c15405080144a000600c0e888400414002c0341180c40d812107000c1e41d4400da030701110003800140d468091242242081e07640c2d015036400f01143c2408203042d201d0034070030b0714000200040c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 484074055 1250 484072805 484072811
    0x60f0d0813090501061b11011b0203120705010606112a040c02010f0e01020708030c0a0302040b030712050601050702100e01030605040204140a0b030f0a0c030b0a120b0a020a050409 79
    0xc001500c82290801c2078400150a0215030701d614600c003c04003441342002144444107040384d06842401c0880003190f004100f10703400405000110780700c01c0c5144100722055109130031080941c0d4100450f007460f03c2d0001e180c82d959051483d00b80d0a50b111540401c00380030500c5101c40480001080c010240e5000180640080441d00d502c0d0703003210100c10309250020318040c0060754096064000b814540e5011b072090204119000c840c0e400c038840c000c0090460b02e42030011540740e0030146c0041245600600e005824692540c114a066900070b80304440403584d040b040c103400c99800d001d1f01c1d602031400d0030308504205858000c60000c0006103401010003c000d544c0ca155a8001da01000140a019000710740321034982444144254000311444c0c0b0451000c103001400c5203181b400c40e0700c03580c5420341c945902d4840c00c1019018054619041d0149a12540031410036200c401542006106209008907040b0280c102641c01d903a000c0c10141d20580100000d5160035000b100315000c0302c11400d000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 484075305 1250 484074055 484074079
    0x31303080a032d140709090b031002040f09050903032502070f09061d01080c01050304060908070b240906010e03070e09060108073602160507080114060f 67
    0x214000d096082a40c60034003c40b02110850400d4401ea09031484040c0e10704210980c408075420036160011141c103000180b00c09406e008204094010581203075000d400c071640a2080318a1500703981281c0c210340aa140b818004000400c0707103000b183d800520400143d403440c285011454890f12501d40c0c207604c1028803031b41c54002c01744208495001816044414440251282000005031405118800030760b403034544100c03100d504101840e0304a5190038003c0072070080790801940c0642008100303982599032244c41c00041f41400d0000c06a2a10503500ba5281d0305d044a403001c004142d0141c0c01565540351400403950344c440142d826088002400d00581c20304807a0000391400001d5000700400d01e0121003413080e44100010700758140c4041800b51518107850b59114108065642c40496403031269900e034100d201c103c100308441107485147d01500d0400107640c0134070568a141d030200d030035a000c1074041007002030a100307078070840b40000403404250600341c0000d0f002c01003000510b803191500c01ca038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 484076555 1250 484075305 484075307
    0xa0f030c0302041e1d0f301e040f06260c090d0f0c06020303070f03020f04050d0f020913020303040b0a0c0b0a0507081303020d080606090d150e031303080a 68
    0x86000e189015030005d000509061038440080103002150040b00c1c881c8440300a440f4a02040909840c1000380c80500c0c0041c445d1504001c000040e00d651400300030030405203441c0c05501c0602c03501d50704012421583c80f40780480100c0210059800001004607840e0914038541044602c5081e800340320700d80c4800e5403950034000d000e030700c02c91021a0f4400d40c00301152081051100f03410400b280502084a0301643d50003050f6200c3c4402c8814500140e4146c80407000300d8029030180c0014003403000d259080c9502c0b100031407098500040161007510300015000d0441c81c01210881c0d00604031958118400d45076030120b550783c09070f405440070a400105113410b03018824040b07401529040895071000d800c00310b1240c40182415105440019040342c0044c7c038802040d054021020b0381035004100300200f50b24119280321001d4415a072200c01008001380640c0d40784242202c860042c0c4c65985060030343c0107501c0844104900c0d1080070303002072140c078111000741d41c501c20840703070010314075541d501d440c0e64 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 484077805 1250 484076555 484076591
    0x12120a0c081609051008040203010b0d08121f0602010f0f0b030309010c050c0d0f03030b0103020304031b0f02030f030901020f010b011b0303020c03180102010b030114070c050307060f0504020a0f030c030204 90
    0x304c10741144013004c0c0d4150880e403001c0400d0081e40291300030020b040f0b1000a2084005500c40b0160204004010301c8003220700e080c0f029580180c0038403030824200b800300415000c4044540c0400c0c01130f0344071030a004958800b0303c21951036400011040200465170004642c0300c1c0540c0c40c00d01c1c18402030815030b405118052101070385c4040c0062144201c403210345420301e010a10f4500550000b40740c1400700e2900e50007482220300907a055101c5003c24075144c402921220924002101c2040f2696035000c01a1010040b160301c000440001c1c40d00d441c07a50700024501541500342d240340346e050561003603460b40c014039103001d1194103080b1580c5c4404207040039000b07446415990a00e030320000410748800c00303d03910000084c0c03600342d000f0b00005000408041c00d81c0c9a403280c0c030b41d07000b0102000c941114010303103091154034850801e403030400f5007685070b007002c03240b5054030b0184240d203810800c4214a45007003a40081c1420004002c945400e546410030b40381c1c26800700a0241d07596180b04400c1b862480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 484079055 1250 484077805 484077809
    0x120e01020f03040c06110309180601021e061b12070302220626311a0f0f010303050901120603060504030c02240702190812120a0c081609 60
    0x41e0340c295a800c0602c0c000701c1d00c00345446440c00080c3c2a806040b82004080200e07400070301e00801300c1d038201e428410014205403020b0a0070b8150303c42c01c647e0380703c98140c040102c00392151040107845036260540b01c0840d00410965040c102e240c08001040c006001900020340000182c90016140e200070807502c00d160070580402c0d01800807002c0c1c0055034035130003880c00007681c2c20540e400114224114506007403540c1503e04d040030018081c0e0225495000c1002a403d1103a41c04c1c0302001ea1103aa290f04001c50b02a241c3d82403403405103410041641c801003100d07608003940c621103001940c51030710010194081c6841b00b0f41048081b4a503840c0501541c1c00841c081c41c1c01140400490910703240c00703404c1d076a0500c001c0b40144180d20008480280300000341e500f07601c500703070402d1400130a0741c2000446075100c510030030010301002c00821413100402c122410511f070600c18030340d50300c100b1240318081d0310001e0410020605104030100c840c1d500079845900210003024514041040d000f09852445c010f07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 484080305 1250 484079055 484079077
    0x70e0a02220902040303030b0d0203030d0c030b220c0203070c030f051c05031005010e0d0303051f1d061f0503070329270601050705031317010e070303120e0102 70
    0x1c408007140242499000700f04691003a10104021074044060250689901c40c0196058005000014140740c00c2d40115500c6442d03071600207161a00540011501c007131204080720020f558141000d01c4032803074816803080800b80d00013142405001c1e65020707403a11250100410841020000c0010002e08010040f01c070810080558407244605030028840e8100315283c011140c1030440010303075940100141403a8078406003944050030156101900680009008104001c00160002540c1c0040040a0019020720b84032810f030212a45840d0540704409404284034880400c0e01020f00078411505440309812403d141c1c0e2070303541d1440150020107840c0140031101881c0b80107020b87e0041e4091204502208a40d60040d00444140c0700101010b02880d007000c400446001c10100d40c0a00064000f00d842101228500385040c0014043d203440c41d8001e000c504504280802c0d012028001d0409280481c4000c0090030701d103440050502d100a280d00700b88a50303a041d042040725082d01121064409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 484081555 1250 484080305 484080367
    0x30d02030c0309061303051b0712080309120f07030f03090c06020123010f05060306130204030503070231320703060602070f2309040f14070e0a02 64
    0x1c0d60240c2515442101d015000f40903140c0002c0b182c24040da11840019059546c99081c046042d00410002ca02e202003524188103400000810042c442c4400080c0b0f4811460281c0700d0a10203001450035801c180492980601032103041e040742d4100c0192001a41c00d132410502c030b2a0501425001060104c0d4050035030a00c1c104c001c00c43c69015000740320700f9420150b5540d61030f0309000e20103000c81c50a0094010b00342100c4410803052070041c018580040c0010b15512111300b244100604990140c0d208035120f404c08504201549020500d140301c80e40c00c0902c2820b4042980c40d0864035040c14508016950f590791500400320103e00d09024110a095000702103904503103203040c8102c041100d0b0000041d04108010420b03a1021800008132003c80251010680c1410400c200c020b0b0700a250302c0790302d00c10300c0085649560300d0405c240124000c41e200300e0306045a04090400520714014400150320400007001818080703ca03040d0b1110312032000685072708060f40026600c002c1c450b0f0039006080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 484082805 1250 484081555 484081561
    0x10f0507150212040b090c030a05100911030303010f050103110c0a2414011a1303080304030c060c08060a05010503010609140a12120810030215070c09020a0c0204150b040b0c030d0203 80
    0x501d00205c1801b92410504545403440d07601c5c1050342d681d20003030000307000390041090545194a541c100c40111031043c0c003950f804c2006a000300c0d1031a00240c0c08500d050750101c604109658044c400c125074206140359003458039084800b4184d403282480300091203d12488241090b041c2d07466001d484071200e402d024040107414000d4401d911400b0b0240011000603444100c0c20f81c031003102100c2205854880a107401441c0d5190740f103007504010f00640074406141c914000017200ea1048103107190050725480c40d00d040c42d00178801e80450607040b03e4140b00c0c0030001800b00c2d98028105008850385941d01b410032511000224140e0f4040d94132070b2320710707589804450302000001d0400327859030a555541d410300b40d40d514040c003145000d18440a500125264113080310b4004d07030401442d00a00a0700c4c17600c4410342e41c7c0d0091040781c0c4001c10080c0025140c4010804600e000e00560f500000105504a00c036800c00811040c507215a1082d142030240004008420181c2071007a5400c3c50011441151a89 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 484084055 1250 484082805 484082813
    0x20010b060c030409050a02030112020d11060d45030c06051e0a050402010503040623040b010807170606010e190b1806160b0703090203061006030b010f050715021204 72
    0x281090013240d0b49542002c0028941c0ca46074420b69040754800540c04003103400c541c091007807500301d0050035106048034201d03010300350301c07110020400305001d000c002030032030350942c1403070070004481071010a05507074001d0400158440701c4080900c0d50030412200390000300ca02c1d06036111040d690004000e541000104905101c0c080400b03407102910b080040f005a4401e07a00c031045400803500240825018408100455000d52040300883e0114015184242c0710600307085490504503405c550060300e1800500c04001d0a10110000b0214852455032007803000041702e4541c80000d015504010362904000416070380c403080e0b102c18050107a007080c0d11350340340e030064021907200c0c4c024001e01c0401c500c514041c60401c00d0840d060350411803120340b8541032a5039080300c01c40015040100305901c0c0c02902d000745c0d40c02e00034107000d40c0c501c0030908541441e1000240558210480d010305001c080740c0e07401c582517000422038400300c1e0700010b03000d40031001307001d403400a0040e0f0b000d0394294803290003084100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 484085305 1250 484084055 484084057
    0x6130504020d0201180e0c1207020f0a0303110408011b110106031a06030102120c0702191404090c09111207180b07060609020f09031c120b0f060f0406090501080720010b060c03 77
    0x10440707032301544289a88802d4140d03900c403512a0100420381c84142c002c00400d110b0b40c0004516103540f1000ba01d01039440341202d0070340e100d509150041c0350711500c031211155041040c00010700302c01c400a018541c6591510b98100704000e0307440f0800c540200015080e80c2e402e50449000d648641c031450f0481c01d00c1404440190403d55049028828807201901e459542c11029001c076409100800c2e084100401803001500310400202c807002442100800c91404c0d500a450110010718100368036040f625001d1004803d02921850030700038031842103104050440500400e9882410079144d9508103460018001c4c801680029040c85c03011a021041c000140c0051010a02c102c084035030304c41442040600d4090b1025050300810081044d040c8040e09980000c450500300400001c840b40c5400e0104019500c03c11400782c403554005010b005460f04405908080c041c28030b00207600345444c5401500600e80d40c14040030605610f0002c42040801b500000144000a0900358503034010f500500e0703403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 484086555 1250 484085305 484085317
    0x30d030e16080d020c18060d020d0501050c0d0b0f100f11060c0a3b01020f01150503120a0c060b0f0d0b0703060905040c0b0c070e01080606130504020d0201180e0c 71
    0x6000b0400c4101c201e240c86019a40c0200c040302603584541c441f00100101400c056008a070030100040504000c10405e2040d90309c5810ba228460b50b07204c8060300400211021103080510915200070504803d454160701ca0041d0401030034070b00d014440b90001030782c60b42021200140148100c6042010401100001d455110001d8544102c0b07a8644041600c1c00891210324a58030b141c0c4251100c50f02e203000705200c1c4c80c41418010f6030700c0600461301c504c2c00d40392500e00c803c2000303025500402c1681010001400b0100007480c038107007400182c181c01043c21030b100030082c0560351500b05000b0203503100c040c5098200740c002d002102c192001d2800003442075045444402081c544000043c00b40c1641c02254410780e4007501d1b15000c28100101e2403203903080075268228030f1080c08008100c100c00384442d14040c0c500800141241d1819108221011a5444464002e64102420300005850315917240c001e40c0d609081c191000c48010021142c1d05400d640a03001545541d02404119a60709000b051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 484087805 1250 484086555 484086557
    0x30705070312170c1e1201080f0d020a0605040804120f0b1008250b040b0403060c2c040f020a120b0307030506010312140a1e0e030d030e16080d 63
    0x760850800b0415030310721568003080720010000c000007403040085000106aa0f050652140101d00710310ba031041c4132034015016002201c8901001805018000c01c01c02d01c7e4606604002e0504100341c00c4c009403154025140102103946903c003041c05c10201e00c4c241d42c05403040749107104400e0480e040c080383c0c580e2484000d0743e005e02d528000c0b4060345c00081104d016140000006c00014005100c010200d010149909041104201000c00d9080080b0b009000400b038003428039464508500309201102c0b81580b041c41480201e08007040c6a03030342042203010302c1080103070a480c44444000442c0140040300c404420141c030002c0c031584803941009050350b03545040c413001c10203808400d050642da0322290001800c16130242d07004200142d90700c030700100143c0c02031a1500104510031000110b0b40c100c000b54002080300980d2222442c0312001020401c803425280c0001c0c0c90020300046519003c4003c0b4900c101600c1d40c0078980e91203030800c5400702e204520105644102e42d40c562a0703898441030341200d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 484089055 1250 484087805 484087823
    0x51203120c1b012a09030803090c1c21080105040b03330a0c0c1506030213050f06090103080409020f073e0a060e0d0507081020030c07080c0307050703 66
    0xc0c004c0303e024010045400c3c001d40f02c2440341c3c1d0560b00c503200c1503040208202e00c1c52080d02c82c04c6095456007540c040900742c40144d4840c0900c00342c0f40c55001010b110742241c2098104015252400b030f400051641100e00554000807007401801c0801d082001d0107181c88108003d002403c68100851440d228101c1e02c031503403007455600d070b102040083c0c444500c3d2250009084c1941440401d00242500709407851016000615966981c049007041089001c0c094109170703280c040040001c5204101c5600940840d1100c00039815560b51003040c0c082d50186004256000c0f4180702107586600231030380f069412503086075406c072110a03240c0601c61130700400728814042c12100b0344810600104c80f0907200004240c0c4c081c0074100300c8120b90075413000021540c04400c541c038034804a9002e102c20000b900d42d960141044c0314042182509946560305d070081e04483d08020040400f00700b000344e82c0c0011000120176070340c29090030000040e00904014550368040015600304000d000520303202201e110714012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 484090305 1250 484089055 484089101
    0xe06011e0915081303030506060c06090a06060501020d080a050c0c01021909050603191e0f0b030106140a260f030a140328020d0f0510051203120c1b01 66
    0x11514620280e6100070300c9148130b041900041c1c0a0b4000035406003000d01428104040359012500d0408240c46840755a0888001a02400890b02480e809071000b800240110903400c00e005040c1c1200400c800411640c400c04a5100004d4008517017881007003d00a40d20764044000055001c0c88100040000c66591240054181082c1c130699100b0341214180041c22001c20001101070700012400302c801c440100c0c580f05500136184034100115040620015180a0410905085801a8204507800c03041c0702d002e030140fa0b984041c2001560074a81002c107070b644c0106200600700100b4940303d8064014403507003880400e4004080c0c0340d0300440d59070300900031410f00d64450316403005890511013042c44103401c0541c8000410f0b40c16050307606600051404401540e15821a80c40036440c04d00581c0350414088010b20344540c403c00342000300d45040801184c25041e594a00c0340a156000c203203640400200760303109550070748210307000781003801441805c0140c0685c028100717080328800c0c69003814031f2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 484091555 1250 484090305 484090307
    0x230d020c2b0602090a0b0304060e0706110d0c0c0b030f10121101050a2709050a1103011707150305090f0a0b01300b060312090a0e06011e0915 62
    0xd01d00c81401180040300c00181584565010b0341c45500e5075500103c0c507103000161912010011880b850190000107100824400b420b401c0c8600c0c0e038009410885010500b07080303100c0c0420030710203011890034521944600d525281c51810704590208a154102204100b403881030445510b2143e046000d588e4055620b030102d1a02915031540080d0084c0d5025000003400c0d40500d004000184c00c1d410000c68001d88100300340a424036950b40000860182c0c40b0400c440d14250284c250400045902400070039011f00c2e0707004a5000503c034901c0030b01003c0a00c6c0c00c011006203d150301420003d07409200a44c905e04015002d04003c0d1100d00301d40c8038113449803000c50404240c2420702a0f102c040214241d181c900c2c0740d9401205c1c80703032501c0a11001146510913042c1c08001d02921031003000040364034949007081600709a244e2034040a13043c0104021a8150341e5055400140c44221001c0c88480e200c1c480103c40c405007503028542c500e1541e8a07101d07401c0fa08981c03814111a8405040540b1541000c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 484092805 1250 484091555 484091599
    0xa03141e010c1b1a07030b040e0604021804020a091a15090a090b06040902040305011a010903050703030f03020d05150f0a0e06060a0311030106050301230d230d020c 72
    0x3501d9000107416440b22103a003000302680c0d204240c0141150041c5421354580705041c1a41a0f4442c00441e030340344e03440107890620340a02911144130701e01502d22840d0940100364a038100207041180210742d070000030115038035007102c1ca0107004d070706004004c90405e031400f2040c1c00000c1000f0354807420301c160711500c200602c402110000303200500341c5442c15142a0241028048101c0c1d22544030f00c1c10301c4003051519242c0701400040d40940004105105024a01c46404842c0c1880c01d04100e1401d6062001c42c0c0c0024200040741e505203018919008a828214028000c44405c1c518441c100018002210700202c030032221194101c80e906d8010454100b040414112840703030103090244000042c1c90b51030300d000a049070b19114140403400e00325401042c8951f0703100360841b03c0031510110040c4806501403030554007405410607400d10607220440011130b0741a002ca8000c0400c0403100009080000556050344207440c000d048a040c64034901c0080d4035012001e171014011046d91066443d00c5e280c0d28 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 484094055 1250 484092805 484092821
    0x903020d1403030c03221e0507050d05160b04120f0807020913110301020a021504021c12021002040b09061b0303010b12060d02010e011214100501110703021302090a03141e01 76
    0x1421040c0600a43c00112020801f20401560180108d10002403191119180140154031540c060500100a04d40c03980c0304080c1900811001e1100784000e00000200c1003a40361455006a401d282990146c03905251621901c0c030b000350020307901d82c180001d005106004040c89445210909802142e11060500b00d02071000103400681c000001c00842c6c1900c545070a400c41c1c0090130250a081101c48621142d01d4031150445042041c0b6080800361030f41448004940c041d4a1001d5103000d10788200c1c2d160900901c00c98034450040000c1e0004860700c0107d546041c0e8400c0350a6030780301d40c1d4403000c900c420b4110300189032011881200203445450002c1409200b164140c45070102c405c124001100c40c804081c4d801001140e0710035034444004900345526114816225401040b60700744000144604801811003100d40c3c45035a00740b005030742e03090960a01081ea0400103032a804040b0024680124643c400340c542542c800c2c54002c00c4401241c409100201da080086007885485180303800c80c2c143c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 484095305 1250 484094055 484094063
    0xa0f0201050a2a0306030204140f011401020714040902040e0c0f0415090c0c05010612140609060c090301090f050705010e0a0b030604020a0306031e050d030605010903020d1403030c0322 81
    0x61403081414941801c1034002600f07140b6002507100d440f540410200c44004120414070002c5c041040f041040c02561a8050052803031152400c0007400c0010b541d48005001d44d50301c150710244001020b0712581c0c403003002581c0090080c4110150791450741e40342ca0300c218260340107104460015106080501906901100a1400510707491504102c64001d14044e5012000c201c041058040440c2d0240a444060080174000d01d42d42200c51070403441b681d003006600c100070b4100d0b008009690501003403055200c40c4050300c4d60383c2c400c2c05000007401855060b0006140300300c2d000f080d01c1800000503140302900d4007030b21600fa12030452010455410480c0c800c82080c00010000070341c1c4e909050b00035041104440c1400308450361030340d4036090281d4116408030214080c40032000c080c00340802001d25210070340e0404102050901000a0105145e03003c040d006034035100010041007c0310b42d13a00d4806c4110015641c032070810030703945420741c3e005898180f100c10303111610b43c1e4508000e4130008422980 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 484096555 1250 484095305 484095341
    0x20319140307021c020103060b0c03131d0402010309021c060209190b04030f06021207121a240c030415021006140120010e0a02031603050619110a0f0201050a 69
    0x6800113550010103422810191980310009042503440e001d0400704004002850f110407850341c4682458220360300c9208201000411b4681040d41c6030740c0790350020740a280104d4200000c1c000300d8616802820820700c2000011425001e02013668080c01c0c00321000c50309400000001301c110b29000c000d82c0100e00202004120410020b4800b03a5001c1c6800d01c25030002d4103028041c076044c01c4015003110002d0110740420b607480d180d84002e100c0e1004d102c031402d0f0040440961400030a8dd0140722070300d0f00d00030310406094400300f0040441919000304100044071390b01d40c1c035200d04c4c140c140494a00b0780d001d0310440898980802075030080001b0380301207008460202c0f5800b401118000e0600416a0959000745562100321000b802031717600713565500e00200f180396801c2c13050500d0201504844080120706000500000e071002c6a0181c001d1401d1186108007500d070004040201841d0810654002c40000c022841c29004251081c850303100740c000300083e5481c0f8420105444a2150414010b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 484097805 1250 484096555 484096579
    0x204080f0705280803070c0503210a030c020309030a0309050102070902030c0a140c0a03020d23030105060306060c060411090a0218240301030b0603010b01021b04051302031914030702 80
    0x40b500503c842c041c43d403d18261015a40d88401504560007400150380c481e4007048140503d003000c101c0340f2081011205401c80740e888544013a603c60142a8558041644030300516124510800607200900c41c000d0070348082021614000d0524611340c441e0700d015005031440003803208018820b49100d440d081041518107440c0d244222511035286001c100070a60030300400f00b0b503020403c0600c03c0c05100360024050b0340100e5801030141d010181d01d0300403607540c001e10784614101100649045407000c1d13442070f48903202e807000141603000700540002c50740303e00710400050008a044d826030310362301501c08048a4a5100300441648030350b5030802e4a1090201d0a50079a0600205100244041c2e000b03c03800840085480e19107540282d00903108069904103000c220f260030310134505105800d000a01416041c1340500400d508507209103445166201300180d0481c1408222a281a50041c2921300141040e0805421800300d01004c1c0c90001c810484281c440364008210b41c24142c004080a1401c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 484099055 1250 484097805 484097839
    0x1b020d08060111030703032016381f1d07050c120702030c03030903061801060902030c030f0601110c09041b03051b04060308091002070512010204080f0705 68
    0x40940300c54100071656402243c42c072024030181c01c5a620aa0b40812400049144150f503601d16480780312000304208041c006010b1035a40700d040c915070001d5120400c080795a02641060512000d80d49030006c80803100c0c40058100012512a02c03500c2c0003616214014404040101d1482c01619400b003151000001018400460564000c1c05850b21a107040c50354448142040c0083c6100441e909010030803804528091102000701c0f84150021420409100000703561440d000d0204d090400d144080c00314540400e400c11030183c0681c040035903980c10084484025544100ca0ba14656106d020118030b00b58842c40101c100c1e15880c8008001c0c480041c0c041044010020380704860002038017041c000e01a0f100c501c07040065005601a001040c0181c030100501a00318104901c01e0746400c90a000143d41c0c0070a4944614059822148010540310305a2070011160441030b484022041c0341451024150000c00558a0324401d4410007100d603041745590300780038052541d2200550410100d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 484100305 1250 484099055 484099067
    0x608011e03030809010b03010e0a0c050d030912081603091e030804051002030720190b0301031731210620121501020a05120f0714010902041b020d 64
    0xb0441300c0d8000074815824600017400c40d4108070400c03400381c102c0a40d6406000d8000e0750b01008102c1550203140b20142075074000e141e400c070f41c0230b2040b03000350200c0d9007030610004005407105401c601c40c07400c04c59500c0f410040d1040c0c00600c500c8401c2219003030b1721801125082c0c40e282c102d03540040c9140c241410b1104000803202040c0c0c0e02030440c40240822004140040e600c0c07107014601d0620107142004032014080302c040c0b2840d41c200c2c44040c20708100400c120316401c0b0790441c0e802084001094030140044001032180d0b081050300d40c0c800742c0c01c450764810160401c42512451906a00016984021345a2020b074020004030112410002038804030344150042c214681844040c20a40084000c00300d02c541c003c2080c1d085113400c440704002506c1c601800c14804a8002d00040c070000c40c0382d5403415a1110704c02413118481c44045502110b0300c8151080d40c2e426a48084a00121070070032100c41c0c0200b0009030244e1042d42403001007441c0c101c034821a61305c2c0100c164054614121815400d03a41d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 484101555 1250 484100305 484100311
    0xa0303020906130e0106110303101802041701050702010f0e0a020607080403020904110307091b03150f080c03010c030b06030f130209040305030402010201112109030903030a08010608011e030308 85
    0x4103104015010354155003103c0341014101c0c00800728219410408020035075a22150350217042c1d84100140110001c2c0784402008407182c0810002094248500000290060350300074890700600070381040340b0031019001948190015030080107000c12644a8401b07a507208007203880c03a45c02081c00c41001d410484000c1c000135002d0f2840320318041e40c9a000c991000801c4800f0b698074041c0341c04101903841d05115000060252100500a10f000030405041c6060001c00c50800c0c5507039030000260681c11064040000d002d0aa807441515640701102c0362500c04085920b88203510309680070340128024414882200e1018041c581585d4806520107407144007e41212a00c3c40015135040050b51600c800703a10841c480d80d680c5450b424030340b001a080d50b1580c2c0c005034404000f03002d8036507940019541c1c4808541d035241160b01d2a1900d0304081d0441c03013080d8943ea054080041d4040c00a50040c01c034504a03120b5959059450383e035510180c203801e40841c41c441e0708060041d810004a442440c0840d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 484102805 1250 484101555 484101559
    0x1205060303040f0806040605060d02060f0904060503010c0f02071a071b030602030403050d0507030911060702041103100312020609150702011515030c03020c0a02040c05040e1e07030902030a03030209 87
    0x454141c43d00112902e526160b4002c0e440caa210504000410025000e080c2c0c01c8001540c074100700c0807003680014081d0042050010140c030011400121660b29508207000400c0064002c0011601e54036000740920420014440903114030035000840303102280080c0100701203100e0641c01c146241d0313142041035800184c10403682842000101c0400c0062000b07600440c8070b91a005e5803005590500815508003c003c04203051808204502140030f0541103090483c0c1160040d544d00f245200250003400c0c84414110740a00120400c202c5009101620056a028401400c0c544d1032548049036100e400300c0780a60140c0180700c10701c0c8030407109a0007640162083c00007164200101c0d8a000e2448090b40c040e08034002000700040c7c0f400c0d0940f0031806206004e26040d03290085851030702d0760307504007005c00a024507034a00060b2000362042e401d41e805000c2c0544900c159040401e40300003052058101044120740e907401055400f4000d12800d840c40354064050400a81c082d06c0550007500600d100503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 484104055 1250 484102805 484102807
    0x120201020f15010306110a0206040209220503071b030807080f09040f06050103051e041e12020a030e0a060f0e03160306021c0b0a150314011211030d1205060303 70
    0x600007242449038807920006041c4810840d8510f0038180190355412000c840100d600300002071140c0c1c0d003c0741c03040c0d01c41c1e0151031a2105803103803107503441b2030f01c00d85480e86050410810b24804111700840200f43c0c03503010b809000d02184c440c050400a12020380f2004000300020810500020900d20190010300b07414240e45007009070359400719081c1c840824411500c10396a41c070500148da058030680d43c110210f801000c4020304100900521440042c0002d45100004449400b54004040e94510615441528840410302d9400040d50301c03a200082100492545803005080c0d003083c0e40d00404560140e40d40b10b0200d03548020030350300740d100828076907003502072030301442d0001d40060881e40003075209444c0182d40f11f803402e81e200707414405500f0381140351341000c013980095560b1060a0058071490100880d0700301030581c0503001405880701903150410140c00004142241c110303900d041d113001d824440b5400c0708400030561680702d40710b038810100f9480880001181d00550015900c40740c00307400c407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 484105305 1250 484104055 484104073
    0x11090c0a032316031b020c060f1e04180920030f120406180807063b12010c080106030e0a020613060f0509011b11040c09080c0603060a12020102 63
    0xa2812082c0840b8144041c8422514020020b0340c540310f031010f1400e4451080415a10414009465058100442d441043d001c40c940d403001600c1c81c11103034031031302c1007401400c200d50302c51034180c03030703801a11407201410a00700d0025101003150254070000c9501c010b004c0350b010000304498840300f00c03d040c1c480e01072058440b4803e900c3c80810081842c2101e8102040c3c407240b902c200108181c0b0382c03100c00041360b0144c4000700b25160b8009640c1c0f003611001c0c1840303520404500c1000080c2c226010500a640380c801191460708440c1c0d02650b804020241c908886075010280700d68260381d044056035001810980c010001248a90300210546004d0001c0c2d94039100076400250581c1c110440c601703441d590f009010013200341c002106990b028003509000c0c0c10180301100203415500042c900c0580c2d80650808074007004440d80450417003050003001000105100040104864102c0c02051600c1c443c1c40b5a100c2c245ca840420f99108a6004002d001260f0800074910411024110100c1c190700c5a41c103c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 484106555 1250 484105305 484105361
    0x30a0e01090b040308090c0a0506040b1b1015060e0109030605060406120809010f17010b1c1b080106030204030b04151506081501050c06180f010905060411090c0a03 72
    0x94030f00903800307aa140e079240d0900c0b40390b031400d14451103a01403250441240420890712070800740e404490720002c1d000e841d202c84e1102c065910b41076000013078482c0114914005180ea50794401c400c1d0703032002e0100029080d103584c0251421a4401002400303d89d050074100002451908640d40c410f102910102d0841c1d0b0300c0c5e00350444904003000451f8800004030b1001c0003540d000d00c001500f032000d80342850a02c0203004100c1105c0d80180a4160181400507211380e10196482c2a00110724000c1c10030860340c4012a50142003035080e862000000d0720806c00011803500c01d0017034900340e0703400091000a42c0c0340c543d1241c0c4160f42c1141e41280c5180c841840050347c1444240702e03c010406611182001d142c907041c000c0e4108480c401031814020140510b2009410014000b03034040100b031003030a50441c1140c4018503000b10145241401d44c203211007441080000f0524034040c900c12a003071804442030b1010010b04d034030101c8031540341c20380034084c0741d4001d44240c120030042001003000500394541205 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 484107805 1250 484106555 484106573
    0x91303020705130b090a020403120c0201031b021e0715030e012c070b07080a0c0f05031b0f070614030c090301050709170f0c13110a08040c1406030a0e0109 68
    0x440840d5040d42c860304d2840328180079040641c041c4440a0461805040d56a0408205a010012000c1080c2c2038184401c41e4041d512041182d08404800d692a4400c1c02000b99100480d540b000c0c00702d00d290240d14a4501c00007900420746400002d802042d140740d1004600074034003140c080701036640f41c08081d598003055410700302000707024000c0c12600714061210a0300d00022a8440f11400c01c0c00c2200c0c41c0800d03c01820703103901099902c0c0000da0445241841ca518a420403c05844d0b4080028022a1009043d0035050301e810450140d0708001c8013035804a8464803d0b12030b00b03020070711058040e5210840d003801503511002c401d041e6400c000701c80c0042403c40d04221856004200b6094040c0300984850081c0c00c40d00880000500c01e6009803a140741d01c81c0806270740c1070701400c00001d14865540c41c135080341117800d8001020f59140c4010302c2c401402d80005a400740d503400d0000b00e01141030094400d0005085101800d071a2454452401c140000d06803010a2625035585610403800a22991 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 484109055 1250 484107805 484107829
    0x708011206020d0c09030b0112030e040b031e0606040c0e0a0b1606141005270c071505062409062a0c1f090311010c0c12030801090209091303020705 65
    0x17503100c210050031850911089881a001044030707a074001c8400f40000c0d80f00200300c0c48420180c1e000b2039602d0103140864684500201e242d2101c260240c0c001e0f03e02a00081d41c544103200884080c40f01440b6850b0a1310075901c110032050b04940044000d1000c291008020300010008080d05007600c5500e8a0ba24201d03040c01100b0002d40070b00e0000c0c0b0041241820352200985021a6154014000350800041c14100742481100100101001a45013079044058074040c03600400c4404082c0050f00e81d40d0010402101c11a1042116004680004581080c0c3e03107140c1d003c80d844203103080c40000802c541c03a041301c1c0800c0c071903140182403c21405010406906844442380080014840c0742c410002d42500740c0c680000c850700071180341c88500790b0101c422000c803508009818012020500120340000f9011409840346251280c0050105d0710b0140d103000b05406981c0300c030150390701c505410b0182e120722074480b0b6014040c0030100d0303403640200c100c0000360781c4680104c40010365510080b50322980b00d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 484110305 1250 484109055 484109057
    0x180420090a0e0c1f0207170307060b15040305030c06011403070317070204140a0501051c02010813020a0314010c0305071d1206070302130801020406230d0203010b07060f050708011206020d0c 83
    0x131459400d41e01000417802600c010310004158640510740a5580e01491401801e5103880c0e0f10788881c3c50725003c2d000c0c01c01030610314030540e07100d89905100c1d41d260701c00d03040210148220b00c0001095600301e4040c144040005000c1d103000381c1340d034442444d80300c600340c041c003816041004200c0044c0e5952256440003511075101444d07914080541e003003200c90580c403040c0202c000c2005d6a810708441e4402d030030442d0b130900340600580c0b03944240300c1c11000340120094000b006c035030b800300c18003e041040103821416080240558142d840c000c806640080e98008089208002e0020140f031803505444441e980c09801c40841140452800c1d181c004251449030200e0350010300b11802001001c41340d000f030000d410095140c6031526400524682e0300303487c3c0404000781c03049a50f1900c83c0c140125911443c5204040d51656120540f42a00303503c0814101d6840d481c1285d03840c44505d460186510034040c80c1c4681d080340e0310b401682c000c80e02d014001100c4140c0c0c20000d0030340c00e40441c07040108401031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 484111555 1250 484110305 484110349
    0x617012106020f190e01020c130e12071103061f05060c15150f1e01051e04030507171605060a02011508060103050d020316031b02180420090a0e0c 64
    0x11320b00e806000300131040384003411500010a0792026032240660740d00c100c42c2c032a10002d42c5000484d0100e040040c02020034204160010385d03a0140025402c500c292000c0c210b0603155031780c07111300c82042d0001d4843e02110360400304000030080741c0b910710058611900260309407107000007002411107845504481c910048011140c040300c04e81030251184100307003010740380848040781d00c154400c0c0348007809585c0f42c100036001072540c20110340d004014218240c04801d03183c445440746070480d00c0d10017074040d034000000e0030304d9405a55400043c501701c0075044148410511424a024000700354000c0c20494250b43d01c5a046058540036083c00f00300522036403001d09800c5d4103600d0160b00b05017a01c002441198000d21844034042400034a10031059407508095440314814078410b840854119806076100218584c9401c0306a01c580782c1d1445980b28402d01c81c2060082d0411b00200c1c0c100540c42d54002280074009180e070b10307040e40002c2201e8658030841c0c100700c40040004051000503d98025143c0e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 484112805 1250 484111555 484111597
    0x20f0d0803040b04030311070c1203051603050c01050c120601030b210102090906060c072c0109020a030c0f0903140f0d0c03090f03110405100b030703060617012106020f 74
    0x98103214440403204503a501f030b850301d02191a500c01d42500390044aa08983c1c01c001001018043e0081b00d4204001e1500d900319951203080191040d0807110101c0b103654241400220050710181c101e0f4030704081d82e01012201d803180c00c011002459008002a00003103940380ca181e45d031380c02259032600d2600800c00541e80d0f0a008040c000d000c500030304824014001846410030001000c1400700584400780c060500100c41042c6240c000f62070713a24104100c805080003c0786035201c540081600c1080340d2001e00943c0c556070812a20382141001d0f03000021071100050002684544943c01078842480c02c481c00100f0031819941044664102d0303d000c602c505042030100341c1c020001100405c0d1144540d0000745c41d64450f5000c8210750300029201d10340c2c41c0001031480b000f0203440009410503c007210340700c6c6800e0741c0113001840d150260b800840e40051000c10b0003401c00410b14103031100e444101c09141e03460b1001d05010030070b000c1d086a80c03d4081c050903802d803000d2030292102a55034a524a03a0744 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 484114055 1250 484112805 484112807
    0x6020306030f1b0f09060a17010b04090b090c010c1101301d0105130b19090b091204051003021308030f03061305040203151003050a0501090302061f03020f0d0803040b0403 75
    0x70302055658000c1c03100c2d4080128591f1011140c01c100e8542e21441400b510071481101e004000c544a151350091500c14500700780300003600854490030406089413a150001c1005460b00e40180c0b200402d1006401e0060b81c03194421504040300c00c61004c040d4140e0981e80d2610001c401d01c000076200596602c1e503c0c20189403080e0780e07544440003084002c0281d42800c0341c0720001100c0c0f00034003508400203100498080014100d080311441d00c0040100050845481d003c0410324058404000070b00c540c03002603803000100c0f0101c0b01120801081800b001e9000b000a5001c0d420001000100c0e04848400140d6001e042c4014102400e840030000e659280410070004001c000030b1071000c600d0725010030400103803170010b850603c0c0c410b0800440764035514901041c55001c140d42006200d4003900340f954042110540224901a2280c1c00391780c07072592071800d2900300c140c0701d0201512080484800708054140558038000d01d2402038540d01102c0c445840700040b40d40241d5088a80ea000002004245 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 484115305 1250 484114055 484114069
    0xb091b040902210709121118040f0611090a030209070908190312020708120405010e010908070c0512070306090302030d0c18050a0f0e180d11120403030503010306020306030f1b 77
    0x104909040011710a400e14031440030284200c100240301d03e0103140a24000c1da100c0c40740d480340381d040d40741d85509440c02d07141c02d070f1200058410881d00c45090401401c901030a40c0241c1d007031010041e001034180c9146400700070450002602e02010300040071004140c20f4014803042e4040ca0103420390030004400d070720f4004c2001010500c3e540415106010010000c0c0d404022100880c040702207101301503c0340c2c14901d005240030741c15040d03a036103044542000c000c3c840303015140720b074082e01c0407010141e0350700e0034400d0b04541c150148440d82c218410a0001444a40c4880600c46c00b900c1140e0038034203030050110403242d0300d181440119408a628862400c620400702c009004142e0780704450500e840c2d805c03504100d036402070400d54920000040c61a80c9082a00000d41000720304a0306111400c0c00c02038020210031902030070320701030304509207042400082242c040740d90560310030345540e195444072030080d04042c00c45589801030420300c0b003055008000b1005052801c0301401c0344141d80104004403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 484116555 1250 484115305 484115311
    0x504050d0e04060e06060315090709140d080f1b06010f2c070f050903060c03011d0103050c28061d040e0a12140c061503010b091b04090221 61
    0x80780c0d05010003888411a50072032960003000c20758401e031f1a41c81c1c120615089034440b015064001402c082044441507000e0361510490303141c000080c0420f400c0b8414040303074004042d40640500420004403400006800040c500c081850341c001154017100c400c401d0500c5400e078440b15400038440030511030060b132160028040c902da401480809080250503914802009082e078040c09840300903001d12501807000c41e6400500201980c59500e08402c0440e42904280140383c0c000108200c4035928851004503181a207821000038889059048200b0011202e83c40c11190200c030200803a41b030201084d10310740d001d84403d44440080000190348801d2451140c11540c0c4594107100327000030b84c2e00c40420480c4a15800c502c0410a6a000318029128901a101c50b0300f0380c00d400103084d1200a20102d00e05000d00c00144082520705410301c10036084e50003094049a04c15180800b0424144503810762011000c0784a54003805e2a598035010360490300070381c05140e04015403604114002c541002030711740c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 484117805 1250 484116555 484116559
    0x50f0d020d0f0203131217100306150803040308090a05040203071d0307030305091002010e070b04050f0d0b06190b0c03030a061e090c0201060512010c020607111218040504050d0e 78
    0x1007036151485400c049030540301030280005141c1d1841c11010380c81204104450b2050a20002e510b0802c940c8d6a520440c00c0e20060719030615054580358031025401444084410810040d03003000d065803215242035000390883c603844046071710700140c80d4489001451052010b901c070302c02070074203400809071001043d0076803034440e410096083c80001c1d00503003510095001601c400b01c450844050076030042032001d141c1c0600d0b2146403800580c06a0f228010710664606035450758031843c441007808843c44a404000340f25100180025105047c40d4001440340d40040060040c1c00b60366242c140215070003410015000c0c1c0001003000103201356805444010100001c0610078003910000c0d000081e0741c1801180074145e10340d044101041c1c03003500b00001821000701903d03420342c45100b4660080488142500c098002d00780080c4110b406001c004c121041203601400440084814a45c00341e8010004c0000c3c16059645000701900c2e00e2260310300c1a0310420007000d070b144071094060312141c0b408031018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 484119055 1250 484117805 484117807
    0x60a060b090303071509021c05010e0c06160512042909010c0308040f150e100b1c020a0b0c060402032a01030c11010c0807030b0a030b1303050f0d020d0f02 68
    0x200c1c64600204030b691140d0044121403400c0000003011000d050104006540005943e042e514001d0804910100b010301c21802004010940d201580d1210801401194007201c1031160a0107004c0c10410f10103020310500a964682640c080c0b00302ca2600700e40c11940c0c050905000402102d84500560100032803402ca0b0b85003003140701c40c0003c0030b080c0010030040070800010003103010820000d43c9a061568880d2021142e4104500c1c0400184140b1940709400c2c85010202070640b1041c0c4520321440318081c150082d18201181d40030800080e04408076001201014002501707103401c0c1c0504004441a405840c0c075061034010185804c0360310b144101628008048000900c1000c0400d8143c21070a007004188030107940029564100300f01d0240d9455400c020001254951141c0b1191180040e0745040255072118024000c02d50014040200401e110303c001c6004ac000303404050020f07511902d0700d103140c00c000d5907440c46e241d00203070081c00406402050500da400e0b101d029126851100078021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 484120305 1250 484119055 484119067
    0x9060c0203030f1b03030108100605010f0801090c050d050109060303180e060d1e0c0320060f0306030f030c06100905060d11010333050d080a0e0a0302040e060a060b 72
    0x29101d12451200002440707001074a2444c10035080080c2c000c182803031054944a40e07480360807a440d41d55525100948520302800420395600900b894103400c0d407942d580083d183c1c04c1c1a600c0b001401b41d00c20290600100f40115035200f41c29014050180810a6000c1401ea14515024104403100c10341891540480c0009000047c00c0801c060742c002011206017a03d000c05003000c0030f0206800041d1240a81c004905600b8800c2d5850f4190440e48620b821040185940c03074001400040256540d620040070091788803c910100083c5810100040598111040500c0b950346198415421440244c211a04002210704000c016000402c0c0070350007442146810300001d0700984040314002c0c824814409421140d91095000c4c40440160040404082c2414030a800d05010304613036202046070040d41c04191800c0c040706074480194848092420f00701d200f1002d0300c406990321031958001c0c540000010160395a03010300c850255010000c1c1c4045c2c10840340840c180d0301700750010800766004102d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 484121555 1250 484120305 484120309
    0x100c021e09150a0308040306090215040803090f0f0a0e07030c0302090a0302090406060302040f2702181f09020a08060102070308090d0312090b19090c050603040305070b0f0709060c02 80
    0x5480e8440300030342103240d40020b1140020703114525500040c08441010401008014080d40800040e07402210000000c07900f01e01501250f204034002d50b00300d078005110301103007400c00c18007088184100400582d00315440c1c10109000826035806074504000000511000a070103114a03034282405103429440c0080402c08155507800922000f8010064603000070b05002c010f5100202466008209200a18a08a030100600881c9450b2802807120565020740f03030300614085e0407081e60182caa40d003d18116417034100c0c0280020050710480c0c01a0802c211218001c01e608000340503040c800603101c03000080d000b4800c1000070078041c1513600550b01400420680001d4944400044802100d000590315044540c841c50380368000c0e0b91410104004101310700116158451382d580c001d00c8041c40c2c01c4d818210180d0b1512600540003001e80307403090103181010001103a003e406400c09a1510049540d00c0d10405001c0320804460307403810b014005150392040c0513000425081c54244200000c41e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 484122805 1250 484121555 484121569
    0x112091e1e0308040221060903190206061302031003060c1805060a02070b1b0f060108060f100303121b08010e0106020304140f030111040603050601031b0f0309050309100c021e 77
    0x100203441249080100e040c40d080c1703031001d1010400284181c0f025410800d4049550b60454850f045401d1072b005145e00030f45d44001003082c400d900040410008804564103400290f002508001001a26000110204240d4015504c010001d9038510640f03a0062103065031140c45a0841032040303508000c040c0f11313a07a0000e80c0f00e042e03c03807109141d5611440010700c4004011400030085880c0102041041c07981404180c060480c0c201ca000d407051640e4a80c451440d01d00100c445500c8102484001e2020a22860346582c50041109000410340d228508000ca0351140114100002d00507000506c01c11002c46d440500406250000b581450708010031a140d00c4080c10902c1c0c01180c40040040055500350001603241e012240c445503203d440d000000d0203041d003207c6e000d020a0408007180c01c104040740b4840c0c1120004c1d80c0d184d510618051044010700000320301a2407500c4240404c099682d503040c1e12560101d110303210030100e654140706009880a110074131b9501002c03110003142250b15820 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 484124055 1250 484122805 484122811
    0xb0420121b011b03080115020105060d03080405160306050702010b0108060f04150b0309030c0d020a02100c031404081e0106210503120c04140d0507050112091e1e0308 73
    0x504003203070380380d000e2004031110a05144040203256402d020f41c000c0c19003010200f8140ca07000c00507042c90030000c05060b4260750040c1c1d092504840b03110b1006020074840c40206070014400d5042d44c0101412210950307000340203400a440260740c883c18080d440707030244280942c4e550b081c20300300c403985403c1c0700184202d41c214407e01d0240c0e48a84c00051607103203500400000c1c042c00c44019481c0c0c249001c01c40d0307881c0c2001305141400d00c1010141c0c240c207400041c0008450380c0c01082800d1484601c0000c4620341402d205c12000d01034180080113450f0303900f101400140c000700008014807541c1d841442d0190180d8091940d0f00d034503010045c0145019000c2081c124203050342ca000b00c4100914000740343d0b100e100e5828008a502c6814860285d000a009000300d46111000900c0303800e04a0401100d89142c181c0248250301c020003c004650103000c5000d52007017020f1001400645d15202c85d007007550040040d0300400721034011201008000d00040190500c0e84030103100489041d034010701102406 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 484125305 1250 484124055 484124083
    0x240504020702041103070306030201080108120301060e040924110711040504081303121e2a1401022d030a0b062701020d0f0504090b06070b042012 64
    0x1100d2082d920703950010f1030980d00c454807450b900c1c681510001c00070301d024002207000400700c4c0000605481e0018038a050911641d04440c9140d18008041d0b580d50a003015480e002900e9814440c0800c0f0200c0c001139400b034444402281420351000038000700c070039810548540c0340081c080074002ca00c8a126203484010185c0e00083c11f503c581c244021035000300c0c1c10b07a4600305002030010040160200410200084580301d8404880840400c6100a0300e090f11380c0c8002a50031072613500c0324071100c40da01641b4401c2e03295640541425120740b0f0000070700d08800017843c0c0d000600349500c1c1d09010780310f0401c00100c009034100b50548800b080d16510019042c0d90303507561604003094842c2e880c041102e04185200e4541d000f038401c0680c100307182d11505450340380940214090741644500840d45500c0b1028290b4503280307000d0402c0d04400c010204000710581040302440400002034260100701c2c000e50060b801c0c41c41e145640d5484004910003148814040c003c00300404079032010005840c410200b070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 484126555 1250 484125305 484125307
    0x60e0409050c09010b1c020a0c120e03100e16031214250510020c07031b031a01091b0c030c06090c14030f07050d03050a0e060d0c0324050402 62
    0x401d0400e2840d0025810490707620141060000624100c01c82c0106402e07210201c868542820b807244100172400ba0200072000301c0c0c03509110f1000030380002e640f658507400c0c2c0d00b0b0074000d0329900d9001c04c2c47c00400f607a10305400743d5507100e09690900104403c0514084141001c22100e085694088021000b074241e0000d210151611600000c1c140c0c0c00d40e0b9000306c14246c10303110b00300880b0b0481840e10704000103880ca40141c010704449a001402210300034031241d8000c0c00e015165640312800d42106640685403403032043e03408000110081811042c0982d05864408154180300c01c05080303030000121540da0b02040504902200e812141642e01e254150070000c0069480e406c0075030182072001c00003003548118801c04a0241104501184480820380440741e120720752140d90f80d0340f41102c2c098558840c8100700c2c0440081c1c8180d00914100c0100d103031003cdc891100700d021038055000300050300c1447d51500c8150140c01e51600c88d0380b6007980014480594081240380b2009119a1401014051a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 484127805 1250 484126555 484126571
    0xe0906070504170a02030a0b060f04200a030221010e070c03080c0705010b0d080315030304080705062805041d100501030c030b030a0b0a05060102070b0a180b0c070e10060e04 76
    0x4090000e2004d0130380103000e44008600a01d4041000707103003115041d101304e120003600707200f41c00d051117110030f845c4410700c140041d80848910100389800c46446c44040507000c00c104000880740d00c5c1d040800d00e04901040e0720550410303501c40244140281610304010000960b4030200e40d002d542243c109903c44041d0341d640c0141d0505501400e000c903486a08242001100070400680d880254482c1e450b410720000d000c450300c020162a4401ca21441a8540c08480244054a404402030802d007980003810050b669100503190a4014400d0140300891030108040103000f1034482c00200ea01140c1d04059950302e005000314a03075140074000c031030402daa87d9204194440c0643c0c0460352884004044901d60392461410b0800d5403001c071032040c003c038102004903440c0e500000c4e110080d1221031030190b040220415080b90603001c042030140c06102c3c501710000301500700c00001c054280720500544102420101000746502d00500460b40740d41590008001450b8801d04000c0340502c01c0340c000c00d100c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 484129055 1250 484127805 484127849
    0x120c05090714070c08120a020601030206090402070507030b06091024090f0b0d0c141e1c05090c0a0b09012706020a03020d05210a091202070e0906070504 67
    0x814000540981e6600c0051000213115010800408603000f44080315a0f500e6131403104001e42c0501d6000340c02517480b090040c001482d000b009000c20300c2c009480103041c42c1950b11090f00e010000d0384240c0780c1002c3c6005020550900d2a203080d1300003d1040b076131010a00c0c001005007000103914074103841146010243e04d040e4843c0300603200900da0440902c600741d44480d01c0d000198462035091361203628148404005038042c13040015180743d8040c80310b040c40d50034400001e03142800c440b00108660100702202c100a95500f0b8038213460011040003c480c5400100d484c60180780d1171000d803007850404c00030004070041c00d08440301d4070b6084c0b801111480d000f00e42607000d40518a0071100c010070b40c4202240907640003035994060360082d4229141440c0c44002983c02d4401c0b1400d0180054400c1513504101c2c04881e1314a401402c00c5d180048d03130001036200d81c00c40100704000e42c001a040000e080140072007865400340c00c403171040044c0042c0d0504074405440c0c0d00c954402c0c030b10070748100c0400d40001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 484130305 1250 484129055 484129067
    0x20d140d031a06160602220e07200a0b0705030a0b090121031b0b0712020414040b03190303020c0705010905030a0b1b03100905150a05061804020403140106120c050907 73
    0x44c541c8020150740b240a0303103015400091319507440d014180b40c400030006e400004c401c0914001d4680752260040d1140705501e50308045580300c1e805481d0310608444800203030b002e107900c40c0b0804c22951150703181d04014040d01d05851800039010700c00c4000340d0041c0003050310b8034405204040315062810600000389019a01015080c5144042400303042242c400d20017110480e40c4500c1c229501c8407100012440c5020890289004581e24400040c00305101c1d0b041a610160041000071304452141010364050314426030b000d142200001c2d0040742e44201c582d41040408050402400c0480c4920704000200386d5030a140600900307541401804125064012411525544c0c80001060350741c1c6004002e04158030060b208004806141c400003078407120019052840e1507074010a021419071402c820070a55412649070504080c0d04503c6113100b13581c4610040000f188101018065000720014041c2101d082e948081c0310300001450710400204048580740030303580d003101c21001d10303101e183d021250 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 484131555 1250 484130305 484130347
    0x20307030e160312091202010804150e010e1903021504020a030206030405010516030501080c01080a0e010e0c0f03030a08010927140c0a050a0e13020d140d031a06 71
    0x5004845044030700c110009085420f9070300a900c0740c40e140200c1070301251042d03200d100d909840080203901d40c00543c0b10308500781e00180a00034481000c1c3e1450141300c110b6004440800c91a995204840760049083c020410110320f55040f0701020411034501a458403c450030740041c50b101240010215543d03132103007902458015141544a1402d8070300140241f01c00d860302902c80c6488883c11010310710034003669050717504400c040e000381c2e5104001901e402c9000352170319503c01d4407020900c811000900c5241d072441101401440d0b0a4810801d1000d01121318000900a402c02c0100c14207131500002800c1c1150000040000c000d65003010688020100b03010350030418829440b20001d02c0700e003110381302c202104442610100c1d220001001460720b070034484d254004402a400300f200c1009190b080c6d0b40034031903000c80c05410b40d050740015031082030084c0896110418941c1c03003100a9040044428140da581820004680e02603440c4540501c5003494503c17640001907101040301207503080680f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 484132805 1250 484131555 484131581
    0xc010203010e0a0b040218010c152f090d08070f05010c05041d040210051605070807030c0906060c0b150d080901031404020616050a0b0705040f080a0c060302030703 72
    0x344a503128407004910780400d883d2007101505043c00c64010340b8152007154a0840045c088805620b0442c00640c4c0302e421480e0155184e044c050645103002e001e17805149c25501858000c845c4034200305100304041119403480c030481c0380c000c0c00280c003da103600c2d203800c00305900070600d15111030305460b0126644012500042c101e5081c42120707000243c0110141c0191989002554911034046140458024080701c000e0750061343c2018200016009200802e510011040c0b01102c00034907844035845d20302035a001e9100c3d90b200e82010400d010684101034007412241c5802d00541d0302d40741c0000c0070244081c60151a40201c80086414000085c500c0c0b5190074029058040d03d51142c14090415080480c1d2140801d081003103040e42030000702989882194014296803c041100c40302c4078110310f03c02801c80d403910440610307001181c120a48184a400d699450039525820910000d034115419030120095520445803000007034100700229080d580b003441d005850380d4500074100c00ad41200711000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 484134055 1250 484132805 484132807
    0x40804031a070f050309060a050604090807050607080f0f0406110904150609080a0201230906070501050702160e071101110412020a060509090c030601031b03050f0c0f0406030b060c0102 81
    0x480c0d010300420518840c2c1d040b40c44640785410840b03001d03a298401210412110340200c000543d42c482d42d40e0086400403000f91000900c00b0540c2d445500c0c0b40c2c0040820b5440d94080c8c42000301035a070010800d5030110f02d003c009032075814a00042c2a85000142c40100107c0c0c42c0e44001d0070040d0700e10103031034103c0c100800c248071001418040c07080d0102d15000b43e0740080c22481c00400e0174207000a078003000d25410ba40e5132440000c09800340b0340c0b50341c41441c200509201001070104c070b81d031214058a0102c0c0034200029103801c004002a241800f0381030f1500510345240000c025071385e090500140e020034181070911a801e4851055401070010803102414002c01080c041215422002ea020865100313031030454030247c031101c0582c3c0b24040c034130091f41d100b183c050002c1d00607004d010140d904003406050100d80080719105020301d008003518907000117a03448007007107482001000c0c0c10343c20a040b80c81107450300303400543c0103180d845180104028075031a9103800003261101d45c202e4501c281d00b08021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 484135305 1250 484134055 484134083
    0xe0a080715180605070906090506090a030b0408041401020105131e0b07020a060f0203010503070302060703230c010c11030301051e03030301090e0d0e0303031909050d021c05030114060304080403 85
    0x561114100036003d845962814002402884c055803c0d10140d58540e111035842c6440c0908002007603011146880d001180440000002442c4100141c003c41c860b0468940352402c00c445400c4280903600000d04681c107101c1881030b440d42907510182030315001061000059a09000c2c4640740c00f810400a081701c4030740c020811103070707400b240f881074580c8164018010420b0703810300481640000c1c040d00c0e40c5030700a1542000140390210007032040c5842810040c0c0000c1e141c041103408004084040544080c0025881c01e8241c400e100d0700d05100e41c5402c100000350b550300003299803400140180e90103820b54410000c2198100c4406026488000302103940c0e940e141e042e1030016000e400071445491181c0810342011500901c141c9039032480244c0214207559802e4100e0801c90600c803000516aaa81d03031649010900612655026501c1500148401a005000090001803407080002000400e000500808076583c0641c0b03031411f400c40b0743c01c0d00c030385807410a007201e48119840204aa01c20340300d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 484136555 1250 484135305 484135331
    0x12060209130b0310150e10080102030133090506090a0e1801050105010f1e0e032a0409111509100e0102060a091101031d1603060b040e0a080715 63
    0x1803114203400e9094400c4e4501d0300d884c000c1030303402c5400113014100505a0601125180c492200e600c146458001c00d00c09980300f0006003240c1c0b0a80052131102c10700012040c0224210000445a50001000d03807854090f45400070a50105c1d8001c00d8800c42c00060f86000ea9176620b80300c2409400c0c21000000f450800b8001440903181d0052034903019400c0c0000000e0306d40c021568004040034984801e012070128220320500401040400c0c0c0520000324107003441d45d28100b0401080d2540e1000c006031031160705040c60103480050710514416804d28528400143e00b1f01d400c6002c950040d22072000b0440d0000061540340186500181c10000307400100e1b00507035120107400440c9a080e02a0360842e128101110151111214068040140c18203c00402e52096101c4240080c4500c0146001c2c0056480f141c14184c183c511040301c0c1040503400d0003403218900c154104203404680c208a000c0285214644602c19040098a004004a0048244805509000754130004103c041003940240c0ca0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 484137805 1250 484136555 484136561
    0xb0a030501080f06010513020a02210c100b010f030b0a211a061e0a0b03010603020a02100e0706120b04020a090e0f150d0219080307051014011206020913 67
    0x1c140c1c1d0b0548103a1220048011000c105503041e1031029004030485c9030103840403000380d4422420b41007148241c0f40360404240342090b121542140ca04072446d034541900c190180340180403111100c1307d52405c49420b40e2a80c20040d8800f00421500340030980d13041c0386001507041100c9a0081c041c4a05224290130111100354000d129a8401c1158951004411a014421500890740c0b980c00021804158a1110311111f1400040310300a141107103180e100d8141d1307051600281e0042c1e0210b81c000c107811a0040c0c060110070445401c00404100400d07aa4403c80d035592841d124000a122101030496441c00c41c507080007001c00400381082d5660f04c0420030041a0750044e01c10098081c42e10f10201d035405500b40c0d0b41300e00030415241d1804040501008004910030000c030101e07407048030841d040101c141c00d605084d005001c088051925800d41c7e04009060090f40c1d8511540c4610741205030001859144440c1c0c1034400706495050b4007919890900c000b0f01c00c0310421a4803000b07482e1003986a9400d90 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 484139055 1250 484137805 484137809
    0x2060c2212140615130e1c03050a0b030a081b0703060612030e0f0a09110904050103110315010602030a03050a1409010b1906090e0406090c0303020a0204110f071205040b0a030501 78
    0x4031005035580203c161941029007111300d612421a90789050510302d2a040b9216085c6180e0a4802441040b407041d400280512039040100f510349041004210b0144911000302c10180c020700b60922040c2d5440c103551241031846e42030200c40c1a9014068602000308038069035000108200103612002920324050161101300c0001d109034014404605144164403440c20307014150380886400d0034424406407404201c0c3c14440306091001c1001940c0d1402a40d0085004440c60b9030790940d14000d00d8102982d0381c58501a81e800c0d0001005081c0d40007003140c900d180c1c2c03860001115154980120301030700b03140403040781183c2e0f20402d001d0030440c1903101901140c1c08880358014020700140340742c904005031040c080400e01c1c090701004107204a0410a9000384120000107206e40580e540c80440143c6d41c1080d07006a110b0001a411801d19100d200c01040ea1845c030241071210150703070840f0b907104803c0010070181c1c5445055a5880c0640240da02410242040e140c490483d4040100240424 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 484140305 1250 484139055 484139093
    0xb13150f0c0b150d0c05041406060301120305070602040b0a0f02192315070f0207031101050901021c030213120f140a060207060209040b0102060c2212 66
    0x104000001500610030000a000c0580311691004195220340342d41440043c519050707420000c1c0c100c607030f95a4004412040314800e4035200840c90400091008640700702080140c002108d5040c0141a038821044d281120459805a110703400c01b0b00d01140c00780910b1000800c680e00201c1c0100c0c1030840607018103040c0d841996207121250305100c003280e03100c01007251526049000117640703000c1460101d403407019a501c00144d90300e001551082c146801103028041c01d000c410002480740099011129900801051005024990031900e1340081c01050303c01681c1072080005503000164001d0064466240c465070f4202201500100090041d5000320780e80c00141e2040e44004c10404042e00380700340e19a410040d0881d048001c1c0d0f0710341060144541a4040b1445000b540000248031800288002440303044050389554502040c04161482c100859041d500004100140b886402c0d0580310300d034019034040700d0000e0300616400b142c0324464004020620410102d1018020a000490000344c06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 484141555 1250 484140305 484140329
    0x5150909090a0233040801020703120203010f05040c2717030f0a0e0d050601090c200a020f12071e0605040b0306040902040e0a03080a0e01020715020a090b13 69
    0x1d0441403980310304030030100942c420310401483ca03001203000d220300324840c0780c1d150180c00382200550240e00c90300954003d0a040c2e4001546408043e481614040078424000d010343c1554102488095084440d0203640d004560b2014a2000c2c640704003c1409003c400603401907050140b6942048015130a002c1e00c3c42c050304484100801120000803112021001e18106091140252080764022003c94241c0c1d0701002e100f081c0c40c041441480f1150003031000ca4000506440301c10340c06400700703190045010500c002d024480c4100440070070311509907039040300d50b5151000b004000580c603406044540401d4031400b000441c4241084c200814046100607054150030394440d401c803414400c500600d14244001d002185e91418160021101944000c0000c50310591b043d5841d85098150300064001440c0001880503c40ca540703d0071100b005107400035440c0848a0302e500d2400c2e80310401d04842c49a00140aa00c110700c244150005000080301c050750b40d43c840d40c6800001d2440740030307859110f48 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 484142805 1250 484141555 484141561
    0x901050c0708042c07020303010e0601050a020303130213060f0503250b0a02011e0b011e09030b0405070902030103080c0115050a3516121110030605150909 68
    0x4540c0698480907070004982c3c1c42d050030aa10510008580060312100f000c20790000d491041c0810100c40c480d84c5664002c0d501c070b6142c00c002400d101406094907051000c01c00603d800c40341d010040702da00c401c02019800c942c00503403020a9943d42c0506030341e0001807406802040b0307103a407215043d007101c1c002c800711503070747e00e40351504814662141500120b42e80c0e680310030070206500360007401c41952103000010b42042e02c440c1c52038001516040000100d03a940000324080d6070495140349030020b0035246110307a0130b104070000e040544140000f41204400c100001d0800104001e00c41c06484071503415510380d6035910f090f040c03c2d0003125004286508200c0c0300001142c00e0841c0c0401c03240b0040581c600d0500e4242e56210300102c4200180b0411400c400d10740d02401500c1054415800000003170a4044151000407504c0d8205d4100088800340c00c036143c4045000000030001444040b40d4060066081c2a0180c006141c1c9900450700480c0703601e0003407041c410b8074019240c650010b940d68001e0399 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 484144055 1250 484142805 484142821
    0x32f1201060603110c031207120228080106022505031606091703090402030a0b090709060207080708120a12050c07021203162d0b04140a030e101412090105 68
    0x4010103443c0c0e102d5034028013003071040810070707103482303810078070904109004200d40c03505101a40d11452080c2a05010800345000c0d0700c2d00c7c59901e1041c03515a00e0030f22819410548020346403421410307120a801500c07480b001c1c42011144400740100001003c0f2000101150030b4404d1804c0300748500380114001e2000080c1d0025002c0c00b0001d00160000035500d40400101040300030740015050385645603443ca18a8090b454901d500790052500303440c1c513803480d45002c6009250000a40081d0303503d4111480801500c480014407404c0300c200d440805466040e80075003103c004000300000c0907068203040034000d4042d4140003e04a45009851550781040d0814000360743c1d2059007a50341d0308842c1c45150102050354040016401041120840070740a1a2800300100641ca400217413405041d1130180070410254100b040344481486014180001c00390700c0103014040c2d000441ca01408d1070b4980c2a51041c42258413009000c4114400b0b42c0303178051a0f44a15402104980120b25036103004040391020b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 484145305 1250 484144055 484144057
    0x1401020f1203070528170c0703020703080901050c030a030f0f020304050309040515120c03010e0708060703050a0b041b0905010503060d0609020a05040507050a1701032f120106060311 80
    0xe0380324452020b296803600c000403240b80e44000120031a0508625054461410039603981400c400c85640b144d2200010a02e0b040306040042c18000f4000c40401640340083c1e001710301002101d030007000c500c0d1140c40381001a038040c8902d40d0318a0f154040041d1307024026415602202d8041c1e012071003001100f00c4060168101c0c1710585025160b50300c03e210501492a264000c0c59200502e80c03280c0d4000340343c84020851014024801c0b54040c0c008240d84d604a00b000d05c146854100000000c0c504289088507054550700c0c00382415041513240d00c001848420b040d00050301c2c020003d0006c01a00104501060a44000d2091200040c00c010f0001540b90304c280d05481c0641001403841010381d1150b901c8000801a08804070b0b0030030410308000030203a946101e5988203040945a02d80d0b02c55038203600030301c81d031003400030b120700d6042c04070060006c5003c03600c0840d01400100d0b050b2a4155110141d40d00d0101144082a40f0058841c0e83c10460a0190050380c102c0f04607450500c01c14400116803052 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 484146555 1250 484145305 484145323
    0xc0f0d021908030a05130c0b0703030b060414060a11060411130b010813020a030c0605070203070609030b0f0604090f0501020c070602011a15040f03081306030b0306010e1008071401020f 81
    0xc2c0d071050001c10010016684000d402c070060350340c8045c0400c400e07922441002c4040c0c1c8440f00890021580e0300906426010b8a1040502251000d1819003405d01c0554140b440800160151801045840c1049d0144c0c0c95560180d04c0c05003101c0c8185031a00d404503890020313507104d5014020415070300c0404803440c0584404507405855840060359001c2d280014202408000d80c2c0c800c140740390010111345103582d5000540041ea85071590390303405006151420746103501140070010440300410200340e01480c141d03080142c1000103050b0b80c440308001340180c40c50310405030071000034500230b07001c1040550007004000c030403c1c01d48000030391790581070f400c83c0c000000c01a801e010a0075a40900c1c90043e0041024040765042c440c00e240d100c82281880c078040350400c0f40c800100081d0b404044c904014480d0050145140502c441e65007040420349607881841100400c10b03194020802886010010030040c01d041c908550903660b9030b02402c01c1d07891a9105e1a40940144540403981c2e01c000306034045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 484147805 1250 484146555 484146563
    0x4060c03091a07140309010510120b0601030f02070203030a030b01021605090a02031b031518071d01050c01180b1f0b03060616030e0414011d04080c0f0d0219 69
    0x5070721a12004a0310039682c00900901c1003200a0121400040e0480d000e5401034205400000f00b615005a1451621001d600824008500b00e141000041c00720f8031055072041d002e20703010403641c05c0751091401038000c8210081d0b05001c08108195600c0d4035a20020070034000342d08032840030005071a031005ca541c01d4001e00b500640c20798005014501c15030015508951204110901101e000b200400140c100b5113080c0140f03418004a800c2c1031404c003405e14000b0095a40c4205079040c600d10140141c43d03100110078041001036401e0000707a000f281034a02642502000380300e0320740280300c8202c45800382d100c11618040c480700401d400640c1450001c6d42c000c09002c0701c00015041603501d40403a0002009a40c0c0024104407644000701a0072441d00c080e803003a1200008007240c8002c120680f1039450202c0c1600c07560b07200410400790b0011201e01e80c55600c51b488502c503103a6051200d030a01c5041c51681d2240f207a065181440880041c1d00400c400259080d01c44012580540100151404001074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 484149055 1250 484147805 484147823
    0xa050603060a0501051803060405030c24040f02010201091e0b0901020901080c03181c0e030109030909020c01061205061e0f061507020d051e070f1a07060609020304060c0309 76
    0x401154040d000400106c548200000000141e1500181c80c0510454084407103800c04160441e845004010b044a03030000070a0200c50301c19075401c00e080f0810003c20280060151302c088000b07690003980030b405103a4000c1506500e0741c140e0100079030007803d000003c54074000d40700300040700b003132041c0300b0f070342c0490b1050755140456200d80003050019000503200c00c0c2c0010740e00b014044107003010841da010402c41107011138a000082d0300c0c0a00009810200b0038001d905281c030b51400682c0c41090b0300e00b560000080184c890307c80c00d1102c0c4c014142c517040144090510341016040c000000b4509128280c0d104a244640707607140e9804200120994400c2508040307100458500d06d00081d0b084020f6544524440c00c201090700000c1d44190368607802d6540c0d030025039498840d81075100740c03014968a045c008200440c5041500940001d80303102d1046c02c5039442202c1070000d80c48500300d0b400560045400d00007691550341c0400258410b40f0708a038000e242c100401c00080c028010849510b40100b290 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 484150305 1250 484149055 484149059
    0x105010207080f0c0609370e0613050703020d0603050318011409040515030a060636020f04030f060605011d0306040b0916030f02120105010308030c2503020307020a050603060a 77
    0x11003490b401c040c040c10f40c0980702e08004131f04d804079401200c201c4003600105540c1c1042da40d01040c544031a40d00726860000e103d20402000341c4031070100100d42515040005000d81c0c2d00e41080300240240300340156054200100017007804400009021810405442d0040c11b83e0240b0065030011600c0ca25514007000511031001140f916a0220790310101c480100004d10030600d0000381000b8082c5021280383c0c1da501c0051152000e0f0a42160004620200007500401c506e8038600c20f4101d80c2408042c080c3e0005481000c1150200581e00110b500440a440c2c1908030b240c020050101c6000380384c00200b8054407009000c019259000c2c2405018000d081070341c40703a454008035450010503000144c455840c01d1088482c1810281d0019401040b48860441881c81046200030300000c150403940e0500d401030010609007811250081c11000000b80d540e648825580b04001024041d6071410030071083c0035060680120041052078802c80e09540503d407240200030407404203842a40d0002481041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 484151555 1250 484150305 484150309
    0x150c0a08070204061505070606081216050705100c06050601390b0c07060b03061006110c06120f09010c0807120e03040b0a0216030317041401050c030105010207080f0c 73
    0x1407524a0024002280141c0c440c10450781d1589251914000200001205403c0c05071a00c12440a0072004c0c6c007824100b8060880f28100303004407010410b102c0c040454110400c0410410070b801000080e02c070100300445001c0140483c10000c600356040d5040c540041e0b400c2d0700c40c0c50700b11030603d0a41e01d44030340041c00f480544100a001090580c400ca024460207001c510b10007030035489060080750701956400a45044401d640000a480303000380d00240c18483c071042c600d4040401c0d1070140c40c221400500c50414980b905010320314850300004001480300c9259400c6400c06c1c4560800b220600c20354441103012800c0380c03000c04500340090000004034082d0b52207150050501400b00c1c1c3c0200c2c48001801c071560442c2d01c1603000070a11840083d641c070080c3d0301405600b080740c800c900c40c6088c051440c0c40c040c203904d0380400c0c1c240241c00120002010041c000c01c1c02c582945440e00204918905019454044d43c001e0003040c0c054443d016000030840d0001030103034129102c28002d400d00001d9902 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 484152805 1250 484151555 484151557
    0x307021f0c2901031b140f12150a020d05090c090c0306010c0203011404050601050604030537060606020f0318040906111801140a0804140c120606150c0a08 68
    0x605520800c2c1d60b030001d100020b4003088003a000e14040c0034045c60482034003003640c0c1a00c907a0b40c0300c41141c8040d914854240d0380d48619240b400312040c0d6000180101c003120303050821f00c05065288201c60448280550103041da40030702501c03010410100019112803442c2507841d0200850b10340d00441d4140001c600c482641e0142d0780280381030504814040c0503500007400c2d5048100942e00d091120b500b0041031150070000980102800e580d4a0300c0c150964640d00d031275540c1580c80c1c0704080c46040308140101d001c0540d441c014800f0b80ca20350602501d5141902c040c292500c2040018801d641c01101e01c001c01204642c40300544485801718001308000703120141c9000344042d1421503a803003110251050610080040c441e118205080e141c030150300240000140100c6031500390000d01078802c10540282070260800c1d0485040b118440090b18400d160201880c1d140d60032940d5080d04109503480090118042d64046a189243c4050200001c1d40c80c001e0010058040d07028010110200714103078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 484154055 1250 484152805 484152833
    0x60306030a030f02012309011503030c2a0b031e060d110d020301060303092405030a09140d020f0c09040b060622170118121b0c080307021f0c 62
    0x400081046880c144204d0309005000c0d81c21b000c0e10022904102503030030700380f05101545100401060500741541ca00402143c2d6a1000802120081060000c52058000340da034a164006100c7c2c8801600c2300400007240d00250b65403100300040b05441920501c201d58114410f81c1e001d440781442c1041c0342c841c507000b11501450b0340d40100ea01351070100035031000c5c001e03140a10300036116402020314001c8000c216140303031b1030904524504524203500f030796485412280c00a5221300302140d51840d40c100080340c4222056281d605105900c0c41c0a1140c0d00441c8003032448071396000790365030b05280400b0b00c8440e03001100d00906280343c2c03a000400901e041c401524500030300b111461901010040b828003143e201d50001801103e04001e04840c18500740036426800e003203502c26000a124030340c0e0b240100da4001c0c0400341400300501c000c0c56044050a0f00c01c441c01d410200e01c03120300740e40b03140c02740e02c07903220241c2a4003408070401000c010200100034850030317010590b181c00c2640c60716114022000048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 484155305 1250 484154055 484154057
    0x609041802120a02120604051c0e030d030f061211090c0c03070303050f0a150506031e010312090b04232706041b050403060911060a030f0b060306030a030f 68
    0x10404920160321005803100c0c0c0640320038001d0103400c1c504e004105010f850004000055801401000700194000c100701c0e000c0950892030380c1d40d41c00000000c0d10740c009120205905482480c1c1c2207801d0580c15040041a1441400100506611030007180d0030f000300034402801100c01076000c106035051124005a000c0d040c655101d04120040b0308141c210ba0040d6400c0d0b0005e034071a001e01600110180405030040200507003045544403465038030840302040d04c42c85120b0107001c0001007255205c011400c2c0803041e42c041e008050340c0c513031030300030415241003442d000040d0300c45602045040804c000c5405079088102d41510380c5148850b4455000f1109052a8121020344500030300491a220b8107000302c0010030f40d031005454810309110445600000705200546101801c20708950400e0868003581c0c0c1001000c500c0d142d03203043c100800180100d04580200000906541d03c0ea4164410309100c86c03400d90602201424000700b2411b4081070300c90541c10f40000304510001383c0a201e241c3c44410752 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 484156555 1250 484155305 484155341
    0x6190e0a061d0a031a0702060114010f08060f120f100204030b0c070c090e0309010f0302030618090139020111040504050a0b03030a020a020301060911030c030a0b091510020606060904 80
    0x22517594180a07083d94031000401e0105005005030190107100b401d014048030f070680d640d5a014040002d007101c00d00c5040c5070500034510003007000c50f110340c50480800341000c0c19001080c001d2039545582d846c65a900d000d041d0040c5d05030040c6040343c41c001c4030101d039040b4240301410340360500c204500758030041086401c03105041c0005205003260043c808640c038808003031603d40f07034440f0000d0050a0060b403000d08140c81003080141d030340e07035100c62404c4045543c099480070b07030349602c83c03580180003140c01c40c41c2404a6841c030b00710b03040c0148200054044144218008c00c000b0780000d038266514820b81c2c07049110144030500407410103070702041d803066007034101107140d0350b0480110382151b1040d10b0440050300001402c4040d17007000d001c4c00c0c0080110000c200710385010000107110500024050950780301001011444c0007a441c0c00c4035400d040010840b6886050000c00e030001c110640d031401e40229500a000000540041b4500d84078200182100d03150070780640410000f048610030400043d12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 484157805 1250 484156555 484156559
    0x81602070f0905221e02040e0a120225060302220b090f0d08160302100608030702040c02030c0c040b012102030109150803091e06190e0a061d0a 63
    0x380341e400101211040025241000407488210198042d0002c0c046107020b1900b0001411840f000c05840783c985100300400c680300c3c80010003a210b180d465291074410300300746100b0300c443c8000048041100c0d8003100e85400703045a000c1120340b0300d01340405000321810340c00c12800340a90020002c4d003075101c6d0060040d010b0f00381e030b031001795029030801c8206580210300da64030750401822001c04031000710340580d0f80d0901c581c0c0b8944584a11081206022010304040382010300801c004500d10440e0300c003e01800b070705c3d620026035039000180141e03ca281002c000c66811400401211202c00c1c10354060450520640d041c0800303005040c01c02e44c100650076036003116000d0100c248402d90b048010000d07030350f940340400540a4624600418005400c3e1103010020f0003400011500140b500341e550103206010311030685003e040320100c0d00d0b044000041c00c6610400a0008010001d5407034440c000d81e01455001e0280c010353300d01407032020803e4800f01100e1301c00d0784403140520090040407405610703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 484159055 1250 484157805 484157819
    0x60804110904051507030e100209060705100504150603020916050c0d080103050f0f0a030c02040b0d030806011812020d05010605190e0f06010819090b130201140a08160207 75
    0x88003103405650f260880e000c08122040c4070b18901d40c010100e890180003612004900c191240082816110b40720350000e01c1c1100b0303450705c60030b03500c605410005941c0b1012404c1803540242c01d007101c0032900c0b0320100039001d061085d1031042c1c1007940d07006044094160786212282101c2c0c90003404000c14401c0601c00c0c820705040401c450201100c0d00c0c2d4039514107516505c1d09620740905406590507540110440982404d0001204c0b43d01540504d00140080c0203400403034010010880215081028020642c060540007161030340030744000ea9170b00890f00080f0349139404241d114000c140c15400e48080c06009031a08400560350b9a0207503000196655036500040c02415902e042141030403580319040004a5110340746a46c1f2002c840c00c47d84542ca40440020260308000b0440e482048811646446541c680e0384074280290740010400314500300507690700e4404c010341070100d0008103500d01000308030a00c0d03001d44245055603240c03441d06488509030082040c0420382410218401c80000107456 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 484160305 1250 484159055 484159069
    0x30a0207170a170a020408030f030c0f03010f03110a032303190801150302030f0627010f050301200a08130503030a05070306090911040c0509120304090e0d0906080411 73
    0x141480b5280c08141e02c03d103901001c400c20000701402c2d035003841440100f00e03030040032081301c1e5220301106081d03590340d45000403102180070307010f10b4204c440300100002c80c43c11004481102a240511502d0f65034000c1c1da07040045204a5000040130400300d80c8504801d200700700c044040080e000c1041d2410810a800f81600d0840d40c50a180005a00c10004100b002500f0044080d100b1080c641540b4500e42800120b19000010b000c96000c0c05100d42c01c28044210058160300d03009500b802d10030103582d9000d40d848103002c5405582e05ca5480c02c50b8080120068405100f071004000c031030b041c10401c00d83e9082d182640010004403900300c090046074000b41c006d00095125108424001956040400c0001c0488680d908422a0149092548400703d0b10312640c10707030450350071680405c440001c1442245e0500a4042c8660400340703660344c1035078401022000d041580c0707070720b10104030913009800303080d83d0342c0184012080400d089120038442c051007084441d51260142071050346e50300d0298042000b03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 484161555 1250 484160305 484160317
    0x110f21090d1a1305060c0f0712030b0a09150909061512030206012c0408160303060518100e04050316060b12160b03190606110d03020f030a020717 64
    0x1040415900140c0c00242c00c4125800c099048000e462242c4590b584580d2918003800440300e1000225641c0403400110b01151441648811012031a131011600034002c6c000b0001d400b8482c040c00003010402100500c1040d42d5010004070388220b4130314000d5890010070050805844803611061101d24440e600070b0180000d110148000041c2511130800a08000c41a042011020303a000303a046501c960a207a010140d1502454041c80744e02e40d403404550903c81c6200e030560b9228225040820703d0780560104084540964071100c1003400f103080d4580c601011150060031144e544400d200c20704a0341842a441807017003003180d00d80300c031608003401458003155044503900d40300c01c860072803401c0031408050f400030200010080410b0ac405088080f0049000d614080840440041e0396140d101c4000340c0d11036101481000302c00d03141c1000400d0010f0101540483d803065410074108140320b0f10884040d44401d1402c541583c9500c142071029501c452400e44490341d20001600e010300c8a00001c0c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 484162805 1250 484161555 484161563
    0x3310c081e03120610030e060702030a0215010510050a030f021204060e06090303150a0515040e0112030207030b060105071a01050f01020111070b0c0408011b110f21090d 74
    0x26000d10800840c07078032605024a20819042448542c0d50482c001d114190080411901005140c0176004218010102c107850100380d841103c0a10044940210090034803003215400d440b01c24080c030022941004080c07003055041880035034140c00c014070410180905511074500811000490314100059030001045806090086c80504c400c10032a4400d034244010381c070010300380760714103098415101c0c0401081159441c4a9601c504060340d202c90690001d083c00810200b000784a00f10b80f411113030858001d0141c03010420001080c1c01c1001c80180042a0341a401001c1841c05e5585251400d84042d1405060020901420340090080115240000c0194261140715071506040005001407200c506055901d000c2c152034180d00580110780c200c5800004015464540188030300b074505ca0359100e80030750351070b20645440e40f0504100c0180d010800ba681c0d0150303000404841c0b902d50040c405112130a501000e010410700800403844405004180405414141c040008c40c1e81d041c01010b00719 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 484164055 1250 484162805 484162813
    0x305010e03190e240906040815011d040204110408030a0c1b0b070219030506070302070c06080108060403080c09040204060e090a2016080c06060a050102010203310c08 73
    0x2000200710818000c811034114a031083e020324607203000caa1003002045000584040c9490611124083c1c0b0049600b1030801805180d560f941d180c40241c0c680c10010301c640c1161192000000b00703e0007404528010083c2641200d0f666100c40d401c00c80202180108410005004d000028414605202800c0907481c241c4820800800350f250030b200b80443c00d24007503d0190822000d114401d43c46d410740301c9240c2d040d11400c0c01403001854070403018840303078002005072084908000c500d5526801030322911b4416005522410f03240c80050300d1544d424082c0d4040f542c0507600140104e0702c10155981c104080440c19480e14075010042002d0b40d1040c0c0040001c03514140c1d050300c0c50f080c0344060943c821209401006464075968450300c4640525152000305d00000c20030400b0b0140e038603c041030041d03201c02c0c4c240d6141032a190042c0c0354501100d0390b520401001400141c154018022203114211490450100c01e080c030a032108900000907800069800c10028100052010100380000d440c5d940014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 484165305 1250 484164055 484164067
    0x91a041b02010609021c090501060806130b071e0c0c030c06090602060f010518190f0c02010e0d08160c02030601060201140a0b0a05040902010507020a0e0106020d0302040f140a0305010e03 82
    0xa82981c015500c1300c04800d01c10880910343e1a00b1809200c034000d41c01001107503104190a01720701400950300800e66a024040900084445550f03031307418110700c100e10600d8a40e944003019180f90003100a0a030780500c4d10f154560203544035200c04400ca44c410070340d0400c46500d0b038645040f000001d0b00818040360611005108840e01004030951100c0c3c1001341c110b881d81001c004c522188501d1070840d04c000e410b0b40204000c803450b80e4066416940041d01085010107420494019040c402d00220241d40b82401c4103003100c40100f40600101d402d03485007078881c1c440040c1c286000c030041c1840400c10004c002d0314001a6002e22100f4004c00d0389600104281495254111103144094180340945151021001c01c58072450000c400b2158100e400264500c04c60005841610036180e00075404a03504502060344010303540780c2c1d81030b540f03181e085400c0102070070400c1e4100e101e980100116031000060400168030040303e01900620050086c1910705c3e660b82c1c4142c03e48069012007000740d0800700d64 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 484166555 1250 484165305 484165307
    0x5040302010e070806090703062d020702041a0a0e18060c041e0e040b0a02040803070b01030308070c02030622080d0c0e1e091005030a08030f010909020604091a041b 72
    0x6041c0181c1000c1c00600414144415002c1d66180030344802011140c4071220300020010103031002c04040cac000b240520010501d80140d40c025800600d04038407682c6020951000b80100c04072890703102001902035005181071001180c01c150004246100f04000ca40c940340780b1500500540d400b880c04101c04a8071303542000e90090307564082c86841e04848103210400c1241100f000320091304640c01c1110854140c88403445a0080e1003141c01c0f8001038800041e0660401007200c1c1128101c0c0d0095649400c01d881d014030444a4660707400c0040c0d0301d80d0051003c20051480d07202c560002c2d03000c1c404106052801e03503841c6844da41001c0305102c40d06a46008100c11541c0156288141450480d0f078684540301e90300c81d2080030450118041e02030311400000600120400140d03c2c00791070000c00701c905506952400581a910840c1c610784038009074000041c2c03820940c000d160020ba4010801420103041051010062101aa10301110780038029608030686075880f454046079040c0020400169503124 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 484167805 1250 484166555 484166563
    0x311030c0d09030c1502151012080315010305061315091503030f020d05120601171618120209070504050a0303030b030115030201020c0f0d05150117030a0509061c05040302010e 77
    0x3c040c45c071443d1841c46828503e50301041581d03109031001c160010549408252400554151308440d260170101459401400508c0018500c51400c0040e27044404103850011401d4603030607640c41c0e8016801d001042005000e64200086812082d4414100c81e40d61b040c1d40000d40740001201107072178049642c10b0013415801040e61b4540206400240324003195401e00800300e100729841741924162031804039506078440c141c6039104542c0d8030300c417036110704102d0f480c0c41401c000b0311040130204052000040c820300751014880308445a4050f02c3c90303c501660284008803100400c00010400100004501a51100c100d44040c4d4040c0da0001035403a0000185801c40c1c00120001c0300c844201202000141e90010b13030307194071100075140d03500501910004120044007006000705140554000e00d46c0c0302030455070080c101e510104000c15054800041a42c591203980200c00004070100720768050390801000511180350002c203001589a0140701d4101214403d940440c0141d440c0e03d22140c0d00b5034100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 484169055 1250 484167805 484167809
    0xf0608060a090209011202040f050c1327151205100b010e150f0705070e0402090105060a0504120c050607110108150f09090102190e0117130311030c0d09030c 69
    0x41e01004401015000904e01c0041441003c030180400b610030402c54960313412480d5040200b000501035420419115080c680181c142c000c0518801701340050221113202c90000c2c0840c00010000f02031440e00c10220150a40840901d00000c81e00c0c0002000e0030f0140011500074010340103031403c2c4185603009400e840b8800441410403c00b4810f10005558615156809108035800c00c0d0752012141000213850183c4507018005008242d40020b4400d00c6600c002d126034421520900700e60303228801c00c1494001c400b586000680705000a00003000411020021035000c1c444040101d030350384002a42644c002c1e9001c89a100c42e14840c02003e5810014950b0804000d0001182c1103084201150b58040d0881c1514828503440012800030340080d41203032202910912885901d0343c05440181000580d00c0e10340e40005c9a072549403042003000c00b1558000c0c0c40b00c25080141086e0354030111648025181c00156a000c2008600320002e000c10050203000d0703494031071040300c9180d4280110302046079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 484170305 1250 484169055 484169071
    0xc03031912060b22090f0506270f06150406020c041b2304030501020406200307030e0f010909290a0803040303051c140a1b050d0903120f060806 63
    0x100c140140b0f0f800034180d840d490b80d03c40d802d0200088011401c40304881e10340c88032401074505280c00c0311060058001c14031035202950000380070f5a8a45800c0e042459007075107402000703000404128204114100150000e04c010070045080d118018910469407042c0d008078056485101062000c3c1441e001c1ca038000a00c01d81a40d107020b69081015090100282c1e040100f40600f0340000c1c24800d0040030399015541000003103465503201c102c0a0300703c9001d0b44000c28500301c0e01e44400401c8030f0000c225030300b40ea45a520b5948603910381080c415043c944120781814000510b0010603032001078811074627071849455100e00049001c04c69003c00f101d089070250b0080441c0c440910950800004030b408a0f41e0500e80340c0c0e0344413a0002043c011000074118101a03e00b8840003041c0f80d10788003011805221183e5040124400590f100016400e01c03100c54008110148075000d0369105584c0900c146038000e041c80080c840c01c2450040c11622003800c4036030b520b03580320000d00c40741504000f069489110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 484171555 1250 484170305 484170311
    0x1271a0702100c0b1513200f03042f0405040503070b15100302040f06050c0a0b0106030203040b06030c0a03021003060e1312080f0406020901050f070f060c0c11120c03031912 76
    0x174500200300d07140000300380c003604151244005034520031100c40f20081030300407074a402d84034540000911a036078025142500d100c05210806402d41801c0c80c500e004a2201c040d1550302050185d040c08042d010050094031280400d000c0c181c0400c84481d1b01034826003072149242c81196a1900b00205024404030030010548107010902c840b0140002c282c1c2980d0f904c1c18007507100c40c5050001864001d64903401020441c401e0000140e542c3c2540180d806a4442c070049842c030340d81d070703024150344030382c2c034801a640202d02c500100090304003c074080240038030915000c2042910713071200601403c0e080e20900c0c1042c0320402024144170b0040788080d0152458900781100b401e2a00f4214044407010304050305a40e40000c00d01c41581c049e0048440050822080b543c40d414a4244070220b003600900556803103061030403402c2c425101e403044180d0507512070344402003060407001f440040403406401c842c140c8103050a409181d038041003d04007280034044880e2104140d2400146843d0300c1e0040480c006c0e00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 484172661 1106 484171555 484171591
    0x4030b101205100b040b06030f070e0a03050a0b0903041203050a05040f1715060d06020f040302060304200f010c03031e0606030b01271a0702100c0b 65
    0x2203c0c8040108480c2030007884161850765440c6940000200300051609145049181d000404c81c681444600d02000104484000c01e07002592580d0040c40c40104002c0007407040ca80c1700700761902a5040900e042c2900c5170741400303144010180500800d119825920a02c25030380140380208001d505150340b101d1440200c60030000c440d40a0113200d001e251b0020410700468040c00002c0c0440600a0580d25a5002500030411682109808000000140e0b44500256001c0c1d4003403e0b003142480321000c2c0c06c0d58522603100c0b109010f41d48a0b400151560b0f0400f0030300c0d1600b901400c0c0841c995034000840100310200e01c20041c00580341900104800350705600c150084482a02c8100b003084503500741e40c100e001900980318408112901c02c1c04515160740c0c0c078923021050000c0c8181012803640c006024044810015000903001c01b601c2c0e401e00c8059038001d0703001641461540c42ca19 = true := by decide +kernel

theorem cover : BRFrame.Cov 483992805 484172661 := by
  have h0 := BRFrame.cov_init 483992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 483992805 ≤ n) (h2 : n < 484172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
