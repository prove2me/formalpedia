-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2671
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:23:38.801088+00:00
-- url     : https://prove2.me/submissions/38e90973-7702-4ffb-a2b9-6955001bd189

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 480215827 ≤ n < 480395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 480217077 1250 480215827 480215833
    0xc0a2115030c1d060d050a05031305040b1203040918080a090515031611010f060603060611031624050103050303270c0402031504051302030105060a030b0406050604062402 75
    0xa80c0d88205292840c604500d9400b1074485800704a0b9440e05c2c0e844071032451b000340280c41d1040000d5460301d2460780031003101c6414084605041019151920420584000540389020001d40240e909602ca10980c0180941a0391399140000d01201c200c030a4407049601070012955811030b5030003c0c00c0207996100b510b108540c82c141e561146000481503070b00031034404803100b06d051090102a10188031000c070310003140d0350340c0140c0444004540603880051030107860001d079450034200010f000c0d00c850325a4040c26841008002c40301c1c012000300021903900004144601c0a0290189411505c0d0016030402942000008418000e001c0001c5000e03103080c290380707a294074201c0c02144007440002e0406d042034220788400701850410740c0095134401160310b4055148081403002900301da400f40c44400e40d00303007080d69501c11070500340b04040e00078070102d45881c0700d54959a0307011500d410082000307000c9a00d40c000700d01f20f511142c1194014040100e2400c07202c9120850a01d4a140b00194003c0188 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 480218327 1250 480217077 480217079
    0x15060c2102030913050a0524091b07060c120c09140a0506040305010b24090d030216030b0402150c031b031c09060b040b03121b070e0106020606090c0a2115030c 70
    0x40b403002350700d608119115114a5001c681c2c00802c495030030020b003c032124680c422060302542c45d44d20000d01c0c0e014407661001503000d5010400402c0441d1222904040c0741c6045034942d95641c102c0007000c210b80254a20781d8010f0080750206a009000e40d019640100000c01d0100400006400c0654000d038180c2c0c40740032a2100003c404941a240068041409001c2101e03000d40c0c18190800c1d40642c1c003c0c01280d58441c1181c0c99211488000c1d4019120342d14450107210843c50169106508800106187e41c200405010056100d1040b054640ba1000341c0100501e0b0400080c07050300d01e00600c1c845d0020b4100702c001c9141d40581100c52080b1901480d281c00388034649040d114a298104010340284100d00319404100c4050b8825410341c92440e100c03480a01180504022200140c0315950b190512035150a102078509007025080c0c600c92808102003101720034800c07041e101c1504880c580015110f69484000040c80c5009020420301400c08130041042c9d881e200c4201c00303e81c0b040490b86001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 480219577 1250 480218327 480218341
    0x506071107060804020105070c0308041202030f010203011a03071106010e010305300c0c09160f020c010807051c0510290f07080f0c0115060c2102030913050a05 70
    0x200300a0040c44040f442120110340036500c10b50141c40c40c184a07001c1c15058503202c2c0c950080c680c20950242d071404401154500450030700340040000c12113498000c2d1700310b504010003920b1303140b8402d405600141c0040002002140b2404603000013030344a2090f600156110301400b2000d807424007017594540706092030004041c080303141040d860044c585042c2fa1009840301c003548242d015150541c0c49104140d010055a41c0316003016000c0c102404060100400b4148041e1588038149100c40c295007000c6410303600c0d0303600240401c0d40030500703251041d41d90141c40160401c4005445c03a849a151424080058003002c008102042e20511514001c0d81070141d80b001800d08400d410402c02858284080c1032040810300103085120f22070152141090403440c50408950840b041c03c1d1003580d11106082c40724210000c0c1c0d10042c201c945403554001c0d105803500303d07000042c00d82c6c40081c507015103c0a2460342c824030565040e43c200070f140d180c9200c0c0c401d0501001d0801610a2941e00e45494003007920 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 480220827 1250 480219577 480219583
    0x6091a03030c0705041a181e1302040203130b160315081b06070816060c0e01020d0f021c08042013090201020114010b0703080105030f0c09060d050a05060711 69
    0x20400900083c0750084c2802c0500015014000c18469440360580b00d101d1240d03180c07803404000102101410046103031050210b04004003098a80343c000403c80284180071040303888240410303406560241c0d0301c0d15644070b0701003007200402c00a080407908609201d00d02004807115010110b0660f400d0200d804824103620124032107101d0003000c2e81c05040840569118800c00600c00e420042c070850504042d40c5412400c2ea01c1104c01c40070f41c05100300880104141c5100f503080001540c030f082c03441e044038280040c1d0b0340d00d100c1301032805100c05050042c00b024170801090405c4840b841c02002032611012019000380c1041c3e070215581c00115100c100180c560298803042c0041c01885140300c040508520300043c00301800a90441d501d500a846c2030782c81d6060064024190200200d0351510a801c004104580c1070704182d01c20b400005000070004c0002030b4111300c1c01803c958441f166115940000c8a4107259100145107000d218030341070610002060303080c8124a2621845210141c0701c0555031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 480222077 1250 480220827 480220837
    0x120903050c120316110a08040f0911160b182a100c080307110a03090603150b0f0c07032001110c0d0303020c0313090615050c06040210050d06091a0303 66
    0x1c07820744c0c40e403e04003561003071903005060074210f4142c0e941078216032214855a803041c0c015135074003180d8441c00c010701e4000d403090782c0c3c0c135010701500a410150f030704020107020b450102d80503126011000100d04030214004400d071013140e10204540680c400880c901e44049659034000201e15002d50361a402424603240c1c200d191411940d4030342240b010340c0d99805690f0800f03400c3c44c0401801c0c0881c4081c162041190245660282e00d07218191490184010107440030354031a13840880301e00508004d84002841920300d004100d44c1c1031b980f0740302e18400c082e241142d540d0010702002012b502e065615040f00083c868124402e1365441e800d144040c3d1038070740e6041c0038003489030020708001d10701d40407a00c02c0d800b0700540c840000649240c4002d44491240280c01d030f0700306072203c5030781d80d02c20000e849410403040804941800c0c50383c00c103810000c40d2a02c40d00c00420203401080901a03014600c5e1140003250415a000c110030004c050f01c0742c821100421004c5103582101c4803084000d040c525002003910 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 480223327 1250 480222077 480222091
    0x3060b03011d070c0c0b0702281403030f0706020d0c0807080a0902010c1209090c090803180607080408031e121b041208120121080901120903050c1203 66
    0x40324031160b000b107080c0c0b40b0300102040300b04290b65000304001a01ea801c10001445901d0f015501c0b480360b030040202e501c00801d000d4407050f080c141c130070100104150742c907012109107860400c403905004011906510400000d103582c620001003031310030020150702408a401e6007860400c02e0000300c000c01c2c1c541d80c03410b6803a40c1c00b180d18000001c0400c40d035504007003400c52040c0b409115049242c0c0d00e01c10b040f42c820480c0d901003203140c8424082840d940c86403124071401032404040440c07500c078950303449125485014100220030b084100c41d5483c1d01c8101d6124640c81451076594a030b59012a946980208980d08000101c0a452450440d1408261410f0410881c22410103481d4041d41851142c184040808201e40030b000c00203020703044401c09810745014141042c0e844005108440c0700b940d05070840d603002c0518500c1e0011855000f071503903040c01d51180c5150740e244410340050320421101c000484606003001c025004150780000035101d9000b4510490318003010740f041d01d0340d143c00304a680e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 480224577 1250 480223327 480223349
    0xc061f030c090b060d0516110c100809010e0604080a030e0106180f0608010e0d14030106140d110412050d1403060622030b060310020304121103090406030b060103060b0301 75
    0x144210401c0e0b502c681074042c0010034040c0791094110b110000e1b5403003280c9128540c41184080d81078141c0003030074401801e0100e0003502c040d10800b0300080040a244584404000c01c180000c3d89a040950002c16280d0a11045403450319143ca08108190f00101c4240000b0341400c0c3e080c0211a01405440140c560044400c000c40659074180030007000212500b000080d00c50f900058803680030310804000700c4000025201821019002030b084132903000b20700f031300d0798030400042205503400369800320038190300003500380e5604150f50800c001d40424030100c004503000040c0060810042c8084506107403150003501d02e840d56445003a100d40580002d5140301d0344041000400d10f1401600034501c1c00146219144903807a0340c242116840700c15081102d00241001c14012030385070400c0741e0752118402000941c42c500d45903854202d101d14a01d500d005000c884c00510040506c03d03c01d4410b1850050302c20030006030b990401d00c219600649000d8003103850020081200c454110881c0d050751800b11007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 480225827 1250 480224577 480224579
    0x60203030402010f02211e0c150405070f0e0a1109210a1502120f04050307021507021e01091224020909090a0203010c2f0f030c061f030c 60
    0x192400d004d4884074808501a04040c0c003050442c075250610311168030850680c840d414641341c013110941030075642d070040310140030b009a1034000041c404001d041c6010034010303c0c0c64620303110b49891032640044045900000e400b080390070901c1101403091000f0002403002244003200070b4824400e903591280c10449030442c881c1020380310886100c0e1901c0c1d020844140003c241c60b41a12500b0540d80c1410003500041c004c03100a03032520076036412500c08d47d4040d00906080c0e41b01c550340e108401c0028042c2c00d00d01540c840b0703005000e05462219401400b00c050550203100088060050801c450b4080751007003030040341a84c0400180903580b98450801ca080c80070085516a00600101d041d40c1c1c8290200209506a140c1050150103014000c0085c0346540c070328070404d070035644520f100200704110342003402c40da1055010740749002d4190322507000d080c034040b0b210241040d5541c4840c4449210020b8000c056034400181a403040240c0c0001407010381d184030315410361303034003c0c4405802002d8100c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 480227077 1250 480225827 480225829
    0xe0105130c0e0d030201024b1204060e0609030a050a03020c03161b0501140405100c21021c0e01080a0b0405010e0415060f0923010311030d0207060203030402 69
    0xc0500316410380342c2003100c07551042400040304640b09800c124010307500071a00790306030620902a000e003415403009100040d070481c6400052002501d000440d61000403000c43c0034100850120303403900302c1609520b8420728040c20403a0251529440c00c4002c2e200f07032000102c0c50380700402940c00c91b0036155241813501e101c00350124060741040e0210455030004201c80902c018003c1c03149044244680f01c17140301d81310705a812000b0000660300040c180300b110142c100d03001c1101022103041d607804981030440c054400004456040409100805000c5941e4646003003021211070030030804060b0382200c808c280041080c0d00d1a00100f4031140c086015420010050340c000e200706640a007030b070440003035040d60030000181130701c4082e03215000207200c81e8244424041040b040c02842481d02105114441c5042911554140e2510483d4820f540c4e44001c201011a500c010301c10b20b9101c902812415612402d100d130b035648280c40560b110303205441000d80c00307e002240b40000c80384a6001b4604603640c0d50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 480228327 1250 480227077 480227081
    0x15060607021c050105010303201c0e130501090c1419120903080105040c180308090a0909060e0618071a070b13020103061703220b030f0f010e010513 65
    0x30304100d901000803582940016800407140220303a000b9800400c0c154994200500100d02c0502086c0c0201c4c03504410b40b0b43c0c404d000940c0128410301070180802008401070807502c1d540501030103680002510070000c201100d98124030b041e40d060f05000c00803000c2c50707542035071480c1d00b8403901840b1007401d00211002040110180155606c0d50600b018450101c40103d0300311142c9460440100711150018001070270103200f00c802d001180e003819691203902100a01c1103141600c0002d2403518001420441d644079401020000e20300200140403070205c1d4505000039098410b1194990b11800000451200303404100c607899003541c102800b4a1418004a0007981180c00802405032001704400c800051103040218460701e8002d0b10b49600c441035200040665141ea400030600c200655880269001c010003114400d021054040841b640c00103140001c0c03050340d910410701d8803400b00810107216070a825043c0b044a5200d0140f001d81c0e2100034040101c0d4083c00b501c1d40010b0a181e81e1141c0c04415 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 480229577 1250 480228327 480228337
    0xd020c011d0309180c16030201020307020607080108060412030608010c0c1e020d0602030a0b0a08060603070e07020c090915070c060b0316050402090d0b0709091505090601050a0306030c12050609150606 88
    0x40c95406250050b4003100201d06c0c00038403403c8005030740c00800c105040341d05103d00c507000380c003914224000c0c0d454080301c00c0d030312000940080d00d40c912003650321601ea0300a520840082100c4802403100c100000000f40150000311819507a0702e00300700c031405c102560071908040140c0e004004548038089901c40e0402074100410840900750f5468080c0c4855560303082290003002c0b098002c4c500761070603000381410a26140c0c80100500c0004080c8001640c010481000903031381568803c8060b524485a186006180134032480c8044c10b11040c00356155008898022003406042c0900c036280003030b02819030305e2500549484100c200860280b14074078003030b00201200080240200c203542426142c90020001c10b54050000c1508400b0402909071742e4026066005403840900800618007004034441c0180200054100070000a00b07040080c081d610610140d50040441c50505803034440c1c20381c41d00482c000070703a80c6214860014000030800100300c2d8440d6138000000780c058450360203010485d041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 480230827 1250 480229577 480229591
    0x41b08130c09020307020d0206062103041703091c020108060d020f2d0303040e0402090603070b040b0703091e03171c0b010320070201080a020d020c011d030918 70
    0x1140e85a100071948520000000c0c00101500503503e041100001e0300d840c034050320ba070056400990030410b4954a0035210709005025410301c01c890140b1000050544c03080707411212007801440c210011a21001000d080b09613029203640360f56000b281c000e001c03031000c1203c0003030008400e034001681d40e080c491007098079144060482450540600e000585034548001201d18990704240c0641401c02c452243c0c13034034440b060380a5450319041100c003140b40b409c0144044d006e080f60b100829429202041340c0780040001e0030f034454540341c03981500950b81c0d201c0035080e4005841d01c0d0020800b8011841141014108500c44482092440d80c80d00c0c2e1000001801089000c418800b006a290303401d0144200c02403200d4000414400e40f500140860f0400303012602c407006040141c2e84a040c504044454140d02403c080410395514a1060007a220b00107058002500110300ea0078000e005410050154803000d40752102c41004071840d5590f0700a80341195070100020890408408140310115004a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 480232077 1250 480230827 480230851
    0x1b0609120a091211030d030603020d020906030a0803010f0609060906051e0409020a0228030f08063001050703020f07063303051615030f1b0c03020705041b08 69
    0x159075032038100031143c50345040d2800030300800d0a1580346428085884a0764140c02c003002800d040d80c02082c071040020300024010000c2402082da655020031283d22200e0303206c02229a45c1d13031981c0d0700c100d00b420f65105010110300203503070108049015050040039a04a0782e5250708203071444480c03c1c000c03605206a1b07070700e0000030800440c0c3c0810b0f6000506085c51150020071b20a07000d52414200400c1050945001c0d1000780160b1000903480704044005510519113100c25072644000100c00103050004100350503a03000d8140c50f0388840806a450810303e800c0200040d0f91403080c16000e901c01e203000241e4141081000c0800500f0950006440090120f821510031359040c000c1c2c0c000d11001004e07140c040401900400070003038100003030003414000a828000e01403400300f640c24207200e90135140703050548a0100141d0b142b21a0f1003d414110754400b070380c3d401c030b00c10213003e049034a50000550050145940104150405000d11412074441121032200c43c1c22149048075400406001500c00d4a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 480233327 1250 480232077 480232079
    0x31b0602030a0c0e030703020303030705030a150909140f190f050610150e010e1507060504061b030b090c0a18230f011e0302040b0309031b0609120a09 66
    0x15420340302075031199810b0b40000030303401082e00000e030200020072110b0344660b000070014001a01c4c0802600c2d0000b9450070841e842e500c441c840440505900d2843c003000d5602580009400071540c2c2000c4100c5015006110b0300101e00c144c000d40341d0206d008081e00661015034400c0e49404001c06141c1c109010700816104e254859840c0c50504106a810190307418030b01409200d824000c6040a441d01b6003414036900c04040078001030314038640351500501c5000c8040e0811249000d80c0115804070f64010800c00c034518151403d0002400403542c00c1c410825048601c1000d80d0083c0f08110764901e004011080c1544c0b4810800c800303a000c0c02141c3e04101d40006041d10020441c48164060440e0506c03c5595400c0d124001d91039450320300096128000c90401184166008039904c090b80940b9101e80070030700d164080507000703841f81e03a100010801000040043e547c002001800c0241400c0b1b51100c034640710355258640d180c0f0706840900317181d00001c0040404050310701c010708020500713052190b107507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 480234577 1250 480233327 480233333
    0x3050309031605010504023307020103061d04030e040902060403060b0109052115010e070309050c061605120301151209020d05060703050106051815040302150c060919031b 75
    0x1108050780704035100e0b91175409100841c42d0a480704501001e0417082c61051000103503405c0340e80603814181d00804a000034455065903c80e0b0420030140181004407143d17070240d1021500303081c6017141d007a800903101c0a92580701e842c003405201c5e0250b030020209800d040c156211070000704842c4165a06110400f100010203486440c2542c608186000003940f030755042285031400c00d12092800d402c400d84410041c08040c000240241d0005824500024000d08624066260110504101e68410404510062000c50804014054078410b50540e446090401c0300e4a450380001e00445801441103c6004002031040781110303a00d40c3c2204000c28039000c1d6402040c0d41005440040c0d074150404020000741035014000c4600510b41482d0141c5801900c0301c0032140c84848525080c850b91050034040d0303a04081000386c4010b03580051800e401380298114213031030381e80200d0340705605014000000720704010100c0c407580390050301090b040e0203221564040b12841908501c18803059603010000c404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 480235827 1250 480234577 480234607
    0xe1506040e0a0f060c0c0b16120e0f070f140111010603021c0b100602100e0c0603100e01080d050418021b0d2a06021c1a090f130305030903 61
    0x40d80340a04522984003045060400c140c03041c030102401800f9000b046c600002c0e06660b2910f6018410710b10051308001d581c2d00c1203407501050081401786a0801620720001c45000c2a100342d91142c420071103210b19030301d0652035130341c903500c4c8284034103502c007546040490350160304040c0c1c081004c44000184107889030300090107452070552502c58602c48001143c200902041a203810008081d07881c0c003918a01a0029940c0002007001c0459a0722a01600761440040080e83e08206004150b19241d282c10901060705a001e441118800d801c84000003600450100e40c0301120a00d42d5120780c50142449c001d10711b11081003401020b0203600b0442d00084054a010221403901c842000c2d04510b50880320082050211010111120110b62186550000b120004010140c3d0040300581c50702c3c1c600e82030002d2440ca25075003586090424030b41030791704c290220341d103001c085044032000034946600c0042c41201c42c0484645d020448408100000710f4060000780d81e0003000c0000316031419500240ca110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 480237077 1250 480235827 480235843
    0x80c04150e040b07030b0402031302150409090f0501050106050a092105010203040c05091b1c09020306070909060b030402030a0213020418020c07090216030c1104020711130e1506040e 80
    0xb0180203d1060268a076418001e03100d082c43d0484081d4190b0501089164001e08991380080c0301d102c602d062020030301840d20640f0001c09000c80c00b0401c1460508020f01c044000100440e01e5510b800b001080c0d41c1c0c010405c0e1000c240c080e64514060504108036144650b0b841c0c07094201c80c00c4a0702d02040024802d00085100d14403030f8011000ca5031422090107004d04020741034a025010905001710310500d4401076490f4203095403c900541d0407035015003801400c1161000e901401044100315400c2d0300b00405004480451504205896442600b0314a502054900940c103070000c61011025103413501c00302d0f45040070003000514041d0f40380b0741c4150061040081006203900440d20300002030b02408074000400c0a01070070f51500d03040c00d0140348545c015400080900c003030340e50100140003986c0c00d42884000e02510841d61412541414001e05580809440c41904070805808200c0d895000b4a20199004001010b036a02c072861017007010784c001800590450394650800c9110032003000410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 480238327 1250 480237077 480237083
    0x1a0708130602010c0e0a0b071e050d0f0908060c03070c050705031903030e010c0512150409060209040b0a030203070b0a020c1003060806010b130311190e060a0f080c04150e04 76
    0x104e88000560150082580c00d8030715100d012040c41c02c221102109013216040344d44030345454101690025420500212500d020b051403007a100c2000c28580c10115480c2220200d86071041103560700c80401d907407840d0843d030480d8034540900200b000e0034065010006060302c030304d054810042c1c941b0082407610695134088895141034003404000e15403d48520074002c5a80e900a102c1c10080c94406021403046805400c88515814001180c48411a140c0c000b0040004d206002c14061414808040d4110401c024800c0d0310701070603c020341c981380a40000301d0f603024010b00040da14000c8a141d09420071000c40701980034210541c0200d40d1442c07520001c4030b1968900003078050900525070310f8160141c2100c440c1d81c03010040e00b80b800304c0d0012030310112944400c561b045035020001042c4e014000c910055400d0f2000d03d00030542080b000c8a02c0c0c42048162107843c2c480ea5540681c6842c0c040520881c101c81d08020599481810140c0044001d1b4501209130b51000c1d0f500c220078480090112025 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 480239577 1250 480238327 480238331
    0x61309030f09300f08030103060b120c01140a0c0c180605060c03070204150504050a0f1112040f081908091204051e0a081b040e01061a070813060201 65
    0x11030001078200341000064200c841c0010f020380705403811200c01501c00a0003035488142c1c01d8a01c0204884a80200354042c2d000c1405030300c2e1750b52840d140d80649103001307003031b0320504007a400848100350010b01218912016035550007140c00220704864658400c000c1c000401135401340782e4011411044a4000070281e030300300000906111500181202c1094001c03503c00e0008021446407040000305413001160100d600040c1d1441c04480c140d50b010240c6d02158110303091000f0400900190351150303034a0a410b6009024049141c11703044106c0c03040058042540b003c0d01e0106003c18240c0410307901040c440c112403894988086c240c800704082880c3c003c80080d841804202e0404000e11103071070000c01d040d03546402c00f0b08120005010318035110200160303481210800015a40302c9847c94028801e80c2c0a8503c4101c00900c0e840032003449000080c002c030f0078030940b143c0901e0144a0041200c1072b1111303600340e014981e400141142d03c040c10648034024280304214401503a2114040180265000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 480240827 1250 480239577 480239597
    0x212190203010b0d0f14030d09050c040c08010b0708030a140405101505060304060509120a030c17060a0501050d0906021602100c0302060720010204060207050a09020c0c060306130903 80
    0x40500351210342c11003a00030b04c010700e1040002100300300c0c81c04078250301041d04821a000744145070304d14000c160812841e5800d000308002071110114034a082c2550641d400d0158441d012404d071007100080c414071012031401c1044034045519407000e590012410400800c3c1560000c00c401c0342e42034280c5d4240e030141c200d0b004080302d480d803522404400c7d82c941c0d1980ca100500c1d210014080d400001d0015224075180c0e0f000840d00322050012041640e141001c15456420b0a040100282012580c440c08a00080d60343d80300b1584101005110b540c00074491190700d804d00004440380e805c40c6810041c05c5440340b480a00046850000d82103004981590300800030740c0f4010012049d2a0600300d0090100e960004070100350301080c3c250388040d0a04000444281c00060405d00ca030300780300c03080d000c0d510200b00880d034180d0100d440c0701202c40445c0c1110b44151600b03400ca04920903000404210342c003103a0b0001d90342c2000c40241d6072004001b8040c0d00d03440d1006c442c800039074503529000c500003030b41340340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 480242077 1250 480240827 480240829
    0x60902042307080105031902120f07090e010b0303070f0302160920030403090306050907050a030c09060f0f09050403030b03010509060115020708061503120a09090b04111602121902 79
    0x18005901140720f161205855143c42c01003522585601c10002111900405481c15034440410184007a0312103021290780c42c0c1c0c24009191140480d0080f08005820f004d000400080140104112404002c025512b880159075440b04141e02c0a5401c60650065406000039100701c02c6802c0010b24050201080804483c0d0302d0800040b200304000c0d040f9901803003400003080d4060000015298096000102da480c0c20400901c1d051307070740d48015032005030080080200715401c0380e001d0442e6400c09046c0402a2284560107403d4458001e1020051801c1410080304903d03400640e001400790030300141c2c890b00e44001c2030035910110354885582d484140104400c24111074a0400b0074124405820b01d503040009041c0c640d98081d140d8080d003020b0400c4240c055405010444011034084144d179501c001c6101c016003141303218031070396500701e1403c800720301303070b42800e0103410204a96402c2043c0307407402490302c90704458100300059810041392070f00741042210400c50341d0003000c0d46205140800700284 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 480243327 1250 480242077 480242141
    0xe0d110a140118030f0f051e0307020405010b0702031209040b060c0318061806030c131d070206070e06070c1e030b0c090303090d050313060503041202060601091206090204 75
    0x14912070300f50080300400206031100c0b58198441e511403203c2e603598596041951425580615081005180b440700e0541401c00000400313101c0d1007520103204582e80e6080107800c070f00490001035055040a260b142c401c2d04000c0040841001c010000217401341c1500c00310303d00750018268102651b10000d10b40f003040c50005012981c501c0c0880c9e195140c9142c20466100e000d00e0507030b402d0700850300400803070310000b2810140d50302044003451042244d50f449000c28400081121141065404000482c14072880852a40e110b43c402d61600e140c1040300e1020310020380c1c4201410340e03400044003008500758034800340d030301032446c440720581866a0841c102000c204901508100300d000c400c01c100305241d2404401c2e104c51401c00c07248804e00c108030307040103800c512034512280508010f9080218209070020040d602883c003039103030640e2031041100103982d02c0000784c45007800b0030060001000611214600354503010300c210004216100d55601040c2512034074407480015600c0c0481d0810740320039074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 480244577 1250 480243327 480243347
    0x5150414060705090d03030609020d0504260403030c150c030209040b0307080c0f0d0f0f0b061014030901060f0e0106170f15040603140f010c0f0e0d110a1401 69
    0xc018000074140180040d041d4851020b01d0b90113040c0c801240c40505000394001c070002d2408140a566070f44a4807083e9004040c119400c0380c4041100c0440038490f0507150f0484040e100c0840141e141c40e040d91015580c842d0303c21002c480a0703a03503030140700c402071580c02032035041c003202d840151712841600304101c166604c00b0403040c001e50040c841000b01990024400240000a644001040313248001195070700c035403610041e003000e400c2406d10007005043d40e40481c003540501040440b0740c403046c041000e02440c0300c04040001344081d050b49480c80340740c4000c581150a60000080e200e80c1c4003002c40c2c914a450340120400d4148000412003a50010111034994486904203070061500030800011544090503d042400728034600050549a0f580003901640d00b000d500d4640f154a0100740350b890014100303816455007050212000d280c0100726011201480392260a42c500c0c907001480b4628500850035142410b540485503103584800c865000645038070b10349454079005650024045d40742c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 480245827 1250 480244577 480244613
    0x110406090f0c090b072303190509090c040e1b0910020c0f030105010f17030f0c010506040b0f0d030e040917120903030c07020d031e031a0d020f120a051504 68
    0x108035070000186906c0c9410f041002d41804413600d8030580854a1841c020341805248004054640e04102500703d409017099003002c9680600740c1c0e44014001e50305000c1d51003802d10043e54400030600c030541111703007134041d540c40240090800c11240300250300300a5034110400580c0044c407100d6401c1c20100c85e00745030b11405078004d101c41d515100900c503007140944139512615503400411480c110042c07082310700030318019140c5500c81034100d4105000f050b05940d00740c40780d1b1801800d07282c5810110f20840b4030f0140100f2200c0249801d4030f003a00c14101a07120b01e58011f03524119000003d03881000d5010b101030a0120a032036a8885a21001d0340742e01800000b00c5038000d10805c00e030354245134122a02103030705640101100030310780b0b02550041003c2c120b40e001d0a10441c2507a0b2060341c10b40c07101442050070700d010568800043c0512640c007100c950041c0d0030150103130000a0500340580c078680200307000022180c00d01801c1c0c9946003403900c85540b01e080e03044003005100c14400c0300c2e000c20240c50a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 480247077 1250 480245827 480245849
    0x2091f1401050403140c060d06080d020a03020d0c1a09010507110106050a03020d0201121a030c12030d180f050625080a1a03161a070b0103110406090f0c09 68
    0x10180300080e01c14001c620000b0480741d10301c01c0f41c180c4940103201c1e8000042005d440e860f21a001444242c0c0034042e43d004e2804d95100740003040e50810320014140b0001d58240d00500a40d00c0000303412921800a0102a95090b1150110388072408a1504030761040700d4400c000145410300c0c41e001400303089024100807003a81840c0301800965110031801003100e80c110740c80b1000d0282c0d480182c6104400142c1c441c81c0760b203020780754400708111aa103000b0500c412000d6602844e150020056101029145e4134080e500c2403091000c0e60302198000d5020174405075440400d031141c0d5555450701c022020302240c05400c05c0d405d200d424a80b24000102e1044207251744015001800300c024048880108801d80d82034503002e0b824003c040801001c241c820008e0203443ca0326461504605849980344035002907019480c40344c1006000f0801942c0d21035070700c180601c83d01d918684498000030302d070b40c8019a01c00c0c0c3d145400a074400640c401d80000302d04855021448107403100000e00b9108143d408512000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 480248327 1250 480247077 480247109
    0x308060a030c060f170a0c110321090705060d0b01030f11031501120908040e0901200c010f0606120606050405030a06022503210603030507030e0d02091f 67
    0x61a461400741a52400d213016400802815022a0140c01c1c0300d8103a06a00300c004144080c1c0035050704107540b820000c2d21041c14100401c00d00d85d41ea0311400d140620400c074084c0c40804e01c00043c901039500b0500460888440301d4840f000218030b640b145003030495260395010001d2440d41c05005410101c076520004101c4a43d03ea07121016621005089048450104090b280d46a0040c1102031100718080c03810055000186400711150b442801045400402100000c030501414020381d0308407800000b0b07011000012200100041c2c1144103110700a5403140c28400307a030407440c07013400d000380425a110244481510002402c451450704030301d0400c401000144015100040e28003c9550b014000581d61000c00c0214000d1a5500c0e032140000340c0c0400254040c903a00c080389101c280900580d9050460b0003402c80d00c22200540720042c046142804018046801480c014150349000b6180e060079250b10b41c00a00c41c40000c442c2d0307440000480d0310030804130100400050291843c01a212070007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 480249577 1250 480248327 480248333
    0x40f1a0301050d061409010606020c060301080d080403121104090b040e06150a0905070c0312050f010b030c120711010f0b0d240207030903030e0904030c060b01090b0f03040308060a03 80
    0x2030300c41401201c1c00f41c4400d400c3c503420000140e02001d01480049180c0300c070f0741041903c4a0180416100303120052003100c20050310703441c1c00002c0360704035481c0301c2c01800b07a00401d04042d1844c68005000381c060000c3c01d611306400781298000e0030001003a09600554a9003000c8910049445c00c004160059142040403880e0b0507000030080d41041c107000207085034000e54400a42900c1c843e4009030040ea00f04002d01810729042202038960500c030b41c50346049580480344000480c1d20440b94100d600000d07c00411282c10380100554108203180d010500d4640700d450099201001a40c10072300041e42148464076028007032080d40111140c009060208030003680c001906070660f2000a0500407120307103541c0c02589850300701c54400c159113000b5920307130215090147c500503591100390040750010490640520b800e000d4980f1070340e4141c039150000d0406403200d000600d99150400d050102e03180000c504940e40e43c0107054200e007a06e0306c440d030300d20f4142340007000c3c079801902c050f014001e000414800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 480250827 1250 480249577 480249629
    0x1106010b0f1b061e1303030903030207020d11090703020c07171903030203160e0616020109050312040f14031905031e070215030c0d0b061b03040f 64
    0x11600c0a01689444040794600800301e48a00304280482d400c52070200ba0152a000c201ea503c200e840d01c1e600507606110074640385001d0300440c3c4446403850848031060000b8040c0d4011500e160003442c0050400c075255010640c0c0c802006410707039004a038a113409a25180c4003000c41d52080503458190305103824a0180c641c2e51865000c0d9141c11168520768050048042103480142c0110007509031b8040790a080180c020351090760003440c0c440349000c8070b10400d40581618401d6080180080d8602010000d902c040d01a4650f001c0741000344041e0002250f607010009504003030a842e140b00c0e0303103a24054640341e00c0d0788076074006c100204030180c98107000e54004c24040d910740218004005580d4092812500b50b214020346003264511250081f0420040d103009049124400e0b03e0340c0090301c420350500a01d901044827a01c2550004100c2c0d844911400c1d0800c14103031001030000d0b0f041c2110050030000d40055070720714080aa102040400007407502c0803031003005002643c000301c04103200a044400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 480252077 1250 480250827 480250829
    0xb100f0c03050d0e0105250c020a14030a0b0702161208030c1309020409021c140604110705010f02071b0b03010b1612020d0e06040509270307060501060807110601 71
    0x10302c0070100e1508101441504050340000c8140000c10003490001045014840311404000306401c564468441080c082c68104044a40040070090654541440b1015210b1412401134050240030680400030f01c001011324050003080d00900400c424500d107481340e80c00c8070742c01281c0d4085a20f0030f94001c11440400c9a0b013003074030340c1c5100b0795519000703400c1d81720500b00354401200980b00040004001540c4e5000d020031074505951514541c400d07200001c141da150450140c03001c80c80102107001b916095001d410030700300c0d11400c6070a01e649074960a0843c0d10f103080c1c510640f50001181000c21050719002d04500c050481e007400151b092503d24100c500050281e0508060006400403045010340d881400b00c0e03a1009210904503030310030000392070703d0b14099001c0c00300f54064048426403604405490669202800400b01542e44c402e9000b50355074111540158500c0038074000003041c00030300060051034000c00d401f0406515025005105110050021003080b030380200d031020107840030030294 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 480253327 1250 480252077 480252083
    0x512011a01030504030921060f1b030b310c020a110d02041409070f08010605061e070c031a0a0e0d0f050c030703030f0b030c0d030309030c0b0a0b100f0c 67
    0x83d89980d00e2034291156000380d00a21401204d050810303100c91241802480164481c0105005150b8484000410765a85460b0406407034882007068032030511035803104943c0140284440e417184880c405681e0a2150f0314061904180c1001c00c0d960068814040c80806282c13900c001c002100c403030344481c8103044240861520a51503260600c041d03690b240c000035188cc680c00b04d42007890402d00c907041d94504c0e13140700d04502143c043e0f100091100b0103100300c2c8115003000e44030f81e20300a0b1680f0207012000d411020440003d5040c0609004544202d9410000c0c2d4407802c952155643e000300c551385c00c6100200324450150401d118001441400708071800041e1140c00c040d589903030321180a0b0360600441c04044070302d00c00828442d06255060300440803000c100c0308204503030300940040c9501ca0b0404003c0940084405d95400000b0384260301181c4154020314000448403442e5903590320701d510079a402e402954071440d101c0d505190034034a25410490368101145500e048a50142803507800034009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 480254577 1250 480253327 480253331
    0x32018100902030108060402011d0112020c1501030807060f050105011202031009020a20030702030601030318030609060c030b01110c0d06091a010f060807231b06010512011a0103 78
    0x10410240c612030580e80601000c03501503481c3e60319100000d03540e2001f1a0180e001581524903030350784020880f814a40c800049e5610400204000320050181d8060748038900035101c3c9040031a2812a03404456010b580705a0040b541c8411070b00b44001a03e00c100005009280b03008010005685c0040d0007895180c1114405030300e0f5515841c1d00d0196528540c1b046000c20b00024050031560b42c040d00e52444242180d44010385103030b001009650f40d00821000941541c050b800500c0400e0290070001c00d1298400d0840142d2034413079807200140d544201003100e4240d11502c0b204145a09801220601c00c404e203007c1403800c1114840755941c04d80c1200c000d00408414207000c043c840c06400c014107494100c440040d8070345030700c4116000300400b403040391804900200040385503407103090813a020700e1066890304039410385400c58200d00d1880703000303065000504118407042a0307074020422540c0620f003006050301d90315100500080b4109035203414060b92400302c0341400c800700c543c5914039070b03207080c030700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 480255827 1250 480254577 480254581
    0x1602210d0f0207060501060e130915020c0708030c010c03050702030a200a0618170310030b15030d0f080c040f03060b120a050106242319020106032018 66
    0x480000303205528010348454180000821102e400058230304003120150b54403061900c000302c4110495450240041040340b625120090581850f00a851412407810541d10781c44e59a01020345568030406c2e201240da5144d0700304400494144c81410707400860ba002071440d15265510041900035035041080804902a200303e030300307020070400d4108895101400f000820710421002004c0c80810000711406500111500116440801680e010788c02008413001c145046aa440101040080c0740001c00d20f0113050341c01442d82c04004e800c80803041c82d128203603010340601004045000080c00702c20b00311401c100802401e804c40c041c0b502102d804c0f4400140ca1001c0c940042d84a000080d02c90b041840b4004050302402019844002200d50b124803030100900040b13220480340030901c1040300401c00080e0111140c00ba9046035140c0c04146e5104a842d0044000300c407407003c4c16100700703180140e641c1e08050003009165603000845041510040c4001019138000848840766116003410748aa6140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 480257077 1250 480255827 480255851
    0x6080d0315050604061805030102252607020f03061b0d0906021b0d030614010e12010f0c02061b0a110c030d0309021e0306011e0305061602210d 63
    0x3039000180c03000400c004e60f25552440d000b00401d04403080c640040300b4289000510b80340c144220303008601c1e4200c400078491244610b5100c1d40040543c241c60601c00000510300000c514245142031501c040002500c80d425030051250b40d00d44103141038041d500c24011b00091148048501c01d210940008040d0f41d0381c0d0202c50071001d041e59800003010b490011417041464002e020700035406910b08000c070743c2462441c0504400740e40040c41172070301038002418102150351180301411210507002e410382103001c1150400908403600d5124465005a690700071003180c60341400000d4222020300f0040b240074200d003070800c00398451490071500340440b00002040d5000140045200c0d89001010b4900040c4881d4010b8090100c45404038491b640b45065019401341400900041c1d101c041c00900b07590b130130000c95004456200711091800c0d03110090001c0007500410080e4840c0c8552400080c0280360400080d1411000098200000461482450503950414180c650540040001003524008a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 480258327 1250 480257077 480257111
    0x8060a180210020a030f03020901091a120405010506010e010806060a0c05070e0103030e040c030e0703020907030906020f0424020a0807030917010c020c010203090603040f140d0c060f06080d03 84
    0x9400a4008401804a0b602d2a80100742054901d001e0384030320070926415502207040b807040c40182808600f4014040c0f0803503204010020710719510800e01850000f0308a19030b9a011002c41c2c08451680d1250104540d035603015400c0221001c01307007001c541030304296001803100e0040e94250020407150b5040041441010415000100141075841c00d0a507100d00380244140c1d41d21ba0a940114208806015000d10920645101000040c0036040407420b6900704250b204010f00444105500d03640301101180b2148010045181c503070307040607500d600e00341d40c0071244040c541c4001c841c0000380110b00415030b000324607134506c158015005640d51101c0d00d02910130310003981200711902003112802c0c02118055200703511841c0103408079100c510409004a80c1c9128020f00341e900401c1c00d01c08140080c18080c0101c450030b01c140c80300c10401d29a24800351801001c501e40c600028007440d01c5a050081034450360b1440144100188149402c048181d5640c54840c080030040543e5110303031658120100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 480259577 1250 480258327 480258371
    0x50d0b0703060512160b0a200309040204060804020a0504061d07020313060f08010503072102120a0f030e0609060724060f030b1e0403210501030b0f0a0608060a 70
    0x3055a1126800412820365494441e0554117000360354000100b850814001940c0e2800310b29134400c0740f241d00b02d5080c10200c0c0180d400c101032a00c0b003481868015980c3e40083d0028102c280d4800d040d500d09030040001030b04c2e01d5480540a185851401d002c00ba00c90001056094548505411691204034003203155120300d440709889200811408034840c0c1d805000c5042e6194103641e503580c0b59881c1c03010140c5640030751056103698400d81c0600302900801c2d05090300c0c00344c0018140301903114006080da080481e4030b036040b26446c18060101c0304054006030780c00c280d19030039200d01e820300d2a9840461800c1c030a854001d40f4403881c4401c200c0140c03803926004440b005c0b04000038400142d440c12420080c0741c2501044411b29007001c009800d500c1035403481c84010342404406000d64465880c1600c59880d07075103041c9942c090030141c0c03003480308560007014001d41c0b24200c1c614051900080380341404601401c160000c41c204041003000800004d0001d400c0700070360324000351b034581c8444002400002d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 480260827 1250 480259577 480259579
    0x52104090603110f040507020c040c020312150907140d050402040b0a030804090e0a0b07050903100e033018010902030a0623040804060f111b01030605010207050d0b07030605 76
    0x50001c080200720380c06504035072000041d240c41c41d8191042d01000140d8100700c801000681c400012481246400c3c1c20842407100740b401520715100b5181800603a03080201c2e03144a08c12822601108d481c1048a1410303409509443c0c402100f40403151044280e1281521100507180c8800204003990340342c0c0d0100313841d84001885c7e504416928a028015500144580c030340b2a450700360303418000304c0302180360103031164000988810b95852480aa880d03402c114003458142c424000d8111030714040d4400d80300b0100d0514003d545925040c07148541268401c01032980031003500c080040709000c01c05a45401c07a55030084829007010851002d030041241302c001035410301c02c1441d10018412198088080380380a66500c2e410075044000448040d4403d903402002d40b002084100003041c400c82c2008030841c45407a01642021a07498075901c0c20340130a05501304035071080d80d140080d40c3c040c400e4034014402130000e01304003843d00b00090900000c1110142000d00e1603400110741500ca944440d0103090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 480262077 1250 480260827 480260831
    0x5030709230d0f02031204030203070905130b012304140a0b012604150603021008040503091002060a050a0b060406050f0d020f0301080f060105060a0518090106031e02040305210409 79
    0x4181850f000c031660fa80c40680c081c0c00385c58103008054510400312010782c0c0d00500180f00c464607084000c001000024000c2c01c070130340c0c040e1075400000c0b00c20342c070079000f009014040150040303000808885540d401ca9028803461404003000f58a40181d91035503408440d060000501591000059405232100c0300403110110380d2072401ba00b40700c5020031541c001e43c0980904602d0102442d40b40c81240c009010107075100d4100b040c8404003034840e210a60740180700e041940c4c1040c5030000400d042205850a2402503001042040400c10b05407003610303403195621100340290000540030983d43d100e41d006000801400240041c0303420710403401c542c440000030070b04540e01c403441800784039950401c2c080d02140b40601c0d00845101345001078014181c58004280914001038404156040d07408690411034102141281444542d65500c00900070203850300c0100e840c1a003076145011110244400c1daa1b5244140300a102140b400100030312034006120b02c00e20060300d02034100c900b5000d2a4041c020482c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 480263327 1250 480262077 480262099
    0x10e0f0a0b0d060506090d0f0804030812061c02150c070f270203090c01030504060e01060306052e05210a08040303030b220506061605030702100503070923 68
    0x9076240050a40c0815100c04100c096101c50421402d0f201c0c1d4004286d118401c0710841011032001d00000b8452840b0f891802d103469a41d44c3d421110340c1180140003410003284007081581c0c100168508000f0b13008080c06000e5017030641c0010442182a50714201481001c140d020f503200d0200160405841c8580d1a1203110307694200140104040d140a802d1501400d802c5003403083e018000c0d40e0049140c0d4001c0d19000c210340c80110024400100280c5e025520b50b0f0004081d13079021311804001d1400340e03102240302d01c0d100c140854ac02103040c03240018075645034140b0010058801d43d0f10309071041112607040098050030700e030949000d001d003035000e24051004064208814200100202ca1080c0ca0074404c0600590420018012039465040480c401410024092055600503580880000c0c6030509005d4a00562441405400c0e8115102d45c400501722003545070505440d0320808041c0340903859880c20301402080b407440e51103426039416941e59103610b0869080c90805c101500945144114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 480264577 1250 480263327 480263339
    0x11a1e0307210515091203040809040507120203090105071b020a15020115060c02041406030a12141606050a060b0708130312120608010e0c1c0807080316020a0c05010e0f0a 75
    0x2c00340c0d003280a1344910741c20300002d030b00c1c00000c1d28403564010327000700d041038420700600020b080c0040c120000c2210820a09401c800d0602c00703035004880700c400000b654074002d100501070354800d1120b41d402c1905400c2403401681c401983c08140d40d800c90a01c00e80103040301c002d074050402a11403120454260b8404610703164408044c9102c98021142845103240c943d43c0000d1004003550700d42d4050b082041c044012400d80300303411100340c1e22441c001202c1188505c284c001c9030060848920007046e84034921003844060b0140e140c101c9102a010069a40790081d07650107031084d210010000c10001ca00500020710000b0854010b68100301c4010004200c0c2100610f25508800b282d41c0c0725140c68004a200754052156108600701403004103442a9101d0400c445e41e09000100c070245a00103041c04001511345000c1c04455205031211038403400e1003603402002c1a186152003046600ca85d08183c040740c2c0c01d040d200e0807540d00b82049115900403001140568503401082908000d034610b0000d48 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 480265827 1250 480264577 480264613
    0x1e1d07080a0b10060801050d241a0402040803040e0405030415050c06070c11040e0f010f06030201020f12030a05070201020d0c050c010b09090d0e0a08011a1e03072105 73
    0x1441440c00d02c0059803034507070300c807495072680c00740f00001480540140702e2828000b010580340c0d4001d445103002d10080740c40280d003c00c04005100040381d100c024074400180d151218080e0342c00c084400354100740c02c03c0034130b554034000d900c1a00a003000039000710303080c09030600440b409030400710414030aa01110b07801500a600410240420348604c800050440d4400e0140080351030380045140344140c120001c200c013030040740031041d14501403901146400b00003403082c2140e40010301404620140b442c0006410800b088140046030b81000301c14844041c150b0b0f00701d9074025102c52000501c2e45840404a0090061502d80b00388540f40c44a002a084c0e00030003c3c0c00109085030090264013000d10502900600644083c00701d6446880b010002034080d505541840e0801303014080948d40d030b01c0750349003034803441070804c9003071360b08142e10328500e00340ba41c1e00c503140303c0381702002e418480034030404656503404030300c1522000d1401c01500c1140340c40040001c00e030103403c042154010082c40640c101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 480267077 1250 480265827 480265843
    0x130f0309060905090f07030b060405030f07050301110a0f1d06070303050115051206090405010b090408070c0605040302180907170c030705030d0c1106070f030f121e1d0708 75
    0x400d001c0c402c001220b01c0e0200b481c0780700703240c05800c0b60010707140c9080030340281021000c0103500142c02c1c800801c4e41c3d1010050031400b01800340003044160302c3e1600341800c680c0402c820ac0da049004000d0240c2c03194000c0381c0c0e0f517041c00440c6808101c0d40501c003450a203507005800081d40c403102c001a442c090540c150800d605840e40405d0b10304041c500d040094800e07101349444600144220400550749103800b544c201c1d03019002d0070000c1442010040020b0744240201c03402c58600d040407071008184415944800301804290508030300c1c1030704507000034001d201c07120010001d040319200043c0c481003050000c64020541c06800301071903e65248080e07268610080c0403400380c4101100021149800541100210030075100d04168000075114881c2e44050560184d0700203204010b880c0c001180f281541640ca406540d8080c0f1455030b019005204407a0f2418000d040c50929040340b821030520b001d01c01005518010020701e507180317507000ca80d80a4410302c00380c45502034550001303035042d40030031958 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 480268327 1250 480267077 480267089
    0x70215010602101514211504060e060118471021090b04030806010206090a02011409010311040b04052107030210020c090a1e09051005130f0309 63
    0x2000c0702101c0c00e00401c031808584540c645001a80c003140e0620f00b001040c0c6001001c52890712840e405c5c10046c4907140040f100040c04040c100c103030402c414030450b440f81140c942c40b01401f40c02e6035450007100310103804c0700d40a0000816999a052080800400100020041ea03400000070a051548050204076030541004200080a106038212440c04a00078041c40c20151036255000340d004203440901c00030a4100e408403695100e00c10040b405001410303220314466510303e48980307801c00009051403800781a4160036031000d1036040041c1c2e0820030050400015104180c8c40384040c00040300030b403058a001e0004d15000080204d181f51130a40280306890045c1c40c0c070406140007503140c2429001e544890483c5810141c418801403800c4004511038408034412500d006101d14005814014140c91203000c9907980d0361042100e8800b002940058954500c080028191603158140c46040821650f04801d0765000014100750700a00440d000c2078000c071214803180014a400f80403003042e4004c0c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 480269577 1250 480268327 480268331
    0x10f14060a14060d020705071e051813020906190b040e0609150906041103100e070f080423030d021c090203250801020703020a060b090105010206010b0307021501060210 74
    0x10500078400b422490141c400602102d282c00a0020218025086405c0407602401807440000e08141c43d40c810f14400300350071450802c0c2d24581020400d01013513442490301081507003030400046072a080e001c1c04c030094043d48c1c6032003035580e007400140314118002940c80c020345504c030010620404600160054030f808413610340c1c150700e407101005101401151640c1701d04405801030070150030544652070b003109015001065600c0c0960050449400461b000d00c40c0101c102d82c101300d4603450001013500021340d030400c0710020030300e0440245100b10003000a481c2c0300304d000070200e0880039201d4107210460b0712003d072900c810900503400044d50098640150005410f030102d241c6210900c0381c81c1000340e006004101d00e4400074404140080700c0b0404560f140c551300d10001e0005403e00080644a2103a4050621040796140401c00c0b00c1243c01c255000c0d1410130b00501050b600041c2c16810341c1e0000c0c0b4030a442e0782d40e40d4400c91034020001c0e508150381081c540000b860030f8002802e000d00b49145541 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 480270827 1250 480269577 480269579
    0x90106090902030604171c020a030c0509210304030b2401140a1b02100c0204180206040317070c0e1603090c0501051e0a0203040614040303020d0e0102010f14060a 71
    0x91400356041004041c2d03144c0c0140c408980001e0741c5000b80452a54a41c06050406081d0500c0f83d003000801600a22400d8000413101c2ca183d41c076124032040b050f814101582884904004104c2e40359101c030207224104d048040c82e48003414208242c9008560200d00c02c1d1462400d840c0324011803c84240031400e4500da0002201c1643c080c1c0038803212041000c0301c041c2000040101201c24402e01c80c030040c802c10716940c400e03002d030f1654405940301c0d2000303444102110080e84103100407101007294105501c010146014010303600c5008a03000c80ba041015015009800080908948034a0600500350f24071184001690008a407000703100f92007135102c3c04400025000183c040c3c0d80d566000902d8401030361011b02c005d6010708042c001c03a403841c8005031080103100c504502540c0c4292014805680080783c2002142d600c075032510545440d18456030709241c0346940181d070742c5c1d45188451041c024002415521640f0035400020b170915210341c140700c1204a522000d51210301a40e0941c0510349004c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 480272077 1250 480270827 480270839
    0x5041e0603320a030c020f10080717151002070f030506060405060108040f0209100810150f0e010509073f06240c05060c0310050a0b03060d1514090106 66
    0x65008000c510002c05010803402c0c039030781101c41000c500422a4031004030040406542c441900521032190b4649400b541c504020383d0140c58141b40c4902c850f02d03003031000200002c0040100f04a0240041a5021200000d01c0c0005900b80441d0760800c0c112010010400001d20a0006006005400c1541d08110302c0c0c07202d4004666001341150301402d0a90a54911300c01400c0507010b02c0d9101d607415041c1510b15444d10031907810900c141d51058102038484441ba03541715038514050006007051a0700c1c41c7c003545081c103240e405503814132803588203030013180020300300d14001c201c011000307011400101e41550141c50074402075151080e60002c0c43d03240c034581c2148a0300620601040d40c181004138513103941103c145100c48034031b22410341d040044c4a140200042c0013000741c0c0340115520080d01d500c0380745c102d200c0e43d00e160700c5078040c510550070800104503020800301100d80103082a01d4410f40d04a407410b000c981ca40d03048040c1d2a009241502c1c00c42d0f0203020001c018028203004001303200c3c042d0b582c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 480273327 1250 480272077 480272153
    0x6060405090f09010e0d050d0e0a120f0203090604030f030806060310030f05030714070e0a05101e050a090f0f020f0f0309011506050301061112030105041e0603 70
    0x10091540088055002c14440d039191040300f80e00c0081e072400400d4a5519219641c104610715014a020a1011550010b82141c90046042c603805070002007000304115109c8091a10150030010240a41000095242482401120900640900b1203650b03290340303180200440102160035000280e520003c0f9107507242400459001300300b08140345000c0303803e589031800c90a40011381150a84400c01c44075000510f0602d02000d85205180a050410329100542c04110402016040818a04400c000c1c102014201402c140c81c90482071900b5040207819404002c0440e802080d4041000c1e20700260f0120590050368030a03074a1041441654000a4003d080e030140c201d80d10341312a401c3c0000d0315201c41140140da803290300300d4008202c0411190f1400b038602041d406c6840001d20000040c401e00e0b40003043c5141c0f186c5d2060040c0740000d4190302c4206680010b000b058403550301c503c0380310750101c84140381070703a4114650010400f80f0b50340c1c5800102c448102c07580c100450000303680d0f001c15076618 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 480274577 1250 480273327 480273329
    0x604031a1005060901450603020a1704080705060f09161401050306060f13031712011811030a06050406061701050103112506050105040903091206020f0f0d05060604 72
    0x40c0085080540c484c4c0156401561120000101103c4001002140d4280300740031000e11551000070584180d12a82d40078160b880f908004c06040c0108010103540d580902601d2400426407988042619107103000400c0344911380001d0050f205110a10190200030702000f4000d001e0700701140c65075800c5c120200503c003180d101e440c0d01c6d0404034644090030350040d001541e00c000e00400c2e4615051903048180340603008982d4043c0800c100c514188204050141c4100000740100c580501f0030700a520301c024036500500a0304550454800700c0b402d5402903401101011342207207076041e16840e105002d0350050410f48100d51240d03091020004085001e00c1100382003405018030801703583e0030400198080c00c0b0b000e6940790545010132181c4020b048800c455040005a02c0c82da41c951843d9040c82410703100c0c103801c05032040340b8000745800001c1e0000d00400032034541a1404002128904000b00203008403011200d40c1c590001c1c00f080403c5c2c481300104102402e4100800480d210041405a54015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 480275827 1250 480274577 480274579
    0x60e210301141212030405070b090616060b04090605060a060c170306010c06020a05070209090613110a1d0702011b050913240302040e24070c020604031a1005 69
    0x104100501c5045081c100c00c00d030209010b0711000007401240c228901d4401500c031492680b482c08411b020401c041808200010f01d030000700142090350a000144c4280324181845c910b2144048100017044a19044000740800c005d100f08130100d11810290003800088504034030907558900049078540c0141940d41003250000e84030368004c0c00209440c5507681c0042c0109041c004801003400005e40140010070000707038a03940d03054903842d60340f0501c001c060018001c04010780100303003001611b15403000464601900420500a10f514140207c0ca01c501c068001590408007541381648401041951034040c4140e41d000b04a81090a01035044170920a9060000240b0030030001e04149800001183c8544001000094501d07010003050004085000e90b4440c900140d00c041083d031a1520903840460207010240c108040410024101600c002d4402107402d4241c002052005200d0b203400f0b4480342d070141c0420303a910340307a04010015007050002c0d802e0540c0c1e00720014032000c119810440480710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 480277077 1250 480275827 480275893
    0x702040608061302100509061306030b0a0608070f0e12030309100603031728051503030c03030105010305041b03061b0e010c02061c050a090611041a25060e 68
    0xf0158200312100540c028072504218040c4000596550307414001c08544880d00710056826203003d20140a0740c01c1c081e0708901c1030f0710b84a400c118160300401001d920040c585020443c40d8003091098804d10090348825402400d55189000304200010043d0701031060103046a00c0d9000d1200b041c01501d040e80401070024103040d401204107008020019040005007034841040540780410700d0016502c05002d2a104d40ca81c07050118036000315540e04403096058010714136111084420599074803041c801c00c0e04260b900d00004040c842500103800d284282c041c40401032075500d041c9840074100f40710000118118050103d40510b000c0c2c400048003d4060311051503801e0180c003005280d40081501040300e20031600c04407204012413040382c2c4a60804103000629010504001e0100c541c801b000c4074146508100c140151802620404050026800303050b03034501e104101c0e1418100d03c0742da003280603400c6c85900c104110468014001420381001203851003400c00030400b0740c00c0c03400b241440c074900b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 480278327 1250 480277077 480277111
    0xd090c050306010f2304020904090f030806030d081f0f0e1e070f030e101508010f1104090b010c080f1207020c13091403041508091f09050709060b070204060806 70
    0x1100312414680c0c603d00040c4010700300348c11030002c00d042d00d10300e80301100c42c9001e2608060415812080454100310103034014038800e00d1000024140600c040d10070050510251401da6030000448401d0000c0c120000d94800003c1d0399030414541e8013016105d0381d40c1d48240c02c031725651900360403074110703c162101d94503540b115043c00e2003500140401c0f00c160a803070003078642c44c1c0898050303401220802c0c0201e070144c500a0b49030a40c0c840c21202040d617091001ea0510403161040140d0005580a40f580294000703000e4007404010303205804440c0008060110200c4c4001e0107100031009000c000170041c0d4460701541c0c4034107040381c5419500441c5c50340548540780c900c0e07001103641c0c170061a0602ca00328901500118001c02840c0d83c205074000205400d807440280145c2c0c0d4000d4655400250804c0102042c060905201342c510175040c6d02c6036200c0e50340728550802e03c44100403d01c01082c80320b000300046070700c07140e842038954811030069010f00d041905c00a020071001031030500c00c0c400410034003000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 480279577 1250 480278327 480278369
    0x50c01050a1107150609110a180e060907210902180105030d140705030c010b12150103032d020c18040206030a20030a0507110a05070e0703020d090c050306010f 70
    0x30f403480d00b9282e1003169175240c000c210301c80702d441525072401812607501e440744c00d1100010071061490340361100300504510700300003444101c400b032500080122a0b0340362560b1001000c81e070381200015023000c0e4059403010200802c01640c050501240240d949200c41e004003c0100c0c1e00341020302c501c542540c055103010000341d1044100121801c05849500c0c902203403526850310f03680180308810050b075500c03050b010162400c4d0010301d4603030b08064054407426150344008100d400052101600b8000c20304604c40710144402c1d0762240601e1010603c0303c1d0260071840096460145419860040c0759040181d0bd15035005c5000c10310030740d4001e210526544e600301020014080c01141e040800403800081d03a4001005409103200740004c40300010781c0d2030710300c1c0e000380020046005115a40c202c80d100e0008204049980c0045c4d440d26603800c061629010300860007032140d0150b0044551604c07840d10204604070240342c0031500c0440486159988030700c0c0c52a46c43e1790070300c90f596240154055584030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 480280827 1250 480279577 480279593
    0xe010206250c05060c040e060a06020703030f050c0d02071e0e0103020609040b0a0b130f050f1e030d020a11190311010207030213021c020c0a030c050a060c050c01050a1107 75
    0x180d41d10785040c0b0940c54207980d03814a0000c00756507044403010041014007803200090b00c150380c0315000700c58a0450910301300340a500d8480300e00010303003080208440255028060802c17640d24081038400c581a10042e100001d440324247e00a981c1c0c0b80300d602000f90b8020803200d040d80301361185a0003c00c2140d20f1075003040040c0c0d021102080d000398a8801c0899280c2c4e90443d00b40c002c1032000c1c0b03000da0320300d44c24404811460a03608044a03182d4a4902400b85c2e40350510b400c05066425680580700300041000c00310601c11810083d541441b9491001c94055404100e10b459540318140411003817003070608003c60306040b0f80344103020317800301c0340c040000c152482c1406010320f1060058070000c64403900030810502e000203001070590703000074442c4010340e000b1411541c0d007049480114240442140c4480c6c460075540c5025040118521006c0c043c86800c0c001c40404036440074040010100840c0040c1071608000309440c4c695280100090144819000e0071101c9040041c12900d484115520410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 480282077 1250 480280827 480280891
    0x12030203011518080303010f14150703180506030a02070b01081b13140705180108040c1502030c0607080906130812071814030c01110d030504030203280e010206 70
    0x80e000f001a0000507003a07410700045028180790400140164100312000041030b50003042c481c004c400c5030b04c040304100e00f5241910249035061601c84280e442c02c0c0400444460b41e0741115034004000001d000040005500a04d203d40c818041c20f20103070780e601c0029031100c02050751001170058210410031a03103001200d010301c08010740320025449501d1010b2510700300003259003001060b80040e044541203810901c0004c0071301c09103031001a52030555140c0503200b14621403245505524009850018000e0003500e4074001e100381158a14640404001c00c0500306032242c40300c0340070708804925280c409640403014180c0000000d4a0700040c1203040140e004010090b104201e25500d00e0880d04280c51008001016030b040348071f030345420003000c2504100f24089284d042c8401c07038840801091001c86c21404d04c020504000880c3d0303031241070980c11803042c0707402c1007000c480007011481c2d400d21a40708042c070b01170b6950304e4840c01088a00103a07600d51069847d01c0541050f14000555020442201d00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 480283327 1250 480282077 480282107
    0x100c030c030b0901150e0315100e0c0c0d032013030b011a0f0a09050d0507260703020f061c0606122901120e06060f03030f040b07020609120109120302030115 69
    0x504c0311030011908c6800c040041d5600c0d8401410424108100a01044450340103090311408a2a0000b50041c8a5451861089407001d0603118203480c10943d01d180c50aa0440c50164890355590307002c5d600e910321302030b040c0c0001c6903104614000410071075100d2002c03c5241021080c098900b0003040c1005000303400c0400c00c9000c10041c0c480100d02501d0340c200c02810240310702c00801a0504201c0d1075910074908500f5100c9003070360f0070910280007000043d800c00300d0760140c1d0983c0300e02c00d030700011500c41d21130480b6a00b90500285c2000e45800e007182c0c0220100c4105603542c43e2420442000794098400c280c0e540b60048407c40b0b103200210a15824008004d04141030400380c1c421042201e8003030b01c00300c4408070400d4000c4020051582045105140d58074801c0b406035141c06e00351680803d09000700d0082e0452044003107078031406c40d1100c0044840c81c030401014034816078808941503020300100113088407440a0261075150150090099905843c10003440c00030b100034052003100c0114410041e0307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 480284577 1250 480283327 480283333
    0x2010525021807390b04031706100c06060b0a0c0c0501022d0c031603020301062103082d0105030c2d04151401020f06010323100c030c030b0901150e03 66
    0x44d800340064001911485845401071062a1401e800c003d4a41780054841c0250814902c081241703c1c0e4654551501c08103040c10210450402c41c01c1007001400950040412814009030b41c038035050b080310000c3c00c2103108041440d030094a074001241c48190180b90f10081d451417818080f440885848100a004250012900a02c1c01034001915210f0054111584460a00024001e5003000c1c002d0358082d10140c9030ac540c6080348035002500580340b01070003074100000c88004c0749a0210031030051000c144400354106540c2d92900184080e000b00f8854244248240403603403410b410051043d07091000001390312103942d414200e00d00c03641c43ca0064440e501c1903450510420028400440901810251080300140300803440060301d000d01070958001c113980114010800140c0000355020f100d0b200440030202c00700310410051802c41419406280141800041d007260342d4144c1c007030314a1070b03c5542d0a105011003a824080b007003c00f03001d0321540039803130011490300b10f00900142000200180072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 480285827 1250 480284577 480284657
    0xf060307090c0914060909070504231305090a0503040602060a0614010c082208070f060804120c0c03062d09050a17040b0d091a16080402010525021807 66
    0x10f05491f03002c039101d00200d8000f04003030181c41e4203500b050858840801d081d000550780880080c4401e990034800f454010b071524001410f0b18401e0200c50300107075008044903150f40d11088042c0d181c0c0b03011146008030301e25003040005c400c007041c40c0e4a0305140068586d40e5240c2c2d400d880d00c00207a131240380824841d4002007210807180c46401c0705c0d0f6004091800152001c1e030304010000d0303c1c070912a40400c040007590420f1002140105e4410141c110581c1015060124607140c102080f142c4d0b640040c0802d8076008102e250100c040201c0d4000e01c0c0480c14118000ac002060030040301c6421401a11075400030502100003200004041080e800030140d1600b080d80d252082081e681c0002c0c0015460380d107a04e50f03d01049848121105192125502c0164500d0020700a01d00003a0281c044c1040105c42c901082c2964028030444c0c00a08220300c0c424040780707070096150f15008054404901410b030b007080210600c1e003c0500d207401040551303240100728422150088400129802e041154064400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 480287077 1250 480285827 480285829
    0x3050c0c0703060603140606060d02070c270605011404260a12090f03080d020d0b0604230a0303020606060d14010905220308060d1a0f060307090c09140609 68
    0x84560300841c4940300101300d0504610307058401e04000b010800480d4021414030045555001c01d0707074103010f00307100d006803103d18034180400f500c003003513000d06201d118503110010b401c01c0a24103001c24000c000c409125465594004480300074078003a5103100c0c040c09203c180511824000c0141036248031000e2a03002c00e108402180c28110311110444001c2d200d003101c100866000032038000200300381a10303003803118610348880e40b0520a20703070440409075001806041d03061003a40130002008000c3c14064440d611501c00344000c3c9000f224000d4003030340929030b5140903e4500d843d101504c0c2d05502034007840e115801442031075000345040500705c1e07443e448584004201d9a02c514002d01d52108007240c942450004205545240580303031a01801414030707400420340040d03a26070840f40070f0341c041c041c0290a06098100125690010001070360705018040c404248880580c041c0408405440030955943c021504984010000ea030120f50100000c000b2170340c40c0200d821003000080e025503d003e142034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 480288327 1250 480287077 480287083
    0x50d0f021c0f02060f09151e0114040608030f070219080a0b061e10080a0212102105060103112806030b0f010c02040b030a05030409020a030b01091503050c0c 69
    0x90300c100019100404018000d5040120503002080101800d60300c2c1030403085031f51120910b01000c8140c10490300070038600c110f03420314030395100c641c2c5001e2440340d6103e400d20503044e0300390746240d84a54240000415418004012210380384a00140e45140c00f8442d0700780241c04000040085d00e002ca01c1600064400081c051441510b2117480014401d1910300204800c03045101c81d115052452819402c90548580c8001c001c1341c503007400c10091640da11841d4030064460b0007400304841e034a940512810084400ca10720a03a05401c4948100049540c00c44d080c44000c00ba0141075079200500410210310348007032810319080054400c83c1d0641740144e040010803465214a440a0707050301c02003100c10307072510505d884100100c402010100301103000a1440d500a00301034410395131900441c40d01d9608020211206510400f0b0300d0316180d1302c002020003174014645040109044c29802c00c825072203003444c031013552030341d00c125a6801204881140203140003404490401c6041144083c031000030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 480289577 1250 480288327 480288373
    0x10e060d120e0a060512270a0b040501060b09030607030218040c021f060b0f180a0e19020f0301030f0c05042d020306010f0f020309041a0907020a050d0f02 68
    0x41c0e1218030319012542d060001d410300395071140c0c0420005001001003100940e00711a00f02c104442010510422406928240300261800c905c4511401d1600c0e401c0202961801d8800e5000343d0081100c4d5684152011300b9114030360402e40d0540001c0c0000d2000741c02640902000c442e00960482c40300d46d0b90011070100c907a505600c0c7e0140c2d0040c2e4100800546105c0f884801d000b10002c103001103407a0488000b514011225034848400307003c98001c50112124103114807120005154090b00d6980304041450050280c601c42c0303035040c1d003844d402000703001c6000b2107119445074110f030f80c40c5a10316103c0c40c8a84400c6001103c0d0f2000f24030740000c0c42e42c1c0d603005003240410042c3d00d41d440c6414680d00700c0700c1440000042d0040900600030840c05a801c00c8000c9145002400d080c0a140d500c05001c80c210711030390101551040c6808031074110902c0421420301c5107142603600d20a07607110000140e90340c000010004000768000050010200e11461a24807600040d00442d81e0004001d640304400d8540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 480290827 1250 480289577 480289613
    0xa020106051504030618080d0b1c140f010629130803091e0307052206121415061c02040203010305150609070206060d080c06070e0901140108010e060d 66
    0x8103090041c4200303031086c052003004004510945d92020340e00e01c0310900608888401d6a5034070036042c0ca140d202c080e400310505244a6026480c41a80e00c0e140300c103039a0002c0080d40c1c0e48140309007940410014810041a11030465041c5480c0103102000500048400054039982c0c40510041c040c03030031241d9408004d071041c1d0b13001d940c0b00c00150083c80901c000848001107001e011080b911060340b80482c140c2c0030307102d090f6083c0d0010804581c441c42e20f40c039850480070301640390460029201c403240c14203051451003014072070741e824107490003203503600e03060200d04e95605400300c0402d5070340c0713050f01c1002c20f80d8082e00500314031340780960005400c07600240d10680d460b4000910181041c070007041943d40c00441110b4402c050300b42190700a40d5800300801103801040d054000405004000e001d54421801c044110380340c074501810010204042e03001c01c4d5014280701c0002180300c0c144026030003120315041c0c0d1500e100b6842c0804081e110f80d0058009038000c2031100704a000b00b00005036941e80c1c011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 480292077 1250 480290827 480290869
    0xb0a0b070501091b1a03090f03130503060606040b0a03050403020f0d090f090207051b010c0c170607050309100f021303140c01080f040b041a1f0902090a06050a02010605 74
    0x941401d15100c003038001140d4000e004204030b000e1208048a045caa4040c0c08601c0ca0700351130b90b8400b00c2403840c1c4141d51074514820311010400803441c224489140095690680a640d120785420041c404c5601880c0152201e00300b0a1140701e019030311a07485168070a009104442d40d1141e1000b2082c00e10444000104c00903903400e001340842401f40c50140018902c0340011807a0504a445441d25100e0007022040384c8001c1c4640000168811080d89a02641140d0302c2c0d24110b40e41c011a0300c14280b100d00070000c9010f444000307401c10340604142c030b01c40c89504001d400c0d01c0701b0700d08a0703100070718410030071072003090b0b091050720000400400c010000c0c6200f10540c20307280f2000f8200c0f13450515400c51650400c403145040060f410356040c07085801ca0381c0f0219080392030b201c525001c0880160f0150702c0988404100401c00f034180c0c4400302c135000000b4149121011501c8010000c264030450500707940001501004002e800d1094000381400e501c180f00028150b511075000440351100304058201c032407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 480293327 1250 480292077 480292091
    0x7050d0e0735030f030601050304060e0118030e01020a020132040603021b014115040c02010902030d20010e0c0f0105072103021b0d080f07120b0a0b070501 68
    0x6242c0301580d446800240154100401086215020f200c0144114100080400400c081011541240c1c0d01e24214000900070000c5202d40d40024844182043c0c002900d000f4043e031286d4000f2500c0c12000d40c042c2c0d240e1240d4010b4400300b50b0441c21801c11141c5042802d02c095444110100203413014001c02e82d03000d82c2e42c0644e814402206208410b680030941d2502c4802810100004841064682023200c1078100107207900c1c4400404004080c0c5a01f0a038000c0d040000b0403600540c00034105d08200e80411880e51090000c90880b03d0b1118000e41690014103009204c40c010014110582e9880035250701481e04c51001a00399080460300504c141c2c4913240100da0b41c68440201c125003a003e2030180d0902d40c1a48031060640f41162000b40c1100e0f0140704c0f4880607110b40c04a65215510900c107080030181313110381a90302d181c2801e81800081001000c40c80c0b010001c92568042c0c5429a00c240d0881c003203070b42c0c120007401c40c0744407160b10001c40311001a01d2104240601490750240740001040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 480294577 1250 480293327 480293399
    0x50609010603051c0509130612050c040501080102070b0a09081e030610081513020d11070209090a020618030a1e050706021609230f01030c06050307050d0e07 69
    0x1040c02c5001c04d99611051400300d4003d507101c2c1c240ca000030310864a0259240070007141d40010503040d0003080e13000c8001c081d50b505000e80020b90301030f40541924200216030366110b80c2400c0b4001c06d00014008803803040451008070158220000d503e00580c1110f00d84031141420600001178048402e8140d0300100c1042007070716000d440071504420605040c0d0051400070b0200340c541480e036035210721600c1096200040903240754140d841c03403d6280c07020011131090b980144116080b00c076040b0b109102c13240c001041800b020800114a680c060031407410201001021490b80d0f400112880d0188901101000030030b1081c0048000301c070080c444200041d4103030802030700f8120b080c0c0103801954400c5107510020441c000d01340c003c0711252980050540307520140340015840340918460410902014003441000c0b4883c4181281e110300504002940e88007410b40345030001716030520200301e083c80344d034040003090f03040310100d40d41040990340241d0f00c1d11f0005050010705150781c040507455a00803201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 480295827 1250 480294577 480294583
    0x20126100e06040203060a1206110c0a050c0d0506040807061e140612070b0d020412060b01080a1401030b250306060201060e04020d03140c0d0f0f110601050603070c05060901060305 79
    0x1071001d40f01946180f03030480104070480b045102c1c403c04c4e01060444c00051004aa122000200040d1071140d13440a103c00280e507107011f1400141c0c0c05014902050006d858218001c2c266181d0000c0a0003035a80c2c2d5459070080e54102601c15140c41c0d4071f070350603000034040c00120f07010081c1e00c02000181c5545c80812035001d4400040183d4042d111840c440d006a540000b65102180c450180e1165503078141d048d00d0003c1d01403544100014580d40c0b120701c00300074464000400d60b04080c1d9449005990308002503050b0303038121014401c3c100850005001003031540c00b880d50302c48018890340300b0440d044140c2005005800460301d00190b03031220107211281d82030143d080241a00c0e28a4500c508003078000a07408602258001c0610245181c1c81c3e024010070010744a4036500360f8140c03410301c2c011a60140070035484d000203e000801c85d0314180d06540c00744006e003016000e2180204056800c280031700a003680090f00c0701003800b008454080000f103041141e240703e104408008105070b465480d010345 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 480297077 1250 480295827 480295831
    0x60e0f04020906060a0504090608060106180e190e0d080402030d0309020303120a09050a0501050403143a0e031e07120807211a0102010e0703020126100e 67
    0x40a01040000d100c0540c1c2c0e00c00c0c50b5900701d40c08981c9540d88031301000c010358151190b81d004411280c2042000201b40e90b003c5540350480f80103446443d908a00412540b032642414080c6440d82681c84000c40c5001000b482e03190044c21140b400001d240f08414101403401c180d62074600d000480000270003085042c1800220780588203070409201d9084107a0010791603018068807441202d07013960004600940d581c009004c807940000c01d9485a070941d0074040d000c1d10084400b540401c510030704465040244cd0100e0b00f40d15642c003240000d400b54518080440c004180396010000c402000092051059119403040420807000660740c138032090303801214103d591007840e00c3c4d14405010b100003050032040610b401c1299882d048145903a50703c0e00340c4440c11003000c120244518418040c0c422741e529486003114030802104824849658801207003a10b0041c3d15001058111890800055001e80c03c200e0720a8031413513109803c040440d4441080b48001c44900c1c0c00c40100c00e0382003005c03d0b01124655 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 480298327 1250 480297077 480297091
    0x151206090f05070e101d0d020d050a1b030b0a020a021006060f021501030c120c080604060603031706100e0f04090303020702190b0306270a05070f080f01060f02030c03030a060e 77
    0xb550800d030b500c001a1086c900386045030801010760131741c0d1860b541c502c640721030603a50091600c8010b4045003040342c1d4031500d4040071030f030348070380b2509401e034002402041c0c03400c4a41c0b04a207840c0940d2480e1001c1c01079006a140182580301b0424640710b400004e020b114080c0200d80c1c0c8a21140d0944800203181c0ba6001031290b030202d5a1400600225481d500d0700c80c140e0704040925001c6c6d03070062030040c04003020350f400a200f078007801080c8000c00113a0341008003124020b5640c40e524035148007190b070400350283d0703032940c5c0000004080300e0402e00035000300c2c40f030810080900c8401240c90000c1025038a01030402c40002ea070000d00c440851900420340065012441e482c421032909040800032144409008140300302c8000100e1001840c4420240c0070040321510039030654200420084080c050903181c2d640440c13252000035800c135200380c10740361103003040c044c10401076481c0400039200d1004000c14030b0f0860004010116545000304000c60003200e18480c00201d00b40343c55064145208060008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 480299577 1250 480298327 480298339
    0x110a2103020f1812120d050601020c010e01080a09170d0e06040f1709120a0b090c1f0207050901060f080a020901170a0219051909151206090f05070e 65
    0x16180501c804001d890b0032100c071100f09075403030715034000003103c0c03032640060350080d40308200c1031440d244124030103072a051402c07035814405625400016601c0711201030030b4a00040e0050700e56041984a07003a0560000c008040001e4200400e403101340d0785903138041c101e6500c0400040d40a4942c180e44c403c1c810780c054801f000d000c1d40d041030360ba042c2c100000000301500100700b8034850000c202200b000c503455040001c02502007502d0310001241c03103848066054809050250000301a150041030b4840c9051000302922030b014442942c207040036510240c0c800071480f03403100c00300d5076461790103c840c040c20b00c0c0e4580f140000c501d4034004111040017007280d02d09074018048500f0a90f08030094031511082456141115603820035544000d000f090380b0000c00001200004d5055500200102400a4a98008500904c603d40161a00c08940c4903040360b090351040e90150051140310360340e070f980c0350044c4045013040d9645c09aa050b2080c40f10740701840da0740e84083c0545140c000c210f1300301b01a401c0d102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 480300827 1250 480299577 480299587
    0x1606150f03081e1303050a05281b090905211303140f013605030304021302090406060f0f031104091d01020f03040b01090e0a060c110a210302 62
    0x10b6418a8011000d8000c4440700e400701c6a4014104042503800c100103501000b03009503902d080c880d0f0741d1500b04409881350300030312603100703040b1808605100320804902d00c25152240c0c1c07540da00d19270141b058011071131030702105c001081c10011070082c101401d004500030302148240c280400056402030402030750303070300c0c00704007004010390201141f60490341c0000c0c551580c01d542014490138503030b0700c2c1703000306c4594039040403900020120601d40c8103100d400410701b000da584c0c090fa0112102e80301d03d80031345507a1041c00001c0040c80d1100d820001d6411100c0c02508100e0680c0224041e0307101500b041c0041802e44820b40401c030381c025882114014035240034070204107103074420380c0d142c8914080c14505030340300c0201c0098422a004040d511801c003200846d59080308003046e84890308140d40c22070303090081400010304046a03009840302180804050030031a83d0b642c0c0d60b8001003468140ba02c05101004e40411203420050060941450180c17840d04416001e00700c2c0300015247c1190210141b61040c4a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 480302077 1250 480300827 480300833
    0x91a01061403040302011409010509070605040f09020c120c030706050a020a08160224150312030a05180d020f0618071a12070306181406090c1606150f03 67
    0xe0384004100440c51076980d80d48407403c0407409059030381a039500001d034100900c914050154020743c4159000f40c180c56420f500d50204540c03605c500c0c070940540c481d45113070030b02003011a0350003002c0f031410503000c5a0800d28113542c50b20722504006040074003600045201d00c1486440e010b031603409000b00c45c00310301c1c0842801c000740c50b0380b10103402061501c00101070004c41300d000b041000304001880740614100e507500308609241813001c5809440e074070b007200704d690b41c1030400003441e1140c43c1d803411110382541c0d00c0e010140c000381001010b820300d2020140009140a005200b1b5a4500d0090780c042d007038204802c01104e00d0300300054030842c030b00440101d000c08410008240c0304191801b2002114080c81030300c80c00041d60049440c2201480d0190003409121a0564015004c60300c1c0c107581c1c40c2c5075070f089441c00c42c110b41011070240d070102419000110545054a4030680c0401e400e007002e424140149495800602031250441d0034070307030b10b0b84184031b9001d0340140c0d80000d00e60b580d03141407414115a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 480303327 1250 480302077 480302087
    0x81303120510050411031b0a081f09021c050c04080c01030e010b0402030f0f0615030a02070c09020d150807050102120d06030f120f020f060105060d090204050406091a0106 75
    0xc00301030400e5519008107003942ca50b06210300c01480300a209110001c0c180744400013a50080e5a2942c1180700c250b41c6120511508058032500081515940015955509044540e285084406030a0b007840403010a25110b1840504040d0705080d582441c10503c8041c2c8800300c1c2c3d0041c004c02041070051100f0810084001030b040d44108007880c000c07034540488040303207024100030005240e0190000c81040140b0444a4040340b0070710001d0076100f541c0e1200014000d85092100d03a8580410b01000000c40c8060642c0003400b1691017541d0a914842e51122140308030b030032411740007210b03907100c6d1140b850017803460314120003070118100640360345881c000000c0c1d5034841c00c00c12180d1003000440d017513105030503651003840295006580000e201e01070f40b42c9042c254010684500c0852380318a03900101c0703440062403074416011440106504c0c0d09290404c001e40e00645c103400d840c540c5444407180141c459028003070040307220700c501080d8001070780b405e170003000441500329038900d035080010483d00e9840 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 480304577 1250 480303327 480303347
    0x20d0b031c11030f12061c0201020705040b010234170a020f060c010203250509031f06030812100509040c0b1c020315030c0f06090603090f0f0d081303 66
    0x5801c0500c5114201c408841c15405900104d4641c0032020540e40c00015007544410710491044511612110490308811121840c1c1200a8016880b18000303000340d04190740420f40d030607014012a01d135010705115250320300c0030248160070001c3c40c07030486c101e9139460b00840c94003502000c4483e581061021848a82c0ca08103044080d22079240b9071003a05458941d0000c031980d5044a00082d517a030f1038415100c401e442c01d402003000c0c10040e10140c6284140c4280c2c140d07008090002c2c0a071034070451138031586000d41284c000240080366070f4000080010711801c02006202403807400c1d03009a182120520721840b80592206009102641c03c100010350200300c103105994202c18a1a2200e801c1050046584803050401d400188000309003c200300c0d440050482c0118118100d50240b510602401200003512265642104090000034968984680515800a49141224038152002407100d01d8801c1c868a400480d4018000340241d680e44142080e520816900b001919a50140c1e4014035030412 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 480305827 1250 480304577 480304633
    0x1021e06150609060729060319051e071a040807090903020c0907020c0405100f030f08070c0e01060f210903020a0231090512030406060b0a03020d0b03 66
    0x10a15030301d809640d0071040e6a84142d01800264490403580390558201c1941c0a45a1610b903001c41c0c03030394a00e03a240300d01a03c00c0d00064041e00e030008402000c1100000d0280341101c642c021140d416441c0030341a560303031aa405048000740710481c90003520b5072400c45400d4a052002800304414000d44000151b80b0f012204407440c0007a40489504049013412644022181d104c07400e00c0034000d0701517000a0548801c01d0483d010030035504e40c14806001900e240c03046100c2000130342000c001150071f2007103405455010301d03182442e10b41303155240400c3e0301c40f90700310701d2102440c400144440d0703500c00e039156001e11007418007290243c59105490340d202c0691403c010455114042c0c6000c0510900c48002069400340c5002c60b40e5068551501c2c551540c0d586940c2800c1c170030328003860039200311b018080c01140c00c10013400c0820345100700100300d640010015038205441e41400680e41c6c104400504400310070f6680141c55403041c91080c2d06840501c600588264403003403c0825032909600c04400c2405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 480307077 1250 480305827 480305851
    0x327061116060c11040c120e070503102003160f02030903280b0a0606020d0201090b22080705100515030706030c030b0901081b010f05070b040809100c0201021e06 71
    0x101600c1d113401c3e81803010711040d1308181050348122095412030204280360f4103a0001b0f1010006441103541e4500702c500c5401d80c581e02c1007000340e604003601d600c0600011182000c000b480011340d02403080aa0060740c01c510581444000d16010560054218110034003501c0a50728008040703000950395202140c500400394500c0c141803141d90121500b00c600668400090191450403100c06030040040e48920070150182c0188900340c1403040c4107d0030640e41c0060194101d441390002d640d030b02c00340a00c0c1c0000000c0c40d85190000b00d0300800240c04505d11400081c07034492000d00e200344c151800540300100c5107000d00c1a1035400d130340100e03042043c3c51062400003409840020110302a100754000301f0741000900c0e00200785d84501050f84421a10003840c0e94541c00001700044030101e0b074006584000540520148000800c0050101e0b00140500e685504007642c020006903d0140c5d4041080802d1540292004650301400f0009030000c642c05044400030041d502252225001498102951 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 480308327 1250 480307077 480307097
    0x7050a031b02040c081506040605041a13080d0e150a08091009030215010608070507030c03030603170c06100614030604060b0a1101050c130b07032706111606 69
    0x219260030101c01c49400030002e008111354604042c1103188151000704068240d02440c1045060020172282104e2a50381e59a1420b468084840c1c83c17504d60041c03001100000708880050090800e08031b5001e000742001a201c00403100001038040c0030040c010707a0040318419215200c2d040c212040c0d036041d103a9820b02c515140d54500c802803c026042c001500c000e0719040b20102070650002d0810001501841d40c13518503621a201170300c00760000c403040c000143d0300b0403040000070710510140005130301c40c0c14003045982c4c807540c2d200803080148184107400300700030520880304001081995042100418021101c0e401d0500c001d081c04401c0351001c8007964000041400e545031a031004000381640c4400545544071350340010640000f110f9207401719030a10000c02d00c4003100b4001c59158110820705103c0c3c00d0700e070400b400c559400c82d0340c058083c81002076403a405960800f2005448401080c00074a00a0400e10701420480c00d1505c8503000da4024000001446180140441a61030b2418030500d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 480309577 1250 480308327 480308357
    0x1503040b0612070801060302180906161112071b0311061e04080105040b22020405091006060203090a1d06061b191101020303070906270f030b070507050a03 68
    0x1460214050b60700394071501000080c10503065000209980c0f0071161030b950381c01405d840740031450041c0c50405c100d03001540411803140400b041c102c46e0b05c424ac201001c4000f81c00c482581030808124124880850005621080040b50815401704451080b503905e0641c0c115101c000200000a038040d004207070024800304082602c5581169100440c480d296545032951401d5005e0201610200d4840c80e0748404100c82c0c4003208404042803010300038441100c0c215400f0840070f03280c0500940101e00030700b20700c0d00700d40c10b0300e0140c1c0029040c10b800a665940d443c20510100d28410782c4000e900301a00f00b03006143c404807003e010b410000403142d80c3d40f184120451510302c2e00d49031400d0501845001d2051142940d01c2c050b40d050390b806aa0202c02c0720441e0001680c0700e10007110340c5030004200c1101800781c0d40c082d02c1c0300b290300c80c251401c2c805502030003004c901d980d6013150002c40d2062030101041003081118440280d00203250701d131541c100240c0350f070b581d5555210b039540201440038481103030100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 480310827 1250 480309577 480309589
    0x90b0903031b0d0b0d0c03021f0f050703030b0301050906070f0e302505060a0219030e1c050705010507080a0f120f02030f070212070204050c070c0803040f051503040b06 74
    0x2944c4402080340c0040d004625000c40402d6442c0300c00c9000b1400301a29814051a40382d60602d03170845500c41d04800f00c04542d04407010f030b00c000001c505059a82d50444483d4a00b44206485002800018826428000c03806041000450010001c11415030000d02450315450020907800494903c840c80d5400f0310300c915410203107050303035410051040d9140a051228000d842889000e84c580b80303041d0b059283c1003403140e5403264000100150b40008080e0610640026845812501a20306414142ca20302c0000d10700001c00322442d0200d103075100e1418180720052003c000208001d0800d58030f40b150503920358582e4080c0203510400c3c00040c0c021104424043d55200100e0580000704120014a0250040080d00103880789951000202c000a1000340005180d080042c0303000d110341d041551036820071026042c02010065410020b100c1000002d901c0c0f003094002c1c01410001d5500c6505000302548040d405502c094440c00c110310010311303222613407000c0ba90000d81209003010140d0300d45003c51b413 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 480312077 1250 480310827 480310841
    0xd1b1407051509061503030310030201231803070510080f07030e07032004110f0901020a08070305190915030c02011814070f0e01060503040201020a0c0603090b0903031b0d 75
    0x4488102d1074104529a14040341645c401c514040b01c078030100503403006156481c0030440f00c21548182d002024005580610001d40790001000106c0e5102c0102e2002050541c000b10b41c52803448040070030326280c0b4a018407890000d0242900c990034440400c101c028251000945000c00c030103010b00c045806c182c8039400240201412808444460790740740b0303044035000d0400c407695403030080c950130700070481c035040c003032180c0e8030400e02ca0140c200b1001600c118002d6002c401002c1c194400d420354100008e0b40349000e00b0120b401f80d102e4903124107100d0000120748100b505040d0402c4982034042c844050181a0041000d15502e0b0014a80582050503030040c07010043c8012000424584001040b16004e000100140c40c003080d580c0302e81c0c2d10f01420205280c1406102c042d600d021005002d41c0380f0078005980c0c083e00503c1107a60f12109500c40f0020440660172000c0081c0d01e422030343c0140081c0500c55034010319138100661441c5401c0303440070070f10031071020b03810f40240c2c0c0000c00900040d02604030340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 480313327 1250 480312077 480312103
    0x206070b1e0408040510080f0103080f2b0c020d05071b050910140616110612041406010b280519030b0906040908040e040206070c0b0d1b140705 63
    0x110241001d00f48603005400c1442000e1080151540c40400d5900c16031503e400f941164103003008590840d83c1d0f0402d01d8003c00c0003041548000c0c48410a00c400c1003000e002d0002e840740d040d40d071040403211120169022000c41800355030001c441ea0200d05e910100b207922154001b40340e4120200c101000e0b210b8039086512543c3e00c141c80700140b22040c843c80342084115440e841c6d50307825080564051103030314000c01d100000300c1b00d040d40d9040045500e403450303510706c2c960080c0301341e140208680600b0620603040da02503c02c4040800007245540c8200401805054802c0780315081185041645040710b244c819500b04040c4400034121159000303106a82c4c0b01701d580012102501d000c148020001c10020310034912840322440451074070305181c403c0c40c4000e40c0201e0410720700303030070840042a164009401280c010204100010100d9610a101006403080d00c0040742e495940100000070781f01c485000f1210420500c0328880015040012070030340072201541983c0f10701e86402c0090402c080603c1032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 480314577 1250 480313327 480313381
    0x4020309010b0406060f1407060b0a170f0a1e03020106080d050703020712080304080a050c0106030c2d260106151101020f0909061c110a120206070b 65
    0x20101212040d00400310b44042614200410f0741d580c0001c13100000a514840c01141c8001441c48000101100030a4914000c80010903018174800c00b243d6400080d51001e07030001030300089400082810302811419280f00b074010500e00c0c4036a2580103071500c000120f40c011100224220023010b000390815401000440103a40da107160242000d410f5a0000c1401c8005004001001c00c0c840301c1c1c041756044440e0000c82c1c190840d1340380d990340c0110b5400b040780003003070040901181030200002d010350006075100c7c09043c290940303401c8410314a1040e8012181d45200291502c4940d0f9848400c0c400c04c5907409554070307810401442079100403045901402200754201040401c00ea0f9502c500008503c402c1e540e511070035946012824200c0c000c00601d8580c0740c00400130100c1619040ca4104c0d004078008103810140003010b601c0c00041d09606c82e0440d100c0202d00701404103490981c003401c0084c0345d8202440d10400e03041c0c2c000750326442640002002c00c1600c5010560b1203018481e150700c01344070b1030749d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 480315827 1250 480314577 480314581
    0xc0a142b0e01210c0905042318070f030f150b31090b0609070203070b041205040e270106031a100b0a051c0c080402131b030f0c0e0607030806040902040203 68
    0x100505ea003000740111401142007240d100760242d0201300503e042208c025920701941c441e0514000c0c01e10700e18021a100b4440c030440400d0001030392100c840218800c0c14640c8000c032540c60088117100188480901c0c0a14008003036803035440c1c95801050071010000c0312060100c0da07142c0181ea1b0040c1c80c6d1454600d03480e0118020800200109140c094203045421001c1551840780c00ca03520b02c6060401880e0240003000b01e00083c01c0d40d243da000350b03103080c10400e00301a2a4454035a071104212110781c481c9010300601003025413042d245c44074866588000b40300e030504540311000c000812209921034490b004000844007004500558050302e07011000c10760312003004034020410703080785416020b247c6e410b200c6a59030b5504c1c3d01c02c0c056130003115181d5048030380d565020403d03104040400c61201c01d03181d12144070880d42c0b03000c0ca410102c51544000400950f02030804003103800c151200703c00d009030707640c0702001070f40d9190554440300c2c1d140c9816896a40c0706004140035000024000350003500100c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 480317077 1250 480315827 480315851
    0x304080f100605091306200c0c0906060a050f09030f15010e33030f0102030a09031106151201020c03121f0312050c0a142b0e0121 57
    0x41c61a01c191080a030500030325454a0030859044410303181c1d00e2028500e0041880080d440d43c1140e80024080e2040c06200d0100c0d402607007a07540030703000044d0320f0303004415020450701d030034010796030071800075142d480c140200781c41c1c0a04140b0503480d07140c0104a02081100c0150f60810608103010b02c00300543d5404000402d8510001b03200b8003030021440418000656244102c804d041a020907410a005400c0c40203480b044c4503151b009060b981602420f5500c0314600002d0000f18010045048001560070490178014100814448d5a061a80112040c0485901c02034220a0005001c40d00010010108040240240310700151840b59000100d60365030016000d501c428402d10060072260200038503031110030442405400000c119480fa00010310342144914041c01e134641484080310101006500d440d003080e0300e69011006158032050614038502035100d106c0e2040035101800b44910983d0ba100a044074401c506258100300084264020700d88480c0501414240248410060490201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 480318327 1250 480317077 480317083
    0x504050c0f0a05120f0f0c011b030215040506090f0312010e0c04090903030b130209031002030c04600525061803020c040213031401020309010501060804020303030601110304080f 78
    0xc170b6601d01942c070408070f0b00440800c00c8005490140d4505480341c402e2900c81840500f0001c0c15021841602e400344002c5800804031405280507100400d4545002c800355482c0041d000e11500043d0000c3c409480181205214a03055414100340000107030740d500c80b05145401294020000b40b820300a50344103042c3c059100d03c041c150141c852801c02c1103a107007006c2c1684500141950541e00400d00a644070810780c1c055504486023204941c070b0079a5031030420560040c2560340316800004d130b5610800740300e82078151100c02000b890407110600100c424001e0442114824682c83d010746442600c80b542c8281d0840b00c09070f40c6102e0203480284543c2500d0024102000100c031703002d140c441ca889800e81000c60072511960b041d4010102020080107100180d08134800d4040150f5808001000040404034602c0c0d1800301200016240c0c9071500c0b4076400c1d910182c0c4007900b400240401c1c031015031004001c80b40c0c00f0f0002e007010070b03c07211968001032a502c0f03594020007050180c0307250360512030004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 480319577 1250 480318327 480318343
    0x30212191803081f090906050604060f03050a060903023904150b160606030b07120b0d02010e280512060c0403031d03010f020c100504050c0f0a0512 65
    0x4400200510420001045102101504050041480b010004030203010b0202414070441c00101c0e11040941c5d01e162220503100002011502c5686840800c01103081030302c41c600040c8014104404200e1035510303881c0d01d440090001411b2030307172100540b0090500800c9950007040d030000408024030f42c0310300001c0c2d060051121724030341000c00c1d030035114681ca401c1c040d1100d034560030b40040c4580742c0303418070355442640054548080724110a2480c4049122403041100460041c0203070901d038034045400400800000d0b1104500e54649800e0072880d84480c4000d120705582820700324100b0300300000241407141003081507120704426100a050031000c0302200d0080722010380d902c54254040180e8580c6078907085420b2680f4100912040000c01d04c107120320102c092613600601900194100070900359001d01100140054000a0102044804004500d445d00b5008401c1210342010380c0e90380e4848282c0c030242c03442905003031002c02d4a0740d6141c1004004040040c01c0360b0009006044041c0c0710500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 480320827 1250 480319577 480319621
    0xe013204090b030a0b060f030c060a020102190903050a03030f090b0108100e1c05030c0c060f1b0901020d0e1507060b03070806070e0405040311100f050c0909011401030212 75
    0x40c5001040142400100c048130958054000b008981e1740c2810b110035054880d00c0503034144210b1800c3c040a8503600010310013403040e07600250780c4181c0951000007084501500d5002c100d43e603241040880e80200d6a01c0700c05a06140200b529402c02c03088002030210500090410000000001041c202c00140034000f00c05012007402080f20300701e00a074442c02c410030800100c00f064205825075520800040d94090240c001403800c10350398090b094070303180d412161100c149103100305100c1c040e201d4080d8449945144403481c0c0c0344c11107060000b5221154940104213112a001c0c1950496070b8501d1924840144881c8454513616503090143c090000f151016002e406030701c034045140072010859038807614180c0c90750748044030307000148001000024800d5007000000600c404e0010002d1242c1400c0c900b61141c0400d000d0011354116044031005030a260b09408200440c88094442038000c0d07044802c0070316034100341c1290800580181c40b50196142035910007901700110141c090555102c2401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 480322077 1250 480320827 480320831
    0x1802091c1203020906030121050a2d12110708010e1506060c15250e12010218060f0f040f15080606071b0806010803120f010302010e01320409 62
    0x510380003079040740b0a0718041034011004100500030100003030b07115142c0c03008c81158001010001d441d91414011200401c03036000c0d1010594006802a40c0d0000d43c168001640500e0321041a0b502c0c1244c0c100341407005010300c0488054010841d0050000000520303114000f80410001005080d0300d0764240154041008602000314039030b410100d05a03840c84103041c0003130a0310410b86600d90a00d402c0180745042030304900429480c1250907444843c406059074452a4440040504004400c14040302a100d00d0384180480c1c800b00844032004214000b0541c3e0f5140e88141d00402802288100820b07410300300c0001800150080040901c04211048420206082c90040100711482081618142c0c1d100b50184000700c00b04580640c280c03a450103200a00425560341d02101c1c1c01e0200036401800d0036040429a01c403a0102c15501552269003c40030018940c1903034006030140101c006a141048400d442c441114843c6200c039014250843c8100c2c81085015242001964840d00071740b0a898 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 480323327 1250 480322077 480322103
    0x2070501081305060106120e0a030503150907091e2d0905040302070501050913060806160e030604030c0c090f020403120509010e060d02040e0f01050a050a0f1802091c 73
    0xc0b0481c0382c8010640c020040c2c04e880e40782481c1151401c00c08144110034a07590381c03865103400810001843d60610035125244c992610700c01c0184000d0b000f03a0414064621a010000c40380d41c052519816101a04458070791030401c0c4900b007012a07501d0b00505280c1c2001030481070304111450000852020072201c61005e1a214a620010b0301c00c140d8005001d03074003851042c4100d40c0160007524500380d0240c5100b183c03c3d09840e996080d900181d0110f0362640041003842b0500d00444044200d443e000d040080204209801013641c8d80170040014081164000007007003000300c50b800c800014440f090342030106510322100c4100a5005210466504060045c0c0907a02400741040d1810204d050b1281c0440c000c2c40001c1c0030700c80d440b450388040015403c1101007140c96805404074003130403410303400d003030301e98105000d00c00c401c1c03402c0e040244150109203007009000c900844d4130050b81e200d9900b06001c44101c03900b82d400b078065909819807150303030380d010703111040b40700c6050075040c60180f500100c5c44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 480324577 1250 480323327 480323341
    0x5030c010b12162106020a0c1e0321020c12030106030c080c070204150503010207110406060206011a0d061d04030201051510030b030a08030f070f050f07140c0406060207050108 77
    0x703000085100e0100f5035074403000c101a80c280d00951142018141c20180101031998a00049074802009080460400c00881e010f00501411103182e9090349402d80c54424102d0700d000e01880d2010341030841d12100124640070200c503d405584001c0d00ba83c01721520100070040c1e4100742d030024056440000d02d0003000c500c00622403510f49000340355800d1050701e843da542e0240320151440070394000d45880761060002c0c0135217091004194060090000000011460342000180c495580c440ba045500000c0107121103260510b0304660300184240c6035685600190b400720240c87c0320380c05903c0b07214034074094011270f903070214295108500c654001c01a80c3d035030340c1c0d00e04002200b40c2d075416002604e0040b0040180d00992110150000050440c0c0b4801d503a95a0b90361303187d00880d802424518190103100e04240c1000c0403111414050030000d042c0f032103600320b0740700318000c801020703150041c1901144501041031150070340800c405402403061640320307800a543c81b09603224032400542e1400000700c103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 480325827 1250 480324577 480324583
    0x5061309050f191a1306030506090705030709020307020d20030415170c0a0507031e0519020303040b1b07141608070b0f03311a041208090a05030c010b12 67
    0x134003940000c40251055400c07040c040c1001d4640c40c850f02d419680c46001c8086401000030b0351081c000d00d4001d1140706e08240c05d060400d03c0541c01010810300500610901da41c000c5680e2200880c6864403082d0099211030b12928250403104000083c00700150114910704644c018445091003904e54036485500c1c4000300161400840d100e40b66541d050000440c800e1146004200030360081c909074116414041c080c500201340200e514010520009003c050030148669031031240e01b00340040d40c214038240e00d40f40790810300141200c0340c5103c4030000311030b104011400d80d240d054110000c0e5032144a035000c02982d4418003010f55015022101000480b080e00166980c01d0790a102402c508001100c54001442d42010b00800c1101c110340400c00104c4080260b0007000c00800640c0403003100c035030b003451064040c492452440c060000c100300404140d00804181001055281051135659441c503228242800b02030010980d001c005419043c009054000c4410701e0011903d1582041441008540d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 480327077 1250 480325827 480325841
    0x30f0b03030a020d030b01231201150804110126040b0903091e011b0305070b07081302151c0509010e0a0507140d060603080d05091605061309050f19 65
    0x1005a004d109135982991180d00b050060305018140901035401c014000b00070180d040d88400a80b65001c81c0d19070910768500d0000b8014030815140c6452404c000c030780100f40e4400200098034018004c0d41d03480c0240d110b0100c03042c01601007445500c54400019000d51248019a0155040c21600002c50604800401141e0700c401004024110000e140114209a05d62800515051001c0803171158410526249080e60040c480e5440303940c1d0b0515031070a0740c5401c41c05881c9d60200b1510384108100009042d0f00c900b00035404943c140d10110491000041501c40c0e04070702c4a10070780c0c0b10f81c1c0014041c0b0340e800803801101e0b01c02c000d0069680c0100c4180d500c0741108400f9105500c14541080300340f00c0062220048813016011041c030b01d1103038882c542980c11561044401601c0024a8054103c0701d00c07a1941060050f0003800d03d208500c811200140800d02034503104110006220100301d46119842c002405445818802032520642c0c0d403a595104443c1714100d504400380103282c85103284a080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 480328327 1250 480327077 480327097
    0x2070b0c15091b0a15030b03150415231f08010606030606030b030102120f10080a080301050102010b01080c0315040f1503020306010e0c0d09050c2e08040c09020a020709020a030f0b0303 81
    0x1000d0b0645c0c10101c0290000350205600360041050b84070f4041c1645086510482c040c1c116105494820034082c42100d040300b4118542999101071120368140b0304c9222604209006070f2a41a003400b8044922412080c4e40901855840c0000010360240c060300508101e031815101000914640810305090740714840c400c0d0380b011020800102c02c01c072085144e0b5000100d0080707107191240c60b55211131030301c0c030981c4080e00e0800700400100510342c0d090040060082082c81c01c42418240000740000350f001c060710b2601581080e9002c600d1036251a408520280180c01e8148218070704a00f102c40c0c1c40415000c2030b80a805100008540500e100110070300821400c1e8203207151a0054070b4030320003000c10b014202c40c1800388494905084d030710f402205105203a4906810440b114014110740074120503503010701031206540400c004101c00d904440b088402011000d42c1d5004002c008904002080c2c20410280344046240500350f603065029080444055004100c0d565088080650b2030040b40600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 480329577 1250 480328327 480328349
    0x3040f03022205010603052d1602010902090f010f050d081c021b0709050106020c0609090402031218030118050c0f011404030308040203120a02070b0c15091b0a 70
    0x400050600d440034039820119458044a02d00d154202c0c90706560b02a400301001030307100c2013030265400c6004010b07030401c40300320020a4034416103500c08040181c02000881f0302c0d02482070490456001790400004154000c01c00380042c9003104542d28001000e01440744502d200c14000b144600342020301c10364064100c00b0751828280c1c00025800d80c15002e480345880c440d0240003481da01c07008418107009521020307000e00071160030400c21204455050303012008640c0080407816490700d1740811184070354826202c2c0f0034140d0355400441e00e0310f003610182003403806e00003c0766205000001501c01020208400901c54001004044910001981c002400716004480d00c240c407403510031302c2c080b84584181002c4021030301803505d1030480d03003082d03000b03802241d201c5040008600d0284160765110100071105402e04195010003507803101107000b440407024000402c4200c481040000c00c80070b02d404601404a03186c840440d6031034002d80545403007030155040502c0d85600d0014110002c2d103402944c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 480330827 1250 480329577 480329579
    0x52d040908030a0f02040f030303022119050a140711010e070302090f0901150906050f04020f1e070507170c0a0e0c070f051b090903030f01030605061810080f03040f 72
    0xd10008142421138800d94035401c00000510040c03400b6901d000754025200144c60b0380000e0500d580460f02e91040011800424041003081d002e21001002441d0028800040d00ea0b180c0c08100010444242a40041d07000d2404100040d90321101c684440764001c40280140040030f50080e0351440c85000082d070044140c0c00050705008070030781241e8454807420001c6210880c0580c800c200101d95040400c00f00c0e1a40002d0110342809241d00c140e0b0501540e08500c1d24a00c544920140e014035410700700482e444079070900e81884120309807900303c0d0b040000c0d125910f84d1031a0761488800e080035810814000c4190703d400918044080c00100c48082074490100e03030764015a1070040c0c0c4400e0044846500c012907890203d0b10400c034102281e0351641c22015103034443c0c00ac20800244c0140004003952040041040740c44c0c0c40083c0d18116980210301103080e840e03000002d23000010341403444660714880c000300158000381d18440f03000c5a082c10113a4021221402c481a102d01c52401503004203225214 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 480332077 1250 480330827 480330841
    0xf0c0e06060306042406020303070e060405030c0409170c0d080f04032708060f0709081204030618140d1206030f08030601050c030a0c150204050108070e0a052d04090803 74
    0x404900c40d85001c40000071417103d14462a90170040c0c01c60030050340080100407100d50807007110000720004171f40c01400e00d440c000000e85c0d2840c06140050007562100085810405070588000d64010f00208280c5c031001c41d0350f2030750358076a10200400005145032006c641c0319204556418012601940c0d500c5003074202410485040710348030160b60b4540d140358000240348009102003405595404000707e01c90626020060000d8042c0c2c00044094125242507414076a40c441120304aa9100c50003007011880c594840003440155013001d0300b0b10342c000188045000c0041201000007446481c0c04251940d000c1300b190488445000051440601d5080d800c04110200c002e19030041c0d05240040c0340a600071101421500842c01c2d41000c1199103c480c0104a0501e01d00c0740715424906046050902e00340000341a01c0018000009010211040b100035854800499002d4000a8602d00141d0000c0e4580c0300c2011542034070308461031350f01c2c0755071003649890b009182e10107800c0f04840d411350701d40007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 480333327 1250 480332077 480332081
    0x14190f1a2217120105041a060d0c12020a050901201b030109060c090e010e100b16020a0f05120a05070b0c0703050715030c02060f0a0908070f0f0c0e0606030604 70
    0xd102600c461204142c0548442210402000144003282c205005945090140800d4914040d8160a280700041e042c5200c0d45800007514003000c01c104010801640d50b06065460052410310300c0040d50001a0a060860700b220042070032a0081e603480d210f200700542003a0b44500c0e1050900c0d920342001740500f100c259420705181d424240140001001c808954030312048800004080b00810800e0303400300a101002500c441c01850664020402c2d8078082c5e005181400003030160074100714001c580008040210410103105540c00340c0750303c491a84419581d4104a140e05c1141d11811203038080302e2403040041035406007140e10400500743c140c24414454240c0e042045851503500c110b12000000c10410026030000300b01400380828003512003140101540c21200d006405d56204c441406440c0f40d9903103240743d20000716040015840c1c61846c040003a03216086010b000c4460210611082c002e40d802030002143c410f00c024440b10b0344c0e03600c02c5040c0700780444a855100906200060b420b003025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 480334577 1250 480333327 480333391
    0x2010306050d0f0218071b150f0204080d1404060e1909050403080606340507150905100804020405060a15170601020111030414190f1a 59
    0x50402051064640001c600c0100200c40141c448030340900e6581c0031350812086801001c07084260b0103585262511002c2e2142000c0311a1180c50000804860144440358a0850328000500d20900c0300250b07000c5500007075003003400703071984c1c42c0502314000303c209008010b0803960a480340a552b04003485e0641c10384208002c0e03048550081e0101001c0c0940d001000401d07809082e107550001078134141818002c00d40e9030028559400307600e0803c00c0400007a12181c41e040000d0710803280c0101201214110000e102c58120010440e2052803000300e1000a42c00c001c80007840e5540d1601d961035501e41c01c0010340c0310a103113a200450b5511003c02c0141c00c06421103640500e01400400c525a07982094403040308041d1a4030700043d0235024105507802160100c0c1c1d0700410700340300911070903c001a480c0c00d544400f4000600311940c031203c800c400b030420322007e1041c500c0d00002c000c0c03640c0c0e90700308030020000c0d480c0e04890f030703803110b107108100041c0300411207010f00c0082804001500400c2c07041a424455 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 480335827 1250 480334577 480334579
    0x31d070810050a061205010905011406062a0d0801141005190912050c1203030702100e07091805060f10120312110d060503030903061303030b150406080609100b0702 72
    0x2502400700d005d054180c81c1c198aa8460000016075000030b0401c02d0071120381c694000c03980b03a262410301c00f19a55a40540e1034162500c1d090000c601200300e07d600c040c0390601c0ca0030b01c50b40200000603440d51f4100c001d260489030058100820700d8900d2080004050301300ea08140855024040d9070744d030b50004412030859100c0780c1005210140c8480ca031004189140604844540c40829180c0c030741c0c2440150000011206001942903040a2102035201c00c5001c0340122600d82d201100501c40000300710a0380281030003d4100502d2060200303000d010f4080b02c4003507a0341d110f04002b0484e945040d9071074503c01c1030380c00740014000741051a00158850505001e80400140c00d114a007511020703c9040180104c001c001951b4408007030005003590080d138492803207500140403040c07440d203011a103564492401c6401010114a03442c090b8020b00e00851030940001ca1004504007000e02d00b4001c00698159490f95403299544000308681780a04503106005070860300401c1242c2d6a420001d0719000b44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 480337077 1250 480335827 480335831
    0x4170304031703150a0b0a050706090b01030614090a030906050313052b03060506070201030509030c070603050411100909050c0d05040c0f0b03040305030103081b01020307031d070810050a 82
    0x66251544050804414007945070302d080001845051104102807070714801040c0c501c032160303d19141c000790490140501c1c000c03c2c080001104401c0180c0c07a0300100c1690350081c2a0041540c49080c684c0041c25802d1101400000c00d0000c54481d100002e44c4c192407a505994200c512403d2603000c40b460381014000990b00ca951541c0c500004005200744801c00f003440503018146c0c15018500ca15910602c24164180f502e803050602c6a0313124101285c0180f502801d003c95181c43e0508090f242d0711072040b403041107029180000c10b506516801460103140101c102e0002040820704104140c5d280418401c0132600c070250812000446803c095400281d003440346081100c2c2280d0202590b07022a8111110412048140050040750141074003a0550413001070851404e40d43c00b50040c441800003600c0940d02107a05a0b0b16111141a0303001590b072200290341303038101840081e019011304074448043c0c211580d45410b01301c000103a81ca0480d803445005003101c10f13407200c0c0d40e40140390251507895029 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 480338327 1250 480337077 480337079
    0x12030f07230d0c0e0103061d04030e1804151a0907030219080117070819050115140301050c0901020a020d11030f0a140601031104021602120f12030c04170304 69
    0x2651140140c6248460300c0c1000c0f5481100700c4000302424080b00203e4180f40c0340c402d06000c0705806500d8400881414607205c0781c0c60716142000d880c1c010030b402180e54082000c200b50451018400c1149000c4e6100700d500944c082c92510040060303403440051240200d031081c2001815150110a040c0c10403140c0c100140b518060984800c4041c10b42c2010b44003044402004010003280d90164250403110031000d410300601b8400302c1c903240c0c0405201150582c00410303c20043c89401c2d4014283d00e440d80d1104a105552481c80c201c030340f81d80c042d5042c440e518000c00a8640352031807003214413210f4140e01034021a5100d07400c11800ca417007020150b03100001c418142c51107890810070400c800c4003007c010400d140703151500007000192610020074580100780104001740c512103001c4005013084a0143e1540100105071840301d0030000c029600c498034865518103404081070101702e0001d044140d034145200c0000c440034601c419078480c42c0f4088100020040c01d241c0c60f002e01100c05100058a00d05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 480339577 1250 480338327 480338387
    0xc09012115080f0f06010807032a15030c0e030607120207050d050306190e04140c0904150e030711060912010f1406100906080a061706040512030f07 65
    0x60301598000c250b0943c0310920014198a003000b82e941e1800c0e095004008035810860810340790001c0388001403800204200a2041c0750240d00c0160580c141d46640022a80da06e400d07105210301d4003c50840407918002c1d40c0c441c1c162042c0311080c103080c40030b030041130251a25081110540141c900e00020785a0910111002880510140010541a0303a65a407a820110f007040481c07811914074440d40400744000b001010381c2c012074164043c1e0881a103981b00440074003d281450000625641e0020f034240400c01040284500d035003108060090401050340640242582ea10416501525402030101c1c0c0407003a15108004084440010f4081070796a1181c5000e94290381e40140b140804035142c14240d1a11190042c4403a44481c3c01c444c03080c0304140601002d028415940200e904005c03000c3c0020307216403c0340c4c00004c000c041100501c0e00d80140100340644602040e6822156402010700e1194503564031800d40c0d00528804400e00c14544543c0426200704050b8810b0100e01251a45420741d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 480340827 1250 480339577 480339611
    0x1a0d03300608032503021b01110a0c091a0a09022203140d0309020d030305180d0513080d0f0c0515010311030c040219032a05120c090121 60
    0x100305081c021620385490600000010395130360000000001944002008254001855038404c034503840d1003886140400c0048a11200c3d51040c00c3d400d21401c00039404101001c0020421600449402c00c084907507841c98484000410084542c86548007805000441c16a8010b241c0400d20003000d1180c1c1450f40d80b50240e03401181e106440590150260311420641030105041241491908100074074403a400101c1c502c51119014003015030320800180c8042844901c020003002c00012180d80648280000b49664000d140b0704091010714030000984400008540b400082c0a44410350712401d00b200498500c2da800b8402e03241440f83e180800001c1d4080c040242c00381d0702035020301c004030740c3e1071050615200c1b00d54012341c001ca00c100321401d500c290200d5000f501491a00e004203529101807880d201d202032108003040001014800e01c05c403250008014144000c480544981d26a00c0c030705010a0750042e01c6400340440c9201d081212200c4200080c47c0401d0b100c440005140500c80082c810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 480342077 1250 480340827 480340829
    0xc102310030b0708071101110406120902060f0a120513080c0304050904060b011d1e120d0305041a0108100e0f100b030c09010810020318030307031a0d033006 69
    0x400701d561401486805031b80203601c46080103822001303002410080400035610300c103d1051208110910b01c051020090315081950f4041e0010440d50711005030b0080c104456201d00010300c04206050300442c80207045005261080c0c00c9011148000c240b03d440d180202d80c080e0018140f035001c01c2001141542d0303000700c0d040c02140a031000058601a10300094440403c45030203151060b4405d1150442e42c1c2c80350800441d2a0580350982c44526400002c520302000f800040c4610b4000d400301c043c2c4ca07661513440103100e64051146048041d0258402035180c0f4020b00815059802510f0000f0861506070000542038100904454400d00c42503042810400e110004165881e101e15013420385250412a11154840454140d02254507200801c0e80d02c2140c00b02e0301d90702c01e8000c000909a00c04925500040001074030030b50b03a5a2902000040c005c140c2c2c4904a03042820040008010f0704040c203000320380d2075042d100d0365075905046c480f0f822a00840d03804007402942195408170b551040c6e001d118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 480343327 1250 480342077 480342091
    0x403051b01090b131403070302040f020309010b09040b130c0302091602010b1002250b040b0715092f0d0c0e090d0801060309020f060f0c102310030b 65
    0x506103034503160004003802c44941c40402d1810050080d400000141c4c02001d04503540b003940081c2e250f03013800110b8100001548081d61252906415002c0944c103600190b10481ca460020000120031104110900e0b0b420385018100c01580d200050054003604540581d0a02850517546429507035400104a2030003142d02c05c02d20f030381c03075207202d00403980900906030364480480b04840d103d030007150025902c16910b040f10103030b41c0001d00310290780440751100720041c0038a10321441d81d40f130f00c481e8007012a901004088500002d040403100420002d03224100181d0380c80511502540c0007021101140c01066081040042a1480a6555031707141e6424160044c0308000e484101031400700c1c0140b5130700e4010007480305500000a402c0c44954041203050540e00182800500c1100302d00204590400d09000380707400510025050b09100740c54000342210a00300e000312240703410300f034261100f0340c1c82d06102140d82c0a251201040c4a5020303070029075010901610518010b40da0703868800741031605807110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 480344577 1250 480343327 480343363
    0x6020706050d0f06081b091e0c0903070303090e0604060f050910080105070f08090d021203150a030c0302240406120906050a0c08070804320d09260307020d0305040305 73
    0x1800c1c1c2440c41240d0b45034040d43c1100c00440c00c8c43c12607031030381c0021000114003804c408410001045814004281e40d6101005004c030f4905980300d20300034104041c240141051700042100140c0146400e000b00d5043d0303407410fa10381400c1072030300c0144048108003602181142030343e104d010882c480d09200d094032449407030355020656000c01c503020703020b60130280000101d0b807c5401e00341c1080d070b00092074404500104414981d681d41d4005e6401c0d003220641140d40e0702c915541c01c00014882d20982a8081c0e900880d4001c0c0c0001c510580008400719071401c0c0c604188040c0030801200340140c1417480c145034541004034001e2050b648880841d01c0403100f4403c41c1d9a02d036000b038511544810800d0340445107040450361070030a40c8400312840e01c02024580c1d800074504074040c42194003404c04c14551505021030f00302010404000d444490903020341d01c00c0b01050f800e103841141c24038050304020308128010350724284040e000d0281041c8599003d80c00d007c17041100100084040003820780e10000c02105c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 480345827 1250 480344577 480344593
    0x70204050a1b0e0612220503190804020d14030d090c14010503070512070507050d020705010305060301090b040602030a2712111507120e010b041506020706050d0f0608 73
    0x1814030491281044042240c442031502080c0c46000c00c40d00309000c001c1c1e13407099595402ca48506d080d81c0d032280742c203078100c3c007016010304005002000d0700740030a04074005100d600300021301303c505030021500130358441d0702441680d000c58010302c14451a01395000c1035a20342444198008240c83c0082c4084400050102c1c0812102c803200388511a170440901c0c1c801c0c0746050100c8000c00f14051680d0103040400c0740004250500d000d0001c03a00d02d558050260340c0020301404005c0c0d11510306213b21400719090030001042460103200b4403401d03d9018903003840e41d442e15141d10009400042040c041555aa0004d051003d40c200d2810791004002940701c040020b1072424554003011403014205100745100604440c0388041a14103488001c40703000700d2144c1d100c0c10203c5618034501507504840f882c1c0701840300da810041d0000304caa90700903503040c4104803400d20084401c8010703201ea100103070040380f400e1101c0c601c80c0d0014001d000b400368011410100a50b400c200b201c015510030f07055684044c3d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 480347077 1250 480345827 480345851
    0x60a0905030705040902010504140102031c0c03240308180319060c03110304080918131a0403080c13050303040b0403060e010b030606040b0102010204030c0b090a080304150e0105070204050a 83
    0xb0b000c040c000035202031205054a500180240c02240144511803140f200412016403080090340ca030041074140410021044a00500060140380607100010b810008a02c00c408404100c40e0300410141e4038113426145140c88034412908040c1011441c4c0440310540b004a0b0740030052a0f0422442c0510501113090501e000380848041c0466a010700d400d0a44d6007012201c20010349034007503005080960344e0208000081d80143c450740010003014402d0701842440c031440e0490b92503040c400c59922850302422500707403440070001c07100200022032520004020301407880203001400c0c152a0340307940290315500041e06540040e00711007423041c0041010000c2c0714030703401031107048603110000b080890f0038080400d4442e030f002403070b09004540301e402054640c0d1003541110011034021081390841900e03200c01c2202d5a100301e1f81c8900c901400700011843c0c1002108450442d4107410a00c1039000001d0b000f62030380640e00c8111810701c50300b80802c07000740c0c0322809400d2103091050030010342d10313280390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 480348327 1250 480347077 480347083
    0xe121305030d0314160903080306130501030605150913030f0c050a0506060f040c0c03030c09050312090906100f0c17030f061518061b030f09011d03190302030405060a090503 76
    0x10044040d11100c100c411030040e4000c0c1d005011fa0313030407030f8640303031b89586100201d8840e00c010041880510f10745000013090200e0396000074059100c142c1484850039005c010400e11400c103440311503040070600d81c1c18001030300902201203a5016402c0c0b00103008247e888840c1403450f400c5003565160007500410215240c044905852200116070030450307101c0c81310000389403820000d0010b051540d1070420020070b501841d0360000801c4d000b0120707214181d000c2e01c1900c40c4d4004030b150300c0c0a60605800301d902c519012624030518a6655211344000e0846035044a200b041d404069985080100b40810030150705401588980040040410b1604040040c00300b1512240c2c4415006034040c07040e007640c403c0881c0b01032500442103c1d83c5888100b00041c0d0103842c001024164000d1100041426a50340c0748800342208110980703c0c03540204512160110001458541c503600da04100c0401403580b02080c13003004818020b1048908054442010a106501c014016000705000390300401041c6010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 480349577 1250 480348327 480348331
    0x51903090506120a0b01050c010e01090c0501090806220f03030b01020c22111306021b03010b01080f040302011401181b021c0c0c090603060e010e121305030d0314 71
    0x203403140b81c6050450350800d0300c0080054800790b011510385a61000d1a84030f1340941b0403909000d0002c0211002d10b04005009010342f501c02c48002a01a80000795507015815080c104d070410006400281d9608059400c2080305000b480e25007002501520041505811060606840380d2000640d881080001903d80810108094880c0381c2801d07001000840341c0c1c01000580e9440c1c2c0c0301040c0c05034084405c84040c000d54a40d940500781c01640098601c2c1d0000f0210320040a107000822192580420b00d42680c100c01b0810b0301065442c80803589000d02c2800c7c60394043d019100005202401103800c1d81e03003000030b900c4249a05035040180c1c40c1182c440c81402d1f5280102040381c1124421208069100d00004c1148120801c0300c00310094000d002e0299410855881076039298802d884045403402860240001d6440a10740040d603007103014140700b51825078030398034010071895100700c0d204505a0b005280c0113500c3c2c0c00542d00040c0c6620104007040440c01a510003082c40259860303644031000d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 480350827 1250 480349577 480349579
    0x30c03010510150e1302120106030e030301050913020a06030f0f0b090c0a020a0c2301020312010e0c090a031424130309150207060e040204180e07030519030905 70
    0x901010b0100702040c01040c001100c801c030740c10351012104401c00752003130241c0540254000035031300f841c803c00341e0381ca034000c1c003500d1502c10f01d2040c580d0301c5400840031a41d4000c5083c9090340208014440ca20b040d0010b2903000d1141025212103620716804903041c400c1c2035201c0c2004c60340320140000c06003014020000d03251201e140070840707580020009139044102610001c0c03000b10025210300000c0c42486074094581d0400f560b03502c125501c8180c2c480e40c02c90785124415495041d54408103030361020080b034848006000e0142d4982c0d00b030602d54030000c6806031103284002070030491034010792100c8005100560150716007049265051680b44e04041500003a90101d034890b014803540c56054001a9411010300c20340e08800c400c89181c1502d0021858000b9080231070361070b0440e191689c0c005242e2080e0f84560760356038220400307002030009a00550141032000031011035645c0c520322241e0b000c1e40c1405c400e101141d09282ea6a00d03252304013201c1c2c06ca40031110007015500da0074140c22100e4075004041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 480352077 1250 480350827 480350831
    0x1902010612020303070b0717070f0e0109150806040b12060a1b0c060e030d06030b090f1f0e071d090d0905010e010507051f0212100501140c0a08030f06030c0301 70
    0x150b0300181d102d1141e564003c3c44c02442e4008108524425810300c5030184d404803d40c40181000b00c0e015007203401803d00c160000ba20719a00d0b00e159449090198115a100c107801c030000304018206076000c3ca401444141c000f541c0d0040c501c92680c642e001200d100d440c0101030205810100011000c4d6001800e0242030445507041b42003c0c039078041d030b4008601d44c000380001581141558824103500c900c0b0400d0610b00c0c24120040107101000720000d0240b02c0c180121500742c0451140c0c01d84940400301404100c0f001108494000d04050304294010070800c019142c0d02605c9243c4aa482d14112b0103030315214032070204100308420104003292a60640c0d040c200c0482d4034120000301001d00e0807006604211010602d07808101d01001095904001c07a085c1c0c0b280f2800200b4924001d412941c0030040418400d000320b07401e0b2100d00e5410003500c4069489614201c1480b43c074408951000c20b44907581d2290718a11804031321084013440c0144c045a0003901c141c103100c0100f500c0d11a2810b04180700364 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 480353327 1250 480352077 480352109
    0x509090307050d1805060409061508061c03140408032a0c150d090308100f03051519050103050a060b041e0b0301090209040f02040507051e09060d0219020106 69
    0xb42d4000b400f491400c2251410500801d0003d0410040100a03400541c0009000c40c010a9458050f0007401c1599150343c4031790f80c03151a9040841d500501a01c8003038018000c00b00b40e00d040e05c1790002103000c032070090901d0340e41001c0704081c0f503030141d100781c0c070031070f06c9400c041640d558001c07540c4140e04030403140d16041c000f49100c55903c503407981c00508500e0f100c1c43c402250020001050b4054900f030800400003000162031504002e40221421141990700e280c0061010a0300d01041003400103803a00513006010102d0304c002e203039a03680c5c009441c80b00d03020008a4064503140d8540103a0340614490005005100501d203440300c2562110b50b40385101e1030504120180020001e8a1020306140e9120f002c510a031a100109006000050002e900081c0b10001c0009006560f4200e094035072094a0420043d516014120358034020700050306012540084210005210b00000d000c1c203000050002d81b0300070f006601d040480c0d00010411003d800140303806c041540d02840343c04000c0c40c040d0104c0c0700f05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 480354577 1250 480353327 480353333
    0x61204140a0308010905180102180913050604172713020f09040b040b10051e030c181504150801050907020c09040c0e010b041802090109060818030f040509090307 71
    0xf01c205000c0d0462644d84c0e00001034031541d00140c03a5141e81c4a2500071980c0d821600a01000407410415440c002d0b04c1c0c0d01c0207d5001c4420118600d00e540d040000383c055a11584d0303031048500807041c0d035001c0c0c4c0c0d076092011070840c00010000441c51030301007051690250940081c010308a40c0001e9048080780706011585160460508451801004031070000e00801080001001040e008001513008041d200c03151043ca500034004101c00308100760003242840002c2580d04441c4401c032045103080906100113442c0305800c00341ca10010303d008081c5c1d00f0b134083c000480100f58100d40e00c64000700130b140e0546050b198000501901400061f20904240c0c5841000655142c00d03502c1001e00401091001405000300c01040c44090314216543d0801035030b41d00c00c0c1d078645800c05c0c01150408541c26038144030080d054802c43d000d4050603100d1401c2c252038000156601c68009108002e040c0b440503040d40540310900060608041c0c8a40c015110790501d014032a0040004007002840c2d0301c100710b41008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 480355827 1250 480354577 480354587
    0x60a08091014070509040e0111070c0906030c05010c0821070323010b07150204090e100203060f090430020d050408070b0f04090e0109060f18060e010209061204140a03 73
    0x80f04545091056541d000b400202d0000c00c4400010f00265183c842da514055845800134003986000700e40580d0503035195400f5604907110351200800342d03000840104001d5000b20b401b1521240a545002d0501042200c0e0010300c1c901c507108079043c9000300040000c4640c0511401f102600304050385070701d07840c4002c4856404032040c050320801c032201050310420400f11000c1a007413801c11440c155100c540d544000009403603544502c201c0c500814030308074000c0c038031031003641c1c41000700400701c0d03107400100024081c000390060400d991315070f45011142084207a00001c144005050b034132980c086411000300a040500c1c0914500801004000401c42c050001904205071082c9142965803401d00c40d00800c8580f09036401031060605100814110f004194040e03e01c2502a0346c00703001180750382c1d20100849200d0220012100d1100c800c0e503000c07580301d612002a103040e0303000040c68040aa80007441355001440207a4a514481c0100f104000b0f40100e5080000941e20040141c01e0182da0090a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 480357077 1250 480355827 480355831
    0x10203101d0604111b100c02060f0c0703030b04180b0901090f1202150a020d0b0f0102031209010b041409010c080c120c0405090103120908030f07080304020a0302060a08091014 77
    0x201c92900c8641c042c04000c4540e04954040300980041e00c0e803174078910741d010b49032121502807903c0c140c500060703a034500f80007045081c03140095401c6081c00307949071448105581c000b2a0700340c04240e602c90260b1165102e0380f2810507015000101d010100a4a2900580c9a0f00082643d5081d0f4102000f0400044100d50708019143e403102e0318410b003d00e070300e004902d025800444119007030020418803000300d107168010071b41c0200001c001e0004001400500c20740c511402c641d240140c0c0200070750034010000803995900315401400104000079030034002020f680324400c01e5031a821a90061003450f50707003407040b44001c40c0300d42461902e91502940b191403601401e0700d003035040c03500741000072924641c2c1d001300c8020b003000604440e8a561242010021f06d5410b4580c800811728804010592507000020f6501c540800c035180c030302e40f000a80d100307119a00040c1040307030008c02581011006981c6c10000e0070341600c8507503480c039880c40c1949107189440100a40c0b83d8025181c0150490014174001c031a80d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 480358327 1250 480357077 480357079
    0x5030a080c0325060e0a120810080d200604030503160c05031810091505180402040b0c1204031e02010c020d052103220c0b0c010203101d06 61
    0x140c1c80381541d0461900b58800c51140079010391942c0a40c9802e01d1090509541407030148008018103100c444003c0e41d0741030203100251240000d004228065403040380c680d64030143c10702070100882c0e40c4200f2070b46400000400080440d100f441c1103417030404060514882d50700d260005248a003055103019140d444050710664105c032010300342c007a080e40105d00500041d50301c081260340c1c0d04102d50081c114985001030041c8104c000e00c0c01c00b030842c7d110701c9405c401d0ba07481c40c041c4c0c0c01c20107140c031098500c2da100c0e01c211100c0d0104c891881d00c01c2c1e41c4601c082c000a103492210030750b0302e58a8209190410421103000c0b03481c14005d200c2440814142c101c40c4c01086400201b03400c2d05246400181c4040241c1d0600a50020f084441c01d810403030013040d440c0111140e46603070359505c0e0302c903d100070690004070707205402c84443c002050715000121224082082c01880c110031083d0321201da041c0c20358003400118241da03400000740060804542e05d040010600611803980e03881150282038030b0380d6406810302d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 480359577 1250 480358327 480358343
    0x315150c050a080310031103010c14030604240603110309210d020d1a010f0c0618080a08010503100908030403180506070303050115021504080f210a0c0201020405030a 73
    0x40c8003003100c00c00c6000e50a64204030482d84034604109205009644c0b8041210816002c42c01100181014012441e80d4075903516012143c0301603072580080d81d040204200c0d07100e40c8175043d14807100e03008459045400f958012484605040840160946500f8070182a25490800c10072820403030114025000d00c8000030720803511540607014410702c3c0200542d03c00c140344000b580101c01134590340b0040c5120b01541c44400c0341c801040c01903551340d802c00e2021010a842c0480980050001c0d40245041c007003120f8410606012900d034003401e600080d5103240812041b6005111300d2404010400500076420b1080c400000b1070380d0b5409003070101034002001d0040100c0312049030301c000c848074009070034050300c0282c0710805810000c003c0c110078860100c0010941d11101c800d1031001c90505071030500d01e502c6d40019280d581c6c4201c0c107a405101d03440c21000050191510301c5100c007a044103c500c0d5034140768420709004040301c080340e2001d21541d055a104000411103620081222014282c2000b00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 480360827 1250 480359577 480359597
    0xf050d0212210c010c0c0503030a0c09150201090303060f141908011404051501060507060b0a0306421203030b1f02060601021b010c0614282307030905120a031515 71
    0x15a602c029a41041802d0110dc001c5d40790741d07075070550203102064020f030740a120169035414080c400526a016145000c100f2030000321141c02c280d01640380c070444503a4540b60242d9181e2029084810780c100b15851071003a00b0600c0240b10007009002207404000301c00e40d0f1607514080703000d419849509801041c041d214686103d40b40c3d03404001c00300a6802c40001e00c18141408200c0501d00003079014400082051131042001d00080303102c186107590585400b449003410440c0c13415007840e08400c11400c15880749003803031407030b2554060b20030108a10100e03100ca2070b0003220041e09040005040360f04542c03058a08141c041106d1a103070305081c8007070030700807d200202e050800241880c889a52010b961403414001c6000c0c41100c001141c505498680032029041035076041620b40c141500703500b0f85040c860111404000705181c6822105508000500c0d0302c0d560b8039981001060020f03134050140c00300d0404401c0380c050003600240c090300b41a400b001414909480c420180c0384c0f68582c1040042c0e24 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 480362077 1250 480360827 480360851
    0x17190f0c050a05030a02010e0a1208040c03151a10020607030b1c050714030f030301140105210402040b061e030703060e0c130f050d0212210c010c0c0503030a 69
    0x840c8140550840182c402c620707503a00f052aa82e03404441400d0042d0710f000c202c4114180e01091003104554802009503c840e003d420444020704090815603824014800000014a0101c9580e21600380b04801148070910000f0310080d03c0c0080081d540203200d80130300b845503030360b000c201c2c15403280f510f040010360200c041c1c0104220390180c103d212121034082c801c1c0024410001a20000c9420103450721200000b4241231541301c41010015400960060005110044540c0c4282ca003041c0d06141050070120104440c40801000c2d43d080c20120114006000a60801d0300421040034404c2e16428030300400380c030030b100103c46810818114510044042850306100360428002091904030b00b0b03800c0c1c103185840208651103514a00140f0901480010b003056420b18540111000100307425406039458080c0b000242c4281c0c2c48000c940114102105c4c40da4544001c819070b8104050542c0d1580d259410441c2120003c6c40b40006100225401600051001049a6001081c400003003003910f0044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 480363327 1250 480362077 480362087
    0x10e1f02070801020c070f081908090402160b040209010b030c0a0305091c200616050715050703020909010b090901180f230f010506030106030908041d0417190f 70
    0x82c124503800d500000c0c00e100044d10004025081d1020101000441c17981c40c400641e9520058103441d1802c000313264014045520000584280c9002600241c60860201c81c1d2002003185c50380b00302c4405084105001c258240103e12602504004940d10b24508007480048286d00909031101c00b055110b400080c0034030014800c1c1c0c004600d4591440303034a800c4a101c0541982d0029803040410542604e02840440d000203240f406100d4141080c03045c80c10781582110642c0c824542541e01c100e0a0152001002192094520484103581c005803a4800002044410913040e403002d0310400041c805994213594903618507045560b8481407501032000c2c0d420100161031000702908a075840c0040da056440001e00580c8401700702410300f9805980c40c0d280b02121528280182c81c0c119606100501032180240e02c8500568040c210190070117943d0a4890213690496008840010240060000304120081d00e0b481038500c5072029410003113000000143c01c0101070044003000401990181c07441cac010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 480364577 1250 480363327 480363329
    0x7030f1e1d0a0317030f280507170406050a0b0103020906030621030f0403140a03080f090f1c090e01060f12110c010e060105010e03060a051b27010e1f0207 68
    0x500d5035140582d0380c0b0401c403159001120f000c00340c02000e800007400c4c503075008003c0c080030042808847c0105030a440c00300c0140310062042d82880403000300f1010300d07590300183c0e03842540328000101d40c40c9014028601aa42402c5650341414018840c42800b40d80300404e03a42c0c0034809985403140202c0b40002405503c42e150010b00c0c46000006500b10718000000080059a01501210031744a44200580e540e88150b80c401030001414100490300d505106070907141c00070205002c9030505000a0051820030b490b01488040c9451a40102d40660b50003030303030b510700422031102d000000358580b0102501c040050016881040030750480030b01c0c1511650310600708a00c100050300e407a5280196860f00900c0c2c80342084c02188034031800061913601c00e54800103440800390140450342c0b035150f5088054403024010a102c111080125120b0b81e603000d000d001c0f840d04604803107104680480d926122940d01200d81070400410f01d18031000768440d0b0b07102d1000c40c03582490074240c0c03c100040807804d001031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 480365827 1250 480364577 480364583
    0x2031b130b011404060f0801050d050303070819062601020f12040611040905040201030b060903030421050f0604140601050d020d1505100315050103030f0c1707030f1e1d0a03 76
    0x400b00c4c010a103564000e060700c04503030903500e541c000c036600d440401c03500d070498100041440e40100005850a882140041e80101808034910501200941004295041da40001d0000c40724140824840c4283c5404561000b0050000b1880c1c03030a003840240451181d40c0e440841d030102078000c14100700c442ea100c51181c541655180c1e0b1140d031200500009004260f6007a800a420040c02d0005407802d1021685501c00081c015440d0074540003103400301c01c0100440042a03003c2c4113014011801c03d000080c22401c13490090502e6140030703d4101c01103031010300124020b0380b201006000315101d401004d541d0070740403500060703c4482131528002c2c0c01ca8a074074112039141024148060701d80c0b90745102054911903194030201d400f0b40010501102c6003488041c002071030070a60100d11500030b07000d00ca0000d0091700403000b0f01040088210386a4849103040740050901c0c5500c14466520642081c00c1c40da20910000ca800e012040092003141040d05030041130324002c81040c040c0c3e4a2a0070300c0c0045074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 480367077 1250 480365827 480365867
    0xa1710080d05192a0213050403020c0117010f060c140d03060906080105040b010b1e3010061218060e120a1707200a02031b130b01 57
    0x180c0340344010000c0d000a0031001d43e000d40014030758192401500380d01c0e14250020490b16014801080000043c001e42000740c0c1c101c0c1c107081c40724100d03684a0240d0f40c80b542c0a6002031844420100004040020010344009000704180c010300100c804500c0c803800b1200c842c684102c0721241400d208907a402c940d83d56844911940c04d40002e8903800da0000f20444a44a50400171950b54189007400c4e01d0040704c0c014403139059240180405050b44001c0e010105901c0000040c00307461400080207640865254960000701c0005100640403451030702d0050b010000c4000c03250f00b0155400003044404c1d00802d81030147c14088100d18900704c5d40710b09010590060210101c2c0c1c801d082c1100100041a840c103803034042e107150540003e030040304480441901742c0e151103410307585c420781b0f0824410180c00344c0e0802000f80041111000c203c0e1000c00c5100b8400050180ca81c0d4610426240140e00480000c0480f80348100300d4041d5100b40d020090320191560100d9a28103000c01240d2244a1071842101c900c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 480368327 1250 480367077 480367093
    0x5091b0a031b021e031e030405150f0f0117060f0645010b1c110304031809111c14010b12090313030f05010b060c010e120a171008 57
    0x290b000402c44d6460f41c1800c011a80f044d03108140f940c9034803589100305c60140181640111a070150801140d00500580540f0704002c5005615201c0207016501c2d4145120030800740482600d51440c0b890040402e080c501440603031200056031284d50052440766030701900c00001c0c807103480303000404202c945800e05107a8110344407c004103040450301d10b0382c901410036440c00204c1208101505050346d0b0524025801c2c8290442007032103030140565100c49070303034407203500d0760030860302c0c1d00610f000314882d440e084900a00c0241c0001941c883c0d501141d009400c5c42d910548400c8104c0403604000c491040c5007941d0b201086036003002d000204005915010b01c0000000c0d1203010b072019000b061281721584002c0e80310241d0041d601d0184000d2030215105542c001c10000d020b011800900380d11400000c110b1603030480009007941c0007946281490394558201000c0030720b05016031038040c006600f8160030a607901c50b0090595070140c0b60904640c2c5da49002c00c140041c4c4c038a00c80018081101201c0b102d07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 480369577 1250 480368327 480368381
    0x30703151d0d090806093705150402040b10050a1d09010e06210606060705150703020d0c0207031a0c070807061d0a0b0c0a0c0606090207020a05091b0a03 67
    0x143c1030910550000d402820081502e545021401d01c10007103980c0321803240e00303442d4240c100c01c0e0a04c01014003012172120700d20100040c403d014640ba403a815003204450b603d03140c0148016152410540c03840303002070b480400c8015800c5410b9076030810003032402134103c49800b13200c40724840400c2d00c80d41e03100d00c45400000d2008c41c40d41405115400584070780c110420640c4007002c2803e182d14000c68030b500200300180c55400c0c44805000418096012115001444a554a41113500b43c2c1e0784d0000070340000d44c0c0000602d40c2d0044004d5071300603100a207000f03032a60703d03110314540a4080103894102142c0104030f50504110035100000d401507012661200b661078944010100324036001c20a040024000310300d0340700401c0212625400041818865580c444074040c198042c440880030f109403540124040b510510404028042ea0700c001651450540100310507400264000c6100d010401d080001120003a01c41d07044491044042035101c0180740e8040e0007500c1084000b1007007100d01c2d10381d0340d11 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 480370827 1250 480369577 480369587
    0x6051b030d051005030f0c040c17040b0603011a0913020d0507060302090a0e091e070b0409050f06060910080402011205040b06040f05060612100806041b05030703151d0d 74
    0x28000c4030032100151644c40040c07540782d5030030400e0303041c1d241c004207068402810160424800741c020303407030006254000c021880005280507181625401204020444903040134801c15030454988440c00c0020075424000a0322554002c0513625071800f0121410115282c00741c5002425501609070350000d40c80d050700900a400c24600c1d28405d41951000090386ca03445101c0d0750140314103801814134151030044a58648446400d1020203114101e030010f08002001301400c00b40c0013a01e804501800c1c1208808144c840c040c3c0320704d206080c100020082c6648000c580fa42c104c00342d05141c41c042e44c8600059400e04030095100011a04000401003009070400300c0310b10a00d0200d81c20402d40801c0400c010481d0400c49400d0b42052040044c40080384080d00c1042c1c0c400c01280d105481e10b6201d40840d070401509076402c6600707d0146407200005150241040017406c826001020114959202e030001100241d0f041d0b80030341da50710f00d1095060340d100035101103042c000c1c0803901c51103034005008103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 480372077 1250 480370827 480370831
    0x10c0807080a2a03120b03150c09122d010b0411070302010513020a0b07080409090309170d090b0d0b0409030f09090209100302030705070c0e04020f060307080106051b030d05 76
    0x802d1944041000b0b200c410303103c2c805410396007590316800d204404000000c0100140c15095a061080000455841c00c4e185203191245496516040d280e11000c010310140001003000400e031500026540014840041c00c40c2d841c0b83c4681c80129404614071050781c0c0103040000026410a06200c48a5112031034100200412803103039000300003d90b18420042140814804001d6100025103020001c07800044058415280600042803902da03070b8100040848d050f0b0748044011500c140c20810026001400d11002207100c040501f0a140400728001c1000025028101e128800460303281200305566000604926024100304004075072810042e005983c8404410002401e040001c50068020b0003600c1901d40c4c0036020a110340f14050068010f508000d00000030004140000340c0800c00303d82d112002013004448208150409005000c503905e105650940501c0003002480003255120020340c0c1162040d141040e11105002c0320300d44600103040b041381e050302c40450464080801076011364 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 480373327 1250 480372077 480372107
    0xf0d1127070807091401091514120a180f0201080a060b13080613030c080c0a0b0a05040308060409050a020f2701080606012303250f0807020105010f0302010c0807080a 73
    0x84981d81c880008050084c03840345c89000441d204810040c81120313881e8100352850600b0300d2400d41920040c00130680e081100080c4075280c283d410310204a0f140d1040584680f030714583d480c03040d112a05c0e00289241031100080c100b0100d407000a0b000240d5a02c1300015111804c5125a00c451000480300740e54500e0245482c1c034080c41d0b002c5440072061a084800196040d140c6483d00061034807842a96002261a002c1c02c1c003401e0003900c0000d0721142075034032585601d900000c41f4105801c000700742c00c00040116004078039005912010a4000030602100d541c1110307481062070070500440c001c1001e481d0b05c880143c01901c20380d108441214255030503a01d0000c01c03541156904801111040c0c0c546110300700000ba00c206003500d4a49540045910440d00403804081c1c0c0b24881085540d544807801c404005417210700410b146550090519403c8202e5100034840d55042c65141100b07070b40b013031200905102010682d0801c0000c0304060310402303504102c0c09500c0725a410001341c4907501c40b401c03031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 480374577 1250 480373327 480373337
    0xd0509030d0f0b01020a032706050403060e120423090a060608060613060f111c0e01080105150a110321010e040804060804050118030504050f0d1127070807 68
    0x7030b842241c6841080812031050b40100314125486d101035a40007000451349480c0a2905804070445520790503030401000c0341c0d5122aa03480c61401c00c00c0440e0b54146444909400c154141040348100078152425641d407903026950700074540702c40b8030400704e0f01d8403616005203105d0308010703405442e64001c004480d101c2d12941e041c0ea40e1401044024449c0f18048a0351150204041c40158440e42c000e80101c4250704200b0800041508898500030101009134200b1030400d030300d02c454a61051500020050a003401c8000d54100f80000d0fa880d1840c0e0051100a040498101d422521404014580314010000d0701e82d82c8001d0186c20b80d000300768521800f20030890000018803000769102481c426500000c825040604081d01154402c10150080d10b02e50340300d00e0004095100c1074500c0340c900740f181e1545650396240a0a110511003504141440782c1520b4400f01c01140900000e040404012505a0040307813000c1141ca000001e414100318500c10724204014243d40c1010705240241c02507220 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 480375827 1250 480374577 480374591
    0xd1401051014030a020c0a050a0f06180201140901021005010e010602010c05070309032003010c020f1006060e0603131a07030b0a080d0818030a0c170403050604030c02060d0509030d 79
    0x2003a20008500c05101d80002d50400000d401008258042e00e034041d070050540d044680a500c51600d0101414001d50f00ca1111880d41d00400415105100c0c180100c820141120805500003a2541500c4200f41d00d1952000516501e541c0c82801103280c500c4d1211820042544c4070a50b5401004007405510090740c6020758292a09000d030040e0b0300c50a82c181d5070111002c1c1980e4940c0d9010b425a040c2c201d440c40c120300081055a805e018410702c0013001c0c1e0050030a254407464007460540754940004000d4600041484096481008007c03416030035124107503240c850865036010780d90700e550041c00b17941000d4003110600e0031811016000c0d40050b901030140c44468020001c1250f402d1050040c5a0f20080c0240011400ba0a54580c0501003a1402d0811551600c00300c0c116484000700350000b0310902d54040c20041e051541070800061a042c460829003190781d40c0355605806480034060046400c24241155550411601d240c404188107001070300749400065030b250088202114035a0411007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 480377077 1250 480375827 480375859
    0x80105010e0613020903070512010e01060e2a07020a0605040603110f090d0204090c0609080708061e091c200604120309060b04060f0812090d1103030d140105 69
    0x38000303002e9007004001000c651800b050642c000d45c0500f16081d09401800300008007592001580f2507000072000011900c5402200c0c600d085400e90703000900c040000a00340155441c00340001d9000d01c446160710a12079520031600070702ca010701d00313000f0361010000e84049841c5030320001600480d6255281071014841c0d030248131000e805030300a5099003400c01e21405081d4070780781d12020f0792540094000101d068041d198103454124a8201d40e012800c40031041003074040c20400c0b00020806100540f0150811106a861000304c030211803031280740e4240819104601480165044080300400d107090300000c0d103014061720f061031044680c030542c1c081e000e00f900ca4086021403007550b21050201c203c054820302a401424940010b90b0065900e0b107058115480c1c920a605c05006a50f01484034a460007252501d04124941d0340300a140003400603d480e0f859260030250b1160f8080c0810111f60780c6000402d1441c055660343c0c84141d42088902c07091010169621030699200391200c43e50800340c18 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 480378327 1250 480377077 480377099
    0xf010612030f030b0a090b130908030105040b030321070906030b13051e0f151f08040807051e0c0111101a030304032108040506040b0a11070c08010501 66
    0x4464060035001410a140009215480e001031010301800c001450444000220f01c00c24a1504031002c0e1300e9441209074032a00d0240310300c4034010401c0c0d50034401c1c1d512a540d0800d2502040c03062070300640e25000340c8002c641c0d00388140d030000034003244078440c003203440e1440e01e00340b003c16582c20011500d07070000811030521a014900382160080c054100b28010014035030b0051800410b14a1b0214107003d0000202d01040c90b02400380311000c40c0d01c08035045c03010030302205000305035032244550403950156616411001c818403080c80242000400e80e0b80d14200804280b0880000a14a008480c0e01c116401e405003207039030f01c44c818078049844440d44d11005441540d900c82240c0b01550000b01880e03525202d03500188a0141c1c01c0e1600c0241071240d101107440e41e0060340013140d00042e44080c0404015402c00c008040c41603038a0a0589800c1945500d502c030354004d1f0000e404804c442002403507028941e00600c1840304004031043e0b5424007810400b0343c114890040f9200d035400d01e0b000045c011104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 480379577 1250 480378327 480378329
    0x613050d0f110604050321160813090e0a1103030d060848040f0507091707030b04030503060d0203060118050f060a121e060506030c040c050a1b021507050f0106 70
    0x46c006090642d02c10f4000d0400da10804400e60315030400300000001c8402c4469070f1030200e84030343c0095446d08030700b2203000d0403840590054076007180b070400012644100094011542600004040403118428012174214410071403000b041e1030074444002201d00c00017680c4c184502503065800f46043d01d0186101c000d409800a5141201ca1000088064090382820381840c4500420025410424404070003d641d011210078000ca502c0e10820019442c0c1007000303484c240e0b50391002d802d0f2203003036a4501c07850400107003000d0300700880880002c0d00c903254180448005e03500182120070a40c1e41d0003070f6109041c44155003080c0300781450302280302c012841070040e0240c0c00050146014a0134880140200200d15505a507a424500903078901c0302c42c00151413010034090b035408200b030f1901ca41454a051455800b15000b0ba1a200c102d01d5419400001d540b0502d2461800c001c074410f0420041d0041d443c880006984094101c4245070b40c0790483c030003061210322850989a8030080401018202d41507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 480380827 1250 480379577 480379579
    0x11202030c040b060d0b0d171312050d1d04060311121c110a12020d170f07030f0204090e0f010605090f070c08040e07020109061104060c020613050d0f11060405 70
    0x1480065445d500b03a802c4045440000703403000345c0c05226601c1c0c0000c40c034801e40320007140000000d000701c07110424103200409800313100d0552241040c250348840c0e6a01070410180200054017410312001d0102200e00c004c9800014028813100703840c0d050a080308419804410310415200a00014000000c078040740c4051002c00003800346010a0b10948181004c0302c980a510301a450505001030b00f480c58400300e405195006012910084c0c501030f0100c501040c240c0001d111410400105030b421040c0594080060315000c182c10030641c8034000030740030304c0e081a0f00e4a400c0c03c0100400301c2c80002c4085028680074000e0045030364440501caa01501921000603c59282c40003850607406407003030302211449030955625003550742d000440c84240a40c0d070140181d46440e011030501005009a600c2c502c22031040f00d140a18001000d0541181740364028060100460042115a1980454402004050500200c1c1c003020726114045c8031240c0300803101c00c0c610b20780300102c03070038104190340507908 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 480382077 1250 480380827 480380839
    0x60e030c04050403030e0f0607080a062108090303040b030f06061201210215070b070905011b05011112010906091a060310080d0c03082203080c12011202030c040b 71
    0x1400305000191100501c198107054440d10800c4d5100010800d121164054001400d203608120b60300902c00c490240090035860304104060090122141004220100508040c03051076040e144c044003a000d107860040c1d05000110b00060b541260100540c85241c2c18180d2a006964000802940d402400d2240100018281c01403080d404044020b8000c41e184446054048055034000342c9210036038820f00110500106d903800401000d150243c1d04040113082c1501080e041100007402c034051640e0740d4000c2491a424141801000c0d48140b802d1400302ea0204e6996401b0241c2c050020170a10451400c54a00700c0c00144000c3e56202d10092413018104440c1c1d480040010084e00741c0000d030a0584440c0210000034080c2010406450000810f0322030b108100c1160401811883c0c1c001d101d01455500c9685000c60001d0711403143c194a60b00d410084041c0d01c07000400e071014002c030b20301080401d01d65000840c120b00d8513098803020074422411074a02d01080828407054914003100e041d0880 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 480383327 1250 480382077 480382093
    0x619111206060d090c0f050102060a09210c080d0203270303010603110d0603060e070e0103080331030e040c05070201091503270b010e040b0a05060a080f0f0106060e03 73
    0x8a482c800030810658024008180703042d44e0b07240d012203400654068980e8684482e0f08011700d503014403031036901c44140e210800003100c454550f248034034040e540fa0354140010741d410040c164001d9001015050300a80d045441d090002645002036105940c111903840c0030400d00c58680036040d906d240341800c000c000d1400d5910f002010f03005002c055202070300c008030074440c2c0c11104800b4400c00c0c00031030003585c010900c920720310b41e0981840c40b0742e0071024050800300e0041c0003269000080365002031026050042016920b18140445003042c01c0104250b25101c3c0f009040c55842110100501002c907010041038100503420355841c41041d10082c003060000300e0401443ca2031641c0c00009a9803420b020400d5000b181340e0402c50030078012240346616076800c15070140600d0f088500d001d040300c0b1140707901d18105501d480208a078010038681034540c964000903016142c540d002001410144121821440107000594881b8688544e005003507203811000600e10348602da81400700140038026040c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 480384577 1250 480383327 480383329
    0xa1703010f14010903050610051509010504050f0303090a060807020105160c120905130609050c04180e15010b0a020f030f04050105031302120304090c030c050901110a050619111206 79
    0x6050b02c802103041c0895160f000002c04d0f004d1200b14403030118070b82d034101c1c050b04000802c40308003c504504104181c0074001402d840c2d801c0411a826102c0855005280300356980000e0710b94410301706e80c10b421401c815000039031103400140040c01384045800038461a940d00c008bc2c00034210070000440041c0340c0d0b1000b88045660741b41640000e138500c0c074001c9050740d112070200305600d0f8099800e9070b203160b840d0720802a003105449442e4100400d01c0000349018030701203046c8400000010f000400c0d69a50507052080d01c0108041311243c00080800010307984d4856611030160801c4c400b00016004a0504040c000804401c89140c216249648c42c00e040c1403100464040d00f00070190f901421402e4111400f694400c03803191002c916070300066a54038201f240002c151443c031031410061606003801800031175009810b4075043c00080c41c00c20b1804810f100d02a00d0040000c2e806001030061000340b0900544d0800281c024592683c02400360520061144555205216159410010031408900a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 480385827 1250 480384577 480384599
    0x100507080f07031d07030c0509010311060d02132309010305030a1d03250b09060304060e1e03190804050a031419080a0513020f0609130603050a1703010f 67
    0x2d40b07140350001d03403a5490100b88910701100c002d01e070301a50007004104100044030165001812040d58038a210f5491035441109000d0f4101102c3d00c1031001040b00062280260b043c1c2c1c042290050042c40507544c3d03842c9841c001e0382b4804400e4000d08441410065500b004003c9a0480790301000440c9400401c0c01c2c00c548440d10101c2c2c501c43e03030074195504d680135070782004518104a110034500c0340401901c0b01c08000706601e54000805101d00380408109507507400f05813580582c22103030102e032020b001529a070504160001100a62051100a0716800c40020140001c85107000e03070041c440006c03d03c1501d91803001c0300c4c0100350350b20814100001900c0343c0d03144014542962040c0e400c2c280c66000d240d03810300c0d0030f2004400050041d0104020030489001e055000305031800320301d010203030700e4003c42c10014001c1d15050040c00006900401707a2540b105048414068840410041d5140c1c42c1aa44464503410300f50b640507003421241d2210a03941702128122210580314070303890782c1341044000c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 480387077 1250 480385827 480385831
    0xb18010813020a0f090c080f07030b0604050409030e09010503031608091207080607080f07360f09050c130e0405070b0f030603010f0b012f1e100507080f 67
    0x6001507041d4000801602c444000c80c01500359012074050301030404010a0403105500701c08410010301c1341c18050081000240c45800210070304e00400c5070340c900c1002c00d00c0761007a0380c08075400038508101c4c001411341c40100903c24210485607250141d0f41d0b4000c2581e80c1c0140c01d00d46802900c10300351400000c603280000c00740014003500c00600f402240b0495400e10002d5480040240c00c2101040307500743d07100095540c00741d4880b6400d107041c140604010121942d69090543c0391040902d0411002d04d141c0700c2045546016071051542c54481c0440c40549417144a0110500d04020205040600010a8580c091055840c3c40d10352442c10880c92080e08000d001590300d800341c003102080d40c5440d40c004214204480903000c1e03076030030104181802c4400034031100340440d10b44140c6c0300c59aa40b20301e10498142d0408072070550080701c9040004401c0c4420048105440780c0ca14100418001e0300c3d203650b040c6040015035981d102c000c02c00805450045030b031900080c3d007600004e50400000c0c0f40301a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 480388327 1250 480387077 480387091
    0x220209030709020705150a23040302390f01052a01020f0415020705030327030307050105060a0605091c03050d05010602060105121506090615040b030609010b180108 72
    0x2600140d60781d0240022640704584c1912a500240310000000240c3c000854010030b881200704401661400a940142c8001e085550651340c0d8002103000d06100f0400e80b04911022600700040f880d403401c1502200c0020700c00000c030300c02082d002c0072491625444003803040705c040e101c141c500301c03110740c0404c54201c09023034188000c088480d2803c58105e00341302170030b1410560f100d466501c0342400c5441450305240000f001c210b6021400038412900c020042d1040380d5200e541c0c45041701c0720300c2c142e15015888481059010f11012405c40c043c0441504240e0050005030b40c2c02c0200c940303464003111144a80e0000a4020010604007078404211160904036240240303881350410100c4040241030b10020f9102e5801680458014440361a00040c0c3e00c0e406503c000042400a248558003c0e040c10024030007441913064130001030341070321011001c2e0000d95400c0301969581703449508050f8160000d03540140a6034075000003261015401048a40b0902070495030829036048130011200740c2c000030240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 480389577 1250 480388327 480388333
    0x51203182106010b070c080105062b080f0d18080f0a03090206070c08071d0420031002130f03050604020409110a0e04050c0a030c1701020f0c03030405070522020903 72
    0x100c4a071050901c01180603005840d2625904c00840c10401c2c078207440c6d500090016490501400b180b9690720002d40d515480034441e2003510071040402040d03460072041c0143c40400d000410440c43e511103001000d6245c0450010010049001829545562104070007014200104801c00356508400c0187c00000e02c03a280101d403030074213940450404d400921046910050510080c805420309110180150203c40ca80590000420001042e070302c40c05800504041006020b4840d4000baa103155415a8070140c12203e0414000b05020002c1d0f110f0500500307220300010f00480c5549044611008480d0090020314094a07250208001845000c000300c80a10508000c0803168442036410401440011910f010901d00303803e100c2e080c00c00e010602e500c2105041410300001d80d01d0801c4030309948030303009840c60f50042440e10f180203104400c8d10074075038000421a0400d81c4c038008001d6200b079118200b0349501c50751711400d10800212400d5400c0a0042c91503207000e0241c0c85030301604008034003e040f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 480390827 1250 480389577 480389629
    0x6200304180903020c030d0c02041d0109030f020d020607050409020310030212010f061202030604031202120a091203090c1806030b04030302130b070c05120c04140105120318 76
    0xa000700700640c4805036290344809a403003c0c15010700c880f0403210010b070094019040d480d0300040a192008400a1250396140c80c4416801d07035001411003007041035802008161101d003000303480d91a80280500c014401c5800030802c2500c045400c078014001c6441d418100b90030b0501d003c0c00707500001d240b10005549a2400405a03544491880d00021500c0000403040c03001402d04054075284c0c0c00100480d48030300700a500681700041c0341584a41c05103000c128140b103011600c0044e2050300c916060320343d408070030b00c492003030703180d100c510860320440585204642e108015401d030b9605d0103000c1c044512038402003002c12103114644204250900000a01513140e0740c072621050030584060700080d50110314901c0802100400c2c034041d0140022960910078503a42d50b200c0c1c080c060181c103020381b10425940407081010010244642c800500074420f6940710681c21590030320034407443e84a22030340e01d08400801c0001c42207407016034552003021251a00d51050003c550200510306440c0484880 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 480392077 1250 480390827 480390839
    0xf020a050604060f060506031006050913020c030a11011401090e1f050106030506010507050304060c0305070503031303120614060310080f0607090b0c0618030c070605030402040501090606200304 85
    0x2850b20840c0301e4900040d000c6250240c6800b295950340100b0300595040080c803203060000080582240e102e45840b660b10031140f00401c1e4a42c11148142102d580003090000001c5004000b900d41c0c0c142c9ca43d038503148400000051420780740c00f0b480c408060098440140440717080e0303030460854200b070359007190b040407010307030580720036a205080100d41190b035003005011596050107440c2e0402000d01e800d508000c2c580c0c88203510381c825403003401b044c0010801c0700400c2500460559030995044003e690b10392400441d054001002c5410031030004040340c0c80308600805610500e820f840584d003007a00201940002d00c0354550015000481924201d0700000303252100700b00078094514848040d0a00341000b08000e0070f55200c58100012464080c0950503001c1c6001811341d5201400031040280c10f0360085415055105a408542d035034054610040b4a2a410100035801244241c4d002c006907a682c0651804480f21402200c0c005405210800640307000346040000b0403040c80b09403860195104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 480393327 1250 480392077 480392083
    0x60409141506090c0901080f0a0b1513050105160602090d02030f160e1b03042303041703030f0c07030203090405190c0201050c0417030705010212091212070f020a05 72
    0x1e40040350591540c1d080007128105205401d4104403800c41e0181407003040ba00190241400910b01c1c50168041c40010700b08254981185107802400780c04000010415061005190b000c00101170040244203c0054294815411101d40c5104581902000c003422f42d10740002e9400b41011a9112401c943c880c00569001e11030a41c40c103001703600a0181310880080500001080e41c48501400d030030b0020003c0c64034040900c1328040201070311556590343c403071400c004154002a0303a00d0915150f64040b00000d2000001407065481182d0b0780c02680c10903588456892008a95814040303000c50301150710004a2800303403801e00e20a0040c0ca09292240d80820225001141c480e4104220010010102e0b65240f20700d00c140051440240b2003443c240000c0781d02071141d03221301c4030610302507041400303106003c4c13040d9101c0d241e10400030b554940540c0c0750300c100c3d000c0a40b540d80fa40c0c013030b02e8404036850010000b2140c10200d02c100f1880d155494110999158400c82d14440542c05405020300c000b900038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 480394577 1250 480393327 480393343
    0x406080c030f0a0f060506010c0f050105090727050c0c190605060f0a21140a0303181505100b07051c0e01120906060b0307020a0209060d0b06040914 65
    0x1400c1208004041610300308a18902a440b500181980750202d0809100e00c0d6101c0d80211011a0a03151100121040c42c00700704054070051481d40001c04110040d0811801a0041030441c0c001300e80f940031041e40901220805c9001c01800d403298280c00c40f00e900038551240400000e5810904625511810000b440c3d001008107403003000845c1c00c00442d44185034010009481d40f805c0e0300441c13004103418030083c3c0142ea8203156201030ba0745400d40f0120000540e83c0c1d1244d081c050622102004d0f41d0b88460700301040300840d0a00c1c041c0c0324025918229017280d1034100811380010281f0000260007040d010b0200080c00701c0588000c145012804010600b1038803650013041003149508010001d64409924241001601480308189030383c04828040054419400028003030004d141400c02000642e010824440000c400c120070143c001c944290414025100c54007141e450b0420071180008070040186962503080100c0c07000d062550050a10310301c51400c004141101000080c501481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 480395683 1106 480394577 480394589
    0x3021204062a030501050306011d151f0f0311090310150521010c0201180809033d0203010317070524011d10050f0f0406 53
    0x12a500811240180b650000c0829807040c0c019001e00070910466100340a05000007030501c110102c000300610307404400350240e6442c00c0d01d1b91403040e8403010030b503000810f5003800411142d0a1403e03c5e040ba6094403490016440d08030000c00751a4410711410b0541d00c1800021441d450000e0300e08009030b0524000304e0780740a02c520080c00031100e07902c201d0303008041494840d1290b00b14030041081a6100c4d00a020380801d0600c164203940301c0e2841800b0346031b699003051011603001c801800700080010141c580c42ca007100b0701c0391003070003030f1014180c0d40c061b40741c01c4401102010610642640c4000754107600319899070301c030788a2200c0035510703401c1d0154002400d0000c002c002d2113407000080d902c5c1003c1282090b40143d06600c180c2c00d004030a9810b000402c4032104c01e0f4818501c920942607815003c03882801c250900500000740502d5a402002e07400c05400c1030760311801a8800382c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 480215827 480395683 := by
  have h0 := BRFrame.cov_init 480215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 480215827 ≤ n) (h2 : n < 480395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
