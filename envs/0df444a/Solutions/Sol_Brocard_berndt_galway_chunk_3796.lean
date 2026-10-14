-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3796
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:42:08.347312+00:00
-- url     : https://prove2.me/submissions/b6929fd7-8260-4d04-a8f6-d24e35d5e434

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 682553956 ≤ n < 682733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 682555206 1250 682553956 682553959
    0x10080604020907081b0a08040c090605060f0d0b030a0f0c060201090c230a0f0311030a050604140106030b1617010b030105010c02030f031201150801121e120f0e 70
    0x480e180c103a001a2a40500070a0300003804010800b05800d07000d029084c01030341012101c0d01d682c030b600801c40901000d404942c210b03096082d00d4404607110040d406450104ca00c050041804c100d604110a011038100c81c00b0524203a6440341000c28980d810801041c040d4000c0c180ea030303002d80903402c00000c400e1082d08400705681c10a028180050b00c0c0c603584000300d4507601c4101c1c0380b54107451a451680c0907114542a03011102a80100f10700051071081ca0450384039000354131344868110f0505031122542c400203801500300d8030005d004124a5008000400310b4440000380440d10303a502e80320f586c030b0161035031000c442001899031a01504150301e07001521850b0702a1481d5850700c1d203115840e2005000300c504010507102440d0031504c08014800040e04114241ca440b2003410303400ca12440824428640180200d000c082082800303034440c07038141d40e141e040c0b0141110680e2034656a1040c40082003034400c400c0f0a02001042d10101c403003180001e02e65035022111003121008241d400e41c6007915 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 682556456 1250 682555206 682555213
    0xf0303040b010317090d030f030f180807020d06112502090402011412090d090515070204050612010e0115060906020a171c0f0f02250c05040908031008 66
    0x10490403101c56045076801200518030303d0300007420b00c03058064800c14640090a90340b560042582100a5410204903135400300856846a840b120550f2514000003400000100381400405d150b480100340b100d002508140b14407419035a080b0449490120f071440f45800440c0500300d80e20018400c070040c2c810190b00449105c0c50707400040704c100001d40001c3c107121041c89a04851501c040030354180455034070380704e401c030300d0501ca00507203c000c0359582d14001620000e01040d10300d80896101e01a283d51000c050400416500b880014a406085503070f204080c0400c0d109505000d0041600114a003070000c10b2154402000206510301c40d04044240107426a080c462140d00040b9121459004126450785240c04684002540b0030b40021009501d44003051080c12050794020b0381d03070200989001c01c441968620074400b00c0c0590040039030201d95680740f81000320704810542c119107000e03450005685503a10009001c4650211044071100341c00f004100c0f0702c000c1030020000074100750014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 682557706 1250 682556456 682556461
    0x50106050c0c04052203020606090604020316030504052b0905060316051809180706051312050127021c021005071434060e04020c010b0a0b0a020f0303 66
    0x800c2e101c81142c081d0b01c3c0519915400100341c032030310071070203c6403034500d101c8610101000d0070002d4680c2d40869000d4000c91002012501c1070405d44200ca00c160351017806900b4003c00d20070110040c010181098610340b2903211414440d1000110f900c021200d55081760b0302d41030010b40040d00c1c80e84194043c0307100c3c0d80c2c14420480580554904510581440e00e00300d1756521240540754149405144a07a40145c81d40342040090629203481c130030100d0b0140300300c400307840d036500b0211400e2088922044410300801d004000c2000c56014110483c4e102d0400803e1001d075081e807003480b400204045009014980c1c0c0c4020550a009645455103c8011445a59120541c0101e800d000003a03102c07008100300060b990040c0b15143c00300d0b9a042c1c07040000d440c0d01a010446000304d1054240c28501d040042da001d030134041c0c107101242c83c04c641e60364032a04503021102c41004025089000d890015540799140381034030340d030b4213100000501201c40c1440d41383d080380b0030b00900c1c1480d411002c200300e5104109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 682558956 1250 682557706 682557727
    0x322180b0112110f0301080d021018020f010c0510051605090315040c0e010b030a0e0a0b06130f230106020a031b0f0803040c15020304121704080f030d05010605 70
    0x1900b4100303407500d00010400c281c60007212052031180c482e80c0f50749450040004a407040010a00580781240da6007110101800340314510704076a5405124950810f01c5400a001410f014850f518a00c80505000d0020106034907910f040001480c01d58000c00d686208001a48000c02c5101c510448a07280003802e118200001c02c0da903060404100240c082e10a0000b410028203c0d024000f800444040f2071407543d582c0c0c02500a038105648138481242020319841140100080306d403101c6800500c0031403503890304c10a1007c10f141900e8100401a151010307610580f0b81800f402072265041e042e29000c1c086040c608905001e410b8001c0703403c54020352034000c0400d502c804441e80040d194410b00c1061441450103084040c1100c0000b480340c58080200810b00c0300d9005588116208142210018007070b05408903128401d9002c0c10001c006a125200b0101d4050203000300061100d0407a10b15098403901c440340390001040010380103610000d00718101250f80d00440d070041042e41040da083c00d20310351 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 682560206 1250 682558956 682558967
    0x304030302120f2218050606070201030f2304140d05030103030e06070606090e010c0521220c080c06090a06050a0207030c0b1b0604030c0f050322180b01 67
    0x106003182c0300354041024009401402c003101c1c2212100c41e102403070b111040c0c03001009400c9a110b4001e0b60040c1000d400410905801131601c203035001001c142ca000340541c0150001c0c1454100141c9080e0340381071284c070714031441c1c12652030500c00701060305051801c0d16101440b082003403103a9a082c0c000c2c01c00d0b010f03821380110603281540c0d414200310395210702d080c0100c1d8082c0641403025112906040340041d070b11000342e00c8520f802c40030b14000c0c044200c036518140c03207511400d00419580c1051400c44201a504140b207071f50410101149001c4005007007142410701e14001c001541d0900c0608d40400c10345801704500914104180c40c918241b40c0c030303240002c508000c80e1003100140200020981e488a00c06c0c8604405140d01180b40d407180d6856020004113a0012144d500c220b440d10031041d9980c0c100040c1180c4540c1e856035480c90150001c0d60303000800d81800404962511080c000c15010140002070070040e04400700700c0940440c6004540700fa0110300101065a6615202c0d9155659034001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 682561456 1250 682560206 682560223
    0x30f050a0f0f060f060f02010e15070e03070308030105040b0a0806181e03030105010804060b040504200f0901030f020a0b160c051c080f0f041707171506121006080d020304030302 78
    0x46c00c0000f241501d6400c26409000d42001c0c1c1e403140d001e4551406c00c0c090710055140e0207180c05a48001ea8640900c0a06a45240c2404007a02e1080300344010801c9151580006c04042c0300030b840c148550317507503014240c0b60140a4581c140c8110520405c001c841c40100041d5200052416803c140401030303000c0300340c503440180101810007091000040900144d90450302070a035001d0020003840c949401c000d07920096628800043c1580b880d8517180628103120140c0511600820781c1103182d2039592401c0d101d180d0201c0890b04400c6003000000c84450313400103884c083d4156181404c48030380f0391500b4454001c80340c0015214815508444e04a00104801a50b9a50340088403a80e10104064042d90134002e400407240b0004001070301103a504d00c50001d003040520500c08544403291101d040c0c00c4045c82c6400124140e900886055540640f40d280d119004800a02008040e1b14031120044c10007402c04903010380161655010406083c0400641c1d42d60b0420f8030265040c6803e5540c001c0d268001c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 682562706 1250 682561456 682561469
    0x219030b04021e0316051e06090415030507060305011e03080712141b0105070e03030d020a090b0d1d03030709060c110603040b0f0a020412080a030f050a0f0f060f 71
    0xd0840f0f407a4030090a9190a40e5080107040b10505251390320605038002c224041c160040b0406161a007002480b505a800c4040004140b1424080e01c00306002c014604080c01200d0741e590780d00004046a414011003016040942c0c02180035810400d861907103100100d00040300002e03409040011a9031101910301540e441518482ca9580003d400c030b40c00c480c415140f00c18550000341c11828031182c5605100604854002408540c0c0c1c0d0740c20694005051204054041d003003001001c0c041020740e402071129000b0760a040b00015110041c80d070164104c806004212130351010013444408440200c0b4a40400010080d8554030340814000c0c0840d645100d03c0040c004160824010003600038400d6003440d8028000640741c0c039003414403003003440b01654070480c0c2400c4000414245681030003228191003580e0360700500c200490323a80880310f50003051141e003095a03401c44445465802d0241c1c0c2c0c003a014011020808090700c43c179000c00caa90003901d10103901d141c95401c1084040c0c04840ca411030b480d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 682563956 1250 682562706 682562719
    0x4030206180a050406081e0f060106140c011b021605060f0705070503010e0a020a060f020d11030c100b030d1b03210606020d080a140f0606070503070f0219030b0402 72
    0x5919002c1201140241c001603407080c2882c401007010600050140941c1207400e4404009405a00303d641e1070b40c209807820341e843d811a0005110030350003a0381103826000d040f04201d15140358010601d00310381401c00c100b4003006501e01a000c0300c590410102d002142c141c1c02d003035040c0e4500f00005071248681c4207000c2d1b1180012071140203000c0c05004140040a01500920466012400080e1500b0444400b20321401200c5004103803541300b40c3c440c04000943d50000c1c811301240d41000c0c1c0300c41d120000b1841e0705210420004884900c24024160341c18558007020035000c15180805040500c4400b1203410451034408a8007042d90140d08031402c103415051428078a035415040d1225141c40b0f82442021a09000740000c0d501d60000d1594400c41c0309544240090311001005030944140c1a154103a07e0700500208a0070171600f0b03042c5411000007880640f410000d07590300d5046030003c15095502010240c040380a504003e40310042c0b44a5034450304010a0460707560480580002d4400b901445 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 682565206 1250 682563956 682563997
    0x314030f040611040b121e0106020c0f041d0106060201051302060d050a14040507030b0c1606051807030302030903010c02030a020a030f05070213091130030d14091204030206 76
    0x1c0400f02120060b000c0c528800d80d4460708102e151502c4034080c2c2e403203029401803108502413000b260002d00e060311030a6011700030781414102080903a007644252141d0041d940c48520a21104a81012049007942800070078140e2421002a0840e0b000030080d0f00400703404034009006a5400b421164032801c60100060a030b240c0c505014000c10851080a1006d00d50405000c2808000034801048030702c9079a47c80600c0d42e03495801802d83c06050b0321045202c101c001c0140000c0c00c3c80e00416072000c00392104100c43c504154071a850308540c2d40c41940540c2000400703000d103040a0181146040c081d00056180c80407084c80256140d00d03110000e03003005200d00c02414000c1c4034a0885403542c3c0c0051070300e802000c154000344000c1a072558111040101082041c5950510403450b0201c00303d00031300f80c3c814046d82307600208184070784000164240820840c41c54921080d1041a41c24010407070003040d0307858400c84141c40e100444000b904240801c1c0010001039441c04100e416080901800721204c0b17 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 682566456 1250 682565206 682565231
    0x2a10081b0304030203041509120f020102010b030d09080c100f121e0501150c050c060c0c13051806090705040b041b020105150607020906041112010e040314030f0406 72
    0x5540382102400400c10000a0106041c0e0000c050300a4801195405801c20707030086081d80c40c07000922070040e618042082e20008180c0e407481405810f401800049080805000003072300704900001001c0204900d14000d107c3c14204104000f90020182c407000e50041d854000a044640782c0d09100082020704102510075400c01d07000003404404200d052844c0e40c2000c020407010340424000c0e00c0010307403c071480f100154401c0d4500d40c101354000b80904850782c09c4005002060741302da6400802849120520344440c1c54400407044131300d02c84580001c684c1401440201880e1020007159003330351000301400280d050200d022411200206d500084062a90000c1400b515000540d08404100c1640c020b09080e01904058031906042100a600c0d820380c80c00c0120600500d1006508901610002022410035501000154101000341760500c03a003a4031407c015902600880c1400c07400506120401d41c1095400c0d11315807002d00c1040c00c514280600c030100c80c07001000504810345644006441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 682567706 1250 682566456 682566481
    0x807170c0f24041703070c1e0519060905011706090612100f06090204030f0807020d0c03080a08183a0504050f0109060914040216052a1008 61
    0x8007001e5014101e400b052880c00c484103400c6440356110b0080d520004808040b004800c50754241d0307111829003e030904102d40a05051550100501700c40000e03034003c03901341d440500100b03c100010840788080780c1440d0700208541955407050781405041c00d00c4000b524401302c034082e0300c0b480644102d0a9659010002000d04100c0702c540403583c000d6060080d1401455001803181c0c1c0324080c0240010b83c0c1d1031007510308902c42c07440040e040c0860440f00e50005511f09000b40303881070000340400400403080c1c48291104030180d04c110394a610000c1c0040442d0342003c0e42c540c0c4120740754011442d43d810b18001075203a02d21518596080c4034510140400c2d1004400c41c4601071418003021103d5503c2c504010704305034410b0190a00c02c4000700b0301c0d07517402e41c42500718606403812581c40c1c42e602c2c0d25002000301d02c558a000c1c55503016400344401030340258110000f1100500400003001106643c140c1139600480d1100088020781c03640344004a243c52340b00c40040c2074021842c01484680d181990b100c072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 682568956 1250 682567706 682567729
    0x10e0a09080313050714012709180606091107020402090103110a1d062a0111070b0612060906151c05030702030709020307120c03140406060807170c0f 66
    0x1c441c4010040c050401d00ba40d200c40c080521a00890341c1042d125414510f50001205005000456640313100c102456100350083c510344c8500070a0240720703110745440c030a0301c1c803000c8400901134203030250006201c1d45028880040003512010480c41d21244a044424441d0100103800740d80c00255006040e4400e9000c1072005484201060302c1d141d030403034020144413401441861600d03120340c00750000d10300740044490150841e44041c4403100380804803207541c1c601c410518802e5503111501110651048024a2031a1084501403014500101000001004503880c8419903101d030381000455000090704540154400c03800c3c246240d0000c0000344106910303c0c3c5600b04034030040082e020444000081c240142c030850940d0342e402c0d110080c1341708901080307078084005840008412103884140d0b004c92800c50480c40d001c56080455020310a170250150f4003160103503a10035042002107014000a00a0049500a0030354000c203205401d5548190704401ca108018802601031039a850701081035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 682570206 1250 682568956 682568963
    0x80705120702310f020a0f02120a0e01170108012703020606010e13021b0c100e100c050d02060612070503071e0503070e04060c09060804170408011805070914010e0a09 73
    0x4a05102004c00d94040e403c83c031210700101d0305030410b460b415400803071042d2030130403915441418902d03650f500301c8962541c9000e05c4e0500c0040500004042d04000505010340455800030410245103190380054074848040205d18500c0304005000007903012403241d070001c07400d10700402204130810020b221807081d8110900020b200040c0100c0c0301140f05910b0003402e50440c2604c0c1c20048201c140714807a4000381601e0000ba500c020000194500b11401d841c0541c3c081c50709070a002125500c0518120885081c0300242c0d115104012451030302000e00d50f100b0205d40c02410380e541c03400011940c1c9512034001c000b42500000d014400094200080303000601004003211a141c0d5250a9800703c2081039405544090920800c504841d002c1c06009040b98803d650700095a40c0d1500c840d15504000c00c0d070700c51341040800002500352800d00072a030044151310400d000c1100c051400d03914007011070344406040c40c14243c440240c940c5088055045944003c0a00d20315a0350300700d040010a01c124004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 682571456 1250 682570206 682570211
    0xe01030b13060f060c0203071206020d140f0619050105071b0608072a06020903100507050405010306091103041e05010f061e210c0f0308070512070231 66
    0x40c0440308841e045542240d21080c0c20851042d00c03803d0803030300c2117607205003e0341640c814001080000c1101000c8001580200c1c801401c04003c003018405032192040f0649101c80340806105080b0021040242c0001c0b046616240c80c40c072100c840c02040c2543d04c6081d0600c02c0c04103402c001d000704548500810f528540801c00b440fa147c0c440948100300641d010800030b07800c040e4400102501c1c800d400016000c200d2020b072203070303250b68460700a5885140801e4042c060080003e19448003402110b016801a40700c0580b11070030800018100e83c555408103041034200581190031180c89400c403504075401813454840484005003442c0005021507000342150b1900d082d0681d2520715034408401d5800a542d418942005041007007114081d90041165654010311450305609215118221045c071403040d008a2560b1070182c07170040420741d4001c0d1108600010180304200e0305000548000c4494074070142058902c2c3c010038603412040c4510510414003d0640c01a0801041c01c2200d0340d4000209 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 682572706 1250 682571456 682571479
    0xa1d010203040803070917150c070218010602010c020601050d0201080702160b030a0c0f08010b090d02060d0c09080a03020601061d060c0c12010207110609010c0807030c170306100e01030b 82
    0x54243e070750003111014001005c07510041000700c111003089014081c008000c201c1c01030b0104c180d442e1910094400c0b42d0580d010005540141c50781c0c1f1120303a002480007461681b561529030080d0954252804500440d08094014003032540c94043e4511400d4080c60014644d540d40d200c140c3c0340103001203115031900c82e1060b000441d00303c40c10003184254511a400e100c0c40c542d100d02580c0da1401441b290000c11146401440001c4049026001249004000c45114161a0046403959001c402d00f07000041c0c845116581a641001c162001080c1403030040401210540b0000e40f035100602510041000d071441c02281418007641680340b4180c010b20349941ca80304c180c82030740d45082200c0210701600fa40c107900d102a29041c400c0d1800140c2281c0403103040320300c81c400c009155101201c114140325a285490000c111240c01170081c240c8652600ca240d144103050224807000c61721143e4254240030401c04c00d00f5120781e100048084030900f04905603140460040e8040c0041c42c00403034000d9100140b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 682573956 1250 682572706 682572713
    0x70f0f050c1504060f080c0405060d0b0405090a0c0b0a02150114010206090606010906110313030f0b060a030201050a03151806170c010228020402030c0703031d060a1d01020304 77
    0x1040000ca080440d882030641c6981c0809800c2d0340038501c6040c0124404600d0007141071300400c1d125500c80003590490340b500d6200c00000d030325908070301e8100306190350300c0700011201d0416100e200c1d04000e16400404404100d60345130701582100c0e000350149980d002c602c14955900806c2078250b800131004041c0025a112850468011981d203181c5d4014414103003c210b0403240440d0280c02140b041c0d50b29a02c0a0500000b55090b050300307400710056100412150f4070071150010450040c40c85016402c10340d02190410100a402c044c1c01c41d84600c1d1342d604100010f07178020301100c2c000e8400b8100030424100c040c12003694007070250300c0014050600b03140540c1181d8940d000d41e003981c0300e030b50691020004400380560384a0f41601140d01581c4103110781c40105074400c17601c42c0f4050b40070207041c0b00c100459005c24140d07042a62100c184600c045a140f04040e014024110740b112111098180206540540c0742e4540740074040a07202599551201c0900b286103400d07224002e412380095503241442d25 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 682575206 1250 682573956 682573963
    0x40306110c010b1008150d0816051002030c091e15250f03030921050702120313090c1b0506011d0c030f0726102702070f0f05 55
    0x1100e00415440c001060219241c603e0380701340e11240c60b0350385c0380c60f50340c52502064030701350034466040d070261494076400c0c00211144000c060000300c00d0345800c0300154610300300307180c45000710a1480003030041c0b0800c208000303410255007100c142151035100903d010701080030800b00d1196134940000100815103c0e1612080c01041076500c840c24280c0c200002c140b03e9807a200806074020407025003a090300d000700c0d20036000105035034011803401103160a81000d20820001000c0030384003185c800307d20352003980f9201c6840c03692802c40902541c90401d4613810b1800e040000c0c01683d020b9560358051415040c410300b940100c120043c0c114034018501410b065598000c00d204030512844c0c0c00710740c100307900c0042012500551044024508586400e40840c5e4106001480b050401c80c03043c4840101d803284216540b901400b0300c1c1120014108440d0303231303640312003590829140f844101c03c10001c040c10a4003841e035003203129000140c41c1c2d981072518035020401120080d100010b4881c440c0c0c184013010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 682576456 1250 682575206 682575217
    0xc0d02011b120e0a030209040809011106010311130b102001020f03010302031603051b011b08030703050912070201030207150e070f060f0509040e0f0f0304080106050a0b091504030611 80
    0x40d00d0703c030882c070041c2c41084070184d801c3c00000e42190420010400141813500a491042014141000b445100190a1303103800703c264000c0d5410000b4490030089400c0c07020f100b900d00088040140010509c04012600003584c40c40c160080041c50565020808480100c00c243c4030203540c02550707134800468604210b5082800103a102c0c0c001c0c820b504c3c60042c035081c008801c69a0150290540c407180e51a59410784c2d10040c211810b000c5040355501a0700d9031007850612862286061036102d040800d001400c075040101000295400100d50141c101840d40951f0521682440c01607520411460050302c06440e00a98000741c50400d90f84d88070701540803401e00241d4040c100452030140d55500100c401042b00528000490710411514a103420640c10140703030526034100b16011610500390140c540300709040b42d1403060304040f03410b000018007801481e006000441e0940300d031a0410207582c450b40f0614400510900003054155840f050140540d8011604006c04103c1240342210010003079211 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 682577706 1250 682576456 682576493
    0x501061211060313031103190f1d010e040e0c060f190903020d0605060105120405240c0a0819091b061b060c02340f080c0d02011b 57
    0x180301d01c1d8146901501c0c8200018240c0c00340c00c2c41039880a54a540007282c084031180403c0000b86058803040300040c3d1040d010ba0740eaa040400ea0348d4005140451000903415101c180d1103444c0f00903a4808110780801e00c0031100090704013552000d0034504000712524540000b004145140540b10040140c260800e403040008400152540c0c100c6034035145010096120078160074400c042400d82c0d002581c0420117040481c600000080d402c2201c2104503000ca942c0c2e803002050f0780c041900303401400400355040600c040c980c1003185c0e919503107024070108034082188040014102c0c1c00d1a55800c261103810900812545070242014803621012500007000039041c41c000145e020322a0250011040700864161007461595540801070950030808504521903101c4611020091510f520012000080600301c91406017004c2c8038003000741c2c0d006110310305050504112000300800c01100c00c3c04103c0382001803101a200680328414214005d03040e82541075020000c1100c45000801d50307042 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 682578956 1250 682577706 682577723
    0x9052703160b01061103030108061906030516030204060807050102190624091a060d0e0c130e0706020a020d0b0603031308010f05090f0a110d0b07021b033705010612 72
    0x856041c5c0ea40c0c0c0703100c01e200b90481d40e0302440020345200c48400003020644c0b0344a102041d42030b582d442c0ca0380780045003611403243e1550b8000070001c500c3d142c81038a000f8085003014041062510002035154a20507003d0450307050b040140804008144d480003c00c100000c04d544110440074510b080518214010851078078075050313a00e48402c1c8215505018184010105403614805000c1030016007002d526402c0700c0e00c6104084032007a0313240004800c41d02c200c80000142c481944030f95a2500076280c0c000380954000c0300025015807a201e2000311180e030840f00340c8001d5290310300800e1840c07040015080115120104c007081d51141034000081c01d41c034020081c08241c503030707604541e1078407060070010216510081181c00091210302b040c0c0c414680052000e01105195151400c1504044401c000103801841659441d00c102e100201c1d040d000a600a1010600c00c030403090121a003e8202c0e6400400b0361200180d00090245402c10035a100000340302d040e95541040010b02ca80c00812280c402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 682580206 1250 682578956 682578977
    0x25080105180115030f0f11040f0b090a090c050607030e090a05070e03060603062a042d0e04080904020c2a040e06280c02030a0909052703160b0106 64
    0xf8818000481643d0f00440c0c048811000d039520004128007002d81101c0d141d00711003143d00259a240704146022903400c10200b01c0c7c001c04000c01000a0009240f01100f80c90985078002117452404000107075001903a032030340d417451982400d0324521103d4800c0e50b40250810104203034808503401084c0600c0c4561a07a60035115810205915030000720b54054140e0312460000e088050000403114680c2140300001040810913140c100490b803113030b0007a103180588221592150b100105d001c214110403d00c4045e201410403c1200c0300a0020348050b1284101150032441541d495044603603821444086926820400003403d4030728a0f0300180085a5001c40d51115840c1010f0098464140303110003d030800f681c0318100380319540301c001405406c180004804000b00d2260344990505081142c0003075844100440004140900350f4000079074050411090060880c0e42c01c21740750700104c0141e1041c0c0c52003241503101d4070f540110040696100c4060008a051004030750085040e80c0895035010400f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 682581456 1250 682580206 682580231
    0xd180204052805060d021807020c0303040f0302060913050a0e010e190f110d06020306030105072607032903060f071b0f08270a08250801051801 63
    0x8a240d012800b44a541c125011902c001688010b5121200030100900d08585402281e071449107200d44240d40901c400502440e140c040290711807a88040f80103515107410124070500901051000034041d200200703c60a05955090b4092034001c03504008218501d00700c5804c0c4042c058400950b140c551820200f030f4105207000c1881d242d4070f100301101140303004203a600c0c8038003050030007025280100c0400701301805544400c02280e900e030080f0380240e103d00f0080c0c01c06084400145c2403070140f14104420354405100302004607103280d80f18034a08115611041f0540103481807a08840b50b1007460241c01084511070103080092210540480b0310307030b50394144071106d044030a403032038004103c1407090000809000c5500827165846501a142c20b5442a9180e404a030044030512411100c40311100c2c0d607852140e030301c1c80c410030300c01c5aa04400b14a00f580a54940111201d821b40c01c0d0039001048500400c40e00204001b414004001c011610b8005030803030105182440c015240d500304800020034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 682582706 1250 682581456 682581481
    0xe12070b0a112b290402210405120a080708010602151807210303050c030606040e090c092502010c081305070b0409061e080309010c110405041401111801050c030d18020405 75
    0x210a02502c10f140d45007004c080000d68410081027100d407441429880000c100454014215068098031492580e092110000d08003440580200085510022112512004d05801a0340110398051010f0024051000706402c010880c0c0200032540c121444010b40d842c1c0d1554400142d90107580c080005172608154250140300980746541d000b5404d01c018402440309000e201d80001d0b101d0b0454200c071030190003092400303508403442105501d01d400b51020010900c2080c02d05021103100030089000392070700c041c00e60107014207504000700303880c41d03075800304901045820094402601c980f0b0725281e44100040207032820340110300b8090300303801c4541c44104c00442510152800d0001640c101036840d00111904080040152110303800c0c50850356040d122845114040e5010b60300703141d41c8003100c4440c03e003964408004050009401c100b04400a612100c03086141e41007480c20598034800c1201c65403440c0a4000001036107881c00b00d201200c291081e00fa480c01d5813007075500b13000d0303643c58040480342d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 682583956 1250 682582706 682582717
    0xc0c01060b03061e0612190c030c0915090306060e1f03050c04090804090509060a0b0f0306060d030302120705030901062103080a0e12070b0a112b290402 67
    0x400114541000d02803003a42402c0c8100203901074101406e000380f040d64914400010b0700e200a6840302181c40d503004800358040e8840c00c0c040c50509204009018000a00c16a024842d05821094142d1105440d0f0b108107050402950800001e200c3e0584840382c0960000f01a19914400107101170010901104640304100700d9800c8005803000040607400c0c0f001411101404803868201040041030a000e1440b80302c4c000c001210043c5250f09e4009008412a020842080c1c4070b1040c490790700d00c141d81c0001d901548982c050b41c8480035500145400d030f0190203038500144ca04038414007000750403540800078520401c2144003e001c101c1d0396a001e8100d42d41a011204103d808842764100424044c00444e500301e440b40c100001c0e00c84001070b06505144070141d414902e00e100042c200d040c020140041034112010820401a020403102c65030070b28450f9100c0005403486210038076251034415541000000000c00080c403407003030b4090303412459004103407004d40c1b00e0044941c0c04100e0308161003036030f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 682585206 1250 682583956 682583959
    0x9010c022103060f060d0b01090902030c090d06110a020a1b0e0a0b010908010608150f070219081905090108070905130e0a0f1a0708091203060f03060c0c01060b0306 72
    0x115000d03151111140703640020425074110140041a28254031030321300030080c003545040009040d59840000619005c51a4429140d0324014000d1001c07110b04801144e80300c40b405c03038441e401a401c0d0f150820142a2004c1881c0e001180407034211007403500030500e5800ba0b48a00c900090349603c540b41d00c0c038003400034041c084101001ca000103507a101035a100c80d0090300c2c1410702c55101c0381e4a4061301d095461030740014445400100d00800820a9403001e03d8000e44250500025490005c000030340d1110f50299109050180a48980510110800301e8881d50783d01500e08010000056026013a680f00107440c6001944000001d82950702c280310382019140c0040c004840b0601e02070800c4007901013076604540070b0040c40654800a50900902156a07201c1d4149844000107403140a000845c001e218009114202c41080031203003011694446000140742c034161a41c03100004a0700c10f1406a081c0ca4140c46240203019003405080060004e401350b910080c002c46884200c10401800b0039514035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 682586456 1250 682585206 682585243
    0x11a0319032c101427030607090f060201020c0a020d030903080307081608090a1209091505011103030f0708040c050d050a020901090c0504090542010302041d0613020a030509010c02 79
    0x18844e00000c0740305c003012003150b408000d2981020001904111080c0c80710740c04200c100c5020030021505c42103034002842e45000847c01e002c24075800e5070301d4440041009202c0e002c0b002560041601400245002c2c64014601a889140007440500070080945082c07103074034545800c03030000900c03910003d071241ea6410003611b81c214159403405c0420050210100a01c151201c0108001c80a489030b01d00c0c6007054541903a28502c1e09001409803000c940300340c0c4498104008001c0c4000c00401500e07001419890702448a0352182070080075141960826540300f400303a9000d5041c44000100d07800b41900031548a002a6a1b842050701164802508503010034028001005161200d41c801c1d0790000340080901d00b070300044801c020b12181d5030308090f09081e9040e218036080101d80e0017004160f0303000303013000c615147c00d112181095410340900f40b030f00c40d10b90000040b03442d190740320444044101d50800b5034940c41c100e980540509001c85030409030350700e040c0c050050184002007925076200d110048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 682587706 1250 682586456 682586467
    0x608012403050a0e01020d15090e060117030714011e0b150309160b120a02120c0904150b1804020301030803060105030a0b031c02011a0319032c1014 65
    0x76405804020440c43c02e6503540d0710308440307030b84080c0001c0407070106503540040e001008220b03c070302301406a044000904d01e0008030200e800707400107010381512182840c142c01c105050442c130385544500744008201d108000c1600d0300c1c4a005400c190603a180a8a50700d0303801e441300c4c207000d00302c0d414201382076482048964820703d03101c4100010b40d003069080c000e403032902107801c0c40000e20214039403180d0300704003000650700700f260302082d04030740c024409140a5103840800808080b031020054414200e03001d0010301c0718100e5440c0e501004203440d00d50b4000c02d4242e602c580309440d680040804151041c0c0818a203041d521306803088a05070381e402a410f5040d0b4841c02c0046590b90401449120400d586010100c4203540400c4845565030300c1c100b004064052088000b402e642c00000c486541e10b1205495260030340d404145810800c8040b8a00091501c0c28141290212200840d0b20b841c0c01340c030321004103840c02901040c020542d06407203803205031070b04201c121078800c0c401e0309600d44c06005111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 682588956 1250 682587706 682587779
    0x31a03010c1d212119080603160e0601020c0d0c031b08030d0c031407020c04020c0721030f051c0203040c0518060405090a08030c1e04090204060801 65
    0xd6a040701c0003078011007040380c0c0e0740000381d4101c00f182c01d1640503034860102c0c1a41c0e06a00301100107105a29043c03141800300b01750003411002d103440d28070000e11031003500240407910104001e2100f9a517a800c0441ca699481c201c1c1840c2e404d05482c494018050303c0c6079482541050000400349942c1f1544d800106895a01c0b11a0b10b80080e40c070460f0280c0c9290702c009101c00082003c1c15400b1310301d41000030751110320740021b8111944405480003181c88482009112900810100d020110607076000d60740300e0b51048182d0034165a80c020202e02c540103122401c00658007a040c202080c4a9107504070f490311005001e9a05010340403802e00183c076052a0904005416009160014031480040d070b9051749540005101300e1100721044403000c000000c1003498a428000c1d250802008800340118804544814010307102c020401031003100c0026824142810170307201c08410b060315a10480d111900c80113000041d40c494440c40c000a4004030020640c2201071111084051810709900d0344d41c8440301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 682590206 1250 682588956 682588997
    0x414071409060a08030301080105100f031110020709110409050702030c030a1d0d1a06090603100b030a0507030c03030f0306060906030f06030b090f070e04050705121c031a03010c 78
    0x140b6054200080d10400100c51004102860180c541c0100110315450b00c41c0d40c2c1c418031006030748243c0040700000c504101144282c680d5030800c0c081994600d4450040c031105a1400c58164060340c1c18078500b03a400383c280102400580b054810080b02840a6120340c103040380c2c1c9010724000c800050700300b000300f20741d6640514600c100c3c203000c0214010b078038450b0301e00003043c895a0901c1511003500640c880c1c1d80040411803865032103c01142d45100074103000010950301c410030001007074076680e60b10700d200e4295810043d075005150b2200445241c0303620b9141903003d010711840200e01144030041c503c40390306d0103030182005499050317442c5298039103031072002c40151850b03e00600c265956007402201284242c80f09512031a00100240700c460705e9690711901d0591180c0c0701c200c85000a00c24400040c9020030b00c0302c1125002c841d40114895030b1140b890070406814000442d04c2e0301c0c11100c1c246160550003070100d440c600c2c0481ea14141c11007081c9400d0310310114024002549800b025001c820061 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 682591456 1250 682590206 682590211
    0x2060601051c140601180317090d02030a0f3503220c080f070b09061e07060b01080f060d0b0a0908070f1b030b070c030c08030f0414071409 61
    0x801007000b140a40351040c00c00c407510a0480d070f07511001d200401c052942c0040c1d45244a12508502a240c949581c4402c503032100b035400c04800c180b00010364a81540e8611090045403500242641d4002c400d034501010031300021441199884d42590040c0030a107411012240000e00f103060324040b01ca4001401c500ca80c0c0001e00d02c4070300d100d8504444103010240e0b8081c00c03030684164000b415450404480710f1510524401c4613000b58051002440003c0c80c07241550307890b0900743c680c1519400500c060410b030b42481c0d01c45101c0240701080032000e009250300808602d00d13007a00d40c0d11494a940082d185084411a81c00360082840102c200000c1c0000000ca9800014040002241602c0741d585000c07030b600035117060303030b401400f119080d0500c180c40c0c46c09083c0081504442d02d1061a594810004d12001404141440801c1d4104014103002d0704c460f01446512050099072468000c400380c2e15a41c05803010307103140d15400740d0313180200340003e00c040c00c2d20b580c0c0420040d040620401c1005c0038500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 682592706 1250 682591456 682591477
    0x5011a07060209120a0320031e0f0c0d09090c09050108040f03031b0c050c030304061b08090d0b0a0b060f09041a030618011a090c070c051302090405090a030206060105 73
    0x4030401c04e1203a8420320596041e20f01c65075805401110808040e90744074074844030885603400811449400c0301c048060050031803e6505606d448500d0186682024016050315050380c0c0034500e010031009034442004070555441034800c2081d585207500455030f0902c00d0283e103010a40003008180030400607030380042603a10030b24001c260500c4d5210388940180300103e211000c10541c1e0300d00c034200030040c8501900d0300401d40044d400c10b890480d005220080401d10880b031480391100b02414080008121420110050085500e02e0900e10b0410940c80003100d0703001042c0d29280b00440b86240450890382d00080c81d04501c0c8c10100b80f11708202c0201030b08404103034100741e1040d6070103180c2c8040c42440d02c07608000c8443d040c880751109046094a42000c40c50b440500d484100d10b040e0741d5405440341d0083d21009686449411a00c2e00d4107180c507103500082c1d80100062540d10410681da0001c0c200c2c00029039003070117251130380210903070b890524280090160308130350001091540b10b43d002d400075048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 682593956 1250 682592706 682592719
    0x90c02010b060d09111203090f0306130f06060f0b0d050a0c0e13020405120109031e021e100906060f06140301060302030c070b09010b1206070f0e210106060305011a07060209 76
    0x15080056200c81c00c60500c46c51a8101103100c1440303140c803550342005040c099010b0015454200c40034000410104030003000c0c1011740341700d001030110b1a40310802416140300b034103c1450310340000303482c1c603003000a500038a030f41000000303050100c0c00d01034580d00320701c80c2d1241e4100100d130a0800142d004000380020905900b07100009a65071201d60383e9044602c64800000e4402403810300514805400110443c03540c800b6a030101080c4d4001000d1310030540c1c030741140796841010035009040c00c1030202c03200d01d81c1d07040c2040042030000c2d40d4414021101c1400007500080d550704c00c00e8034011040300f10102c01d54000d0004100b058066001140d000d0040544507203820341640d1074040000b026180a6145c0c3c0d075583c9100d406090030080c0014a4611100500c010328010702d00421165406120100300440907030403400a071114403075a014a96140c00c0090300045034101d007402801da61081c240000d0622000084003004480038150340d00b1052681e514104903521446e001c1e40c05508059000704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 682595206 1250 682593956 682593983
    0x1081c1e03022209050405010c020703080a18080d0207140f0d0b04060204030c141512070f050f071b1a070b07090b030705180303130323030a09090c02010b060d09 71
    0xe6401c0003c00140038404000243c034107050030440d007101c64250422082d5030000c42c050011408640994507900960701d804a104414600c0501000c04d15074000d0100b403058540039050540c011038107205072980159050300001c4290108080e08010345461031b000b03803410300c0c0c83d004591794034201f40c1d1050085601601d03080e960303507406404c2c10440c0d01900c3c0c1413a0030500c3d81440c0c42c00c140d8014503000c050301600d0800c200038000849280020340094103104031115580026030292041e12041442c1c082904d445c1d140364280b44020030048260100c210b01682ca021a2502617122500410350000001506200300c039515920004000740040050108280c0c00040e402880c100451152021b070b41c406071105800c2c6900301d1200c581010a620a805c01d00c000d80030f056803410b0405c11170350003100070260350414400c804a00d00341030401c050300303001c00100d200007603401030580d0742114210b0030f081081c00f418820403403c881e800c41409500000420510601c150789821100b54140036450100c41e07070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 682596456 1250 682595206 682595257
    0x61a130f03030f0e0427020d05030a0302090103150305030417160306020a0201050f0906070c030311030a151d0105040b1314100f240c050601081c1e0302 67
    0x4006075004400060806007204625a84100350294402040d5003d02440c0c0450001888545220108600f1403000c0c10300c80066682e51520714441e80d40180075a5030b125a4000c00802950000031713058017081c10700c4416501e1603135100708201100e070058003031400c1c00e0a043e01e83c02103006c0f4002c02c104910030211100813032400004200c0041d4410f68006136034841100000c0d0a40c1e100804048050b00200100140440003240603603200400340b802d00008895880c05400405001040c994503a101000300289000c3c9507105c4500c0002031240d054189586041c82500d82c0455002060700000000c010017080c2020740184c01d02c03140040c4014904049104804125546400007228100304c0500b84a203c040300620f26001d8040044508c1955081101c030001c041610354040080d2141d40d6641315a42e44190b50741e00b90f1550003030039182c0c15651506583c1e51030001640c07500c12810090100d11006000e81a05203601d6034005520034684940c0360140c000f50020f501c0e02074100e401c0e1018003581c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 682597706 1250 682596456 682596479
    0xc13030804092a020c012102070c06030b120c19030f060f0c09080a0f0206040f060302042c06010f2102030a0b0406120f02180c0d050604061a13 63
    0x41c001141c40060f04040102141000c0141d00701a03d0003411034102c440b4603030b68040742800c28018207003010f00041c845186d141010480c16403103000e40364800300342c2a0411030341c0c56650040b00ca960785c040c4a481c271100200000301091003014041ca50110300300e040c5509001c80d0075503040c001c4d90320752002640c0d00e40b02d4800122519a0860340255140030101410040d8031504607681c0107843c00c0a03a903420642482c7d40c451815030081c000e100c00f4203c9208540c2c81c00c048401030041000281c441c42c0c0d840501602030740160080d082e008602340140caa180c144030f001599080c4a52010803851b8681c4401500d002c7c28945e0780700104034080c110a0901c41c2c2c0c0002d50b9250554484005a80f4038000190204032000c40545a00c19030030031804000c3d00c40d0034400810a10703040410b049172844075200041c2645085c0380342a105101075400c100c2c1c0e006454000d0032250300b0300710342400030f07036507650030001240d02c9801075140c112900d807030180440c000680500865800482c82075045a00c0341d400010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 682598956 1250 682597706 682597709
    0x20d030c020312090102030d0b13061e0b070807020907020148020d08070e09072604020a140102010906060f2306030721050f18060108060c13030804 65
    0x426600c0580c901141400c01c00103516110000c105401c160060000075104c1c4211490041038581320b040d0b03c000340d070f142c904a080c0c0c540444800c1114642c0d03003105041e0034240024490304030303000d0b00300040c80311034000440348850f6100c106213140103215420040c1001020b4802021923503900ca11121760310303030318004000c00c8a00d0303250f89040c44880c40710900c580200389208110298125501c1010781d0300010013021450351404c1400c1c640c0d07504030f401c4581c1c45008a55650001c040c100f441549900300c4a0500c1d90314490f03d2011a40e04000f60641e5440400c2d6170094010340602c0b010030030000d940c0f81c440240c100500c008144000c11f070b295182a980300c2d4014000007038501004001a01800e5140f9410b0b038003916103209500b00354400940c09010040c078010501124641203120941e807500700f00215013510404014500704000d40516410049542400103202c03003c094892804c001456812903a42d00001c0403250742e2081c9030441e81e00000410b003060384c0d21480c040f0014a03c03201900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 682600206 1250 682598956 682598963
    0x309060f061e060512010e04050f03040f0f0b1207200a082107170606040b0d09030f050702130e0f030c01020d0b0d021008040302030c07030501200a0912020d020d 71
    0x5926140c401e10051400d0180d5100f0401d21108210340b0980914900c842070440d500391034141c00555850030110704000d0641d68980c500c0c08000b5020940284803603d20f000e5505d0b0140500e4031075203511004d0464421081e610707203c40e20900000b10481e2107480340e260049050f11580703070a40b48a408403860006030714011203c042d00031903c0b0540407041c4620410703405181741494958102414045e000103a0b40e801ca2141006c690001850707074444030100c50041035000119941c4c0c0035070004000040260318011000210001c01c02c10440d4400c0307096030f45154004180044112015070b1540081c160741000d075465020f0300c086440b0280b020310281800355a00b1001699403070404c01844221a0040500d40c0f150407040042005078031450f0707449100b00903504184500d0303283c5041c240e20358001c00421440f5841280000320401c2010340000e00c68001040e0010320700882d50742c40d600c4e6400b40c40511000222207510411180345044441c900c00d90016240c030070703014002d070003150030301c084c200301038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 682601456 1250 682600206 682600229
    0x31c02071d16090e0c0a031401090e0c01141b07051018050901060f0f02070306230c03010e04080a1404120b091b0d140d17010e06030a030309060f06 65
    0xca110303000442e01819401e0740e482d111002c54140340307a102d001040600010984000490381c2200e190196124849130701419150301459a5a1007044000c4c051120a924190244000074840c030f50040540142100008448500305144000f07003510300c0007440d02c0c1505a02c1500400a881d4540c2c61140e0311140c45a80c500c0d18904454103e960900220b0388058010a508801005903035400001045002c415107010600001151003c1b40303000f41c5500082c001601d4070449044244501b41060700742c00f241524010705940710703403201080740030901c0742a000c0c1d01000b0000e00011400401841030045a040481e40100c1d680d003034800d80d400541150500f01c801850040038440400740c459030010796000140038220701c4c221044114038031403a0b01c0e801107075002009010041612a90741c45501da91080320100c070f16034507005119031140400701078040e000350004104510a928045d101e11000380040150b022a0b0741c1c101e0040203522030980d10745030340c2c0742d900481c3d42d01c0307000705001421401c005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 682602706 1250 682601456 682601461
    0xa091119110613050604061d070b0a030e16050603090307080d050709090b0f060f0409021602010f140a140f030a0603020f010504031703060d02031e0d0c02031c02071d 73
    0x40900d0b119000e405141c02c50440301d40e038000148005205a441030384104081800100741810208121001034042c501d4001c40c0c00115545900c0ba01801940b4250368080c00a402840341560700c0c1c04200c00d00000c002030ba6081071001d4200107004581015030070003205d01d001d440e612951126000030840c3c2101c107840f4801e001516902c202d5240107400c0030141042141e10f10000a80c00241c4403050328042c070700210303000e20b0460946050b9001001c407a0303410740d50760900ca408400540c1c008030040780412012101c0c04296882801200d03880d00c0240d481c00d240030b4041c2015503105a0800c01900140804c000c5104400c50880c05180241c86060000c05c0f902d046204201c810012201114100f10f02400f041011074140d580380d110408000407029625200c1ca008502d4241d0844000ba4052140541c01a18841202c15078201ea1b2003040a4a50001c802e04c4100d804e0358003424081e42c07642c08881e0090703600301c80f444051224002d500448801c2c0c0e0340c0311012140c2440119118410f803074078404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 682603956 1250 682602706 682602737
    0x1e231e0d08010509010b0901030e0705030304091416020706030504110d050a02040c0e010909020c070e180607050a122c0a0506010509060a0e090102070b0c0703110c0a091119 76
    0x101d550150a0498084002c3d6042502503402405642c94060415403180081d8190b6030702401054080c0002605407982c498031030346030710302034910380102c0300011802c000056010071440b03008140142e515809006100d00c2c2c0360080307011741000340042e00c01001c90301e00303038006a64410880700040d01c00c0000c0c101c0d0220b5801044100d90308084102c090010304840d4511581e400f010f10401d4504090006072144080c980140c60000c3c1508000242190322090140307103003c0400031000c0c41c1104046501c0341d9105402107a150094504270300215002e0840f00d0025480d540200c1d00442004804a104800300910035041200004801b11140c02c000401c00900034107005039409000140c800942c9800c0070008140f5821413031040e00101c030400b4001c15400c00c02034040b54111500034100300400d04000c5900c2c501c5500100044020988110313006103d482c001c02c1400512000a04001060345403480700700c040d00d001d0110340100b1f0010400380350212650030141c0384002041da40d0b441c86844e02c81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 682605206 1250 682603956 682603967
    0x40b0c0d1e1805071809120e13180602090d020d03080a0f06080c060c0f0a03090501030b0108070c0b0603100e060f100f0605090604031a041e231e0d 65
    0x20302200411210401040205800240138402ca607a103100307212809100b040d5410091100320380040c5124101d0120a040980c4007111480c01c040c2203c101034260041c03242e01045401d405480d84c0d02c01d001c0c10404c4080740070765010304441000541038110a0b41c3d83e500094588109002c200c0108080f1018000707100c00e584500008440317001e504209e01c1d41032004459403441942c1001e441030100084428400e0401d01651040401e1f24044400d10105880c01408207c6107006d0135000074035159440e10344e0343c4101c001900401080c0c4a2000c04012034480b20000300c8001c0c080e503014400c2c1021031201d20700710702c01e2200da1999500540b00e41e0900d501c0007000c0604c0504011043c041c0200c00f4449801140c9005c01100c0715400d0507030b5203012620101e22315004561000d08151501c100c021001c0181d4450640300d030b48100329840040b0200c140c41c10440044180c003900305074448411180203000561001c0c085943d89085406014142a50050300c102d500c50904c031036003103d130901c05660b4011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 682606456 1250 682605206 682605221
    0x20a030f060b070b04080d0b0d030e0103051b030601180f0909050f0c03030f0702041103040503030f06010302041a090301020d02040803040f05030604020f10121a1c0209040b0c0d1e 79
    0xc02e90358070703105160b11140b9000c40301038009480341c031002400c0c407003001e0550f01103510000084c0480c80b964045043c0508200740b0300c640b882c0031908100c001161040c0c4001c5030600790b21200d030b0341410364a0f10001141d05918898000045802030713040415203108c41c0340000c0052a003081c02056600c26440c02c981443c621800794441540889080c1c4003544d40070003034500081003074140390345a60850000601500c4440d6203600303419400400d11080c031802100551280b0000302001c20320b5250600114102c0c0314900c40d1440402103503100e00d8603000c5c0c42c40240051140100058200002000014202d80c001c0d440610aa0700001d000c00241c0000101900101000c901038400c80c5400d0f00442c4003581101102441100108010080540503250841d201850715908100d180350b02031a269945401d4030a071442a200700d8400220124000c00181849501920b0310006441c2c80d583c088212801810303960400500f40045806003c19100300b503040000c960340c14a99110031241a011101c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 682607706 1250 682606456 682606469
    0xf020313020904061103070507260901050a03020d0e160614030a050a2c190804031b03050307030c0b0105190303140c0613020307270f0e01020a030f06 66
    0x6008200c920021040e141031401d8040c0e0b8550410b0f501c0d464488001c0c102034151000f000c0000c800d0003520740e4000c001e055243c0c8a002c484813030100190413521000c204202980b000f03401000250010351149010b80309900ca9401c000d42030022001e45942503c810b2005001598042e88541402c603282c5014203000b000c25060030110301244014485803488010250440c070b580320004682070300c450398840170034145e59125030703041d94580c1014402c1c441c0d0200e0140e0501e203d040401c2080581103008026100e0348507883c10324151456503a996a02c5901d050300301d003011100d90010100b0010b04c01050024841c2e030b1070004542892611002252043e08031601502c2d1700c0301c1c41c19400d141f0311005415070346c041c14450441c0051441129291007500c400c10f00c075001d01824890031240324298007941500c00c07400d503815240c4030320710507050700f0034101121264518181b44155050700759100802c0301e503201001282c8000031840c2682a640240c81c2000001c0e03540001510025803485804050281c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 682608956 1250 682607706 682607711
    0x7050a0f05010c110d180e0403080f01150206060f2b0606060801120b0a020d060f090f090309060c031803140601171b0d052d010203010302090712060b0408030703030f 73
    0x4504c00e020340d1150881c1c421400c1c451840b80e1038000c510f815095a004256003034403195545014a4010b2501c001518072040d2840300700004103241c1c13502c190b4851004410b0303006080300d554000411903a12800c0e031000d41c011070710f00c1d620040b200a27000c1d00d6010308951107940090b0f070a02e01c0c04400301c8116910200404c15410010f0101d2141242d20480072034000600c007200d03482c0c072007000e002842004145040c2d03600d454400140c5a01e2004948200c0304c0c00c2c00e0810000c120b41e000c1c0410741e44c400c81c0040000e0744040082c02103a000e036600103004c1e4060316001da4140b90301c010b1150181e12a40050b1051560604407408140f02040018050311a11068114015200008555504821030085010850713040c510400b51551803580001c1c2e074101085a62203d141c58591855030b0050360390001d80d9000c01542d00c84030340140210303030489a000e04000f85aa032410011a002181e00c040024160b4848400040035210301d40a400506a4031020b940d41b80c000e454040d044418400c1d06280b13060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 682610206 1250 682608956 682608977
    0xb0c0f07060903020d06022212020a05030d1e09050402072a080d0f0219030c02090f0402150f0d0606110f0f060f0702030d0203010b27090c090607050a0f05010c 70
    0x8492481030380156a1001b4090b840d421904990075049201c0e403101141018182c9001030201c0d01c080c001c4031090300a441e01e500702620f07841815125040e442c0c0d44808207180381d00a0412002c850890000302c00705190555405440700c00040c01ea0784908016510200040c165804113804041e2840075414494901802185000003440c0c440d0ba441b0081010b0100c3c0030801445280240980ba0454100c00201f80d01c1501c549005002c115200c441617016004540005083e2025040d0443c01290010007000003500c0043c100d001c10341c4011891858103106003c235120f200001d004680142c5030a440d940342255400c105986007050401c403c400b070340c1c080444803200b1580403c82c15005030f025032181d4540c2c0c0e00e41d4001c1e0f280d8442c40f81c400c00043d02c00800001c0401050029000a00c000032501c0d40b072035000400c1203ca00701c034402c3d20382e00401e80d80c0070074000c0041100800d1003210140542e400c040d85a00d800307040c130040010507241510559010410400e083c411080e0390940c60419840d1003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 682611456 1250 682610206 682610209
    0x1080402040218130e07060914091e0906060f040b0922021e0102060106030e06130c05130902030f150412140426120715060b0c0f0706090302 62
    0x5101600207401254001403025920b03824030001143d081c1c010380303006907003c0c0d445010030060408800000203801415408511a0b12a151110460b4249858030401d9490b0750200604800050000203000c501722244026a02415001c00d219041c400003030310603803402d01c042c4074080e082c0601c4644031b1481d110140328566100082d0740d800c07020250f00004204d0924440502c4c143d00480f001e5481000f819a10220016001c0b00c6041903000f80d00b075607220f90741c1d40410340a0b210066070300e000c0d42d0410384c0050700c03540c110b101003500301d0f005448640b036440c1d644000c81c2d056407070fa04141c1142c41e00c0300640d0f401c0d41010080010354002080080032100a00c02d0b8418040304040d100512512020040e810f00c03a00c10681c0146541c100a882555241c0d00c40200c1050f006039400c00106405e0004540d00e03480c00070501628003102071820519200440d81c0d0710321804500f12990880c5542c4103400b040084084000c2d0035024001d40003000108081c8013841d18000a80d84081d0820141100a2005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 682612706 1250 682611456 682611467
    0x90b0114090301110f132705070201090219050118030209042604120210090602031602010504120803060a0e0c09040e030d050c040f08210703050d0609020d060603050601 74
    0xc02602a4251900c2001001901410340d00d00041140c0101290b880006640000101010545030b911810b0295541c09000c414501e41450b200c1c4003408501103082e5400190000f90340b0851303d200002d4480f446900140040a048403054000d100c012028042940c0054a900d171100120940000803495980054100c03900204000c0280b420482c1e194401ca9101d076030b102d201001200d1041d20386485000c0421004070b032800036441494400c400c050014028500402030b140b00c2e50155107001d2205944088004540394220f04000d000c00c000200515610300d00103c0324072450185580b400c0020400000303941580220004000c0c50051010310881c050840e8042c203000e85e00800c00c0302c50121890305501614804600d001d0a00f410010134414034001801661010302c580c0c5055611030341d101c1d55a5809140f51451032440203001d1000ca0a80b501410300b49200b4a0300614004400c040c00e81a284554004500c0a4011414401007109406220060075188c50200450324142c07000800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 682613956 1250 682612706 682612727
    0x1090204170604110d05340e090a02010806010c021203130b28110313050312041d06210a050d08093f2d0a1101062c01090b01 55
    0x8150b241c5104001004414042e4420003100500140f0703409400b00304403040f800411103ca07801201c020004194981c08d044094000d051950007010714009543c01954913400103495107040c014403140350001603070342c00e80300c68021500304040d42d01d401b04207545d000004003681152501802c280301c4800d90f0307241220720318421b000304040c02500812402c1c068031111426048414103000000301c600140703040e00c0c070403006c41c2c2d0158222642800c404052010b1030013103016011009201070034861a82019a8000c0e8100300010000c0b444107203d800c0c1011004002c00e08008685c111803910014480240141003040080e030901c406c1c1c5d890450f81d01c0d0789900420141081098491003644010924900310141030020540c003a212031041071141100f940105012020b00001802041d80210203411442d200600700601c0c2030401d1078001c81654110020400701d20b030766580e9940051000d00140041a0304110740d048e551000520182c039100f0050140c2140e58800e0400180f15070740d9038000741d80311 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 682615206 1250 682613956 682613959
    0x1a010512030d0c03090c09050402130203010f0306021b030c150708010e0a09050f1204050f030a0c210204090804062003031618090509060106140313020f090109020417060411 76
    0x440440c444030a40c0200a0369102801b00c1c4880368012900081e9584102d01440c000ca8074014444588a01e0000f82c0c0300900880c000d9441700708040000540c0c58000d401407078505001140d42141149041f807031a0080710640006038006101050346003c1400c1207034019803e4a41108a981425120300d00e10302d001e000e2b80c502ca41c0c2d8506050174410140080860300c8003080c240c03013100d02c403590b09540d190003074040c02d8458413013545101586e1500060401201380d0041a4400705454600e0781107801e451104c24a58185000483c170006a50b140b049103955480307a90a541c4844c14500b0007401c0d5020044003542058560b0788a54490b8000415294080c0040400300d01217009803004035600b20006c0b14082e50780040010109130310300d1075000540b14002031b1081f1000d90b80d0310141211900800103c4a0003220108041566400340b030b89040f5080707001a00c02c0184184c0340d0042541014268400060194085000e1080d588192212000c3d44034040041c0046c5c00e0646410600850569005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 682616456 1250 682615206 682615211
    0x60102120f07080c0610321c08300f041e03080f0a0506010215060d0b0c0c010e03040b040b070c0b030a0e24010e0411130906110708160302191a010512030d 68
    0x403080b40c1d0b981e040f10500c03232801c40000c00a02164a4880400d8010864024010600440c568828900e0078202c92107166880060034081d01c031200c0c1c01c00e035404050300c26180640744010214400713162041c1c442010740300380c2e10303e0ba051616040700c1070000303c040d00a04a00381406e0601c04d071a0f90000b90b03401c0c1d003004545d81131096140d650010b025040440300080c140043c001c1041206c121305800317403120b455040000d00c607e140c0f03041090307120300c664000c1500e18202800140101d55650b000b41540d1882000403504650b104c51007d400307a04204c0d646900c461311020b110503070200a0041e8203501c40c501b0320749800078205034103404007030805004607402d004464000406108910480c210540405841c40c0315082c2410a0716014040482c8195115800c06002c02025100c99040b100c00e6a0080b454504215040134668020f00b21022305804500c50081d150380f070526812200441180310720080700010341030f40b40140745030a0507806688200e4826404140c880004000c0310f07080400d10000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 682617706 1250 682616456 682616549
    0x20703030206220b060f0d1a010602060403020d0f020115141e01210f0e07081c08010306020c0703060f020d0e07080a03050c0f1204060314060102120f07080c0610 71
    0x21561010381c1c0e0304003503400034000d61007000323004484000c03596149200c103211400360780701c00c4281d90701c0805603030040c0103a00900030258041c0c1304401c00361140700c1c0c5200116001002d4070850500305501d8000c03103061018403448462500e000c084500c080010f201502d2038540c00000080d0040ca0000c003645105031482d2040c1a0602c15503000800e2101c1d064410070051440c82006c3d9944c5c1c0181c0100c0d40248165596800074864207007550300c890906550316003075603085a503582c010750811340406034248110100480014601d00a00c02b511082c118010784500306d01c12280c054511500700100260815a001d0040030004644640b05a40608080c0d030703954100000c0c18a0304028100d01c1c07195004089601034108100c40080088640c9507406100322580c41c0400c2c11012820f48186000d40e001c0310904410a0100000c0c05000304020001820144603440c2c0a180e0b50164058100742e030099002c00081041d90b94021014200080140303080d1070782083c9030003a04420a01d034200ea000440c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 682618956 1250 682617706 682617709
    0xb07030f060302030a0b0601020f030c0a02010e04150b090f06031303141b0a03031b0207050405090c120a0309230d0206090301020c07050f180f06041b020703030206220b06 75
    0x110078001c40e800340885480c061203003400180703000f095510314014015201e800003d20070000c1030303414180721540544030700c4039036a0041d40d031032010203500c6810544400e602840441d654441c50010a00103810780d0f0385c0c0044408000c00f0b1483c2d260f007140f0800041c03040c8a0034a24440e105941903902d801c2003064034410060500c0c45001e03200d9518201005106030401050f0041401d510080c8251024440c1a107140004250042c0c0000d0180042c1d0068904015500d0305400c0682c00c4405003082c0c0303c1c802c4142011951074201101410060b80c000c112000c10154400e1909000340005181d407409424405221341e00305401c180c07103030302c41c4003244021000c0d540c2d46802c8030030f03010006000f150365002000f2102c2d15840c2602c50b440c40380088881032409428a00151082d01c0e40101c43c004c05030b650ba001001d600310018000030b0704941e452200d00b00b2040165500b940c5c081d219002400d08074076500d4024074080c4014a01140035005080810014801d47c03890541503501c101103c6103651042d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 682620206 1250 682618956 682618961
    0x90203011407120b04020901081f080d091e12030c0c0e0403031505102106080f070801050703110a05160215070212032818090c0f03090b07030f 63
    0x594101c21584401c0c00e0020a54001d190100e001e44802000c0c007204000da03040000300c2c0111100140030a4000000424001010055410002104c4010201f898551300082e181c00350152411003c50460a405d0109504200d007020000403241e1710745507200c0c00c0a0396115558660035004060294080108041020000d2180080c1804c044100742500e0181002406448928400030060390614408074a9061601c010030803400181c44400084600748280c540d030341300c207050107158559a060701042c6d48070180710442c0325104510003081d0090070070003003608540000d8040d4043c5403510281103605201c074016102a0341080c2044d54440c44440034403841d082d80401c0096015603d203401d03202907050301002c0d0803054000e54027a00d230160100d980036524841e03203a1502c441718403070700d812501d130884400c044140b1040c0c2c5014190f0060002c1000ba01c0d000783d0f00b014807075a8a50820305007160340526041e41c401030310324060000c0c1d002511824a07210b40501103008054845521505915054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 682621456 1250 682620206 682620221
    0x23030705181b030f04061a0f1e03060103210e030718020d050907140307050906061b060a050103020f060a090e0a150f060320042112020601140d05070909020301 70
    0x1a040c072a500d213003601c202030310828115170840d00c03246000c1d0302c0d44203d2200d44d041c11401c0c074050705604080d95030200b00000900b000040030481070001c2141ea0060720103201d0680207503c155001c1003020601c1c0b151a00d035070f503200c8050040042c1b400d0b0108055500103401e204407a104645100103031f4028070218081d00c204800d1a00c21403c20b4280400f0840c001081c01c1154481201c07038610800c441d08142c0c0387c290702c5c0308990380824440c012485601c3c00c40000c00038019484240d411007402c024003a410500f044428144041d542c030010400c2d42032001219081c1c1c0c00407a0000e1130290b00142c050070b2810b180c0605c03140e9008120005a200351130b94000e1003000d0180c80c03081d8010f41d8a9491000c401c409024000c000707400c0c40ba01d07580714007603640e4419407805c80701d5680d0b003054101848420b44200610b01040f0f00f6100388040c001040800c2c0509004401580c05802c1c0c41d030400040746448404001c01900a4080715012004035901191007020b0300d8130031001281c00d034803a00010f800350152 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 682622706 1250 682621456 682621501
    0x20304020d020d05101508071a1603090306051e071107180501090b030a020a150203040302091e01080c06070b04020a090c1d0102120a0503040f0b012303070518 70
    0x70041460f007801000030b00384c001c0800c036020a10414000344150408010315100f05009607111110a02075004c019541c020300c010004081410b2090052a09200c1ca00241c1c1c2607011803d1603105105211450040b0303540440c050481c5003a2902d41101000d0442c4001d0140e010010031070040040b00c1d40c00c0c844034000b00f0030140d00120641204d04900c1c01001c1c00e1281c6051545088d03c1442c0c82e05022503101222500144090710580c03a04c0c0010702281030b401450421030004100220050760703120b07041070103040d80c010003007800c0d005451413a03502d56068004100e964081400c41c0010394804080720348055018505a074640c48600c04600120755075080861241c0c2802c03d086142c45d4004010700507895841d0394240080c0c5900016a110500b9511040020600b001100c9005005400464215120350307070030f844100e10f903181c0c00c103980c4003030700007050310300f4840040070100802c0150b52440004c106c015108407840c00000500000d4038100c0c0c54901c0310010000740c114480d038200c840c40100c0707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 682623956 1250 682622706 682622719
    0x30a1a030106060f080f011214010f090f020405070c022b060e16120206030703180c090b0f0604050303031b130602160b0a0e13090203030d09020f030a080904020304020d02 75
    0x1200d03003000d0004d40c80d06124034006004040001e1030182001e1724181283c00c2e12100003041c07405a01ca107207043c910008048510341d240c4840740c0c02e00c0e036244a6083d0702401080e00708202141c2c2c0c410001070720009023140041041400c41d100150381d804070b01c1401624074820b0b01021708d1441000900c0007249100141404c0c0c504070200400d640d011404120b4500b11540f154466922034280c05c2d401c0b00f155030069004003050002030540d90081d4003030002400000300d90b0110780166550150390b02ca680e007060070ba454407660706502c80e0902482e41c4078880c0c4c0891740c540c1401d0401001c6030341d0313020081c03050802c0c075200c400d00f100d40d640c410100c40e8a582140c00806000b40c540c040656583c00e1064090744c0b034808002c000803101800f0742035600c0c04206039160030403c07180e801003000725001e4075040074503181d440403550010303507003080102019980903002064426881c010051219844551540603400c03c42c04400029611811a40603010464005807203465900214407c4000345078000d42002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 682625206 1250 682623956 682623959
    0x5061e0a030c09090c1d151c0c06030c0e010c0b06010e060d02040302090106050a0e12121206041802011422090f0509190803040521030103140102040b030a1a030106 72
    0x90707280e08120003d038017030010510166543c1e604070b07500c1d4141d40c8154002e00c550401144401c2c0e04101040070002c0000c0c20704015152048a1046010300540c5c00c41c0c46503404c1d001001a55014090082020914100020904d1810001a02e581c00380d9078014000c14450000940d142e00613926070b560f4010260095868040b400300102c000d5226000507031152909900000da030030f01c507001316404030300c06038cc2e907001c1590008144074001945000301e0f599401180c092004040808014101030003401b121782c0d4060501c1d03001e001c210351040b200c40010205a114200160360032145c0414483c4100c80910f81d194000360340e45034541651200c60007041c01a05000804240381e4200b100c2c2e19901400821403a22007003000f6030388000b01403010308144150040b19010640d0180a19071103400f440544200070044180d40f80b20305d22400340e0070200c0001200500500140030b80280f41404100003c45c42d0500307110802d515801700070554030210b5250b260440f000050301868102d10b400150080c02441e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 682626456 1250 682625206 682625219
    0xe010507020a2607020d060605060a0e01030b0303191110110306031905120a0201020d02070b040c0b040f23040507120f110d0c1e1e0305061e0a030c 65
    0x42140309401e42d8420f03c103028611101401d0070349010010300b44010186845015424090352015004064070300941e01d000c0090303261602d81c01409000980d99603440904860030015040312100440030703020f5801441911942c0d0a81c610450f20114203051500d440032580c1d0450b0b103080228001c4800150070130220703119902c0741c00d01950040c4c00881c2941c0008603076004070f4220701c1c00048007070030035030141540d1044064800c0050091448034400580303040303101c245070780c16684008411200e500d6204104010301c9440c10625000d0403180032640c0c580340c0303440020b003000e110718000d0114a6403503841c100c04604c0a94510224030b0000381041c00030f45081d02001e00f00034820316050508504058040e0702c041d600d4866604000b0b81d9900307060070115000354000080620750084000d0042109001440213100059403910541c99a9410013a02c14001c982911140c002c4920b41454200401d214440e5114601041d404510554022a02c918180010070001c1c40f5030024105000003000410079 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 682627706 1250 682626456 682626463
    0x306210b0406021e070308220c030611130e0703200703030b060403020904120e1203040b130806040f020f0a060f231810090501021b0a030605090d020610150c05010e01050702 76
    0x140485407040300c0102391100d50388851000c41c00c0e00070f01801c00d03411706000182c1203a112500e03e104000005090044200c28100098420303000801907a40307050420a425525024046c00328003684030084401100410f0100103000350b8000509041c0c48400e000042d8480005950095800404803025404e0606083c1440419120110001011401489943d00789140a40200c0a00100651410303161005115040d00888081c01107082c0700040020030100c20003403c0c0c00ba80c002d540c0c52a02e0f0b81a4810400b003911a842030b180030701ca103410100714040c0c1043c1c6500402c1410b040203c590b404440040c980d030400c4001c21400718001081007424072a138891035000f12a001d4411064101d4001003d0311145070304d01c9482d00503440769507036002017030580c002000c44160150508200644940c3e030707a03050b13800489101d00340340d200b000f00c0c414481d03040098a4010040315a0000131354104044000100382205840040c05000070744103080000962055041e140140000c100034200f00300003d45 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 682628956 1250 682627706 682627711
    0x3070206160c06050327190c060f080f04080307021606020c0306061207180e1218190504090503130b0c06010b120103110607050a030306210b0406021e070308 69
    0xc142c0540e8401040301800340040b03034026030f00000f00b00f8032043c00038984800301c1121440301d401c500485000406084081506410343c03445844d601000e0750401c04010700c1200b0310203c6404104152041c03001c041002400c45400580014615681e50340300c00d0241d25080300603d0160b0a513420000000c0c0c0e4603400700b0480080c0c03804400741c84c071a4480c1d0041184079104140d111a03207030000c13002006801d0000c1c2501c00854101400402c041680314016800c0030001544e1160f074a40024a14009900307240d41884881130458004c0c4007120030341c2842da440d030024040e0601440d69945c000040c80000c1094481c0c50f07509a107000440303a1a001c0c8987c40f5040010144160f208a00012032550321400640300c001c072010303440411580c40d5840d0a82110f920f40105e5400040421036140814014417a00500d240285c9000c41d01a1034003103900c0060b6040343c400030401c004031101c0c3e400102030202c1c081e0859000400541c48080341070561003800c0070f850111110000004141c81055040800d562 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 682630206 1250 682628956 682628963
    0x3082203060615020f150612010515010e010318082b02040303021c08070c0602121f080f2a0604120219080604060e0c210d0c03050d09050307020616 65
    0x390240f242c1042c2c0e9110409207200705244c003c000680c0d08100300f8804607500440043ca900402d443e003d0200d401c50700191200b030581d40b00c1d404400d0055811a0b805940c004080c0380400014101c845110003240030040000c1403414005454041600361079407941c40d54015460040350001c0e903c40c034100035030062000701c0c054041e00c0484100d9034038001c0d1080c80074215071074542241d035030401c0444041c40c0d140d00441d0701c1c5030b0a001b880c0c680c07950750f81e40600c9004064250292030040c004014006100b940c0503080c0b50340203d81d02d100180d40410360403040d0a5080d00c0f020170407864050003210004002d81c89402080120700041d102010260514000c0e000341d80030f04106030745101428003002c4500800712607034404c0000c00d000800c0c5501003c1090002025118202c800e40e0000340292150000000140d50000c44007640100c24043c000070621607040c40d010784042da0f50054418060303409059031300340d40c482444c130a1103030620884d050254010b015650711892503000d107055101d0303104142c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 682631456 1250 682630206 682630229
    0x30403020301050a06030b0117011d01090201080901020a0f140904052d010e040311100e0d090f0f0b133b060303191e02062e030822030606 61
    0x444428981c172405d015290402841d02c00745c1c0c2003031000310003142e100ea100714140d13680e181203080f10403821040311200c4800d01c00204800801340001440c0b0030f000341005049034810080f90400c03642080c0020540030a5007007004082c190310204424601501200a8000b8101010003a49540b00485000c40e00c50385c2c040705405508000c070480a099090103003003440405080410042070240c000c0300c041c41070306e904980c0290145e1048905541508441010640c0a180a1001141c00c6400c43d030191100f00d030f20071011460300740624034155051040340541d400001d00541ca240d07048510102034101054200c2d81070340c4104600c03150150174010400c64840310643c91580551307490b0f5040c05014014019070400380058030f0240b403c41102240340500a0aa44111120b010425103086404580e0058120307440c10f255a5442c407080c4884211031841a2740c00c1c045600042051503044c0d94015640136200d98401c120380315002200e60101110304185200002000042c0e040441903070a0203110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 682632706 1250 682631456 682631461
    0x10050c0406020717030d0b0607050d08090114040506130201140a020c0a17060406020f040302031c0806090f1b0c01150602070f050609040f1118030c010c050a110105091203040302030105 81
    0x1d61500d03440c40001300960010400350318840b03032603000700104200c0180058500101a6112031421100c08000400b040e5030200b0444060404c3c40380480106144401343c0c050700c0c09035511903c65200030b00d80741e03417002e03001c0e140029a48240c0c0c4000c0003280d600108d0b5600c2e003111401958962100070a18819041e0580200d800f02e502400304410090540c020310458485a941038003035000804110000f060030300000015076820004d180d0020003028952039211a8920018220000204160701812400b001e029291841c10601903003c0c10900481902800070040070f4100d02c11400341605075802d203205901d4501e610713412041240c0d01130702101e4400e0380d90303c1e401481100901c05e56611600c01c2c00881c0541c01c0642080c4c01122141d10000b60303400e03203e600e840701034003d0310442101c050f03640607a241d242410000481c50703c0c030901b0f1601041a03280d86035a036890384590b00030700344201c41d4140601640611306480384481e0051100d0b88403800320014503501e4120f4841a4444c2d03080002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 682633956 1250 682632706 682632719
    0xd0306080c0d08090a0605031801060617040614011d0f010506180d0605010f0312022b140309030c0601050904032a080f070212010b060a0c020310050c04060207 70
    0x1194100e8201902030081c1d01588401c2250182401105462a020030440e490b000e65540344400e000d40010b444003034030390415005a607030b0041820100c071404c0c1e14142050180541000743c0c01450300302901051030360340d114071340b0102a042c544448074050005c44004035100b00509400d94201c403641981c40c0840e591000e0343e0034006000c0c07250a801c650304000d141807850000100c1240c051000d499501c509880c1c0c4d07106d01c11600d0982c044828000c002c5014407c1110400003005981440d100030700d9041c1f1b0b07502450014074803079407070300c41d0002c0c002d01940904c1740241208282001c1401800b0341740c0c17801c0d860240c0c50354400780802542d806140004502803a01024943c05143c059440e0604e90501740c40031038200403004007000c10010f070329100300005190309e00241010f92140d4a0281c4400d01403040c000b2001380384985c0ca0007a410010584d03042e844000503035990030781914100071520114000b09050180824686512509080411010038003000c010011501d10b503080300c0c80c0540d03400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 682635206 1250 682633956 682633961
    0x311010806030a1101120e19050709050105011d03160e060f010c0c12210306050915181902070812060a030312110415020d021b0603010e0403020c0604060c050d03 71
    0x490080610441300380d145019480b92034858064142e034180081c0b41c2100c2c0c9036851604c80700c501302c40c41211001a0180c104501440510700816242c041441036504060010f0940881290554038840341c074182c1c002142e404001d210070803020160607544094848140c040044001c0b00c100f40507070a00c82102115502c5200c05078011500405880701d10307400d00314150580c20102c8402e540c04030310300081c9034481004010000c021f520b00e80340003a4540c03510013480701840009045203240382411600c90a151a8001d0f1103000d402e032121111a940d9039109900120900c0c0303031101e04094400f1500804003d1504014a104840f401c00c05115550b40701c1000b2100380c0d140002400509100d6201220040f69048001c1800c14203881d10300782521401101499480c0701c00e07490042e0705c0040c6580d5401e03018400d0040d03114850740010b07100c0005d4408070308c0500c07043c42050511030000000606162003480724080314200100510356032a07a85000420318840c002050b1201e000702c003900e540041c000c2c0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 682636456 1250 682635206 682635223
    0x62d090114030304150c0c0e0a0501170c04200a03050105030105060d02030d08060d150f1d07140303092101060603050402010f0c030908060a060e1b190e0307031101080603 75
    0xd000f0751403d41098481c02000210103404000d0000c0440c50701e000900c1c804009000d0211340c000039943d440c0c489000815103106906c8516003210728030820843e2100400c884400030b0080e18080b0780400010071040c0104d1841c04050080480802c1c0706481c558107401480c1260012002071049450758403c00066081e0060029410390040d441c0c40049406004529800b0b8030003421a1301c0d154950300d0300c1c62080b041e0088050215139800310080f80d00d14074840c0d10084201c3d509440080400f0002c002d55a510601449031801d802060300d100d2550100112020326201a200017000002d101004500c03c0c2c46d0302da090029404d060010034680e20a03c580392103140c05035240010701607400380503606041c4841c403d400300114501e021079400400c01100d4000d081092000803c2440e00c0c1030320b0205040581442c583e2090413110b0300002c045a01510090607030044840341140b40e4802c2a81c003d40d618500c5a014041d403080001030020502040301e902000382c84000040d0303a160b0805031151400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 682637706 1250 682636456 682636459
    0x1809150c0c211b010e0102070b0f18031c060f141206060d02090702011d1e06190209010917011b030506130203070c0f050a111f0305062d090114 63
    0xa20000740f9010400c641c00c80c2c45558076000164014054620310b003640c3c05642c1c1982c500015605001500b40040c81c0154040c04003a455004070032908040d0b40c9910442e8821501e0310341080c01c040d2403e605038030000041c0225050442e0159403154020300050028100c3d610525210072440118580464641c0c03160784000c14001030011950f00700624001c1c081c04d45800c5640e5007900a0368803001c03c0180c10040514402880d25800704000d000c140c3c1030901001c001d50b040341c4103100341c0d902541d1818040c0681c9100160710303524140b0049403001455032040502039004040c0002050301075012402e012010001015001d032000030a50903903400396800e54100c204c40c03c84040300035455003e55000340b00ba18001048656a0310341c032241e9100c190007600c1542003079201000300303e171101060003224000e031080106441901c021005400c0c840fa10601810b440b180020a103070f44480080044100142b080482c20000019180c0301608054a00780a0010b00b00041030640e0b01d580c40c4443e4240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 682638956 1250 682637706 682637773
    0xc0403020d0c08100603020a0803040e2a07080d05012421091104050106080405060f090a14030309010b040213030213061d04060c030b1809150c0c 64
    0x615400c0c44406400508241d85030a490310000c210b141c414800545001007002000c50b07150b00314010000781552950016030154020003003088075001c401d181d00e40c0711960000010b001c40071035010140e40b28003049242c550074000102074080044000140011000e10b1500300701c2d80e030b202d0040d4159245240181400c0480f40080c100902d4840e6541540511011248028003444285802d00350380c90f4203001c440d481d070554250442803c05d4412180105051302d00781c1d245040c41c1d260551141d1b4058441d8446c01c0785600090b451180c01c1000d100019481049081800b10480c240783d1aa00b0650301e98940e9400c0c0400e5901d280b51500944003075414010502c0041ca01d540e003080010b1280100344400d00752120030010310640c0001e48420300c8044c081c1d15058078170701481e0110841b420714000300d061515100e001041a00c60012220402a40c0c101c0040a910740650380c0745000071042c0c40c200c0312046c01c0708010704551800b001e07181c4d0f00c2015045601d00e200d4024401c0491b00e09860383d600508 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 682640206 1250 682638956 682638959
    0xd060f060e060304140105010f1806030b0c0a05071b030317010b03160207080d0305010326040312110d030605031524011107030f0209060301090b0a0b03010204121101090e0c04 77
    0x98084011900a44503881c07444545811103170071405d44000760f1107a6120580f060381006551400c6088450a00c0110300402105086543c0c080d5401406006000c04100109840b001c0c03034001d00845000980041c03080d0141c011040c1522010006800100d001880f45032141c000c40d203070001c1c84e50603a0f0b102c500e01c0381190b696138030090504c00c00119141c11881500d070001005a81404610300c01c01180c0d40c041120342c15030411007919a08503003080001880c684c5220400380a282c25582a00e5024103461902d104124080b540d0362080c8541c190f140c010004090020b80c0c150344001c085480c10303000d807640e21076410405000364404680703481d000085010b600715104400c480000307181005040142064520f201c03442d28003645a0001c4030010301000000c000d5203881c03105c0a0303005a00300c2c0244040d40d041d80e207542d814079000e4410804030b5103562000f09255070170b40550b00030741001c4201d551503500a0510028620300c504003540030408084011502c60600f1881c2031040c4c9031101d42a1405 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 682641456 1250 682640206 682640209
    0x3100902071205030916081c02071203080406021c1b0f092c0f09101a09061c0302010f0f0509120708040b0c0f0f062e05030706050d060f060e 62
    0x2e40c4001c181e0802c502503406e042c48024904429036000e44202c03001055100031400348242c124413544d0103130b000d5620030202046070b0301022984c0700806515140c00c103080c0e1180e191550280c051244060114000101520210042580160030803400d070310b0400031520b5205401d40b01020703185000f10000e0325a40080c400c0c01e011707444400100841c1c40b01056104002241c25803000820750f026032480141405101515208000020b80316510702c2d4100403440881107250340146885c0c42103170203031003100000340c3d00c0d0752003920794819902e45c985503812600051800a000b0482510940f01182c40c03c81002440c001c6842481c0c802c204160080c1882c80e80250040701d60380041e441190814000c020114140420074007501000803000002c00c0b141d84055400ca05080e1000151165079102c801004071200b0041e204030080c0d00c401404a04070002a070043c002005d258009a40510070b141c800140c0a6018008000703155407441d04001482d154600e0b22801c055a200b00c6c4005900c16036501500d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 682642706 1250 682641456 682641467
    0x50702040213080303100e01060810060f030b0307060201020d150e0402010804050c100f080f0c0306040e01150f031b120201081e0403080106020f4e031009020712 71
    0x4015002c01400051603680048919541c4121484120102c56030300812030181c1e03150307011b0b000d060142040d90091515000020000045104400c20400c40b0381c0c0703000d8607a010b0f6000c00781c040d0016043d190728540300c000181c00307503000c1d41c00354401a24183c80d88401088012080043e1900c00c1030701161512542c00449409801610646e40782c080c043c203c003000d076140446030046242c5922140e41c001004003018000d05070051005d0f0502d1469810040074410610450f644400b08460010301d080c41d50401500601c02c04d10580701c81841d411b00410a8490700140e1002c49118030007494407081b00c2d0301c083c90b01c0d501750301c035040d11a1000d45203600107601a294442c2e010350340105280f00b02c202a50340103100031054070140d02040291005100107503041c41001e0140480100070055150b2042412440203c60000c80c0891412000c0e510b1003c003044000c0001c0f02c0d80c0c40c803c01d04030018000c40c4003090b071050b41d1041d9411054000000c040525000356401244c0103941c400d411102200160762 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 682643956 1250 682642706 682642717
    0x103150e0709020c0d090909111e04050c0316020d020303010501030c051c050103051002090108181212010501031d0c0111033006090105220612061a01030c0507020402 73
    0x640d02500303070081242101840070703040a10440c0010980880c90b29006040612590828105a42440310303a50106003070b0300070324900380000e80311610001c040c0744100d42e101900c040301642c0181880180503010000001071030065101c55548c4034848213015040c2c1e17135002141c00000241e0001d10041003990301035880b5048012090400c1c03031520070944000100e000040c410064803c0d036910043c020720100304507407248080000011858503007104000b0b0040b03040208400019580b400390490381c18824811420781c01d052170007243e140c42c0f00c00a4508a9102405402e00091800d0000001115107010038144c401d81840907081500219004403a0081054030801707040c44104618001044419074510254030181011401800610b8502c0041a00035082620400328100140038544d514004900e94410303090090380340301c10500b202c0c0003800c4c542c0c0c482400300484008141c28001d89803c0601380401030081001c000700c0e040300540880d10644088070000d141031000d0801403c06500030603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 682645206 1250 682643956 682643981
    0x14010302090f0a021c090c0611030f0313060e1b03010614270903041809030206060d0c0305120301090e1614011b031e030603050c0f0d05160f0b03010315 67
    0x5290044136001e50b6200440c07425210702150fa94002e8405203c8110907103000b0340007918182140044259209d40c0d02d0099140d0070052120020208005401c003924000e41194170440034442c4020300300040b0303110084010b4407004020b84005100481c503061242000f500c1141082041b0107018605001c0b0709240e80c0703444103e4400c442c0c1010b100c483c0c0101028442c4015100459a4505051312550650f8149517188219401c00c4000e8000980200341c2c81c0d4099010b454046211b051800d00001c641415030002d02136014001c140c6412880d40c8000358165441814140080f801540c1c96039a22000310200d444010011001403043c2c403d40300001320210014075041c090780741c2d9401059100008250308078085800348109900016800c41c5881c4180c465040c1005401d15544815031103140301c00301c0e50b200380f104c1a90130119640f00543c100015030850304a0703408454404407440d10044901400380307c4180c60000003001071520080340e040c0ca41c090108005100e070084481302501c41d603010070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 682646456 1250 682645206 682645211
    0x70b04020d0f200f0901051912030f030b0105180111030d02030c07020429093106050a0606050715061e03023c010909090605010914010302090f0a 64
    0x6802040c2c840d4071519005015408201541000309403030104a14500c0e020790080145920f810505e986565401e41102e40c1030300c07401c41c000c03c0048072900b104019000210b1140200c2000400d16a000030b01020001c1b5549040002100000c010340d601d000c2c0c191205503007280b01020f684594030558500748040ca407042140d0034a08510311f450107903003080750080d801c104080b4180042d03241a0288260360b640c101034000c988403600445482480125a81500a405c0302020454102703480e0701046d180e0a840707240d00c0e010131290110755414400c3c44819135543c0e0404000c1420f641d06485501c0c119800c40c0c90f581d04d842102d541d841030000842089080c110b9442ca00000e1601c00001e142d000c4806001600241300e0951040000550705901400b00e51882903202146042c41c0c40101f01c90712144141c04d039510704080c0d0041b541070510750800340205040c10452000c20880760003050585054040a005420980780340e240145000d20002e98407030950000304c1c82000310604415005600c04070b01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 682647706 1250 682646456 682646479
    0xa0b040e0706020c0a0b1207050f1e120f061003110904090804060f02011505060711030d030f110a05120a061a0403030f0216090f0f060801090506090303060105070b0402 74
    0x200e0703041c01a5540010056080303d58000082e250401601c40501082140c19041902c141c80c40420244c00802000502c10006000c00d14420500b084d6502c2071507480b4444055034814451180c0c64110011040c2c0048024000c6104800e241641510a010150036449817156619048001e400c00310f006008aa400b0880380030306840c2d41c0030301ea44441c081c11226039183d01d88100180681e0074401d4100469240c40b0b0002142c001040c0003a08803442124030340c1d1a1015820502ca003005010200c0f41d246c424124150f003d513800d904178005d01d01c0051410000c502c0d01e459054114400d0310700f5038002500801212a0202c60400d08640107440e64400040281e01e403000e03103e034041f68113600c80005c2c4000c501041055840202e00050105520280c400c02c00c2d161120169900c2a000744403d13651101003d1442e00f002d5407000e100c400d083e00090003015981c0000d40c2c020180d02606079014080c00000501d0301e4800000c50340075540603561a45400c90350b0715154000e500c0036204a0f8030131882c212 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 682648956 1250 682647706 682647731
    0x1706010e0d05010c09080f030c0d0507052a040606051812030c06070203070c09091104021b12091914040c031b11010507020c0d0809010c05150703140f0a0b04 69
    0x54108040c0b00307616002c172250b0410200c140f0f440301c44019205942d00070007000f1442d000c00320740c6001100450a025441d8881c620348542080d1200f0400c003648081060a8246200000c48024840c00191400c11840d03440b44011035051050300c00c00c1003c11845000c030700e02c0c5d08208294401650000c4196418840041b40180c10320f40c045d1a64001039002164000500c942c207405d0b0f100034604117800300914804d5544a695240001546510072980810100000c020620141101d02c0d03008065920780c0ca00100900001d4204003e100e00410203405100f101c001080d1802082ccc0d01074481d01a0303405d000030304001c080c09486400004068440f030280b903170030f5115940404040d1007600c42d01d01d01c0007140c0c0c8403402c480000b412101194001c480d502c1c1c00e41c032110380181c2e4264001c94411744e02c1007603400503507199400b642c004045201d82d0580c644079030056070030f00f40035104540d0b090003507006a5034a8640c200064580da10b12103600400708600721200c1e4030000d0480d0018001140440a006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 682650206 1250 682648956 682648961
    0x70c0b04030314030925260105010603140a02070206160f0210050f07030c170a080f06100e06220906030215030f011211030a06020c010c1706010e0d0501 67
    0x28010441010041428020581c211000e100c61034007641c1d480b030551a103ca0b4240e9035016241c194445000556100c00251141c03405410140c9120948440140d01d0400c05207422034008016802a52801d00042540c0b0310030700410302070741042140300120741c030f9803090003009501c24002207070310010410140c03100e02189505004041c3c000c0000450b445030500500c0b00002e084103018040200c10015060b6240149041d2110705406140450403040d00d0724100038010035008011013030031408980b070908641e00c24080c52150300d11000e190056143e45044c086c1a06034014098046081c0070008000d42c181500607004900c866900d074070108515940303c1454809a400400015803a12010700550070712100c040c0141004030340c81403a40ca06481d04016060040c0078100645c09002d4512050201d80c10500c41e40030f0001b8192281051140307031a00083d8005450904c1950a20304140314a03409414202559020380091202556600300111041c01c40c80640f0f0f940710000c0740742400821803d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 682651456 1250 682650206 682650209
    0x3906010603020322051b04110c01240f050402071a070513270c0c1e030e030609070311030f011509060f0807090b010c02030610030201080109150b030a02070c 69
    0x640380143c0d20b05200314000550080d2020400492102140300ba0000b24001661041c6012107091078110500a00020300a08817219400203000c101140d900d0701c03080190f000000c00040700c1c07032001100420801640401171688500b2420140c14a410410f03801e054000705101031162801e44508213200919940c0c1d540142c0310540082c80110341140d00340390002d40080078240c1d0003040081802e11441c0f0110300d03c1034001c981d10b0151106d030140141c6001e00e01c61040c2a40c8012020400300b800c1c100340b1004212810305a0000300b082025181a04010540c00c2c0100b9441d8060726078642541c5480c02c64120b000040b40d010310403030703ea8414802c000e101e0f41c4010040a500d2111180c45c16038400c09489140c5c02c00b20307101c035a09004201e00900020b100c4205e40c400c0d5800300d02d007a260f90050314400e5820350080d4041c0610002c2003442c9403c2c0302d40308281c9100b48c80d0302c10700c2d90301d6040910841d4880d21145603d60040c0600b8045245c0080280d907000d00001c6000d460030815550f030040d0302545 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 682652706 1250 682651456 682651469
    0x1509040f0e01090c030b01090e0a0f020105070f080c010b040c080a0b1c0309080606102703080301031a0f06011b02030708010207261314040609020408070509090102390601 75
    0xc03c84181704001c4044000c60041651210a1180e0b0b5000320800784c407094140c200034400d000c031147c0c8004590280e8140e80004e43c21600059104549080040c2e0990200081203802d510b0a0002101d44c44c3c98031400102e501c599407982c502e65a4888903400410522160b1035000c100e0307130466a41c0c05400f02d0303a01c01e107a00c203550300031420346001481807401001400142c03003028408510b9540f1741d03002c001680310241c07442042d4446210058440341418aa8102401d000c00000c008818410001d680d007039081024841407009a0f03420040b40c00e440400c1d5032083c0000c040c21440790340855013164500c41c41d400241500d11241d606d094041c00c80e4414030089400302c440c940b04013000720041e05035450143c100046039182810b003125038410f9040500850700322075441120002c05449a90110001d4849004219541d41e1140c0940ba51f60b0260310484e0f214003003080018031b400b4018021b4404039064000040076407100b03804400c440c40d5a4400500e2240303501c0184451100301000054001e006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 682653956 1250 682652706 682652723
    0x9020f1c0309050a0b0f0315060d021b0d05030c0904060b03070915020c0d060f0f14061302040803070605090f0d0807090e090c13020906271509040f0e0109 68
    0x1020318020b482c060640e44154455481800300304030132981001103441005580145036503940d500304441045030340c9442d40d59007066001c98844000d1199500502040450a843d0740d0500c41d0032a080c2d80c0c032443d541040000483c14804946c400e24500c0c050900035200800100b00c50740c07a03954280050b0001c0360000005039a10038100081c0020002c64030700c100c0f2510140c0394000700000030900c3c00291700c0b801843c1583e40e50805644e82c9442e0303c41507404441031400d011500341840412045402a038503a440f0b58484140b212110195108a804450014000e9030510070380380c071807400402c0c006040411a0090100191501b4800e00201c0c00d410240d0301c51541900f400f1200800d28112604005616041c03e0144003131401d00160501c1081d000715024940c01e2940e80c0c1441c00ba0140c1c20440d03030000e0300072651504040040322180050f042c11000c603180d00d42140c040000c04240e4101010352070f2010440082d80c2d0510303800001c003201580902042544a0021880c00c603a05000242c0b5a01c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 682655206 1250 682653956 682654009
    0x3031c0203100602030403080f0327060411030c0a0b070f0f0605100e09061819030509040506100503220c08011e060521010e030316090602150a09020f 66
    0x2d0110305014280c02d10065040c94210740d529010b6204100d0b01400048004c0001011004410000b140013001c803550132085560310041c01e0780e5913070700746c40441d400c6011281c64003107801c0019003030410240042003071828515000e00c0c0c40150344043d005a13400d40210654101181d110ae80c042d143c02c1c450800000c035490001c2501840d651550002c401d4428601c042c4242d108000400b540c03c81d800d0403010700103900d0f541c012407a0034885114100d03c1000b03040175505041e00207000e452a10b00c01c2e1000d0140c1d640320002c01403800c03114080c00d0003050f03003031010504031700b1200310441d101801c04c0c0c0e01c0c1038035450903142c507000c1011943c810300715603440740c10b1030358001103a04082151507071000c414088641004001115200c2c854007603604a0b01c203c1c907481150509400200c03204a0600940703a49042c06480011031440c0001c2c104041101c80030006032a034800103003280310080240f0519030030780754208203401804400d003060744e0101d8205d0354103a00e56105203a00c1980d2403191503441050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 682656456 1250 682655206 682655221
    0x60305100b0d030905040b0a05030d020304140603040308040b090703060912120506151c15030201080c12161e02160801050f0601050f0d060e19020a0f030b03031c0203 73
    0xd0307020086250050104034002c20021350060a01d0040d6881102c01180d102c844001289005059074002070703041c0304659001d0480e0ba0048001c00545d0340d005d10300940301c2c080100b48103640c40309540080000b0007030030008010070301c00311065402144241c1500d6043d90741c2e8071424145d442464060700c0182b900301158503a103401c41303420303d424080303034400b4821885e1a00001d110014a0716400c9015480096a58160003041d104d503094003640302c404010030004d241c403403200108140422400320719034401080c420f100c0041a5915852100c051b4a41980c9001c908042849202c1805090100040f00702810340300700845810640469070040a120000309542e05528080368054541645408144060000c2d514070740c5078404820300f8070541e102481204451603104c2d180240400901c3e02c1000702d104a6522410b23030080d48128034203009109103091140480c400d02c0c07003d0007c9442c5007000151a8080c3e00b01c0324000c200101038a00340896550a030100e00b0300d81c90002d06156000040000741c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 682657706 1250 682656456 682656461
    0xc07031a0a0b03010e0a0b0a060b1210051507030e011b11010e01030e10050c09030706020706200c13060801140412230c1f0f1406030706030504051006030510 69
    0xa0071003c400030300c40d03142011300d1035449000a640c041d0000b81d8100026a03032080d0fa41050009003441f4034001d586800c04000a440700000391459801e41c00000000659850b164072140704010041544519001c55607405560921550145c141840b60600003164642d042029082c02640101500c400c00b01c24074000501e00400c450f481c0c5e041c5480c2c80f40c0038090701800281505045600600010241c890101084542c0034041000e54144030300c00c4007003402540459120101c41141e12010020484d0b1422902d0728a504009034900340d01040205040e860306540b05c0c0341100d0f06c41c4001604540b1112424290317500c107040000d10a040b082804100448561210341365440c0746083c4001c8508140c80c01c011154103810700702c41240201d517010301c0f683e003071181c0013400e04050300c0c903e40003268080c460060481c045241c2031484c41c0c440341c0301d408441000803a10038003008000d01030050a0034001d4004010241098803548240c5458902e400d0040c41584003644c0940000d02c40c0700c8201034007105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 682658956 1250 682657706 682657721
    0x308090c01081b0f090a03050d021216030e0d08030a0903121401121106070b01030201031b0801051005090307030809090106110606060f0d060e1806060d03050c07031a0a 74
    0x100182001008820a030103000103c5007000141903680d15545080080242d014000e0629880203061000204009000507203541a090940941d1a1880d80b148821110b0080311103400560702c4051641c07000038400c0038000402031004010240001d510744031b1301200d40040761080406a40e90010034103064114103038500210090a0503c2820808486511011410701c1404c0319092800500310402c00c1d0082900d044d042c011308945d44800f00c60400d1440c2c1d00003848146d011134906200c51101c600c075045d0340700707840207d5161141c0b10f91030310041c0700c4c0c0c0004c0410984200700741405103140965040c4042e100460045c1000c94468000d001040301c0d0403410b0303003c0001d10141c480b01d00c24244010400561059048600c0e544410903841c0b484810301c92001c545401524044000c40c001500d41c445e580265040001c1a0017000c960074000e503140000c1e280280d0010083c404040002d108400401580e080c0b8001d6404465490b500c03800040f181305403540b1048070203c10804d43c05414803500d05c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 682660206 1250 682658956 682658959
    0x40b1c05010606090509130b0c0d09030f091202100806120a05030301030516060c2909210708040b0d0902100804030f09030b060405090f03070f0c05300703020d0308090c 74
    0x840c1c0c207142400c0c4007e50100b8a00520750748514001640040d0103209561900018402c00e12030140c2e81d1070020f009456040898000c00d1001c07002103000f4481041708607030207a015003841752000f064482507030883e100410300c030360000c0c500003c8140380c00184090000e0038480c400031612941140f81590511594403540b24a1821440d0100070b82c0d607018010100702c6402c840c0d003040c015441c0380c20b0846205801e07521300c01c021007602440f01454001445160029019401e415540c500702c142182c00c6c49480000f4007094014040ad010045140e002003495245401000861104643c0456000e06407589003e000c01c12003010082410f4102610790005180c07858010302c454150340d1610341c2803502600340e0b402580d80740000b9002c0300c4100000c000b0f9203004000c03207440780d06a190240e04455000400c5072640b440e110002800e06020041030740f1107103001d1820900c96aa4803d6007001ca218181c12426881486400000358030b54420050020f4002c3d540c0340410f25194a2041c0342001201001c4e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 682661456 1250 682660206 682660219
    0x20409060605070f06020d0219080403020c01050c030a030e0307050a0503040609050312040b09010905120f070803133b09010b0d030206160311031e0c0315040b1c050106060905 77
    0x2c0000030900c042c040c4d1440e034000c0d00140c072400312404100003806084149001428401e400615003138004a14070b1040d48203500b20342640382d01600445190041b0400004d09a00c184061000307a406074108042e809201822070b4104401a10b6607454034050400980355a080014140107060703004811402030324095004140000d082c601c821920f100e2031050100c01d1a012845003040d078400c3c00640d0081000424148c8003128071423245445080005252806215032440040c10b035201209407811100d42c2c0c144140072916100f0088032907090040c200e0242c18655400f40320880c2c8c022005452a1382c0c40e45001d8540c6032548a141c21200340da00401d1290b40c14801c03100c0026400210750340d022001221007541100510383c242e010b0141c40d00741610406020040001008061142d000303400c1c042c1201040584803007006200780c0c8401c2e40d041c03250790b51817800042517013010b401c821440c200140608090072068130191a007420181800ca4a40e51908800c00003c0c0e8418100c3d40503010880d80c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 682662706 1250 682661456 682661467
    0xc0c21021f021c0b150d020c0105010b04151713080c0106090501150e03060711070302060301171e150c0f1b0d09051c1109090d0f2c060c010204030501020409060605 72
    0x508040c0303404000407024180086e800c402071a403074042e6811310f08114002c2c45256100e8500381c03441e07001801456250321122030050400c2c1d104180d0322245031996149447c180e00c0f241800e80050503942c1b01618940c00170080c1d21460482441010700408583c6000212541403c08009480002c010980100150081c0f80700b00c5590100d46d05400040904041c04100c200301e1009080a25039030010350b11410200c0006801d2180402018220052105503030141c0c0b4403420302020f051940c6070395103441e07009002000c0e844807441a0281c202080a402d581001481d00010005901c100b4007101848402c0c0c0c201d000c00700c010800c5040d1060346043c2035044a00b40350100308880f181009010160365100d15010611803500094000218080c2240c46186810b04106968041d005490000110424a030810580c480d4010401d4003402c1004c49060b82d80e00c1c802801c541c40c00c1003006a010504100700740300f040c07091005000441c8602c00160310399282141806c102d8031940c0c03080080c031804024 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 682663956 1250 682662706 682662709
    0x90a0615030518030c0a060e0609100b0105090a1409150105091e06041d0a1e050915090a03031a030316050a0609060f0c0c21021f021c0b 60
    0x104031140300c10528001030680c2c0d40b4030140315007000d0b01d001403015010000302c03d2480c11000c218802d0180c0181d50030300000044a00240da5800704a448100c180c110b03d41c458114061600309210031001450300d9420056044000380000007544d0062440201d01d1421140c030741041234881354080342d040071404008030000e0010305184902c2040e203228002100004017001c54000550764040380182040c0d44440c1c462982c0ca850b800801410617001010100140c010321031800384401c150060400c0d400030314506041d180107003001800c01d016034066500140001d141e0101c05511505640380104007038a8603040142c102e40c1c144d000780703600c05d00001c90f5440684001045441041d6440303140c110102c0c1c1810300c641400b8503414010141428420510f09000098001400d404200d82d82001002d41446080c0d0703411404000003030840608102c0c0c1e90140b0304080f40301480c02c01c3c9006686402c5516240207050061000e00100b405501050000b12250074017800810700714425801c1008103040b00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 682665206 1250 682663956 682663979
    0x2004051315260703031407050307060e03041a0702062b0c0819060f03030809071505090a0605090f061c090f060608071a030c071203050105030d1b0204050402010c1a06090a06 76
    0xd450214580b80001c9507c10030108100700c0f1540364004900700a0340c4426811a40c480c2d005215000030b0140070700d04100181e0721a0304030754965034002c06032450300043c1c141d01c0618547c0310034203041046012a103084d030b90080b40030700d0b03143e080e4603520103100713141000e59020342c4510b4090004119151407020b002c04101c4000a2094039098140345482d03a540c0c420307061406400e83c1014484002d00c2614121187d000380107003021034801c1341d40c0710380d507a01d60004840c00d004070340540d075000007039052042c100d003460b500038542160b100b00c801000041c104803032410382e510030744220340c8461a03c41c15020700c0303803a01c1600e02801e070000290903c20b2a28080d0302034450030010410584200101260122500108071000c1c40e030b210141c0030051600180140c01401c091040c1ca0280c02a4a510040544a00040704810398208044015049a40c0034407005001c0204100c0c148000c150041000c1004d000010341034103034513000382c4040d00c0d10006002d40f0b018050b0180d4201e9042c50b2042c4811606c45 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 682666456 1250 682665206 682665227
    0x18020409021306030e0d0206150316060203070201080708160f09120c0801050a0203060d2901080102130e010503030a111009050d0f08150d021503070909200405131526070303 76
    0x2c1c0012120103050800180c00c101b6440d08200c40424032444c0011003d400ec030103802554001d80710701c0096a00d4400a40d02041d0440d03c0ca0201e079903c0007010002801100c400301026980e00e0040030460700c40e00e560704409240c1c041910a41d05400c000c11810390240289503102881010550460500c04003145480c18130920040c4150140c140c0000903000d0300e040c00814000203c3d881c050fa59490700c5042c001d600c03550022803c0c0b9000d40c070100e004448a804141210301c054002c600e415070104084600c141c081100c2d00f0707540643c0d078000001110b40e00070360348064022800343c02030f41055200542040c40100c68002844500e00402c40e1a042e4400c26021989081e038500c6c1e20380c6c000b803000441d0070109a104482c2d000c0040280320300d05074410390420a0751050740d410001010203610710f00001c0d1030b0800480302c148040100740407600b40b1f208030808001e8128400300302ea481d0f4002c80140007150b90005984c02090b151006220091580303030204c2d188005001c0c25407c5e00b903840081800070300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 682667706 1250 682666456 682666471
    0xb0a08010b0705010b0a031a070309020f1003060b03160f08061c030528020c0a0302300703060504020103050606160305090102190f1a010f18020409021306030e0d0206 73
    0x108000b4240304003034100c002c60350402007420105907200e00e40592a1428007040480300c50030740d800101c006006e0310468282c150000d01c1840485080002c020010310300c03d50940400d500c2e00e000081c81460407000e1400760303004520211251000c103000401c00030040e244e800800c01501c041c000562181402048001c103049440b0f8154021810140c44c00d2041d00c4007400c49000c43d49251024520701c82c0b00c042c5003420766098424080d0108200090080d1500010f0f52001e030344800c10032a0861546840c240071403414540d0403003661f2001107814000745500c01e482558581c0104800c540c1c0c148200c81c0c0c4000700300c0b9950b0030a501216280c0c495040220000c0a001000840c0d0607282e00800c200d40042100e110062034406e05450800840c1801d400102c500d5003403070003101e000d07a405482e240d041e141aa0244c580d07441c500f90081070071341c410b200003001c0960f0820010036002ca0070300040040d0008406140881031600100808031294140002d51030341151310100d03402c40d0301041d029040303044c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 682668956 1250 682667706 682667729
    0x311030c0a05131d01090c17130c03020607121403070c06090503042c01061b1b15020c120c0f0904020a0b03070c0311070f1e0b03070c05070b0a0801 65
    0x62540000f14000c540d4000b0340071240d00d0405030b040fa40b1900c42080c181c1369804e00c00c0c0406500c0c00360603280340240c1050b0f00e0071420204001000c0940202000e04a01d004081807800e0b141c6c0e81d00071a0803640940e1080d44c2100c40b214000c40e1151f00a40e038058400315001300c1a28601c0c0c0084001c10007104c155000b01020349450240f002c4c0f0200300b0580d40686a0311046103000513840e00c40f00041f0f031a81a02c0700c000c1c0c40c6080001126406180c0701c1c0c800d0f00004200b4041d00d100c2c3d0b581c040d074100c22010164805094180c0c0403070382c070423241d10700000c4800f980c00416807080828101f214800301c0c054040c1c030391362001e01c14400944807440b05003032920080ea40703c941d584580c0300240030840c0700d40210306260008007c024a26504c881621603440c066110441689240c0400d20b0b1518038a0080851b1003000c4542000310781c1803c210302038030308090762041c0710319500e8000c0c54103d40d1040d9541c0e80059042450401408810703c6017400400c0070850191418001602c050140c10b01482040e44128 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 682670206 1250 682668956 682668967
    0x17040305120901110d02040812092202040305150402090f0405030d0c0504050613030c09050f0103020d061407030b0a06030e0c0f0a031a2205071503090507030b01060311030c0a05 78
    0x15025004039600f507122144058503071740445107a4009401512801e141d40c8100104907001a1004044800700c00300680010090700054140c114403100d60441000c1e1182d0800c00003002c15000e000c1c0c0103140c03024181c413000ca4101030041100784080501910611680c0ca0107000000d50300004030303100d450710014082103e551044050b1010f004070307407105800c04000900001c91580c1e81400750305a80c442ca06042440703032101d240d081151012108144030b0340202c4c00502c017618200805600c080d220307000214007240c1c111b6070303869030100680d4400042911038490034001d10300b80c00f039034010b040c25150030011014402005503842041c011060f004c0c58000c44000c2407504c41601100185400c94003110780002c2c00c10340201c1290080311203070b03444c005000c200744032200c0051000000701e420000030810a81480c035a01d008003900031044040c1640d5001100000344240091002140101c2c0701500355032401c00050b0548070040040d00e0341000800070450700f2041041a03804010592a06680343e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 682671456 1250 682670206 682670221
    0x32d0f270b150303040e04060e030a0c110604031e030207090902030c042703050a091215111306020a02090a0603020904080f0d0204080c0f040e0a030806130c08071704030512 76
    0x11014110b0290076010000b008219540b100403100c0c0580d21400741082032881c038000320340d103a00500d8990700018002018180208500010001c0d1844000340050320346913030307541d4480035001c51802c0d038100341e5422000c010034960140034010040c01000014440c2c0b1465a000036260010b00b10114803490303941012020b00748041000c0703850151040500c1c0441d564604001e00381d600801003140000e00500c402141c0ba001510030800c44d503611503800b04d003100740c41d4000406043c114001c2242144140102e21181840340302d0302004060301c0d0060144c1000b18010f000240c0d030003c1440e010340e400c00b4420001611340083c855441504100c086858168010b855801881a040100c20003400810b02050451000c6139503031424008584801c410403a15003800b09031200001100c4650f0003242c0c410700880e00610150b0340c0444000d100d4031036605401940380c00c68108011510008070880c00b000030b01504404485a07014154107010341500e0540d030000d0a500c900d499602c1e21740c000b0b02c0811800c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 682672706 1250 682671456 682671481
    0xc03151806091d07050a151211040f0f0b0705060610030905010f1406010f020601091509110a090801290f09090309041401080d032d0f270b 61
    0x14100b800c0041c00700790920340401c1c1c001d00c080075a040b054003d2140c006100c0c0b80c00382000e01190422a0010012000303000d064580551812104580c0f40c0c87d0041c680310102d10000038405000900c1c1c002202508043c007001e40c280e929000300030500810880700010520000700c05511100850b036000c1849607012040b40600f80c403d1000304a90b0803d01b4078160340c04180c1100d0280b0080c406560304964035000111030868a0186850150f08030600500146400d5081040500007e5081901c43c594aa040308122114000d00d00703d2174001003842e010955010307207064020309025000744505030000c0d60407d85420607004c1001280900e10030240140c45d12191021070550060000c1410319100a00b6900c9902c26000386116a103801040050345180051340c40c141e60165008009406d0340c1130b81580104480c401c046100401c070000e1410840f00204650b82110160300c0118144143c001c4110584900110400550f458a842003000c0c545114580c080c464215860f0441d98840c03661030840e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 682673956 1250 682672706 682672709
    0xb07060504020112111b0a1101030b0a050604080303060102071508010b1b0102070c052b02060c1f061e0b070f150c0503090d0c020102151b1c0c03151806 67
    0x134650705106100ca5009440c0c0701811000700300f60326036000040c03030075109601c410201000070050050300d42d55170504d503c01d60002c178800700701401c4400b41d5030b03c031000103010b41c02c5980207108580c800020496030b542d06000035401000d403045403800902a0201c050500f55050044804544000ca00c3d00780c0d482c1d20801d032441e0012120021956100349042c0507aa04000d80612400f4810260b10164403806040448118a540011074421010f50f0b608203c1150f200c40c030005050700c84c520f001103540d15000c2613140c40d000d10840000d02c5c2c0d0701c1c2075030081c10748800040100a110f010303842084103100fa902211100c5a02040901e02c060082c5812080c000340a8a1440c446d0324003822034082c141c06c44015401502c402c82203651504109804444030340c121400240140c02003e030300000c0348503414440d0341001c0e15668090826030703605426a102e40050041c200e40b9902d803102c600030303101c079841040f205044030326080c44a1981d132105015600c01d503115022001e05015198110403180358400c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 682675206 1250 682673956 682673987
    0x706120b0604030807061a0a060c0f0b1614121f0305160f050a060e06030907120804061d0a062105040303021b030301050f040c0e12030d0f05010b070605040201 70
    0x640703032a100d09004d0b00c0e50304130b42e00890b02a854400760100c00b250f03075105140d0346c0c0f4005044001d62410a08221001c9040f0601291030489a508020000741d42c1c9030341c42d20490143c09520880307a0100001091010641c42c1103441e00010481a244402d03ca50718603400881e09a03a12641c03507800040e81003031502c650015086009419841442c1031440340e81c0c0c5c4c1101c15426041c1c41035611203081100d541d4061203400040381c0890070081c498140907015680c003004000685040320356030328460010807480c1c0401c5564140000b01401407517000052443e0440540070603258020000300484d05000c0e40703029100521140d2080b4110701d91180b110040001d588060070300c000e04140c0b030042d000c4c1d00900714a50b0801c1e00d401f100500c1000010039070303040310f000818042d521036101040c08020140840c04c102001602203503240a0b4580c040032107400c0d240b41c1f0065a0710001c0c010070f082114002480000400d0410004000240b0084103403801d050304030000003650307100c5100607944c0110f4100081c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 682676456 1250 682675206 682675219
    0x10030b0718031101020d0518040c120204030b16050c0742030b06031603090c120515090120131e090605150d0522110a0602030702030706120b 62
    0x30040002d50358075150a000f00fa000c0300c007080444007040d01d8070f0042107030307220442c0400b0403d14030f50b107415002420400910b04201990003a04449841a640030b6002038032481200b406010a401e000c03081a00c1d240154549541044450105580c0301d01d0a4407640005145207035401c00125030003d103c803401c860300390152048510541072031190314415243c505c00300385011800f256608054040782e11440300c60310700640a2027010b0060340240351007101665178640605c4040307100420321240e4038034680940d008052540d060907860030848001050f42c400750341041070080328600d5906400c0754ac0c4110250302c0f80c485020110303202e0404010780c44080b0201c02c014520b028052180f1070350003a224219001e00c00c1d15103510074440c0244010b00f10301900d12040204400c0c1d601150b02c45500105603111049010441c4250300d003401d95000d9041d540c13070400540c0c0049a00c1c26002c0d0304000c1071140082c50070003400d6000030751152110b10580c0305201c044490f42511440650203450103d170014a80e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 682677706 1250 682676456 682676459
    0x180601021c0306140607030f0804050307120806040f0204081b040212131403092b0503130e0112020f121603030309061a0604090207050109140102030601080f10030b0718 74
    0x2d0182a07144144441400b032214051010b040c600e0840d030712540c03d074807030060068450000300d4a080300204107540e40d001c14810b40c2c0000d00d00d0021b0a058406a9a90710402c1c14a0020402280c80c000c03003650956104200c200042c0102080d039480c0c42548101c007403100e58541000c00c02900c03d1400f41c9642c4003d040030021200049102446a81e000b01c078214251500c82c040c80e5964403e1000082d0300a4000c1c08143c2c8181007030405420b0032443c1e180d2070030442100c0e900e483c515003080c000c5030740300001e00800307128024207942d80c540105552603e119010b1107a8012400d03800605c0801801080d0180304008480300411202140009152500505c030381e4909000f8003c1005000403030f401800c0c114454100c01c6c1040440c0f049040040c5041c1c90540303845980c200950226004455654907403040c000801c08004002d00c0016407500007503924645500014600d1340010038410003103070640240701c49413010401c14410b0f02c2e0302130f1881045032541001511508090340c0380791200d10700c9010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 682678956 1250 682677706 682677763
    0x10f0509013905210f090723040f0507030c020d02070b040306201908090a0b16030f051f1509030b0a0b06070c03060b1206040b130c06020c030c090618060102 69
    0x841886a42200030b00b1701c0b103840300c80d006521104184250711448140900e004018441d82c0950799101e200140300190310341c00030441c40d0030b580d4200d9100000c203551308074140c40d2540500510704125440e101402009007440c44160160140d4080035083d07070768403020210408081038600844108051046490704401c0c0340c3c80904030a034410f8100015000408600392180c005040c0b01202e46c40540681d4a91b10b800f89400c82482c1c510489003015190b40c010703480940284034190090320511090302171a5803000100c203090709180d21180c68000f20400700003d0950002062054a0303000c19200740585a2041080240410320b80907a442800016504108483c00c460081100d20944052080295220400104da00c6142002049410a0b0001000140b4100042d90300001c5040c2e62a106511030700c0e10200780c03005401850140c2d100c004032040c1482e041082d81303908541182e03074204610344500800d16042c803240100300540000d00100702c0c240c1c001d004103010314084017402e0110310945013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 682680206 1250 682678956 682679017
    0x406050307090b0103110c0a1b092a090b1806040b1605100605010e060d1103070525080a0e0103090215091806010225030203010f0509013905 62
    0x101c0380f50100f454020031802209a072816a0303034004881001c0c00f5203422640703452007040c0108440341e91800003d0804604480350b489241001b050400e1f500540b8030b00c840191503000c150001c4c0e08240050410100407001d007490842e400002c1180441003d110701c80c000c200540541e40007410301c41004500290600c94030424840d00c640200c04441109580045da03030300301d80b243d0159600003424580c44c2e4049080210081451440c00c9a002808600541d400e40c03d039003050398940d00181000034013500202c400540180511072004204070480c2c00d030b81c1ca40e907684c03090410386024002003c03040355541c1e020b540904806030300075200c0c611003050f0508024203139101c030402d94400c43e00316526000126158958520422040c0c00a05250038030100703844081c0880c08126024500010300440140c8080c010010741c07122030b40d0081898100003521500303551240c500304500780c0c0202d0440314180c01e50000302c0e00c01c040380c0d41d007511f040034410000c17a1903100320404441c03030311a4012142880ba8151 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 682681456 1250 682680206 682680221
    0x607080c011e0b040b0112020c0a0503160506091506040914161706010509010b031902132c0106030f06170703050c01080c040302060d09060e1b121902040605030709 72
    0x4008000243c4090f003000300f1204242d0b8000e00007221015050300c900f105070f00501c50700590300c0884170010b070039a8549107543d000441b4843c0d1881c1d09111403080140410a41c0d07005420b04020b040c00b0342100d00000205400101228811600e0f60900700c14405100403104160320781c4016544500d110900c05020b015981c800c980d05100e00004035000407801003a01c5040e07070070003407541080382d103046d0100d4215040075000f00700700001184a01b4041d401d40c40108a03600040014201c05450000b041c2c4404084075400384000c40011804200d0031034890b2600c3c1590041e05001800d000326030500c0e402021281c01464225860030070b8060590b0300043e4110445e0711810071a1505c0710b4460044518807001c1d2072030114600e0500c014001031030004060140444001070003d81c0b200340f81c4540040d0355560b04810301542140c5141c00960781c51040042c4d81e25002d0b101d40c00b403c18000c140c0c86e40c0344040024040002d03c00642c100c115500c5806c10002440c0090440e07040031b880c0c80a500003072026 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 682682706 1250 682681456 682681511
    0x303090807210c2d060306080312091606030204090f0209130207030212071202010b03011b030e15190606030b100309020f1003060504050f040f020607080c01 69
    0x9808000680180000320001550201d02498400d031000401c0c1201c6684403000859040300300703840228060709246030142140800700b011a20601d1610395090b42c0184503003101e0101424804280100f0b103000048950181040705024181d540d0036450a0410701c0b02c030102000040122400510a1f078590040e20550b142040d04129542c902c4880000320b21480c00710940041c0f417400e107983c55610300d40c003030005107010340182c0d11910020301110b03405512015048400b800d1003103011115540c248036134a950b040640081045180403c0401058102480b205003010303154690200282000e120304010300074076905580f414142440100007100007120941e41c0c0d80c1c03a04000103001172082c010101120000b4009a24410300c410b8101d01030220524180c4e041035010002c443c403034a03441d100e401d0041c85a0703400a0b1072401c08040100b501c0c0084c08000c13901940c4018031011941d8404090356455049818036521001803800030113070700594552044551a210003400a051007407218032034a2913 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 682683956 1250 682682706 682682717
    0x41418060a05040f080307170406020408011415130f0903020a030f0e060711210304060212180d050a060504120f03020a0f0e03070504050a140c07110d060209030d08010303 75
    0xc0d5581c0e800100c1e102190081d004203e0309101102080c01030000310307000b00c0b0f185061041c7d02c00c10381c2154034011082d14100c55940c0c2c001804c21110320203216211203030741040740d0b012443c1425039840030074003000c1c080c0c01c0c0f02d190205141528510107510940c1030390450b8800307209841950030082c5d00d070342090b10190302150803003900e4140b0034441c40c0d0034010740300010001b509040540e22032440314001c400c2401e070440c040030a8008100b000781180340d0301404010003142d4840c100384000b810020504a0074000321810701402d20055046051074090340000e0700c0440707802c1b4807810641e24229002340003400790b41c074020601c03052051b20008081c02d01c5094403407411a40c5114011002c91040d03281900005480ca003040d1038aa10481410781c11140c0101200ca20a807039000040440d0030a03959103c0c0c3ca9621040ca100744040080c050b540540a035206a0a010064990207900c40c2d102d8a228800d03495030b54000c08010550703060701d605c0b00c0301500721103a0152011029201c050b080c002500802d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 682685206 1250 682683956 682683961
    0x40b0108010c080108300705061f1202100302041e0f05010807020339010e010f0c0503041e060507080414030406020a1e210915080708040204141806 65
    0x280140340f031604075041c84005108002114400d0201d5550082c1c0c581e0014040702900b48501041074080c4c40d506000d10040c00b041e050003801e558440b21140c1c05a2000d44101a041040c040010303282c10b0a2134058990449040b0298001c40091059030020800300d90083c0304400c122180c0782000d400d540c8412082c0c0209070f10b5000544d60032400f01e0714900140e00401240c644880081408a25480b19000d01c0c0e2a96014107000c0b02c0a00594650044582d50b0f610484500002401131010080f1010b100304400c0507440002400c512005102130594940032200c203048624010000c030071150825070401170b50900e880c2c01008110207440596461031816030302c80d9021404030440e0200c2d0714940040c030769441240d5508000902c1c4034100b82855203000d403c00041214204044500c03540c0c141c06034840220408050081c40b004c1e003041c40051403100070051102c5e080141c6941102c658142041c1a541d1440054064102136200c01c0d00d00440c6001d0203650070f003c0026005e00c1c84203005943c082e5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 682686456 1250 682685206 682685231
    0x80d0f030b0d060c0c02030f01020a03050f010e0f2203030b01020c011d010e120303090715080106080705070206090a090f0e0303040b060f01022401030212031603050a020c09040b010801 81
    0xc8030140301c4103501036004007800b0300007240c56001d041c4a43e0541040c00104203030741c0000e410a00d032150076426503500041d400c80c00d43d50500c14103910040030a41da0030107505140b00765994000c010501c2c441c0b0280c1e0300109a038800040c0c000030520348154600c1d61070500602c0c0007405400024600382c09480740840548081d806003038851010001000300d01e4003100000f00465441e409400e107507801c00002510003100500900003144104802e070010b0500c0e52400c81c0b082c11031801200d541c01000345260061005a40c042042d80d0050706034a0895141d65081c00020380794400c078006154089448000000c01c80b0703080d00f000d445c0602c0c1324403c20904807801d00c00e0351130348000c41340102a206a2000201246000031401d803c10324184125054901040b4403502040c1035410415902da010034010801c40c60042140c1c0c0c9040940c0001c2d5042100030900e10b14a00441c000c000c0034000c001c140d0700f00c00c910030081022040b030000d0801e141743c105402c00140c070000c280901d481550a001d01640b94 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 682687706 1250 682686456 682686461
    0xf030b0a0e120d02120a0203010e010e040b010e0613021309110702030a1209080f01020702100309020f13021e0d06060c0b010e040512030717010608060d06050c0904020301080d0f03 79
    0x86500d140068002041c4071150126283e21000321074081036424400c90390502c2c07100c1080c0784100721075400141e5a50500084c08401c2d44160b00c4104002d05880c04c200c00142016012811140b264900d8003186e00c604c1c0008036802c41010070b140620748040703500c10300407006c0c2c0c0b202c204948515030108650040001c09152034810084040c0d0103611112501e4001284440101d450404a00c5c08062180d12495200c0c100725004121803035607900460b071b00b015841d00d004803880c1a0058101000040d00a03030204000500c02804684075090020800c0d810110744d40407030710380c0d4014901d40349141202c40248039403034010406503465682b07041008580140280b8880300204e400458030460340e841c003080d010030390364001c0007107580340540c040340781e40620000f000e58011401515055003145802c0c03140702642105a01013030402600505004003a22200500200d035a042140881d045d0399089000039140300b0203200e1a00188004000581d000e00410500d8000c56241d841014040d0b4a104c12400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 682688956 1250 682687706 682687721
    0xc02030a0212090f0607050d14090a0302040902013f0204030314030703060b0715051b040b0a0e0a0e0f090303011a250b010513180303020912070f030b0a 67
    0x1680c02661424034000b03110700581510303100180100c140c0800440490b00300d80101ca4120f580f0340c000b810140c9800d81118011400d07651921072142001c20f20400035007608024400a40910380d91001c20782964401c801089000d660044004600c100138450a140d4255000411a0034000c00c402c1c0a0340c1e010a000312821a40c15990321040000034440e10b01550340301803c0c1b4070601d40d445100040d80038814001c1d104190248409914000b0968140410740700001c08014004440b5141540403608090660341a0341007144629110f40c5070910a41c3d0030580c805000d540312413040c2c4000344282c141d03404144140c4008220300110380702c900f6050390300c1c0403c0c02031040c0007028a00080e00d003041c2030090108440d002c48043c214801103407a9000c0c010f003845050340e180301c846d00144420308015001c030410400115041001c10001d85200c1d011240d4124024201500090018031950f40c640100146d000c48000b62801d03140c1e00c082c0003910440364807048495006640000c1c060181a104500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 682690206 1250 682688956 682688977
    0x20c0303071b0b040506010905010b090d2013061e1211041b2a05030306060f04051002010b030d30110d270c29030a0f0c0203 55
    0x1821078507012016a031a0582480107000008210389510100e896107044501960092000e0a00d0b07504204850069402c140c0003040c0c01d040402181003c0d031100c0c01b09200a617000100501d55400306044003e03441002207006610541511340c035039940da01584480b044658483d09200c0207085002909007038180d5200c1c070040c541306c40c0740d02000f103080080c030303100e440d20018800034810340c40e0700c4000315040030301948100240d01001100d4003213207803440b00300c1c01d403d1980304442c03641032680c1c5841d50303880020710b91805901301013407030140c504404041e01c01a15000300702070081e0301800d200a00801082d0791451003403240350060480b440c001d2004000c6100038a001d445030200c130040ca503140310b2240340c661400da641c030071244c0a588104400750035a82e0120070701080d421602c1110394000da52401c407910708040000740c21400144400c0340e2104a89081425110300c0c00500c103c0c0c410341101c455102006c42c000030400105080f240e0011400c00200f00c03080040042551049a85e07008192460 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 682691456 1250 682690206 682690213
    0xe04110d1a1f03053103020d090f05060702030102040905010e0a061a090907020a0b1e0c030601051b0a020901120506071715190305010204030312020c15040614010324020c 75
    0x307034060340c0300350815944035030403d50039400001003003580080da2158a04c0d45c1008174800d00d1401c10940d0521040111041914110403000e08081105201140c01e1103020301c10840064072504644003034054400805e441d00042116603550072440c410103504842c0c42d882e90746405004583d03000c0c00c00c04406481c04080c822410f041004091020161002e840c04040d03102d44c40041c0002400c5450303642c811031131407a00501118186105110892010300030304000700c020f10810407203990100559070041c820003485050885544103c3c1e061003820000a9004000c0c0b50001c600d030301403401e440e1801e03071252045405690340d5490494008910aa0822000c901d000100c0d1520b941e01d01c4406640c14000d1106011300c244030101d8500351800c0c0d10848259401203004c10501d80c0004001810010030302c01580b030710740b055190707075140c20741940481090340c0c4400c0890240030450f03120800d07003008154038001c1541c59051410160b8104071141044011626881c0a039034618025568500b401c003008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 682692706 1250 682691456 682691509
    0x281703030c25060f0c090302241908040c05090702061801022a070e0112020103020a0311160506070c03080c0a021f090204050f160e04110d1a 62
    0x1540842d030000a01040340b07580c41640d80d00450103595001c2540784544000200424040e02500903600a00314280901c012843d041016032180c0754403c00c0084042110010300100f030b403606146002d00e55585d514450407201000d011500291054001e90003040d04a050650760070400c0003d410860f15600140c010902103440c03040042d85190341e5a00354000581031035107070007000c80c8089903c94082c4042c2c1d481c00300e95601e00c500b0f205660181c40e054208110a40c1020444c00010011000003170416030700081451060303109911410a00010004096480c003000366960b0f1520703911042035515005560100d40010f014850741d810700342d810703202e00d080d6540c0c0a0440e072a9401c1205044194041c1c4001e0481400000740c02c0a100500100000354500042c01404200c0d04002c00c000d070141d41030400d1240e01a0302d040c54030300a103040d1511014000500c00410060042d40c000c0400001d40420511911001d80e009420b00d00c2006d80c0008103020480c003045002200e00d102034100070211042c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 682693956 1250 682692706 682692721
    0xb1e070c06230a0804080c0d0504030209061005070b0406090609150c02010c020d050c101e0501060302270a0b03270601030f0f0503162019140d0228170303 68
    0x131544140610101c50400542a03000b9040041d00074802c000281c0c0081d0620461034400c04080d0060403d0316014000c00c00d61801070720303a00c1452805007030100300350001001c110b865000070a000d076000d8000d0200d500c0a1a2200001c4000412a000075050080f95550340348140300e24915207482c0d078024600040752040c181c615521000000c0d019000704015480215480d0246d485001006c00c0c03040c68281c0408a200d0881e003040c0c002d2010140100140a001a6503c403800c8505a00181d50025949900300103415960300c0c2c2e0045c04044408420459124800400e5080c0700c81032340415074120404071183d41d196031003400b0044c12404040c0b002c03c08036201c0003407030a0035842202140d00c0c18000510007075020191038011141d1008070116802d0041e00354110041d008825500b903500725401a00f5442d40030024020003082403480e0306042400e903640c65000101c541c001d2b0052820300340600c0340c484c2c0008502e12602c040c174904c050004004200c903c84008405000015505540f07980c03c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 682695206 1250 682693956 682693967
    0x90703050912130f0e0601110a050d110f070905060f010c1509031107091e020319050603070b03041112070807060f0c0218060112020c070b1e070c06230a 67
    0x341400c1c030f0005082c0403034401d25100584028204006803042103180240c001450401105501445c5401200c405400600300040c604440f141e40c1c00c01f114052440710aa925003590a107416205200e2403000098003603160388070034003400082e40e0b80016a08041d0054a140708071160081c04581403d04404281c0055070040c0f00381e900c203151440400548442c04e51030b000b01030304a0748a580e65086078114038130b0811a8030010b020745800640c2189443d46802e06051101a0b21043c0700352141d0001d8903641d0103100c040301510030022515245d080134101840003a55548c1864025540042c981d18410000580041164000801811421705012040b10011100310b4644140306084038210010b0b503851190701c1c01048212611411490300c80d000401a4070004c40d0340030014810010034188100c04988075068600000d035940d0342e064200769030705852889440100d2a4080881c9810800c050701290004849039951200044030b410340c07110b01000340041d14404200002c0040c00303022402039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 682696456 1250 682695206 682695217
    0x20060a1d0402120708061f020318040213030812090c1302090307180c17100311030a0602070b070e040b0109060c031e120e120f071511040302090703050912 68
    0x40e00143c1400c1d010b07400941280d6040e039110010503040c108010007810300d050010240784001c0c1e41c8180c008108140a5100d1044580421560030107070a0b24840d6200c58041743c8a4480d01559110b00075070300c2c145489240c10409035210300ca05d014020880c1800c0000c0c0c040941807004081000c0000d51609000003544104103040d011b000741040010780c3e07200c2c400f002c501d2100c40c240100d41154038000080021001440601c1c2102c1032505026203600c546994400343d95000c984400d4020301500060700c0d01d41050401070200d400011503404001030b0951860103000641c03504210070302c01e0030400041e50110030f49280018448102000b645105001951040307010b0b04209450f9100c131010b0b40383c008105102000411840b10003220a210780e442070500842500010303010018128840300c02d6841150381d4514903140115600b0140320034511000300c44500d01c00c04101001007111143c0c0240c00c1403200364858030000f4001035a150280c025644100031180243c8201080340002c0100da8015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 682697706 1250 682696456 682696459
    0x106050a270f0903050d0b09010312120b030a0f0506150d08030a0b040e0c0f030a0506150a210c120b0103060c1101090c0302031e0304060518090420060a1d 68
    0x200e10a500c4156820303c03c80304114001d5860b265a8209842194150382d000c000c0319026880d284010400f2441240c1c117448489610314021a0000d54030385100090041402082e500d40a1f1070340030010046450440c1c1c542a11560030b5070b101e5600c260f0b94041500398900d40942014451402c4400121803100079944001001c10004920512101140490743c103510f4600855212114403030491401d4188600070722011002444020050354841d0b440b0343c8042c00301d03400c90052142c2070f07080d9030340d0255544c060304d4621401881080e601850390851880b11b80b095a4801c81c09202080e03100050310164403542d000741c040c912a91035650303450010501c07c000b082c200034081c0c003106600c13a02030040c0c142040c0140d5060944d07a0450040505180e201c041b22046140c00780c00d13188810002006440031a03985003032030b90702e9500c0054020b1200d1109003071540d1000040c4100401c018030741e00d803d0381c01000340c01c00321040740f041d005010092165180c0c02c0d0114280c404142c0391110380030302070200c1c00070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 682698956 1250 682697706 682697711
    0x6171308070510090605061512061809030301031b0b09090603011d070503060a140103060b03330c04060c02130b0603160f0503100b030403030e060106030b030106050a27 74
    0x11078954908041841d019980480d13251140c0310300b8000640078a41c7c03c250100c4208024a84030300d540d03070311845208002201d0482c003600141f8595522004c078110503070740007400d000d071b440d00d01f800a0701c2c0d9009001c01c581203003c203699001070030b00b407030f030200140c45190341640d140000710410468003820042200c1c2d415900da0617020325940d900a00d01014901003001080810304200c200740c1840002040c52038003900d460300c0d4040b22070a0820a504490300107200040808640001c00d0074684102800719480702c4002d100e0b1658101146085003030f44210b1498401c680310184030404034840c074429000020050052000585051703040000c1c4402d809400095003007181e00816800d401c12142e1000028604004020140d000b000e2001c0226a511741685907142ca0782403000440d582d0702421040c02c00110004040500a5000c3c0c8110008101220119a91100000c2c043c04082c0c0d600c40c02542407400000ea542001e020003010b40301201c03024030400343d08501c1d02d00100e0529003505107594 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 682700206 1250 682698956 682698967
    0x702210c010f11040603060801050636040312051602032203061b09330203091f14030f010b0906120103030507021c0c03030e0102010917040f06171308 66
    0x80b10341c850280030003102c2e110a07841c0d9213000d034090304540d065401074410340d040c00d080020b00d540e102e034505000403428114194104000c442800140c0c0d01240b541c44802c46181400b00b419003007590191400d0b81800180402c0d0350f4020780d1503410090300e0060001d68000c1c41512414a15140e0903005245441030382c8003543c2e544e031510401c0c0e0f64054002c40700c5400301444981c819a0010700c03080540b60a1090045421100c5060144011b02030805003811a541d04100181c0348280116459203800402c4c0043c0601c440d24607013002c514801a010204402d410003059290041d0282e031303c10080c4440002640c0e1070003844080303540c014a069035120310108001004503210400b041d0285000ba51025110581c40c410721001c094041d003c94528840f00e160000010400c4141c00c091300c0d414941035070448110740043c0e0140001c05802400031070b000c54030b500403400c03171009003045403503000c50410f040ba0f40d000c0540f2030a03004041d19040d04000d40008080c0f070100000d1541440c0b0420040703107402c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 682701456 1250 682700206 682700231
    0x110a1125092f0d0e0604061a0a030f0b10032003010f0905060f040f05070b040609060e06071112030f091e151e120412110703031209051f050702210c01 66
    0x3001211b0848906e0703a40c0d05aa0b003981c03940105084e03658000d5503549603090444d19001402482141d004201c0f89059001a43d0780c5115000840211340c07200030b4800314601100c02c5031481404504d40d80c02903180098140c10100140101840c0b01d030414041c00c1181c41c0e030400d00c81c2100c0002c10541e99510343c604840c1c000703003040100e500100074508040361a18100714008143c400e956100720200020750800e4200d99942d00e00b21840240e0106075616080d801102082004c951002850304a01011030700d00c041011880062401600c03c075846044c00610350240d5180701c00f8501280c0c3c108600c800f9944416003414003c080700803080201d48801c4030380c070800082d154807035242c806000c3e200b041440b0400005034603c2d1130366955800c0c01300712900d01020b11035480030345110180400104111454451003598003284840b604101a10251144d1030640c1d904200c0803a007801e051072030030000540503031002c1461150401c08007403540c852900103e07400469003009030011181d541c1c80000040c1c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 682702706 1250 682701456 682701463
    0x1a071704061b090f06050406120b0d0215090310090c170102070b01061d01170606130e041209080c0303030402040c0509100207090f110a1125092f0d0e 66
    0x200c4401d503a62504944c2040c9010000004070350040c0c0c1801820300003880456001081803280050409000510042550006a00902001010350056002c00000d402c032481100100100e07a425002c82d16003183c031144441c00c4405400e0301410b180591a0240100ea2012903140ba0b1200080000b60900600740c03100c081451003030b070040d40070a00309001520000d0303c003c4040000315003400d142400320030b0040c40c0d01e4000c400400240c810440001c00c4c403030f811280d00d68040640609900100c5502d090300e81444208844038814000c642041000249000d000480c1d0000007809030142d82180c560b030382840090408984035105101040c400315209403581c1203861070885099000b44165441c00c0380b040c2c202c840e0944840c00303045c1050040e400c0760034200b003100c244085a2030544400e81c00e29652034240f00201d0302080140104001c4c0b1014291448610001d4485030308040050b111612010b6408099110600e00f200240c1c04107511091090b0000c1c00100e030a03410081850f10450018508 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 682703956 1250 682702706 682702751
    0x100618030236010302090a09021f050403050a060204090e030a0f032a030903030c0c020102070b0d020f0a0e181303030b0604050a0b070b1503070909111c1a07170406 72
    0x9900000c00010415490a50411034100e04600d034200f1445011f60040382d100840082d039440600d420301417402b6614800c04c1103800840d00042a18001081032801a020354060301c14035039183d003855940c6403145000310481d0419082910f4036040e401e80380006034050280c890000000c80d027106000e20505850032071843c8081d41ca03590020f9076809515000e400c5174103202d003810800500b1403001e00107036000551b04064038480300c0301540310388035154210701902c901003244460b5540458541891034110340085400481111040d041c0d030b40003100c4d02d615100850350341500307540b00d070920300100703003c3d50000030b0355600a8071540c5890346403400304004014503489071011110000d00780050050790210f00d500004c1d81d5000d41070f20403104000a55812090007440f081c680e07503180c05010003000d80d41c00f01100c40c0242045001e090040c03a8610415404101503901c60b08411860390349550744100c0300d104649549445420302d05903000215001d000800c11a5021b0703840984d2104290312030714464 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 682705206 1250 682703956 682704049
    0x14061c110621060102100203010b0702060d0b180f010e07300e030a110106050105030c0c0f0d0504061d1003090201090806040803101208030c070521031006180302 71
    0x7210b81c14114002442c0030400424601010310600043c050211030004960906804136006030b00c4002d071450540046c03070580c80403903100002c042c4280d4460b8211000d60310801c0840041941c903a81c0d42e26135400c002086458000045101000e01c404440d0514610b56252814140400d04190401540e007110503480b10200e0b560710208035280e060354004080f0380b1110402c402841450714100000e07203171340405440d03025840c00110f80300308602c02c00c200000000e020740d011203031880b1188802410907400340c011180060310764032604840826140c034001fa00407001e02000c002d20286d100c210018210440224100729030080000742801082010901544c06910703581c3d0b907814442201800b2000d198841c141440500c0700300d4011404c000c040d2584928182c91407a901c22041c60414280342c3c0701902000301400b201100342901d16103e01a612480c2c01070842021261078413026200303800115000044143d0030181400107081140c24400300318164240c048076002c900703000c04a0100032100382c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 682706456 1250 682705206 682705267
    0x1050108100f1107030804022202070201030516140c0a140705010e0a0b0301031b18050a060602070b031b13030609030f2c0102070b0d14061c1106 64
    0x14207440015206010b210140001d04001d6194100300b042264000d003100a400c6c06000c200040654480d80c0441c0c400e0741c5442d080544400d50020520000c2d00704010990010f4948800640d003840c1901c04401028040c0d102e941c0c0d84440c0c0740c0000220f5204d0807a2031818014903c1050000e800c4458051f20440c01030080c00d4291b040c0400141002c07100d160940c03049010040410001d80c2e01c9040781d041d42d03001210b00301d02d9030b48507644008074150f90f403051805a042c040d4442039500319511a078001c2c820307038105100c010341e145002c980d141910700a28080b0101007010a440d4503100704a81c840c03041c40554203003040030780259540132a103a940b042d10010b840b0140300e020198401c00c2d4000c40300a90030010300041e91107a10202c5407004207800c904491110510520aa008010840c01044401400c950780c002c105421b0f409808110305040d0100c1554011580610b030142e8842645000d010840d810b000050300c50182c1c1c2c09a80c070400c0c0d080b10701000120f240001c4190100803150042100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 682707706 1250 682706456 682706473
    0x40b0607121e2303100611071211040e1b060d090f0807170a08220206041701050a0e1504030c050d0503041a0c090d06020d0e010605210606040e0c0301050108 69
    0x7100d608000c00d8a10640003401042007104001c0304c08034040070f07070f83c1507d01880381c01171410200d4542290398008503000810340d84804200200c456081d200351a0650b81800340d1b18014060755170b101840c11200b45030200c0d0b0719101040c0e081c20409000360840c0d6681c0402d488000340c541031001011240e003034541e62000500c0c0001d014848c206a004800107070815171a05005400041075080c0103041e00c90204440c07071500f9081d640300100035500a0300140516a541c2d640e0703056030b84070800000c2e00303201035085c140058030101c06d500c40c1c020420a480c000d4241c01603010780290400900420031014403070b044c01d4030b40114608200c80072480c036403030319010390301d003054104980360282c18a04054000b40c501c080004021a500503640100c2040c1c0b00c5400d82c420341e1030a40064083e00d02d9644400303251281881032000b05400c04412542c080d951406000007490031101d041c0345003a01c680c0a03034880781c04038200c2d0420340e100255910b0528255107011506000103030a584007a8043d00041d0700010b01b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 682708956 1250 682707706 682707737
    0xd0f020d2004050f0906060d0c02060a0608031303020613080a050d1e09091d0a050c040e0d0905100c05031201091104030308160c0c030c14040b0607121e 67
    0x100740d21400c0c18044024189450900090808041d0400700c074017522100000c1241c50700e442043d01d800c152440014043c0c2c100d182002951004121460068941030050003e04418088107c0710204c0c60403c6806126055030240501c56020506403440200740800000754050284001184603101c2c6014000914259070300a045542d1803841e2084904502c8003040036507003041e02d90040310010900440d041507620003062112854680e4241c00e8012000f4482c00c0083c0426a0b9154810444041204940200c0c07815581d07506110500d0200341003070410b00c100c0c500000caa50141c481c0e03180a144007090323a6200c502703642080401c0800c00c55403000521090345103006044c601020300c0d03c1c0034241032440d20000c0c60b00c03c2c083c04004074910000748a580403482802094802c03034108802003030082d030302d1500744006007141c4241410880d4a00b9030300c500b450507020321064040001c042c5414220b1079198144140501404002840108a154246a055080012100d203041d031114885c142c00280c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 682710206 1250 682708956 682708991
    0xc03030d020403061a01020d0305071b050619051314010603080409050402090108061605160b090304080d02030301140f04090c0902130b160b130b1005030c030a080f0d0f020d 76
    0x14000c41c5c00044421079001c01c0c1e680007440415051551401107100c1c0c69010040e100c05c3c03503c6241c4420907074211100c0003070180001d1042d0003480e00c041140841d03180e00c50404c0889034207866890590f042602010302040804500d02c5d03000503006d0000940c60750700d580e04a6207501c59400ba5020f9500c8501f040f06602c0c1a0040078010468003025214601d0b14000c0c2c61301600141003503200703221002c14092840c0c0420800d150314070380d016000c480d85060140c101035030ae401c41c2c032170700d0098440c1000c00c1c0c40052000c01a00d04071800e0400a036a10b1190f4400c100c0c40d88055600076410651321ba1040c404140e0b03201e496402000001c600581d04c01880d0200c0c05c8a01c00741c4c101c20310086040000726484080d005880702a203801801c028a6504d803071040e018840c0002310040e20f035010003001c0c84401c1100310041c0c001c48070304604076210008050705041c0c680c1c0c000840580b03640c1c410b01240c9124825800180610401c80400003601c50500742d48800300e03041205070b006195a43c50589500700c02e1315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 682711456 1250 682710206 682710221
    0x6020f1303140f0606011808060906040b13020d021002030d0912020f032811010903030209100f080a0b04021323011103090d060b09071e090303090510020c03030d02040306 75
    0x318080c2c402c0c514030551880e59508080c003907034104040392061f4214441500764038006005400c0c1a80c0950419aa40c81d5495a040c3d800f40e61001400000c00d807510000d003598142d45a0140502c01b81d0440d9808000a0007660300c005420350004201781d4001803818403030001000d109101c00035007054450070083c40c042c0c1104c9000362640c002c0055a010f901240c0101c010b030301c80301414030480740341c214040b03032014806c0701e81861940c2056121010141c0540140040030b9050f00e1b0b520504501c0d001c102c0d00c806c84008004086545400894200000e6400440e59990301030070142c605180c4401c08040c942d4582e000c4d110101074488104a1a42d1003420900403010907e46031185a011450090b200d1003101c1c0b0303051013004015000c000700050b0350004680140300815006841c0b803c00000380c10030b11074080b403000e42c03225500d4000c402d9000b076001c0304c2501c3e01a900c140c945030a080902811071400f45101c401e41c82800c0c5103c901d41d80410007000b00f41da2074071015031950b103103182000c20f46414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 682712706 1250 682711456 682711493
    0x40e061f090c120f060806040b0f0705040501050a03050711030c15010e0405031803011e02031006030203071209020a09060605130503073606270b011b06020f1303 71
    0x6028810004a9124544a0f6002207000000458444410080b001084654010402800b50004000900c0744d5182e031240301360711014120085a9469100303d90074030031402814086041807103620200e0303120364000b43d4044000d050070100ca00b200880f451454200c90200007180e400f02070300c0d0b40744140000f0200d0040085540070081c90a0550300c0c0c544038006d61144c2c240b5000102e0f261146541c09400414014040c6501d056504203c5040c00000e54411200d06281030350500c0c000600c00d109100312442001d29942d032a240c2c4a040f44a84003424601805a0b8080143d44011410f18020b100e00300040103140c0304c2580d07503401c40491030526800c9034082480b07600465020810f00d0b90720841140601c0000c403001c986514860079848500641c1c070450070000b4501100881c2d10078044600e402d1049005006187d0624882d81d59415540208a103a0020740c600d0740d9094482d58145001d03000900c0785a0140c144142c4c88080d082c51b401001800d903001c80302c3c0808005111140c16006400d001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 682713956 1250 682712706 682712711
    0x41406161803080a0c050c060a0507020102011815090807080c0717070b0f0306040213033c02010503091018030e0102030705070509090c09040b04030311040608040809040e061f09 78
    0x91501d0301061130282c25559014030030740c0d0407034000300b000600c40c0d0080b1000081446856116004008001c0e4000010481c007540ca010301020480c03040d0503242da4202c0d40100c551394110200444c0700d0141940c081c2c11036120f8018020300703000600e401d02511111340124004c09241e85040a0300215a00101d40303402c1d01c0d0020380d000e01141000d08212040c8143c5001190342d25124000424001c0c4148a00006506000310010040010782580c0b0054602c032203545100d202c0c0c01c0002c01017000c5000c43c080c000440714440400055014202441c0d0000070341c070513200b00c40d0b030410991044e50009031040070140b00070110001010b820407806000c12100703100950511010344e40b426900d07495030103024070032909940000c842203010003030201d800b84c001c1d002030305c581000d2500315411a010b032000c90100b07080941032155410b0b007100780c40032230740c82e9a00c208054031145c8900c1f40341d6220504c040c1d00030f900c40e44034000c010001c210103030054492a480c00c2c01002d0740a491a00a299038014045050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 682715206 1250 682713956 682713959
    0x30906010527251106040f030e0607060903090501050f0904090302030922110f09301605040207080409110f0c030a0e0301050601090e181504030e040504030f05030414061618 76
    0x800035120381e005e47c0c0040545030760002400e0030384aa07090140303012780c40000014184100241a00f14090f1540b10b5220a0090350304c41740103540c90b0150840c8100b4000080c016401c5034a007542002075103078001d00541e85414641c1c03000c1412464503001400b056403080554400d010501d105a44080740d40380051800d001140000c0c6095200e40c440c40c0e8407401016400c00c2c1c500d04c02000c7c454400c117800303924100c6008885c481039124030018010840031f0102110004030381c10b16008442400c0d034002600340c606420107030b2002c02092080700c00c42003900140b21442c09448407a0040118059007002180c4820f400740c40148220401c103492400f80c1d05000c00d018540c1d030400c00b80301c1a5502c40b001c4001030b83d28081580040c40700ca40d54955a44589485001541c20307204856000394002d5540301d419510010610052b51800d03540200091900c3c0300381940c0740d10039070145411610500784403610210b0007000740d182c00c20588581c0c0304240c00c40310700300e500c6822075144021869104c00504007039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 682716456 1250 682715206 682715237
    0x906050a050405060306130e0a020a080601050d080315030a031706120705040902010201020904020703030b090109020301060f210509100605180a0c120c210203090601052725 76
    0x5000d0b40c46102d0151a0100220341c0d10341da80c403411202410007040030071030101900d2425070740e02e00900003a406400703480804102e1782d801140c0d80741aa00090315841c4a08269540d0102941c07004240690b0200c0110151807240e0781880502d164500035501d2034102c850180c4140021000988218840c200061810f61310408c00710b4108219201110009a80c848600040c0d01910420011581c01440002c46c0750400d038041c1d200c03040f03070103007034844003801e80e00c03460504120b2000f1f005510110341480c080003203861080c404c1c05590200c00401414118400001d1030a807141640d45552a8024800b600414000e0b48031b404018a8110307a03050444161002d142c2407802e01070f2008007280d07291100a4109030054140403030341410740d01c04009200c2011001030480071011104840680300700c4124440c10214020b80f0b000e4144980a0720150741307000204051507040280540c044c0b000e46803032070350704c0d010401001c1c880c180f810000c60314001d41c5c69548030900b41d0029081c003881014950715100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 682717706 1250 682716456 682716467
    0x105011d01050a0302040306090c09060b03071e12020703080f2202040f020705030c0a110f1008060109080102040e180a15020c070302040905010902130b01020c090a0b1f0906050a 78
    0x12900030b00740103588808200d4110040c0c030a83c0c10242c00141406000700400c60700d100128200d4008603005c0243c65255450300d0b000f0b2006440700e00024410f001180101184002012100c141c24200070114500e541e181005907044250700394041916082000f6000490411444d03012000134072900310300d05c5401250360341d4191003801a0246075156581c205910b00c69045509540d0418120303030319410440c0e4a16690094240101d42c005064090300300281401d070460ba401c0c1e40004e140800c401002981100d0340b410061107141005198800080c0340102031000300003030f007085a19001a0700d8482000708891508020b03030141c070350140c2c00190120303030460f10ba1142d0658098026a0714902061018034012044d000658003501d401020010040150700c0800007920941e030001c2d021191140c080308940080c01c03400e015070020440d5850514103500ac0d1907104040900004031501d180300401ca90711051800440794040490105403525004003c20f4021f05507490003a145c2840c02000510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 682718956 1250 682717706 682717757
    0xa0504050f1006020d050d15031e03020c04060e180a0b15011404210609020402041d090c0913030c0b090c01090b0c0a14010b0d0305130605040b0a180f081005010501 72
    0xc50f03545140700c5410100c03523035810046804c19244c1800e11102100ca03041c20180e003408038094440c01c14141442c0c1000c0c0901002c81e0001a401c0310315079200f0448845403a11001c0c86c030401d0161001d544006065242900d00074801c04012501000c101d0001426144d6215003410040c2c0f001d00042050708021030160440701600040c00046a400785850005001c060100951280c00410003040e18442c4589084110320001841c2d02c00e5200c5524070750b00d0702460090150480105c1000a969000c13602140ca11035110303191801c8040d100c0c2d01ca04004001c155020b10803a00044000c1e0000d69000c5005009481d602d50390514015611200f982e649a9241008280c01e070f00c4210080c2a0400398800422042d0141c004034400f02146001041c5501030390400a09015020340480e40d94450810f8030f054a6207910712901d80500e41030b05403039904401e4000c0307201e41c3c0c421002003006a02101c24400078202040281040d00d111400e04055a40507081281040074a00c101d00403103044424045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 682720206 1250 682718956 682718977
    0xd03020702091f15080a0501060c05060105011b0606030804050117010e01030b1e13051b0f041a060d0e011d03070f11061c0f06061205060a0504050f1006020d05 70
    0x41c20f40241c99110400d680803e150140089808800d2500301050501c94400d1032402c010341d81c0c85080689804010b024040e020741c2c0002d00601541d4058001e90341c10100c50f03100c41c2c40c0528540c0e507600030342c0c0c5690021200440b000c1002c22032941c100000e8840b92024a00c401095070524042d102c140c40140f01c0030f0301801506004c138080d1050f0340380c600301c0c01d0194800e20074a86030601c1100612011f071758007110031303204006000b114650070b4a6040c0110800525000035011601c0800010340041501000300b81401d16051055a4551004000c200c20355103002c5180707014008686c0c00c492512400401028031840860304074100401200c9076194000400c0780400ca49041860b00f5420701c01c00c154008200040b0301a02e2400b183d40c401d91803802c070b0000e00c00300c03691441c848142c03012440340301c6c0466409400c2418542e550b0704000e030b00030b602078041c0074202d60b140002403d030780c82903401440b01d446820511108104c0d0040d81c001508041c00100100101a20000c080784550782980 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 682721456 1250 682720206 682720231
    0x30f0b0103021e16080414121b011d0303040f060e042c070801060b04170312041509080d050105040b030d08182103010e0718060e03210c0d0302070209 66
    0x100050420341080d080d04505c0315500c4036283c0142e180450880c1402522640381969181c0745440c00154448102048002c0c04440d290079a005440490103804100507290380080b5211150700c00700003400003410045141000c2c40e28152014207030f0070254201c24051400c001038070600d4904268500c00b0042c0e035000c502d12243c0c2461801f030078951325410a5440d5420500d0004102035881d01400646546200b884001d2030081c124503034a02c81c4034142c00708103803410009408140400c0003510160b68013400816185420781e80da0300c042e4405140324800700d0b641d00051159050a1042c10f5601c50700f41c00078954130000010203041c0504c0102048100710900c4480c0e8442c0005100e6008562001140a81d00c5003246142c1c0403940c0090055018070680c200002c1c80741c902c00c002a07285a1801003080100c1c0d400d1140854540d40f403158455018481e03002d0101680c1038003044071002c0045512116283c441c400109400e20b6812280ca0007014014402000540c0d80c03c9002c0b0740120384030409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 682722706 1250 682721456 682721467
    0xc030b04020d0c0b04060f0512011e03050303010b0d06081906050a020d0203040b0601111c120204080d0c0b0a02070218060d021203070605060d0b07030e01110703030f0b0103021e 78
    0x103040c0b080560001444000c3c8070a00160200007400500709890858488020001003005c04650f90300440d60b0480d1004550801000b500c0c1d8418928a090698035113081401074407515074a1031a402a40450311b130250005241c24203911500c03c0c1006800048007601110341e240141c000c04040b01c58001d030007030350f0300d0380030814603401a8120b90308910408010764680c03078507003402140b12504841ca540414030480c0c1d400300520000c6445200c5808000c40d0948a042d042c00c1201d02c240d41500c0d02251907400c210101343da0708200841c03e0048e505c0da445040e804030502c2c2101e110403001c1c010364003203030060043d00c0060780d4a00c1c40b05100c0e074610455550b25917803840042c04840002002940001c0200c0c181580c082002c001824100e015010500007511640d062080c20100c440000e019a107a00000c121400c0c442d0300049560040240042448071148500c2c0190b5030200e103086001c06e6862049103d151018013030f10500c500d00342011070800210440d011303210f018460405400c1c981c0080c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 682723956 1250 682722706 682722709
    0x8190c050432030303040b0109020f160b04020316150e03030d020a0903050601210b040f02100210050a0203040201050906030901020d060311031b21070810270c030b0402 74
    0xd6500074031440512410310050340c1088440094a070110311202e005040c85415541000012240181e41c0705190100680c80c00c410b50009400412483c003464904002c090584580002d00181b0706d40103e54280c01c50170f2902c10107140407000c16407502418105d00c02004994115106484c0c8040181040034001068500090440c80f805c0c4012143c203102203070003440341d640140007070140c038410b9003241c41c0ba07603d602e285001a403048400800c5120000c04560008503d1404079800a2240007e0500750340c007940052003000c2e01645440c016800000340c00101001d43c010035070402c5a11408600e1820603400003803003807103050f841c10302405000002c19144d074400d50450b030060414841c2000b55544910340800c2034030162034164860b114001300e103444043c40c0451130344d18090040400ca000f00e400c94a105843c1c1c0d00785500784080c000c10308001b41514091020406034081d44100107140c0c007801000400e6010b07100c1a07020030b0317800c02d603200b0b00095424500500f035980003802c0c0706c0281d94520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 682725206 1250 682723956 682723967
    0x71502030c01050126010605060d0207140706111e030901050307090b03010311120d120507120e0307033f091208070912080f090303070f0516050108190c 67
    0x1032507400350342c6400c0c00010310740c1d510070703504140043c41e061001030929124215820f840b014000d2130303845041000500b0044071035500420b002407084001c00d001c60b0080c0d100c20304082180d8880800b0030401c240c1160561401d00c0780f04041590300050040528070003850366500c0c05460389840c14804000082286603015804c0d001c01881d01940c0191780b580c41e4681404103108016001e409221004042d01c43c03074201141b400b00d80c000329500c1c1582104c50308098006044080c1c03280c1c0070301c12a2030b919001042103004003186149018004c6664145a2500a0a86100d00d907070130103130504801b4660707a140039202c04214150142200724002c01c400c404a8000301481c0d0402442043c400b4100c8100540101700303613204030f14644a411031180c0d5143d20620407002c003180104444400c22170072044d50362a0001e4641010050226810106030350382d800906d0840341001d50305548410303441d8000c00b1503049034501800003881d04a0a904142038400504038105208201c035545030b0942000c094410f0703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 682726456 1250 682725206 682725217
    0x702072903150301180f02030714090411060c01090b04020a080705100503041e0f0c0524160b0f180c06030a091703070314060d080a1b0204141906050307150203 70
    0x400021011199601c1c01900070f016081d000c072300a00840c5400200401d4006c180710b040200a070a800c03082d40d655540340c9103184910394140d8080b4060090000c4601d0900c02c4501c10341c421814070003941014010083c0d000d4059015402075030108100340700300c2e110100864014501c90404c41d03100c1d141c0d4035081c08425000110000081c140b0307007695061022100d54213031814041c10b03c002505071500e046c0007465400400100321043c41c0c0d14040d10321480c11006001c60f003041e18a291035001c803655030b513a056201f6140701c210000844184002140582618411025401c004144200046000c6886800000d207144001a40d0300101014843c030403100142c1a030710508010303900e14203024060001c14030000d02141d06104480040c0003424130328000005c0c2a0450002030403c4002d01046035420502d00c0b40f1004209040c41040050700d43c0d02030100c5210f8002418003142c90003041840c4000b2090921a42c070b141408010440b64501044000c143e4030704000019a240d81c0c40e9050b403951240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 682727706 1250 682726456 682726481
    0x10230070c03150f0b0907050f0703020c0405090102040e07170606072307060201111c020f0c01060801290f0f0103091a10120c090f0e060702072903150301 68
    0x41e1640070030381c2019403010306107000c00030301000810581c00c14043d0480003280e80d01d0109108109e003810020240c4041d0580c131380702e84121000c4620b40d02c04181543e40c02e540c0b00d501607401283c1070010100c0500c1b0554400101c2c5010f50013400c604030007086010300546132a003e0580000c2d074800380300d452244901c407145000c1030a120118140e050036600e0241d440740b100107510b005050680400400d00705c5588408034070074240d150303d500a081e00250722130910130341080c0341000b842040d00003c2c0580d0004045401c000a55030701a40280700c081280755420f00e00d045540800c1d003400303546640321207880c0801600c802804440d81d500590062a4540019000c0d05840a50034070341c4043e40c00e5588070380c60752403681440031317994409107100d00040c010041000803040c40500482d00070341d00030044640440d0700418200342c03185140c0d0401c00700750b038500016000020107000c101050b540c44c4401880711200348200d2611440ca00003580009004403600030624043c21a40d40d80c25044044686003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 682728956 1250 682727706 682727723
    0x20c010e0609090403091509051305070e03250b09010f030f061805010503010f050f010324050f1f0f1214010212010602060f011215090c0b09010230070c03 68
    0x4c0c07509000d040b44d1014030500050304011050002c06034441c14a2808443c4042c00008203950009440000f911000b80381340c0800c6034a24107500507035400c12001000d04201003198007030342191680d50010b60200e070006820244204680101640c0c8060703441508809071800094882a80005501415140d88548030b81001076140b280740446d80e0313106a048600c128000c104440f400c03e0306505560040398064810b00c100310040000c01d00d128085070440741d083c2c116085075209a451401154400d8a8030b1507048104e07402c22001809100480046000c01c520390454145005107502815815006e0b4a807070304104003041c0101300c040c0303d4907880074034150000d5446280300300d403003881541d00344220340051041102050b6903140c682c1c14503060f142d440801a202c000d090b11840c9000000c8251801d480391384001c01d08c0801e1040c1c03403d5000e400d95800c0c00b5920135065000900d000441d103408034440900307200744204000502501d400240b145c0000c1c54440d0243d06000b803c4404a600c094455039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 682730206 1250 682728956 682728961
    0x405011b050a26060d060603050d050306040507080c040b0a110f010209210c10020c0406060207050307091103060d0c03050105040803040b01080c0109061b0c080a05060f07020c010e060909 82
    0x190072001a084000c8140c1d03440c1d020f40407500c68900c81c4446081c2a03c02501c1d2400840c03e41d081104248210300c2c040c4c2001304540f03959070f9849180c99104040100060f50200500400d89130900a480e000542454004081d04041701da0842a03c524402c03146401400078460070014007600700b003d40d100e082000d0350700c1c070381c0e00000d1240032394041d0b0f0040d0301c200d55801c210100030810f1801c007850320540030010100180814180b181d2207400c1c0030000700707502c030301c0d0b400da070082c0e5a81c010ba0015268036405810b640b49408103041c9400069042200703150b0800e450582e442882c00142c960001c802c942035100b46007130342082451038102d508050000d500b04410001842076900046008070f10910b00010141e93740c40c0046e49504001180a0010355050801c0243c28864041c1d242c5031010220400c060305925901c102d41c0040e990f204040980103001c091081c0001406034a0b800030314800c0f52580f520704030070000d4498128040c6281440304040301110161110010b40b03904100240610342c0d0313070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 682731456 1250 682730206 682730261
    0x2091f590d060e0f03030709090504030516060b01140705150c130807061806020c040f27140304050d1b030b0705030610020c0f280315062408040501 65
    0x602c0c00f00b001e5451031141500c0c8500001000041701d10600c4d0507038410550b10309007100d0501070b00010700140c00b00311042c41201c00c0b23840c280118101e400d02ca0b883c0081c030b4550b01c0c070024016056621259402c0c507401c4c010f2001180002c11403002203800d810520340c9070750b180c12500f8454015a0005680810303110001300b105440080d000054960b65120b84d614408820025842ca1007140242c10040c0c0121011071141e04254008184100143e41c0c00310303581c84042504284031101184500c03039292034880501c01d000344800f807843c1035100b48024625060a08000c11403071240104002d0041c86180320300c22002d1070844044020750384c407003404291803d01c01c90080842d0801c3d10800d00c26910010054541c40c00080d5011240f20043c0c4000900301104041040c5ca481c0b800e55525a1060001d02e00e0b104075541281e200039502c90801484003000d200c100a00720365080c0c11100c11080c0500d003a81b104424009240d5400c1403030300d0003010344d40d51441e009016014004040803182c80c2d104a10590 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 682732706 1250 682731456 682731461
    0xc01021209030c1507050a12110f1e030606030103030c03050c0613020f0901081c030222180902090f0c0702030d0e040c0e1302091f590d06 61
    0x403928a1004c0b219038001c5480e401240d54001d90b0740d02c1c042003040103a41101405600683c11006403070a001801c10042d0104d01d00c940d00c00380715108039050010300300100c401d84070f105030030740000f0203421415072130402c011640500c810300024041c0020145a00c0415204404403001031240d00e00341d904034206070130030726003200c100f03c401c030301c941180c130080051820144001030480d00401c0c014480608070149444542117001391a80400d40c00300700700e0505141c030032520b40700325003142e907a8010640f07000d50301d240360001000d070110f01038204400c240240c1d0766544156085000008905283e40316144036901da4800c004009404d03028910303031050050340000700e5004d101c600340d0307003803000c9000c84c0c100302c81101020b0700d402d611079aa0a040744034080c196000d04804d082c040c0a000c0b144411081012903c000741040800180009050750f04008a42200d4101d9581c643d01d12406404019001c8950851110240701508151604418a03100c084082401000080c110700101001400e01c00701 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 682733812 1106 682732706 682732717
    0x110d121412010e091c0e1309060f0f0e0a030206040b040222062102100809010f090320070305030a0c080906160605010503210c0102120903 61
    0x90400000c514076010f0300c0041e803881d40915014007910b01d440009010079412045110f1410200303900134030700000719081203a100603040d480b28100c1c3c00600580703202808007400d01403103101c4059a58800c03243c001c400c5005020000382c810031141c0e10004a40e005006920203c000360200e01480c507406d81051000f04452150f101d1514480762106038001d9040006503038581c100480020400d202d0345d4070810007461401810a500080e2540c4841e50301002445000070004c0c2d821a070a52188040382c3d06008200035204090130020b00203e08a4440355030882c80c0da86400464000160540491340e000b0003c1d4503140c0d101808445280c00354400700c542c044240190340c095590701c0d0213080c0040f00f24080181c2030507142411816140c06038000d90194100d030100700c4407105084030fa200c109850304c021655a240d070f10603a9009120701004035000496540500025220120080070f = true := by decide +kernel

theorem cover : BRFrame.Cov 682553956 682733812 := by
  have h0 := BRFrame.cov_init 682553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 682553956 ≤ n) (h2 : n < 682733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
