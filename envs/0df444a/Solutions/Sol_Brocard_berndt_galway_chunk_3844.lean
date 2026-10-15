-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3844
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:50:28.950136+00:00
-- url     : https://prove2.me/submissions/13864f38-00c8-4922-b4a2-9c378422bad5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 691187050 ≤ n < 691366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 691188300 1250 691187050 691187087
    0x3081206030d020706050f0d020a120f112512030b031c0e0d03050d09081806070b0a0f02090411030601020708121b0c0402070f0b13023f0c01 62
    0x401c80d02c041e0b0b000c26444100c0d0300905140340c81d1f010000001041d8043c1003403101c0080e101044091140c1c0d84003204400400c0704460402007020442d0b046415182d042e4078908030200f0400106c6071030000c03241c1942c2e260400c88845407a044540d40c5175000c100201840f000001d4490a100a4900c1c0034405500100d001c4003002228a0300c032100a880c00c0448505544a54540c000803024940140d08840d80005103182c104500403c0c1d00c3c00c203046810100c3c954405031640200000c030b034200f40c4100ca1119802c0301502020b5034130300b43c128000d04040243c0f401060340920070f074480c540f03130741c000e142801c2842d5019035180d14081000901e481d070f040e889880c25034860f060355900e07001158101c485468a1a00010140c140d024040f4038101c40401c02a422900c0014054203101e5445119100301c2c0c810b82a40d40b007034460085c01c1101c82e074011800780d1310a0207a5000c0d030404218281600d0103031441d11002d0000d200386561400c07007001e02c12000100e034201c88002e101315a1f0240707080108100001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 691189550 1250 691188300 691188313
    0x6080601030503071401140c280903210801050d1506060504080c040605011b05120d02070314031626010801020315030102070c0603050709080d02030a2c0415050a0308120603 76
    0x12001f8090006096469101400540c101d400400103c5541c40c00e131182c0c0d421003440d082018000c0141040d072000381e4260220310210305031603c01642c0024260f0340b9a071030200030b034241420080051624201280c1e407014040b6910301c149042d0040900505087d12410b4480d864130721424184103d032200c01e403240e480d1250a0001740e0300002d2038102c2e1810390b40402c500180c80d1601c81d25000c13138058403101006d40840c0c075440b117190f80d40040c09201d12a956a04400c1d5610303032156281d000941c0c0d69501c180b140100e411a0512480340d070710f0114524000500b10740c811482c0c60381c80700300a820880c2c05940000030803850303030001a4030030b17030380141a0000c5260103846d0f01e0344410005680242c2c0c00b050340302c4001c5030325148216250409040315400380c5100304103041c40690359a020485002c0030606c941c8250345544a001d4003020b990110014072528070140000f00300051150100c0e4080c3c031900d10101080e6600da0b051410065803040044c1c40c1da80d5020f021032543d4900c000d00c2c05100c0d91001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 691190800 1250 691189550 691189571
    0x1030e10050a020c07090209010f0215070f05040905041505010b070f02040c0203042408060f1320040b0d050c04051c020d1e1713120606080601030503071401 69
    0x101515032040103000000c0a859041e44903000e4461842c0f448403034810800d003c105141c032580140581c03007090706e0b0002d07101c0428070241d880e20001021100f000d1041c01c00a004180607241c4554052110701d41145801d4840301018120b480581c3c00f500c0784480704541c4440c0c810107103e00c6000d4040106040d0411200341ea560240011000d4000d000340c2d142c030720120f06207000b001a103018100100001c0903200c0c1500307401c400e40c540c85002c107001840c1c41d000f15000d81058000c150710650080c0c034405c44005140b038800060200b0742028510300c403e10042c4400e02c0601e00c007601c041d140001d16180c3e5025000303100400c0c1c1e48050b120f155822001c010030000d581e10340c4031600c40032841e078103144e85c294250700000b00401c80002020b4101d40041224a40881b86a45002d51103446000401c00041c80780030f00442500500c0300600300300101d02414410410001148c0b0440352044001240c529242d04069042c41402c2c0c0c000c4440d540302103a46000c1001c2c1d85a451024480c00d00200640402d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 691192050 1250 691190800 691190803
    0x90d0f1128091107050105191104180902150406170907060203040608070203041d011508060307051e0301020d14070c030206010303080c070605091f0501050f09131208070e01030e 78
    0x5120388001a43d40300c0c05086a401c440003503800154103c0d00801051900350102c1101900c0304001903805881d05251110600504003514240c541c02011403408154600010f001058095810780c1d0240c0d0104400d01c0848402c0000c102515480d501c6504255000c4030118103050f010308100c203590881001801200d50003c151811501645806660b5031a001d00076811841340da00300418842a60031640700490b243d1781031038121003400d003044a141110880484035448240c07441940340d00502c0e0100510310308102c442c40190303189001c41005a283c5000682203901050706000c00584510303040b00d040070166042580b141c5981040348903100165402521410305000040c288964580401c601ea110103081e584c4850b40310904004a04003001910759640c0a00216050780f0001c1110086031202e50082c58100c0700b001c3c0940100c80414420000307544001003d48011280000601d0f0208415990105004030b02d6111020142070880c0c008062a104601c014140341c00d00c0d0422502500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 691193300 1250 691192050 691192129
    0x2a0f06010305060f2715010608060901030b06150d0603020f1005040b13080d030b04050c0c030414030f07090501030c151d04150902040905010f0b030408090d0f11 71
    0x806180045607a914645c0704460340b60a0300381c800d002016110b03d01c00311403000070400c402560029500c80d0070380c1c5c1c50804645001c0203c0e00282c0081188004100040d80810705a411100042400103e4002074003540c00c05e401ca085d201e0754854617240100700754140b069140344d120b402a5002400d14500010280c0170f4821889032450081001456908901d80084900050103810080d9032580b102c0c050700902800080c40d2962040f407619010503a80d00711701040710030000c4007601841c1402c1c80c252201400c09150740703c0a41601074416940c207944000c2c0240ca0103401e40000c00a420f5043d8103028070451042d811001481071600600000b0603045a00380304400e20b006801c00c51005014007203800307450603c1a100c10f5440844d008035241c0300035000b401c00d441c480c0d5002c0007140e9032409034100d07071412449020001e84081002c0b40224840c00001c208025000e06040301c04543daa580030101002c00c031068400a160b58425000d924045481440280403035171010410295443c40c4540d080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 691194550 1250 691193300 691193311
    0x8030618160c021819050a050601301104080c1e10090b031005030f03090616030912080304030e010309031b0501091e051002040605180301022a0f0601030506 69
    0x35507492000c115654a400007090703070a44d0307882c00c1300390030040840417100711150701d418101420702c0002403801e10a8072030329115600583d40e003400e411110704400c140341548540d0100c1d06940d018080310400a40c090941d02084000c412503440d80b400712440d04141c3c0b400340c264451407910802c000400851140e40c00c210074121140010301c8966201503c40c0c1c1650790120030030000120401060100070b0810344111581501903982d21030f008044542c880c070554200650111007804003220400aa042602000384281803155265898245869403a1950030080301c4001d40003042000305948174001f0b0703040c2a42800e0600154442c2e50307000c1c00c1e1341000c4094515058076055081c09201c000d40043c106550080c0e80344030710300c40034002c001c50a00b034001c1c20b80d0755114003543c808503040341c0c0c421101155042e541d0710381007070158801405034800d2004200d45c559001e001400b000000700881c001070400b1a8000206032035064001414040c070354075004649c0e000040100045400441c17080da110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 691195800 1250 691194550 691194557
    0x2030f03030c0f0c0a020d2d050703080c030c0f0109060f0209030c01030e12030906090d050715020d09080310031e0209060f010c051510090612030e0a05030a0803061816 74
    0x1055403d0513035290221895010358082210a010000c1c0010340d5042c1c0ca140180050f1240b00c0ea4070340c07a80405d40d1a010000400702c0d4820b030070402c0401c0511003d802240191000d6901d030072501200da03460045201072440303483e550b4002060401c0010f109040d00070019040030740c2026035940c00262280080030469050685503030032601c00c0308040c800c44021189480c05036440342806c400f00d941d00c2c0d10803035a40b039461080407035007102d00d400307002a10700c00b961180301202a540c0100c0d104010f50400d141c60303e00b40c0c0e01e4520460010b01032401552045003c103060140341440e50421500b481c1c2041014292a10901c001c400540c54440155512441c05d0b1030742d0141c840d0510040b242c21001c0c0720302030701e240200c50301c50a01244020880c0d004503a0042609001030b11012003070102c1e0380e00d215020320740f5500300701c0f04006802106c8103844030303100901220700c680e650000301c0c0c1805510314040700e0400d400400c100c100c1c600b90b56035018403001d04184041074980a42d080c0803c0c0a07002e502001e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 691197050 1250 691195800 691195807
    0x609010807030f1401090b090c27150c060606040510030b0f0a08100f2a020709060b1b0307050312090f0102070f110f0a180e010c0c02030f03030c0f 65
    0x40c1c0e806500721000051650700d0410904000200c034264840303080c000d4a000d64104070350042d807403030030780c08907806046060000391a00141000300c0300f02c450b4122081203a06004803414015a4030350303404160740560000815510b061713860240d0705080c4001c01151152100740310501c443d4465040501d038980c2541800a90213100e280001d12080c1c0100c0c85583c840c10101000c01e40c58408a103120500c4504542400030030784003070002c03068400d801c0c6034000543c0540740218000007521000c841c0401c03e0b006650134207480d00101020350b0203a80000c5c00644000900040c01c0e02c48178519a04212040302550800ca40c43e0f44254403071144429840c2c3c99040302c0c002c2141c2340401e2002e495604d144000031561a81c4c1882d000d4080c000d2800b00342c405003000d20349100e903801c00c200c20318000c3c0d1006000c25a050b080036044c614088a500c00031f000c0b10b9540302c0111030300809204510600322070391910710392209140b04061800c42c2c0d01d00329212035081030040c41404030b04081913864107203141c10380c00d45 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 691198300 1250 691197050 691197061
    0xb0a0303090b250c0501080a02030405123702070911030a050709080a12090504020c0d03020a09170c0a0815060103090611070b15030706080c160b090d02060609040206090108 76
    0x602e208400f0003040074072400d1040300c04100120a1890442e202038030b030b0205942c0c03524500001c80c08210340160254202da0a140c2030703134440d94004d0000840d00e4503103000b4289540500510300300806566030303c1d17601440d102a00c03140c0400c402402802a200c0c14081070b980449400c00d140406072002011070b440b1030205001d1402030804001410314101129418040b0b41000110503944200031008691091004500e5041c2030084515410900004081980c4105801c4009500010305041042514103001c41e6103d0760015141c0c082503100001c004050182d002c1090355412544030091503403011045426001010b80c4a990084003400d0024100300305d803c040c806401210910045603000003101000c1105806025000c0d11019060907102a510018555981c400e401a0b20214010b00005101804400c004165111a596000481c038015944800c5115020f4440101c190400300c00b4005003a41040010380c010b44c03c0314502c91608158011588901c20103d402d810841c00b0b00c0042c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 691199550 1250 691198300 691198327
    0xb160b06010509090403020601060e0a0b0306191203120b0402031e091c2f0a0f05100c080a0b0d0b010504200f04170a031b150c0306090b0a0303090b 65
    0x542c51000540b504c001840c2c240b8001703448100901811010030031070312065045080564440c010703030720024410751960303ca40c010070901c04084040010a14200e2001160b8104e00800d20070701c9038425110380500108000d1390308140c0360720b5110240101c0c81482040038040e198905c200b246080f0605900103601c0d6034a02604000d6140e101d102c2016045c801c03c02810350089242c500254a80003c1102410940141c4035940311008650240d900143c404c8c1c0104001103441d607926803050080701c681c01c203140c3d001029142221003802c0400d0480003048001240c0c3d0055003000c18044446000d070180d075a480b0f00704031383e040c02828001d079510b1440c00d60829080c1c148041c145c0c4c0101c40103803506111800c0c1c07211548107015110382002507502d003d2020200044040320142d160f1100d403641c81484081061030000c0400a075070062451000020300c00051240000481c5940e4010550034100310080041c1c034040c2400d140906001c110400c04a0b500171850401d440e620f5045942d1041c101b075044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 691200800 1250 691199550 691199557
    0x3031d03030a0908160311010f0504090509010617010509030304031b02041b0f050c0316081909090b09090a02040c021f05070f050a090909150e0a0302070b160b060105 73
    0x503800d0701c000a42c24540a811040030ba0844580608403100c01d4a1032050000400d00e5110003000e800000b0304c4c80b656503010713010344140c040ca54a415800c25940784558400c0d242e085c0d4035a411070351344007020f00c4180325200d082071204030501d00a01c8103080010b01944c3d00d2000401c06402c2008080c05541f0000c040c0f020300521540042082c0107904907880070106c80d440a100c10008195030030000c0d54031038081c0007502c40100c003c001035401d01c2800103400e2207110410b18110343c5e014007004000380a039041d00050381d03115015035602e5005810303e04100d00b00d504140f0401d1040c6141e40405c81000c00c0020201139007903041d40c0c00b00e61a41e20441c01ea241c500300c86807210048040032006240d08a550b0b00c220300c95137996460140a000100040e5420700c85da81d0104005104c038501030051040a030040340040f445860401180407600d1100c00c121139054a034024141c01512074039082c16410000503000c1c042482145182c52040340000d20b5407404c00700018000d081c480c001604a0b80200243c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 691202050 1250 691200800 691200857
    0x1c0e010c021e10230306030102040e0c040503071a1804060503070801091a01030312050c0d0204090b01020f060c1606020c03031f080613031b080c0a021302090a0303 72
    0x40c101c2c00e8005910710381c140b4003007442c45000b60114442c214400380310700100300c2490400030b1410340c0c640f0344510303000c3c13154801083c1d1901903408001c0044d00b500e00c444007078450302d54800441d46071410101098188501ca80c044000c05400003840c3e0014010013049a070501c1030380905244c1d02285a000c40e0140085600150741400b41e5034001594200c19040001c001e4465003207031021448a170088110700341c0c217010280004006014070644401c00b0781c000ea4001050581c25420704201041480c240e038400c0e0044c041660320f80b2500b46440d42c0400c101c0714104150f1018082c10326144440f004507001c0c0c1040c0c441e104035010518000c1c402c1d2541110341e00a00141642d50300d10380b03800b44c6600f00280e80764900c01ca402c229400103143c040401c1d41750142980c01c441c050350341c3c0540c0301203c0f951402ba40c0084c00d00704190540e000034441d50b00400c0b0f10310b0408007420050300b440c01004078901c00e003801501c941c0d00420809039140d65807400501504d0b4541082008010307401c07800c50904004294 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 691203300 1250 691202050 691202059
    0x806010b0a050315060c030a09050d050a0f15050103030e03010f140c0703031b0305190204060806060306012708012007260d0204170309031b1201111207021c0e010c02 73
    0x1b18204103aa01000614424403907440d003520b2540e45000740f0540d4100c5940c0905a60014445100000c15146640c4074140c010384214850200110b80d5108a030300a0344120041011000c00c11071a0400780560090700c5113854080181c034401c003070010440e078001444600300601c000780c400b0805000e030f80b1041c1c1d0541d20944c01100700d0800c3da0040c0c01031a042d6000804a0746402140c048100a8000c80b803d030390702c0e59104443c0b038541c0303030520049030800760250781444280c9940e8000c83c241c951181041c051000d24580b095482c000000d8211201c01c1d6000034203009403074280c10106105c0c0700321070a081d031004610245d151381506180402c40c0e20323000a14010b00006501c800140160040c000340c131421110386840711400e018455582c45030030304c0590560060503803040e0306e840306290b40c190348130040c02d51407402130681c07104da01b1101f43d6620034a40e000003050b18220090031381c1c002c079405440d5000800b00b0f4114180250001d88180001e28100b2070f03c0c54007004940d12a10046508550180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 691204550 1250 691203300 691203307
    0x3040b2205010e01092d060b0a270506120c0d060204080d020703060b040b130f021b1c0807080109020f091f2a0f0609050303041b0806010b0a05031506 66
    0xc03d628080e107004842512074208080121444030f028966040199061054240250805540e488080c2c1b40007200c49600c02c0904c44001071403294900480400d0b0345112225032840780c85450f040071a0800341080d4020300002840d69148200040c1502102c5021101012204841c1c03400034041e00c5a41c0004e551405442c00240206800003100c6007920b2148500340040c030226020b100c2210091015943d00c25480c4021001100c850303403007042e110015070405072501080d00210718200303021400310390b504d074000d0615070361141c11440d0300c2c040c1e048545048200c6042421005003410410b00501003110b600040d1091200b02c1070085554452020309404281c81160035021100c90740c6003881404100c41e040c261402605802c40151a03448031410784c1c5404000382c40d0aa1150003440040b03880030f54401206002c5031041025522551040c64042105083c80042e0320311008140c0c071010f0568070240c01405403ca100d002e44e100c0303002510f07056480381da80000d000d095039100c80c1c1a540180002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 691205800 1250 691204550 691204571
    0x405090106080a1b080c06160606150e0306060d1205030919060522082d22060216050907120c03060528261b100503040b220501 56
    0x2e0380410816500407078104201d5a07900c0400340ca0b1b8844920312030784a1801c1201092041d1034602c80312425004907800a9040c1e1554002134016003880480700110300040701140c0c861800b00002c42c7d0100c404d6807000000e0707509554000c007100b060110b140a00c800400029865401001603002c47c0106148441c681c1445092850007084191400484070b90003c01009400c80701101146480c0c2d4030620035880e11943c0140800154544a4141c5010301c0003030010040410a4015000d081c18086e11220100c20400c400c0c01021199800001990841c01e074010301c441600e40b1410445000340d807100d003d40c0c1c6001d0211000802401c1d09520369240070381d281c0c0b00f140d05030b1081c2e00b5114142c0d60100111034010242481c0c00d0240a8119a00c4401f1000d00c00310840400e45860310340a40d140b440d01040390b80103142440f074800c0f030340c010300d49010354000703902e03c1c003c0c036003140c1c2c1500c80c100180b031403c0075103403e500300341c008041d01c1e00143c11040c2862120b0f8020074410320983c00074001c00018514 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 691207050 1250 691205800 691205813
    0x213020f1c05060f0909070b0c030a17010e0613090803070f0207050a23010905130510320f030114040213150e060d0204060308070314180405090106080a 67
    0x4041c410007000d1004004895020a442030902a40d001007955466115603070412207031290041c10380c040d90065103000a040d80081001d090325070804400b4648411103414000d05a2280440d030100d00e40c0321100400020310240b05154010f5419180456540a40001c170000342041001c0201100d030004108680d06a00c0f643ca80081c0c102503081d05c55050b030b01c00410402000d0f50080c6000c0c00320880c5124003124013906941c0051206041c4051455598400219001c20107190804166250002c000ca8040042d0100c009055080c082610403c0309890038900745424000f0183c0b8584802c41004640d560b04a1001c0350800040080c04689002070302c0090b40310040c0c0d0200c0c061405840780302026075160007014088903854851521031071900c44000c9482d00054005c0d80c100041e841c484001d80c03501d00a020155025034085507603118103290080c000c8101404d00c0078110002e0107540501030010205002c07081b02180c01050944507000d40a00510440d03200c0e00c00391040000c0070302004517 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 691208300 1250 691207050 691207057
    0x40e070c0b070305010b0f0c07030215040306050601180501050a09090608240603062a070309060f1d040209040204080105041101110f12070609050d02011505040902090103030c0213020f 81
    0xc5407214101d903031035070324040d000e4400078000c5144403030092261908507084d01025041120a03c0b0440d02d01a56a801143c0bc6019180c840c00031504000b4050051200030700415400c118203280810001540c0410815001100d0051504102c00000d201040e5441104c3c840d0207480c040f03000308161035850015030f5489417440c0c9005519940e00103c02e0b100f019820703440c0e11510000c0c01802195079404c00f5120489103080e1200c84156880d4615420040000b001d008007902c80d0712259552030800501819000c200e0072810204507444ca900340400c91b011000c109048001d076005038540850100040c042c1c0210b40164806620f48001c000510030300d040c00c0c8400c27030402e03243c0c824a403425012064031604048065080c0b940149a100059083e0314010000f8a018100000d892207041d6511414003844507107000050303445a040c0500301980019800040c04129010006901c143e4003040440b2014400641403005500300b40e41035403510303041040602600d07107045503a52081c40c003920480c0c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 691209550 1250 691208300 691208303
    0x108010c030c0306032102070b0a0f2d08091e150c0304050303010509041e030816050a080c03070e09160e060726040911190201060506031b040e070c 65
    0x203003040800040503001e13101c1c480649130049010f42565006003034842100c4040319400045118510001503035000610180001650981c0e0f803214040381420002c0c0395441e07421942070000341003003050a03100401342c006090303000301e420140365550365070089a08084c0da4204031110005070391841c1d0b00884005c1855400c00b20200e0f051030311502c915041582c2400100d400070b080d50f008000500040c078210480652042c81945006c42c500e50703800420881c00300c50030007100402c20382014440d01801c40440405581e0309460300034106990b14030014209a8003903c14401c0303100000c0800c0035030b481841c1c511110728010b4007404082c01c0070400e141441503450b4000000890201d10101c9031f207445d03c115201590010320000e40d020b400907841404540316400103081e24020040060081082d0081c908105188428281c031030f940c0e548240c013005000300200046924200c2e06009035981d40c2e0503690444102d00017a01020b0319810303131005a00ca96000010100c80140401c03500790f5001e80c8660007907 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 691210800 1250 691209550 691209557
    0x50301060219170a1809020c15090a0206070f030801090e0307061e0903050a111c050a110d0e010215040309060f0c05030f22030b06060f070b0901020a1803050c06210108010c 76
    0x229910382c1c00ca01240903030403200d100c8c0e802606010b40e080c80c40c04141d9030008600304c2a590442d0203030740002e0059014017030407103881a0202400c4c0501d60440340d0980104801c41d424000104075090703080d220322480d1001804180c4d2000c103800e11008145021848101090b8200085460350070301600d560052006000092650001c11243c00004a03060340c181040e4504040f05819403201034034180c010580810070403100000c0900e0280041042c2101c01403180c6038a8019100040020306140401401c0504d8003004024400080d9200d02070b0000c0b1512407070118660780080004484c905e071007880c00740c000e11002c80c20305140c0402c0f400605030901c0d00321032074216500040000310006144c2c800a04070b1380240c400281d0504000009043c0c140c800c810742840c0031440e9540c604441c0c4141d0b50304010b42e501091070000c40e50851421110039070b021071418480c6213143d403510b5a80102100090103210003180c03c80003e400494031019032440603c0e10461582c41c1c643e00c5000700900180038001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 691212050 1250 691210800 691210847
    0x1805011b090302060f0c0102071a0108011404050307030f050f040e15031b01030c0207030501060f0f0b0408100f0b120c1e060723060c09040507050301060219170a 71
    0x24107000c0da184508881d805004642000c125031040e0089400c01c0d0104029950200300007400900c544000810802201c2421000355041c201c00307508444020f003540d84003000481c28440414400426101c000f03030f0615049011646542d030803982d90240c1e03000099a40c0001c40c01107007011101c2d0f0040e1007406810324800340311000e80b041568810500145a401581e02ca501e0100c952003a0400d00c1200e22900442d51000d6496844a0844055611083e01e082d0070090038011440c41000800042c41014421070030141021243d98a807014147d00c03842e5907a64005401415415030040300d82008010b001c40030080c0c038441001e4948030400311052103401003600800800803245500e0315400d5001d000b240c1804495a030340c4441220181550245055003419000114000c04c0160b104e25140301e4400e456400510911043c0c8001400c910700b44201400113200c0554001036620400600701701841d451002400c0055101d030702030031b40f640380c184006030745421940c02008010310107010803050700d00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 691213300 1250 691212050 691212101
    0x31703070807050901200c121605010207080d030c12020408061501031a01050c0f0d020a05010605090f0c0d060509090321010305030a0815130c020d0314011206180501 73
    0x190f510411014601195040d1060400d1003c2c0e4905030f50803003d070700211003000c004070340041d030100310403d441d850562010450454400c0f03402e070038400070f000030b000920803135041c1101c0d40e4641d000a0501c80425949000c0c41c02c0b2103219081c0c40c40901c090240840d95143c6402c00b1544a2404441c0308518442000e10012154441e115020b00700e0700c816080c980b441c440e9401141c06600031f100da450203200c1ea0a0162030b9241c2480b2024220b11940c0080c0348180c0140b030003031309540c80e50340000e103c0e01441003045043e100092400d980444c482003500d645680380c2080000401207a040650404110804c200e80488004005c0c401c03a41384a0180c1004012224203984800090100400d02d030801c2c840d043e0889e0040480581001c3d5420f111000c0b20356003c0803130036035420041030366441c80d140c0105101d405e406100e6214440d016140502208a210a185c04020418851002a074242c4503c400500c031199014400d151000c0c12229040c560703604185003e440500e0581c18840c05695413441d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 691214550 1250 691213300 691213307
    0x30e01090e0112020315070f12050708060d06020d051005010336140609030703081e0612030c100609110a0e01030b0f0d1406090a03090b0310031703070807 68
    0x407140c5070345141c030480e803c080c5480030032a0003610890b018890b12030781305615030180c140c1603c02c240079540d4414507002840001c05003071400311401308080c80e02051100d034070350001c007582d03101c401926901d240d22010718180c0c1c028428001c0d1600083e25200030b011031003c2e0350348594101c8000366014450b81000500014400d078074498a1442c002c18a01c02d4008003501d00002101c0b14000d0344096044a4801403203070400004903405620781d080040c2010070103030071007500f5070408110009016826071040402c1d8083c030001d407016220382101da0700341000080800c2100c0c8a890361009950805075400b1400c0050211805006503a504005100001d400c10b20107440909010b41e83e50500b0490396001500289030752402d6a0700400d11074001c4c45070f030711381075800d000ca544198014001004804005400c0a402804180280c0c1014101c0c2010a5001171410f099807180c4203126941d440e000c0009500200b660b000901c03038405004074683e010a48000340d44a0580c5032508521030340d0740348045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 691215800 1250 691214550 691214567
    0x260a0509010b06040f05100507021009080111040e070809100c0504090e03090904080d0f0e10050105120c151902150c07020a030b07020c04020c010c0207050603090d08091216030e01 79
    0x1134101c004d005c2c8100842e20304260036503925410707410003500d0800b0b150045170f40c06140d800c8500100d0f603115410440101300744101e080b2600d483d002141030500f809180740c400300003c2d0865042014503000b240a1210500584200c0100b6560400c03400100b6240500140c100303104110020307140c108485a0800c010003121040c0c40005c010038080d55440d501c048460f000358414800c0503035503c0407284070281c0e80c4034034203260b0391490040101c4000e42a8050603034805810050189400701544507002c040021400c89040b01105c030403c5c902002ca0100456021b10b4034034580ca51140b8041d11351640d004145051201c101c010101c1d620f1356016202174151064000094200303030381500c00c1011503030f0801c01c960018043d10546040c154541c002505903080801001c0c1c01d41d5441d8041c0100c5501003040500400060342c0c10390662401d52403007910340c899401c404060103a000300044402d01d050025100340e8007041800c0c1d4407042e034050780214081000c44200c003ca201c82030417980c40c0d070040309007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 691217050 1250 691215800 691215809
    0x111306080a110402070b0f132405130201020d0c05010209100f0f03021206061c050a0506100912020603040c030803040b0114062701050403061406101e260a0509010b0604 74
    0x107080eaa44032400c0026487c8030007014200500403c2c1c4915001810f84401800c545d0b141400c1000c0d000c00d4041c605085032400f4002035012401e0581d4900141d0300031980508003289410058860b02160070028060300c101004944d100c0c00924400350101e03040449201a0815991103805840b040442a0128072643e01c00e52030f0480c40000049191030848010614070300300c02150803060000e6213650003038a9040c0c2d4000f042c90745034020003259003441c0941c88401d04180c80d003a0301882c50407501c48850701910300080c1c052480000000c092201d501413079402036900103040703070382c910b0030741001c24810001780140c82496070b9083c0328007610f01e4414240c518070702500d980070a0f0070278030b1640f0b9a50500088602030620a0612002001c2a1284201180c904062041c0415480c00a0802a0040385100345c001400a07551000d5641d2410b501c512088075100e00300315903003c5a20f442440581d034034001c4003c072104032000b0060101c80940026020300501d000a0100b03003641703020090940500d016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 691218300 1250 691217050 691217063
    0xa050105090a21200a0201110c0604030b0a0e0303011403070e0402010e100e06070c1503020a0909050a0b040e030a09060207060c0b18070b0703090e0112111306080a11040207 76
    0x8039038003111008508910050941c00e0a001a540410200c5140700f08040d441c1d81c1030304070a4060f42956000230307825500d0400031020309001c07003200c4002141ca008501011f0b09001c0d01c5c0000a47d2001254003c00040d50044226a107a6940d2007250f041403415074812030280c02281c4002035008a007045041c00f581e41615113104412211061081c100c1071000450100320840840c03d0264884c1307001002524003811184050346d09010401c1203100d00d101450b0201803042200c0c00e04aa80300c1c0905049c2d5502c2e040125442d1910b841d41005460898181a40f00e03140c1260000046000001410096043e840390080710740d50324816600e80455204900c0840e10000c1c01d040000c90074441d03d40d00014002ca451405036001c11040c3c60414650810700c08110300280307203800e1582051010300101000102c060856060010b00fa103480c007a000002d00c00000d14a208400741d4aa820643d4484c2610f43c04001090780e4489a0b0340d2001420410740d200030b01d80703140820508183c0201c070a226008034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 691219550 1250 691218300 691218323
    0x20328180b0a06080703020609130626010608030c030f1612080123030c011b0c0b0703021b031504052b030b030102030405061b07060c0305070906020c13050c040b07050a050105090a 79
    0x270300380400c0d4401140034880440e83c0d20008a152a04103245440c078424446072400404503082c1010308403111034001e81130b01d80c802c2c00350b907440660000843d40c1039404000402e459550803108031091018104d00141208600c40c110b1840d15405507007203041300c010b07420340004c200c080070010039151000748070150107800c0001e90f940c0ca5402090484244100d0001d0440702d4200c40c2c8507064503a02607040140d04103000078004003030640c1007003040c0003102d0340501502e4101c00a40041c0c4d82e4031282056007040710600000400b070101c14452900d1110703620700c042005001814031920050300000b03034500441c0c500400d0f02480e09051003035910555014000b00b61b03d07184ca404038480035603003055800006800704288400038030710b030080030102031040e1004269424500c002600094907030708030328210740c8500c01540056031003002081c3c00d500340b4440010075840340030711540e80b841160445094081c002a0113010044001000c101441c007483c020051a140c4002d11900c038000d40780084c20710725254 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 691220800 1250 691219550 691219567
    0xa14090601030e0316230609060a050403120c030603031d0d060203131203050702061303050a0e01021903020601140406180b0f0909011a04020328180b0a060807030206 73
    0x250f000d01110711004080ba42003c030320041c030840c007052188003155140b03070500240d01210741c881007000d040981c0c440644220710300342640940c0c6080c014903001030180ca85020400b4140100c2e007603039100c0d45030a003d204d0388500e220060042e0a031072008030f00003859060310015008031503040f880e1203503004148610545203625000702039040500b20403d50070070120502d0000380c0d8040700d080c072094191000304007071801d5903001c1c0c02c11000500e040b92034205c004e240305c0000d510804072581e0f403481d41010081481c400004030314000003d14041d0714102003040100a0540000382c8034101d80d421014854079081410501c0155001c611880091002e600d00381210343c2c903140c00100b40d41304081d11140680910703800151400c40c00303031101601c03a50741e85610041c8055103080861904c0058805601c3e60800d540754000c0b2035440340010140ba0350a80ba428584051070b08021035200e0700c00c1d550544603002d424100b804200580f090900346d45480740c0040d0712100441c5260484e50010b21342030078610754 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 691222050 1250 691220800 691220807
    0x618120602160c080f03041a0705010b0a2603130b070305090a1202030f0c0a1203050d060627080307080706020c0d020c040c09030b04110111030c0c0a14090601 70
    0x1104858407078091182021407440b000321000c9242c003600c880902c03149400101400c0900d03a40c19036260350400c00c024002040076140718171280c880c502025940e0b0700f8a050060040884202040d4000c502d0035001500000c841003507030307440b0701310b40b8021540c11003804101c4e40c130300c910815821180c2380c10070100045400c10010788070b01030007400c20500d042c003114002240050b5580104a010740004044420350408000611591400e8401081401042400142082d604e48500405040a503040ca400c061080d01034803190b015441d800c3c404540c480802600121250801240e0064290801c010301c2000321640b40440f403400c4090b5242c00360984440489501000054400c15000c01000d041c20740c081110a0340969603070f01034141642c20804010503101c00d103038014100900c05001b400480c0318034000f150000da0020380030000107603020060302d45600c03000c0501500c0c040810b0148074144041003100b2020001c85003051465110340188810a1178070540300c0c2c1100c40700e800035426502 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 691223300 1250 691222050 691222079
    0x20108040c08060c1903051b030a0f05090a121b06020a030209060721030204030203070509070c121110090b0a0507050d060f050a08010c020d0507020f1011070618 71
    0x401140c0c0c641038880810794030f400001d44180855404c0043c0c0003100003a040c114841d4107016140c1400726050180705d9520380b800d0001054000b42e000408161a648540c2c841c1c042c840b642d41c018481c4d4a0304200c1786803503421408041d07818800d519600508a841001c800303401560715002040721008607102d1034020b40200b8151011f0682c200460074403035441030068224a441080f403507001c58188080c4034503d00300c401d030b0b50302858010b01081c00103940108405041e52400d5650f41c0e0599248501110b41190000c4040d0060001c00306c281c0c030044e4841100c68040b540c40c0c04580c001c0610407400b0084a6984030007400603112600400e40f00302c1c8a4001540142c050b25005040c5182540e990080b00c58542c003040b040c4108010030001030801d102c2550044c00640d008000642903040044d45400002a8880421000140b000708641d121410b069000c200074142d0b408402003c00003420070b481400344030640d403140450020f1000c3c405c07001070040b1902c55180649003807038002c01500a41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 691224550 1250 691223300 691223303
    0x105071208090c0a0b2101050609090c091807080c07030504150221090405090a03210f0207031d03010c09060e01020f340501090302011b0c0305010203091506090402010804 75
    0x80007800c02007903450181c00f2010300421045607540303806004003181c3d00c21b140749222500c0f00d035000c010006640e5403000c0da15189425640001a903651401c5581e10340300b00c0103450350150152044078986644a10480e114402e1626188415101c02d07441c14030a00608400400041d001c01003406030640c00b03001d140304400305004484074240000080c003411010440d14092685010031600d140c1d240c42d0041c0758215190402511102c0303480e4400030440c11840207050000450007002884400c10755010b00c01c1034890100840d241e403998038004096a2802071013210780040001400040d1034107200e0701c0f010011035201d084006140240c1039600036100300d0201c1c103500440c00e07091481d5009121101000b4070040520310f000e4807010320201d200c0c0d51500d400c80e58004211041c40aa6002040441540d409080006000503004404050f9050210006004402c045000000c014054001d50b00685610080d01d248000280d003400c010681102c1c0158040c101001280140d400303842c1e0b15030410b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 691225800 1250 691224550 691224553
    0xc03020a120f11030a230c0a0320120a080d050c030f010302100c080d0c0927021602030f2a03070306050c1608031e09251d0402030c010507120809 64
    0xa805a10365089540300003c0d0f4800c000300d0400e040d0a265030038008003459400841d010321403a07089da21803001006c2519540b8044844480300105559161040d80032400011800c49004c6a10391601d0102034000e07a20180910342042c0100348809152015203108500700d01c8060944d80c80c2d502004500d070b41758050744090110041e181c2010803200030061a00c2d1503052404540d1040e9120000d18001d5950712201c620b0350507030882000300c14a404ea07035194414104015031a05a40554188800700756000254540700e44844000b80440c0440e0550f040055030113400900641210304400e000f00d00200d15905030000300701400001c0f8241c1c0155003061008512a003018441100d203c080000c10704d050701d400d8004401c00c43c5d04004580e4203a009051124190620708045004903543c4001c5085184019036414940d0b00c0d4500320f8202d00001c24a20300600c02c0d4001d2002c00b0303140c00d0400c1e601680a4000c0b485803044c1c1d5400340044030b610581c860300a102d43c4518030401c8a000c02c01412003140ba = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 691227050 1250 691225800 691225813
    0xc0906211b03050f2104090507140711090903090d0b040c0b0f1b010c0c0b0711010507050a02011d1f0f0c11010507030c0e0103020a0302040b0301030c03020a120f1103 73
    0xc0d00e85201d95403000d940300d00002c3c028420b044030414646038044840c0c41d24584010401014000c406050381c0480d0f03644480031038161a580819100440c0c520b004111140d404281c200038071a944842400001041c0c40b00806500d03080c00c3d4503101d12400b90b41da0341080d04400e10030001006803041e0355019000d080c620905549450341201581d000c1c080d1410071200104050059141c600707490b40d04204034100800a403070f1b40c2c00b40540100e04580000c4d1080d003400300010111030045c00160b04030b01e5514020007080c548850045c000742c122041e080019031034480e8401031004551a0b8406000307103c0000d118031030717a01d91502d00c9111200304080d0f1880d1143c82281020031170703010b6019000c00300d0b2240c006103040075101c1800c60f08010400003c01d03040030034103d0195044520850a86001e10780541d030344440240940103440780d0380c0b00c00300403000000008103001280b50b10f50160b9100319200550143d940250319640d103074807240a0804001d80d881d05c00020707000d800000d80703d00050181c416 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 691228300 1250 691227050 691227083
    0xa050d0f090804050a0611060103140a0506040b190203041106031b0406090501110109030f111629190302070c03021c0c08010c05090609011e020a0c090621 68
    0x5441407080d0854594801290500c5949407082c440805410180b41500301c0070080000c581d665803040c84047d1005075004403041e0030030400d2001d44580f940102c200c40c02c2d4141450a00f0741418200c91044901d2607159414040402074000c4078066074010441407076141124040000310f03030001d0503203013014035480802541e400040000c0e100800d260b132904070f0882c0c43c0100250401c12006c0705241d190740340188100000380c110303480307032019025881e1034208080c00c102c0c034520304042181041000300310024002071150006000c3d01071104500301d1100720002c1d002412415005180c0c584007480052495680c0c6144242c1c0075241c414014041000041e69940104880107241c0070007500007401d2000500034045500030803401006164002c11213140071a100500d02c0c01880f00161242500280f00209a840788011510744c0102d00c2c208020540040c07000380d42da41c0d4082d01180d22007035900c000500c0c0c0030148214000c82d035400c0e0300035a00a01201021843c080d402c0021200d00301941110705 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 691229550 1250 691228300 691228331
    0x21070306050726070e010e03100504051005040c03030e03070b0a02030903330c0c030408100506030705100809070e07030603050c041815020f031003031803080a050d 72
    0x1103008140004650500c2c05009050f6034014551200060408003101c800041c0a41c449034010000e10b0b11613200342e00580121101d56403c0603495043c41202d0f220501904141e2290f80102c0c072800813141041035510700c0c88d0a440c8116805803440054030b10420100b4000e08070200304180040a4072906c03a140c0ca100c107000c0c0c00080c2020010b900120f100c02803401d08008000751800d000c9118100a000e0074400b40d119000328284050454451010441403e03500c4c3c2901c0440c20400c0c156a141e54032011590307500c4040e2071094401600385001300c0d01d40d007030200303420042e101c0103800a91844102e40d0140c1d03100d000030f40607910781c1c41038020000e07848a480c04058059800c5640110b02c0c2031850418a1404c0c0750b84003924411031070880200c1c0c0d80c51400940c111210fa025900b04808a4440105002402500786003240c0010000400952503039081c4801d00782c03482501d4032459020301d0707811074481640c1d600000b001c0000400c200761406025071301800f40211400c05c085142501003001d207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 691230800 1250 691229550 691229563
    0x1902060f0c100f14090105040b0a020c0304050901060305240a0e070c02030703030206012c06220609090c06050a021b040608070305060109111914040504141504020f030621 75
    0x201102607803079501018200c4d62030346003904621048000e002c50f042580314902010000703842e82e070101d58000359003292500d0910075034000b4800281104038560356243d024016103021a01c1002c806180040203503c06e10b1411050381d09140982001d00d102c0c2081104103980b1400b070704800c28010000a0200142d800b00541c02c0503622179409044554904644140700340d00c000000092a812114452665440740d400185c0c01341e821164a03440c100d02c200300e83c1e02d800312241240d4545003003090204560455400c05240f151255440d510490f58440d01102d440c060390f140103005800540040501c0016005003548489008000241c0e040d55408510324045140c4e10444a94001034010030100c21184900440022000300b054540318080700d0843d0200d002e940c2c000d043c459040003007440c40d004030090301c01800c400340040140c944c0c02c4000300d108000481e0006015885c0103411501070806000351000181c0c1c030f81d00d031400c42d200d0804005507450182c1270400c0791403517294144c03c51081000031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 691232050 1250 691230800 691230821
    0x11e05160206070f110d17030c13060c02031504030206070c02190603150e0f0115030615030e1c0c0602210f0403030c0e01080403030f200c1902060f0c10 67
    0x10003013000140b90070360602c0c8010b44001c0c410104240c00c4008220301c44003645c2c8140e18000321301d607207554040d03660346180996034102d0762003081c0703200210b400c1f83c002c019010320a008030b048502d01506000a40046202101d008005030003c1d1302140b000c5014004601c0b0841c0b00503c52081e0550125031003507088941e5200b80006512440e11001e10508241130b8405040c5600c0d983d000c91a002c030241010003018441c8000041f0310220986259200340d018602810560741d203500b8820301b810004028122401d200d4046000d100401d00281c1c90321844c10320040155100d03100320150380d440314002500428913070b41200040c00c1440005030f003a907085621982e103d88030340205042900700142100c0c3c0e17020098040c0040035101210a80c0c0180501c1d43c40b80d03140c500030410030411603025010303044d10810f02074050a001d060402d0364203c0c001900c14551b440e000c403004220300b400f045a01401811010b50005410410f640d02e5026180043c443e10124070b0031a10104846960107040303542c14070f003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 691233300 1250 691232050 691232063
    0x703121a0108090c06030f15150a11060601020d0f1202040f2102090a0903030912030203070f0203090a050d03170c0702130c170907120c05040605011e0516020607 71
    0x9030244940c1c01c100d03600d4020024030000e00300701c41c000001c82d44030701c4080e2903084c444a0705000916040711148501011440c060030020449011603a8034445030031800c0b0307180c0403480c1c004500242150001d6120302ca40c10590007011a1040f20409a40035041015510304010120b10707085204512400108000c0101200941c560341c0744c41c101d0341d072a55207904042118030840720386001680d1003101c12034121084000000c0d00030945d00e400e13001070800e001c00801508080700482040c03070301540910f100390b9682e1261650343e21030802c00c98591041142240d40181444024070550400001e5000740504c60f0802c0d400c081d41540c0c00019201c8120303482c1c8a00040000e503d41103040400400c0c0c2000400042400740e0250410058800d600e184c02c5001c2601d001030000d10264001c200d904002c03c9100c0395246071240c5414208403011190183c02e0207282440400a4103500c21282900c0364217224a0b10f161400944034104d40300d621440710301a90107410040040960764440080071518803414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 691234550 1250 691233300 691233341
    0x717070201140f03041e060c0f0e030f030d1505131a0405061c0c090e070f0e010b0a1b15020706060f1a250308071103030c0906070312 59
    0x800100750076541c02600c812094140f0500b42c50000c4403084d00e07049603001c40b501c1c41031144000c034010f8189500b00094070180c00c00e03484000c040e40000048d0000300980e651007070b03d98030b15414540e07204074558035100603510030070000000c6e01041e842040c0703002000501c001400d58500000e2803420000c182c0d0310203640d59800185507801d107004407a280a505480034007982c60000e0000d0781c844101e44080c1c5810402c42900c03000c01c040030151402a164030312003080940e50080301c0954503140b50042840c00b080e80400801c510029100c40c3c6d040b5101c114810b490711140c1142103900202a86d160036120f80c020b024040050f00b81c1005121304061000c0040c0c4480d442c2c24540180c0354036610010800004401c01c0c080324807981c280000c003a010480203a60b4508000a55010b0f0b10b424252450103641100008105944034408070302503000303551070049003000d1850035070302c0384000e49128448420802c19020581020405481014080e0619101c415815519141519042000d00103003801d00d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 691235800 1250 691234550 691234553
    0x7062a05060a1a010813020a03050102041e0b09060a12060b03010303030203041a100501030e0c1f02060c090906040b030f120c01150e0a0519060332061b071707 70
    0xf44100350b00c1d00709448580c410f51402c2e20001e07207680c40192041e40303000c0e14048060150344410810000640d40725008568440c1c0d24100080c0903010109400103108849100141503604807007501ca080c0c074004c1105140503040b207002d13907400da158008442003544445000503c1c00d171010140d80254020740300540c0c1d92901c0d1034900020b14229070318819130340c150400d10900d45c1c00d41000000783c46003070071300040006010300c5c0c82e464280008502c55201d414404a010021415049660702d1120303070b02164240d45032075101e01418007602c40501d4101c614180082c0c15803809400006400b040a82620072010701030810909109070340000109003040055410311801c0248160940c2103401e80e450214035003401c1c280005400c003d046200f540341c84c2c00218403901304044030351040e101c404908002540d41c92400c0084c1e00b884114226001c8158078114880ca2807011014403008000343c042e007000e5031603d043c11106460304d40f00c4648890b0032322800000941200c109103040c43c402841d1921080b0300e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 691237050 1250 691235800 691235821
    0x6110a030e0628021605070303180308071509050303100f120b1501090503030a020f060a0513150209191a120c07060f230903040807062a0506 62
    0x35210041141c0c0401e080000c4240c803048450030321050703003c4060606200040107006401008945280e03204101050400c2010004400044910940714180101d01919502c82d01c02c1852001801c0d101042010800280d64132031103142c0400c0300c01001407504d059403501890364004540801e01504004024040500c0e0241040c00412828074181e030303440c00c156100030a020018150920b4540183c40e500b02583c02168030501800c0050b04881d00c1c0d0000e088004c3d82c1d0b821009000f0070900460002c1005992107000e0944201e0340510003502480311966540301c1d2845490000f2911a401e01800405584410640d1119200c468468034070a0608a80707600a808815440e000b194041003d80c1c9425104a600e42d070004010354155194907003410440b010b04400c0000108603171401850035a003000096856000b10000128604250380d87c0007101d640e44294000c00c100c1d41e01c4004100035803445056507046180110000c0000c4100380407400003e9181c45400b103400d900481c04202a8205 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 691238300 1250 691237050 691237061
    0x70309050f010b060901182706050105090a0e061302210109090b1b0706060b0c0c010329010507060c0e01021912050d140708090c0103050f0a051306110a03 68
    0x1c008214000144000810621400c4007060610480d0100c0e400da896011010780c0090218034010201700c1e4101408030750403c900b18942c031106d89499404940c0703501c00d4003510700401d000341050603158140b031000712920400800203540401c64503c0d0280d444514009421003403500200b2490104034000c1034a200e29050b001641011b241807540008202e000c10425000407117000c01012041caa8440034041d8454898080c103076500300f24000859a8590b001049a5401a020390742030304144030044080d2803010104401c440e54103641440c030780f52202402150a241410800d00d001819a1460280c0e5010b059140102e030f00040010a2540c060104000c0040711101d0900d0603003941d5142000c203102d01d443c0904000b00400c1c0456241c1445e84003c0002c03140c640050000d1030800f00003400c00070115140d414900481000304c0700c4e9402070081c11700401290501c0d83d03c2da907c07504c1e44c100401004202d01104000c2498140100e141840303403401301f00c2150810f942c0ca03802460003406450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 691239550 1250 691238300 691238323
    0x309030d060803130518040f140a050a06111201060302090109050d120801050109030c031211060411030c0a081f091a011a03070c020d02030106080d0c02150f0714031207030905 77
    0xb9894903800c2010081b20b62040d40c031582c404200c40e600006810012000345070071007544203d2203003c0c107070300c1804000154400fa05105510520038a1412420100e4900900714a00441e0183c080188045406070300608a0240d06240541c0855034950004400c00203a040a41c1c8100c41040e04001e116404028a40902400e00340880d42518507178524070314881c0713440054405c900c104001008940b04210203480d03000a8070480d000c0f41030500301030301440001c86404c0e1180c8604600780d115803c0120b151011100703004081d007440824005a43c0152800d02094030305259280701c0040000c05100410603180c03600c51401d003c41d810b1031160084020340c15003c0f940ca0790148204005a270380240e401040d294140e600705245402c40c80428007426554105c40400d000d0300c80d40d20f400039800300f170f045081c5008880304000203810f20744c200e880b881034104800d00358204000c4003010840b016400e19141ca22101100c0c9403c0340e0340d10900c0302c038009076000d4001030b4440e402e00060007000c125070303210074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 691240800 1250 691239550 691239559
    0x1d03150a0e0106030206070b07140708090414060a061d060f180a1203030f0609050a0c1707020a0f0804080303070809010b0909032b050702010b130e060c0309030d0608031305 76
    0x1613056400017100e6008005000b80200d40176400160003500c11040720b407000400c2c04c1c155848d51024030782030f40d054120341907c5005d540340c0505c2c03058920304802d1150142070b000c1c04242446040c031070101d52507074600742c5502d10591011088281a00e85100406051603010b5041ea101c0303180c003110402c28031f00170004074030070895203505020010060189070510386e0b1500b00091503075111580c403009020103a2220380f0046c54501002403568050304060421030030742c2d6030b05281410100b1032150724401502c010005901a440e88000190b001c0708401107140117141c6541000c0e41d80e03000c3d91555101b150ba640c001840d150034050821001d00403c1e00007003080b030301565185008031130182d4a002d2015490444d060050758800000241080003480c1140840d0601030361801c0360740640a400c03000c01d010300034003260f0300480c445001e82c132508030307103440ca070340508008c0e19640291901608050212041400100308121406a080c42124001c10110300616124400740c0c031015060701e80c660129005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 691242050 1250 691240800 691240811
    0x20c120a08090d0f05090d120203040602100e0303010909230a03080106111f140a0504110306010e0109150806100f060e0d0609050a05061e0a06060804031d03150a0e01 73
    0x2c0341c0c04c0300100c44d400007a45000c0341c8a2100c8400075103d04030070f00e005003160801d00201c4810603400b000400580b0b100390200c903100221a1820001c40e51609082d202c242c20501c014000c141d100e4101801e1280900000e010654a202c0810441c4010200d82c55003a0b1208508404054100b240140104601c2c00c0000540145414842d00e400320403c01e04003030b0100700e20b4005118010390040612007400484442ca91503c00c042000900040c6c4042e1140d080e01e51000c081c40c900000c4190503a40d00e101c4000150746070011940107041001441d103003001d030005020030328071400c0003264864a602e008040e5507030b160040c42d851005003901321804001d804450344515403501c4007009003003070340200002152009410084d082c004904002001400f0704000d209164407072100300501c09840103403900141e2200c8501600721151441003c010440000009000c01c2c01850071603110307000c010180d900102d403440064100000291282e20000c0d120051086002c01c1c2e100b000a5104402e008114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 691243300 1250 691242050 691242073
    0x30717060714030c07112101061a13090c091203020606041407020a0f170f030114041a04050406060e01121b0e010b0309030f0706090227061201020c120a0809 69
    0x31901c61000f014046040e0f903180d462030b40d19040310004c8001380e003101440601f000c2d400755a018004500c00c04d2901e140309210001084104001c0710b000200c420300b858070300341c90980c81c040079105086001040c0000d41d00c0c0024201400c207040203141d440703503015265501c0c2c0041008102c50f41c0e4014800000c91250400072407d400040301c0401e1a00b00000e001182c11320b11b000b11610100b641d061020b0003011801c0100c0210f03e001540c1602c050290003800700081c40107010440e5000c0c03025280d400080b1808000c1c1d401e0550117541c21034010318000c101951138049a1840b49400e0388250f004611307011444081c4000700c001030fa045044100801d07580c0d07150917503240300316806010f00f004813135000021680403c07041088406441110703252549404180c00e04a00410300c0c0c41d016805101e8010a98202c804d04140c0c0400080e02448220416200c907000d00c41c02c41e003844010303d03d6641c204410041d8202c100306820302c9070b20381044641e64061540c001898240042e0404001e507014003a4078a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 691244550 1250 691243300 691243321
    0x1030b100f0314010f05010311280e040b0901050c030604050606190f11030f0a1803140c0405010e16050c0a1b091404030c02040b0114030712110406020703060b03071706071403 77
    0x44d00c82100d00040c10180702c500c14480305250010b0ac1506198140c0c001405101c9031200346c03186005203031440c07281c0d803160542800d8440c11581d20440740000c000243c44d900d8154042e0307401a00150a850030164103820611009200f64000380c0480c2d0017080c0245001d0b409004981070803e1240693b0500000d158010011300405c0412001e11040c040c2c03106c00400e82d01e0000c40116081011040c0d006042e0103515100c4c8144040540501d0514002140745e008642e2460b008400940c000c2030701001c4400225006d8210b00c3c03c8100a000305a900004034051281c190b02040500c0d1320440c4c16403806420300200c42002070043c4001d40c0c034400b004082034107c41e482102c01d030142d8000c102c080040340102d83c086c40c002c0041e0410103012041c00800350740042c01c00d041c42035421040005038161080440039014610034500140e20810040c40000c515401010722050050111140a6101d001e100e190340d850403895103180d4407036801c000b03e41c2d80c8038a00681c145582c08040349141041d600c250b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 691245800 1250 691244550 691244573
    0x3090a0b070c0212150a1a040f0207020607060b040b0607050c0118080708013303080702040207020a0e06090703060b09220612050d0305040308220501050c13050603090601030b100f0314010f050103 86
    0x848c406d6550b500c1080c107000c019011600d100385e0003004c031542d45140e07103030030401088600d40480c0180d2500c6100d081e141000e40860b8151a080401007403031281c070000441354180310031001c0c1e1305107040d1240010046010407140001c0c10540b00045018020300300c0c484010b001c0d0710204800040381c070309840b800c1142c2c04684002c0e42d401041c0e542d40c030103440c00803074040d104907a8025040403d40800044c0d114202c00030502400040307030f0400907074032044403c40c00c1d80c2c40ba00805250003404c12050325540f5086c4003503608454a080b600c2c04603600c0702840011100190711500c1044007040c180d40c10042c00f4800d1208140300f6050402c442d00385030314000c24101e00244503c4809a00d5201100c0f09034844041d0700013168040e000340583d24100c24482315a0b00b00e0f250b1206542d0f841040458189405401d403403040c19108007d00f440e80c690b4840108401c07001d007240c110310b5821303100801c50700d8990540a000d0741c01000c6850481c0318980d090b5003110015184000720a1405005100050614440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 691247050 1250 691245800 691245851
    0x702010e19380f04021c110d020112151e06020d0c060209031b100203030903070b0601090305100c090506031b090103020d02070c080c0603090a0b070c0212150a 70
    0x81d203044126001e401c2c816200044401c0241e00654010010001c51114045204910a45540f00a805055010a194400740f03000902406a5002d01c8503141030510800304014014074004001180a0b4546000c650f508045213944200f6594144042c16070070546c641d802030b9280c00c2c0500e580c94200000d4079080c0d041403c40030000c41c04003a405011898041c0d821609000b8240e41c01c06100c1542d034040783c440d0102c000c0c098030038280e04922032130020007074030700c00c0d070380c4801540c0361003125aa00d0344080e00040c0301d141440419140400895010410503c140c49440400140c501183c00d000c0c0000c103c0d603000b5840380400300200212604280010802c40340c11b141e86545500320600160042e000f00c01e400e1410b14804100907003400844064402201c600d04280ea46065200003408502c0c40304035001c001030b074403580c9040000303022002e1032035114005240060100e41c1c20b038002160034540100703c500fa6400140c2c258469184018269080001031000b0800300c0c0107803c01c17004480c9a80b50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 691248300 1250 691247050 691247093
    0x9070c0b150a0b130618080303060f0d05070e040b130510050a0b1914030a0816030c06020a0c060605010915110109080408071508010e0109020901021002030702010e19 73
    0x1140340481e12010b01c8000a0610a0001a15012440c01104000340e05106803c00035118007980c0d403100000320300a5042d502410090741c91503955506000e003001e070040350150408000c0712100702040741448100060142c080004003981050300780312030174070f034080c054100600b10103440200103000041c03003601304481c2540202c1e1640c0d500e60104020110011106c0e00034850440c0000030152008000d01500c00d1039171801c00c070b42035050030306989058818000300400d1040000501d222180040f0860b080e200345000da1112141e660f6120a80c0c016640300c5000c0394812000400300304050103258042c06c42803a02098075844c21203181c0e0a80b80450100007031000302c88030700c0e00c11002904130644460b003254615a0b180e54840e038941c0d98607203502c0340300b0840f4081d100d0034016a120300301170741c101c400003004124141d0904106000035031000107214103500c2480d071592508005400558407480c01900000368603607051002c2c40c00e1003600564020300b03076050b07020036002600c1903e200540003032814 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 691249550 1250 691248300 691248331
    0x191d011e020f1b0102060a020306060f180607140c030604032703050a24060b070308091e0105070906020a0b0103061808130510020a02151608030a090209070c0b 70
    0x403040e41080c5450b030380242940100e07100b2410503d82c41c002c141d641d030020b03421104c8036500c02200310b04030f01095480c41d60109041050300d210181340406044c2d00c1d8440d1004072454200500000d0050b40152022503042d8400d80656018001c1885000114503003a80a84610325096174000c00d640343c03190340210304e440c4010881003040b00c2000d000014641c0a801c4541e15211818950f00704001c55031500b03419140b00d52605016950303400380720b04139495081e07c40d09048041c2d40540344442c0003040c0294030702c216001c10740c03804d072005000400d01044800016950034110b40052080100d45c105106540c051040d503030005264040b01c41c11250028000500e03c015051141c184e8900c0c4140038054038404141e82200c01c0104540008031002102c0c11071b4006c0307000d50140c0c0c441c00150000f030341c0040d040c940742c201d004100740149500c0a83e5038440c4041060f5a0b1455000d0704251040c042c4d056035804c044085040100c0310b15044040ca041000c80359045503103400c054900204403911484010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 691250800 1250 691249550 691249607
    0x702060c130801060815090d0f0c11040906090203070801110d09021c1b171b0f0a060801030b0a0209030319030b18072318060906191d01 60
    0x1c10510010b0100c410007400074960381e86507031742d80c1c030240e110165040c2d541c0804950a64000502048624481d49800d00c40141c0fa20080e03a66544104040c0c5840c2e05034400c0c0141d6556601c81d003004107200d250002060407190050502d0000981c00c0041580e03d8001c4c8100b030400b8170000c1c3c83c8481c501a001083d814400d00c0410000b01c0c180c01c0722040e080046800c1010801801e0080c864082400b084041b805d54801c2e40b80c03030405942407814226086003ca48078600c01c1107100d0400450098080b900a040100110710007054540c419000078001c3e0b130040c810000c240004036007010481c207003581012112000251a0f02c203d000d08180d07200340c1130040c48001e01030f40006034a540010305003030212200b442d02500d100b201b200d1380c0c0c0000b100d11109810145c03561062060443c1552245030514101d13084110004501001a50340501c0c20701042d8100e0703039580c000b0160750707000810074580c40350f05a0f006407500905000c00c0842c2003c0000d0302c56980d1f409a40018540301280c4800c44c1007290 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 691252050 1250 691250800 691250827
    0x24050126030f0307270b07031d0307090c1803030e060a03061d07020f0a03080112020f10031b030c02030d05042619080912070221100c02060702060c 65
    0x14040707042d4801d82d001c020001e0054100d01c030100d0741c1140c44c1c07103000340100c00c1c41c2a4150000314064454a81801d01c80180820f1080d0030409001c525565078036510300079000042c0c03802d501940200c4c0140c1d01d802200150541c0400d0640c200c0755080c1190230b01909660b0068040506401041d01030800410205820340c4030340c100c100102928030210a1003210f00f500c107105cac20030868000015210300007081e10014400503699030b02c186c050303445154603400c1170000d8404911b0a0000d80c0c0c01203039901d0000d03050f503c0010b80c850310080e60300e00040e1481c125400740d20324900c510f0100141803410b40b0440c038094000c0100c594000c21407000181c10f0340c5601d84001c81081c9109065014a440207820300225004802040c11003000113079041441c1035000102c071803200480f900c10f219040012048400d6081401a2203202c1c8002c1407074901018440300b8114420302c81405c4980c1d54000c500c1c0d44660038491150850034140c40c405480725180c26a00a0742e6010058054408004d000815100c2801d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 691253300 1250 691252050 691252057
    0xc030120250c060905010507020108060405090a150b0a1e0e1305030c060402040b060f0d05040317070206010509070503240f1806120d081902162405012603 68
    0x7032940c1c1100d60140300341032074044050a03000702e80106514407004140303580140152010654140d54000c0b41d60f40d031405110181c240034042d01640d104120300c480c00076100e4034004111001d00540041d909030000200014900c080d406201a96a68840c3c4009030909000441c203885a05001c0c06064440795804003182030003a0001d070040c000450344e80c1d815180851414056070080703405114000a007000c10040b480341081c40f101050b41008602c280f0450364000580c454041e0900300c1200c10000040990268200da1640042c5c000800510440c0b40c074203041908484c02e0324180c3e00f103203401100c21051440e80080000504244480c030361003540e52142503040000c01030000c0d609503100050355030044070141c500d14031a000e040c1e0501c03070780200010b052040000581c0d412105448540526040e90145440c007105c5075002c122400c43c003804420640c1c5035a225203c255072515108420301d01074040083e03819903560411380100181003402c0386c40ca540031108144103960004507042d01e071441c0f1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 691254550 1250 691253300 691253347
    0x18070c0c030812010806010602070611101104090e03070305090d02031f0b040608010b0d02010516060c1e08091e03070b011202120a1509080c070b0307020c030120 71
    0x1030059401008024101c0080c242d603800740b041031003444e41c0790207603283c641d50301740102c20040e40808070070805980302e9620007055002c0382c1e0640f285281c120b00b0722810707120b5010880c3c0d40c070303c0005010402214140304c0c40c4206440d50b006582030450642c0c005096200f54103140d031190007070301202000e642d418816007980189c52080880048964001c1e2000b81c45050f00d803d20451800c03c1c0098091018019070502c2400103050507940c02c01369005444a0b00138a150080100c0c14242d103a00240300d61003111107080c8151110140da08160810314115060b00d2000c00400c00c00c081032201000300040c40381a0b9005c2e06a8807546902c0d14008a8654010440e015110b54a1100000395096601888003600340c003d0301d586002d0b4410170313003450351914070b5500200000252000d2519102035540324085040c8a80c0b02586040ca040703503410f2610105030801688000c0000a1085042e01040080710f0480140c0080c4030840941d6094400c60000f0703004030304949070004085140d041c2140f42080c1a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 691255800 1250 691254550 691254563
    0x4150c0f02130e0f0106140d0209040b100803070807060612111c0f12090b04060905060a0c05010c0206060f040c02060412170702060a06090528200c120918070c 70
    0xc11032a07130b0faa0302820440c840e003aa00e50f013200301c490090501c20401e2044640103812a0601d0b1074a540e802840390f130003030500c00c3ca41d070302003008101410188020320000d4000c201290702d40040b0f04000307040701d01c7ca6020307880007100190024000f4408018158403868200d96504100c1e80e4543d0300880b5400b207031002802070544000c03600400613240d8501100c061907664224107035444000304c204a01c96805514042440c0c2c260070001440c1c01d0000304404000c900e0080f560301c600ea0783d1142582c044c400d051015820400400466061415191410741012203081c1b000d440450400381d2030704c1010b800138004d010316404e04200c40f405030b46650307407055000100051600d03202100946622080e04c040b02102d0500100048002d49400b4907801002141d5030407555900c0301c09140302e0640c0c9294014142d603143d12450401451010791100b41a45002415645112000843d81010540807007050102000e028405968a40c4840d4550254104001c0d03003c54448034020f0ba60482d4000b00203001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 691257050 1250 691255800 691255813
    0x207050a060e1228030c02071502030d050106171f030206160803070207180504201504060e180c0901141911010b0a030b0c07170406030204150c0f02130e 67
    0x1c0e0016a030185000011903a61311001802e80c0d10071816a0011080d040040c0e103c40428007440700e030301c4040c410000c0280101c914000602d0044130641e1004d910680200d0264150780030010060f0701069804a0b041d64a40203100030744607140250851404080d001e000c020801da0400300c0151030500005e5000b500443d264a0440002541e03080c075405002d0791100f4012840c1c43c00c51442c01401d0080303520801440c0041d42000c80200d1403160220b845905c0201041c050040079050310007000a03100d55030740d0110000307541050040b0240d0074190311221b0344504c802c0203d8100d540c01078030421482407800081040c191100885a4020841480003011049002c0098603404c840b04802407801c22009010340d4194800b00900340019110103054aa10040000e803202c07100402003151500ca004211a40190114400e400e50000e804c4003000c29030014050050002c0b9582601c4000702c0c80c503004400414668030701011240104d8024016461080001d103c4003058214521444403103003200c1c1c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 691258300 1250 691257050 691257067
    0x7091a06120928020f0112090b0618100603021b010204060504030c1e030308130605130b1803160c08060403030f0e03120408090a05180103030f030207050a060e12 71
    0x15490060b240c1551500c00c0c1c65030019500f184050340803074100180c24240f96074403140c080c00a1082c852281c0c0381080382c011b0080507a24094030906030310f03a00801004044e07103411400d0190035103068004680d03119203841004031036402c41100d070003991007034900540c03280301e0240940403065800c52410001c3d40086400f081031340e0300070040d000302c5e0300680d1a2880603507100c1d18040e680c514001c5120700071000310024401f1038060006144c00060115040403209140d0315440d08803542603584c1c0c1e1006140012810078404810107040d080001c080a60b0022200001529624030400483d00c8003100d0050000040c080010007420046c82c13030702e054480529291600170010007844054080f0b00380341c20b0701e860401c0c40c000700303840d92505100b0a030790098403661507a64203070300b0a5500729800f01c2d0301c44004c2507070341300d040004021010046207000154114600070303043c08103496081c0101441841044081680000d90108454002c140000c4a00e41c110580c0d06114a80f06848414400041d0103007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 691259550 1250 691258300 691258327
    0x2310090f0212070b120a052401082a180406060207140307030b07031b0801270f0e06070801082803021c051c2f0c0a0303020304031b030207091a06 64
    0x52041c6c684204c200001e54038411043e5a0b5075085004120701c034803042d07003807641d54040d01240c1e4120010100b02510b1901c2c0a507000300024900750000c1c91030402041d050717090389448441240d0303a507040b6001e0018600b8001d000703546440038820a01490f0040510342103548003400501d02075500b05100500900c3e040901501070920300c0c0c1c2c0c00041040c800035208060703108140315416225150882d4103042d0007840014017110345d01c10009040360307840704281c10031002c600c2508030304200715015082c10300d440d581c01307441144144e0115807d078010b640e402d881daa82e581003081c0c0b40c624070b2040c0c0301d591049046c03c174500081c031110801254542400c13910803030340040203051001c4030000c808009418440080d015100b0f000f112010700001689141348507940510586001004081400e04140302003510514004107100160042a030004c103210a065010345010034850f906c1c00f562503a4040c0d40d42c020740e19421486215000c580d0b694540e000020f94481c0b00e580404000c3c00d068481102c0540c0e207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 691260800 1250 691259550 691259587
    0xe22060b0904030e011b080405040e03090a12031419050a050d05091606230702030321010e0105062a0705030304030606091826072310090f0212070b 65
    0x5001c40e000112241b901404401c146004030340c8605441d08180c0f42c4010302c00504841088130680c0d00007032081d0507298484003101001042c184503c036990b002e41d0304000e445561242c15051105204004000d43c0440c0c000c408510880a4500203039071301c1d1414001c680e507004035950052902d0a010a100c00d00000080c0d1780c590f00c904051800d040c503611002610020034901c01000c0603100d020b01448183c4098001d00245400035044c0d903d003032020350841c110342440c1c4034904202034114005000d28000500300c00c1c0501000c1ea5001d1a1a00b030481c0301400d41000c051503511060810b210310300d070f910309110034401000003030308136601da0703440345014000b409080c040c40d0100c138030342031209a910050310030918420303421842a001102403514800b504035400408030139005410081980003400890034842080c1c03420700c00c000c469500490f42c604048001d42585491400c10660300c01041400540502c4198100c964561416041420783e0900802e5404940d100e0804925003407244103040b02d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 691262050 1250 691260800 691260827
    0x60e0f0702190201020c1c05061f0b0405180406061a071b03170c0c0901081507030b06041701090b070206040b0f0f040b1003080d0b0a0e22060b090403 66
    0xd407190b4203411001d202400d4001500640141e000c0040e58555040c600c00c0d40600c1314032402d0614000c00711781c031064500030007520542030a46c6006c1200d10150562410040580000d4095503d4030703182a002a403002050f0031002e04242c0e062000c6010032407254055001444441c10000ba088074603140714005410908094a038800b4031b42d8103c0c00c040030740300c10809a03580a1450010784041c0c0c00039218a41040042c0e00d0a4452041400090b64417200050f0091940303100825608440211401e116440603000d0010700d8109208401c00e07694020940f410f840000082c414150f43c1c0f0741519000d4040320b40301801c1d05088006204065a01260091140d4094840c4d101c541c2c813514410000304c1811101810341001050200f40040c6c400100540c1200c0c06540c03100d403c5480e070300c540903c2d901c401d010002091307540d68051880d040c03855121000b8000f40209039514a480200f0a0361448848a0300d140c80100c1002c500810400d94809118034070301034501b806078503203450701603c002804101c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 691263300 1250 691262050 691262053
    0x6180c040302041b080415180f020102011d030d0c0c1b0302120a08090904020324090d09030c0603020703050717041a2113060e011a0a0806130303060e0f0702 69
    0x1405180c0c0344c100404100282a02da8860038141d0382d603200c9040c45c03035055440e02c10041d2203400c8000c01c0351003080c40700c4403e40a01c8400840da15984006421104d003c0b406a6001e010003c0d45010010048169003a02e418410003243d100d40f0030400322500080c21000805100500040313086590081c0d404400f568400d4804072414a080c224407543c03081410303c0106035010400910100742030103000790f40c005201030110b0307074a08583c3c0c03c014240c0d00d00440c2d2242d60340e6000c081002c518010055459403400a05140710f0043c00d64039075407103510081c040c0c00145500040c9580806102d94125966143c00c80501d40400c124240302202c17541c880d00c02c48004074407a1190320854102181194988000e280b140c003501e0259600d8206c000030f0080640b00300300f900301700400105a0301d010712010300c041400001004d12503134500910058882c0380040c01424040d405004101d0000f03201604a0411074246620714039a14045001c0c100580002c01e04900803010300902204080020b40108403640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 691264550 1250 691263300 691263311
    0xf071502040f0b0f0703050f0c06150108060d021c11060d09060b06180d0302030f0f03010e0c0301050a0b0f090a061d2d061b0a0b071409060306180c04030204 69
    0x4068183c18001c18090301c01480e0304215040009028030007e14a110f482045641000428004a0b00749041101c22428a0071081c240b05400c0d039003c00c0301a4401d00480e1110107080050300803401c240060002c823520b4007640c0241e281030201241c4858880c0c0802003150360703600b164840380b00141c482240112466410a1000440340c0342c60f43c1a1664480000442101851481d0070040315200008040d415400100415600122000c006146075144094001c0c0d0381d52421074001407000c0d000700030100c01c00c0240010b01c03a6030746401d4010100d46118100640324030107401001c003144651507070340d68010303010000000c139079030814000100c40c80407a4500c00d00b079907440c050208403600500c4a00381c2c0000c0f1427014030341240304881040d58243c0070701124204000f03420700b401d403403100009542c021b0340040c00718070400c00500c0d090350f4080058030b00304c540d02072040400d2640d4022403c44074800c0202100041c01c079210210f483c491502035038084501070900e00c42e408407503405800309038001ca0400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 691265800 1250 691264550 691264559
    0x7060b0d1401150e0c071703010f030512070206030601050d0b09011d0601020a030f030908041e210209010909080d0c030606030e0708060a1107050102030c0307030c081501050f071502040f 82
    0xf00101e40844048207622030059072440082c05082d401007100722030301400640c803203180c0030084026501a0040e407600b10f040c0c034103504020b41340403c0001d200d014600c003040080300503207d030401d032170f00000282005511103801d18610005000300509894002c402d802c00090f82e01552006801c401201c44048001a01d403240120788501c00c40c940500410110032015000d54400c0d0b21003440c15008d803600c1d60800d501d680307565122030412000e030f51500c103000354103124007482010341da5584900c02952504000c103035404180751250521440b80324035907907a40030f018040c0820441d50300c100c0c4001c08104020020300e0203030007000310340641d8000030f1800e25000342e442ca000403a4000d685821000f4072066849005900151004c00b5071040169000d0220314000740342400654015140c01e850b0a46916203840000c0845d410303c1e003140200075100080c071440e00030f84054040e070300100303180859a9024041c0f541c1c0b0780e44589000100b211501d0307103162120b0541c075805402554110520286402e60f613 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 691267050 1250 691265800 691265831
    0x5060a06120308010303260c091810030803150402071416120b0c13090207032a031d130e0c040e03030c0702010315080d09170a0807060b0d1401 63
    0x181e200140410030201c0103202081c0181c52182c24154101703070b000705184400a004203075a4041c0e50400700200b0200d01d0106034604842c502c4185441400013070f8240c60050380801950b0764501c00a0a070704070000103c0c4194860a070081c070340e49005001595143c14034900142c50210490724806140603072131401c801011103c4096084400d1400f6504881c103030707a03c6802444030060a5100c040034200500200a8a135141040051085078001a1140c8640c2406800900364241c2040dc001030f400d120a0211500600381a03010f0309032801103810840b4641c0081020704448400b41d20504816809802141c40c1e00401e0030b42810350b003510444c0580300144400c0d50b07188502d200080d0014400600c83c5102e44000d001024014500400d02d0100c091740c1c1c1d10102c880c2e4020714425004005401300c402d4000c400f103802400d03175a0507034441d8004010011b0312044404002003106030b00190160601c05143c100d4031202c48010040002d030b4802c0d00d4010841031000d400e40c0410b50030b00d10001100543c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 691268300 1250 691267050 691267079
    0x203010c0828090c0303110f0d1407030201060b03010906090608012f160c090c110718020904020307050301060809070321050c1203010501110102030105062a010905060a06 75
    0xc80c85014442d800c0307204806910100032110401c03066903181181004903103084604801180603840f8030400c12460100b460802c0304075514618a80c1c040c1801f41e5419900a10958514a142401549803041858221301412540d4840c0284d1a40030001243e03072009640524100e0b526084d0400282c0d90300c04046007070785e41014031420109507131034500c41150500d04c1204d20b0001c08440d0185000a99850300c610019500029903440000c000b003404109024440c600c91042035007070841d0042109038000c0d0b5105038030b00684104007000c070800c5002003c1070b0160307104071400030410b549a2802c95001403e03074109123712070020703c9510219008c42408910744059981040210f500820b800d00a03070101c01c4d1403164041040000c000f041c141501c2807082e6205000d145024968030351400000410754456026020f030380b40d104200400c400c1e950042185d042c19644081004141c003c414181c020310002c1c031007144254203052450040020110b651351081d0030564081149586840c0b42c3c001128 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 691269550 1250 691268300 691268311
    0x90f0e0a1707050a06090602190c023a0506060a0605030f010605180d052d1c0302070b09010b010915020a0201140c0f060f1506071104020915070203010c08 68
    0x3201d01480c04500d040080c25a98001c0c411140d400700560b5409044503400c0f542995425408207200d105015002c1c403140000c074084c80c01c0714050400e84c0004014810f260042c0b80c815202c0604a00404d054400d00c110145003001c0c43d0507202d0030750601b66140d220455102d48280e00741c05010a00a00403800d5030301441100d404070750141e00340360054406034082980f0301000103107105035070050360750700e10000382140c41036020b02105400d0320410384001c03030250f881301e01944a600e964000c650300000e00102030300822000c140750480702017095000340715044001d800160450f00300700c080641504609003240e001e90391000d4841da0780000345400072141c181d0324016000000d62502640c4030f45803100700100d0481c4150302d0841c41080036440d01131001360311889500708a0410003900174100f4080d5100d05519a8007508808a100245161140034001045603a1820100140307858030742c1550540d0a01030840c0c90b1703003d50440166aa40c21400c4200d00c01c0d802c09085034201031050030124040c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 691270800 1250 691269550 691269563
    0x1d01090504081207030207140313091b0818150118061a0702210703061515120f022701020f07051e09010902030f0112020d03030f020c0601090f0e0a 65
    0xd20300c0f440120601d02e002e00001304168007440b94401084a031001c000366007010320300842d992080e4804002101845a001d000201e15240c0c000030b00050400140c0648003040c45c1580c415070f50f480c4500142d614440d0b2480e403034822207080e5000d10700f4803401c00d4143c030540c84588401e0a85c0c010074800761080c600599805c400307010780c6025100710210140103018801042c21f1f0030741028080c9080380010381610111254464042001031150074480c00081c2c00141030064140d17828088003002102045a0100400010210603888441c45e0340c0284c0080016010541d510790341400c0216000108003105042d0400c189800401503000040ca10b4590380d00d00050708000389000d040004e2103800480295100c1800020984c00d90b6a081d0301d0340c068001210300507101d04007901c200d00b210405800212104888000300d40140e600e891140982c142d15107404604148405c4417400a0f000d541e044030101e10584001292143c01c940040c020a2183c0804002180c01c00c000c140e61048881c0e40504074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 691272050 1250 691270800 691270807
    0x1170c030702061b0a0f0309050d020c040605060408030910120c0905010e030f0601140414040501060e0615070b100e1303020d030204051507031707110618100917041d0109050408 78
    0xb0381d00a038086d80c0b58410b181000603580e16961507590825a0842c01500141c1205101c49294905031103224080c1c51305a840c1800d00d4103204005035a0322804215920440e5007040c0c3c1e8142d80e2143c201c000c40c8030004007040c04100b01c9508060101c4040f801000d0100d00d007075884a4003401d001a007440000b0416000b8501a440d04464441e415502001c10b5049030f10742005c42061022820354602451046000103419460500c03003000c0307428058070080c42411030742e030700d1004041130704103171003400d5040501401301ea1180144d58408144036444251805121403c00c1140c1010000302004680a502a80c217460840309084089105501455920a0302c051030320b00c001029002801c102c0d407103424002c0e504818429281004207045614600203414180803081c6007106120040d00412421000c060712011550043c2e1510311039400ca0052076a1980c2034001d000c802d000f510002d1007041c804a640e00c2d1240120724541111400e02001010040c2c00083c0203085031103540d04c15a044000d0609 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 691273300 1250 691272050 691272067
    0xf070f03050402011e0206010f06030b010f0e0a030f03030e0f07120b042613120213050916120209060913390311090613020901170c030702061b 63
    0x28440540182e04001c0d100b4020802c900c0c072a02002440385e0160010002585814019402e86c05e503604110201424420000056600300c11621150065400c11004d5000c200c400300d10300c030b1310300d51000d003c1c60420880e02082c143c0683c40a2120804042910b005600041180359100410b105422000300d5042c1044040740340130b907881e50440e116004003c4403142c0f41e210440312036289a8006130318240001c0300300c0301e1180b2103050b5004014030116150300d004141c00250324404000040712615440340c0001d10340c0e40060042c201501c035030041e0385e140a0740f81c91090b1705060130584124010340082e4042056440e00656040c03090012344102d2500c0d822554844920304805088100780c00707100c05044100200d50716008140c0303220128803002040c03540c10000301444d05e24600d2401060703024103008494440c4110f03103c0ca40c05c9a03101507580c07030a510040320304020580038072600c81c0d000b8003441799100c031030740003140078983c658210303901500c5800144400c00003a0450904240c4108540e48 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 691274550 1250 691273300 691273307
    0x10e0306070e030a06020d14010f0e01090506030c120318031c0302070c0f0b09281a040905040803100614120604090803040615170705090907050a08010b090f070f 71
    0xc2d00c00001d0241da03044c0115642e15010b90304880610002941c03182281030104a81d149010300619007450076607101494000d00005c49081030103102601030b01c0e0b0000480725101040644582c40b4080c00c3e60b084024401c035056200d422001c400c0a02001910701000c15207000038209160074003421100c0c240e643c80070405c0d80254032042c0d0407159550900c4000940807410010a40207044505d01603554116401c2044040301e0b401403840e0b224040b105400d1504074541980d0400c0e51404482206010741c85010403425000c0c41d0f11080c801401c1208001c2000800c5021b107002d100c00d081545140c1b0703210101a05d503032180c81d40f40c10210348103001c1030741e1400601140030742003100500300040700412078036905050307070007128140c035010b8446d043c0e1400d004400031000000c10184044c00c0c1d801c0361200000341c8410302da120f29846036250102160f1074001c14841c020042100400c140a600d40c0c071010b25018082e213420b5248101003210008100c0c410301c8808520481c01680d414004400034181035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 691275800 1250 691274550 691274567
    0x40b210601021605042301090507030b01110a12022509180b0a0203061804030e0307060e010c06020c01060806090703060506100c14010908031306060f06090b250606090b010e030607 79
    0x40b130442106d1034001952613611860b10340640707002132000c5100d207400070001d010789403840b0626040018405610484440101c2c3c5510a0b980c0300540724401240c04000300c2ca081d0a820b81c84000e1243c0c45416201c80e84201007120880d201f50300b0a12040d0300c0300010107245d441c1e503d4090300000c0004000380345c00365564000c513405a0001d14205c841b0000c550b002c2c100c60317801c6400720042000c4000004407480d0420000d40202070030301e030004409a81c000020302c40003040350020706081d0080343c40742d0341d00b80a41041014142c054102e43c4a0301d402c03101603603140928441510a186400b0120b100c504000303604070f20005040d160b440201150f81e580c0e0050880d0741410100a5580b103c098001840960040d8001c860400c0900403084850400710700b100c20075480300d1034110040c1c10070801c2c9604022510116615840300a8548070106079420a0102c5080e0310000803035074817096400c0000a0744040d0035909842c1040103166071035001521410700c21f01d0781c0e03a031540c4032900050b0520700c00d800c031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 691277050 1250 691275800 691275821
    0x3060903031801020f0301030629030c0d021f02031306111c030902090106030e0114061f260403111f0f06030c0311030d050307050702090606040b21060102160504 71
    0x14548081024040c2561b0802e0700700302c5400e0307280d0780700315400660101c0101d40250100d40301c41c44410080f0000e50303a040000c41050064030482e08442c250b50f11001e00e620b2920f000e02c65400ba0f80d0706010029206d40c4603066907290310b500701c9004501d031031240c0e44c843d0594a004e0020b1071848492800f62103d81c4100c0103140c00c050b10781744044011b0712220f403928005c000035100071a5400c0070003c19400c1d108058100303c180801c030010800190340300c94045880c1c40801c880c0d20400c41141100303d5519035021156580d90716042c90f001403055038000f105119a009550f0420352104400c0041c1c1ca601c40300341000809050364846c01800035441c2c0c400501581d28442c0050340035501c0d40c1d918042c0e14154802d94208801c1c02e182115414180441c80492008ac03801500d035141c03241001c0c00700e008200000e406480010300040080d200d0b081100e01801240f44255128800401617520541c044044a1891910000450701650000503940d110002c1c0c1c44007a014107041c8421b0000528094a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 691278300 1250 691277050 691277053
    0x605130c03081c0f05061f0905060711032e05070e041a100c020405010614030414030706050c0c0f0c031b03031e180d08030103020424060c030e030609030318 69
    0x420040302584d02c9104402e500400002c10145403940c10042c03903020050240b0132529041d200610300c280c0c411002000c1c0c680488444d5103902a030704200e68005601d0104540612981000030f101c000812481520715035104000040c0a828030b4034039081d9902610420003103408100c645000346425000050641c89034440810500c1140c0001944191544051008206090400380a504150061501401b009d003000d90700280b101e09041c0f042d1100400241c180241400c403041500028800c450305150000410f100b5070504000c4d10b16a43d00001490100d403107005100c2c1c441c1c1c0804100b02d180c441c0002c0c0900455812801800852295103105035410b000800070031010440000480c011810600d40c85d64a4003840101c81241e0301a40d00383e80c0c421440c034804d80000402d12002c0381e06480e030540380481e081501e1010803403090040c81d00100c0c0841d0242c004900143c0c0a0781e6901c4d482c1c000e5464500003c00d0754249500c640098800e520b031030300204001482040c8065407503500c41030440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 691279550 1250 691278300 691278337
    0x90906030c041104030b010e06031903050705010609050915060603070f0918051603051005010c020301021303050f1002031911040f0e070e011107060807090305030f070605130c0308 79
    0x140000d0032944940b82d2080f5100e00400d0600c144403c032041e40f07003d49808001c000d030b54245000001c5e03a92500c00300c0342510190b2680c8002c10144920150b8050b20390010017403100c00c2c0c4941040000d01400c403103c50141c850004180001100014074a014080240c58286542c4980f0750031a80c07164205a02d80504c0200c00c8005000041880000303144032144070009514240345002e200c00c45540c0c0111003c04d0b05003002d0000c000781c01340410080b24001d00341500c5069003440401e019018103a103034000440b55510010a200010455003400c04503003046e01c0c002141048080201e00080c2e07043c4014411410302d805004020741d204408080c8030810340e506143d5078a603080c46602054115038200800c0f45c0501503103a41190040c82d2007042402c1c001c10610100d54203a54807140381c4a0001000941c01c08608414000c1080e100a940c010003901d0b9103c0c0701883e0040c00340e203c400100c440724034082c0040c0714512050001150181c1c0301444940e041e02d5a1101002d60f0451168003944002c1c54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 691280800 1250 691279550 691279573
    0x90c300f090803040f0c1a0904021e220f1802090301020c1c020105130b16120f02070b0a0207170711121f0c0504060318020301020307091e0b09090603 66
    0x84000e035200e40e1140b45400080c5243d46000c1a0800090b0712402c1e08a00c04181038650b43d187c40283c0e15400801e640041e02c40022080081142410b01c01345800040300049000c0d414030700030420849000c80252810107586d840c108440e13501880c1c8a0030411002c06425551000c40d0340c3c00912030307804020005400c1c00700300c80100341046010303803420010f9145074403090480d64081c0203059000340f0503a089d076205015a01d800700a03034001000b064118840c802c0303640c482401001c04107a003e119403010480b07071030b100b4600c0c0001d40c0b007060309132144880030b800511a88003900840705210b512a0f10203025010070103803404290040c160888108895501c100001d498500520800c0032080d00100809201384140c901c4d00c000d003030000c0308160b007031141d51902c40c0d40080c21201190071030b20340022031460303000d0011301e00e5441c9507000354035500000600900f5580402c42c0419502440301e4107208540f00962000340180b24400e07495044028441614240f0b0141e0b55960321840227001d032401d40d00003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 691282050 1250 691280800 691280813
    0x40e01061a0c010b061602010305100b04080f1207030e09131b0509151f110a030f1404060801050409031106012706080c0906060f0301090c300f09 64
    0x203810307044401e6011a20340e0104009006034582e4a4003520303254500309405001075050a006e40029061588410210318141e12041146000306034a15115880da0b80f2480e68076114601c0340007030310540c4112144180282e00503011540d5640d0301d621605100920b11043c025181d4000b489025084803c41e0080042642c0200328884070301c1545c0c6800c0000e00f80300400100c000043c0c00404180c00f540b03030b00d240c26107c0300b40c030a0622003410301c01c00740c0752402c90041303c2c0403100c602001c0050040c8000041090307042070900c0c0d440442c5403694010300c8070b40c9000c0c03052030007031f4440d4400155070f0a00400950500fa031020491034060302d0104e1040d000c581180e850300d2401e0303005c940f85c8440c035800e518030248010701094200c51204404d1041030300d080c600b29900c00360303a0145841007905202140d40c43c0d072508200e914101049161503220341c0d40d0114080213200c0e044001d80481d40911011024140c07540440b4481154213400d000281d0380f010031100181803280000030f240396640c1000010441 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 691283300 1250 691282050 691282079
    0x90b030103030f2a1523071403091f0906150801180809100c120807120204031a060102070b180f042003070512041103060c1305040e0106 60
    0xf51240c4010b0b51110900810748440c1c0200c1c03100b41042154440b641d081c2c0b2840400000d6003100e02c1842d03941103000090010641c40016a000501601d60706810b50380760640301d44195119203c41c268900034200d450700600c411100054035400801d50307079030b0303080d682110f4402d0501c4032600042c04010994800c421528903108410008440b42c0080210100034000d0070281543c05d84007110b18004d0340e803282058001c1e443c070315108540d0b001d0351889651140880040d0290080344081d840548690043d0044005642c00b0000500201c3d011030540c8403030080b64200c0c0c3d40000c041d51040d10200c06d030341180030040c102c54114003500100080820511002c3c088039050748240d81a82d51801c0f08000c0b407806204240b034092800c05018021741c601c2e007520040c001400303800266a82d035410500702c8140c0b180d001c016490049030b81c1404140805100442c4043c2001d604031803040c3c50f00d01015189020305a035003011164549403e00c031a040c240c10215110500400205400c1c0e00c4800c03d648411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 691284550 1250 691283300 691283303
    0x507050a0810051203221a030912270d02100c110909030c010b1f1b06020a03060509090f0d051b07080d02100b01020a060b1305010b1305030c03030a0807090b030103 72
    0x500100f2041c1641b0000040c660079102e01141041705607140140303c0021001d503500e040b081d420b010002640d2001c06100610404404030580c91b135405c4c0190103000c2c00c1710041d0b40b420206c5962030b4608000d0800706983c3c107920360000d2420741c03a000028000c80b03002510010031181c980c03020f440001251901c1811034028445e04018648130b030600f045150840c0d02c400c90540c8206aa0a9214031902d4035041500413a191490400f049000480000103060040113000305031900c00a01110b80b2a4164032280698600b2180c1c0c0c180383d210040641d0b510941c0050b011050341120032800002c5000f20024880086260300750500c14050704001c1b81003c03000d5010300e07031740d40102c2011074110342d05002ca0b440440c2d15004c2001003030107090000b5076074031100d40018445a41e8103403100e0103903601282c1e01d030301458182c3c00344529078482c0c03030401c201e42203400705201000300c604011809140c00718542240c2c0310003800850800030076000072524510b02500391024030a0070900410090343c090021030195 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 691285800 1250 691284550 691284553
    0x90c0f0910031b02031216140412020108340e0406031103070824060f0402070516090b0904080d092307061403040210022a040506040507050a08100512 66
    0x1610310f0481002d4108180a10001c5410810408401404003d85260030a1036001e1443d407000705c4107816540d24502480e289007412000c10005103e01c1810085600c82d4400c0e80c1381c1303c00362611010600d41920601d05410382c40ca4203003107041e0300c0500d0050182006103038905107000b103083c03a01140403202c560b08281d80810030041c1500d11403c0c01c001c0c03071009010f070800038690340c43c0041c1d08284868502d445104007131075006c00714086985812103082d2222004008540c0d03440c040c5065981c50350000c1007030007110700e50700000411078024400c0d00812180a00080115503950741c41075840e900000304030400c10341c2c6000010114a4410601d0040e10b04500003402d13040c1310555191501089074442010000d08480f000d240500755016a900300758159003481e0099011201607060030000312001c0380322011241c240e60807100f01421071781080d405407402c014645a840034801624021904100494020081c81111a109401ca1a80505040b000c114110b480c3e60000f150f425605072800c546 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 691287050 1250 691285800 691285811
    0x412050f0d09031b061514060a0f050712020d11010b010c0602090409061b030b1f0c02010311030a020d0e010c0203041e210203060603060609060607170406090e15090c0f091003 77
    0x70340d12001070540142100000703040c0b20000480014238035100b400d404208010901b00608280d9014030103954030b080d0700c4903c400304803070309490083d13441c007558180341c0c0003842c5109002250703c0184104000c1c0705040c1d40c0c4a48624554a40c3d4003c0c2d800083c40c150403e98807403503130001c1038562007910301036118680110780603111000e0003403c1c0c07043d0004040c4140b50b41e400e0421076403070011940c51003d80342d00300708a18941600044c0e0080045d80d2401100100000401427142c03a035a0040c61a4050303000100301c65021100820308070707a03160821a0240c0d008000030311020181d404100c0d40790080c2c00700440103540f03900c151005203a11095440101071410389030000c40c076062041603449801640105038500d840030020701c00403000340c81540030308000910f01d01448405503001d07101d0b128801003d50384650326038004044181c10304c550300040501801144804002c1460a0b0441c14002e040103440e488080c0315592a91201080a0001400701300000c226129101d038003141e80c090b510000b42 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 691288300 1250 691287050 691287071
    0xc10050a0f03060803030f22050d0f03061a0c03070821060d0c030602130302210d2c04020d0903111b03031b0a0c0e0412050f0d09031b06 60
    0x203100e044078800c809241c2400070501007842c000080c1d039030048094420252070340395288001c183d0f000880c81018000544005182032040003d050408542140d8455404006030741003281115540c1c01120540182101c20903581040c0c8006030103400c02c41c4040c0c030319006e415510078454bd401404030104251500101044210506d030806e5030050003550499403801103991030102689450200800040c4d02055042c80b10700d540140c440503580c0a007144200e811642001c41c840d03d40d031500c09049200b04040c11614030f11a18a117030008030b401c420301441c040a00321008039030700c0340a81d00344c1140d8240182503054034a0f00440030803a009440b0003150051810b821810802c800588041000254800c00340e40e07100002162110600d14511165102000441d10308281d40d144028118441c1c0c10390105071860103800e4103010ba40700390305019088668a0041e078540c0070710070104007461710038410068402e62640040c90090302c070780b4101141d40b4105944800603c0511015155240d0f503c80c03007071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 691289550 1250 691288300 691288307
    0x219121103100b01021908091c1118220c09150f060e1e09070216140112200316090806061c060902060708070228170c10050a 55
    0x42c042ca404900c1031118070103080001c0e5541c4d4101c80c0b84c42c24255010000c006000700c2c0c2081d2140031178001c0c01000c0036030401d0110301d0618621b41c8242c074158180e0384842c4480c9005501d150144003c66119041e0381d64281d80c14400014062000d440c2400810078071000951028603540030789513420000400c0400e18403000a0281c1a0304500003944801005004180d009402e5446280003241c040184101c10b02c88440d80030039091510740c0040d8450140181c80d071300401c8801020084150751509640d80f100c0300000382c0e0100d40c81ba030100d910120202ca403180141c00281e44040400b44a440c202c4800c1c22000c140c1d13108a40074a514070030f401c00c140455a022550a0040000000801d03d90031b050307001611100c10f046070610070140184607002000019005281d9207034004017a161250000c3c00c0c43e200952011001303d02c1241c0e24220001c81c42501d0380a440c001d070a004210000c141003020400100c103590f100d440d090b2041403920000c0c0d50300d4411032070b80038559580b650341f544400301c80a07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 691290800 1250 691289550 691289563
    0xf010207290c0405101101020408010225020108010b0a0c0209040c090e060f16021006030c0f08010905120c12030112050706020303090c0d1104090f0b130803040219121103 75
    0x107180d0000c01014040410000b100b03880039580c2c205c4440080d015030b09000e5448000d2170014904550011400054280065015001082049081071070b003407916035414000c07441ca2400280402c1c0304000501039401d03041d002c0c114109031401e02480807210394002074446074040ba003c40312844211401d1000b5103030f134001c50345404a0380004165034206003604100000c0001d10a051130800540308084140c0308102030140ca510700d25003081807940300c0c1400c0d0351082c0305000b0740b00412201000040d201c5014421011915003000151090ba081c2035400c1083c0d41c844401504c0d00d200382d030460f1a140503144025402031032030900c81c8814441ca407801c41e040c0300056001c501950802c0c001c0003075140021600380b9280004960409403101e41d0300c5e21000e401c0001c42e041d034100e45008490740410130300308152141030b8004c0c61246001d9503107000700030204409440c000d01c0c460f41440418014203110400d00c814060910100b4441603c501010103115a001020b403003070000c41c054a0201d0a090100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 691292050 1250 691290800 691290863
    0x60e0103020c070b030903221a09010f08190606030504151103070f020111030901140f010f1403070905090616090e041103012909130b01030b090f010207 67
    0x40d814180c00262071038035080c1904ca003400070840040090b00600041c002c4070005000500d0480202d0120110b146c007a2400e401510b48030109100c903080100c3c6250207075000f50105a55512182d14103200c202c1c4c4196000c3d19030041c05180388000c51000005c0d000c0c0c400a0301d040e0350f00158500d01810b100300816042000229a185026232121200244c141266401007850502444840900d501240141000c191002d00350202000384480c0700c1040d00004800300c3e00703a00300d000079195440c409003440005e02c100c450340d0f00a10401c102c0c001c14880300d100c1181e4024180c819042d944c0c40064203440c011200f500141c0c12120411004038250004000030148030714120f4501400c00500c1d078889100a40041c0515140403c4010603a030250896401803103404174008221041c131500c1d004228510580c070303204032958800981400c1c01c44032a16031464000d2451601c591860701d45284018028008460303034000d03070b1803001e21a41c0900040504a104410703014a03442000144405400315088 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 691293300 1250 691292050 691292057
    0x20a06050c04030f0f080c0a1a091c0309050319030b12010b030607030e1c030f0b030615011413030b0a05010618090b01120515011b030c0b04080702041401060e01 71
    0x34030100c0e02e0050b8144500f0350140c80c8640c0500281000c01c001c1c0507030b01d847d01d031510805400d0030800c8201000404e1202d00088080c2d001c4e100c075201141c4441401c1c50700740da81c019003501900010f03c250060040c460045c41034a02e840c80c13004907840400a01d10980740840d46441410b103003420458440d601100e034400082000c07425942c00a511580c5c086d01100803d078541400d00007403c42441a007107052040101082507801c1078202030080c3c0392009a50342d0803480d150f1854150304010444501c0703101c1a080c01c800d0000b4000c01901e05805481801c5520b2409004040c0c1c144101300301070000d54051502c441e0ba61174140c0495040da00f058100300200417520380e26029440d01c07959000c0984100035004120310840000480c2c0d030001103150038120a080006100200e8825864404003801c2a83c521403856030211742c900381c40001000040003d41c03103803280c070085100440380c0b940040c800c0203503a1030315010340c00140507684082c1034481051303000303001040980d4000aa41e04582c4003800c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 691294550 1250 691293300 691293307
    0x905010510091a3a050601020a020d0813050307080a05070f05061902030d020f0d0605010e031b0105040b0409050f150307120f0501051006140f0406120b03010507020a06050c 76
    0x1034003050400149000503e01c6800464241c103107400b904c01c00b031460040100000b440e810130030300740d1304854900d40d4088582480c0c00007040c0d007940301203400501240c02a00380056101035646038003442d030120a220303949101044000ca119070342440003800600b03006000f400d00c080c81d424214100800d950000c1a0107420503420450354580302d00340c4004038184188907401800302441681503206110039603613450b00c0000e10b42464007035017024041d400b030103040421145403210f005443d1403c1102d811130785030340091402540080f82810f06844900180340503801d041e0b842128442c50740060700000b82e696192010040c0131010540c0c8503a00a0b402620050071800d06000304c0e80b19980380c00350140d80343d401e41d82d40c1c0a110701034050440c4d0941c404001c20451400203494080b249441c041e11000071215640a80550a01e90035207071000d030380100c41403401e4900101921040ca152303401214103500c4041d82c3d080d507542071084910611841e0098080d0f08128a000c000310740c4018404203040d0002e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 691295800 1250 691294550 691294559
    0x3070b1b0c0d060c0e131410080c060703090509010e040605090706211811130e070620010e0c0102250303080711070f051302090d240204090501051009 66
    0x104850620550003c43c0010300040b00c3d503044a100c0003041032142c0001c0b1005c0c0e15405444541e10107440e0014012010300d41d6180c03001000007100d2030f40f168285c2540b282d2900019450203a0040050501c00d007040c3d004e090341c41000c1a11007500f40e0200c45480c51000400091081074066250b02c0000c075000340071b4141c01e040340a00b10242034541802d4031030b2103c0c032a00076031459510501e8600200d01825240d42d2003450454130602c4a8004103003e0402c000f207035001401c1034040c07100d69401801c0a04012030a0040c1150440440b5040005010031644e0860f4468005c0c800c444082c00c0307010242040b01025000a4a4080483c0e1956554030104100c6202c4160400c4c400c410389505160084083d02d907100100c4000c0c1001d41c0500300da0050f07200006e50300e2814410f1008980050703681c0d013200345040030810100c0c020b07010142e0b0400090040300300051080d1680d0020901207038013007500a040e003116002240c1158005425503991000180018a40b01e4410140e030007941ca4890301103400d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 691297050 1250 691295800 691295809
    0x2010b090403081905040c05010306051905100c02041b030e070602060a0c0201110a030506091b07030818010c200609150403050418050a11180105030603030903070b1b0c 74
    0x108050704001d40c04000c0750800c240c4084411010749450800e01c0582458184000c1f0041c2520800d8046440c00900203010305003a01070000c2039400079051070409140c18103102c02c50100316645070401500038075140050b541ca02c282030311154080080c1c0180d200c00d0101a0403640b494900b404503034412242004404c0d40080c440d40d0021503460041591020302e403051340035201d0166030305444400481e0300354129506070302c00d600c20401112000e01645448650100c1031a64205c8403450741401c2000c200482d019070f00198000350114024000c0c074547d910341d00d0031030307140d003294070005590a024032403102e0000c61548802c001c56070103091242426040c00303560784081040c502103455410001024180601c059500401030343d0300b041c802c001c03421070100c020b045c1260345004062610103403403d00d1a03003006541c4075001138900b140c5015540300c0151290b410040c03030300b5072520042110022039142070111708010110605180d844454140e00e075006141010b4140b049a4071148600000c0d503075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 691298300 1250 691297050 691297069
    0x605060c0d050717040303020609101107030c0c090203010b0c1b0105030105150c030f1b0d02030d320f13030206220c140109090b060306120307050f010c0f02010b 71
    0x40c0780c1085561143c262800e00e8003c0000713900803801c03070000f00e4008185500451640d00c9401ca540c01d40c0c01900c0319131443c60031100c944c1054500d001e03050040c40d000038011214612140d005814a12806944864440603039100360407605668202140440d0945800c000c1030505006c0c1d824030706d006540703640000701107000511035103100c1c03d0300340b0603041610542c0381265020120407003540d58681d02e91301c1304c01aa034003a01204100207131a20600c4904880032481280f5034a450f0f02035460030501401200240c0b01007080d4070050381106220349031542509081540000700301d1140700007441d00e408058030400c0c0c01070000c0240903948040ca0000b0368081680c560000680c110030b000203540c2d030440100c05406803001803013080c1c0c0d800c1c049580514003451440211090b83e422111548030a424001e0310410501c681c0c1080007030000c50418500013045207502c1c405981202c1c2800c2d590340301c9a16028207070424207580d940d030f900040034062f40003070311601300744250000f40b020381144c0010030800603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 691299550 1250 691298300 691298323
    0x3020a0b093f160b0c0f0d0203070e090712020a05090d06150f0e040f0317040606050913030203030117032b0b180a0e010615020c030d1701120507030f06020d0605060c 73
    0x4d55400024041102840c142d6410701d8640182c1c5ea10f610000a40780c0003903005403000d00105507074428900c00f900d040c584140c03107190581c5d2241c003a030413507840900294000000c118180b10301801891400d0b120b000030386c5861401541c2c08a403111118901d48020311040c1c100300340d071001d0340302c0070b10544050419064001e0b40c03001d0321607845d001600302290040d08031058500140c0d1094180414054950841303c00e03100d007100c4100c01e5495a08801010b0714800e070707000300982c000303000410079a54600b0303c0000300703403441094914201c0000c1154000d007044202181325006528608c11260840d40310340c90040e42c0584844254a20058a5514024004100038401a221a100d089400082d0080c600402c42e10320103070010452043c0181d02c404650030704901a106981d00d50960510840500d40d03040c41c2d40b4080d18103a400c120079000d03041c4a03000d003a140c41c4145a000000600e84401400801d40201d00040c0c070f80050180440c01c0e60060340c8200d11841d0140038802c01c1e00c6001c103400c040c20707 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 691300800 1250 691299550 691299563
    0x61809050a2006031303030e031306030510120b0f0903070206090f0a03020306010605070b060a0e070c0303110a0c060b032d1507030506090703060303020a0b093f16 72
    0x1480c0e070031840c1070190040c00143c00200c0441407081020021140094240c420f03141804901403180c0c413150340340605400f150743c61661032010809507000358000383e0800403a229a008031a02c1c1c0d94080044100800112641c000302c00800410400504c3c03010742000c4014059803030000a500014200e024500060388940f085a0381005030303a031207804080080d680030742a510650b0b035401d0058410703004030105440b65440b000001d240c1b0f140c002e00513810345144605402154403040e004443d20441e8190031010305aa410507441110801000740074400d05595070b14400e4601880d0000540b0040d08941e4040e6001c070000048614144448501013010411080395070f40740c41c00010310303040840040151010704c2405000d80d06034035802c010b20800069410700d4454503004012403c50702644030180040e003051828000041c1220800e40e001a60745040724074030010070200400d4103090280b0000400c4498034650580c0201225100d1503e0440d000ba0703050603490040030b64800c400b0340004244 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 691302050 1250 691300800 691300823
    0x20d020f0c060f2218060e0606030f1e04050c100c030e0f0a0909080304020f0d080d090311150601020d0201110d0f0207051203060a05060405210c0310061809050a 71
    0xe0403150001644c050f452506202c0c00242c0e00d41300404944c000d100c3d40741100b0b0a054001ca034400c420603682d8045d41c1c0c09030140307156540d014003c0072220700290030040340140c01c441546043c1024140540282c2c02103020f082810414000c00a01d880c90501c19024002c0790340d1107102117a04030a00c0d88004405441141014000c0000203801499580040f10781e94588a000014071001d0006940320b5842518511014585003040042030381d810300c0d0080129104002d030900c0500160040400300e8424240032102e411800d010504284020000fa46a943d207502001180d42c1d04006000341c199a500081010203403664201055200b11031000c149036850702c4020742601702907030486212580103001d840e1000c1035000e42d00d0182e8401d9030404d12410f4050004034a51400302d04035401c45200030b103c04a0051005082e0fa464130421100702c0080c000c0c16600c11b025142400508450310318402d000880074180081c0d4401005a114098410751600c80944001f030b9000a48084e0660411a03c045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 691303300 1250 691302050 691302067
    0x100c020d080409020c01061e12080733050a0b010c0b0c040317030109060b0f0301031b08010c031413050703021509100914030a030909150b0a020d020f0c060f 69
    0xd071449294040c40341207100103010b080401d410360203203050f5480400c01c42511224102e4000b4800c03900d0003070501c1c0b0f04282c946000000c1080c03004181041c410b00003e0000c424a8250b143c2a101402507504a43e09000e91440806803d1042a500081d078013400c00020183d00300082a600b1a084020301c03064081d004120043c80d0001501d006640c414001c102e40c0e40b0020103601d5170780080c03080c003113040d081c000b0101d4246a5807080d01c1e0206402c0d101541580c4ca19210080207800404002030350141103140402c16420a000c1c40c0704140302c0b0b40740820b14a96030074204290400c028044c1c100701c01070000314000503201190760400c40e9011501501082200c2c40e896805102c2d1000b56139103d09003148121035290031013440c41c1203c4d14580e104803110040e1040c1502c40d4070105009000401014003400f419162340c4c000c01074040784015020100b07481d2080d00300590b100109410250b071044901d903100d01e504228541c020f004207409840d43c00b0b80703580420864041c0709a83ea4009801143d0801e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 691304550 1250 691303300 691303313
    0x3140a02070f020a080106030308070207080c040221090d120501030f03111509061b18120a050703080403020301052d06010309050312093a030908210105100c020d 71
    0x1a51a5001489501545e0303540d00554002c1105100032400b1488070b10008800900124082c011548184050024880d191003000000e501101c14035403036028030541102c0350105120340510400c0c0e0305d00140326000c0703c4e0101a0400c0508410301c001070741004c1c014030000344030444c1d03607003010fa00d424521170b000ca1005540c0d007040c079660f6014004060500800c6000500000e801b4054004200c2400003207460301d0180d00e062292200482d0b8640740c0c3e06030703900c050821000b1141026642800e40d8104221030352410708003207103a4030540c0d01000106003842075160a1040c0b40d0400002901d811030203800c0c1d0f031070402d8210aa0a00805000120001501c99029410134180b07107070710209590303450001a04507800c40b103007500c07002204e208038000040c10340ca040d0350400013804040c4002c1102c01e040000c11f1130410718280a03004040d195802c040026002001525540d140c00e0070100044d010ac0d4003081541c1c20513407042e031158036450a515449604000d16281c0340d40c040c0d484402c0705c181d600308170 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 691305800 1250 691304550 691304573
    0x200d0b12030a090501080f01060c0311070819050c0a0312080405070e04050f2a06030a0608030f0703112107020a0e0a0617030408071716030c051003140a0207 69
    0x10003440c080000c00042480d03108041c030040d5103098907224040d03141e080401200301024022000441d070410a10804a070043c070724009103020b4101198182034641111500b07010b0406185c131385054104005000b0440300b03001044d442d42c420f0750f01c01c1e1507900c0c64807842c041810301c0d080c800030301c9090408241448011301600d00908100c00940d070090030b0624199540c0c1092401d084010301469840181003e00007107800b1981c594401c0d4107402850345c07402c200c1c1c2c070b90000d00000700b01a03030f5440000e0240c0b000c1c800b618820221a00807525040c85040140940c5070400e00380c7c1c0e0300e4000401100c0c1c10450b01c0d01c071880341802c002c2c401d5141c0c210742c404501100e9864100502c800c03010410021482401e0700120207a40444401c1038014002588080e03990042d8042c031b50840d045000e0611a45c12030700d80207c55942100c041300d80c039005036842a841203d654109031800480030a0510050400c01da8400000c421458100001c5586c6180d0b00360b45900030300040c24840d000140034050000c50000b9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 691307050 1250 691305800 691305829
    0xf0501021201140a0f2c04030c031701050a030f050f070f0515030f04020603041e0803070f1110020c0c0a0b07050c0306040b0105221a010201200d0b 65
    0x219910700501c807140641000034440d50040c141280102421030810703a290744120390803d01400c041034200740d00114441b00381c6d52440340160829000e515088080f00d1480d004902035110602411070358140106100740b40404401c1110030780340100b103030342c0780c0440031800c90b500602613078003190740c0d40390080c1000b8041034012400d120340000498260842007170002181c0341110242103a800303c0e01c80d080131340002c030b034141814034030740d0000350250030154000c5a115116000c404650312005089100b2620030718000d0740d00e070b0350100420005513049088540484100d0814100118261009a6942c1180b52261031459008102c403004840b0400c440b00c0003400052425001c9500d554400e4426084144260b48074407804e209a1258200454042d000e203030060062142a800c2000340000d0049441040c100011013089000144042d403180c419015001010300c018a5007c5000a09480d15100050380c0004900400d1154a48000031500c8404c000d27100424141038010000310300b100302029 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 691308300 1250 691307050 691307053
    0xb0c0a030f02121005041e020d0b0d05010212071d01120204080d11010f0203040f1205040b0714060c0c031206030a0203030403031e170c0304051f0e100212130f05 71
    0x4044100450050043c0e01c6011081004440e0030750703035420803056880011b401203c914010742409040320003500142541d8580c01d4000c2610380f0b00c5000f042c8625a480b0040e00c043c0d601040700440300e000e402505810807201c0c5040c01c41118a1014204041d075204a40c40c140603240c2c6a120f4160080d80582d4000c0804106541c044c0511a0f0050448011000c913095a075103040001c1c4020710b224420350380601e4020401b40e018080d282d0741c1001141804018809001042c04005100011000209840392045192807148015214410b02e842000752a058a480b0305008034141c102002043d10b003200d1640341000e0142d01c2c0c200109050011560019415010004000c410b0542100c061940070b03a4241070211500010a403c54034401c5030320f41c10403622102c1000c2100e8640e0100510b8025000f181540d00041c02c00c0044d501412550340c64030400d89e15001c0341c1c981d13036000b805010b4940b021440103520b0a000e1644150031004001c0106d115000c0c0e0f0f002200600ca00700b003c1104543d800b20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 691309550 1250 691308300 691308307
    0xc16020d0605151302040b0306130603050105010b090306100509060d020117070201090b0a150603020315041b020714060403020108190204061701080c090103021c080301090f180b0c0a030f02 83
    0x3070200e252980d040f00c40341c0101c1380802850143c250902c201c50480f841c0050381800c0d03032035000800241070450b464510f29039881d04804004603000b8803806000740030020983d9642da0b0820b00749824400d005143c21103451194104110a40380e041c40035500920071a005040d126641c40181c400014401d003594103000344030100003040f501540180d18090051000540c16620381c070200065845c514014070b0035100d0b1007020023109001e0b40165402c003401200015107044a01c021500310760700b900c00c2e0040c074004280018640c9405000700005070a0420305645114901e10104103144503621000341000400b400041d003200f410441d0f0380010004180566555542e0000280740b1030b181d11900a0880249000084e030120000c1e02460000000d010112141e2a64003044400d0009070584c940b07042103000302c1713800034078260011070290203c0040090030a56101c01041150044224842a1205500e943c004644503001180d4000e28410740660ba41124900c102c01401c51404241540c81c00403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 691310800 1250 691309550 691309561
    0x100e1206041104060e04050a020d17070c0e01050409031704051c0801050f01050a0215060f0a0e040b1f4a0f070e01050304080405030a030f080f0c16020d0605 69
    0x50300c070070141c1d0b0000c40d41405941c0e1105501c090550068030005c085501003c4403038010309140262102883c0a10390003080211001894441030380520300495514801c00014800039020000d018003400040c1e608101d108815680604004a00d42179441e810360031500090802100300844c040c190b02c20303003c0312014001c16002600c1c44000380100d070312460b00e0921484072540301d101a901640c40c1c507801031030340c8001c14a02103085032000d0103158000b459116030040b07544481e00000001d15264100160901d8242004110700e100904208440c0802c3c450581d60700c0301000200c801c3c0c5003080c80b80e10b48107803044000e41c8a10040395040b10303200000102406441c08283c600c9400050750900e0301d140e550342007000020719504990303503004110203005031229541b007039000d90b5016100307803403183c60140c031140000d00c0d1145d110022130000750001e205010040c0c1c00440280c0044a1250b4003000d410450181d5482e401000b01c111810a1a0f044ac1c8041d03507242c92a52aa81f50064401c01150404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 691312050 1250 691310800 691310813
    0x90a0b0406080414060c0306060a0c05070803040911030603151f1d0f070f030b0f182d04060f0b10020102031512070e090a06020c0a020406090b100e120604 68
    0x203d4059a0416400028048003030340420000c0c81049688480751450341ea1604008060300049101000c00c1101d01040b40010401c01c604809000c841004580326890005040b09492078440c03003614480d0300b40140440364400285c980b41e16040b03c0c4041e01156901540e41135800d100e94945c22a00c140d0740c20000c1c0028100400b4042d0000060183c1c0981d62900b1490407400000e807000e10020744030070700700501d082c443e41c40040d699400800d4402440100c100007103038000e0255400c0c400115040a100090140160110300010407140c0a01c2c2500c40c4462842c1c0180c0080000e800c80fa00c410181a00344c1b016802595064001002c00700000d84000e8001d000f034204483d07001c03400c1c1c045691401e15140c412036062085071204002d094260500440705100c40c0c0140105840c0d10882401000260301400603100c0b44d80c40714000c00080c41c40b40100400d40c1c10b51340c403030b108840c07070001016215160581558003030740403401d0490b000c104800104883d0b002202502d0041c3c02818140401c0041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 691313300 1250 691312050 691312067
    0x81b0607080c0a200d0209010504051005090f07180e0f0606160f02090114030c120f0a050c090606030720030f0d05060909010b03070e15040e060405010e0105071202090a0b0406 77
    0x13103501c007200420418018454400011a40a5170125840004100300d00d4541c00c15903004a0a482c41203105613120045103030128190740002c40020000b0400808651109040c0303500c20b008221224558039010f902626400040c0801d0581e0b900840011003513210310044400c0342a006c610541001005d0920f00920071243c0000c07889803400000009001451a005201c84c0d440180905001d00c00601000003944110000c44481d00031040004940340090041c1440140180050504010700074100710030400700800d000d01c200f20900a1001d4944c1c8460144000410505500400d080920249280d800342d02c20601c0d0000d40002d0380343c004180c54100750301800003130740c0d031900b1904e4400c401401d0ba031000c40025010341c0405800c00401000240241d04042403501b080d0b4501040008035058070142a0000e60503800700092008000007407003000402c0c8a02002000542002c2d800204402c10044c4458162500450b01c281296030b0305003610300600c00d134641e1a40d41c0d591410301409090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 691314550 1250 691313300 691313333
    0x605100b0705011a01050a120b0a0f1d0105010206070c14120f18030a030519030e0601030b01080c010f090b1e0406020606030712020d0b220516081b0607080c0a 70
    0x40d82c41303440046500400944480340320544406007130380490b03820700f4020444040c00301d5000100c018005902c1090200000190800e001c61401c100b82e0610400000101a40028110343c8000100208580c3c00038051110660156901005601650030716190100d80150810481000a80820384032182c40051600304a07082c003104000b090b00b410541c4858900c080030700400c4c0700b0494885404031100c641e04281c1000d090018400c09d204070180d1803c4002d030000c0b547c0b4020f800050000e040c0c10040180c1c810b4091a0441d821a010100140b005070745124845a00c100460181d1051005c1c0030a43d850300d840259a54a880c0c1d40c2d20029500da40990301c1c01c0c0203000d18800800c40d030215070700f40c40145402070450f01e60038885641b1100d05140c01051444c255201003800c00f0300c00886200c2c5203080340204c00904400001d0308074034641e0410f541c0100341550115034010194120181c101000c4c03101150151744030b0032107040c4958544a074108100701801200010f00c1009a41c0702c00c032903400e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 691315800 1250 691314550 691314581
    0xf09011106090f251401091e03152d270b07090b0307080712050a09022b080d06030215130e070503060d140d0801090506010c0f0605100b070501 63
    0x555103050010300d03074130b104c0507010303021820214103210400350840756203000c1506151080042c1e540d5414040c0c0d56000d184854184400601c0400c107014151070811040c07200c4007800c01581c2c10f40c00d200ca000754001e1010fa8400412381051150500c00d1741c0c0b20751101146004081d0015104a260184d01c50784690215400f1841002040c41903104412010a5a0003100e07018a5511307046001e8813850f000501c28020064bd8150803001c58480f40039041c02410524008604000729104008502c60319500d03407082114015803032042c28034440d00180d030b015001804240d51351008040c03003000c1d01d01608081d410098000545810002180041c450244a40210112152182c40c2c0305135102c01074401c5800200144003087d0f0500c0c150001c031020070310400c13102a3b4a03003c0400c65041c90558800030000c40c0700e00d00104a0844503005148d4099024a0329020f09035050b42c0d17904020b464a0406014107540d400016841380e9201280c6001d442c800d65526202c000c41d01d410342c082c08400400001a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 691317050 1250 691315800 691315813
    0x303040c0b0a020d030b030319050903060c0f07021c0f0803160504120b0a090b100807090509030301030b0a09060f0207060b0a08030d0e0319030e06011a0f09011106090f 74
    0x4600c44000350340c18920b450380580748000c10484100c0142490701c032540d0345800104010704040d019000048007810040d111107846014203400c15050043c010b15094003140c04100c085148030071801203c0046604175441402e800c1c0c001003025020841340f40003003012548104c00307000c0c06118030245100c0e04070007a030310f4140d0401480488142c015071062104080c000042e03003001440042d00aa40452032480002d416a0389484c0e4264a100c01c0d2401003442c60821410b014222041c4000e41c0a01982d40051169051003400d856583c8414440517202d01d869002041144641d608a0040305030012001d200f1075808600110080d8091f0400304c07401403500e8006c40b41c90602244c2d03541161070050203141445042d02000e80544440402044140000c018000005c112054801c44210041e60001440d82d500c07400701d4606203040c1c0080780d0f459801e810464200c0350030411140c0810350700c1d0300a62100d030500c005903501007801d00c080090340125003c0140c54000012502c4445c01d18000300ca10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 691318300 1250 691317050 691317059
    0x5040f0906051e010c02030601060306080705191203090b03010608010501030f05190216171b0712020d02010908100b04060501090513021612030203040c0b040b090424080303040c 78
    0xc66890780b044640108004030b08010b10f0005140340114030030181420b0180d0700183d80000d041100c240c0110011944d10701040c800780100b0009440900b806540d440c2b900044003215561900240c800d200141401c810b0410406125003481c00083c400d40404503240d50315581c010342404801d002d11800070785006c07980480524035000c1c103802041c448220302c10314a24581110060341c01030301c0d900f40107640e85512100207003240407405030006506400719114400a000c902041401040d0302030554450300092112050a20380c0b5060698115000d4042d19014401654416040e601c40300c1d01d80140300f90319000040c2500402c000100445041103019190001541c0c0000300d070080c90340050b1070034042501d01c2c140c1d40c014040100e000542c1850800c9aa94034000a820000b4503800a6004800e0008210040f8009005000201c8915060a08204030b0302060b00440c7c1c0103610039519a01403900e09449100310341182c012100c840b07090180c940c030069503240d006440c129404441d40b200041d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 691319550 1250 691318300 691318319
    0xe01030b0106021b1f0e033003061c0c090c08090d080108120c010b040e0a050c0a030803041209080613020114091c11210f0d0207090e010207050a0305040f 68
    0x103959004002440d101042868110b00c0303417080180b002481030b841c18525250340c0401c43c10921108540c4489401014003861101a515510354080700070814400d00c0700a94400408121282e980103a10420a4240c2001c07603c10303000b0761000303010f40d01d007110b00454198010045486182c0c05003c850b0404241c0100b21120f0f4000d1041541540046115113a00c4903100700403c10104c40070008a05940c04c8400602241c409601000e8982d00c052458170070008180003024281d0400c5034800d225038030750713100c6051a02c00108010404044199289007041c02030016002405480007168502d24218100602404141505a0104a0840c41d1102a1225000f1140020000341c1240e04004c0403c01d064802480e0755012120420046400c07000c03a21454103407980802c03080211403000780d101440790300300181400840760a401903040031610315000a0303030000311442c89900150744a0000c55050084c05902d2000f492400340f854020305040d440b0024000385c07031b03013940715030782d242d43d9002c940 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 691320800 1250 691319550 691319593
    0xf27090c0604090c08061f0c0305090301060e1806010e010509041a0f01230a0902070228030b0105030f330c0403230c01050307050d02070f1e1505100e01030b010602 72
    0x44640141910301f007001c0900c14400428520b02c01c0c100503040c0202000040d09466003030704010501120340f01003000001103500352058810a100242845505181d84850030103014003034035003d488400b0104081004140c08210b940c84030111448084c00c0c06a040340c2100c0007032083d1407200000341151140303188007120b10381450000410000041d031078034000801130741040d8800c0e6407005050100300b040403403010782d001e40020761b0028002c0b000d00b50301c0c20501610701a0041802035106858045062038000751241e80118080095048103043d004020350310031100c045605501400c1c014041d4450f80c100252069a1003001403a242036000300d403003032420400000300c00d00b0340c0c0500260040741d406034006541140c100c2c03030401d1900b5258040f203c1682e210510494491200741d0701c2c0c60602c00c0d40c0c521821460080318407200540603d407a03d038008400721040f6401c80707aa800102d1000b8052030030301e50050022074840d50f210740c0c1d01d0a010081103c24480c0b00054001c250985003802c0d1000043d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 691322050 1250 691320800 691320829
    0x10c1406091006050f0f0102030c0f01200c0303040215040b1b060108190f0503120103050c090c0a0e090a0b2e05040302010518040b1e0f27090c0604090c0806 69
    0x101066030205d40104203001e4040385a00341903000800586842d03207000c1c0700500c0342601010000c110000766416805101c4400d286042814409111300b00d520500030044035009501100c503912801030100e8010f84038401d42d40841001032000504100001100c0c5180302a195203000740c48c1c107681e80d0f030102900c0b8105e04181d00910404915403000242d1180c3c4511207031402641140d00f440c048050007807135407031b0a030026540c990020703821003007900e0300d4410310f0ba1100e5140c44240c01c04100e03a4024000d2441d00780c0f1281300e0303900000051400c56955010303401c0010014481c2c1026680b500c903620fa4516032210020342020750b40281c4804a02800488044940c11317510703549003883e003240c42088442c0b108c400c00d510546a101d51b800a55524407007814520030b00c50355034000c011510410401c15100a501d600a40b00152803242410440400ca64421200b070602142c80d80c40503d6a41014460034071b16030312032400324020828100552000801e0349480d1101c20140e11400100080000d45094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 691323300 1250 691322050 691322059
    0x3170a05031b0904051015030b06043f1e11040237090603051e0403260a060e0609040221010204290a02030301090b010c140609100605 59
    0x10980b0b601a00d4000500d0040c0101c6490900e9141400034041d2441600d4051111200000511080f002415065030741c000e03a04080100c44016000f2802d00c0c001d03071007450515400a400f10080c0039841e10f000c07001c2d4003a4501e01c009025142103d04413500c0070b0109540c1c80d80c04500d910600c004000d4841d01180c0c0102840140000b00e408005c040d51100d812010416881d80011320103050f500462031003008594804110000c1c80b9000500c012100c0c5c1c0302004050500041c01862105290302180c8513640c41000100f40d40d540c182510180b6a12855102c03032192060f11804400c180980036002d2100ca400070322009a540740e85c01c4400e0700035078a440c0c0c040012004500180741c03550980c8032031222841400003040c0070740c4891b42260070540c0f0a4010300d506025118030b080c141307000c040c80740c2000400c440c213254044200940d64001401619080b6075942d011000903800ba5104005059004030203000314600b4100701d640755039090f01c1d20603403481003c15000c00300d0241e00465003914009403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 691324550 1250 691323300 691323307
    0x9010c090f060804150b060304060b01110705240405060f040602150c090f1f030603021206010e041506030204020c010207060b0103110d020318030c0f0d080114130e060106020703170a05 81
    0x80745c140350100b8207000300f07a1050b510b4a804044c0e40310840610f100c3c2e07016010001e0010303030340c40000d46040314110310040300e0741040409109640c1e50901200807440000c1031002049403000c6c0c68103062045401c4558010400302d541640000340d10024415601c01c0d41c2070b520a203458a00d60041c4010650700f0341b80700340b42400700f6581401d020700f0700485558010825044036004050042281070b1b1004450300003a101e20080c000d5081120141c01540740f4a801829150701d401480710b46490043e00080c00b081560100004060341c50304880301030754008004654403810000311034000e42c4090012641542441020541c0751301900c01d00044121080b8118602424203400200070351005200020400104607480c80340d0030100090aa141c20500c0101603040a1305201494154129052010010703210010f0100810301e0460110124007a10229076808240406901410781c1c0408064188074040c00000c909500042e2141128000c080e1042000281103100e0681c1c464024172401260080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 691325800 1250 691324550 691324553
    0x1005060c0a030e0f0d0c2322110a11070b090319060e0303190c020109080414010c1e0b0c21090309180115021209240706020712081302010f1709010c090f060804 70
    0x181850103030403848d4140011000d01008281d40039404c69524400025925407080700312110070011400909075000d0002e00346019200000c1e50313000c891f00f14128600b04840c4550400c0700c43d802c0007404c0701d800700c281c0fa204e10300705411002e43d0f54403841500c0194100209110307210300620138040b00903080344000e407800382040c0b884a03200f4800d002e000d0410440d8208130020440c03030b8000c003c1c1009043c140c100e44d6800d42c2040c02200002403e0b42d00c420301c08200c062036000000548543c0300e004bc139007a106903601c00c0d840d607086008003908540c0042c12916000c21a41c00d80e003125059480407034405001a220381022070b40c1c0c12401c64407017a428020400035616180141d01c001c600d081840d400c0901c2e030034460014510760402c050484e0f000e43c000c1048010401c11003807144001c0c42601d000300b00c500d800c01182c1c20300301041402134144500c0304408100da038403c1244000500c0340b480009001c0c10900c07402d40c000c092050862002829074400426071004841440044030195600d0030a1920f40703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 691327050 1250 691325800 691325839
    0x90402010f090b0c0c0f0a062109140c0316031a09070503030a051804091e1707031805030307050d051c0c081005060c0a030e0f0d0c23 59
    0x401d240102840070a41d0b0009507214440001c16500c1080c4e40584043c10f891011b00c00c00c04003220100c0e103d1500317000306000c899070041d580441203295042d50401700203c840e01c14000d281c1d050b405000000e2200c5201d070140c1c0c0001e08040c6030441039041300d40c80300902e40c0400741c5800701c0c0801425001d003800c20301c1c00401170510040e0040040c0095918a596840004c6c4c69640a0103025010070310100304003024804003140c902c00d05105860504c823400e903658824500080107035895400c114580f1552080c0091040702010764120703003074415604c2e109828080c00006864221358401402c074030001c100c604010040d06e07102a0300c107001385101c5010b088152555080482c22409940c00701e01021780358007550084107441030351a02c400c07059003041281034401e00b240d50000350069900308140b03901c5650009001980c540c2500d402c1c0d4005014600040004044282da240e100d9400c0041000340000110501c0803110071306504124510780e07282c0c952a9829600005501880c1e0704100c401c450388 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 691328300 1250 691327050 691327067
    0x3090a031805191e03020112020a021501081b041112040305070c090605030d0311040618090912080a050403020c060c1606030203010f0506040509010b0c0a0f0f030f030b09040201 78
    0x915001e2900041d48400220f41c498048031184504402c1c40d4004010301141006441d004556854074401124115000a4900300e6001104004254000b401e038007058828820002c0c150081400c044c4156511100c155031a0003c40c803214980160602100d91454644180c1c418040e20403000e505000c995a0601c22040c001802581801410480031000424071750158006d0802d5501c006402c5003072a06043c83c00d68080c4082c011700d0300e405121244140703860709130b40480d0654907004005031a0b02c80d1098020102e030f44100032031414044107000f0450b50348d2182d0340d010800e5660710740340c0c1e503612505030030b613a01034070b0140250700300001c03000c158184400180f145c02001d104494052030341c21101c405485982d03104a00103680480184142e440d80007501c3d000304000c03200c444c209800c107070001d486c90034103108080c8114800103c1000701e15090080d102c905400003d4504a0030700350401c04c62040c107903c4110300040c0c80f082c41c0343c1202e000b8030802c101c007040070f410b00302d203650b86a0054841d0b84 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 691329550 1250 691328300 691328327
    0x20105191d12040f060215012121080c030408090f0d0b04050610090905030306061315020a1a070c0f020402130609090c08220f020a1e050603090a03 65
    0x78204161002030040401070403105642c81c1880e99901c03031600c55505002d0034039801038000c640100b56450002096411224190342d04400d9022403040b0f52840e00710501c01d600c000400f41c064807011503902d0140c0316a000c2d11003249446d0300d1010355a510307100400348000c5030001d281e05d0050000d50384608000070340c03451218014200040c100c0d00782c2c880c90481e11048070110f80e01c0c0d00020030086910000c001a400402c051203082c403607090a641c42a80300d0000406590250002040c08040118070520f10f20042c03640c00c032120041002d40d0f100035100e482460055489c0a4076204a200c1ca00034210304510807840d658981001824a5442c122001507600003a6441502408010580f041201032503000b400756440350130b0a549401824426181c1170950b00341030140d000c007041100040310039410729030f10044040b0920382c056890146101882958044d4110020000c08980e01c0c070726001e50084005c1290582501d180e9803010014035210441d500c113203d4001034918400240036030452110344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 691330800 1250 691329550 691329581
    0x206070618140604030908010b0604090902130c120c051227160801050c041208071b0b03181f020f040e07050712030506060901050706021611010f02010519 68
    0x6200700d40315454030b140904075880e881e4000801344030405030404100c00040142d040284210680040000d0303840c0128414040410344610f004005c55542c82d14401c03d41d010450100085032030901c0041c00b40c00100d0b1980051352404a8900c0b8523030042080c1c4840c200c111100015079644d90a0401000f40035406200e8070540b02c45168060a2084c0142c60a03101c0740d00306480d503a4038214070503094800151034091440d008100c00e02c9240c00403400d0380c04680d0004038156648425180a5081440b160701524030a5407410003c200300100ba0f00443c014642c4450322540c05140d041c181d0780345c480710748030f141000070220764110340c00036660080d100201516603c41c1c2000d82d07540018520030012140c030400500009208401c01c2000655110202060716040080c2d02c3c002004c05c0e1640324104190f814001c000c00c08100300a12034048440c034642e000320203030310708809103069140b10038070002c040e000c14a9480105140c601c144102d500c540c0d0311034103038150203105541e03040081c420b803a00c08190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 691332050 1250 691330800 691330841
    0x2060a050a0e10030b0f041b05030603030c0703031d1905010e031005040b0a0e06100e100302180403110d0503061005040e0420040b0906130b120f061302060706 70
    0x1607511100384094600c2a500d01181c90444201003141c0300440e061b00507c11031038140240c03c1d50030310707a40340300051020341050781d500e0321a640060f18500509082d02e20601c01c07003001008156024180e070413100c582c3c1c1c005105400c452402c0002142c0010b00158154922103070801496100e5084440c0c600c6000d02030711a00c03080000d400f410b843c0112400e1311910a0b01c4107001c3c40184070310403a00e8150780c02000c0c1113181014081d080c00410071340700354a40100808042880e00100040b20070085500800c10703102c500a9580c00d80200b40104c07015804100720805040d450390780440c40c40300c0046569a50f602e1550741c1000c2000500603027031904100001880701085514041c600680210b00030000c0d62540c4034400742c00407044641a8041340600d081c0039030f0040079155800400d400110480f202c05400d0380c000c01c042d00506208102e95880070450310b030f002c1156001310384000800d50402c00c0d00e580f651140e080b5445a41c2040000790003080c03c01c0280c0104841381c0c0300800368610307881880701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 691333300 1250 691332050 691332077
    0x412020a1d0f0c13080610060215040303091505011514031513060801020c0304030c0501050712081305060c180901080d120b030703060c030c0806130903090806090f06011202060a050a 80
    0x40811307403500250070307a41c03289041c04803086a400d6810000c250b00d100130481c40310f0000d20380e140b44030040e01c01410b054a5000c0d510400240000d110f41e00066032500300802d603540d90440385500151042d09000c5402051060242454802101d1082c0350b0001c0c242d0b01d458014044c04047c000e40d086903100301d603443d00045221a001c3c0028a8405a03440040d503d1790308500700f4543c100c46661000303061100c1000824005180100308545584150030200d40659901c45140074590305640c00034210300841081100054020003e40940600980242c042d00c64050030312202c05020300503604c5650240e07031602c00c01445804030710741d210003c42c0c01203400081c84020a20b4901c140d04100c502c90b444203c0555015414891104d94040a04d010f010344d0070300c4404101915030409070712807482e03119110310f8280b6000e100c402000b8102c00f8116440c43c941107041c81d40b542002140800d141c015440001642c02010308050411900206020302d4203280a000762035513446091404144100f0500482 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 691334550 1250 691333300 691333327
    0x6010315030503180613270e070506090607060f0c1209080f07021906080f0f160e0a18020301053d14030406140916030b06010905060412020a1d0f0c 65
    0x2004205a902800c000c032400d15000c1088905136031020106803610605010b40f100025089c4210740003582c070035a45400e02c0300801d030188150710000d440d0505010480d100e816450b4400d425100c490703a80d20302ca681c0107000807000e80e0380d4038202400c211003c4c0086031003140d4520041c81c5e500e10041020a80d6020020305140c801420b80c00040412808030400504041444c01190b00109122150a080c50200d00e02c21403240c070000d0a00c1084403062800c2510703140c21944c50044d068101041102c0b04200e51b580c13000c0e6009000d210700419041a000302008a00c200c800d0b50b411300442d800d401390010f41d948030056007074034cc2d405041050103108040302d18980130007140114003030940417980700301c9841d0803400c0483c05040240d25610840c1e0701c2c41407885203041301080e00e5002c6001c121603152040104c0745840c4a80005134031200028002402d41c1c3d10503034804003035200703540080c0c28540c1d0703c1c410030112000c21781e0030002c00042400540c0c040421010140d10865041c542ca080c840c1040300c50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 691335800 1250 691334550 691334587
    0x30606091306261c030e1005060f030604030504091505040603030f09050f030d120e01020307050d0b0301022a1213030c0f030f030f1101090b060103150305031806 71
    0x164403641d40320028440007980c1c5035100d2614100d11a4200110201034105680c4c400444201c010f004448185507030007846500305201c9a0000c208440b4090038030002c6400408041d40c01c0d42c812800080d5050079420040f8032948629010346409090074580040140a050403000b9034800130b4815402040c1d1b03a40d907129039000345000740e640301c0425425510150200c001d0740c0102d4032030091001c10100980e4001040702c1c4540c0145071400264400180402c0500b90350b00204516500110410103400e0b40729000d05049540014184017592200f002d01d801c0b80300f030001b1a628140b036501c001d4603c0c882c0580001c0c0c0c0d0700b0044100e4005403804144030342c1c15080100c510041400381036007081440280081c030006000101d0308648075a286030784104400c400100c005043c0305203550883c00150181c0c0e2880f8600080740001d0004544600e004411039a044030190301207490b0411f4011416990084c02047c2e95000c00290314091000c4000085021140d1805030702000802043c0440c03050701044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 691337050 1250 691335800 691335829
    0x60b0a0507020f19090f0e010c050a020601062c0621061005030f181c0306090c0509030718061809140609060a090f0209040c0501030e030a0504030803060609 69
    0x890780c840752244108200141d2800d5824840c008211001a107055528400001c442083d40b002500c1c1c02d845c00104d000d0001e0383c040420f2540703031049210069400c14000c1804400d941c0c21b0b00c13410f03030703c801c02541d0f110460242c0c004d4102189004000c52071003080c81c0d043e1038600800c03160400c21044413101180c0e22403000d0514442c044414018542054602d003201803996081c0b090842c84c001205180b0044010621f030300401d503003040180c0c600018400d8150000d1024160902a0789040d809000340039641310345800c440c40d0200100145d441170050703a0726910300402030280c0c0c0e450308000008180070881c000c2001a030700c0320000340390700b46035004c3c2d45601c0c8213140c0070a07184081c0c20002c800000162403032013250060340c20040b20113070216006134854840200041d00c0c1019040034007a0940902d0002d401401031000d0006000c000c00514081320030981e401e100800441c071810b500e0740100044540803031001d11051000607041d9000d1580300c0c00140a160600b9811000245a007003690907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 691338300 1250 691337050 691337057
    0x23011a19090303030b030304121b0b0a020d0e04060e0a270302071403121611090a020c0115050d03231902011505060a12330f0b040e0406060b0a 63
    0x20410544c140c0105106114100d01a500f4240b8000040780d00b500903000045c008200340702c0618244d080480844054202e096a2545800e0500380103540c440c9010424404030381d2a8035801064070300f40c06240283c2e451800c1c410882d846941101024240d110b03174800e80030301c4a0060b002c4003a07900542d102c00038005c0c0d0081c20403500c0c05000c1d4940d09003a200c1107010790071980c64140c880c2482421644a83e0348109012843c41040c240700d09000c1c45621030a500070240c0d01403113001c0402d50013500c0e54685131002000305408907095244640340303900c80d0355000b842010b00f4401090180c143d55038a1040010301c078a2400d6a943c00c200c45622a000500d031000381020440402642403007a01c0c00036490850000070103060500194450050000c00c004001c1502c1101100c40c03090b80003d101d000301d85035950290030f0031304d142520080800c2c0e4089a062000706c40000c141e00e0002c1104204c481080f4180e00c2c060916000c0c0301d844038001d0040d82e04a40350301000501d04202c1740140414030f00340e603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 691339550 1250 691338300 691338317
    0x1e02070501030f0e073f121e030207050c0607060204081203060f0d020f130b1813020f0607120806131406040b12031c23011a19 56
    0x40016040b00d0f052440800098500125010b60300c0d40015000705544215900f041b251003004a600640d0b1940c03098440f0480032420a00344100241d0107440f00f961092050388980082110100e4070301040d49500b1729400c2400c00a0840d59000350f00070100d19008034191809850244042266544110001c6890544c000f80c10000c0140c14801c10180041010103d890340c00c229001032425104039210f6803181c204104104119940c2e03140c03460344c07110040c1c900612651160a04001030149210700ca001d0380c7c40003ca401422140c41e07a0038403038104900780e8a00201c1036001d00034110080d51040d90018410030443d004a02d4040b81f4030400c802e00d603201c000c0c9140440c140a031302c001c0303050055080c070f041917901c040315032091041c240e2003042640e001802002c01d400103802e0754a4030300200c1c92400000703041c507181e41c868821040e0362600b800050141e04401a0034620071280c80c1301c1000d2801c0040700500101c18440c2c038907012860354262007401e105083c044441800311403000c5802140004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 691340800 1250 691339550 691339559
    0x3240d0b060d0807120305070807020a060c030e010f06031202072d030b09070602160e0f0a020d24060804150903020312010620071401080a060e0c030a050109110405010f1e0207 77
    0x140031f031540c0240d00e481d01400341e0070050b00c040d680c1c196242c001408d40c2d4660f003c0c0d82c9a5803207a4083d91a903910007000340003c3c1004030803034004002a00003030b2100007654000a01d640d000040c480c0807281000c0c4600010354403190100c80295202001da4540d2004400000100d020f00c0d075850700038000180501130361868020068034003515030300d510703800c1c00d190306081085008074a280c5900102401e010384840d96040d02d1100284284d5200d11101450306024550782d5100040d00c4010314003c21074003c4907170700d0300d4054078507a504403002049032480c01644042d86202381c004c0369000c1c0c400d004480c00d2032004005200850400d80001300000c88004050a00341d0301c0c0040c0210140440c00684821414406654404072025003000e06005a1002041c1191900d900c00e42c020541d01350442700c10700b4a080341e0304a60740b098030010502c1e800c200002c86c1c0025540b2407c81ca00d1400c26440713280c00e01d030400549882104542400503c00c0303042d03003115540b5006001c46d910f00301981c040c0003081e040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 691342050 1250 691340800 691340807
    0x20f040b090a12150e011b0c02010e1f030e010b0d0201140918070f110d03180f08040620030a080c07062a0534050102040b03240d0b060d080712 63
    0x40001c44445c0781e05220f9107042d1086129011124090700b464041019181400182c5031030440301c0303a0320b070000001342075030407407001c144d1351400300c00810360341030200100c1401501d017038a9510200c581e110b0700140e4200010b40c0904100101e0441c542c60040c10000c0c6000001d520a00c0c1041190090307407101d08004245600401c1100110181d081c40b001c0304045005880d88ea440e0702c00d0b510705059a548200354402c01840c460f0100039408400a1050401850f1400c90307a0018811840820180e07840c1001070802c03a002000d41c1c201d500019401e0201300d130b108039190308020340003a008540400c280000b0540d00d000340340120703031068184610b0440c00b4000140205818003c4000c200c000e002a407401081a01e131700103007114031482d148400848a801c0e0f00b405858150040c06980b0000b400161580f03e075014500c11380030390f004540c114403034100c000d1021513040603541c3d21200c09409a0300040c0c2a032540c03a000040542558906280e6030340b8030704954407240007541c843e1100741c117009140c1da1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 691343300 1250 691342050 691342061
    0x4052209030c0606270e01020d11041403060c0304080904060302120a0203070b0702031209040e06010608100e15040e0708032205030f10020a020a0605010308091201020f040b090a1215 80
    0x425617a100c0a035880700c25400d41c00e8403102e0020403655268220381c001203000b5010b035007100d80a0384040044c2c0c02034008031596540148942c0981d4403a00c012100c06140201e10303a44141c1038140403902d191388903a200b01d83d81c0e10070354030281d20903900c40c400320151303c4001040b105c40c01560b0081c04402d0080c0101454079256901c0752921501c100300d80c50060314003042024001e41a80012629003134074000150140c8250501c100d541e20515000040b03150340b10080f0390007000103050395000305888403020080c3d19000c03945130f00806114200c41c00241480c1d80f14409941d1024260f800c415200c849050031580030018040961089220510010b5905406440140800c4000304000703c01d5402503030f2a20761088142c40b183d41d012502403100d034003d000c48066a44c0c454401c003c0707136031685490241c58000c840a103000b880160f120304000c0405208031086d140e100c006050410703141c0b2008458680c81500165001600d040b4001489184441d14080051084403160100303400c880d0050100c41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 691344550 1250 691343300 691343309
    0x20105192d08010e010b12040507030b0408210408030f040215040f18061d071202040b0d050a05040308060f01021f0902100503100303050c1527070b04052209030c0606 73
    0x4c1c0190010000310044d102290f028000c00100108030b5a207609041c2d080840c60391000d410124104208400c0102448c0100078008090506071100c2c00c00c0c0201c030f1011503044600400408042000c02ca85c850840a15544503100510700d048003020800e184100f80c100303a010b103400d50300003070042c050754581d03041040c003800192504124503860400d400c81c0c0c92045401000c110003202c008140010300c584500003051b41080703820345d522562507502c0c982c0360740129084a100c502c0e2001080440d80180541c5000e1601640c03518004d496002c00c0040d51001c0d29400c6056200b1504040104182e802c404140e10714403c10014100101c6d005201800c02e001c0c40030410010104204018950b201080d2029690146401a01c802d05200c26074900400d03100722030f40980021040040d00c0945001b41800c84006070000d00c0da110b0b11020b11790742c0783c5c40da000e41119400184010b01c124108007010400d008005010302240e16040070030f86040380c601100c10340004045d03c01d01d40034802d05010320390050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 691345800 1250 691344550 691344569
    0x80d11090d0602091f0c0c0e0405060105060a1107090501080d050a0206070c020406031410060b04051323010b04050901061b170903010c0c020f0607020105192d0801 72
    0x804900144102010141c0201865408103610009803280100e20b03426a928003a41305076440344070b10141011407620700455003180070200100e9140d015409403030003a98840c0080c0242d9003400e08000740c903000b040201c0f04103e00c8907040700c040d410401100c0010b01200800051035410100c0c46800d00c001041d50364240182004042c00081d4005442030b406156072030181200b0a641c40080c0140840e5440644000315001b0510036403040072036100c15240c5a20804c010b09030340c03815403c01500661003925402100a105415122016007010a82441e40e00021100040c82da01c000010301003130b0003004403210301140c18801d606001486030b002d07042905100c409111781c22070740e01341910101e200800c0d100c1510320015a4a4841080d940085002802803005c001001ca009120f21041c101c140d20a0b89000445002400c0100444141c1901030b9a01454100400d504002e00900c00c40300d0300c2000340c6091900c1d07150092100107540c0b58900000540c0a1210741c43c0149002e00603040801c65 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 691347050 1250 691345800 691345807
    0x40f0204230109031101090302180a0b040e25090203040503040311010e0d110307080f0c01140a140f040806010b0903010c030c2330010b0a1b0519080d11 67
    0x22a038109104104a07030344001007944640071700340100c4011341d490f0f00c02074000d40e60402a203400403003803a105c0c1c41500c0141040009a40400c10001582d2007501b040070250402518640e41e50000c099902080f070001d151401250761b51a00d010480e401242c0981e02500302107403d100300308103180e0354903c0d5002440c01001642c400e0000400030304404c80018520002c40040e0719050b00e0501424000f401400185da1586920300c056549038940500c0182c00901d40584902d01c4c0040801690703848101680e503c001101602b1f0043d00070b0380a0300c00541061800c4c400000c959000308107a9010700850340c1d03c00d40387d01402d4180740c20349282c2544c0505060508211035812a40803840060080300601660086041da000b22080c0b441141c0c00c0c0103440c1c41034a42e07032599042e40c50880f03002a5407001080941da9881c076006c84280102a40400010303000f0300480485041c400c0300510f9079015105403281120010600304078258003690484c7c1c0c0300c0e000301d220300040e40e00c0d10402c515400043c120918 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 691348300 1250 691347050 691347119
    0x1b1a030105090901090510050711010e0d0c0f0605010305033006280b03040c0b180402130506070b010306050a0b01080a150b0301290702030316020f040f0204 69
    0x54902050290900418600b000220071841c00d400549600d50440180c0f038651060102e1540a00760440300d0314089104d210680140d010140304030301d101c001400203400054440082201c9004020501345d80345451214480c02140d0f0034400d031030083d8803840003035640700da81004001c1200c845400c0100c910107500e8611440c4400180d0183d48108120380900e1300346004200b4241d107156010245a80801800001c6036041c40640203500490082c1844207070640c0d80c085da0400b82c03007510122010600d14040c00040d074146500602683c500144240e0b04c40d60301c031008103155802040081e1038203101100100203010f550b12602c0c1d04594210010b21582c81064001382130000080c018200c0c241d035940c8401c04110400d0514005001038104640d80d80d41d640d031410010481c4411125440c079003e1100b42c4021551701c08503000290701a01641c20164410b00325801602c641000340c0c0c11130582c0b506980980e8441c0301d61281c1b0300001100503155810540100704d600b4000e4641040403504010760300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 691349550 1250 691348300 691348349
    0x6180301061205190204020f040315050c280306090c020105040201091505180f0907020a0b130b010e0907050405070c060f09030e10110105040809100221251b 69
    0x325107058135065450840c849201090007031041c0710102c2128035001c0b4002c002c02402800d959058401502c1c14840d03a21000240790181c4a00c0540c49070100d40050640f03c410302081304c4507031408640c2400924540c0c1c0724041d1050301d41c0031100c0b90060f555201000215038002003141c0140c03a6070409412400078a03c1d024042d48601c000110f40010070400101240c0d43c1c0f460725442c0c2c84806000b140c61750074403040c047d6a40c0f860030700454500e0300e0080040c4040c8130b105460000140c101d85100c3e02e69107400c2840d80b00c844054208026801442c1c00450f29460b1030003154040c21103641d607030380e200929040c11000c9400d010140e418040c14042e040d00420b500c02d8194002d40320846024038406003100b0151043e15044050900c41e500309000c1109000828000c0c000807001910404408601000201d071203880551004c42c0e4081003030f00e0030001c131199402170a006200104903842070740c8064000c21400e0620310084541042195108041050030f0840c8001801c6644200504103201410030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 691350800 1250 691349550 691349563
    0x61201060f030507120f091728050d0b03010207140c03072102040209013605040b09070302090f030312010602010e0d020c06090112021303020307330e06180301061205 73
    0x4542e100d03180e03e201e54911003113611030707601a680040032943ca150f40301c0f28081c030750300102140c10b034801404003011107490103500079017401740275680c5580c50001d004031801d0081510b560102e41640d0700348030403c0000c0f40070303046894000102c0c00a00c818420314041618003c41600552516812030061058500700d00046440c80d542c1101d01680b11106000129a21020074172a07880b2600800209580c4960301c04042c1502100d501c0180032080c1c80f18288410703100507918085d0000c80c10000901020300c80c0c0e014042c0c2c50300040100ca6a844c0d8400003d2079178204d400619030f909410801006450340911074049000b0100000e050700d80d81e200c1000c1d441e0050300c00054007541d40019924403580c81403020781d17201308542a0442d12518003104481141b050382c04124000c1c801c0510101d190900c182d0b140c04c000350b40b2a141e2281d800d2a406292000400c00102030a000c9894101c240e0381d62808007070002d00704901d03410304000c8034003420103003074441552149c06c4070703240c402c2e5100200b8804141c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 691352050 1250 691350800 691350827
    0x102071d04081c09050d050c0604020d14010c0314090106120b0703110c1b150d0b1305070c050c0109050907050a090506160c2102010f0e061201060f030507 68
    0x400c01241d03140c2c28481894800ca480c1c200c05111280d14488403190a0341c0480b0351301e4010012580b03411482d00342503a00e84200724035400240d2103c00020014600303812843d035240e1180004015030003802951a0a4940003150540400c7c0c0300c8209001005c41e1444213540505d17501c1c0280501d0345000031580e16803040302c40c0900001e0341c100004503918020b811a142d4034003204201e564551703038030303850301e403240c000311000341400b403400a60607502e10380302d82052080b0302506641843c1c41c80c29826800103000001c810760f044000131490300010b10403840f6442c42000eaa480b43c5c07000a880b07190803402d00c0180c0e14042c0c1809031040081c44903845160440da4800054206540d446030001015551145a940899071103500028003511085980c5603801c03845224030381c09c49201e600c0b80c0c8805e42c001c3e4005040b85195000c000d09002661062040c0d410041d0903042075250480c1c0c02c00400d03c903038800c80503560300300b039264010032416621618903005040d8628041001e400c0040c1c0003041039044200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 691353300 1250 691352050 691352099
    0x30109080a050a020102091c060c02060708070c02030c03030f0430080c01091410060f1203140720090f0402030d181d07030501050a121e08030f010311010207 69
    0x2d903c42440d000354100e44615500a000c1200e18140003007407125480028400c40c3c01c1c5041c209140407050002402d54060240d6484028940ea22403000b21011010f05400380d03494030803020114002d03103080c0b0040400c0001d044440340e445003880c540002020400d0704628118960f20244100106814400030342d040c4d110724480c0c0d8070401c5004e0107014040c00f000107045405d40f110354203242c0400082d0310a0b0b13562403c20512146640e0030710740d40d80b55900e00c05c0040c0701000d09440c0000906c20a04120040c0c0480c002505090494075002030401001c4481110052010303801c0110346007440d409507110700c120b5043e00a0740303010360120b030f00e4202d964a070006100c01c0d1400f10030281c0c00d41d02880003400c029040d1510559510304286c5d01c02d00c00b500c00d0b1010a24220022800b810b0610b100c3c0160740c0c416400c20b020030120382e628010a0001e280000e0b1088104072840c0010304c1c50802507004000701c2d03100c44180d50442c00c1c04103400b181000410b065510222040096645901b64214402007121 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 691354550 1250 691353300 691353307
    0x10c1e020d0624150903151b0c031e2304081f18020a1415212d06040e071d1e180c0306010f090506030109080a05 50
    0x1001c101d400340030140040400382010302c01a400000c048000c000c9040710040050019503d10031003104482840008000680e05901400411000c3d81c100014000341040016803407090b2588080d104040c3c135510300001d0350110002d0074151f00920759100f900300035018400703180320408050841d000c00c0360300c003903d08410303940040b0b0303949041c0c103a900601c03610b004d44010f411f12401070407588048400342c0030401e1410916218030f15140c001d1480403540502080203080c140340c6040c01d000410f5003100d91282031000c1c1e164041082d0b40285c216104035001150003c01e450314645d50071300c4010012121071030903182007120318440004441d04451a88080481611000d000c036001e00480c0d26101d4082c458a0300014004420410181d01d540b8101424045500c07041403000c00b46144070641d824102c044004640801800141140c3d005003220440f002c5080403408603080c000c09a101c000c00d841c0a14007040201100d01035607502410031002003080d040d00d55a404514001e0b404400100040172 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 691355800 1250 691354550 691354553
    0x90911031f150c0213050103021809070b0a03061d0402060d090305040b0f0318030c060f06190324020c151305012f03040b010501110307080f070c05010c1e 68
    0x20400040503001d0700342c800345015221034001e821110340000480c052102c1d0300e092021400d241c40380f036060ba580100204285013102284e443d600308090320340c00c1640500000055400d21120013400b80e0403140c1c5000c104a881c2003101d000c031075082d03282d8a00743c20301d481c1008010b030b03540340c116441c50403004000118501036080440b4103004079080a450080002915000741400340003440c03145840b500a40541e9081c001051303202d018019080b040c9500003004034030b02000b501121544128050845482c104200e942c203040c0502650042c3d030340703402500309820143c204010030318801c1501c0b0020742c505070342e9110040e95624a10710f60860385002401198040c110f045910780d0143e000b4000317008c1080310a0441040c101c0d541540841c2181c5201380400042d09441546e01c038a41080c81480e19030703c1d00d00192004003110785041001d020401100c2d00007210480548140702e40750030b08507103d841b145412a00725507103130002c41c14001e910b07200c2d400040c8107010700301140081d59180c8210303500a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 691357050 1250 691355800 691355851
    0xb01080f010e0901020d051302091003030504051e1c020f0616110301150305070509060f130c031d0a021c0506071103090a08010b040b0a081504020604030b040506040309091103 77
    0x200d00b0071b00d907a2030500050050030400141100100c6000711040051619400140b10070344140707100040108031300744030421071407800680c4103e5500414a8520011200c6000038040e00420881524401046002e05041d401e00c6031158442e52029900c0750705c1d0503c4883d5240c000c820b50b010040403c10000c007054800d850070340041428503140b00c00c0044140d103910f0b0450311500e0a02800303001d94114000610341e403401294000164001901241c00c2c400e81100c0e020150500020100c2070540701d28880b84c2440040c25800c0c0300c44800c4001e8071046041e0710410290034080700208100c01d400c1000c00e004200081801a08020755080c18003000c0c800c0d550842c118054034428681c0200c0ca9600081c11804c1074220045908013203808004000000d000c014100d00c0e03d0081c0c40c01a40810405c0340d02c64030a5640c150071500081c00d00341099504d0392009142c25044600301d42c0c58004405010405410105201c05403546070002e00400b02040c001c1105404014800c00c04100241c0130225500d1f10b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 691358300 1250 691357050 691357057
    0x6062402012d14040f0506070801050d0b070e0909010f05011401271e210c05010f050d090303020c0f0105060915011112091908100b031e0606040b01080f010e090102 72
    0x14030f103028051525050a600c8102101400e031054051000000d040728403070380045041e514000c2c50400c0e11180f90701c406180e010001d02d00402d0109442003d040c2d6502c07011110300c1240d6000010507420f4001203028151903060b40101c4412030f00090084240e81c00151201101d40b050844c0d44000404e61410840303c1c80c0c5601004103a40148150725841896a0b45201510f02d1200c0104c0140810070240444036080c0388054400507802909020540c860b692035248011146480d41c10710380c29214200848a810b8000c034082580000e01c0e0780d5049040c030055007840301000c020002407401902050284800511345956030300c040c1c18030380f510307802583e055095510b6202190501c00001c6594142d0b03034000728201d0300c41d004620100820604c65500d1000b074034022409000c07440c3d800007003040a00f5801e05001e5041c02801c812600784ca48000c106c607a41d1900200502680c00c0400600040b120412061030411002004000301c1040040502c3e0440790354501c0700c8129a1a80440d074020700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 691359550 1250 691358300 691358321
    0x20a05060313140105010302040b100f0e060d020409050907050a18020d020c03070b09160b04090905010b030a05061902030103050d08091603150614030a060b01030906062402012d 78
    0x305081202443c1c50015806941664825101005003141e0001000103c0110641010005440c0c28041d0166446140d12050850003d8090390409204080300ca040c1e801a420145205a86a080103010f00040000000030601640c86403031280c00d082e9000000502007043c03003615070300000d060341e03200c501e9130441d224405c0b080184d0b905e50300c0a141c09154a0000ea5042109200318100202c2601c00800400100c400c1001540d281c2442d01d4a0940584850b040c00e8459550701c08101c03600751014001a804207104001501c61752510820b1859064486214020003a2051005100058001030080030300c030414200320800d952820200c1d072804041ca07030228450301e44910008100100ca801c40d0120402c0410244030030361300d0300c014a540780380a14185a0542c0190342810221303601d40d0045140c50418035020881044584420701a1902e070707440328080001000000a860760080c20145500800303200a0200303201011148000c094000004c000d0700c0201e07400e10b030159090340d0080b0081d0f03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 691360800 1250 691359550 691359563
    0xc1c03021908061815131a04110d1401090606030b010c03120b0604091a090405120c010e15182d010207020a08031201080a2f040509100e0a020a05060313 67
    0x9107001e02d28140070324603188001c1c1c0680b189158084112502d4000c7c9149031b041c0c442400170040340e040800000c1c00800340801d0b0012810002401d0718202c1d80119091940b00220021103075162200401c201e501c4c1d640000c08051030050541403603a40080050001505481d040c0b843c000725100480082002a080c103a21160002d80012034655039000a04901c1400b00860107284075941841040c000440d00107159403c00300251442e000c084024002c138124140000800b1a40b6106207403902d04c0290380502c0035547c13001000040200c808036491610000c01c041c065100070341c5221200b0a00034140c03c200300c0104a080ca00c10b036425815100c000350020003201c002d555840e0002d84981c00740000580c4200075200206400b00000303840c2d880154015021080d1061100c540e1406441c03042001c007500d91250180c1c4001d41d158000c06024000c218003416a11744050f500f441111170350401c41406812102c090809a95100c0300706084031016500e0646c1d80c1d640000d00c010031800014024500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 691362050 1250 691360800 691360849
    0x3020102210c01090318290a02030f0406020703020f03030a080705091804150501081209010f032a09140f0d050319080402090c0f0904090302120c1c0302190806 70
    0x34150b0118840311031a03c0444240041b0707460b40580c500c204400051005900c410303071008121206c030100101002c01c440d105032407c00b04050b11030201d580c0540c0c460001a03114030018420b61a16821104039408214010f5107015010300e009440450010403030014071038013040044058503040c8041e4003006020074404140e151500d4002d1070511840c1400100d1803500001151040b4000341c52614144a42c04040c20400e01c54011038801c8003403c01d084c209a140d21101c06822810114070b000012070024240c030141c0c0d5508000c100980c50b0b8424030900d030101038041c0d51911101c0e240024408142c500c02d10032503007424140d146100340a00c2ca10894411080703145803a50048189009510856541140e03880c1e00e41002094021500154801c80c810030214480c2e142c654840c2004074030900503669084881f00604245402160303801c00183c00007814140210450300d05c1621100440c20214145450306881c001c0300312401d000c4c039090041c0103010a907160f4604082285000045220100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 691363300 1250 691362050 691362053
    0x30302040e070507150203041718030c01030209010e060c0f030a0f090621020304020406080f03070c0e2a1306090501030f09021509010c02030318100903020102210c0109 74
    0x96206101d440c0610707116102281c011446842240d03400364100300d0620f0040000e0a5100003903101400c100c50307a100d980c240c01900c40f42103000d02030103001a508446c41c0d04219017814204a07800c610b0504040c81041440f10036030f042142c02e415080b040e02c0198407405490441d074038280248020580501c0040b070b001e11280e90180c400c007943c41950342c60349102e603518402039810141c02e5246080c00419007132841c0c481161540a503030701500003480400c40c99070318090103080002090100e10300e030f040020384105005004007024014003060403042414644240c0c10904020080c0c42400382ea21044c0901c60104010350950300449492307c03600c0004c0e0707900d41001d8005200780c80360f640400d007000b202101d424600e100c2d04007030f540c001d003406145a03c001600740c090741c011601d85062107000c01a20001d62001c1018142c400ca05108085100b03503103400300039030b20f4400c082c12030810810301030610043c1d07070104200b103510b0942171100080b41c0c281600202580141201d0880325860b1815510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 691364550 1250 691363300 691363307
    0x3180b01091d030a05030a05090109020a0f05150717090105120c0304031d0d020111100203010b0309010e0601120206090d050d0201091104020405060f0310050a230913021009050a0303 80
    0x40510800b02d5807001c41000d11040c0c240c490040c000200d022800500000d0041d001c550040d60b4003140100001a80300965400540d404815401003001c2c2b9003242818401820848030f80c0d104c40c0c0c40014070500b4114070391350f560003c4843c50780030903a41d032010031234041990090301506d10a10200e5500800e43c035013907035031420716007040714103074001540c02822881010000501c4c1c004070001511300d1110a00c580c006440031032241c40003188610940d940c46070680c0d41d03840510b000e06080d0042c60345d0703828441c0d10725095480d290541e200c182c00c810010058120b0b001440e03a04d040c0d05507142034a400701d41000880080600c10040c0c440d00404528406259042d48074045042c442c2c80b196402c0300b2100103001c120701803401081d07000f8400700724803082900c03514083d60b80f0284e5000056179503500c880204081c068207910000030b20401154451072580401002c1020380f4040d984044a4544098010b440381c10420300a0b00600c4016052060760388503041100c09040b02402c1d8081d619928a8000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 691365800 1250 691364550 691364561
    0xa08071502061305151018020702030d0302090603010909081b0609010501094d1213030905040209041b0507030206010807030221010204150e01080a06030b0703180b0109 74
    0x400140101c0b00060364000c0d0182416000301e030003900401444e20440714403a03442001a005201c0e200da08440042c0b02d100030740d01c0280710b5844080240c1c0360070301c0c0c1c4140f52a00d8450241d05003494014455400e481c0c6485045c1d80c11a8408480818105420b0500c14428826400c512445041d056030440002000140081c0112030f0328008120507aa01c8151500321040107441c0b98a2022003801900d620000c244210a07000000340d455507410042003040f2220250070890902c2c5140200320a04294000e668066110800802001e034519031540d004144928070702800f031155070b001c1400c215540719030b0300c24180010301c4044600c03101ca000d207014100c6d07000504114014030904001184401d0042207160480354050710341109000d03c0090102d840034980448d08442d1350a00c000074451000d0040414210907a44901c00d040c0c00880c001000d048005100a4080703080400800004036034100072580200360340341c0002d2010072041540981c1400403030140c07140300404000700300890940e218 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 691366906 1106 691365800 691365839
    0x1f080115120c1e030c020c0d081909050301230402040b0d0c030605010e0a0e0c0405090309060301090b03190807120c02030307030801062007140a0807 66
    0x1104854034079048500181e05103103c4801188605003050349190645014414203040394800395440d040c8820040c00351194144031000d016131042075800450000c0090340d4000c81050780200100117030f00030103109500e40240d000000c406164040c0c1c064140d003841052594507130302000000d040c0d1a00300e6030090015a0441300203601842d6040c02b541c811500045c01d541840200e505200b80106602c61162411440c880880800100c814451004a070082401c0c1d6070f01081c60f00314000c44000e55000b04004c000400c0700c4180d500681404202a42116100c80c104200003032900b40c01003010b410904100014800320302484040306c90201207061412001c0059404249140e001d8003040e00000c500c000140801540407280700d441221713212000203070400c0c010000e601d0381980d01c10060452402d5039981d9407522216104001403c1c0102900ea8003541c0b0302d002a11840c0c007844 = true := by decide +kernel

theorem cover : BRFrame.Cov 691187050 691366906 := by
  have h0 := BRFrame.cov_init 691187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 691187050 ≤ n) (h2 : n < 691366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
