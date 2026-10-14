-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3650
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:17:11.215245+00:00
-- url     : https://prove2.me/submissions/fff98553-a8ae-430d-a942-a6d368a305cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 656294964 ≤ n < 656474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 656296214 1250 656294964 656294987
    0x9031504061515031d06181606030213170a0201031a090a0c03180c0620160e060411040e0604090807051c09151404090609020c010b09060a1a09060307 66
    0x4a0420402c1700710001c4400310034010519800d241d00c100d0109407139080124842c503544000c00d050f00c1402010280413a000031071984030200007a0082103100405c00981c003205c0007056403450504404c520050004e0b2581040c00c40a418556101d40005103103013401c410b01d400f01c1005200560307030701e04a02d180c401040300d10100000285005a0984440a5100d078164095080003030800610b242081c121b8271100340d08504800c010a03280b0203e03810302d0400208100280007500315900900703103030001000200082801d407195040950444a815004040f182500c1c64640c0540711b03541c480010034003814034118010020b46000600c0428003a021601d103000e048603d0450803c03c041c10b20071030300d2944500824002180d40f50300841454000c2d060090840504550642490759620405048072480c2e880b126035141c0005140350312003002e1081019625080702c00d003042d400d00b00c0c0803c1100401d40500e41a241c0404040000704030303941c040d1603005c0801007016990f0314180800500020825 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 656297464 1250 656296214 656296217
    0x1b030201090c0e010f0902070c051503040219060f0507020a030203121b031c15030803161b0503090d050a1b03060b0301090b071b05070303050a080106020309031504061515 75
    0x180c1c086402c2c2c0455000c04d040740c20602d200c0d203180342400c8104c4001e42c003208013268031a162143c0001c558a40082000d8901050800d40303440c1e00c0c050061004c031b1300340c000d100750001611a0090104640007110741c1144002860800d48840b050310119402d249550806541841100c0c00000e036030403070304010012051180100d0030a4214190420303030b81e009010b0004041520b1b010400000b00880d40f02860068440d084a9207841c0e076500c1d411410b40c01500e66900c10300030111010003683e040b1104171100c81d12880e0040e141d01850b02c42a4030380c001c2903003582c03081010850304400d0020070001404019000b100c0d0399109030302141c03021465107840c0300407a4901e041c40c090801910b0184119881d09404c5050861941d44400c0111007452a1140550510309041a5880440c20401c0100041c41c0320340c072110b542d82c01040c0060040b00b0305034008070846d032041003040d2003503c002c02e040080240107052540c09071a1440d00034090001c5418000d03003503542701c20004034040703078420240410916 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 656298714 1250 656297464 656297483
    0xf06010815091005060612010b09010e0a050d060507020f0f03090906030d0905040c03091502071e172b0501090513020a26060103050c0a17100504031b03020109 70
    0x2480c007819032810450380700d10b80741c00443c644510303010141c00981d0f000c0340c0205518a062410b8a0265103041c080c0c010346002907001c1034506140d6040107030003046460031258151003500c1c04002961440749120f0081840e9290302c00308031010700030407103880302c0c1c1d08400c142c8018040080000b5500d070803003280148076034054408111107040c0032610b400c0d000c0150351020151810182444081d0203400802010150703117042020204110340345110b1007001104000da41c03071101d41031800100217214414005849030340b00d58000204d0030036062503620901200c07180c480c528100001340440038207240182a41d0090302c0d4040844131a88102e042e65040081000740d030301d4100c40001c90349072140b00250000000c50040c030041602c44c60702e59018040182c101000e8012208903818034100780d108860701c1c1e1000800c500c291a041c5a9a006003010f070740b0180d041d44c54400c15607907410124000c0e440596980b400b003400d051045031207815100880703c0c9840701c41c04a1400130700030011050141c1d4980e42 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 656299964 1250 656298714 656298733
    0x140f06010609060813031e0917190318031205030a060f06020706080903090a030c0905160905010f110327100c0213020c0a030c05150906010b0901110f060108 69
    0x80d030700c2c40c400d40f490780e52501c40994452041030007030310200c14181c0074401d916007004094404e000344001e04425a5176121301c202e00d801c05414950004034440c0c18150000e45022080c0900031500c00511500b504e03010455000a803181c0c0d00c02e865640018041c0145241070140d01034100005501031841d504007000354550325a804011881c0c1400341d4801600260f40030040326104410f071036009003d9105172403505082130005001d21049500450343e00032036a0003042030320400e10a25500494422001c9600b0304102d50040500c10301340a0303107042c02490102d802c010340c0318a800f1680d1f155002c003203950f60401c0049000e2070040900d840e08440745010f0802d42e240c180164112030a415039100d52100348540c1c1d081144002e4140d020141495013808030b0344942a04106001c2c4d15070081d125803103042d080b802c0c243d0810340510301400256140c4e50600c14003401c00103455046621b090011038031140e820f0012205101010241080e5114071851000c8000000ca1040c0c100ca84a0048800a08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 656301214 1250 656299964 656299967
    0x30a0609020913030207230d030c0c06030b22020c0d0917030903101e02041418090a061e02030115090602060c030708040f051c031d03070f0201020109140f060106 71
    0x180031000084c01030b000030f40108500b11200040c200d4013071070865184501400071000c10007140d18241c007a0300107014102400c00f808025620703480600300da071a0920030090000b01040c240440040302e40d1640b0401e003450702000b8101c0d81603401564002c01075458810040c100144a2042170144c40d485080400c803c00d01650000101c4884480140140c504000d02c01d00d0003004145c0d9004c0400f1821042030407c1642500c0d10003170010300020024010310307110980a102002070600c8040402c0f814001c244411003e00090310200e1781e0b070004000c0f4024060a417500c1c1c596002e071314034000c0203001000206294040350f42c41100d000d4250b803003010043d9146802c82e41d9140580d4103125240040000c1400340c0c0c03281460359403140c0100740320042092165241845c002420501c2412100c012007d0310101d0760501907200804e808540da000c009945000e1942c407407190100042c504600314502c141164001e4010081d41d40d008605240d5001c07040c2c014603140c48100841821502402e000400d640707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 656302464 1250 656301214 656301241
    0x260a14071d04020607262a1f02130308090306070c02060409151205011505040608100902040f051008060f07090303050d110f04090e0601030f0803040f02030a06090209 73
    0x8809841d00d09489488a8090195951113404140c84c04e21600500010302c003140e2149040c20544c1c06001ca581e03145007460080c0d4454001c2d0300703c2d00420108084600600009000703503442c00425540203c2c0403040b14910024410a08926031450310500000144283d002c080c1c010b03190103a0a441c00b564501c10704030f075000b41d21381c8029030010f02170201380640a555401902c1d141050b02034084212f072903001d2031513140c90074101110b80c0d0f9100d81815480001144400c2c0050200741e50a00c440e500341102c2545401411a40d040455910713507500c0299680d507002902001c0e50300c1001c200506242c3c205c2e46001c01c1d14042d1084900c2880045859000c941102c03e200341c02c581e0f0358599060940c1c5d0b044407a81d1002c0410709410f5190710141c040303000c4440003031580018422200748d99603e4500742c4002d550007c8200d8045030002c00041001c1402c1c4c0c0c14090b2010f600148003a6642d031075140144a04404c2d50020b9058418140d401e010005103070700118106000f00c980c103e09680704c6040c400c1d038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 656303714 1250 656302464 656302499
    0x519060210140f041e060f1505030d230c01061d150108040204020c061f060804050c0607080c01060605071106090a0603020d093f09260a1407 62
    0x3602c0c2c0d10000d103a15464180c0709400c203200b0a03000712644000084800c0302c007a00b0f0b0090b031311340e6130b20051003290410b81d11901c5000700d0128500c0072454680400651100641081c00e0140103140442001c1c00c0c8081286118900b4506003039501c420805c0c000700c0c000e06d0680944564070161511075103003a008418684c1c41024003e540c40e01d10030128004461190000d8000c9801036003e101c15003020707d0074410940710b10300701e82252065100a01310750031107e40540c401414843d4000a1002203000400c0d00001d101068924640d03030310361458018854468084d40302025441c0c240c000c203119600c20000d0410070700072400c40003680c05010030070900f441003842c550343c45103812200300031890103034001d4074ad0036490403030010b01c0b445661128048103c90240c1034240c0720808112401d20305918003007045058194420074112002d11002034040f000307502070b00401e036000190741c4c8242504100e000d0400301e03510b4150340460710316203000712030f0481a281088980c003c0c1c2802058040321610f48040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 656304964 1250 656303714 656303741
    0x5010b03101206090602031f062c06090d08130b0906030f07030b0406080717070e1816080307030e0118050103090606170d03050a061412070519060210 66
    0x4031a49040c0e0210950001120103c4081d6118645100440c0141c409036200d2188503c1c210300c2141e1180c2c11b01c1040703080d0740103482403014502c0c10601005031555090314161442d881030043e03918040008680b4010816400da2011500c4403010070080050b0141c40c807e48841c082410312a160b0201428074069926407a0700010107000140d40c041141c240c040e00025103040000d802c0e059000420192007031a00840b55946c080d020400000e040030500c0d140ea142e0400c0a0000c1e5420700300b00030421400030b004503200201119000030740722014441c1c81035010780794002215007a81c0307603015a101c0e0098901034000c80c0305803c3d02c1c8010350180c01d1a2100c0c7d44203044d5481e400d42040015002441c1381902a19240c2d540c450101b8031141598042e801890304600030320340c1c000c00b0070004040d61070003000b118515041079003c02065200c10120841c508003166800004000101c44914101c0241c0c043e651041442080d140e0114016034454140c4185900f528401d514040a69046d9000044130742c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 656306214 1250 656304964 656304991
    0xc01080601180e190e24130803180d0c0201021e06070c031107030308191a010c0602040f2709021f030207061d0f060609070e18010e06090112050c0609010c020a0312020105010b03 78
    0x8442c94011684220ae03401661035028040c00e5092400304d2300c0e1103ca0210302c0d4072112500750341e010400c40d1111061006405461005509146e0319201c1c083e0005040c003021084220401d40500c400cd001190031100302c91445a4a05008010b00310951340036a5000c0706850b1000d03084c90314040e00031507041c00d0480490585c03645004440d4082800c0060b44c4566080c8004222001a01e40d01c90003048408656024040490420741103403980703190201c115443c1008010058a80039115118864000d5089038a211044d1040d00a4421044002c2c42d607813a0078040010345d400750740040d80458040302103c1004281c18034035507880c03105071011503000b81d0702000038031885e00c03640c6003108200d4003a050b06020209112660000340c001c1c0c04c0381005094100c20020f46003002c4035801c0c0100040d1605e00040c0c1c005032207141d1103544030b400f0705000320000101840b150f4068800c0006541d4007400304031f0410394034100142054035200581b00103500303140c00060492403400540c1d0261400c1d0b15003e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 656307464 1250 656306214 656306251
    0x15090c020c031c0908060f060906010203160f021816080c0909041214030108010603050c0418110a0503190c05040501061b051c020c01080601180e190e24 67
    0x2220f420321801c10104011400e080414004428000340b80245c001c0c1e412100b5606050301040601c07000144143d045500512440c645811110380015803281c1045560380103030b1460021030a81f03504400030350304600d0303400f05001040040020407800484165a55406070b280d041c850241c610800801c0c6520460a0000c00c0200c1c1198150120049090400d0003140f500a1070185894000741c0c400b00b2503964440007001440000c0c030070203550400c111010000c0c5040e0b07280710707003080303003119006885180c4041c111492610350100200203040000d007115298190805000b00c2c803e4504000c49540c40104400079041c1821b020712810385034144c40f2219410400a40c001042d2512223044c4c80b0351040364001849003003082c51103000030382103030301404000c0e06010000d007811501409190401107000e15080c041c0300784000b06d005480c5519002010798a6603000c15112082c03e020701000c03945850740c59015039000050785d4508030300021032034600000d482d60401d2000c60444107a5441950003042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 656308714 1250 656307464 656307493
    0x9100302032509081005072a020604090b040b06030f010e070e09010b0910090503100c09090507051308010908030c0c0a0f0606060318050307170d15090c020c03 70
    0x7455224902c44440840e01640300041500901c92860b51404a100040244115103092226402140c110503040c046070800810040450740117400b6684900342d141070040b86000c40900303490089070010091520f1b079445990210003011301c4001244101e2600001c01000d04000c01620700c100d400c0788071049160b191042e0764035400380040510081103000320360707007050740d030740e15a05030282985105047d12801400e0a210714155400d04035800e00507001402c011175600003406260100003600701040f031142543e81510380d21010b8100c01200f40c00c00d420442c0b8141e0040c098a240e15015400c0a8050341d0744255500700e40c448400600300c8a0100001141c2000c5c1d00010100391807281c048810790302c4942c0750141041c4112204a07822501c40d2410820107616005000300407240d2009000d0042d81a6980313907a910a0b0107000b071036048003482c14545c000c042c0d02070380c1c1f0b0805180e100b803090030034096500069000078015055140c0c0b40100343d9060700d100150415069102500520240034078504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 656309964 1250 656308714 656308717
    0x7030c06051c0203090304060e0d020a03030e12030f0d14040f031b050a03030504030f1805090c1e0903060c040617270a110d02100f020120070209070509100302 70
    0x241800b19149010740700400a4503803005520a411400c05161610300f0010000d0104152a58142c405e5010442b0080507a1310754140c0c20459515040c090744c0c844005000c44d040b0b0100c009a81032074000403500c1004916000d004041c08004e0607400c11198410a02e402e031080020340d4058507071841c5c10910300000c0d000b070810380352410486584585a00b007030768a16141000c1580c04500080d162000c0c00300701500120302624140d80360030403c40c820111401070146180d0f901c112071180b051203000c07414507480b03081240c4900510700b200d08030081000020950710f9005861081c00b0340b00b802c000500c0f2003a01070036102034640c203a4400c1915100da0051100c012006820010220b030b48002d04060100c000e240c3c480d802c107241020740000403172070800c03441250307440c0500e030f0140340c0c1c0c1d052200059403090b43d080042403942c1400c18040c041040d00300d0041c00210303595640390b4031807401040c0d1059200c0c040c1100c580300b01c0319200c2c0c40e6100081240c0c5130207036a00700d0740c010a003d0b000145560080c1c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 656311214 1250 656309964 656309977
    0x90302121c0e030d05180a031803050f06090f0102040e06061e0a03060906170a030c03091e03110102010903050d09020102030706020f030f0702010504021c020f0d060605040e07030c0605 81
    0x10400201070a10780c014404503080040224416440001c2c6510111518055150301100010103890680702c01b922113500e0300e50020b0001c0c200700003071001c07014581c41500e244000d1600841120102044030003550340c1c52000380c4250b5030500c41c5e03082180d500b00c014002c95007514070b0800780c189140c80e240b05000041d0001d19400710131a10641128078941a40c1c000307090680380a81d07000c540c09150282c50b408603503840e0041001411864140201d500700080c852501c10b078149020441011582021100d00c0c4098022240e15800720103c806494050035409084d240600c29114291044c18016422114921002008510b0500c103021035100c0030743c0402501c1e8018010780740750010503a6210100d80c050a00d82c45d55150100500c8007401d0b4040d401980002140001c002904040e00042e602c0c80003002000960440c01c1c90640840d141d081c46600e060b100501b040010401601e8070102404450150a015518110030403610100020352071b81100e40040da1210f030103042c88800c03145170307102c0e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 656312464 1250 656311214 656311237
    0x11101020d050703061503020c070b070503070506070315060806030a26041e060906080f0a1d060103050c0114030121080c1506010302071112010b030a0b0f070309030212 74
    0x203000c140c0070014140500b40c0f02e4a141d44d030009880c0d00303041804e4400c03c01c1c001441c007018030601041441045c0000d042c0306944550401c03a8880c100f03131901a241d480791040c000d12600900701400005174142c0c10000c0010713555501d2401c20394450718111a80003003298042c3c1e1652100411101151950040c0c842e01031070720070074445200620001404075801940304081200c4485042003000030042d00540160145240c02c15119142160080107940043c140d11022a40740010826256803640b210141c1c1d480350601d0350360010f05207040340d200c6000344000c0e03c15028170366421141e5803140082c0c3c008480b116103070b00e0035a4240160146400b40007250800d50b41c02107010400812203480103088034044010041641d200e00c03a40440a0304005040f0606240c014003074440000d40c80741002c83d400c642074945200309010703c081580545105650f280d0103001d1a40c9800c1880001c95a0500c1101400384015080c3c03101c0034110102e4501920280c01600b00702c81d122442240c090040151443c0d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 656313714 1250 656312464 656312467
    0x9030c090c0234030b09071d010626010303031e020f0a0513031a040c09020a140a0e04181703040f1704053a05030306130f06030309080616020a0201110102 68
    0x8243d182c003010b803519001900c0e400700c4001000103440d010810138005c0c3c4880c0031619043d58100c81e03c1d0320071540c1030003240184800400b81c64801c020b60104150240340c00d00303460b44c042d40d42e8103003c2c00900b00d40f03200410103500d1423441401c00549008507100c00701e10002452030000441011600c1c0d81200a42c802c841c41079a400101055011402c3c02c4071030002c0241000a0030540b400c06640107003940b040700c10b680140f0040c1c0301542c01c1ba407030000c0d20490020080c1d68800c0524100c0d05a440391440301d80c4140b0f031030b81800076001810440b0030124802c0032108003112490712a0351207404115402030501301c1010f200320014003840500205600e010807554105030303c92000030a00c103c0038581031203c0460300c94100c0c81c22108000c14110780f10254034481c1005143c2c881c05c0c2ca0780310090007036014034402035502d04c94500c283d0105005500301c141c00c00500d916854020300001d41440b440889201c1c02c40420701d611050b141600390400150020302d0552079940c01912541035079041c400c41950f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 656314964 1250 656313714 656313793
    0x3090f0d020303030c130806060603010510120c050c1203220218041b1e0e06010908010207050c010f080f130602091305060a06111e070506040609030c090c02 69
    0x1000c201450180761403180e016125404d9000c06e0180b10000d0b8400301260b40050240000c2c1d4070350108507810f5070b2040e50202c403007100c0c00005991210f07010141d110054544240d500300f0640c0100a001503d0312007003031f21020312030724150080e20300040c2c070981d120071043c000c00728041541148007100b00d440640b8180318095040804a41020f04490039140c0c0031544c2c00c41c10600401d0540640584251010260203a045e000c920888281c1030041242c0b0300c020348003040c0140e000d11942c0c0d0052810340d0096640b240301d4940300d52107150381c000d007d011618100d0300c48516401007128621070545205080c0080d580c2101c00c80b03542440c404d081d20b040381e003040002c0361034a032075407142d49880e1800c03000b20705420f0407000c1c82100c1d2450751100c000c00450031400406002c01107040004180c0c101845803004c054810b409080502c01d41c000b42e80204001800150580c01100705030840b4019902a10856618180c000070f5641c0e009610005070071800060b00c244102c0c41c00240c1070030075505a41d05101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 656316214 1250 656314964 656314969
    0x40e01030204091a2503062403060b030c090307061b06090c0b040f0f05041b0309020a03210f050a090e06030c040504050f071a120a060503010614030f0a050d050a12050106050403060e060903090f0d02 87
    0xa0090b4de0b02034071003900180c1d0300340320705042020b5402452146807100076100701041400b00d604a02030005c03d42d039200e207406d80070700014031310a0018180c500d04a650302c1c0e640301078507070055107984078204ca601c0342100d001415103410302c07956140c0c1000907184050302400c06400c90080110000480e40010000e83c0407020034508141d000401200003d0390400021501c40980072044c0c54a000080200c1001a90700c0c00e9030104030708044504001e41c1c0c503d592103000010b42800760034202039412620300010003050080019000301800360300740a599145407103114400b0040118039954032043c0d01005039a400180301c0510700e42c003030344ca07a0002811580342d42c0040d00f518440e5010400351702000364400340724a41801000300205860006040a01d01c940e41e00c0d8844807240c1056040c0310340420000c08a5004002d0090710501c0003008100642c0c440c034010b4420b0b001400151049864080c0c6840780920026407a40280003410040d81802038040405ca0a0900843c02c1500181d200d40d1034401078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 656317464 1250 656316214 656316217
    0x70201210c090915031e0201020102090603090a0c0f032001021609051e2a070f060507080c0a020c151605150c040e01030204091a2503062403060b 64
    0x350381c0d40d118508240341a1040c03055402c0e6480015610301c1e60382d001c000007805180d075020320301242c8107180c50181c014001130f402400b40004c49600458000304100365420049071000a0314450345002e180036480741c286e41c0300d1290b10f000043c120b00304003840c09900040c071a03104885040500c1202c4020740c00020301074040d256507009a4149480e0b5051000201181e10302041d0441c1c2c41c080340305c1c10302d4806611384410115040240755034550307503504250205450301f224905500f100d48500503200c9898880c0c002c040803030b41c6100140081d4042003c0103101003ca030b40c070171460f40c000d00039418084204080c01c150b02142485855081110b030b03c00e1050342c031100c503002d4081d1002e8150750040340764040c00480014a2000441d00c10401409140c031800b210038196501964000342140261405206900d030343d0b140c4100100c0c216041022a080c0c4600042c0c58201160208040803005841601030f10140e0140c1c200b48030701d118a46030441c042c8100e0125001461a011401ca590b58400c414039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 656318714 1250 656317464 656317481
    0x6060b07050d1d1e03070f032405190e07080d030501080115050306010e04030c1a0711070f03030c020a030b13030311041a1b03041403012007020121 65
    0x110341108040403241500400c500c2d041c05050010003102050107000260f2046070300c45201281c0c1c90030004d21680c3d0328200614009444464028950186c590401c01c070301141d980c80302c20002080042031516134226000700e5020b12a8100000940b89450a000001d000307000c0d0b031044d00b44250b00000802c85420030404c00007072115140090715505181015095619135440c02d498094081c5003040140c03000110941140c200981c106a60b46030361804903140019050083d0103111440c80700c81c2d01c1055804103034019041c5071541c40159201803030054903545c0030710401c034031052410700401c080390042c50414082c0d40700500642400d5200d980788422040c090f01c28209580984d0840403c0540603c81c11005030020110300b42458580140050032030401004421219800f02e40c8101c031442070044106c0349c050900c29240c0303840d02c0d030602c00011400000464402e60074a00d120308c564a100c0100304a14000481d00340c60400203400558031100c181030b51180b01d01004084000b40c900380d210316844c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 656319964 1250 656318714 656318723
    0x4090609061d16030201020a1401180c0e0a11040b070609020612010503100e030f09010e0a030302010b2106010e1806070f0914030a110a031707050f151306060b07 71
    0x2c9441164540900c0d180c042060918400103039401030000d40e80004840300c1c160742c404960640e1440003c0701501602100c010040c5600590030b803030341004070400c5003805650340b01c040d00c1d0465841e0003140d0142c0341d41c8508841c1409040000348206000840140b030110301402021540f40e113681d01050b0302d40d224014201014102000500581c2780a01031304010642415060200a00103500d89440b4071400422440c4c0300300004503420300764080d02d044010940c0c01002c500c0016a03038140640039000310382e41184662000c00d0282c461851504504480743d491100600c1545e09050100c10750180262141c0b001c1c0e40c81000010442c082044450700c907003182c0e40e0301e903c1000e00f0394014041a055401040140d1030301c200e14001030711b0000d50f0a07400e039044009690b400901501081000d1440d0700090b01da034080c1100040800c28040003045081e00c541c085030f0000030020340468403840c2c105e0105c600a030780b600101d1001c0d00701010086082d0302503e800290356940c0c215101e81030b441504101c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 656321214 1250 656319964 656320001
    0x24010e0618150f03130312230105030102070f0611040f03111f02060601080c0d0e03340f0203010f0c0806010e011e08090c09040807050f0c0904020409060906 69
    0x41c0309007012640411840000c140c80c5003029941c0c5020310060000802c0e803c01c103a0340c80304450505124540740024030880c10b2081102c82d8148014002e100600c25245c1c8104000300300015882c1014800c450074640c001410003034180f129a159406041042410744400d0802e2002082d50540e19040b1001944510b0110030f1074030b5103400b41301c50a64040b420f00b0b41d49810300105002d154010900b41d500c200c003440c000e806a40e8083e204c0801e401740310303000710000e840c050302c640d00b11100200500c803050750b0820380c248410f0800781041d507151082100e4084503c0320f459100c0001c1c1030540b0402d000f8401000840d8490000320b5034021254203107030750000500f0321800e005d0319503007000e05260302540030b281402e02c00000084222039441962a07a20400500700001503810350107101c11414000010444c04203030501e800d0000103600310715001e071030340c0c000c8004001d2031a2000859080c40d82c2c000d00144910317500c9400700300091240805c143c400d01c0c0c85010b440c001580c1441940300c12035100c120b68 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 656322464 1250 656321214 656321257
    0xa0906021210051e0405090a0602041e0f062001020d050f191104120525080f0601080714040e01090819020604020f040507110303040f06050a020324010e06 68
    0x1201c24241e41c3c3c0709034041c421504800700e5a8034141c0740c0c08100b1000f6940031405d0f488441210740740242c00304020302818404500130521a040d8400300300c400c0f14410074008025150445022200e0303c500c40d81c0f01180c0c4400005c01010480d200e8240c011102c1c10006081039134245598043d10400c03540c9180c0c3d088a1000c1014540dc500e1442e000840c140ca410081800c00c02d01107a014070481c00340c1002529aa001003040080c108604400c5c030080d0f01030044120020245c3c8504441300c0d00484c40540900e5441d030000c0c50b80001c496040301d41040040c082e9616145000448080000e40540c1042d1900d080204010090248840e84c512039091550b6403918134003200d05c1549011001030854020f1018807000d030b902d03070b68003019800c0112000a6992250041903814401e208554100d5000200400041c03152281c8903071109400b8800600850b0794289000e0202e2104446c00d0300494400042c016105a02e01c0e600085518103040466400078118001075041d0400b014501e81b000010901 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 656323714 1250 656322464 656322481
    0x1d010905070c120e0604180617160b0f0403140c030d1404091802030609100c08040305070318050310020c070b04060813050a02090a02070201031a180a09060212 70
    0x609500080034a400a200307040c540d070354119502554942d40801801c0044c00906554400455009202e00407210014099100003c1c000c1d04aa109142e801e1521415020781010040f550b6039020507840b80640806003043d5003110300342c1111402200d2040180404400551b90030301c00d034407105501e001006120ba15404141c5081c501c00c4103002004841141c011802060384141c4080e120b3799200072a0b1210240250119401054006581807042e501800350801020a880d0a9800c0b1040305200444a22030281c1d00e8810954004002440070001703100403d1098040d0000c502c2880701c40030078907664000207031400e00840c1000e80000d9002403034401c00081040410300900d440b00110b428545006030190501d840103241e00c1c6c6140f00603d41d441004814409404011b900401711807107070500b014150300035000321a040303000c20318024460202c1c460031217042e040d450000b0400c114424203070f071a032803003501c0140c020016a6159007080b0000344060000d0f245200f03a0042e2100d0030b203402c606 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 656324964 1250 656323714 656323721
    0x6030905060c04061202210106090311030606010503040213090203160e102411070902120601081611010b0904120801091802010e190e060111060c0d09020105041d0109 73
    0xd1040b05601c200300400001d41c00090302038510f401604d00585a030310781c020145102854030240316122110034004225190413081d040d090f24040d0f5128000d00c0c1001081c140e03200416598540400c0c030a00001d4014070b00908400454500c09a000c102112180d0202c1e2030240881340301c031003154900c4028401144245070b05940050000c1d01141c0d440d107010704896004030290599015090326070341004085000340c10341840c00c6284003c8603410395440e02008001d4001c0d040d440c0c1c01010060201d4070561040314040e00541041f2405445244040310541e0510800e180d02221035480b050410030f9a52225201c46c8154003c45803009000d40095005140791016041680100c1c03416216a95400c04030a400f6100382d030a00306a0000c4c0004400982140010403c10200c50700300400442e101d0703c0c850b0304501031042a02c8a0b002d40717034210344181d11181d04a0b03c9034404041480220b40d0a4205d802500721a401814040e2401e516000c10000c0040099510503d100550004120344032082c071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 656326214 1250 656324964 656324971
    0x3100b12011802060a050408030a0c020f0d02030d1d041404060e0a0b0a0f06120c05040c0c021c0c03050f060906130305030403031a120c03011107021f12060603090506 73
    0x40200080000300103a540c091a880c40c003c0d01407540800c11030901802001294094520704003201c2e1121001c0b04c005200d8865802c0480c0a25152003034030140303092052403003401350b9000300600301c406401d40044641c003103500041500d00700301841070b4940e500e591148111501500392076008500d0030741807190aa4504280c0358059502c15182d080c0890b003142207054200c68282000b04119015500e840040c140503045244c0340c11f180d80000c8100b250404000c01246c0c0b0917203050244100010003581d05080b0090041c0d0019a80070031041c070801c03005444140c052140c03e84441050b10303900e42c9490106501900912a4440810311042030b4081001540c031200f81d00391307030080504d2030390020705500024000400303040d202c21685084013640000c0e451000d102400c9000c00a0444070050f650352001e6440c103011b940380c030703005070000a8403904035207140d0340141c040180c211603e00c42d00c10101c140c8803144104840c040c041c66410160380207240040c00140e03400300f50148903040c4181040c0c00035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 656327464 1250 656326214 656326249
    0x90303050406060812250605090d030c020c03070506070807080a1206330c0b07031d0706020a02010503041a0411030606040c020706030e19120807030605030a080306040b03100b 77
    0x100744943c40700c111007140d000c00303540c00320204800c444006d0b19400c80794030301004209500344030030081504000142d9010707940f0259002c1c010345801d0706069803a503480981c0f858060700b00500038030650411400419a003407160b45181c3c40d04c00182c03107102d1a40c0200c090000090301c90b00000380354500500480018180202d921401003260803500003d005c5100e07403d45445030488c1140450902416004c04000d0700302101c010107140024004004015000e00113800210248282a04540c0024008188c820a4004211400d1241c0041d1566040280102c0c0c59a002100e0820301074224039100d03028070b01c250a40f00c07480c4030703110815046c0b03100205030a014910b40103840514550006000e02110194103000680458964200b4106043e010031484240c401603070340c90410207200d0f9640994a01c0d41d4880e0160303115407008805445c214410980d0541c082c1e00f40c000855900c10045030443d10051001a0240365040400d04041e81e181c1c28056160b92000200703501e08142c0402105107088 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 656328714 1250 656327464 656327473
    0xc070c140a1202030a0b0103030323061c050f070f1d0402090109020f0c120c0c01140711041d0109020301060f0315020307030908161106040b030f190903030504060608 73
    0x505000c100c41d14076a11030000c140004004034802d540b01130020203000da8018040701c456684034180035000c0d1041c00c0c65440322448100f0142558543c820705207020700c02c0140344e111f8107400c2d881c0c10092041b010409654038040c0c4080480958010042d00d00140040c19142107001d02c2d001c0b10020001d080c003003810300d00c0010801c000060307544800301070540b0345450700162184040701c4100e0185c00b80002d1400e15104258004000380c01100c00341c601c1181550032942c11413204001180c051135880c0006030034040034095180040c4440180c0d01c0160380140002943c06407034403200d610440c1d0790241003c2a50344104280035800c1c01c2c000c03500544403c064030315045241d0390300e40301c1e80d030104146006603550120120f854288241c1100303913255044580c8035168200a4100c186491814004450010003200301510f281040001d44048540002c4c01c0ca0540e81c4441801c03807040e01c02420800c0c11100356950709035a003001c2c45642c607054000e0b81c0000302da1805107018422201c0705e0f08055800c1c0e00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 656329964 1250 656328714 656328749
    0x30b06040c05030c0a1d0409030305061e0102061324020a030605010e0312030a0204030212030d0c03051306090309051f03060b090916090305010528060e060d020d0b0c070c 75
    0xd50b034045a050405600c0d2a0b00302c110805840301000484110599109040c01d221102741a41070f009070b80111802c03200607240c040903a8000411028880700c15015803c1300000a4900040c088500c01507401402882004405480700c1010701407011100c0d807286e0b601241080400d541031180c2d002030802802d0880c4000001070021380d40340c04e91f6038126500100000010340e410038540650300210340c080c00350340903070141c40344040d00c2c2d800070102448a40d191000b107e50140c482d01505010311414501c610308500507464000141c00a080c090301807007070410700000c8507200c00c2c0e00010380d42d01d0300004c40c04510010350300509440780ca50084400600504c103400182d0f036800c5038142c014500320540d00040c40060f2040c1e580c408694000b038025443c103010001d0f003040c00311a8801e10b01700c8011740c800ca411035400020407a046030049005d2050000c000a200781040690004001d00050080103035011554402040710380443d032041c41d0070804034000e420480082c107a80040e010001e8107240141e03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 656331214 1250 656329964 656329981
    0x1020403141c080c130503030708041a0315040507050c0d030506030c0901081506150705010204090c180512030f03090c3307110d030206061323040219030b06040c0503 73
    0x43c00079010807018440002c80003030b03100024000c03c000342005004e69844d00c145081c00c00b256045803280345103041c55048120903e0308448100c904c1b4284c5c850166104070001e00070300008042c014482001c3c008100511800340008111051540d099503070086580c0c80c2800c01c0c141025400044a1b000703402a100501c001d200115500b83d00803c1c00080001c26a28800007441c907c0712030103010740c0c6410010320381040c44019001041a52017040c0148029a20541d0459145400c0c00440d407148070070322018071a602d0403c40c04290303d4003440481c2d00780824190b40b8000d03548113075852000d81d4400710503100203083c0606500490110b040620724102d08001c0c044d01c0c00004515003041c10040010404104003c0714114511003101400c4061410510301d4003030b41e100710685003640301c0c1040f0300c814680d165440c01a11041410000c4d1001034000541050b0300e41c0502610407a0301c0640c400c2c650301000786000700d40b402180074902d1007200f410400240300846280d86c03a0340301040010006c005080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 656332464 1250 656331214 656331227
    0xd02131406040b03060d05010b0d26070f02040e030405120109060c0e1813080a02010c0e12031608070204090317060d030903110a150e120712031101020c01020403141c 73
    0x3000d1b254202e0410940c50003a0042c2040918030707034446100c649030320901410f8031144031520900040c4808540907138008442d140510f0200518050b01c0d020f2000050034681c119283c1c004600003101e08040d1544001800701266070001c0035940c1d900c103542d00c184181401103910100c1d030303800c0281a07241c0c41002304000d1003540009943c0b008003a80072030004040e28404a00a540180301c16880d8401004000d020780b0400300f2140006001041446591600004041421500800551030101c0c42c101080610503182001d60b8807907000c0c4020001768880740641801c00d8801d0381c8108040d004940b1510100b100030304000c1c0030f200d030104000c000035086038010b001d80380c224480c00e02c680348110001d28204200d40000320040c042c000302c1c01841ba00401c80b004d940384c0031904904108032004c10ed0390390392071521514040e484c001e6051004030b03000e40114520104160300252500c0d200103081800da86c055801211442c0110483d25810441271040c0e950306500c3c074842540030b600901004100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 656333714 1250 656332464 656332471
    0xa0905070e01081506090c19051c0e010c08240109090e061605030105030a02090a020c011526060705030405100c051809250905040e03030609011d04030e060d02131406040b03 76
    0x4500b2000000d40234501a0082d254501034496107184110300d20b0170100060115454010540c0d801d01849400c024040c0c140c040c4a844260480407400e000c00c110083c031b200c1c2c41c44619051040c0c45001082d00740c03050099242c0011381e1030040045051510300c0440754a03140c140201001010b100600c42580e0104800b03030b42c5501102c450021751240c54021000f441038070b868003415840c1c000401814500303124001c08450030300740300781a420400511134030095000d000c103111b00c0c0c00000000e005680120301541d002070142703084170000c8140c5104e00c405c45000d643c03003a02150000c00c0d5402c0c24a4810b003442000c5109449a00c4541841c1c3c8400d4801e80002c3d01042d0440801100408a28440d4035040005e05004205200b02c100c6060240d40342d170300903500d0b03034020100d8000208019903004400f204103500c1000c2c1e401c0d01d95907074508403403003203a401c00c06d0391002c410051250f80444c24000303040010f0085040b800810b1a0001d00e03a00445105902c5025801c144000c10605c201c079000c0d20351 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 656334964 1250 656333714 656333737
    0x70c060c170702040227151612021c050315010306030305030703320a0e0706080c030a060b0f0a02010624030f0f0204060804050d09030b0a0905070e01081506090c 71
    0x7100c5020b8400034000e1b000c1d207800180d540e0002c20074060090034405031303000e1518082c2c4d10b0303400c1c040002606424503c1070024081c01c84030b11403461800a01c001c251440c1e110b00c00d105030b40e0001045031070035101d80340d0610070500040010090250712980704040c044660401d08042141914555010708180802010201459a1590016030785e03109010000c0c0052104c914003907101280c0c0300d2000b0725030340685503400028070f401007503014000c3c0010258151200741d111840c5e0b0350341d40c440b00c0b0170310740c4002c29188038181c030354000080c0c4c0400c000107020310b074408011241d268005180b0090850b0345550184240540c000303041a0b113482c140c00c5807048009640b801050310760754103a0b4140500034801f440803040d4400100040c1c000d90151280d070046100d20141e6000c0048040b04858090f0b5600010740384076440d1000c918502c00641c000c1c092144250181e45049a40303040d03d421507a403d91000c1030640180c00a601090320320007125600c03100c00c55402d803190031700b18100c414500131040c00d0031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 656336214 1250 656334964 656334967
    0x1208060a03150b0316080105010e040b010e040305070206030a0b0117160f0c080301030303021e28030902120601080d030213090b0a09050103260304021e040b0d0602070c060c17 77
    0x1512403040d500f1185030000090121032504550b02000814401d00d4400e40f4419444d2400224171048210700d0603003c0d82e000000604943d081007044c2d8001d000240c01242071000130443c003001622240003551141c001490000786003c0c0050000d0080c40b41051281200310740d96040140c000300b40300040320359070b04510388200c55040c1c3e000296080c1040002c058100d00021000104240d8150000c1140340200d10464880d590344080450300c0d4046e4001070440b09207030314070101995042400e483c08003051481d01042e18083c6402080002d00d00c1180500709802c0030005111043c810000c01601e01c00a150443c5055413080030000710503c10b01411243d241c8902c058111a514288194003403c07420320304100d19650307840e000c2890050b118000680c03007804a00006510305900640f4840d03500580001507038828500108048841440403941c000c1c1d80f0070b00c40e0201e464000b101e03a09203200f0040107a4070115414000700d086100c1e0702002c10428942c1980b0001004404000342950a410001d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 656337464 1250 656336214 656336243
    0x103090b0f1905191b1e0e1e030f03040e010b090406030515040203070e22060f1103150a05150d11030411040b0418110321071208060a03 60
    0x10350241e6410681000400c3c10704040c0310701d0b0218410031082c0c0031209501000314144240c0103c0c10181c0040c52000414003020002070741c0101d004200c00b400100b45071641102003404005039800c6180b44626122014036103582c2c241e41010000e642c00c00340268011030816140401c1c845008005000d040400103000c940002c01e03482c3d0b40c00c000095a80724040e00e03000e0f06460307500703001c1c48000c407026403081c8a100000640603101048840c004c18100003100e214a031441502a490b080c2d8040480354269500102943c003203081c0f0858101c0803800410742c1d62410907000b5a0750944035107200c2d9201c0c0c011880104001e0b43d4045801d500c251103c0760345500d0f03000058a150041050646016602710b00008020404c05176600b0902015021501002500c0c000824001142c04509042e81000c02c80003a2074041303100c07010700a03180c62000b021961948050383e145048010340402010115038081208403c00020801c0c0a02c3d03400030b4986802e10749032110000f46a07a40074800900400b852280c0d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 656338714 1250 656337464 656337481
    0x5100219050d140915060d030e10020f03030c0403140313050d03090510090501021507080c0906070c03080c060a05090a030503090a0b040308010f0503010209060a032403110a050103090b0f 82
    0x580c50402511410350701440c1c59018140c80d11000c42e40315240100e917500095240ca09a50303c042d003290150b41d29100001c21001b44095040941010360a602c49c3c080074140740d450401c019441a040c0f80402d54503140b841ca0400358a45044e071007001301c0e400611000500b251035441007411a007084a903404a51883d0500740c40d041c542e41c11258000c07007080310182801c1d810442c0f410440c2e60a174200c8100002450390040350700c4003650031900140103140801c2e0380c1400180500101c5100a08880c64944a981c5110840e859a07004544000d4003181040200c1c00c1800305640c003500f4400140002d2514450f0140c881d182031030b0060038414088049140c01508002d00c0040c1503201a4444081c109410050501d00c400d20405840c0740c0800300100d880c2c10180280c800412020300a07505001c61040290003a122075500b1400c41006100030048540800078100d00442c0a8011070f04c0064040007840780003081a0410ba052500705880d00700002d0141c1c0102c2e90040080401c000759440d003000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 656339964 1250 656338714 656338721
    0xb090d02010c0c1d33190e1b0a02070612110c0f070611120c012a0305060a270b031005100e04020303041401180303050705100219050d 59
    0xf40009003680d0010504003a09a080d03a002c81010310b400c81a9941c40c41d81d002805c540020800003c0d1450042084040315407224840e20b950003400e8055030700d030142100310644443d0b408803d55442c40c0090141d005200d01e560310240d03842041076031803c80c115501940e41c01d80d620600040041029814070411929485003045041b1100000c0e41e481e0350350001035441d00c1c051210782c0c40d402170010000303a007030042c1c2d800103903e0f08143c00b40080200800e02155507401445c800401c2d950ad450600c0401008047c0b42c900c049844160211040060000117046580c0140054050209078500780b0407800380c24900e8014404400c0c1c00c0782c161240a403075201400c21411025054455042d51f40d810003000d4100c14800c00400314420060355982a075491801c4003a1006500358000700428000000f420500313120000040c108000d0024460300c142c06003005580c001d600142c0003083d4201000300030b2090001700c0c110310000b90704229000a14015028006181200303009000a401c08098031703503003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 656341214 1250 656339964 656339987
    0x303010b0a202505030c06030903070501060e1f0b090f0f0a06030e1917070c0b0d09120201050c04050d021305040506071116050904030c0c0f140a0b090d0201 69
    0x211810059501d8155680d901d00300c400710460000340c1d22150001c0b90510f001c05404a440c003d000380340c005030400911460342d101510440d4075010400a00c004507109010f00c000500649112500030315141541e101540e10240540344810ba20701010044643c0a0054651154040744c24200c0c80b040507001411b0155400040ca80141c1d0f090400101d41d40c05500540341c14440b1800e4910ba4118003200121041800c2c0000304800199829075500030844806040218442c0c0c000a07a059241d500322040358010360311002010303817502406020003000900d54041d0308030600090005081180c06207410340124081c542c09186110302c03840c150365504070624108440101d0400c40c0c0c0c10a0708295444140854000c00411200003200c40c2d01c00cac00007504407220120303401d00d4071041d0400d010030502c4100a40300354204550007806801181049501100620b2900c0383c0018191410305a880e081010310125881092005420840b13650044212919003004844080310540d480c8010f03034035201c800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 656342464 1250 656341214 656341247
    0x1080c030a140c040512030408030f0f1605060a14070e060a05120c04030c0b1201141302120106110706140a09080f0304140f0d240c0c0c0609080303010b0a 68
    0x2e07091081c89520180100241d407410b5401c0498003817072210341c50352441644500e110ba50b10402c0a1030000c25900d029007001c9000010030f92500c030003194880041c116030170042d80c181d0400000d01c4107507155403186070b03800400380d144020240303030000005d4500c3c0c1541c42600c0c002d181c00903000d82168440d8040768904402c1031a01c40e0a0706005103101c1d105e0304140822a0300714004940400c200180509882034a00d140b1404005a801d154404140001903400550031140b04101041701c826240090702405c0a036100e116925850306600925404102c885c03200c02d03070070401040c0425030348400403160324105480c0040d912036040744125201d50b103036400260140100544082c00c85008802041100d10040f510b002c1d07805020308102c0030180b040362407035109801c25a800d00045084d2103090305100d0107402e0b0380178031a00c40304031030549100416081c0000c031030003041c0041004080380c001c090309051801c450b00a00700040b59a491106000b500c081000108964240f544144242c84600860 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 656343714 1250 656342464 656342501
    0x3060e011401080c0d061d0a110a050f070807062003270708030a091403030a0509190306052a0c0312090a060c0509030d020f0316060b100e03190201080c030a 69
    0xd1f0303020045541200e8900d00074041e660404210302412501903414a0304005841920b01004003a081d12580d0100f9140e54400b40d05200110201c8e00b43d0000d03002d9203020b802c0c01704028070301c5c81c044100340c08958800200e1140500500c2200424034000d01196050074900d90b40991400210324078140c9541c0c00340300d5038840040d0051941b5405146501212141000c141869803010700b090344078002d0161100c0012414060301c4224600b1450b11403108a2010072880e90503100d4654500b520000c03590080c10701107801d010001d460011100e4070482c8007180040f410401e0a100e2075840340304180e0000c070070005c40f1021800141d0180000e601103640100c04101c7d845908030042d0042e0064141a03100e80a4203005a069500110f4803114614801000e10b181807520460080074180d8080150b030480c0c3c3c5c542000b1115120001c421070700c15115110700c1c041110b03070000c040c0f42240311810000300041103117003000140d802c1408160002d00d40c90106071690f4512004000400b80101142000c121 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 656344964 1250 656343714 656343719
    0x118060f0b0909151305190c030c02190c05040b0604171006050105070f030f02010e010204030b0f1008060103290f1503010e03090d080705030a03060603060e011401080c0d06 76
    0x34500080c01002000d8503c2040790703032056529940381c4c0da8841d07802c2e0002461034013203801d0a00c0e0790040c0e5005c0282c82d000c07004007101607141822104107c0c9141c0c080f03a0b9031401a81000c0d010410411003030140c041843c500350ae25500e5807001003940c0b049502503500c0f005602e4241d0b031400181e50103400f43d000d00c2400c89143d04145c1d82e640c1c42041c0c61141007854200b012810f54401c034212500c0c142c00c00c0f045503c500903941c00700c1d010800a00c0e0310085550318803014190381028001013000f0340c00307041c408000b8200086100424840a000c1184002c080740007041240c40200c2d4813411250130400e9602014000c6546042c072019201d00d0384545941c16040001da41f04060b0020302800c5d0826400c00d019491405240c01c8404c10425090b00b5841804103144601d06032039032500c2d00303208401d9581094000e64503280b454000c05156800300740c450600340a82c1e03a0620070310b402403117500c040081d40c7d40b4224000c0e0301480a12a29810024003500141c0c0114801c01114075200b401c2d0400c02c000c59 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 656346214 1250 656344964 656344979
    0x304030f0c05040b120607110c2d01020d0c0609030e0901090f050105060309103902060901110a080612100c080a020c0d0c050a0b010e0702010b04090b0118060f 70
    0x1849805010b10031407038040d03044d030103040c0600d000d90350700035807001080705880e242020b80e00c01c4071081c80744039284100c9138103100d43d4581c4811510046141342804503214a14601c0511104010300524115400000b20300c0d0b0741540801400d2540e0b800101c0000c951503107007011100915071000164109a40e28000070ba245a203602c0300d455203030101401c02060f41c035141041928801694005c6039540f03c00f419200d000c12079032000c10329540c507503603658010107412407820480b0000710641c555646001041598290103000d003a6102c0304100081000c1203114070780880c90301402c490541080003500000703c03d619445401c208a000707080c01c513028058202d440c131001e08091401c24000070803d001003130528929000f610904850039000d0111034400c1c074400c03100c1c012009801e8075180b08400ba003101044c0a21030319030103040e8200c0a15050307d40740001a0a4032044000386004914025058010644001f01c0c681541c60041e030719241c050b030082121010f0640c0e9003140c000808100800039814 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 656347464 1250 656346214 656346233
    0x913030923060a1d03010c05041505210f0c070b04120302070606090c1805061801020a0816140d0914040605120601030201031404120305060117090d1206050607140304030f 75
    0x1298003400f02c013914103540307041c50301307a0701843d4040b00411028001400250100c1c3c04800303103044603180c01e508101464091204188801005200c980c40ccd1000f070050071000340212962005c05c688002d407038140181e81d18040220010030180c049180c0c0d01b954400d46101b50112140e15801041c24000d20391203080401c014503c021b0044041900e2503144001220210901c0c42111030061443d41444c0c5540c8a2075070b1038021103003550450050b2603921001401c1d000c00341c51342c140446c20341070200103989481b826005e810703040c0b0a02c69001e42503411405511042201c162503040d0468452450f0400104001d4000c5402503a0b0184010320403403d400f038002840c3d03040743d0003641c00380712035a0144a012045042a5805080c0f44001e0f0640c0007000e0280c0c118030742040041c9420b40254600c0284040b071078000391072641050300007041081240b80e0000c071303681d50040307100010040300d85402c0c00a03030741c2d00c43e13000010b010f2040002e12040c01c10061060394001e50300711258154100761032a282a08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 656348714 1250 656347464 656347487
    0xa05010606081305150a1103090106060f142d0406030b270703200c01090611131707080d09080f0a12050c1606020c0913030923060a 58
    0x1480c1400000d00031844420800c00035508080504080700d0400d170400c05250000f841c104055443e50100d902c250541e00003184246500350001500500f403074001801a031001c0740860412916500c46108107a600c400c68850400700c00b452060000314014509441a1860b400e590107074020030300041039038141d080240392441c102c0703101c000410084050b1101d5009081e12010002507240064103450003503011803210a190311212194a8003a4461a03207940b00341520200f603511200d5103010040f080c010220289241c041140c00c00c4612025902c500c2207074801e1f00104069040e10384107141d414810500600880015280640b1601c40040c2145400d40301c2c03040d240c8503c4950814184c80850010907541c3d1040301c0031500c02c55a60300701d40c0c541160644600a02414903200740e02000014200020b00f60f40d006002a8151a81040b4003240020101d80c50031800120800000741e100c00d0341b44c20b84101c80410500c4688000c0c1515000d03412248164202d00c00284400f4a076030404c050317008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 656349964 1250 656348714 656348717
    0x50a02041a210c13090c0305060f0f06070828110f07060e011b1121120c1908040509280f0b030a200604060e09040f050a05010606 57
    0xa200c000800100514402c064034441e0300414010600305240a405409400c050b4000145090020003050082c91159580c0007030005590f8806560107a03030180100d80d0702100c216400c0310500112001309034403040e10000380d84541400502e4108020403281598070750040302542c100001d40f0222400500d9940d4881c44002c5a44000c420110036400106010346003000d6018004070741c5004420b4404140d0440c0707441c184485005c140e138031074404140c41c0c0312300c50142e103000311003403452800d00221101c8150700b11660725400b2103200d05900d00003440c1104411415002e6695500c500d8520f040c0003040075640464203a0300310300c1c01030105140282c001c1d038408403019825920b440ca84507982450742c1c04085140c1040703101031200555180e000042ca0042e031580818014514400282030140c0500d048904d418110700031a07501700c0406403401205e80940e21745152604001025151070207402901344518511400503042240d80c000c1051601c3d030190450b0682503583c5001406804d96001c4c090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 656351214 1250 656349964 656349989
    0x5010e0f1b04050c07060203090607090518010b0d020c06040b0105031204230a080313090b040b0d11040f0618050a150512011d330c1c050a0204 63
    0x6000300c0c8007194001c0039000300e140c1d4a448105020a0002421000b40301981d155820f12401c00442c459000940c407651010300a801c003403800d06009841140c0320b4000030f0140d01c0020307000b00120b041c91201810358110581c01e98980c1700141e10500a4410400c1c4800180a032100340400c01c08010030f1181642d80c103d00f60382074070015407062007035400341c1e2091800403c4007125000050072844103081d603000d000f82940004980310b2805510b9a808541c0c1ca05070080fa00808209000d8103101d04032035103008540a11000ca050700000b480e1111084000e42100308440f001c040c1556264845c00e40c0302c42e424414410f95648030491018030b01c403203200d68141c6090000007002c0580301e1054085202400c069002c0a6003040107120260200c58014461507588210030b4840020300d90b0340c1c043d00d04854005104658110300181c2e800320581044240b40c03051403000c0d500c0340194420196100781852201da488400c0340714007134414450076080307101162411050101c0519190000c000741d42c440000392 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 656352464 1250 656351214 656351233
    0x80c1603170601180501030507020a0219031704080607260703050109200318010f05010e01050316060503060d020303070b180d0c171b06310c061101090605010305010e 73
    0x19038144400303980300480341040130400e220a42c0039070300c8590851094411180c050b00583e0100c0c00244050071202c1440c3c408400420401c07115810141c0c0b1800344003020b0782494906001c01e43c0e1a24040d10410a000207001c2404181d0010228000f0300c0800e1080f400c2c5905000b503000c1e000740400e0050298541c00d02c080c0008400c10f2640740660307519100640d5140d50707212525941d5158140c08031400c99501c61120b0140d000040c05001c0c0070305040301604038154500001c151604807410508031034101401030800c01981c200d425030b0390010081d14061500412807000030b00b90310403100c3c000e180090101c140541106c03484c0b03035580c0c100b1000c0f0849001a0b40b280b01a102295642001001940201a0109003200f010068140022028a103124001c1c824a01c41c0c00d01d001101d0380100c6814298980c00101c03010b101021070103c01d05507420f5010090b4031042d04020090080c80f0500ca05501c0c100c10325403095000d407503445e400100c100201c1d6128944240030b00024080c02041d44a101c4a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 656353714 1250 656352464 656352467
    0x5010306091b03110d060801060617160e12030a020a02040606020c030316050c090114040c0f020d0c24021b0c131a0409050303071103090d03080c1603170601 69
    0x180046490074407002c10741c0e0350b411842140600202480c3ea08100301c14014017404280c18000c4c04040e1413201e00200d18241020030041110030b20010450000c000ca009001c640c8982c650b1051982e00c3c28504001c1a00b50100466441115000c03900c25600c40090302502080d80400d0f0201d0b450310881e070601000f655503a00320f9403400c0074240958160400c01030702c044040180f80405a4501c60030a076501c8000031000034000e560240d009520700c4c030141154403190710f01449234501e0311100d41401d00d416003400100a641d03030204512401404031500d15281480b0380740102e582c2d0a00c5003243c030900c0d00030656a5030080c0d004884070803150600f09040307054140c00031540c040c00c120702401d8010364015980d8030102600001d884140794025000c1e403a40187c44034020880340381e01a00081d5900d01b040750000b00300a0070042039494913002401444826902d0440e0303040c3c0250075141242064849259403c59407141d4a00044e418405203219010181c1000707940344450720000741114265a403000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 656354964 1250 656353714 656353721
    0x20a08030f1b19051806070803151806060d0902030d05210105330a050301170c150702040b12061e13080c010b0a090510092a02030706150501030609 65
    0x8149042c0b00c0070f5144070f40643c4907030050501984045500d41e140c1140c200071034416032007408140c41503c1c00101300101c845455040415100d01540c54440d003600751407400c044180003030100c43c450000010740b16030b0f0007855040122a40d0b0001d050303036602012108050b20300c1c1e1044c0146041404072082031941070150420680c100c2e2400b8101c2c012030b030365182c00806050740715400e505003042e0464000390052042406030000c0001c2d521216071301e50401816820320039164680c00b003a640002185070050b2030319103010008104035005503803140068800500580744984070150480140d41900005100010707400313015502440c00619001400800058124002c6900c1026404100c0a840001d880c5100800b00720b00301c0c600005902e1040c0700040c84402c00f60f4002da100d04d44500034827240d0424101c200c40100700d115070402107101003405611031075042450400119000c160b000010030b009000302e4250300e034030070010000f071552580c2c504d540400c1c1d0300640b4002450700c640030540301c0c414407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 656356214 1250 656354964 656354977
    0xb12010f1103014e020a0803070f021c150504060506030703050604020d060f1a030606060a08060913052b090602031801020313031523070c0201020a08030f1b 69
    0x610800207403c600c04e581800104003441508007404840e0400b8010440c0d0800303803c00340150700098101c019030041210030b0311b25400c50328164100b009000e000030a012500145507906940344001d01d07000164400c0b02d890700c001c000c0e04031460002d0900ca2030096030300003440781f40306100c01c100e1a1280c109060703840300d071070200601c5c07648418041805827400075403000c00d07a4850300e0040380880808264034180e0716400c05010600041056070149840e09101e6280c0c440810380b507641c00c0440040303004290304000b0340800d01030840030340403510400004140813030294109084031440d0301c00c282c1c01c1401007000e0210341001d5091040b80684540306101c400211550360b4004c5003007002202030401104801d140b6181503210400c00c240d24031054554042c02180548404510302000e08413050070340d03d40040c400d2818821281c480402022641d0f465006245460200d030225036500c0141d1034141d0303104024148920100400c048900d4800a1520030202e607007501c0490058000c49807124001d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 656357464 1250 656356214 656356229
    0x80109050d0806040615050304052509020f04050a0b040e0901112502030607210b01090b0f16060b01021009020303090118050a060e0118060207030f03030b12010f110301 74
    0x9401254450b1084140030f422001c02000054003d0307803150000507000c012940c9601040011003007000740035080c09403401c44401c072818000b60000701140e91187c000c0034003030108000e44c0418409a14a000c4040e2400340c140030302448a41c9842d4a0b1840701c6802a1244c400e99005501c00110003001c180609043d00c1c1d00b0380701d00760403d01960744c005c0103400056100d40d0700c4030445d00b0040c0135a0702001198080c00311074407603d03003609880c0122808580c4210503441c8a0342060901101c591303114510382d003114000c51700c641c2c944c0c64a8501d445540721714216181e200700c003503e814091010640c840da07126002602107504102181442c88180c034a4141d0103540340d002401414165401002455822000030300d12580054590000a4503000e0a40000c0c000840406180c802da50700702507000c0c1c2c40c190540496500f2480e0020003951420f15000c01010307070800d0019141018001d030000031900c02c00400c0450650f01d01c1071014000c000034000b40101030f0501896079005031060080381e06840c580e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 656358714 1250 656357464 656357473
    0xc07091103071110050703020901020d08060a0b070c0f15080108011a092a30011503020705010228050708070807080903071401090e07050d0c120e0703060608010905 72
    0x342d02c030036940f05201540c01143d42c00b41041ca080150114850f0611500e05903c0050302c80510000082c03910300802c510030f0501ca44031b014032581d69519030524044070b04061b0141d03681e18252502d0b05139103280e5841001111500000456110140640d8026420b072030f55658113244e1782c41c9105c500382c4145d411141c20910002900ba8030310b04120b808103502401c46c00510340040c09410814507200780001030894110070220301c0b61a088090194131005141c101115003940e40b40c4041184444410f00c0b4250460700010f400c800304038040d130141d072100c6400a000315162001d50070312040c070741c010302810204901c01215081209029078182d400e00c0d60421030301d82c00c00550b5030b1034070074541c0100300a40300904144100c005d165020809d00016080c0c1d00f84115011542c5000982000c1141d00305d40386001c007200422064561003010340d8506801c8600200300c580c4004c000b81ca280c142d41000d20b0040703090402514000e140005e07501c0c100c900c1b41c40100410b0b55928082401c840310f00c50f008140760003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 656359964 1250 656358714 656358721
    0x114060d0201030c050c070e0907090b01050316020c1201020705010b06040605220302041806050702120a081915140d0206030f0a11160308070e220e0f030c07091103 72
    0x103e54000c00e041800750900a00d00007203203110914028859001203ea08840c0f030801107100d01c2841481c00030b2401c0c0c0c0c028002c0c0c1c4410000a042404010100b40c0c00c000d640080402c05032081204000101c4064008800880040280b90103907002c03610940d42c079070900e2440000c50410b0790031141101d4041da11981041d07290400106508035044c0e802d03855280c03003540800540d80718400c4e15200000d03226040b6250f0450b10301001910704c010704840030340d00400d42c5d1041c0180c0c030000701c07143d411040c81e100020f070f13551841203001c1c070502000d00e02c005450407211030020b16000c0710f0003007643c0704003480101c00d402072000c011540191700c10080d00510709001140c0030394002c2c40115001600d5000c00326004600c418219000d41180c440a20603945d0541510b040c160403810a9070050070728035200d600e0070005130108540300d030250b528000000d081c0303220079a00007071980006141c60300002602c4488a0100802d95640c02c071340301030003d40c0035211000032500380520920002c83c0307840800608558 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 656361214 1250 656359964 656359967
    0x2130311120c0a1820070b101d0c070b0711010b19090b031c031a01030b030a08181f09052205060409021c0605150a12031106090f0114060d0201 63
    0x80400d200f04944d00c0e1a0f62070320168000030a0070001c1082d00510254451010b428003184802e405403068641607200d0b00c0501821031180d4841e041c00c0340580070b8111703c2d15809505101c0303104840b00079001036049028005115030011a000440e00410028801802194104961000404140812031030200c608101e641351b01e03086400c10450080994132114049100019405090a100c100180c1d0752100841032581c40031191100c43c0c0280b0741009000300600c003099a5803410070380038003010720101d0340703062490300380340c507011401405400168072320f001074603102024800d00300080110300f401301d0100e0a400d1080b200000c1454000c01c40e450364005d410091300410024103996041038031000684056118034812078102da03246180307084241017500707002007150409001c07003825074400312190302da07950340c0951407007511800881e004818446150548542030003040c1507001e0300842c020880c114070007040594100c00002d009000700707600c00d450324420581c01c86040da0300c210025620707809035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 656362464 1250 656361214 656361239
    0x512040201090f080303190225060f090c050414040b0f1e16020f19061d0a14120301050a1710050117010605042d02130311120c0a 57
    0xa8018140744026948600e21410200c0c0f8a800401e0340358800014003402c5014000b110301d144420503800c40c03d01011032421402440d4032003001c00340c01c0c006185e131410301c4110380c8a01e0401010440402c41010700d49022a10011140301f114404d929003d9140460003000c2ca01c1441183e100d4200b1032a41e583e040b012412038000340c0204462007100f010144012182c2d1003090164801c40f107003000694102c14024680024040158101c2d040740083c000003da255240001c51940070601080321982c1c541400000f002c82d0071030031914030074000c00c041400000c1d88070307082c4c1d8041d0005840c051140403442c0b00c40ca110038440d40b5001000071004100c2c0c2008a80c601c1f945021990a881c03540b5200401c3c0800e8800370313041360300486c3c600d80050020303039401d2080c14010301058500b402954440042000030300c1c0700d520954201040303c5400182441607034101c0d040b15081ea660f59080d9074580c2001039840c1c40c100c1085015400c220b41c09542c03640b00080e2404204801800801064107000100060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 656363714 1250 656362464 656362471
    0x30e0f0a0f080a0525141c30230114040507031e0b0310150e09071215050903031009021c09210516081e07030e0901150512 54
    0x10004e051122881c107040d0411460140300354001e084054044c64100032035041d040359002025548520405001c0d000140b5102140045038103000740c0a00c400050f070ba454002d075001d4984800c6143d001c0740ca100c0d149a000145280c00007002c444064040522403045205c02c0c01640000301440300c2803001032915420440e4000310514000c40e16034900c0205110032045503411301062a111120140242410440c0c1140f21110360703824000d540000ac4a03000700c40c21401b550002e202e00c1000a14074000c108004070080c110324a80f0702c403920b00d6080004050045207541d88919040c43e000c501e104a000060701d0040c510b64480ca00010314041510740203501500088004205030510704542204c588240342e101c034010200404901c204c040d128000c1c658107581d030010310205000d5503110240700721075041a1a4011841035903079201040c0582c480c2d105404801c0c0c002c000003000010182e00603036884600b50113a51200786a62245c013402c1150b2000400c9100180003401101c00180801681c40d82 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 656364964 1250 656363714 656363717
    0xa0e040203060a050d1a0903070f02040b120f0105010e13030516060b0310020706050703090b0403260108030d060b030c07030302220806090c0301150b0a0908010606030e0f0a0f080a 79
    0x1403140c0c4e503c01158441c1038490007a1000305074014809501c81c415448203611503854070140d0b181a04070741d10200c0c40058141c0c0a8011076594000d54a9a2a0545400d0a8004000440b14204442c02801d4040c0109015a000450592004c01c4249100f00e24240101b641921031904002c000c010181d18040b00c04030681c1e00544548504845850a10880b2140070881c500584c0e11001c505011041d1a00507000b20f0070145004950000b0860003159560400c1d414a015a10381c1c09204510628a140099211402001030300024007802c000004010b5208104004d00c00a0b0b510084150f090208560f0031a2184c420007113480020310a9004104180400500100c40c0d20041400c0b5294034150300032110a81c4110107225804804103c04000c0003011402030044180040111810f44240d11410203042004500c02d59068090a8407001810012008001440d0388040040141102100341c10036800f079041203a401c540701040440e02150032046203012107260307640e4514aa84104000e80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 656366214 1250 656364964 656364979
    0x70f080a02281a04050f120c06070f050303100312030e060a0c020f010c0315150507020f130c08070f080c181c080304020a080102070201121508061602120a0e04020306 73
    0x7903043c0c3e4450000e8061951a15070507101c504003c20b0003203581204041ca0310503c4100181000c4a0000400313000c000f40c1561a191130702c02038034023584900c2c60403800a0040c00044100549102001400011640200c6c441c10038182c40003015000c9481410190240d42c01010025008071019008081202e03942d10444003c10300540d5000d0031a1401d130000702c0000e4943c0546400e00c2110000c0002504100c15040c1c083d0b69280c1015003e41326804000f80105100c010820141d62012113050340239805490130310030184043e03001003555004170b0b940004554032002d1394100c207215000c03080c41001c0c0c08001da451301003c980f10f200038105030802d4551050060108815840b40640300d00101c502c43e0a00703a440e400c152040001d1400c0325000010540c0c1305001440260381d0041c026808240180d00c001055030000700c2050a00c1010782001d003281c403850044c44002004010380d501d090115500f038501c400845441c40d401d40c85035a480c540010040c040c8000140382940c015038010000800c441e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 656367464 1250 656366214 656366219
    0x70203040915050f1203040915090c0207050102061302030a020d080705030d05070914300706021c080f0c1c0507170601030605061b0709050405070f080a0228 69
    0x50b520385000081d5050141c102c20403e90420f828544030030320045840414680700003c046036240558030445183e02e80325944072494444142c5142e0103840318820a001d006100c0d40040e50380c45c241c1c458240144104400140e07050700d02034000d140c803680140a03008005081d0200304041d0030710ba10078cc590704401c000e41800200c0400081424501d07180000c0746900d0f0981c405400311015a00210041380220307400d01d80c96a9864180c081c807540708080822001d01c449864038a04603d00303684c081d03803090702800325807503070005203010b0180c840b0340305511104110f64081719100000d44401345200f5246e80030070701151000c00503002d030a851400064800c2040324481c001d40d1004e41c6d035503020405c044000001c2801c54100194812402e08040c04441d25200124103148150800c0c1482854012400968140140000b0009003c6180d00344528107080c00c2103520b5800ca07208000141421035000182100042400300c180c40d0000c00308500700c0008032068800c402400d449201d02000000007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 656368714 1250 656367464 656367479
    0x26010b040e0d080c040e1f0f0909020a1e061b0c061e020d0207060f050906070614070306030803070302071416090e0c130e0a08030103060510210b07020304 68
    0x70806a56440e00007009401c2c140381010300304401c05805042e440004000c00d1083d642d0920074590000d0a43c2813414480181302c2501d050a541500004910045800c0015181095800204105008803a13025a4590f202e802e8500d460b100388104c100d50f0810382c000c00c2600d001c0c040010901c0350f2810344e045003280540d00c4801c10700440d00725a0105004c582807414244c80300c134080700b010046000916a40c5840c00003e0f40e0340b0590f100d83d400304407801805c4030f141c901c0742e0f007a40c1d0301c0c6002800e00c680750440382c0307000000752071700c4a280c03c103c4441d40006003c0d24401e001d60800c1705d8000781d0340351454031900401ca0280d40141c0c02a83c080c4203c842400000004001c01a8034030290f41d041c250903420101081c0076034290000b003100340d0340f0501000006550300c41845c0071f9032140e0b58000036504008004141440c0ea00ca070042c101c82c9000c0000020720840d03400c440e224003068800304040c240c550644074561080415400b29840f280242000040c501240060b0010b6050044030f052980d02c01c01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 656369964 1250 656368714 656368721
    0xe130222020706050a0e0a080a050d0f060311091302011d031b09070f02340f0e0132030c040f150f030203100b040b0d050c030c0103050126010b04 64
    0x2a000c42103980001c2d550240985407140c1c9410040740001400b003810106c0d1810756603030751881c0c040c101c50000244107203841c1c010700481d0f001d2024030344103102c0e000c003c41541d8010040c5100030342d40040da5400a10040c03814400091042400908101c0001c8841d001168591090a0301d03064482c00c0400340600f6680400003500f01ca403079090b0034010840c4500901041d1040a40b000c4184010500c0001c482c82e00400c040c100174240d0301e11043c41d0380c100540c0c65558040a100c540c051200300c00c000c41d903400c108158006450314a40d600c02c0b142d0f80c0700c210001c202004400928a4002590000b1100001c002d23060021003000b802c40d01c0c0101118009400c59912454401c081c9548140000c0041ca5010000008190740c030040009076141d600443d444006a8013461a4541d880c00c4900ca25920740e84a03414448005d00703410001e91051500700e50354110914024400d1080242001156100b401218180d81080749150b91251100741001e940c0c0d50500b40100712552200c1608a05468510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 656371214 1250 656369964 656370019
    0x4170304170c0f040510030803060f1807081b0d0e01150f050f1f111207290105100e010c08181014070210050910270e1302 54
    0x801814104540d03070b041004210064103814000c6052004000040743c1030a600000c9030b410022066403a0f99a00025802d0080605041d900040c0807032040304456001048a118003042d481301882915040d40700103803c90310360081c000fa80d8081003418003091280d0041e074021200140003042005000c51101c03200701082c4c001c003040ea00211020812847d12034a98480c00d0025140c4080032200f14220b0b029800f83c2485841c18040e50703070521048000204404400010404105520f614061030210f140c0680d815801c2e50b41e0035689505800c031a03000f00401e048950040000c0c082040025080d0341d1001c4050909050160005d803480100d481c4e4001400c05041e803040b035006408030340d01005850605d49002008000310400c1c03c4440d42c1007a0102c555258048a0b0700d0100070010008a4a52040483c500c0c0c100301a003560b01070709a00314001c0f690030f046102e0710454201c800115400c41030f2480c400d2806240015010460900605651600b418001341c80400440d04031103803005860b41c0e92 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 656372464 1250 656371214 656371259
    0xd060507050d1a0f010c050f060c0706050109140712020f03150a0f030f080d0f0e010c02010516021c0207050d0c0501170f0420120c09060102011104170304 68
    0x1e4980c0b6100502d102d48200d903450000b01c2d04071400028003040e41003000090140c1480751016440c401e204c4100030a050801c029070443e003d910301a140c0900d039801c40750b8100c070894200f5001190300b003054084d0a404100340c501c807807040c0d6140041103441d035049105e90405540d080102c40144a004802540704800c1c2d90346240b92810303c1d81c2409007840e1142c0c4521501e418458042c40021424036600301e04540010840e41c0703428142c10940d008203643c00b9407900c0b90345011201c840440040d040005a10035640081003560381d81039070030201c90300240110700140c00401149800d07001105018007074443c00d1040360365082e21480410030300b0808603010341b02145e110408210660780038100e60b0940d07681080540140c14003001903410008003400060062071702140081d50300c200701c3e002c40c96111008041d150394000c00f40030360b0b841d0008004418001e00c1000002040395005004540007070807030b03107070310b030b11b85403a00c5c2e400c00b01122400310724030203408200320001b101c1c080010030030304c0384a01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 656373714 1250 656372464 656372467
    0x150917210c0d05090306161209020301140103060b0a06020d020a02060318070803030f16050409020703020a17180d020109120804080a030e01080a111c060b0304030c02120c0312090d06050705 83
    0x1c4e0820185001030080041208204000189000d240d00003990394041e1000c04020130794001910000c1c1c090520f0f12400301e0382c00450800001400150341103010046000d42d90403940c20b8907601c04903207440b841100e4001607405803560f1070041c10000001c55000e107075109440c1d06c260400075194245810780c0d00050380f6038004070501a0148850702d82581240314a04070003c40444c0740c0020b00f240c01a881414400e80e800320b01c0c0070030b244c000c0c0090003c1c5a842029140c227000d1303242e03c0ba059508004071071000c920410701c4c140c1590804195095905405844a5490300e140012400c80d044000c0300071900b4101c107100001d015001001145c12151003512181c6030303400035100052034400010880c40200781400b01e400d0720703540e42008031104040441c461040c82c9250b101c801001c0d00ca598083d20900000008000034035500030103408845100721180c01412030041400b03582c40e00203686c83c07581a044880c0b0b074580e5802c01d600810a581d000f0300a440400340340d80b00c807011541c0803502caa000c01c40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 656374964 1250 656373714 656373727
    0x90706110c0603090a200a030305070624081005130f02011e09030201080c07150c050f13090605010518040b120a05010c08060a14060705011104150917210c0d05 70
    0x406d1128004021515952000e020802400046407070800e031001400780400051201c05001c925009904103404031088070b00d501d940d0400e94000200c5030f20070480e40340200314a00341490401d0040da8041c036030701c0301503000485d450b856403400d20580c190200d060100b1543d54190103400c60050400d5811180c844915803899400007525a06004100390711242003044070100084c004804110019000500000c0d4142c60ba074017900d8510400403a0114030301d000c951105030011140102003601d00700c05040c401031340d958005440700e018901080440d010011441c4046081c0303940801d05190b4018281074169029000300c90600400c41000e54a0344d448540402c10190400b07a1260840003e0714403040031880d10107440a035204d4506420720410f40000c214041c04025041425a140c403010415580c81e607131045950240c01c4c8800c0d11001c0760103248000341da084150508485c0d40d040d6000b82a5200318081c202c080c2d4610306100105110091086001d4100f040080204071031300f0b603c079103a5440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 656376214 1250 656374964 656374973
    0xc0c100c021c020913050a12271d09122101080a0201110609031213020a18060504060b070201120f0c030603050f030a170a0f051518090706110c0603090a 67
    0x240106001178280016040c1d10004100003862102d0716040001a54800703c10f040032900d004100451100c0e032006404181c184000e0402900f0841e440c1440d80c1c1c855950309610425210000c6402c41500c2c0c10900003946400c0c98800100100d20300b01c80c8a03e04413540c0c0078200180384080c1c11841041e804401c03850210358001d1034000300c124000b0300402e050710b005841c4650340d1007075510f07842d0718503240f0010800d44148400c508a400b84e005201d120b8507031300d038034241100800342d2010780c8000b400c01d27000142508043c407610b01501c0c0c0002000389800400d8005403119100c0c9480426503650390b680c0760010714501e00c2030182c000e0341c039500404c800b1310b581041e902d40100e006803842030f0740040010070000c5821440e01940c1014a14400d101a950114280c0040032414841410700303007444104007048481291000c6051411034481c0000070075460390043c1c01d031b0121003001d85030780407107c00d04c4079a0054404164400196080700d581a0102c804504c01b9041901c0b0b5084507482541040c0401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 656377464 1250 656376214 656376229
    0x20d0c0e0907020610091e0c050a020d0f05030103032a0506070201060b0f03010e0c0d0903020a020a060c0c05060904060909050606090c0307020601030605100509160f050c0c100c021c02 81
    0x40c543d100030003040c1054050f1044400c11441032482da10f40d40e41e07400d0307a01c098619404a00c04030720181009421070100025202e5400500907100500074030304c1c00c1040b24002d0700d0100c038428442d669603086a080d40d03815100307405100e0142402a0182081000b601c415a1030034401d54440c41c0500580e041c03c07100a07080d18580c2d00540724114044c8010050445108282d038116409141440d040380c4600805500512690070703420100d504000c51481855000101140c1da03910907100301508070303503035038007182c81035a07034200200300c0c211111301006240703040700151105000c02071001540d1540ca02c5400c0413522200c000702c0c1c280c2c00200c100802c51a0241907035601018101440d480c500c0e100350020345441c414040103000035034400214220310101e080c14001342401501e443e078035090545202254070540003213040001d115441c0342d40102c1c071036000d407034013a02448001c02c1090386003810041034056034451541006641140c910240e5107201c060040740038116400c0f60850380c00c0c0140000e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 656378714 1250 656377464 656377471
    0x80712020c150f07022803020f0108060102060a200a020c0301050105100c0f031e0509040c0327050f011e0b0604030b0c160c08031201090b0121020d0c0e09 68
    0xc0906400d00750481000310125599112083e40255451040e440041e011074014010060f10300050010300c241450061820000e5900881c1d24507103c2482c080119420301c402c8480d580141c01c4040400c1e000070f502c0c2c122580b5041903031400c660030f0901c0440c000c01074002840301c80060340034000e1040181000e10a90b4007501094030b01031511200040007422032403070468001c008600440404003898820b1507404103038020341c00840c440400d104801001604039201c0301388528071f000c51800c01d4501900c03508141600880000008000c54020b603050402c04620030f6607075000d2448000c2c05010284103c109101c2031644d40c0601021444200017215603800a841c01210200b00601c0802c06404041d07900c6125030310501da4442e5518505c0030301c002550030040c20a0002203001c203890b0b40c0400a400c400d412541d00c0490740e81d17154406010b0324500141c182c045110700b003400c007040310b010300725113283e00c3c1c60100503141c030740f104500100300c07580c1098030400100134a075a00101e15014040540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 656379964 1250 656378714 656378719
    0x10b030108070e070e04020a110610080619090b0708070f080705040509090307140309191d060307031b05040c030c0f0509030106050a1e050a1d060a03080712020c 71
    0x8540c14007001581d510a1409070504405160000500f510b102c0c194110b00c1d00e034060300c195154240604040e2a660341c540d0503a029005080024650780e500754021001c4401010080c111621006440300102132002c3d000561503440382000170216651490450041c0d045503100081072034503500040980001a03135050806c0100001c0c00301c00d5612500b51000d0320421924a0302c240c8030480041d00d544540c1c0002480c01040c1404105a414084041c0400c800203540020303503032041c01480c2402c03ca80e030103400d04200782c208a090b224100100748603400f08000c2d0403188060b450f602e4100890305046c03400c14600149140901450406000f154000304071420300b446150b05510002e84142081c0c0146400c0050102d54003105035400d4020400501c005061441016250440000190203515809013101c107002c0000503641401240241141c4401c5da514124129540307032a1281c03000030308800da02903403400c000b00104800500919100d0320584c042845a0a02030001c3c0c141294000703810b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 656381214 1250 656379964 656379967
    0x3030513080c03042c0f06060417061008010606051e07050601032006070222020d020c01090c0b040302030d050c0a171206030d090e0c0c0d0512151c03030e0f03090405010b 75
    0x26600103403080781e1a0000c5040709254003690ba0000814207901841d4820209682012100c880324000802c0701c83c033a211010462030a543c86003c010700b60b604510640000420811041d0003010b000c4190840d0755602107c040d180c40d51135120b4070300d00b24083e0810360b031101c031090041c1c41440e00d00840801c2d00805440741401c0240940000f1683e4448222042403166410f54603131009403242c1c1240c04903410140115142c80501c00f03654001c10f041401101d021459403c041070341802c102c142c4084039801030050943d034412840840340c541143e00e07000c1151103002c2034a4002102c1c140c0c05040d410300d000d2501d0b102d00070f00500b6001d40002503d101c2c065008a4124031881d90300c8425002a0703a00d03070303087e0010381e11180d4000d0624413600f800183c09009080083d41d005500000409260f8040c1403001200d881b01401d1386443c184c2440a2a03022000c1080c145403010360404802d00c09000381070001d4003a804075803c41c1020303040d04411619410002d05010345140901c0381d680501210071606 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 656382464 1250 656381214 656381279
    0x1a09010c1809180b1e06060408070b0c03040302100f1701321f02060703050c1803030706050a020301090e01050412270807032001020a03030513080c0304 67
    0x82103415650007214441903d500000b1141a0302c910824196944138038000390307a10b0205108420305103901d002d81e82945104010403030320b280480581c0c00307451580000d802e81da840c00400c0c41e050342c0004c00e440101d0000b40000030143c1c1c0c07611070000b404505603c078a0340029031418001c104801588030035810145034030042c0a4144031022002c101138020011080c40e0019080d0007400320511080540c0c0305401d000302c1c607030002005500b282404400c0d022600d00d902d030700b0700c141c0c161340c0d080310b00f4a00344005108010880e0fa00c03440f440c40b451005015a40340c6000e648503102502c0040720840c1c0100c0d000001001140040c0c0306007103190003148020062400e017552000081000c0361852010001003500003c1002204c2d07005061014070100000c11042d41e403c0718075240c000500c420b43e502d08400c0d0381c50180d01983c0d03c2101d075040d016400b0b02108480c41d901038ac010b00340548540100031002c02c0350320005000c48000c01003a00c0640007107031a2883c0481ca194104041c0502c004014440f074501c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 656383714 1250 656382464 656382497
    0x509100606030e0a0b060f0d05030903150f04020108040201030e03030f1603020f0711150c062502030904050903040f12050f0c0120100219030b090105060f161a09010c 73
    0x138490000d50003410025240c50f9140011443c408010780c0c55400a8510104002c010000000700030480c815070036940b50413003a035090320710020201c96428010a0310800240158821841180d1040c03050400140c54500403203601c2c51504110342074040d0f007100b40244202d10b488070407000000e101519056140048040141445000340140248840c2d4800844a4030359958101809a01c030000c0303040f5211024420110340c1d541d030548044060001001003407920601600e80078071481c5d10340d00114079015059080c480141002000041180004d110205621203000c4028004000e021620341009205040c42401e00000d460286081d500c803142886282e41c00610303400c4c5021011880300800604400128104281800e00d10040d6100049550f400d079089842a0b44658450341c0401142c5905018041c0c2c0c50307801e00486901960505c0541c030040c0380c45009005801c00074800391001100c0755900218140f0180001d150b4020070410042018024400e420300054107150100d203800c0400324 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 656384964 1250 656383714 656383723
    0x201141306080603190807061104051509030c0415030201020622080c2e0b0d0308240a03050a0b071d130212090706090503010908030a15090509100606030e 68
    0x25900a10003035100040265901740004031a0605080103903c41000a01c0e2800d82540300c003504440741450440311001e0301c407141d8151070a80307501400039951a0b90700c540002c0242c000d07000d8180d00d031241000d5900729031980d01440c241d540810f103504441508510000e82014002071040e04814144080d034074040007034004000e81540c1241807207595070100c00d9030f01c0c144502e11094403100e0301c0d60341804900d0800030104504000100348100310810a001c200440702100010107000950341b000407a80d1604102c14141c80d11a6190000e4005051540890158181c40c4e20950300d40e0803040b074036014032800303026003540729290f85070040f0001000e010a4803c07900c1040e001d8025942108004141c1c82c5550481c2c6070100ca0b0401c1462510f000c0030b2a0b40e81e8941c0340a407000248291000289900b414015001e8460b40140d5032030031903490310f10741c400800303440c0489022010014000501d03001144507030340c01100084040d146100060f45000c00341ca4141c0d0043c010185803104a10b8000000309 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 656386214 1250 656384964 656384969
    0xf0e0306011203110304082103060f0f0f0301180308100803030a0903110a0c1a09010804150b090f010e0c0a17060a09020a0c0204050f061e1c050a02011413 68
    0xe07509208500c078241184c801e8116402d0403020300c400280482c1c03811000a8200c0d24000954000d00f05050a00041d00c003800b00f610269044101c0030381410b01c510782400e075540344034400b904020b0382800240001e400e5071320350414480c1022140d400c18040c15032107000c495100381382803030350001245000c0030295240300081c0b5008025070349450000c105881805898041088007040701e801c101141000351000c04039200354226003c0548075112a641d410099a0316900146c48000c120740d902e0f218500595106002d15640a035a55405455039940d403600038069400c502e5802019030500001031203680740581140b10790351040c841da10189610503010042030b101214400d442d074076008049160307144d02e50880c0602c14004101141150791084100c200c090080301d091040d41c03690030040194480544809030408181002e01749205024102d0101080380607100105105070780703002a9192000e44e500300c0b00c5030444444013040d90392042c4820015000b03a04001d180c01d0b040c0415440324282407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 656387464 1250 656386214 656386229
    0x6030503070b041a0103030522060203040b0906040b03180d140f0d1e090b0f0c07020904030c20130e06130f02060a020607080c07030203090103020304150e0d0f0e030601 74
    0x610004003000075004069141c503c24400724804e558503860084d10a401200c00d40021000420180280c2080c14540104450b080d8001d07528003800c05040c08650307409200803d410510802002038140d1006000b07600c20301200309403041c00302c4428800c5080100d04aa01c1042118485940d80c10400c954222000070709100421907980070561000c0c005040f21074031130444052030402c4050748036807a40001c05054450703282c0e58201d0341c0d1481d01d020903078410b030385201c0702c81d9041c444580141480c40c43d494001d8021305201a500e030300d81e42c8003941c103d0003c0034500c0e480201c1d41191101e0a01160140c0002c500c40000e01024007842c40181c2d41d45c0c001807800001e01c066001903018022140703070076100d180d0080e0085540300085103001c0e5403407000f905c0c074400280c502000100c045000300103481c0070651560196290101400044000c0d41028206581418070a90b80d45074100c003034070030041c2d000c1e9444060040740a10020241c012503000341210140180c1122840711076501007212810b4600700d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 656388714 1250 656387464 656387483
    0x305160218070e0307050a030b0406090510020d0603060b0303210a090212030421030909110912101d03040513091e021f080f190204060e130603050307 66
    0x180001120004804034107500703207292405001030a41c1c40300d812403001205408542e0500c0d80d030010320000f603101e44005172817428104085000101542c0000c100341d80070303104488220300481128403c0f68002800039480340c2d40c40c542002007014500440081c8d1000300d02840c02d04450070707005211140d0102030b40c000e05103003600181c08019281d000156454024103011155002050450350380d0b8007602840b500c10610424400383c400d1721030015041158141c2e604185a85403c0040001d0f088589410901d000107120100182d1914111001500700d403c00602d0b52000c856644d0003220030803a6a8100550401c4501525030400030494040f64801e0300c4000b041203002c1920001000701120040c46840c400c6001c4850f1360710103941c1140036000320b60191b402c0031040a050a6800a80644404540500300203131044441a4440341d0201c0520751051124031307420309943c105e9001d6000748010456040c0080d1503030828001e501c0d443c55a40404001480c11602e40c2c9591b8011044010f209025 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 656389964 1250 656388714 656388757
    0x1806020d0315150f1107090501090e03070213090c05120a140105060a050f030c041514030102090a03020d020d0602030a021201362a0305070e0f120304030c0e10120305 73
    0x1050003a800d001d131110098444042d280c607210b0028288c02e1007121016810500c486810042c00300c219032202d58000c11006030000184007941c060802010155800c03408201c0008187e16821007070134625592001900104940d1302d0300c06603000e45403401c2d029583c90181004129100c1d00c1298064407001c81e0a5030152800d43c000030319014942d03016903001402c2110007010600000c400300d0a1383c00680302e4070310030800e00c401e00d4202d019501c0a281d200200702c40800142c1080c84182c540c450024121081610b42c5498880c113a910a07640100065400030705c800c045442e514059000d49440014480790100d04140c48120450204001803102c00100d4044542d6400741c2c400744008240101c0c0c1d881540c5600f10a4042c212011075120202c2d00b040005440c1603c10001100700f0070380280001c040040c18014061818403a041d00c0705907101c1000088085800390070810000d056096036071a040c41c0c250500d188001031644400c0c5004200e0b254003000036040029503101c01500e804074605000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 656391214 1250 656389964 656389967
    0xb030d050f1b07170d05040329040804090617030307110319090906061814010c02030609060402031504110409020d08034209071806020d0315150f 64
    0x482c910194041c10324490700040003031030114880d402c8912036111111501c0e0303802e4440c0d80350b4449040710400600104800c0c40000c1d40c0701900b04118a035940e40203803080b6059656852008166000e580650012800b000034800c180613280280500c0300402d10840340c400120360390317404050070311360a1010464040100c0751b410804e0768081143c0341e80c544e0f0a00b02c0404082d18480070f42c0206448a410403102040e658040c1c2e50f003048140d01c01d020107000c1854107202002c81c540d81c0f0740840c1003024100701c00c00540e90400c404d03800341540401400984c01c081c030402d86000405000480a80700c00d0003008080f030800b0071034099407941a030740450b041201e03200003a2098507001d0000c103011008818041c4142000001d285009a4508105156001c1c11441c20700b1050321151040d2880d0404120a0315041c07422001d60484040e040420111801500600201d415a001600140c6c01121b9916005605000b0005894010354441c0748481c1031071a402200d01f203083d80d20003408140800050000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 656392464 1250 656391214 656391217
    0x1031e0e0f0307030f18140d0213020c0102030115020f0613030c02090411030c1c020d1b12030e0406120305032505090f10020c011809050a09060f0b030d050f 69
    0x781040819695030303000d640350103008800c5403450f101c0050000400c1d10711019030001403d0940358800d003195841d0510b0b2003013000c000201041203801000060100090102c280050100f80740e1080016840750f0400b2644100d4170440b0541300c1c11548549104c140045000c6886e9410078a03000c0084403002a6050a44028552080003908900d001d8200b000344280080a0380404008600b81c0302016401020448810a08113040301c114080c1980703280145411782071509518440c141358900c80d50321218221000034103038045024440c821100404256102100160148045030104402c7d410319081c2049110040700c0102070000010201c3e0441d00103444030300c3c3c60904800600c449021400004003d50400c80625019948107d00e2140c03c0c5004480018070040690041c014050294011907c00d4003c0309002e540711880030002c01c4404c024003d6510401c0403a1020a207020b652420500b1200c02005040c1031921740200d15400d0303070300402c081c07840030ad107480c1041c2c4030061240341d403055 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 656393714 1250 656392464 656392483
    0x150501140f16030801171c180803070b01050a0b030c040902090607150e0706020708061b0f0304050c0a090e060610121a01030c1b030513030f060b0f01031e0e 69
    0x648508109040405138064101c0e4140c5010b4903031020801d45a0100c5951f441844410450b2608140c495070a118030499810169881d104004804039503142000f0b415540650401e031200e40422005001e01c0c28040710b400014003000c04918558940258003108600807405840720319600000d1300c03000d42e9156400c1e154250b401041e0000312603401500d550091030701300301140d614050042e0004440d4000700d4061b044840c00b0014080913034a901402e01d2400403c085021118810711000c8110501003014511803481480201400d40001d070810031640340d1544201e000714107003164043d4001b07010034090b401c1101038038100920646c001c03007a01e42000309600030022911b0409490a00302c40007000e42400e04081c1c8080009030f81c08001200d84007102d1784c01c81492a444070402d00020f104000406103030f1650750031400b680d42c8a40c1c8070400b400403483d040d00c8894a51034080a24607160007004c034501c009007401c1015081208058881040701c00e462000d199480400c0d43c0e070610700b401240304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 656394964 1250 656393714 656393737
    0x90607020c0d02131415010f02100b0d1703090c0f2218060b090f040308010303110703080f031603060617060409022d010201380901060309030201150501140f 69
    0x50705c183e00d00d171001800301110700c251965510f41001c9400e50142c2007540240b07019901526481a01c03d61040c09004000304180d04005520044004200c90b0b514115925200400c42d0755a414855822803130071041e500356a100f070300d843d020800141e451401958444450101284080d00d40d10420401000000300b00003595100a40721000c001d0f190f40b001a0030f01017107441000c140c85003210741140080894008001c210301d9001070021070301901f401421011008110340e840b90b120380d5803000c0d5400082a4002e1904080140701400d00a807e03440e100d00c00c01d00d810042245468401450007452504992162205001040385030320b0b6a0400d402c82078000d4515814a800540c078002d000c0d00070a524556140790011182c0c0540c41030041244001c103656940c54054002c080111b4546450351014107020245500c942c0710751aa040c045008201548001940c154036007406402d4801c0a00020100480c6000a00180c1e0304514107010690032008034980f240d0070351000e4117a602c1203a18240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 656396214 1250 656394964 656394971
    0x1401200d090909050c1c050d03050105030c030a111005090405090606121f0c030207140c0117010b0304081b120712020a0302152206050708090607020c0d0213 69
    0x1140094640c40c5a00c89a4500701c6039680c8404040448070114001001900464410344651402c011645034044526846424590b00c4d03a0b0b83e90302e4a41c4982684003c6a101c0740100240d140c14880c4090100d8181e0150001c400360350380f01244d642841e0201ca210b1854940703404082841001518080d880141003044641003035800243c1d00e60045490a215202041d58414190000301e0b500346040140580b034040f0030040e1850704040c1074916055010150f00b40031450107d0f0311030340346001458203c00640b0080c405140018003403c050246102c1003013512004105c1210b684044951164000c0d06264450304201d40395031036170840510781181445058115655042c0c84001040e42600c600c08004420b605030f0002d070788036181d21314080c0258215101d21007510107000265a8070003c0d40000c40009000103c04040d0030044910070368004c1c0d99001000700080c3c02039403964102000400400080c0b0700400020b60b18414584072500941031640c070201152510350b40c0c05040d5206a4092 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 656397464 1250 656396214 656396267
    0x110c28080f100606020a081c09020d12030c05090d0213060b0d0501090b0a0e06010e03030c010c0309052404031d06030a090b07081003080702130504050f0606010f091401 74
    0x599a0b10500003408582860801c1c0000c0c3e203400090f0910445500018003803d00644210660075040e65410f040c200740d4a4002c20300041ea248580c00d041144100c04000270001c40e00f1004040300d400141040034410100308520540e50b40749403c01c1d0255040340c40741000a44c030043c500241249500958240c1004645002c9100481c0c000078141c07602c0106c2040301c51418020000800400e100303036004030f05d842002c2419948956402d50b03d02c840a803c90f8940340101c0b00b0142150752254651000039540c1210b94200300e410b00050780500b00f10386c0c0c0c826040950319158401c452000c1c000400380300d00407181181c0e0365004004184140b10007040d04d500c8c2e00d001c20062028000c2604d04560740440e403000942c1490089521a00a11800f5640c2c104a030650b03860742941d0307000c950140d034402041028a02445403601607948100c4c0700d90040d04003542c2e07000600713280c03000180030705044c0500300160340c0c4010350000c04041128181d1209054071102900141c5101041011444001e03a80000b80b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 656398714 1250 656397464 656397493
    0x71b0605180f0a120503010617040606230f0411040b1309060e04141203010902090d12050c0d0309030c0605040f05070b0a020d030e030f07031202030406050403110c2808 74
    0x3d020307140707000345403e4144d10648542110035200902500000c100c0140c01101c0024902181075031140c4152070001c1c00c647c480d844800f1074000780e9004c000240c1240c010500c01d00f02260f80c800340000685007402580d075803a0141089001300e004003854020080740b18040484a50f4810005000842c01040130580b110aa0020180101c9050340c100d04114807114410a0010b1180044103607a55490b04690804103158041d40c864400c0d213a115070300c6491403003c107804542c0500d403d01d0036105c650b910009025800c1c1003956902c42c4c0c500f030500c5c010024001c283c1095414400c0ca07400400007425645a01c2e0050080c00403441c0600588a12640443c520307007060000c0001c0d646c42e4084480e078041001e411000d65a002c0c480000715007060100c48094034440000c2e021107440780c01c111030500307a80120b100480c0c01c204c400381c0d108c0d0303258820f00040c580c000055002d00403918000c0c0254070001004520020080b5214080d039010300c4d2502d406485601000700d01a04010058407035201410b4207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 656399964 1250 656398714 656398723
    0x3050403060b032103070504031506050103060509040803040605040204062d080a11090405011d0304030c0e01030218060609031009050c030706141c021c05071b0605180f 74
    0x44400034078102c094034903890006140641e16044c51540d05500342d44034041e11190700013424400a01c02e00f8400400090b842400c6a00c002d81c5510b00000c80310b103410001020355541d50310107401b80b020030f0184004218000700300e985c01381e0426130100310f54442d440403030000d02c0c1aa100302c40c03200d0080d1041000702d050781006400340c091014011007054556440d542c42d08040400100254407912101505081c2400442d5008c0d02800001901d41c5060720902038000070100e00c10041d400010b82801008000c900003405030000f0b10740d01001d9811540800c2c5d000304002c807003040c44449000001c07465170f50314044404800d005030942d40880c008888020140201000454090141c04c2d010740b060708002444400700c3e005503035000204c0001c814a1303490703548113507080111240b00780c0c5615903413403a80c00200803c090300c101c041e9a0f6001040311504a0340702400900400102c000c0004489006128880d03000c0d8003c1000600d64458410030704501280043c0440c007030140441e40d5509860104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 656401214 1250 656399964 656399969
    0x131b03030e01110c0a030b1003020a03150608070501090605130302030d05070507151e09030f0f0b100803090402090303090405131a0610212406020109020a0302101704030504 76
    0x2c0b03a219800f031200c00030a4072600580304454008808010400101b8501030015130401c4500b40d02c0318515481e50042105072455030400c6d41c80c00101188108010105c1c41036600500183c009080c0090a100000300642482e110700c500300100403a840d804038010304981e500a55000342114040d003020100039105030480c0d18141c450303010304500001c0386180607110302d010f000d0641d2a00c2e82d4071081d5180b1003001d100b40d1080703070400102803000b02c009400a012418154000c0c040e8550400b1180b40c51248098014203014803610048020000000000103480c05424121009625410300c00042881c5006807000b80e98040d0404c030611201f0307242442800d240034090a030b01d28000c034260382113188200d01035440c0340c0c000c13202011007982a4410804600014106a280d201b0b0180e5903985006030380d4141485000c14520074400e4a04404113054075004000c180000d02202d2403035000154048290711029020b08000014040100d114039251242443c0044a044a509080c10001d11981050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 656402464 1250 656401214 656401217
    0x1230105010e01081303030207081608030a1b090512030f040b090901081b0609011b060507091703070b100b070308010e0f04080304021318111305070503131b03030e01 73
    0x1904030314403c0d480381032003510454810034850441d1026644c110002e40c81050280c400800c00e00081031002951141007500c903028400254481c18891540303000c41d030101a440030f40d00d4a244010070800d4100d075100c022a00d0031a50324000c100d4460b01c26045104840180190b400c0006011400f20382a10240802100c20f0360705107210781c3c85800450340e558180f80c00c264200121040c03001240f405200601c07941d2010b1405607103010380312a106908a84480e81250195103c00c00c00030803541c4420140b0060091a5006070422090000700381ca034412410054001a101c0d00020f085c1003c2e011140014060800c2e420307034031005030234000c10700c0c6004c0c01a0050081c0310008036110700d410140700340c05190016001450f40d10303503900f080070700280d4000b00311500391540e0a041010085526034036006000340107901d40c082c1d01d101008150141007503240ca07424548014803d0740c99009003a01e034000320440c8500c400003101e080c00c490101d0000440180001c13720303c01710826a200c104021a02c50a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 656403714 1250 656402464 656402477
    0x1d06040b070e030318030a0204020f070b10300804120b0901050403050a050c10020301120308090604080a0c0507091523090601030b0d06050403090315021303020d02030123010501 78
    0x1840300c1242d0400501c00d000d9490b51007840b1000903402501c82d01d11250b42c005044800c0400745034081782c00d0f40c201c1ca1001406d4035000c5446024000020003040d4054603000e411400f29007040c00f0401002c9120b0f04851007100502100401c0d5005400031441058109003255161540e44190381c0420302880b40031030b80781c0c028001160f100c1105025460045903d921081d0401d01d44020480b480e8100100041052041c0d014160141070184000c501034011034054850b9442e15050140c50804040d250008543c00300040201040302c070020382c0c00c480400d140c1070301c11a0684c05d00c00d290081303e800c41c501300d524102002159000e40002c9208403404001c21000100c1c0103d411513161510401880c0c120340c2c2500001d00d19071007a8854007151100030324503089140c40d81c844100303c40d805c880c12008161403550500038844802d03214203425251100a42c035005a410307500f48802c4031407200030b0040e14003200240455a0a40100605007690130341e03d000a902c4404000310741c9028030171039021818 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 656404964 1250 656403714 656403721
    0xa0c0c0317092419030b150a020106140604050f01140a0f0e060a02250f030c030302010b060f181503040b01030312021810030e10050f010b0c1e011d06040b 68
    0x80910b03c0c405800442078101d040c1104681201d14a0a054151070101a0b5070490340440e45d075042c003d0341654090000035a1103441e4a04041c1c06c403040354002003540f0034400814501030b550310045605980701602e034065600894030060f02c4145016459001010000c503034a100d42d50300c244107010780000d1755074821443c54480140441c3e031181008840060300510000034900c480404801490f52640030180c16103580d6090706041d1205c41c1d0030440e00c4a0040d5030406c14550709022302107032190200c0d001c6140040000a00103540305800b4044050001c030b0010f22855643e07200b03100121a0b41c00619541c034602490252030210702404200c011480950908400f00c1440c429204c0100305d101c4902d00b8034010404101036010403854401c10144c80c0c411500002c0e13800d00a0000904c070003040402c29041940e190512024141c000300c0030301c50107000410780782d01d000403000070130148001c510010041081100b4050428420440603441e5030030031201d80e5207000540544100e0040e000f4182031386 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 656406214 1250 656404964 656404999
    0x15040b0a0303120515030a15140702100c0c0218070206090c0d032703120207080a0f230d11100b030a120302070606141011030a0c0c031709 61
    0x91140030280c0000c0e0141040018841113a10030f81d00700740c48074010003000340780301c000900d00b124840003211003400b045c41c0c0e00d09807a01c03400f03807520441076021104168a046200259610042c01d8010300e481d44508100d40315900034036000180603006070803180c080d8000c5060b024240b206584000041c82500c000400400003c104c80883c01d100404200480ca01130320201c9001c000e00b04d0400c98038490000040d400d501264aa0004620070b0100c64001340650001034280485a4403401c840c6e00601000381c000740d413426040c0000c45d07100701d035002e10074030101028031002d1510b45081d02910812030a035021542240003200c0181f001c20899005101c0c00200300e00782d480d03443d1400c0d0141d2100d440700b0002002c0804000100401e03150060030f003940d503154001078540b02d901036081012a4007004900b0305108803ea1306101290905e0074803815210036042e44c078400c4822500c100301c041e04480d0100021800c90710b0055400c403001c2103010803c0c400c1901c02c2d0313126009d0a40305040303148a514444 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 656407464 1250 656406214 656406229
    0xb071208010e061203120f010e10050d120c02220b06090d060903181508090d020d11030d140a0b0a0f09020a030608160305060c04080601031101030e0615040b 69
    0xa80c24001035103259200d03401070103180c40070313528010b074240424030003080040d5694410b00e03c550114400c41009500d0241030049805000c0c225401880d811346061149445410404051a500131080c1e10f010894640880d5092840400203501c40100c40c013030300d03940c1c448840710b00112100c00d44c101b080703080c1700003048424420075500903044680030320040041803441d802601392a009007003000303d6030b0031000080c8000e0041d8000c00c4400040c0001c921190351710102241e07000380c1c908010503821200441c080c0d6a6080c6028000801035400100710f41c9100c148291030b8580c1c10340400f48a540103400c0c180c00110011550810002e240c0700100d002460142864021107512006803214541400a800b000e54010800c840a06880e69400142d1040400c64500c080f0851181084001e00f54548182010406056182c0d4000c060100307120019001c103210341142d074400d4038036074010690300042c0c0103821001c1d1148298000c000400000c015551600ca044070300403201000103201d00310402941 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 656408714 1250 656407464 656407469
    0x13120309020a090b0414102c18101119020102120103061802100201051602011b082a030108011401030f0b040204090c0803181828060b07120801 63
    0x80016040100a84000c1303034414800520090320100d00d403081c4064144980a0988401401744001a410080c104001840c01504011420380410840404004400c2684003801c50381e100c034406484500c4c0c0440c00c00000e02c001c45451403c0c4aa00c07120040380300b0940001405039152030700d002c1c541128074810320031500c40401d08030300c0315403607401c54035564020f08035440d5980c4001031040800740560740d00d00540d582c40d4801c0d8000716081c90607402c20510043d0501c107a0065a051003981c0003e0b103100d02040300c40c880c0d2468078003032696a6802ca0030a0444076031317016040e50403000220350394804140c02541615814002807096280c503070880d9440d88800d21016080071600120400040c00c0c40302e916801c00d0008001281c1c85031a0303203c00201d1aa581d0251078a540001401800003012200a4441d48000c4407001d4080200516118140300002c25441d00e002c0351170000d8444074101c20020706090981075003000019100c1041d15650f52044406496140111401d44001c511070110b0905 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 656409964 1250 656408714 656408719
    0xd0615120509060105150c0a0203100c03140c1b0c04180201170c0d0c05120109061802070c09051317090a0b0a0e010f02120d020316020d05091c05061312030902 70
    0x3142c041c05100e200c0350044e015600403230280800380c13000b5942c100440501050b80391000551140d240324050201d4030610741188002009404212003001c80c8403d8402040741140c602400d21408550070f404d06241e400c240350f1061400c03c41c41d8000daa0300c51200c501c5032003a210704100b4030003c90315105006084030642100f40c010005003c10040329001440076002a0400700d003015a0b0700845404144260012014682c0d5040e08010701001ca1190800030700c00410110b01d004801e4a03a8030071040b103030050742249511100030a00e81c084e0703001c040610581100c0c80d0141511940003921965021f84801c0340721b24800e901c00302c6c0c561110012a5142c0302d240c3c440550303102503038006548001c0441e0445040d8000c100e01c082258004000030103c1c181c41100c0141e1720302e40568212482c6a040018004550081004c0d410040d0008200c980341c80c0111403250035a01a01c25515600e00001f000030028050142404091703030030b205100c881c8921841d4206a40a02000100c0c119081580041e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 656411214 1250 656409964 656409979
    0x60b071101180504020d05070e0d080403020d030e1002010501080c06040509070f1112090a060201020a02070902030a0612030206090d140d021e0a09080c0108040c05060d0615120509060105 82
    0x100d0342c000d5041410010706840007420349656070740000c0032a0000e00781c800ca0a03444000300100075912094112060600b1181d58440c04000d807280c04181c001d6010080c02811002c80103c00e041c02a810020301c040003c0c8403200a59107460028040c100c00e1140c1034041c442ca070140800c034a80841510203951000d000300d41c01c3c2e42c40c1d01d81101d481203444101070500c003410203060703094036042c40a4040c0044003401540e0314032041c030234440341c0d81107680100210f91051050122160f404180d200c11180303030f203034003503142d03100c1710100340040c28240d000c4c01400d000705090750201074000c10b90503c1505103905840305490085010743d500700b01480e516540400810584281001c103501800305c801401201c2222003d0302001303050243c1c0001c02c0312001c83c0385001e0801c003d800800c1005940102032800c0c00aa0030107030b0f1205802e00841c000c180c4141804556850100600d9010000410001c1e41c40124100070f01009401400d69003000d242c990700349000240300d100c001030114104e840142500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 656412464 1250 656411214 656411243
    0x30606120b060a031a0414010509070e100807060c140106060e090a06240e09070e031608060a0b0f04050106180e06150307140307050d06091b0f03020f03040501060306060b07 76
    0x891724540001d0040320380a1000e00c080858040903c2000c0c802c1a81c040109603441c109060020748000c0100805884041120700384090722011925000700e806604000300000224a0a48085c221020712103801c1e42c0b030000005101540140422020181522946940d48a8410380c05c2581d105000e071801c045c0c5160403c540c0305421200e00e0508844a14000e4071107804500002d000d03070420b9501c0400982c481c03001e9401454140050100b03401c0d45c000d25844207152050b029100d0500902142d400e9a031503031082000c1c1c0781d0140000c08900010010011907840d010040d0031801d182460315656010b4000c0490a161180d0400e40078100c0100b40a40075480040c027840c42c4c0e4001041d940800080c9845452400141c001840c01140982c5801c5d8448040a00c40c804650441c2d020701d00310b40c1070107074420b82600d0890304041e400ca65032800040d2400b0a0200360080e101d2064800314041000007004140403040d8019401d60b4840c0340f050007101c1d0307510041c000c2805551405091a4100d6401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 656413714 1250 656412464 656412503
    0x20c010c120504050301110c010e0a0507050d02061b0d020f03130b0702060f0406020d081b0d09031b0c030b090c010516050703120804020907020304060c0809040204030606120b060a03 80
    0x40381003054075403400900d07003034407900400d0941e203a010b4444505400442c8501e4011000c0c01803640d490500c0e0010401120302c1d4542c60365a142d5841220b00401180c0313018020341d12000300301c030700602d40c8136441451100ca40800655a038014080c000040c001c030a4150307201c050110486900e4140410764080303103420690300100c298061941242e010f2010404200c0d0628200050002003025401403d100c4404200140032058001c1c000c07a55001c640c182d2140007000311056a003542c00303421001070200d14628003030719500b0b0510139090001c40005002420007522103403110560348200c00080d800d481c2c482186540d4040c401141c0e021a5041c080c003449403013070382d80b8080b80f02c0c00b4100f15078805640351079008903405071914001c0010000010801982480403134950040711910003180340a26003c402024031003105001070000400050070000c0761b0b1183c05031400f45410040c10440c250743c40c2c00e0b80450350321185c003c65030000703801c000076118a04210000c0132130f81c1140844c01c0c209120b000c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 656414964 1250 656413714 656413733
    0x20d03110f0c0c030a15061d0a15030605090a051c08060d0c09091a15360108160f0b070f0624090e280302070b0f030601080601020c010c 60
    0x8442d442c07143e0f1002511660701000b56240407402414030f000703200d0b503021052050750711603000451388249448101507500701d01c80c45154804104440020749410610006102805039440a4511401e040501c08030080108035042c283d07102c2c504807004c02105124000d60003104030720a2021502001c0002c02605145846080b07880c0315403024031242e6199030649040705c903004410744001c000341c003004540f590803c1c501d94208000c0d500108084105170b0004800300b03e003c10083c8840040b951010088004105104180b02c0a8106800c5507031554542c13941ca00c02d0109041544080c450002180e41c440c2880000780d62a03c1d03421454098181c131146000007004e2800c0b151a03548601100e17041c240c4e1a03040311441907100040c6075413440c0070590000e84a54403620301c10b94128002000070100102849010400e06038010103400b201401c0c1030b0f0512409038040e800b007510004038505801c100c40011032082c203090b06c5a0318541c440000480e03640749116002408503c07840c4004000c10074520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 656416214 1250 656414964 656414977
    0xc0b010302121e0a12082a04081b03010b090c0409110c01051603060906050f0d0c0e07031506112a04020403050703110105030405030d0e100c0f020d03110f 68
    0x20112034601540003031500c9070192401114a090700804c1102d801c0020004c07040703e0381c4080d450440100d080601442d03c05030820300400100107040d042c142404c0126105403002491540700f0b451442071110987c51074000741c211458429460021038420a140c480d020f0ba00803503030b851900d0704180c14240810001d00901010090040050180141812090151a1245050003912048000386881c05801d8410742d41004170400e0519605001035102c001c10104400011508891003540714140b140c0d60141d0364016a41d4044890204440c20350550010351014503080620100751340c0c2e0b941d0868041c01d408a01403044c0c0c00c500c00200c901030442c003015251740c8032000100401000d04000030700b00e031320030740c01141e240e0048201003040c007440000301c4070001c0c000c0c2412840c62506030340300703900d80c8518030802c0c180982d01d030742e10080004108613010000170800810000080c0031140078240c0c1d0101031081005105180c440c8000600c00d004080311282d05560b41400e0407080100d1252917002807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 656417464 1250 656416214 656416249
    0x12030903200904030e0306070503091911060a05070506010e06180403030b063714250b0411100801120807050a030921050a0206030408070b0c09100c0b010302 69
    0x384240401c1c0c1d51901d4449015034400e45654020403070640c140b41c10702c0d0000b41240d090000034010020903100c0450144240102001e524a06251034507049038601c0360002465001100400c90000e202d81220080c440e0b90300030011a8400c0e1390751040c45008441c00c0341c10301d8001c181a9941c0e2502e00da070100a507082440f80c00d010403000c025002140d03541d0802e164a403039000b050f00708115078040755003d15038400401d1100003420020744001078401098000d45e07000c0204000346945044a101c81240c8803500064bc0c01c1410311f50905040203100d4055a003038a4020b001408401c45180c005080900702c266a01d0340a29a840c04c2042d441c500000c101c10382d05207004000b0400045c00038406070b02c0c01071107502e072060168103198001490036001c4482c841c15802c60080d041c04604005a160b010941c11621195642d0f141e1826044074002d00e4002844081c200061000c139008080181885400640b1003d51300340d40803c0458520103084405400241c3c1c2c130340140302601b40308640f010309c035064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 656418714 1250 656417464 656417513
    0x30d020d0b1203030a06050423041a162a1103010204170d020f07030503270415051302040e0c07020f03030712020c0406080d030b03070b07051612030903 67
    0x89a010030029440c041452002c1d40001040100400540c452a0081d1030192001c03c003000705902024140f07002a610b0345c031105e46a000040400002d070200324400c044800a8030b41c1400c1c10350340104d460030008407401c0840d06c0086004810007070401560000030440c20603410f005a65102d164026480030205505550200004219801840c00a44044020000400202c1758001d0003d0908098114541203900040c1042010540000c140e94110420541040700746452103620b020185022030683e070000d0500d00000c8025004030b480302e04445060714034000d1280d43d4a0303140d08034465400780e14000d0b446c8070085000b90381000c0192201d94809001ca203038101024001a1842e00080c0f0b04032240d01c542c078030f0001c5036603040c02080b070080c40540d014020542491340084d01e802320381c4501c1040666450b2241c8042e40c3c204100001403c040080555408050030955103c1c8040816884180789082000942d2502d00c1640b420254041e61600318544c01d541e03038101d455080e0080d06080016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 656419964 1250 656418714 656418731
    0x6030f0b212d07080102190e030a0b16200a0609050c060f030a0b0105190f0e0a0f0504050907030f0206161208070216030b01140103020c060906180a05030d020d 70
    0x1c0441408000d05076103030281520a5202c01040d242c0310390742d080407000fa40180300011007081c20003071581442d0b41034141000030315400d07008613140c10102000600300e00c46127801c0c441c1345d1400b46001d4100544940d41c00c100400b0800e507800050303980c1020317407205500c180640300210305584d10406007140325006641440c00060300180442d00122900900e002002082c00240790304c600c80c0d080204020300300b060918050b0b1022a00801c8441941424885000c1200c81803a03c10112a00e80441c0141f04078800c0743c031455504140c0401d8010240203c0c50440492aa80800121501240c1d802040101031005546c01d000301030700f10141113509100040c2c9103000040f400400351100e03402c030341e070b40070750505d1714210080c036008819045211000404c0c40c180003040040c0c50701c80c15640d044d0110106040b441004800900c108e00e048138440c0145401e0102040001c9140e50048020500401100b4107101406460b039910010040069100f00303c103a07150150394028100144110074002079443c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 656421214 1250 656419964 656419993
    0x13030f02121606031a0a030c0609080a152d020d0c0e030d030209010932220c020a0c0f0e06090c03060f0a080f1006120302060f0c07170406030f0b21 65
    0xb06c468204a81c1c0a000d204207011450f0f000c030070f03c0e000f00522002400230b19080c1d15003c82003100607601100503900c1d000300c002d800703e40f2404d00340828600010000070b050a403261170025000110080409400c000c000c5a60f144181c02040d803105c0001d0103011113184c0c509042d0021352141080c21b061010501c0b0001b08004c1145c4440c4d400c0520f42c030001d01d05403a00b42d0500001100d007040e103103d80d101c814001c4002c500b44074055840d00e04c000e00090000c00616041c2d15004002d000280a2005940081181c0b0303160740e0744004481d0a50001e450380e4540d6420890b40781d40860344110301840601c00900310785841e10102a4520001d400c9000c0b5030340b10410701c1e080042e8844040100e50040605c052020034900c5418000e11108481c14400141907500949500f40608445d040313428880101d44050003850440da01c0325030013400c2c118440d29103402050560031522401011038a095002c041445244c05010544503001f845892406d084001265182c550206007040900c100100460381e40c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 656422464 1250 656421214 656421229
    0x140a15030b07030203100b0c1f0f11040e0610051e161112010b0a09090206360405060109060f1103030a021314150f13030f02121606031a 60
    0x1080e9598000d80c0d2803814424100c406c84580d400542480020045c6182462020922517100d0540d020100800c208400e00c41b000740441c100812002407178000c0225020302d8000003030003111a080980c071541c2d55680108158031403031024074008588204084030601d006540000c080c0740c0c5030798405041c080c402c9003403002c2684044003107480d00400d0b240c410071458459071003042182ca0340c0003844030b102e200d0302040300d810701c03441000c581035151b00f0070000715a03032031054404183c884050344203140510400c1e030000700b40d400020760700c880e07503501510050b0038503004161180c48107850b07041d6003602e03201e0200c43c182c0c2401915410000c9603440340000903c180000c500407400c1980240c2c0f0ba400f030144510505030b05a20100c108540001c04035920b4a03000c41c99280c002c000b040c1e15484007100905070300c5a00ca00720407461000345460011041108560f4184591802921610307840383c0602102541e400c002d000722038261131101020000e061080e00180300040c5218040400c00c00c40c5c00214511 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 656423714 1250 656422464 656422471
    0x31803060c092214150d03050a0e1507030f0f1805060903011b020c0f09010f0605250b040b060904020a03020f031e100c020d052520040b010201140a15030b 68
    0x1202000000c0c0b108511161420b1004c40c5c6045841c100380e486541e40140c81d5200d01040c0000340110200c50184a81c0c2d0040741e07510041d2050780d020b94580d15450000c0c8400e00119040000c80d800c0300701c1590b0544600b500c1c40d004840038071410080d074201420070a032a00800c6c007075a45592120418040745801441c1650b1810094000f002809442010000e8044c20a0321050046982100422446013040c131800101c80d03a50900e1313550303130201440d4040790380762488810b102c503644081c42800704841d01e581e0a20490046520007000c2c4c80307000c10000c2648041d140a584806040028405880d00b8050061032840003401c07200d81451140e0210160f8000001d0118143c1041500c5100e45c1d5a600a0700080b96003440034140311100034002070450f016036400c043c5100b00080740e040d1501d03c440a102d07440d03508030540b84c1041362400b02c841102c0d455400624080c40c00c0c020265181d5005005080c10003074503c030401002c0d0750340c6280c2001086480700c9c02056070140704000000c641e02001c124007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 656424964 1250 656423714 656423741
    0x80402131a0f0301150e1008060106120b011b0201080721090203150105011b06060f140411032206020702060f070c050d02090f180f031803060c0922 65
    0x11112812000c010600402c2c0204600036410000380b611a410f901048034180c544e6071600222075207131000e0054900b01c5a41054000d44580000817031451b8101d2400340e140d081c1c111041c09051200700c01114030000324284100510b04032000e010043d801400352a40c44820b9182019841d10b01c10a01e542c0c00100c0103040354001d03542e6001000303504040c40414403800b000324410712254940000200006117041001400803801a49141040102d070007034001030400002e261215070721414541e10442d01c80000c144524907010a65801c0981031040e03a20607a20ba1140054182303420400c0703005110700d6881190159400c21400c3c2c0140d42d21400b43c107000d840611035940b948040d240100205010341c000034400d000d02e4414400594542100d40e070b004009070300c9044e450f06d56030410503000c0d944003c0350109010f031005001c09540300102604170211615a25452007047c4030500d40c40d003805031419a0118010445410b0b03508080c1d90310130326a5280e0086054900000c07141c03804640c0184411013 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 656426214 1250 656424964 656425001
    0x15030b340f020c0a0e01180e0114150306041e0c05150319020f030a020a0e0a1e1a0708220905180c0102060f130b160f1b0308040213 58
    0x1103015070410004100e544151804180c00b400c0005041c0104170500c200c04517a05c9641d0b16103003188480e0400e920803883d482c02072080a00d003e040c503501c103030112182036941c0d00c001e0620109180000760180140d03004101111840410a45404546040407065417030301c0401c040060240c4a1018a05898000c001c190f526400c25040d0608150045500f400d84140180701742402d240c481011aa000b408070a03005a41e0384001d10b003074826821801046500566203400000d03d219101003000206061440081105460707960303a0b50341c440070803801e030350450080c0455000101090000e00451404543c205104400c0c01100ba910100c241c02803c0e40a031900240207104a0305114006246003020113002003244c4000000e581c1d000042460700d0501e40c07003005c20500440780161040040d041000715040c1e2078002c400628104000a0280020300365407518607065110314101100354440000c40216051151000c032210300003d40280c1e0700c00e280010101600c0030300c0c07141c40000c00c2d0100004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 656427464 1250 656426214 656426237
    0xa020d05010204141f0509010e090a050f0c1617120a091106040608151f17060109050d060905010f06030f0501150b04030222020a050c0115030b34 64
    0x520344d8444500800303010b000a00180b0310545160401c07101050414039000d500d90301c0000048038040e0345103810300d400003054014840703098881c0d003006100304408461204182c81da03902c2100e09100d03141d240400c40e25560701e0000000e648004001c26082001241810b02c1c0c04803204040440c5d0558040da20340c1c1c3d0f10502001000a984140354940d0000c494841c106031910201410032140104800d003c080c0030104004141d607060005104694225100c0117a0046010040c241175002880144143d20820000d806503100b2114141981c102030800100c00c0c05c9503031941c001c0e1024030f4044803c8c1d501c40d80e0789841d9202905c01c03240258040c42020221854501b01a402c5580d80c41005407110030441040c4041025030049400f1a581a10401c403020319810700302c242070028804c08060a40001008403802c0e600c50301070441040940000c210a41d41e01800c0c0382e990f289440000c1ca60303840e040025010407144010303006120704a84805aa5224100429601800071981000840c1407907405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 656428714 1250 656427464 656427479
    0x50f091302101707021c230d0603020109090501080304170312042f0102031c02120109050103021f1407060e1203071d030c121501080a021c030c0b090a020d05010204 72
    0x3500481c050015160800844075491045c100d44203001060242c6036441c81f968918150200821240c0805410303142d107040d5211201400e0144002da00051210340045080159440344604a4124100442c03400340b038444003102002d444101c10030980020b06c0604418100541040c1c1b01310301c906400007d0034400d0015020004424098544a4110031a040d08a9800000f22844009440b80808402d2480741c9008041d200b000442181400c44100010b0b511600b500158181d80c0b00b1204040e11801c078000c0070414442206503a00011640000600143c0650005005d1079005a1000c01c86c6484185e149180922806503020000800820001c44035440036420303c01310160050441031419031400039aa805100ca40d603071254074105602d4601207010004014490210200d1070100d41c2d65802d600c0d250100a0400ea001d0a99403e01c100740b02c2d465018500600d5254880080417506911503230034281c2c0040c034620442c401d010101d030247c0c1c5c0b64100980501e00c01c0d0005a9100d052244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 656429964 1250 656428714 656428757
    0x1050a0e060907030201180810050406061a16081908072003041e150c05190f1b05030a0c0306060605031015030207140102070c050109050f09130210 65
    0xa01030841e40040082c0200c0000100700f1600301c90302441d0800b40406003107100d010050060b031245031107101d406c10000e122211500090700c624081d0b003040001c2562900303100011460200200d1401070308005003004035200d9408646598019030025017400070014400b80c04568542d003020101d405e00007000081035012241d0149543c0c201c141d100711030800b8241c1c950324022030244c2e01c91100542206101d00308540c000e50000c05890420b00d00d80e1646040140c040c90394400141d40c140500d202e10403804949900c01c2c1c95241d4043c0142d0f100c181d154480c5401441c000600384046000c08100107029502002442503043c01003c0d0200300f20320354a000c00464400c0d0b4030030303028070070180100111211004c03204d0084415444003410100c510b040300310700074861104018500b444016141071308550550140424611900e20a11880e0b101c10054030a4101d6210307040e0302070b442c61035074036150510b05045a000a05810602c800c0905540010b01e001804500880000c0100c40d08080a600d0f588 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 656431214 1250 656429964 656429981
    0x1103010b031b2d07020d030917120706021b010c091d010303020307141f1a01020106081f06030b040b22020f220504050c03070906050a151209030201050a 67
    0x100c501d162a5129581c2c1d0f91402030701d81c841c181035040074541c070b10600280b000c41d054a64018246211440c0b540340190078440c0b140910300c5103140d42c0e0a41c0b2101c400000e25040344070303078840c1030700d0901d141580c650010b58880300712800c0c4155042d1103070b42d44402c24003600c038582074141c94000c0124180040c820220070880c1c1c98115040d1454010400b003038000c82214074140c0c101080020600d0030810003464125444201002c140c00000780e0180d142403603004a143d036281003940313050900b01100480c00e0765010b0050700300301e4020041d0100700d00c040b0075041d401e600c0b1a8002007505944c0380c4820003801c0c0119400d0f01e826401008010342403c2d02c2d120394440c8a0b00d00c040d04600300705600480d401d4004a00200d01407488404100988001003400400c2150481c0e0f050140e46024504262200c125011450080c440c001d40070410382414000c140036038401914807403c0c10704d042480320010001420030750074025280d1745062951040d000314591680a03400210381410b10150400c00c4501c0c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 656432464 1250 656431214 656431261
    0x20060706141e0c07170403050609030703120902030c12120403051606090e01030f03090e1e070e031b0609030d0c0b070804020d0b090309120f07060f0807121103010b03 73
    0x542080000c40201d004c2d6031215400c400b01c070340210342403090300030180300c0e40c0c2000e001441074a0400051560002c0104146482541e8241d6580550101101950700c2e5170b8000354150010b401c0e101090410b084406007031004541199405d800b0b89441028a0b400350b001940c45805c00d1261400c4482c41164140c014002c1d45003032808117240c01d408031001401804020050104901c03030b002418130a10210b000350201c000c030790703242d8180f40079141d40c640c0c054962050f1a51045000030944c40c024010210304900c090050000809005640e2040c103084c90615a40014148085032180d14204909107160100380c4480d0311070308083c1015080420300607e40f01c1001440400c000060301d400e42d414000703951001e0040259142e1040107825030117460042071b0460760100c40301e03081d0400020301c00d809984120961b101e16403105004c07070b00801c516290901140c6e8140204100c07600c40d00032903000c4003031200700082002c6501d0700e0f800700740d20a80c48011101408002c0c01040144034900d40c0441020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 656433714 1250 656432464 656432521
    0xe16080705040303052d120a020406050a050904060b0c06090c040b0d1b03080309030a09090e0c15070602070b091b010e04020702040b1c1209032006070614 68
    0x2000400d03500c80c2d404010100280800d03121709084d040e9941c0201202c1602c82d000c108040ca0345c1801e26a0070020b00c000389205c40001007550f000701d0380700700d40607218690b5450f8a0b1807954201551030794001c0307152540060381c1d0000029100d002401030109824108041d10007420007101d42c900c0e08a84c1d4004a100e039141c001000425521144282100e640c801c0a81600e940140c2102d00c14015580c006410040c0020410041d0f01c804401805004615110103102c0c80c0c4840441d0304a404c5103014011580c0900c003007082d02d20300003010040c1c07000311145403482c04865640300f5040ea08211005c43d008103000342449156003040c0524080804020156422000d135000001c03c1101e802041d240555800100c00040d91a51782103e8180d40c4090300c0c0e40320b800d44074100303940b0070070240d9001d0344c001d04000c0d40400d090340b00b0100042144c0d005070003c1c202d100d2050f0005504c1c3d8058980b030307512010412900340020014029282420082e9420314800d1501204c5050f0380381d465000100d45441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 656434964 1250 656433714 656433721
    0x5180d1b020904050c0a09060602160b090f030a06020a0c021206090703140f0a1101030c080915130f030e0f01020703080d1808042309040b04020d03090f0e1608 70
    0x3420100218981d404885000d0180c43d0350a1050524078404030694206555407000302d00c0010641000b41141d190392300b1120300e4403680440040c404618015102400030800000ca0145080f840052000c0001800e9414000341d87c1d9440e000c0364441c003949004502035041e44002c0d403800914016900384404003401702c914041c1449a110030306400002d00400c1401c0c030b1620b041c40100005021000080110f914140c0d00d403c21001c0b801d50076486500007420940807452252159415500032006a4028110007041a003005103c05005100c00320100010182c0c001044c0c0b812560740800b8001d807a031072014003a0809000841c101e5200050640d07201040400000302c9282c22101c0d440404000066504c4041000d00b2030445040030180503d1400305021410b444104100000000319241d450070440888040c420b181400301c41c00303002c1080c2100003034054100100000040c0f842407411403021a100c00e1502c200d20025004003c0e6841c000c41004003882041211448582d40d40c203002001f0715 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 656436214 1250 656434964 656434997
    0x30a02072f09130519050f0d1d010905030304032d0f020f01050306030c09060d440a0e2101061a1e0d090503040e0405010c0903030221040905180d 64
    0x100b8140d010107120854481e500244402808402501f0f5001070030344800d1a0100401040c1c0e500740d5007001c44024603003402d100d0560040003080c044890141c041c6041138a951030b425400f5296100561402c002c60304c0818081c601180c2c0d950965104142e03031400720f0b940e4014070150034034001240741480350800c18031070301c1d035000164202e01141c00c4482d15841c1d07450001145a5000301e032070081c00700c100c0704400e041c4a000407005c40c8407180342920321585482d1420300d94004880303940b9000c800003810400155020303c01c0750040300e643c0300645540a12249800400e6031250795658144851355134070814840d506810014a407811421100d00f424a0303400c202d20200704404148080b5039002c0000c01924441c4190010560583c00c001640e4407603541c0c0400e0000c017001103900311155483c05107100700c0380e4010120001a6905a8014030703d0480080045100c6c2d240e80e01c10300301d90310040c000080d40b007a03076008091003201c2144607199400384038444603207041050302c0c03003c0621070b07140342c0c401b4002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 656437464 1250 656436214 656436223
    0x903130f06022a0d29040203150408040b160f0501051e0405060c0c0a080d05041101033b100209010320090105030408040905040b040b01060f05030a02072f091305 71
    0x3d42c200c0b25075070351000768504500403084240416280b03255220302c3c240b00d100c030303007400354407840c0250180d5050880e0040c00650f034a0b0308560040190500384400c1c004c00c1c207054003611440358001040c50b0440f59984940c441140b8039002200c0301c4e9120010082d0007020b071030756070030100c05001d0f691038907091955406446000003000d0900310180882e4a0082c802d0400220f0404d40c0c201d01c24a070f440c40c00d240d440010344002c5505a4000201d40211481544a485201800d440c100e10281011041c018a03480d0b00410380404401c4106840b00c0000000c404e11004103802603a100060780d03012800d0014041d5840800301c0d800651000300d17140c2458061104465086030700b407900d02d940c0c1da00c0e46001c0400d4021500b0152049180204100401c1440000b4a0040d4050840c2d240d05070390380c09041390b14040680f81400010030a00220701c1c5060142c000d011080c3c49020b11541c49820f0003605a2604450031001100404040341c141460a250900b2500a090130b183c01008115544601380d0740c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 656438714 1250 656437464 656437543
    0x5011a09010507141f0506100f02061303120c0503010503070f1203080c0708040b03040302060606130b090d061b030e0c010807050d0b04061202040b0406080d080903130f0602 76
    0x1d02408114071107004c07824841240000b40d040c290b8010003100b41000d1000b404115080c50040c8903103100c610324a4060b80040001c100c51b54002e00041c0d94408480c01c0049210800710700f0300420700400002a5a10b0040c1c008401c0b0550711140c50b90324003810140740030071075400700d02d0a80d0000d0050001c204103072030441c0d815416041c28250350701c0302d540c3c21129204400d4050304224010402060300101c40d002940524000d0b802c880064480d9010402c00b4800c1100e110f003c0709040804210560b42140a8031100c000101141819610b41d241c031404d0710401110190401000754107665184d8042c81114094013580004004920841c000a090082d000e885d03242404008505d0ba1031201039500201d0180b4000340051100c940d82e5180949400704185040b440303513003080d8080c0c0090030584100401c43c0d100000414081401003000d41c0d0040000c0e05128140c04100079400c040c205800281d0300130400c0302c0b4000c0605242040080c10b00400090f034280016416900b14a50060308841118 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 656439964 1250 656438714 656438723
    0x315050607080a0e190603140f06130f020409050412030606020303070815040c0f0e3313180e0102130311010315030c09050f0c0a0302031e0a05011a09010507 69
    0x26112001a0184d50000c884004645e100c3c1003244001800402c0144140881c0c00c0350700d0a2012000c28251140f445104491044031110701100041c1c091030b084492994071f8084880000f02252803a0000050303034800d400114403e80c494003800b0400180c09855080d008440c03404000c40740c1414030081d00c900c00500004204030f90f82022a0003980c01110294140100174010010a4202c3d072014101c450300e10030b10404500101580c1550341000e510b1040d0030140d030340a14420840c10240519410400c01c0e03261840d00c403d00c0039100311511502da94018000151034000002c071100c1181d000d949103040d00d40f120740d005104c40c40c81d09400000900503070382d01c9a24146034004e8030340100e0051081c0345100e0940030700d000d80042406240700c5403006440c10f8101c00e12180c5d491100c0c821501000395000c458020007001540c00b264403030343c040d50704404901910180d0700c462200802c0d184600b542c40c0200103a070b40004000b0102c1070614a282c0c1c29164814900305241c0c2400a4614003840340042d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 656441214 1250 656439964 656439967
    0x10603110c01020714190f0b0406140405030304020405060604030201081b0c010c030e10141302040f230f1315021b0318010207050625021f031505060708 67
    0x1100159007038a1081c0071060007151200580d0800d40f40c2d6480002201030700340a401c3c140124104c0c41d403807482d10160041e41c000c0000350310b0b0741c440c40c000100400c1615580d03503425600341141044850140194006c10081d030700c905003401000200d44000d01914400c0200304010030050340c01095042d03004000b0010580034485145540d5840d100301d80058101c0d510f000ba102c40b00503010351100e003000d004042254031440b1201e03145800c84803444060200e078081000015141c00e0b000ca0310b064510703c007810108001c1040030038001580c5c50803e44070b074080e484411514030808109074041d13100460903100c1455040c680003030400c94480c40c01c09050407100c110400c00070074258044070201c1d000111120f1842ea44410b60036200c0e040480c070710b1500701040c3d4100069610001d48281074442c0140081d15041c1000c040c0c48000c01580300d14901d2041e2903c2140150352600b0901b20f08c9046100350605034103000b00002c0c00c803480700305812040308508209002c1611020b05072448540e000c001a17 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 656442464 1250 656441214 656441231
    0xa05070317090d0303051503030d270519060e0303042f0109171c020f1006140d1e2001050f07030c1b060917010218061e030c09030c030d0206010603 65
    0x12040301f1103801c03820380500c0700080b900300100041e4451a070b03174404010b4002200161441005500703a01000c050080d40c0300b035080d030021007001c46030441d00700c0c0b15107000900740d110f00c1413060039900101c5040e500e40c1c05007080d452180780d00e10450205144422400b0103650801e80c0064000c0800c0e000d812240500310f03007107080f041004c0040005141e2031140300c0051540100e0001c2d50b40c00c0d0a109244c0038040c00c1304280d20390109021386025242c0004c2c2c0151451102d005019060802c004140c60300000c2034500501e040b465001d4041080c05414000214001d0700710511001c480c03082803e0411808005a0000e100000240d9554542c58584140d66031498203080c154014030300d95050011555440004040c2c2d0000e0180048030403554400c11a05600814070703080703008071204844104189402d40d8850300e05100101028541401d10842d58070750f041d2078001c1030304201d8103003800000006040d00e1501e410484c88194420450003017040300c000d50002525904184901c900b81506c07070005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 656443714 1250 656442464 656442481
    0x90106050d0605040608060105100801080a080901030f1b0e0111070b0c01020903030c060406060e070507021009080d0c140a1a061c050a0c0b0a091809050a05070317090d030305 77
    0x440041000804c10b200c65612003496584030031084c8a8584124000d600820415000301030b054100c03410500034040d07400c078948844401c1c3e44080c04c61410196681c01e600e034007030128401c40d203841042d410003403500075811802820b000300943c1c1c1c15062091442c465000701d100020201c051710051601c0b20303220200d03240c0c090702901400d946a40c9c0341c00040b07001e404100d00024814881c500849050280381e5035001550580003013650440c00181003084008094148103a601e09000114601078000350340d903030006410315601c0c0c0d0310340000a08100112040c41078001c00b07103a64440a601921001c840c1f60b580400841074051226001c0602000064803555950313000c103594203150286001d00c400342d2030002d0b01e40586440847d07255075004004104403184505640940303246894000c8624188901000101c1076042e07904e200725150300812000500903c60680918424001052a90b056141c10411907985622241e0f25043c10702c00b00c181955021000012180c0600b030005c1c160b20755120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 656444964 1250 656443714 656443721
    0xb0c1626190c020607020402041203090518070f020f12131a1e09060f0705060709050306180106080f0304060f0302340606151709030921100f1a090106050d 68
    0x50103075000d0300c08600001d1589400c402494698032039330f206a5010384481c10030820160b9020f100608020050010702300e28000d4001d4102040710f401143d00d5400c07031100403450103c650840d00c80c03c3ea408070310b0240c03418001080360003411a140248107402c25184458509000e106040248050f554449070911b580441c102c0f2501071024120903650481d101d0000aa58040d070002c8586124034000206194443c00d011400d90b00001c0140030203894122129016408c80c201061082d5a2044005260841002042070407403000340a1501d980c5004ca0181920f9003d42c05981414010401900306400070040c0c21101034011448241d51548460a0702d001d18000000400c101d02d4a00080b9000b21f03100008036550034590707124000d05070f18040b964242d5000342d440b64915801400111620304e002402c0040d44c601d02c4c035000e510101c960702c2461500184000d4804150742c1d80741e00380c111401d103008921340302c078504201354a0000c480000c505009014450388041000109000e002c4040a80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 656446214 1250 656444964 656444977
    0x50d0b060c1507180f060e030a0203071701060f031203052d0a060b030a090506012c2203090509010b07030519120f050108070504090c030b0c1626190c0206 68
    0x1440328809621009560801910307401981d0120f88047c0010320140b600141c0d0341600e550141c0070b00011450240c2c2c100d961030400c0d0398107a59549441010030384400a0b006540258011800c0c401c480304c0d9800301070120782000d400d861050400c10b01d214000e082030500140700101c604405551a0342e00340700c146c010310341c580080c081c5003000402d0200400450700000842c0303020b682580c20301d1740d0381d220b03600500d40c603900021001d014400410b481604411784055102641c040b4548a8155a110106040c28154030840c0071604c509403c1c0030a05082d2610b6015104d1140c180c0c1c5041410384000d411030140d100303014006070700c805000c82d06c00d00c01e0384016182000c0200a00c009200415150301a040034003807102c0300d21a0140000d410310b040d00400c01070681286084000500350340701c800d0b245400500d208800c903400c001c8040c00c128518a2441c055000c2c480381c10118219042620340e800e41c11164038018038051001c0d48010042d0b4072721403a81144e504004400301d07010300c00f003241070140e103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 656447464 1250 656446214 656446247
    0x403060c050d0f05010f1a0708030f0405010612030518121c0e0901051c0318090608010c0f050d0c02102a050c030d0902040e0d050d0b060c1507 63
    0x40c4040014035088000342198644040041c06801c50b205880c2d03044913000d20440c41800c46d608020041c401c0ea4031000008050f0039042549050031607110b0504035801a40c0822142280d0820001403120a00c140406400316418a005c1c1c10219180140580262011040390305a61091030340903948a503d042c202a2102c41980c020013014204000c2c620710588140011919881e0b58012614108102d941a9540280f03249540327280000004002076140340203c050000b071200c5250019000100c02c03000745003541011035424104034100b801d640104c0800c0d002c0c07003900c113141c20000c0c1c1c00605a81406a038604001b400d03202c010f00c101d1500780b400d0f03482e0581d0b070710308941c4010042038248524148800074490b19a000c0c5144800c45461054024200103078005100e05494031034103812100e02c06000034000315146c5240b082140c1002400d400c14008214002800708000c0802c0c0540c502944c401c4890f181040c120103822a21054030529034481c0f02c0d4032600041ca501e0140d8810340003400c98 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 656448714 1250 656447464 656447471
    0x30b03030d09080a110a08030103030c15090c18021c18080c0c0a05030d0807080a0908121909021302030916091509060b0910090513050a0e010b090c03040602040306 72
    0xb1420301c101c241d07002a120400150526408100803600010a0586940e2100209280d6032a42d00c0803680d0034181002203401c0d00300111542c010804a0107004d01c03107030103011100422840c1c0041900000b071505445100180184900a0300d600340d03e130310301290340c04030801003101c0e01d030041660380c081d01002c0c0090030f00b03030045128020418001441004440280c84100d840d40c0c0b20810169a001c03454100000a000c807000100060303c41c84c507080d00100300749804111030034503650f007a4a40c9c020307901205c040b03401d0008010300040705102d0000c42403002c070340400c4a5801d035004034852003599140080f03e16000004601d0075001000030342e0580300e0001c01d4810b03158403001c80101030034004107d001c03480c00e0700c1400b08605e6601c0c401d00d822900440e828500e421078220608c6201507000800005203c040d500000e1651244000d242e550020060300042528011071315208844049560941907032504000301400e0301c44202d01d941100010031015101c1d5a0b030f140c500041e21170398100408803801d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 656449964 1250 656448714 656448731
    0x3061413060f03110f030304240c12030c030c030506010c030c1505040b010801050c0f16050f03030901020c120a090e0c13060e010206240105070311011d10020c030a030b03030d 77
    0x940e000721040d84da00440b04066404080802c042ea41d00450142409010b071814001e440380104022501442281741402c4a00700115180c9942c00d451440070390001c02c0d10340600c0350b04c0759410720074042c00d48002c1c00c042100f400c0100008061050b03500d002418000211072010520072000001003405582d0441031000b80303041c5c988041000380078464030500b50b08010200710044140d1081c1c0717002da040003030710509100d503810380d820120520840070f803000e0054402089030101d083c401140310320b481c00000b50342c9285402c81246014048900070200710014003601001030b40c40011203080340c0c84220a0350007900c8181049619105101149101003000344001480c250040c0400e429040c00360290781e031999544c142000c5601012100d02d0f446054900d1041d525070042c03000e07202c40ea00038503200000c110807a00d068211404041e4901c0700381030141d0078820002c000c0150700c455008605042d4200755400c010303c1d9403801285400014546c98201c0c003040742e01d0401c10354003043c007421014081c005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 656451214 1250 656449964 656449973
    0x7060e010e0a0210050913020315090a1d060f1602072409060c020d0305180a030f12090e01060309110310050106091401050301090f140f06010206010603061413060f03 73
    0x54002c44203d000f00c075030342080c0040e10f0040081c0c136946400036010003009404403905500a5200400c0482d940a00803110749150b103503956541e00c030380420000001c0d4550144040d0301150200d846c502419440003003000f8000410017100754210010540040c6039a01400050b4100a8070360054005200003148140f500144080381c12248000e5440f40ca0307440d500c1d03941c11216181d05020280d00103000c5440c0c040001d01c100c00910340550204652990120321000099190b44160f20554101004c003502c00140a00b10352108201c1e141c5040c601c050b0340c50445220880e00d014132502091603030348c104510501000c0580025030040007003e80e120380406010340c0004210a00644000400655000c5001d022500e181484140c05865807400d5078a000201c40103000000035002d07505883c1c42480110f003409494260041008072820020b504c1c01c5070009142410507071200c000c06042c030408100740c405155202038000b005480030380300500e01c0385183c4c02500183d80014422000b1102c00010711 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 656452464 1250 656451214 656451223
    0x109031506030b18030a1103090a032001020a1a092e0506010f050904021b070e010e0f0f0105060307021e0a0c090506090c07050a0210080604050708100b07060e010e 72
    0x1c078400d141003e101c2d11040040d94124a85901c0d81540d907008110103040d050282101c5030514400004481c5032035038450208124082c1a8411528003d581482c0648402c04090311074070b84c0300a100826001d442034031510000c090300701c80003d074100843d021a40a00d0180710700001c0403524101d0310701d5403901d044900c96100000201000031441c1c00d01061240d84100e01d69410420a03940c1c02e4144284181004002c1d40301a2810100045401c41841d19075028001480146a5940307150025031404a644078090b00080c121101d0312114410080c2c08605400a5815030740709550040c2c9903522034a081e46030100069041c040000d0600d0040380305c01c80000c1007503e161207250b9104405980e0351101054440135103910780d01000c070308000340d4195905800703020518085d00c201e41304544250007140c06101065202c50000d00504104003240c03c050260350707044891850250348510302a8042400e034a031a020f20030900d2000100002403088542202c0c81c0203000100812184004680d1036684 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 656453714 1250 656452464 656452469
    0x100227032e06030209041a0708060a0b18120c0102160807181509051909050705220204151b1502310302100203041a09010c0605150924040b0109031506 66
    0x585100b00000c0841d48909c1840b4000c09000d400200c1890800c1110390060b046146101e02d03942c0070980d05c0300180d542c500c80c014100d1048000d08411410300000a081c4048440000800010070400704501c010004110048511102c603000e54104001405800b412606c49000c012482c215008200d66040d030f400240608000d05501ca038a40c24250030605031909888003a00f50340003102c082101d07060965803003400c82c84002c090744c3c01d030300628406422030f0442c1e08070200009915410441c2190000019011642c0d0220301d1884030100e503855100c800385007840b01000c250081102c2d05003684407545d42d004a00241d107451007010f052401f085041c0d01c54442a445401d10001d841000ca00110895003600d400000350741000510000100442c0d01014403070341004648064840030903898401c0c14014109203d0b11500200184100000c00382c001c1c052a00e02801c00d4896030480c90704c2c4090201490082d02d011409a81400051b500b2049540c4064074084c00000e0981d80c1c0e0501740d1140f400e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 656454964 1250 656453714 656453753
    0x2070813170109030507020f0f030706050d051b071205090a08030702130203100b07032c010f0e1003050919051c020703020d060905100227032e0603020904 68
    0x1d0002000010700b6907506440c0a80820003c00050000d1300b040c1e440003600040260500c81c2004091010902d0f0004d640d001b0300000c1d802095055241d40c0d207000f1150010340c0d65107211058001201000c4c0688240c3d0801050114184410100030307000d40207864a144009180440484e03a9440c0c0781d40301d40c4290f20480c8601800c09002c54500d525200391790085d40090170104001d410074401100d1075200510a030305105192281000c01c078054081c6490000c081d201c10003681920358005008a4142491070302844078002890a50b0384850220070b1240100d4075020070300361104007040e41080360340c042180c1580100c2c01c4c000c003400000150764401d0f6544000d1481100d1304410126100c480c0c03404000d5219140d44000000b180e42c640018405d81d0003035040d526003a10842101080741d014590010f10070317a012a190410f802240200103902405801800e1410220901c01410101c00003043c114071018488401c030b1901554004d801465000e030a209060038035080c00f40c504c00300c0321860203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 656456214 1250 656454964 656454989
    0xd0b0301050a14070c0816061a010206070f201009020108130b04020f03011b090f17031b1002071112010e150702010b060d0e0c0a0b070809010302070813 67
    0x8410482e1031140d81c440500081e000f01c0305446201040b180034001c000c041d2084c40c002d01082d400b0406881190303007514440c02002030700c9810b03407408000d034808042107981903410203402c010320141c00c4124440243c5c241d1821124a051903910300032440f00c1243c00c00c4143c0f062280c0c40d0f0101d4a140e000e00c104a000342c844074400d03030300d401030488121036480700149501612000728005080000c50003250020043c00421101c0a4005c40074a2220398504000010350910017040060b1012900c0c2e0041c102194809010036410000c0c2540c0c0d01c9642400c1d17922028409400d0341c600401c4c0030b02c2d045803503544070640d81c801c141d05160f00f41d0800e51032520b2080c8902600140100300500c50b0441c040010300c05403401c440e040c2c45100c59804020038090a6548071280b00c0000e94410000b07004420100400003600001d240300b2610f070108900045000b40c200c0e01040c4240c603030030026204079540c018801540c4085e54001200a4012024000c00390540841c05214100d103420031001075500041654 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 656457464 1250 656456214 656456221
    0x42c06030a051b04060b0a0207090c03181704030c090c020727200d052a0d050403050412120806040621110306180d020a03210b060d0b030105 62
    0x350301d40d11402070042c51540009003001040c0c2080300b4601c04103800900006580e6501d8001d2400d551000d020003006803c40c40003071002050b20b1041510041032441c040240c2e415020301a00500c0d40b01e1f20182c84a40349000d500141041081220090355000b004080c400740c2c2c3d000b007040680042441040980100c8101244c0a089800b40130340701004c003c0460010341c4140b08820040c001050000141480c0003070029029065a0007070001d004403040c006218a080c0e03100c41c840710750a00c12208826400d03003482c03400d170312210140c0b9000f1001c1d40001a494441d460250350b10b200b40d40c448424481603900c0710051044162303030b00960884640720040c00f82c0d03688003000110303070b5980201140c0003404403500e0100750f240101000700c9803140c240c16800111240c0040d26124048440c20b0411440000aa015400520205659408030b00007406403075003581d80a4240b50751242031039100041c3c0e213400c049801103a00000c207a1319025028543c0c0302d02c224410380242c00d403505050702940c20300020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 656458714 1250 656457464 656457469
    0x20d02120429010b0721050a110318190504050c0a18051c0c081203100605090303030f0a092102010b0916030b1305010b03010302090c120714042c06 65
    0x681e0922140042481d01a03013042141c1c01c00d90401081500c018807814404000b240400460b2440180300b501d540b529030300c240c40010540c01960141208a80040c412103900248010150440490407500c4402c943c0c90842220310300030655102c140d21074186410f200115009500624610040390350380001280b4030394914803c6542e0f403203141d410007008060003440e41c4000030f16174291442280c1c41c4540d02d80d503081c16490442d40e4a405086240000f06021280c4442441130005001904125083c00c41c3c0100007a100d0100606403c0d13a1210b410001d0303c140d0040c3d200040581c0d0003050f801040c1c0080c1e0513000c600c44489131080141d841c02c2855100c4c0c2c9030908085118482c0701c030010101c1c0102240890107424100f10154004014131108a0310501c580141e40c040c29540203901e4496146004100400c0f001800300d841c2c026040002d81c1c8001091291107501440d82d0600391780c001d0000c1402c05040c4502e40c0851080320b41d14440c52507a0495110f42c00c01c1111508070360703a16440c2e0204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 656459964 1250 656458714 656458763
    0x914010c0c0e0924180703081e0c030d0504030f0201060b030c070309050d05100b060403033903020304030203011505180606040f090504121103040b0c01020d021204 72
    0x1601001c1454400c104582e06104116441180e14050780e615406103610700e043e40041a2041c1010060002002454131510340078421a164001c014940e40d899a181c00200744101200080340041049540b5a182144e000700c0300b41000d004116a07403410a03c2405000b080e0594040f00000c400b40f1503040058814040d90341541c81044c111441c513192080910850703805000c0071401e1101d0442e00003055960b0144101105000d0320251021110401103201114031040b02684940c5042c4420b00120358801580041c12103d0301c101900705202880c2c2c152510a160318880c103115180440b1001c166010001d441241d209400a01c0f503105141003031413040c0c107079010701030300304030880800941040c007103003410340040c0c0242a00d46400e4071504001004c11041d008004607030740343e40600042000500c062082480b0f80d14002c0c540080062910380c4a02c80da00c10380110403004552104440d41c20341c1120131041c107a030300841d910726807401020030b0b1074022941030344c58480e0744604500f00c0c4641c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 656461214 1250 656459964 656459987
    0x18023406060b0c03090d0204330603060b09040f090611040807081b0603130c03060903020f01060b04090c02150103050106150513090e0a060504110a09020c1005040212010c091401 78
    0x201960074403800340d050000c200c0000c0400e0740d01a849014627401483c03800d9000132400d5202c0f8498015950101000c06501200da000c001058034044082004014107000d85044900860300400d030b0b1000324940710094072600802405285c03401d040f11a000c140b160040040340c03084811707210380d50346c0d0b070402503160b040001400c0384021b800c81402c149458200011039000f00c2420521284140036100e003c89030006800c12290f50740c0e200d54190900d034040044581c005000d600a220030703800d100e800c0355a405188900d4401c562218000300c5914000e209000414011100e0240c881d1303581d0030140e02805083c4a80e05040842c0d0000160a0344904203c49050001d941610170741440e00002c00020818900605800c1c0940314004000620030301070107014501034201070030348200400c200034603d91294046a695441048000d140703040209010380d51416084000030b03103985900101c0c0005090b110140c5240d4070303009500000541029400c025960f89000e030340c0010f440200159030108011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 656462464 1250 656461214 656461237
    0x910060b0c07081501030305030405120d0b090a05060a033e01080f130b07090909050c030c0d031e180b030106091703030a0504031206080606030c0301050118023406060b 74
    0x384c006001080c060300007140c011b80728108903000114400000c2900346c200d4420ba00c80e80351120300f03031141032400000103504420300003810006030510f07000041d241c1c0180c0c4402418403036850540c182e400340b000910311000f20080600c404035403a5113482c05401115070850fa010408000c04a0402c89008030110b200d000440101d0303461680c59120704a241100030200b4003000401c0c40003250201c142d025810034203200f90001c0c2380e940b4501d0109400c0200305482c1a00960380307165075101095007c0030310104115401c140494cc071543c0c0c0c0c42100c8405408040d85600000d0300360001d2341e4200e0301c0003941202d07440c0d600c1c01182915203000c0ca41e034184480c18699640d00074004984501201da00140d00244642031103c0d02001610302c5e00300b61165070348040300c242c2207201080020b08092140850280c1c04074020811907040030000503031140400d403541c41041d33012403008580d1540045031041070290046081000d18440c0c0c144a00d0030b84000c0440d01c103030800b03d001030149a1034080e1408c04103003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 656463714 1250 656462464 656462503
    0x4120e1014090622080606011d0f090c130e010f0e0703060302120a140604032a061407030f11180604030803040b010303110a050d080910060b0c0708 65
    0x16144121988051141e03464441c40d81040b0814565540c00010040500307100720840c0301d6070038026141005113aaa10442240d0000c80c2049013036030b4018036112440d5140344032020400b001c1c42c00715003805d1071101100e401c109004203001700c488094002e440d102e54041643e4407207944494070389030800e500f803040e00c900e02e10711801400248942010250b011802d464002a660390343d40010f2440a00c220101000c0c0e0010b250800610408004640826507020001c0401e41080c1c1d07001400c036031114005610039000e4a02034a1507030f50340c001c603c050b140c004201b4444030652800000024005540302000b103480d110092903004010302074201202015681300f4100402210380d059a03409001d580b641c04402044080009400d19001d54003450040400058540c1545405440074126070012009944110b510030000317400002c0c42e00421105241910080d121800954500441d19503c04101401e0600104482c0b606101500c0400c817400c1c221182c440c0e031012559202c1c142c082c19000700155 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 656464964 1250 656463714 656463739
    0x1202010509090a020c0106032003120f091f05210601121104210209010f03050a080906310b2a0a020a0806010923160504080d050304120e 60
    0x410000b15507220548032405440c048210300c0c00c0b801c4500c0c90b01b0841d1031102d0030301c01c0300c5450740042c00007410503000c3e4000c1c01041c0c070800d42d420041c001d2b00c0200300c1d4104005040151502d441c0341c0441811140d03e903541c2c0358540c00e42e001c0e180c0e4005441804140120f00758104031090302c20f02c081e001d86010b8440808640f07072180c481010301901690101194010040000d201404004011400b0364038120030801c0728103441000341c041ca060f4040d0084000c03128081c8041400440c2c000f4500b644058216628006a004204c2501902680e41c3c00c40d80003450069515a06a280150b030400140102100b9070722035000160358000c0c0b55058400c15503c00c15a40c28070400c07400a190107010300c013150a503841580c0024216070301d07500b18054a8004000401014490f4098180c10585d41040b10700f4200071048015440b81006004011030180c00060300c0d184c501800403540a4000c5406075400c90010703010182c8182d00a8078112104200140f444100701d10a04041c8608d500080c0280010030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 656466214 1250 656464964 656464969
    0x140f0f100201060803040e10080a051506150c0309100815011407050a0804060311091e0d0c0909020f04140c1b01050a1a0102060402030303270114101202010509 70
    0x3229049400259965400003207814442000984014004408901103600d411099038403126030f641c1c002c0f94079038040e130140c40000d50301003008121101d0500800580b5038569001070122040c2003595a80790070005100500c0e0140400240031900055030700070700d07403101000111a04107080b92840c844141191840c03020b03612842080051081c155805030400c207481e100d260904900350b404a078064000541000400e405000341c80e210b1514281d100c0c240340c004c1002c00e24401d0059407000c0704001503444071400707917194600c556041ea001200300c101c03a030325a003030100144541d410591061028500000441ca014021255000044003000190780c45a014002c10740d041001790b0b120704107620198280803182403042038425004500089803101c180441401503421030300c40a41190401810000036850000480740c0001b5441e822041020b490240e8482e2200760485010042d4284000041190100030103035009910241e940c104d85075481482083c4103202d041c1c02030103c2c40c103203c1800e561 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 656467464 1250 656466214 656466229
    0x80c09060a14030a020a08071103040e09190501270c0b03060d0f030804031e09050f01030b040e0105310303090f0515090f010c0806040f1b030501140f0f 67
    0x2180c1801c00e900404800d0920b489240c2088036181c442c50f5020481c06000355000c456030b50480028240b45050600c0610001d44034403072401020840191880401e10302e490400c04c89207525960030010320070306c1003460014040d04179005024150f5481c001440c0e8003140190110004c0365014400582c118a00300031100d07582c00c002d01055108181001180206035403d00090780d0038400d0340d6407a000e103854900600182d004020b540e8002202c42214441035800480d6202614001ca55500203405032000403005000940e00aa42085c01c01c10b05002044054200340c0c000e10201c10a070000081014550801c0d0191003140c140071103001c405003000c20b010364004408540900646024136001b0307104c0518208910b2103240c114110300d0104119420140a07200c0071016510007400329004c024001400d0380e1000d410140b04a58400441e012162a0ba0012002c80f8400c140352121101c1304802a004120910851042101d0300c4c0009000745009812650001401003800107034030155014420030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 656468714 1250 656467464 656467477
    0xc0506160510020c0316060227030607050307050a0c020a09090c170307050307030c02210a0b07020321062b0c0b0306060304080d06051c021905030706111c1707080c0906 74
    0x840348d0801c041d00701951002c041c0d00c19102e81030306008148403410145460450000c3c110020020b050040c00743e016800070807a1000b503610f28107a90104401d00005181da2000c0c3e02150150385000e80d01c1c4c04209000030f42c0e17400c681072881d0241c0c0031072841010320b44920600c0703401810368200f0824640020f00601e91003c5c02da00107081c400c0d03c0003003511510300303555012220100030350106007040100040704d01d40c280e100134680f000e581040fa005003401807405208821010840c40003001400503100c1e1b00344101a0403070703039400415a000001400c0f10388244500142c82c000c1c0070400104040b14194126801814042d09103491a9901c0e11180019080f41d03d00030202911841c000441d40d0301d042c0386510b511580100c205101d030791881000141c409d05024420410900b040410040d0f4001c2000c5d0129109406c1800b049004040d483d800c3c0100129084032661040020789102540065801d550310002d108103141d684542809650046080385c1c01d00040c80c081002500504005016120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 656469964 1250 656468714 656468723
    0xd020304171002180306061f12090c090912260402030a05121c0501082d0607080f010608060901030219080307110406060809030708070c0506160510020c0316 69
    0x141801c0300c10210580c2c2c007002002d0764061350b40f80d504025190900440303400c41801c0351610002c0c3c10740c4504820038a42412108203201c2c280403201c5060a45812480781c2d50f80c80089004500d4070352038214020b240c89103003500d424001d1103001d101c441c01880c42e140c0034020710002101c206404c10190000c108006d0080380c05010382941200021002c1000d5484c01d1303039642c41d0030344400e500d68079032050902014621803002e00344801000044404114802070706210100300c500c5402c28000034007200420700c1c14212038800c040800c032440707074002502809103030100c40c0d0030b00a99a42030304845000d42507410a601c100070400400040c42c200e488001300c510101541c5c49140c3e03032500705500315044507100b624a80110410f4050620309841240c6c060225403c00074814100403107004da80c1d0240c188000c28155002031000c0900911003040c8005000c001e0100d82c0d6049400100081c00a407038008641500c108450085044164000e4a4415500e44002c50405030700741c80030034514094180545 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 656471214 1250 656469964 656469973
    0xb030708040b10180e190201090b090d391d0907090f09110307030c0b0f07080a020a0201120b0d03030218030307030507110d1509150c17090d02030417 66
    0x3400a42c0d03100300f000a03210341c10300001c02500100c0101d01b4076480c0711403032050710840d0800400503a04804480c081d1044000c4803500d54000e0800b10b5050440c410f00a000020101c079841540043e04901111369181d0038400c250490b0748500030b4021110030301888100002d001aa03480c1c1d401d16a4680c2da005034107804075140556100540000c42d20012030b900c14482d1100a00310038000d5442e00b0380f48a20059004002e2240756494104600c602e078001c01003080c0700010501040e0300e0b072005645000342c0051003180d8880146002940c0d80003540b404a002c5001c4621894010407544505102e0f4080a00551401e4005039402c03002036102402c040c103101c456038a4000b00b034501300040c1c64414800c2d01d0b5550f45020300d08101a8010340b20100b6071213211000341100005074500c02a05100c64040008200aa024900380c034064032080300c1ea0202c140307404030301c1810030740c0a1405102d01d00341c80709243e0540c481e44072154444a0f80605803025a008000070815542c2404105501c42660001ea4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 656472464 1250 656471214 656471219
    0xc021305071e020109031e0819110a0c11040b03030912160b04030b09030c1009060912080a0f06080a020108040c1809032a03030b210709060b030708040b10 68
    0x880324542c07081d0301d08010707036507000301c441019088030499029424030007a03003800c100f02000051003014020030880b62000084584541403600d03400c00c1d41d0b0181da20320401d40b12504608003c0c603048030030109803600791070700d01640110309262048101100c030143c0507529010f150300c10b002051501c0403c41c00a48141103280c1b0259100c40f80400240c0f402c2410103070764a1a50800b22110b10010b0000c9456400812109d00901e0000a44030039040d030340200881c00011508014000703109070007015155224080f0f003154110391000c9404d04c54910706a080203015858084c000843d400380c0510f8040307070b00c0442e00c0c60141d80a251080d42c028403841041c1c1c01d403519a1500000c07074014090a05000e41c441c00c00e8070801da04401c150520310a0341020180101d55081030518020180902034181940c40b0350401355900ea50550a0900560307490a40440c20301403115507886403d44074103100ea034034265005c03440207401012203029061a65a07c1002d46039038440407225480503100c40905c0d407500000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 656473714 1250 656472464 656472497
    0x402040b19090212090303070c111503090703021f0c062c0109050712050307030c030306090c05090405070320091c080a02010608120a2f030a0f0c02130507 68
    0x601001d0400b00d0805a2034000c15800050042030140005610ba001032003003003610b641c48100c084101d038001000c01c40400000020480400241c541c00303024000000821515510000380d19045074426500b14141501e40d00301c0300300b407665401c22a030001c0c2c403000c0000c02040094000882005804001404034420503032500c56812501c50002c1c000d945a4241c2010b00c0414040c403001011001c8089a06072540d40c2c60703548034800e100005050001046115007418460360001000d40100c10003041340540c4c0c0e000141c11030704600c00320b510540c1080d0020701060710a015581107010390356026440600e030000c41d40c00c55044010ac80d42c02220020f850f22465014055641d0800d00a181d1580d440040c0c3c3d000070309460650300909643e61000e406150f0b40740500d82114454a120701d8107118404038600200741107510841c4140c1082d030365886c03100390040b0100081040710f100380c80751145000280c40507503034603082d180041d5100105101d40030900c1e0654002c0b9522103039501d0405000d03800c0341030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 656474820 1106 656473714 656473759
    0xf0b0d030c0c03050607111b090610051204150c09080d050912031321110112090c0311150306300307050607030b0d05060402040b 57
    0x280c180600800410082c09103510009890355030400c014000c05504407040010340c0760040b1242e85612210202c2c4250301804058051500c5580315000c01140c4030941c10b50400f884402c0190303410072690b108000340b180e4070603540800524504401c00d01120800c1510a003408440079050101030800950101030389403034584107549124920200340400302000e1140c5451001280c60400740210741411301c141c541070301c2201c04110300c01a0032001080c4c1150040d208500c02402c8122951191070b003102c203280c0412021940746601d41c8d41101c5070100e82e07c1543c5101c1c002c410b0300b54030b2512144898001c9005003103241581040d00000700258885a03034011014500441080c040035108607495144660f0b074240d81e01c0d1082420441e4548030704441a1000038541800c206883c078041080e01c0b10b00d500203000300420b940720f40c01c0c07000400d80c141046501030b00004104408806504 = true := by decide +kernel

theorem cover : BRFrame.Cov 656294964 656474820 := by
  have h0 := BRFrame.cov_init 656294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 656294964 ≤ n) (h2 : n < 656474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
