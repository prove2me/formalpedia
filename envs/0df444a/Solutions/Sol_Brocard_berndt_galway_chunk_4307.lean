-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4307
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:11:25.584463+00:00
-- url     : https://prove2.me/submissions/d5bd9707-6872-42da-a096-c32a3d14f5ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 774460431 ≤ n < 774640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 774461681 1250 774460431 774460469
    0x50a080310120f03050a0908010509031207170601080601050f031f08010204030f02120a080c01092001080604111b0c030f032823270d03080c07060213030c 68
    0x803d038224580c0e240ca4215541c1c190b08500700d95080b01a8015482907081c0f030144502d103100480074150103007081101101550341c4040883c0d0902c0703403031102e0b8250381030240030441551045c0310b09648140181011840c080143c008800c0c264401c0b202c1061194072003040c00c20381c080c0c410701c06c402807080e00020350415095880344102c520b00c0c0500244100c41200ca15101014240a400002600030600980b03d8200301d951501800301e0304002c65550710085488204905c07040352090300b135001a03482004039540d01047c0301c000c101049a11204880510a10303007005a4800d9003810207000c2d0018040344500903080c13502c3c00810741003500680d0803e10010280305a811601c000340a001000a0340b1a1120002603401402c80300c00009030b40300c1c0c1e034180014035101c40d0040041c01e48442500c0c45185003290300d8030340c000d4003081507075109690303080441c0130030303c01c0d00301c50b8000440c02d05140c5014195078414081b68000300d0a00218007811008000340211101500001c00000000e2035039a00380f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 774462931 1250 774461681 774461693
    0x1c030905070b18010503060301062418143d02160522020d1d0d020a08030c0714070314101e021c1e0608010b090f13050a08031012 57
    0x950f80407030b070402c0008800128150f809401003c01000030035034640e08040c3e62006440c041080d03101c00008501400440505001c1d070801c41400c881001171002d5542010800b004201200101618220b122103076901100c0d4a42c0001c40c089a00304802c08a10b02d03040000103418010152082030b8140c42c0d80c08200400d40b1100d007400158400d040340c00300e018044000d110000d0140c076000041d040d103007000051800120f400120501c800140445480800c3e890b022aa0b40e407140000402d0b040c0180041228010b0250141c00028820034070044c0c808200340080d494000c00341d00955807554000700310800c219040c06051414011202c0034810b0500c0e030b1012229404440e00440d11059000030000c3da424a120740310601034040799000e105220710030214030240c0c0c06801420091514112001404480500c6038903c24038029008003d01e941d0824428010000201040094038494105400049082c410521003512030040c80d0788034104615040b40340d0341582c11050100401c07142c0c0c0d0000c030310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 774464181 1250 774462931 774462967
    0x2106030c0114120c070c05091302041d03030903030403090f0803120a06050409030315050612130501110304050a12210f2913090b0115021c030905070b 66
    0x20b0800e01c6090850103188072807485016486030307400070b00b50144205600040c006084950103008103907550758465080200700d01041d22080042c041c81d804500c0103003440e07000380c0c03114442e01441c07840b003d049441d020700f076a02c1191404002e41000040200b05034100e0081000341c01c0d80c000c240c18540c144031040f5524070035100601c11075000300f000501000f145070445d40141c107018005014950480ca009805801d1031010740d01e0581c1e510001040070300f802c00907603c01030901860406030b501c1e00c07000440110740b481d2041c0c8443d500d03000c4800d140c8940d10002d40c00b50703200c2c100070801a1100c3c1820190100100b824504101c20224520300807140004916500610400001011300c800118a0b00030300d004ac440342e840022214450010040ca625100b030f03040400c0e60300c100e0300f9804000b048100d84040000921328681e100048c8910b490307804000c5030b010a140125100d0000d049114405820491203900000751220014000c000b81440984000d081e21261241800c208003000c1d0310400b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 774465431 1250 774464181 774464203
    0x40314010b10080a0f091a071b020112060e1e16120b010c0b01061205010e010f1502100f090201110c240d020a2307080406140706050c210603 62
    0x10720000303e5062102170b0f0107450307601c02c003500400030401246402c960361a043d801103100d0000140000d46a04e000e40352000038010415401c8000601c55030054030300602804240c0805903850102003070500d0340d200542e02422000c0b82c00014085d982e404411007010060958140001ca24813040d26181c209140c0d080c43d40e001c1d000841c1805d5940c00480324141066130180500c2c011000008889030030204800c1800c40850060080b41c0e201c44cc3da101c6080203100f111401c158540d010400751103c080c0e00c19a80144d80f0640da0904c500d0210706c0d041c3d48030045410310183e51401010110340c0c003c0d0803100d44100c4a0050030b052044c000010360f06042c03600a2007880b52107511f02000c1080c0348403c03640c1d8106080c1e800c44d190540c4642c001e003203c0a000c280d241c08007080e00c0c480c4112070658140c50b50150b000b00024646030030654100c2c0d01c40001c401d00103a01c0303001d00455000641a00540e071080c0e050744400c0b9150304480c00c1c0c0b07240d66081d044010010b40181014030101c0d460200d04c0c0c07a420 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 774466681 1250 774465431 774465437
    0xa03120f0825200c100f020606130b0d0312060e04050d03020307021504080d0605180c0c03070203150916120611090409060c090914010b0a0c0b0702010b18010b0d09110d08040314010b10 81
    0x100c498400d404e00bc1e0002180440d0b000d06001348007802c25800140400d140034142c0703c100036140e10780f80d4440c8000300a43c0e0207041d980c010b1040c0114140300f40c009580c0320320300d0302c1642e1808006001d03204841d00241d1f81251000c40c0400e411020841a10800d00100b404841200e26500418800d901e441800340c004008000001749200c60300c0020011200030a901a04030381500c2e18101069240c401c081e01c44041e1070060091051072007283d011564207483c001c0e042c5440300d02090341c034203000b403400000340045601c00344600507042c2d58503c10140c4140c040e0b00c011500c00c076038260080c0110040d4120b0350119203460b6240c01000550032200d03056503a039074466035a07581150000c2d40d000d0203030003008000d00d6017401000803495064000d48040f02061346c0c2a1442c4a50340114000e0400900801c20410001e0100303080070b004036040308100c9800798a25800b01c25122011404110b1801e1003513440c41c8000a0400400084002a0b4880c9044c0f000801c00380c081d140004000e099204c040300c00f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 774467931 1250 774466681 774466699
    0xb090c0d2a0c0503040803131701271a01080a060c0207061d04060b040b0c0f011a210105090d1404050306071d0a03120f0825200c100f020606 62
    0xc000c03041017224050060070007241c0e11108801c210150604a50040c40c04200e6880c459141301c0d841409600303500135484108a4240c46074504940481c0700c1e9075000d40d0701d604403542920000b1011003c85010306070140240c421001182000c00507a0400c0d02c0103411035014072410006203602c907461220041d001c0d0602c101040c44180000e000d0121908038801070b41c0300040024038040d03503000400c6803403624000e40e003000140c0fa030510300300c3e1b05802040b04045071003d094500361a250031201e0744041e4070280742c02004e01c000b116031b0854004644103801c80e40280c05c9403900035000000030500110f2010740c82c1c135007030a003008a91114006404001070059515070f100c45c2120850080364682005469100426907070b0030700000d24401001541c003c242c9201d00002000e2040d203c140c404d40d1001110000c604405d162400f94007038412400c0c042024241106070365007440303031500140c0b481d8400102038400760901007020000301340b0a24418454200d000480182d0049003656000c0c07012180101e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 774469181 1250 774467931 774467933
    0xf061e211e070f2001060906080f070603020901140901230a230f0903031605030415050711011101090203030301080c090f040c060c0611070f0c09090302070b0d0b090c0d2a0c 76
    0x2c094084c40c1c00000105080c188c0c04502000c0c0001c0350075028814104480c2c0056a800003607041f4401c046600780050041002d0308200c1d03075060000e0400b406e0625000b07000030910301c0309035481031300040c4c5055100703000990405500d50040030403100348084141c50390940907201700c0100a00c00c07510780c18070482c40824801c040380d4052050301d41d100201034070143e1841c801d04d0000d490703600600034800e120b842c005040c01201c2c03240d03041d642c00507030160305486040c1c0c010005554140744000a82050340d214052000180c6051002d18020b0031000014410915000708010700b14400503c10500c0d2a02002080b001c41c05d80810070003261304504081007038850030304020004c2d00c0400f9018124460005d444010071414203c900341190107401400501c0c4d8a07000d0790415140420005001a8400c2c001480131071060001001c00e1500c180c0006200d400801c0480c0a50000f100d15900100001c0340704000480d4500840c4942080300c0d220100c0300100504480081d0005c40c0c1c0718040000c0505040c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 774470431 1250 774469181 774469183
    0x10c11010c0506090703151a0d0203030918180109050a0b0603030f04060509010f0905031002091305090604030e0301140415060801020f04050f061e211e070f20 70
    0x41c91080e008001e40d841c03413034200741c0684e41c1c83c590b00c0129422202a400780d102c411712072094000f00c00042410292010601c0100039088081e03540a03a81070204120301402070ba941d52461506070f01402000c0001d1511141c3d1701d0014440f01d413500400d0341411a400c1c0001d03404100031801d1a884030961440f5222800881d01c4c5006200d07960703060080000b00820380326040707806488100801d03038132122003501001040301d000d41140300307a0b6050381c00b07c1c045542c2400380d90068252000b016145903524000002c2140945800340d0b004000354100a007800181a4842e920b03011a5009900074000d051880c8a4041c1000e0014170140038203031900e03000c2000c1c031290b8101d01c00922110000b036460f00b0a03e0280318440d4003070b00c92a0701c20f01482c040350060b4200101610fa20b41c4495190310401c0e80388861030300341070b4091401380c8181c0401c03489501404400c0a45c0d0782c0680c010070101001480740d51a0000344103005403580c0180701d0307075080b041e056591000355090061031000c2d043c1050794494589c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 774471681 1250 774470431 774470447
    0xf02060f040e07050306100f02030316020a021008040c170c100201022101140a03050304060e030f0102030c04090506061303020f0307121103210a0302070f02060d091203020405010c1101 81
    0x94055a11480180074111341d120000d035008a6084590b00113a90003982d05a4068021164a801681041c4001503e02065026070b07113180a0900603189040306603800124000000701c1010003044000c03081c0424484034a080c180500480c1248400004024206c669100d03020100984903060140d03200010380d01c00c1d01078a0301c0707030384075405a60f07041000303820301601c0103090081140038070b5041c1e1010420300d0001300c0c1400300c0350800040c40c5403905050f02240c400701c0c108141c84d0075214502209000e0082440114421403501041540b102d04000b0044140c810140800707110b403205001c0b803a201c06041d01c860085a0741120407141032140c09001c203060621660080b461303901081080300c248204103803030040c1c1d4041102612200c0c4001600e1000342640601c103035011000a200012515000364000c01031a0b00070043d5500a1100d0341c00600c0d1940405020b030002c9880c0c6100c001003045140b001c2004030302508095080a00b4100000c110501c06c031005001036003205000710142e401000c034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 774472931 1250 774471681 774471689
    0xf0602030d0515040f0b010806010509090f1f060f0206010f05010225180b030d17070827100c030c050d11130303110d020601050d02090a110d0f0501120f02060f04 71
    0x1030003540c5c0310580c070710300906003000c0250202e1444400681c03950701c18400c0725858100100300c04e002c0e0300c880e1600809068000e005101b0100c8400c00d014403003460b1045400101015943c0400801c110b1000070300341041070340700c8610740706000401e00207070389c0202d200c0b0350140450654101c910401d40c0204c41900c440d0740f01d0552403d036808224003101c42c2e80c001507403180040d8100c0d03c046c440450211070301c400b490045082d84e0b85000100d503415204400c1c0d281c0068480313078400100d060010300d0904111801c4808402ca6210022084109445014072031500040b400c04001d0b040152001506ca80b140240551155a540d000b4482d00348801c02510800d1f44280f4886004949924025007140d0170906992124030403c50294182840098854140c0d41e019045005200d480d03800c0c00f00e403120140110843e80d4513200c6d100964030000c0c0250080b2a1035103004524558440c1141d030440c1c0c01a0071168501d5050800d200c04610492004182c555041da0803d685107410b001400b401d00903604 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 774474181 1250 774472931 774472939
    0x8120d0506040b10020c180915090f030d0501030506071403161106040c1d0106020a0809060c0a0308010504061e031e0602041202090f060108070f11030c030d060f0602030d0515 77
    0x540b005150354006140d0701000c00075101a0340da003c0034480003103171031000c1b900c00360154070000e07140710b05d81e180e449c50a030000406002c0b503c0c280c920303080c03d900359003000111304c4905036107000402c2482400c010540d00000542450748072105108042005444020054840d9594403100002c079140314200841840003405c0c10703500b1a061078a0901144030355880744607d0980400ca29404280d942c255150484d031070380d001044072101a80d40d143c00ba400140e640d9074040030600c0080307454901070010040c654802d695100380b035810901000101c6000c1e4102c0a4440c80f0f460b90128440500f640440583c0d0b0414041c44d80400c0b2403031f40c023842100c0c44c800208840e00104000603800c0f0380440c80b0074890310840da48441550390743c406580c8a8001c49250340003890b00f50201d90340714080e010a80c010501c0c1c1c5030010b180e80c04000c0c154074560104040a003258400030319040c0002261240c00e019111521100601d107140110003903581c001c42c8401c4c4251503980c80402c1070520013000788070020380d02030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 774475431 1250 774474181 774474199
    0x30c0806010e01021e0309030105060a0b12070509060705010c030e0109021503100f0b07050d05090303070f06020c0102070b0a1401050a23040e1c090f031103030d0510030c08120d0506040b 82
    0x40c840c261030b500609101f40c080e60810f000b142c1c40c1e18150b0b2451003a40c40400e421070906080031320078803a40e40003500c18800e000d41007100c4103013601c9a000600700741c1d02600012810f80c980c5070000301203e100603081e500b20f0345400340080060342c444091031407550380d50000a8998032100301118100d00c1e1036202881030078100c240064085051b0b4040d080d040c1c000c3c030a82e002d0a291000c151094071038221101e5142e0000c000350f10000340c6e121101d031149409094014100402080ca41d42268006d0809031500b45e1707004100b00000641c0d006004001d510b000880b000c1e545080041050300419000d2504002411882c4030760404850904903003148000300280402c405400c644c40d11140c0380b4111004070780e040045510010700a804400882c1d0310314a444581e07503e5034860301c04201903415620b5140c082000496043c9080d40600c6014201100520540c14518a0042c000c001c066001040d10703001075010303422207c600800d551404880d0000400c86030360343c00009000300b40000f03103968000802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 774476681 1250 774475431 774475483
    0x1009092102060405060a020301060f0c051c020106030b1e0118270b0a0606051e07080f030612010b03030f0c010b030f0f1009120302090607060e0d0906030c0806010e0102 74
    0x24449010f1405902941c58646400c1240c1c02a4802405400049813584d90450b444510855400c1d2000c0d0040c0e0540fa41400111020704204100101550041c4c0d1160828020b1001282480350010000340050440c2c3c904840680454401440b4004102c03400c4001140d040d4020340103003100c09410044403c2024602c039002001082e00d10090381c19164100015174100340340c2c414241510b45e1070711890300f010100181c0c542403424403a0340e409a0f00003881680d0004841c80040d00d0500d6103060090b4403881c1220a0102805032440140c81d26030402411080e070b51004411200d1103021807001c665155007a080c5603000d07040103510300c0c1d058407030188116000c10b800700701911420304900c20b6074460f2a0325001a000e592182c0e0010300103001d034a00500004c0d0003540148010310000c2c2000c5c2c03c210003a00d41d20112409004607110316003003161400b18440e1321441240c007402080c10100f01c156821a4020a4090001c00e03407810310001c500c00b044580c1c000c00495602c80c803d03031240d540001407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 774477931 1250 774476681 774476683
    0x13020324030105040c030b0912190e060307090612230a0b10050429160506010f0b1b07090207060614010c051024090507080109051009092102 62
    0x825945200035001024280d036441c60180951406503400190f0024450708544404c05400c1000c2c0110300340e0300c2008540701040b00702c8000b61032114101d0184e0454000b05a4000e02502e0038051501e1280c00200100003046410041c813031300381c1f456403412500e54010522008000e000501e4220b003400710540e1502c041c07464800c003040c0b20b0203d001d01480101a0501840351a1141182e160082081808180680d00260b1a28441280c1000c00c1c00900b407550300760302100f54050200f80c07070107011b40640c40c8103103c030410013036004048252602a400d0b00d085150250341c0170b01e980c3c044154024045003c80d101c4100b11001c094032022208541e0343c044c40ca4041c00038441442229038808281410700071a600801000c00c2d034540110240040d8545441c60900620307500c1110703560884a1456021407a41043d00c90001c2c02c0c00d51800251070616660107007082d401640500c40c1c4500386010045141207005904045601c14100418510138074a0503035600d85016082c040e2400034448a40390301d943c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 774479181 1250 774477931 774477961
    0xa03060b01110105010f0b03151f020d0203040b070f1104060f09060506191815111902060a0507020301060914180604050c0d0201020a050114010906051815130203 71
    0x1098071180320400c042d400140c2a54401d100c0d115208500c00c604200e611208402507a0000986051071a05906000040c4149928a40720003200340034520340700e5078a07010004841d00c0101800210b05203460a040e00c05144a440b100a00f84111002030b4010403d01b45290004100d008005015442d01c811140d01c40c10081e21492000d070b410300e0000980c80c1000c100720340e80301800c0d49000411031011201a542d082030400f03a84001c02054600281e2000c0d00c603140f600584095658880d490907103000185056200c06444440501503800702e8016900c070b4013100e010130980c2c246a17445080c0307400080d004006550014540c0d0781000341c6005c54002d0ba0541c10302c1003201d8a916400e0314103500792107596580c101d030011329540c4203101c51161071a058692850881c814030460f80884030a0b0f9400b425210450218100c80c4a144014810310940340942c0024241c15103030744032815402c0121a41d907441c00382c04200400690291642e003500c0b102581c0d030b0b85a080c01029503903802c1c1320800000c014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 774480431 1250 774479181 774479201
    0x12080d0f060b0d060b03010302060d2f0702091e0601081f1205010c140702040b2b0201110c01080c0c1212150103051e1801060f030c0501090303120b010e0a0306 70
    0x51303d005004104500708405403410b0741c1e006003071f55040280c84407212000381444020440c0a4070745416400358060ba0b070203011581344081c02c01a459074010320610140b1600070b01074030b181a200f01190300b0301d01e4100d101280d0000c03003480c2c8481c1d280c99040341a03c00c42da540b10910004003030400041540241441c41d00d5440c0d205100070442d800141008403030783e9100d44002c030b20a040402602002d468036410904c888900203121170710210801c8801545110701c100e40003062210380c8403900a640e0040b1148190780c040c0c5018029440000c40000c2040b035000700000030000c4003080c0120702001c100080c1d078240c403500b01ca40c0d6580c80e940a4242c40c4c0700d4120f0f00d89000041d188080f0b055940301f809130314040d000c0d10040c510301680090000765002c600401b800a42c90040141d0003001c10240201d1b0004c15000b80180c04407411070030200c41101c4142c10490511245120070000640c0c0030300e55101013400703048000782a844a100484003c4006003c00d980140740140110600030f10b41c0c0071000c41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 774481681 1250 774480431 774480457
    0x812040807090b010813031202070f020307050906030c090a1107030215070521060f0604140102010e010207020f0904050c03060406020c0606030705010f030f1803050703080c0412080d0f060b 83
    0x400d030754a804000f81c0e6035581156000070a031002040c0103d030000d00795100c2a200741809000090108815012a08a44d0b8181c40c0549032602410035402c1c184440340240000b83c40a00390391a200c40420b96403083d1f0780805029030b84640024103561501e900036044a5042e2081980c3c0d4180d500300203644900f80e64000c1464102103001c1400d542c0908102c41440b4158145c00910403411841100702078002400c043c0c003d013110361040982d60321100140060541180c6000b9031100487c0020b0868100c0482141e0b0fa0384108940005070307544011000b04000c007200c80d200030366902e02d055400c0c120000c10385a0148a05010300040114030340240c080240850704a942039902c0c68101640c48041d4030406001c262181c44c003400051081d00040c220107500b100100e030ba410190070540d007409012900358001500401c8a40415074400f4085801014082c1c04030300306414100400001300302102c000b40fa07040b00286402840c20740341c1100010b0301a0351400c0003100da582011800c0c507800000b030b03200c42d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 774482931 1250 774481681 774481693
    0xc010e0d080f0c0312160206010501030915060602010c2c1009030b04030c030f080f0c0d02040f0b04060f180506032203022508120c0a05120715020a02060a0b0a08120408 74
    0x5103210003a40000b4040240c7c0240f00c1646000010340040c490070206a030303040c0207101e0141c0f80249902030440288103a5000240030403620710010a025007105419484e07841d071607005400f180641100d81d2624000300c41001010050b000b00307603030318801075000a1000c000002088180364015100004040c0a0b88480b0450000050b048030b510b03008481200200b50013202242c15161640060000e40c0c00d8010018501a11070700c1d00c03034440c0d0207548040c0700035000090502c01c5550141084154078401d0400a00c001964100c25681c0d10441c02010b005150120000c0c400e903002121f00301d81122071807c0340b020390107117080003901c41a204901170b1440c03c0310701d8800b002e842400c107060704548000e005006840c5141144083c103500150494802e8490000f064010450500483c8650020141c045607108000d180c601000703960307090200b02030b9205201405c50140c000c941d2036400800210001303203617250311000400d03107107140d0001c041e14400c14210a0740b0700c1102e4000d1066038100c0c401c40304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 774484181 1250 774482931 774482941
    0x307060e0c280609150f02120d060816120605040f060e060403090611100b0d020414070f03020712050d1e29030a0209070c1a010302120c010e0d080f0c0312 68
    0x80c01e001300c1c480c000c201210b403052000c505106203800800000340d44190750807503007050041555034111000050100d03968a40c10040a40c1c10801c1409984100090702c948500c5c0450100714070990b4440a000079443e68002004c10a44030055121035a01107020000c0c442d000c40c55940c1d403d0120340072004181100d0021035068000c154212142c06036100602c0b600c43c0740e00f45034000d0074142d008c094202400302c3c200c000580e500d004088040200455250301403402500c000d280c031540d00b1f25042130610400224004ca40c08203004804080c0c1130a00c01da4910713941c05283c0040030010894005501c0341180e40d0b080900340d800500c0245103600440c0480305031601c10038000040d8090340356140d070002101a00609100c2c4080c1c0d03201d1202e062015003941207031101d09505016807050b04105814200601c21494048055800d0383c0d0030070010101050610001303010010b099442c60700c14215241c5900402c9030910803031715000801e180341d517180d6035641c40d00e035078a402c03105800c21280c0c100030010b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 774485431 1250 774484181 774484187
    0x10906030213090b01140d0506131e200d05120d0c1e030938010e1009150513140f0f0109153501020901020307060e0c2806 54
    0x70f00507400000c03044140e444c00088030040300c855038280f034105202c1c450701c801040381032124610801c8c0c0c08400b11001046440d2000c01c140841002450310100b600484010030f50601c1006508420343d45481c01403007940c800101401080b010040241c45040b0300300c40010b02c0c0c04090007540b8031180d801d00000c21441c00c10345040c008007258070034039141c1e90102c0c0403440c07080e081406a94058000602109c0107200030081004404640d03410118408500700716011106150500402851240c45503a06107011040d00d00358091007072616198481c1842d550350380e01c040090004000c011700d5090040814085030001e030055844603000c040910000803824034180300b286c4e20880410716180c03516800c001e200d800a00080c0314a41e03500c0c41142002c50601951949940b4121072003d80842080903000f040d140d000302d00d600c400140e4014000d0b41000e0340c000040c1ca110560195000c07600d40804d0b41000d10300100d0704002548600c5e1004140d07400f440142141040d00001c40e80180316075282c034415 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 774486681 1250 774485431 774485441
    0xa0b1806340e0d030306260d080601050712050f18090915040b040f080721110c061e040b0408010b150a1d090106110c030607020d05130e010906030213 66
    0x540c003054181200b060380f80b52054080c1c001600c241000144561140d40300790f00782c03120704480c0404420595025409100401400c0d0f4580040e10b0400075034500000000c0c82c80c003403243c0003020145101c01006101d030040c015102042c1c144201c061b280c00120040c1070100440740b22007402682e0420204081c3d00f004903810074070080410b81c1040340e0300c844e1390f2600d4143d40184240c032030807000794a05000418050081410500440d06081e0380105084000c10312840d0003102400d002d4000003c882d00e100c041030105042c003044503000d842d03e414000d0b80700046941f00c2d000c1c0c40c00d500000d000c50078120040240c008d0300c40c2c5070002c11060751900c0038010030441100c002c034101c20f0280441c503242803142100707402c0403030014040250049000c0c041442e006080e04494040341e80560114011881044010312003d8100e0081c2441c1c1407415010392180c0d180c1106108001000032500d80c0b102d581844107008003100d6500d00e4440d81d40b220300100401c101d0200320b00c103c0321610b054007104824069 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 774487931 1250 774486681 774486781
    0x70305030a0504051c243206010905031f141f090c08150d14010501090e011a0603090a0c0609030611031512010609050c03010807170a0b1806 62
    0x61301e40d203103400c8178800507502000891002468442801504036004043c010035288070803203c80d030f00e03403003003441f41c00d41e4200003001ca90401010081c2044144d4002407481403c0c00903400d6401c00c41c0046074240013504a24550501c0c0840d084140b00707150b088084500d01c051004200711840c1500e903600c0314281c0301c40c494083d00044003080820012100525405e9440350020169007016810346d958071603000700801d05100036551480104540507150099243c22800c1c500204004120940840b00607003400d0900e0b80a40e801000081c2c440008001040b80d05401c040140368641d42c40710000c11104060108441c45820b205a000c0b0310301c0001c0c1a603000b80003444401c5180c20510013807001050001e040b843e520364850070002a001d680d44070f1140100f504190071952581030498091418145034800d1442e00b1983c4408503524802080c2d007411395610400780c100717079120b000c250301c0b52851014441680d40109400d2012203862100c1c2444001034142030183c50412418401503d01c02c1c0c111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 774489181 1250 774487931 774487943
    0x15090321030610050408100f061a220e240105070f0308091c020f0c01090803040b1321110f01201203130b090303040c17070305030a0504051c 62
    0x101041c0b0b1807400c14601d0350300d0811407408a00341540c840e191840c203505030f083ca4210650341c0750000b03c00c2007a0301880000e088445076108090014181d0070b4507521588171020308546426182003403a000f664102001880c6207840e40c1041e007802c1707082800040300c152490100040d1103000e03800c2540101c1c02e50740a11340080c0051403006a81e2801c2d228110300070444040c2d40640030203454a000f02481142d40322589500030814070b8405201e46103401050811281804001c92040000030f000104880983e10305020403500c640101c0340103000c290b10340d004240700000880560b100303981100082c22002d07000e00d59002c01c200300041031087c0e0800c5042440d0024141c8500d42081078402c041140e60050b6002c02c0318811103081322109016001902c1c841805060070707100b0003c0c0105515030035041502070700a50701d5400c090390b07402c444603124415400c058107003a0b01440c40d201d00344810801160407506403a912000c034840141150300a01945120f00410703c1c405055038000c221100f42554005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 774490431 1250 774489181 774489187
    0xf09050a0b030c09120303130b09210c0c0604062a021c080c071401090806091c0216060503090f0a020607110a0f09090c0b130509130215090321 63
    0x5043c41079440300c04e4007a04510040e00c2483d0034001080207512400310103c401004002500c1c26002059000d0030703100e03595010310240b9040c40d005100d081c100e0309002e40e003580c0e1048003c0403141084840111294070140105001032803d4200605110860341c80141c015004102c00c4d25241103290a00c0c080c1d04a0812407410009a40103040c0c50101d03801004e45504281d6440b100f02c0c07030841d00d80c01010340840100049555075800c60700c500c010340300da600500718a24180c5400d80e66400c5103080601041c060100b2a0300c01c600a00515001d1074104144141c4079444690192150703100f0703103000000e449844005501c4400108041c015198001c040f0780c071388541503c9000782c4800c200078842d0300821610002030051800d0a00f040108100480403c820507141000da44071a80b40d88401c80149080004030144034a5041103819124111100e8180b612410a080305008004400a404c280c01f500c2400d018000341014001046040b01200c080c410f016110300d150810301e0858400c0343c10b0034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 774491681 1250 774490431 774490441
    0x703081305042a050a0509130c0f050c0c0904150f1a01020d171509150102060a0605010c02190f0303021b0607030507062a08180d0518040605100f09050a0b03 69
    0x40f8010b0052800c6883c0103407c280c1e08100041d18603500016192015030b0300c080c620551904035110180720a1603081560400c40d44001c610b4030f44440c1424a1701c55006500000c08120031031405000000c12860200b008842d080c1200d4000c0483c0380b540c3c3c1c688000b00064029640c40014982891803043c0d441c0c040001240c0c803803411100c00036080e0021582183d01e0201c1382c1c0c0752082c01c1e074410b01c180441d0003e422945000a41000805000340c2c2c603203402e1202c240a01d9810622191030194141c2d81051025000d440001e10070303c0c03a03044006071644081c0c00100f0b26030f001500c4001140c01504941c0142c80503008c00c2074600c2032090042c0032403000d100d81404104d540d88200170900140f402012007016001e2011008105a1201c0000ca1420810300482031010080d00031600c00d500d005100c00049044003070520701444100c0001c1d0302e00040d18404036100c0303400c144002e050103856038008061582000c0c00340c0c0e0408100c000050081400000d40380341c6134450b44c0440c0c080b001a2491500c030313 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 774492931 1250 774491681 774491687
    0x190213050d0f0203151803030c03190605030714090c040501020a030c05010212130501050a0b090a0b030a05121b0115120501090f060c02010b01170a0b01020703081305042a 75
    0x60241a12804021555400541c0b01030205c21030012440c2c0001c8094500b842a403c1e608582501b560700c81d9005100308910b00300c04004030790b000200c9603800d8000600b2020400301134003040d00425018010400d00291030740c00e0401c04040c1c04030440e1451302c1a561110101000d01551240900581c492100e84020a000d003c140c01e4013809800003602d0540c140d03400071410002034138440202c190a44900301449020b21030980c2001d0000010b20510014a00190403110003400c029405942c841d84170340140c1c4c0c01c002454290741d22034144d400b005d41c1e00c032001c00c00360461224001400c99105001401c980c042c41095594501d0301c003e01c543c030303080a803400392454015000300d40c1596103051010124a800d00003c087e24414038010840c1d14003c20024256441c000c0041d060100c8040d44012903400011810b0340010100400564039181800403841d0100303c0e0300c0a06007041c00508030381801d0544103420207484040d1020300001c01402086401d4034801800000301010884809a4841c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 774494181 1250 774492931 774492949
    0x13151d0d0c051b2d01030e0a021e030f07170601051c030c031209050a1704030308060f01021c050a0201110325030e010c0810060c02090a05060d08040e19021305 70
    0x31014000344400060b14180741441880c00d000c0044513050a06030f9403e540c0d0500a074007428000760042c0084502c641e000c107a5204092018010002c100d810103402c689041107020000e202e110103c9403c26916500500c4510031000c0860f024001e440020905080412803007035807076400045140040d42580b030481d5059007891f011420000154561401c0c4541c40c011381644a00034405060003642d14030f400ba502c40c400220507612114284800c0001ca81c10120b1a40d010740c040c2ea28801040c1c0040c0100d0400c45000105008881c02c0b031a0452010340c420f001c0c200c00000c6030001c0000c2603003000036613518041198001c00c6402c20003409502600c50054081945405003401309161402001d15802d582c0e05548600018105078108115032004e0816880140954108040c0b10581078011a00425000b0a641c1c02c15031180003158150300c46080a0010580103200706488503103400f011240110700751016a05450b507800003c3c4406402d00c2102d411340551500409103629000900c00140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 774495431 1250 774494181 774494233
    0x10605030103122606090108011e02160b0712050c040b09131508010e010b3c0a12111504120c1d01050a06050a050313151d0d0c05 57
    0x80307001c000c07800394100c03c00c00382d41c60b130380708040414200d19202040c0542c0c81016406003010f0ba0400f01c84902100060b8203000c803010424a026130b44200003032404410701e02c1e80ca80204220200340c01c00c03041c0e9601c101c503080c00928696083c0610b844851440e8914000da001d21000204104111445071a084c3c100010071140044003041d21030070080c1c0c407650940540d2010010303035110300000c1e1610341d0030b10610388440300c116440740b0401c041c5000b8140c10600489003c2c113641c80790000201c03a01020440144505005051083d5036844401c403120a01041c0003c4614901d40d000410b050b20b820b0b01c2c240c0a581c080718215081c04d1800804910103418058281d41003100032a020030201c160409031024071303042840621003945800240304078500c143d880401082428807110040a40c0032046035008544038021441c481d001e81007006110304007a9455007000c3c039081d04803080c13954940384c0a041404442c1030700d040c0303007400f0000d8861000c0500000c00030f4010a0407c46080340c1c48144481c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 774496681 1250 774495431 774495437
    0x1050c04090b130504050309030d0206011503050c0c0616030605100c0b06040902090c130b04030503030c181002072c01030b070e030d030b0a05180a0b0102101e110301060503010312 79
    0x70205480190101c4c2d006903004d480940000031362850b1800c04110301c140450f460700c02086590f240c11075244040c2544c90541f01003540701c10219281c2c1c0381d4007059516628070b500a5034844d0408001140000d204000300401080c18080001102d00e4030b440b403500c01d150704d62070b9000c0c1032046a03200500c62100a00c0c140e4801d9880380c030310300907850b08500d03a807043c0154140c0d5966846450080080107110303500a50107200c00300000e0000a01c00f00c140d07034020350707608a91a20f0b00c403901e404c0078034044040394141e005041c2480c0d05140395800221941216000c280d044c1e40c6a000440c840341d00181001c100c2600131501e0010400030308051111640714101d850880300f0a40403900090419045c032840600080c0c07502801a11480d200c000400140710449203075044150070002602040c0e002486110714644d110805040d03a4000c6c0100399000440f203e00300031180c100c4bc12050380180d0b0118440449160841c030010f6402d2010440e0f060700c100340c03078140c10b41c0c0c80c550f105024026600714070410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 774497931 1250 774496681 774496699
    0xe010b03090c01030b0a1d0103020301180f03050c07051203180a05061e0d0204150f0c02180403110d0306090609020a211e02221518030c2601050c04090b 67
    0x583c95030001022103001f41c0001c0c40259500d540109402d40711728108940c01401c80c402090002844008500030aa078103040181e11070035451071107070501e550f560126808c502c3c000c031149000140170004101d5110340400c0d0246d4802e04800780101408940074040d040a401c00480c107085104c1c465a041e005801503140c2d01e4281c540d500d4500b41e07003140d44000840a501c148020f2810b800a60306181080f0602d4031039a601840d8000485044031044001c21420755100030905143c0700b400701e003803900708000c01c59011003419000100102614458108c6042c070740354000c80c3c2c00c0c03050b00884da4201c5866464100c3c410b401d1415130f00d07204440c496658519034600f501e0b88540f2442000341800c1450841c0140c8801a030b03601c40d095403d021000d03220440680300c090100c41c50a80f4004000039041c9002d080c0c0ba04021070700040d089081e0030250080d0b40c42440001c00022a030420949030741c5511320410404c460002c400c5c01e0b124107803101040306074244018002841690700107103610800600c1d40766 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 774499181 1250 774497931 774497939
    0x90703021518270c0306010512132f0105070f030e01020304030c0b0702040c0509030717010f020c060411120d0509130e1b062125090e010b03090c01030b0a 68
    0x40f0782d8010726110300304042c40c65644844942290318040d40328041203552442c1d46003600008100c1d1081c000c501105030310080c00303d0040d010f041d03511070741245d000d02400106404601e152241e4100101035014081211849489551044060b504a258040c1c90010075042540d4240c60040c02401c007281144404c2c0030010100d01e00301e0b1990000d06100b404a81d6a0b85540180010758107540103140138480c0c10010540c1944000443e0001c58002c1120114079403c41082c03140906040f1607505100d40c004030b00300244c0340000c6440303401075200c1c143c03010350701400c20107000b81c80f446080c0c08411500a4511000c03258020001000301250062918503040034462050302150b4041e4182c8245503c62030001002400000d1090841107044902e14142a010140c500d02405258201c0c1c601a8941011a1010412080c94a060140310b03480a0b1150b8200100070410065841004000b0344035500028000280100304d07401001c02e04082c004121140005401030120300381056000414014002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 774500431 1250 774499181 774499189
    0x2090a09050d050a02060604050405150402210105060406050d0302030a030e07050901260102160602090f090c07062906090102070902030a1d061003021c021512090703021518 76
    0x2891402d03103520f6142c0c40c0c0c1142200203203071200c01007aa5000324584020711020550004101c1c030b000d9000c0150f4400d680d2248041070007c050b00d52a4203403540000902c208001c01900100d2007160241d07420003c40f5a141c040004503620788e440500542c1040100e80c515502c08d8001c074050403000c0b011103186175640c0010902c0e104d0264020051a0600054402d03c010110101100380c807500009500340f4401c540d51084100e103001006040640c001750094468441c4a420041c200004013105480d181c0246184640d60100100b100c07180e10380401c0b075403200d0b0740250031001e00411000a5000702c10720418400c1d203038480800241544a80d20300003c1001e80ca0006601c290010341c404034030085000c0340d000c101041f03825003200c0c80c0c00100400c480704100c100c0480c2180d07012940891800c1c40309007681506152050080e421a004141c0a00003040c1c510040c51a280d061080032100d98410300704c65180e06036400004c0d48216050b512802d01000b1388040d2014804600b0100030340300e050380000e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 774501681 1250 774500431 774500443
    0x711151b120d061d100620070906031e050709180c030c081e0c060307050f0d022520130612020405072307061103070e0a0f0b0702090a0905 61
    0x350400d80341c040c24424401c1d994085644013a0214040e900d0703042180d074440045015004d0030003003210740784c1c415001d54465450000c11841a41c03c2d41c1d0300c1c0da142c0419070050b050703d0200ba11100e0708488840503403012041071344803842c0c000001c2c00196003000c6544c4040c1c02400c02c22001807031650f0946010641201610000714401d40365002140e103001041414990165114560011000c0c590061084042070034802c182c07003121125925a20104103640ca03004101120110210100b4a1002c545a075402001c4400103c001e4082a8070540c00a52500030740e0000248910312140c41050501c01e01c581540010134003d04004140304500071000403200e030b50740300d911039402005181041d41841c0c0b141941200891826118145410302c8848054a0003022044110400a085020700030700c1d5020840c81088516030039600e003030503a802428107000010580c410200da04c00001e00300d00141c01842214103502c4d4150401002d074081042018004003a113080d5900d40540c0d0b0001102030002c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 774502931 1250 774501681 774501697
    0x403020612090105070e130902060705060405030a0201110a0f0305040606051c0b060d030804080a0309080a0f2c0409050c030319082202040507020c03070b0711151b12 73
    0x7600081d840d107a4902402d550000c2c04c00801e00007200101d12031601d80315600a080142c0c184041001656407000c11458454100041c0c898003440050204100000c0014210b81140c1e138001c1c40a041801000f5180d803203802c41c000042941501840b50301c9001c0d401a43d4000d0081d18000b8206d6980c3c40803070092124550140300f2850000c102a04000c0c5802c84650407940607501395410080e13661f0007401a040162014214400103d282c14006100c2d401580c0000c1c0d100404a494000a06020313003080511030010700455001409201d048901812800c1e070914040700c00c002d109040303010301c80101401c4400b5100c07405039020020403524200010401c0103100c407900580d0720b1400300c005009100143c1000c14800d400110b8503150407501205071040d6404541c0041c0d07a440740d0506a103004900745449400d80500c00d4009040d03d02300c0c019020244c0a40b00300d802e140040400c2000c007000103082a0715040c4184203d040b40c2004491b803080c1c2e1200142220a00c08454900382516007122031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 774504181 1250 774502931 774502957
    0x40e010e090a14010b011803080f0309010b1c051915020708040302190f09060302030303071103070c0f051002030f0a1b0605191b020c01031a2211031603050c04030206 73
    0x202031400d40d42e1001c0d00306440d81151f01491056030840d41c07108803e00c9242c0c401a42e060010021402c007100c02e52010201c0c200092000364545108080d8400003031100e0411f54041c0155008071710081d18407007040144990159006182c580c0c80c03204500250001403041d244602d0a200110040e180c20010085080b4205103500616203040c0c022005500107801840400d8101113041005850000580b50491203d040018240801061480c0b550084440140183c00d208000041d40208a4402c205442050310104c00c6480445402e03a40d07032180c0410319801c540304001001c050f503c64280c1e0071600002407951100642d1a4580100391441610f40c07a00411001c0000c1c4078480c4c1e240711703111400e8184a030402c0340003007400c0040c1d15801e0101035607041c19210000000651100c00c0c0350001e10700001e00d03208120603503e101c09a041000001d10402614114814102031032074000d50b4400c0d035264a564104c603036481d000310b0141c00042c0016031500c42c11b11000c401030b80c0f0440581002ca903101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 774505431 1250 774504181 774504191
    0x603060203010e010b0a05030f0a090203030a0906180e130201050408120c1614010c26030609010602070324020d050108240c040b0306030c1c06060b040e010e090a1401 73
    0x9540d0f00d5100c00690002034800c400308601c01c06e03a40c2110650b540a0380711024000b40f90394000c040000b400c1000c9000307600d400009030729800780750130500f800c081c5d9140ea0303a000c2c2c103034522041800b4050058040d04402c00031280010303401040200640d5446071042c074040c1c0c1070581d43e440e520301d40680c165000c00e1020340452401106d2004100322284503200300c1401580b6807a020811240f46194414181001060300004040c02907042e408079540c9040001901e400181141c0010142c00944059105050333540002403054030001d9280c1c2501e030400d16860b080f5451070380d030041c110102440128230940030f108034a0107d040c1d1003114000c00d0494060305095104c0c020340aa41072520104060151806007840b0300b1500280a99065480000040d9504e8881e040000d18102e0040d2026600519401090900202c544d401040c154400c0609019194481c0b21f110725900840c00f0740101180c2c10790040110485a09c2000c3d04000c0b20000e94640c03808039114081503c0d840c08544280f43c2d103175 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 774506681 1250 774505431 774505439
    0x50303071e03020a090e151e01080f04050c060705010e07030821070519030213030c1508060d2a0609061d0a0905041703240906010f030c050d060306020301 68
    0x2200c540000750405107011807038011503090180c0100414000c1c5140d00303030f9280002c0c15800c00d0400000b503103c401840c0222001100002d02d075808000d40d00b260004d41e203403000c1514005444806401168080e024001e0300181c042400420f4010740d0302a00c080d034031481a1071452000b80b150340c01841c0030300300303055590600310554400c2010380d40c0c0001d0403074208020410700d25440002c0d240c000310705103403441d41000c0380d401c210041c0c01854807502d01040340e4440002009204074002c01118905d025408115800716000e49202c002141c01c0b58010300d001810070000b0b582c8024541044d1209a11700c0003200ca13011068a05007080e8021300081200c0300f000744480354010142e005c148a248648200041e515404568061424801c2590403522140490204443d004071060354401030901d0a480e8508400801c290101c2e54600342e0030b03403022244040c05820425030181c0718100c1a144d1060329803100d50308900030900c04014200b004400d2100b2481c01d211401904010343c0140c40142c0c0329414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 774507931 1250 774506681 774506717
    0x60a09120305030f061807110a0b1006020d0c0b070e150703030c02060105030a03090b07060e0a0c030c06260a0e161401080106020a03031e0e0616090b0414040905030307 74
    0x17805030341c0309041c1c11120a038114070401c1001d6100c4100d1030900d0710313120140715103850011210030007019a10f00e44100409980740ca0211011208550300700c40404050100070b032200445c1d02c0d005002c028204000911003805401010700012018100030803d44c1e541c8d0308603080303401a800480010740c40301c583c01d40c038950411a403409040114081e06541103980e4000c1c011000c64819084001c0002c969441401310070750210300d541d0041c9090300c01000c240d240c1220f1204440c08121109402000701060882c810001e1801d00c10400400511100f0744d43c540c0c0c504031000809401d0038548602400740f02a000344032101f40100440b40101c12982030000401d1004c0d407039681d00c1d0400a140c00100581d49d8006145d2a1103501400c000032000a0103555412402c9541c02d52a021800c1070030491241600080b4a8810300003e0840541e510754040101c80b034030500d114651b9222010301c018481c3c091100a04506210010b10010321101a40c0e25941550801c44001001c43d0211101040d0008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 774509181 1250 774507931 774507961
    0x2090a080c03070e0603010b0901031202071d01170a1e05010f05070f1d0d0b01031b0305031e0912010b03060901090b0f090a0b090106060f1b02060a0912030503 70
    0x14420301818050300700001203640d8000c94401c0b901d19507042030211700151001e45c0300c081400f03000b500c0c4912a60b10b9051015002403e4401d80b03005108038800040c18503031803142c500e1400c040c103418401030391804283d01c0ba8583d0764000306086000d1080420700141c4224075450000740c009a03500741c18405420a60f08581154000309141130074034040241d1503500c420f40c030781032644505124205c107031344103a0f960300c031007094140356000144c0800a01c140a26902c06e039040b41d20800d00f450b103000b86003030500c100008501c00100240e2090141600211a01000d000c40c2c04011100506024130100060320300001240750307401595542098030b8260405202060780010810000c0c01030309125603c5d46041d8400500c01411200303054003007241070b00184410054150044450804c2d81003c29009000346068494180450042100c80c0c080074024810000c800036900680c4d41c0c904110740138010103030b2140b90440f0400070740444c00b081643c0c0c0c4801c1c510800c0c8c040e90358252686001e03030101d41403007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 774510431 1250 774509181 774509189
    0xa2c0f01030504110d050a0c08060f01140102060a11160c080f0a0b060f1f030c020606100518060c1b0301060e04050a06240603051005010f0207060f0909020d02090a 72
    0x40c1040104000304080740d081c41080700c420f5810110141d17a9050940c1082c8052000400c02d40e00c0800020300e40d400000c415024031444604110140da035026200b680d0003407182d5140c017580001c2c000910014055000c030a47d61800e891161030301450f00350100111104c0e150403107414035041c4080c422280104584898005403800529003802c0f90b48030710074a43c00007064213206405040c410b80281d00d641502c910442d822103000e0401004c17010015000d4a1030104400041c0300c0c0c1e01c0060090301d01040300b1010a40c1d513448d0507140c112031242e40b40b0303c840054241d5821030010071141171812020400b85141d178030300c2c0301d40d242948030641c04c16080d9000d60780310200c1800d02d0414440490302c04214500035692081c40052a09003210019990400307030305150003030802c0c000c2c00203141505074120511a9210244280105403070704019101051034400c07120050344049020f01070389001d240c000c050000343c1d060001d800e030b50351031080050742d00003111021140c0c0c001c52120220705001010501034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 774511681 1250 774510431 774510437
    0x70617070e0d080c0a02150c01050a02040b070f11090906011502010603021e012a1103031204020922060f0c0e01020319030204050d0b01051801080c060a2c0f01 70
    0x9281403400904040342e0b911002c3d1221000041074442e02004229100450368040c00c0ba088031039004004c166541c01c034849080317444d4200400242080041c0c800c4601b501d200da989181071401d00e881c1e5030441c480c2011300319400c00070101312031582c1d5140c0003024492000d00c1d00a05241d8113110703128046810301040c00e401c0d6818080700740010b9a480f0192500d0450889243c081040c0c680012100f92145e107110240d5000102250b842c0d60610091951289001d0100958074580d1071050659030320a04845405003201c0c1c0c0c1c0824014901241040e801215190425a1186203500406d501602000b02110844d6903500d80f00c0894015024528400b200d03428428480c100500021313460f03100f140040d900e804206040c104105000e0390649020384070190135100c10302c0c1580350111b40761030b0030f02809218400e000e402d0b80c140c202c0f0442c500d050b60842c0c0c0107804440c0c260707000e000c05074000f40780d8a401c0c000303031414200707158244a080452882e104225007481400b10310920011300500c0e06004c1c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 774512931 1250 774511681 774511697
    0x602070201020709060f09020a02031204121d0d081b03160308010509040b07050d0e0a0501020408062211010e03061005330304050c060708030f0a020405030c01030b04060807061707 79
    0x3ea41c6d000c0c2d443c00111950544056520307005210101c0c00d620902a41c000d10303200401c00d00060141e00c400007080614161180304800c00f041c8030f00d80c81d410b0814511980081001c101c02c001401d410040c081d400c01c2800b0130801c2900304203142d4219005110b5815102d400070362900305056112103050300428050340e0300e01c941d04068940c0d501e030503c014400700504c540050445090185540507400d0745201d0815188812044d180641c041e52042c03050010510664001c182d040445c40c1c00c40c120407024412400d09444282e603400c4440c00d009284505125140c44d400c0a82c0e2000e00c04244030321924008400481d0802d010084114030a50b140c2c1081200b104022040b00c1050141602a442501c501516960385180461401141e0707982950010f0000c02d00d002004440d4018500030441d205000d0300603a141c60903441240240d11815515501002d2100400c1d40039501c0010000000341c0041085504ca02405d440c00c3c905500820005040540404282140b4140340d078110134a0f18013104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 774514181 1250 774512931 774512939
    0x10503070c0b1b072a080d0c0302070e1f080111071e061d060a1802040f110301150210051303051605060f0a1427010e060103060207020102070906 64
    0x9401c01880080118820702c000c5240d40c50308030000101000840307042030340c8140c03c0c03410310380c1504541c01c4140e011041190082d140d1580780c1510090318030030302c001c0204e040c3c005c0085032440507980096095008115000c900b2500205174140300f952000703410101e40c40842e90024450000d035000741040d91400c0c82035520000c050b4211003041c2d810043c02881c044440960880364100000b0003400d844c41c0600150340358642d043d40c03500d842ca040007551920fa441364003100546c0c0102c08610b00c0f0314050000b200042c500303035110555051a4150014450101c0d001c6508141c0c0280c00414416400407074000c000355040014100d030112202041c00181404455489001d80c0d41600500f0b10a001c0b650b40d40105948030701c0c01c4800c2e000800c50b1a1410900420000380e041550a1403010f800c1c010f05030740c0f040084c40810b015440c1820f245612a08000c480303980307014041d103030810380e549a1060b03a05d180402c01c60540a10700910b00181c1e0790003d4030001e8a080c4c820360041400606140c0104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 774515431 1250 774514181 774514187
    0xb100906180e1620070e090609030703120e151f03080403020108180a030f1b030206010b1602040906050a0617061311040510030210030e06010510090e04080c010b01050307 75
    0x43e0000e0300c1c044900c0c00741c016074500342e0343c0080f19241d20f81341c3c1640c0416448810b40005641c03040b602d48010411881c0c03201009192940300454403130f20542d05c20402c410000341302c0e1006182141781c07484005000b408040c00d2505080300b442c000f00718000720341705104009081c1c600540c103403145440e883c00315615654654625002c1c0e0f21010781400300c0c084c0010180014600b02c00c040340790120503100450503d144c0500702414070b10904000410341003d070f80070121494024084943c05800070200e43c1c0c600a081e8000707903c80f018005030b9105501080005842d07a0152300314041c400c150115080c5001402d40c0c013207d1030b40d0300030300c90010101c0d2040b074030b1080071a01603003050105484156000003414180e850b400c80f0002e450300145040100054090b4221400d01900d01c00c40d80b1000030401d0035000c5040c1c58413211200c0d16500010010045854185000240c000e001d0034500341195a84545001203281290156550a0f00160404041500b0302c1112624030003401c09e2400c4d803d0408000f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 774516681 1250 774515431 774515459
    0x306080c0a0308030912070c1a0703050d09140a0303140709050d030c02041d030306040b0402031512250611150c0306130e030c010506040507020c0d060b10090618 71
    0xf4205540c00800321708200c00910103690200d04840d4010f80d01d907101e01d4005480207107031140009800d801484502040043c0b41101d2031240c06545450070041a11f208000070a101c060466119000350b80c1064500c605201c10300700b050294a00007503c032046040b220b60000c00900340c4081040c046402c1c0300c0c0da40c85a02801e0004d4240c5405060704050f1f03c00f0400910302811002c1200d0340e0440a13024071200040110710460701690140300604448003840140e020556149541401d1414041c11030308003584142030143c1e050040711003200580c400910524220620a50003c0034100d007840706603040041e5200101c064001040b4090020303114288218002c2d11241130702c0c000001040c0c0700d64888803100801c40b5200010000e220b0446061907690780200741086640d4200300c00034950f031500d44a107d1007100c2c40e4014011203022f14040040b02043c6000440e0481e5440d03400000d6601c03080c417281aa0605a00d501221a0801d80d010b0140c801300c1c041c0700100d04100c2018004410714000c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 774517931 1250 774516681 774516683
    0x140a02060c0a05090613092315030c0604090501172107140105010906090b0303031005040b0a1205060f0108010203060d080f07061107020a151b02011e020105070306080c0a03 76
    0x24807a12124003000445040c414061219801200821070f40c20006d10840c00b0821508046810000c10001d10420142076140411240b0700c10940000903400000c9008245030141d001401e4801641c20000040d01e950084d07084000f030690b543d0f006200880050781002280c038806d100629440007003440d240903040c0c445180344610400070422504011101c7c1000880030303c0580240074960b100c074481c40080c1100d11502d000c450030912018164200402200d0250403880c94140d1000e041000744406865518000e5400081040c40041c01341c001d100200c202602c154042d0169080281e880742c4181d006800440d00c0e40d02c1081800704580c1d4821a66104035400004292140b400b036204000900949002910450500c0c1e885003440103560000c0c13142c0340c03084605440e955212800a0100b0700e403d142c600c0890440801c070364040c007401d031072480034610502d03000c50032a401300d00395210713000c4020980015039158002d200e80d6503094000c18002d02140e1008194540c0003078005807518402d0303c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 774519181 1250 774517931 774517951
    0xc07030318030819030f0c050403020f0604030c0b070318061706061b010f11040608011206090206070503190e01020703150e0307080a0305010f03030c060218040e030a140a0206 77
    0x140c009501824074000700c025508610f9180e00d0b0301c102440981030301005075014000901c2c101001c040303070300e60344075180c0958015a0751504081c196800d201d002841d00109940c8118144000030000d0711965410015004c1c6042c4e250b20f903452880e002c0c010358490460b504600c43c00c130360140030483d8010810483c030101c29858034103545880b00804c8561099450078004842c2c0c05d40d50548046054101046581c2c1c0444208044005000302c51880e0103140034020004640100421828140800c00000e4034001d120005454109078001011a880507070111034580021038005001d07a40c500c1041008003241c00c01440b66910103000039201c583c140401440b41641c00c0d0040c0b0a105160300071041507051900b12a69203601d4285101140c02010480340000d0804001090380311940010000301d0f80c1c10748800681d054280c0d5514041d41111300700b070062402e8054400020b9903175024409458107224003841c0d4903000790100815038005003804d051302e42c800300610302c0003640c006510759000781552 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 774520431 1250 774519181 774519197
    0xf020d03020415080a1b20010e0706120209220b0d02030c0d0305090a0803030103120e0a03020d0311010507110f0109200321030f07020105100e0c12010f1a0c070303 72
    0x1600300002005400d1b00140424000c4480442d006e402c107402000b50414402518480d541c3e00604600380c55007003c0c00007042d0004071702004403500a0244e914078603200c840140c181454840403420f144011511075244039035041c2c1d2002c0c1c00340310384691000014150b81c440300340ec5403a0082907903650040e041c82c0c00344551148500c00d2520400995140e040001c1c41c61580c01c1d80c400c0703c150b89030028007082e50005070f0000380010f01400766404680d1105c018100540c068599020402840b0202c00140e042c400e18078403c0c100b4001c01c0c81401e00c1032255840c0d107103514040c0300e1042d10b05034030071110841c242c3c505030300e80340404c01403004548410b01c4505c051000c0c80701c01d4046030508450841445152000501808148030041f025510a04401040700480e03034a0100880c241c07442900d2135264001850001d121070f84407280300c80da01c0300384401054a0031350103100761001e03005c1c02d0707000007903c41c6840344c00d1282c0455022007401e0010004540d50034140c0b14221662684034501c40103060000003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 774521681 1250 774520431 774520441
    0x140a0602120a0b031b01050405040f0b120a111003020f12040606090c0c060b060702030715080a090b06130e030c07090e0a081c0612060902042f090a0b04060f020d0302041508 76
    0x43c0d1f04950103802c0180c0280b160292104843c006440d08001903849941c45201803c201e46000501c2840700e074200d020850000d88541c103002c5104201d100020415400300071482900e83c00500030030541000c00d168001da0314007428a08121402034120b120501d041c070b00d100030502d80c07229500050580052000900c00d910100040c1c65114100000307405010b0b0500006111060310407407000410300746c80d03600341503070382c03000e040222009680010300702c0201c0000300e52541001c82c420505160700150000300300c910300e5a000e00e540c00c009184222984642000d00824007a406540881c29186008084140300e90380c804586020302401001d0007850f0380403402c0041300070b80028000702110120004000000d08041c1c1c064003d014082e0f00541c20100c10b550b002c11007003020312058001105183c401029498900b44941c00519039aa1040d2180e0340440d488509500500091545880380340c15079542401c007900704441d205403142410b10500081000044815480c4184000c0303107412071503079842d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 774522931 1250 774521681 774521687
    0x9010e030709090c060315052d0a12021f050f130b07030305010e15010503071101060305072903070c0210180f170105060d030c140a0602120a0b031b01 66
    0x74981c452410b0908081410051200e4040ca05060310700540d42031203000004444030400840038032a042d0006040240049440b54924070014030007480007442402c150b00c1ca0024400306940d40103102c11510000c0d1040c2140360000e00740380c0203401078150003140521400d000d00a03000340b40811000101c00900d0282e801845003685010340001d500f03168a610150900070000d2500f401602410480e00d00454141802100400780030f81c01656510302c0e60352429012a02810310100c00b000c0c1d50340f20500400066014070000c000f90100120320405080d500c1740754095a807403009501c290000030414008056802070407485a641c06883c01c01030070b4105c01045500e031007103440c0001c1c0020800d0002c1103c07221030841e0011174600010300c5243e419000c00d400e088031002c0c0c580c0c0d580030840d0901c000002e4094110110003d001d1b10324003030381742c001609250400f22188001c86500340e00049072034404500d044107581200713940408100807803030600030a907144032030541405021b031001140c4100c1d80c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 774524181 1250 774522931 774522943
    0x14150f1501120c23090a06050c0c03070909060501171507050903011d0d0f2304050607030c0c0b030f390903100b0d0308070e061207021203070509010e03 67
    0x3540e02810404000c844100030301035502c8400304412001004c24001c60150001c003a2044510700800380d01d50b0900d00101625154030201468038540601c0c07105200583c0c0074000080108020760340441e100746640b8008040701c0c0d050300182020500341001e02c40407100040c40b540d00904108050031245c560b800150f81c03a0140e05d041603419070074103059000c1280c406c4029811040001d0440e1160f00790080b003030304c07001c0070041140001100c0c400d246198040200c51760000303900050030286040d4803440403c0450b8002c04083d4003090394003540d0420058007400c0b4030020245542d05508509000d2001c0b29180307006001c00d0409807000900c048034a400d400d51400401e1180c00b0412600c1a10f0b030b01034029003050b00403e1190190581c1c370181041a401040c002590082c02d240790b10440da0741c01c3d01c0e5054080c0c020b90030030548580300034442c0c441100401c8401d802c441d01242501c0c114034000d10708405550684079a030014020b1111443e007003010b0300c80d00202400d04001265030003012a140c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 774525431 1250 774524181 774524207
    0x12c120a0318030e01030e031c0f02090306010b0c0f01060e0f100f2603090312070602071505060f040b100318050105010f06090b09220207020d14150f1501 68
    0x14001d9100100300f540007210360402c240c0030380303044c0900042c507004582c4038000c01804880103100080d003070340e20f040303e584696401e00340640e006081c40c9101001c03900d8030100740c01c000c8804400203110b01594004008000e00000c1c803400078400c860910200200d5a80081e1400420307502400100b92650304c9000d01e200034091040c654262950b8806424200040000b4000d03130181000010b840c4001c07021049079203920001d0003c050700b490400c480c06143d48100000d482c8a41e091086200241098800c1d00c1400f94103e0086064105201001030181c440442c03544698646184042d068940d00020554030038035050019241d03400702e000e0003202c0d0760500d0060165280800218100b050402402c00b51111703a03441001c000d498041c2164148110480c05510200d529403014031108804074565060b101c0a002605160076580403030416005801704441405080c2d8640004403402c0002103910b0039020384100840c20700b00c802641034000500100c0d03164140d0041044180d011f003003000170b06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 774526681 1250 774525431 774525461
    0x10051309060e0d0e010201050c0702310c0e011d120a0609051b01090b0f0d020c03120f070c110907051c05040209010f030503031323012c120a03 63
    0x42510703103501545580c652048800403030103403581303d4145d51052003041e10586900b41420700d402d04030b4081004130f900921007484540151842d04030080700d410001e40d984506100d01142c84400c1c8c15001e40b00d003d10086d40c0b41086060010003000401d0b48403c2211400b09807000032a8030141c0300e1040c18155410b4000d445a81082c84510030010005a0303101e00f85444504281e034640800300440314840584901c250150080c8007501181e90004024081c92a50034001840c200c0d5064034182140c101408518804c0c0d0b05108001d802000c0c085c481e40d00c4030040c5841d1580040c9070b5a121201d50003d1140f601070702044000540040c014012613884104240000307070030141003052000900002c850032030050b00351000000c3e61140e010014000e40b41d03c80042d60860741e483e0103242da4500a0001a540559903100110107052290109441179101e003002044041a40340342d200d1041c10300a02a6040ca00101404481900803a004504284120380301e592400d054800700c025052000b00e503103036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 774527931 1250 774526681 774526691
    0x303181207030504030c09050c03040605100510050a0305010501091d0a020f12070219120804030c0213200a02030a120e0d0801060e01090302010207050f03030c06070c050708061005130906 82
    0x20b26030004041c0c001c40b0711621000703200586a01c1124107a6005858003210360105001050008016400c50b5a000c501024912041961040064107071a1b008034a6800314400140b001d1100c1d515002d0707a4052710080c2042e01c20302e45440064882d46000d4103100b070032480c95401003114098103804403403000e100d10b42c07050340b2810ba0750400382c0d40c403a09903001000761081e6200c86e02904051202d99001c141c01c00303040c004002c1151015a205039000344201c0410450b81c00000050307035480c201f44401c0e9040e5100241c81c41006040c00307441c6580111318180d5031014408003c19a600004035440e04c03843e0f18020700c44901d0300580c0c4000c1d000c83c040740c2065004001004031003651002c1c0d0070b030407070b1056070319503040e484183e005498100150002900580000200713201d80c1c02d100140d50910784002d012245050242148c0700d003003800030744442d40012081a00c41b0240001080801c0c060003104000d00043d05103002d040c0d102854610544c1e0047c07002c903105140d5041140c0c060310643e0f400c01c0c1d044c40303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 774529181 1250 774527931 774527933
    0x92701090914100605100e010816020c0301110d0605181b0c070902070614040b06011b1b08120f0d200c1501090204032625230303181207 60
    0x4d0181030284030300515038061080860b0b0b00c1080110307440441a100d8405584039034050503020004a943c3d403003984501c6050800c107807024031a41e4050302d00700d99404d4488072048448026120103030300403072040300c182a5601c0303a02d91a0fa00c7ca500015000e50302c40f407000643c914076005000701d00d03030586207028142c0006810300c6240c00500d4814462030040080025980940c00c5800302900c0c00b802c017843c0c00000404a5010702040c60b00f031000f81040800881843e50303410422100e90300161401203d00c102005005010068075000c4410280002d003403120310411042140110f8602141040d00c0301c208040c03c0c000115105900d482181407240e441c50522003081d500c3c0c06a20000c80d000809000008202c1e002d4820b90301641c0d070017101c204011659440002c40e496910b1040c0302034001c100401014410816000d076940200b462554402000c21b00f0b00b006048510320b10000441c071190039912410781d001c0300b180d600c80340307420340b8403000007500040c50b02e80421060000c46018001070048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 774530431 1250 774529181 774529213
    0x11091f11060711070b04140405101a0903060703020c060417090a080607080a150603050c040b130812070f080c0a0c0605070c0f0f1215050705092701090914 68
    0x2000b200f201e00c201c40120703a43c2c0c14140ca0601ca9885410403003007456207090701e00d10b03298000b1a04105491012031030180c03560070034145200000502e1003030100c00140d2014505050140c40e5208100c0d05085007008100c118181e12604000c1000340612619000b180000d181903003070b91600c0c000541019130103502d60982e9907480030240c80d500d0200707145d4800158500481d0080c8903c405400444007600d518000040e00a0b000240409030142d00c01d1001190180071500034000708090000904102d0789031130034550030407045000701c211a410400040011170310001d411529103901443d1039a0320360000c01c07054108018008000c1c81611807000000d5000d62000150003064015414407200340e660705280c1446510318420440c011400303c0041100440c03840542d00460b000c0c017907040344095a43d01040444d4030450748a40490404550000b150910581c0050b03c010200800c02c020345841c4040390a100e01403203034a00b002d403107900c00e00800c8000c80c800d1a05820000489145510f041002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 774531681 1250 774530431 774530447
    0x60f040b0a110105090d020d14041a04031716020603150d140f06091209060c0d090311030c01140f070b0415050c03010b0a1805090f04050111091f110607 67
    0x42c0c80341d0740c2401c001c0f80f00c07a100440c105c0c05c05000c5800808400030540b2080e2821902030a000400d001c1c1800300040c08004180c1045038161001a401e56485c00c0d80740104201802c0000510900c10510000e02003d0300855540d0000d40c040742c01c2d40d207990300c0b4000c82e44825000a140d94200c2c1c0640b141204100e0340d6024201c1c1405844c041d151070450b100340c02d95a41608507140380c220fa002400c00d000c3d2a4140004009a5501074016854071000d840020716010000c0003100014001d0b20b01041804040c40708502409800c5018015429800000030220012003000401d079003000540809038590b448111040c2d00c2d40032951803141d04d4903040c1070b6812800c00501c1c20455091800149a8a00c0507088130706031a402064107090180003e01218142e444210035907401d0b504810110741076507201e600510800540d0a10b0b81c0d2071820749481421340b210903140350243c21041c4031107910b40e0795041c0c03c03501d0060400d501005080000100300c0324080007884a0301030f40544030601c0034050340020340d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 774532931 1250 774531681 774531707
    0xd021c06060f050f031b010c14030d05070302071a190e0604021314010b070f06020309031305010509060a11010f052d0417032a07032c060f040b0a 64
    0x110360030b100c0c1c0e514284424426440102e690680110307103074810b0010320305080c002d044018588406800c001f035603140c800d0600d100c9550219440450341078003000c1c1034042e507030740211240f40a505121080c5c1c1c44180e140c1c02c0c210b8407031410002400007910072840f034481d035003581d0407c0010711100c0c84041d5a244c40d04000d0b00c00ba80100b5101520401c00407c0340144090544207044004c0a0303840c0c450740682580050340c084865218040403c404501e02c0d001442c05021204041e40da074900d54150b658940300a5031003a81030100a125111540d0b80701400d80c0c503201924100302d104160b42c41c18040c010302d0309810072410b142c074010500480c101400c0500341811040313000c40d5182c1d400f48801080c0940d0442c0d00900103842d100d0505a98869007001c2c40d008403000b00340c541600c101c203e1503005e144d122a4030649401001c120201455404070302000721280c0031480349250303446003000e8407040020010507030250300e002400c2d0201d5001c8030125001042207421150300d41344c840700e00510f902c40d00ca030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 774534181 1250 774532931 774532949
    0xe040f0216050114010515070318030c0806102702040801060b0a11010e0703060b011803030e031b060a03091a07051306050c0d030b010306030b0f040309080604110d021c0606 76
    0x4120b0311013001da20b4100c5c140c1c1c038014110044410024200f000ba58402d503403c030104650090515804051110000e020318403400c46124181e003000e040d00d01d0b0140003400d501e500ba184082c00c1158100c00031906d00712122550100c2189480f15000d81c02034800e940c04a503480d032030998001036500c0c100e4050b0890800301d580304102142004265400d0b03844004290601c0d40140c041000002c17503543c05442c28007418140100c0d1051214190429039800340d2065002c0340303080e200c4d80c07202c2c80d0030300c1032004a0603203e00040c030700d4010030301083d0b85010342d0340a041419039442c9074900380607240d2a41d0103503a48440722420700340b802520040564201e144028074401030818080b41190268064541e07000403600100782c1602c00c000c5c100d001d0726900c00e0341030526a407600007001007213800820078410000104401c8090802c0e25004100a5696000000582101d820b000c00038242d8011041e24071001c03100c4440080e42c1d4000142081203c2c00404000b550180e50041004403e410010441342e0b03641d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 774535431 1250 774534181 774534191
    0x30921141206120304270b060d050415021314041e2f0a180f030f050f0606061b011407030903020c060a050906031509071e1b030e040f02160501 63
    0xe0481e43d2801540105142c0085200d418a1540308a00c3c010f00b00706d05a450100f01c041c1041c0220326242d1048a102d24500c2d03e07502003205004002e04581d410f20002032045240c0610300c060b200e0904000e0040203020b8099400c00d0f009a42d0b190032041800c171380749066886500e100d042b4407008203442c0050500d42c245155000034061101c440590580c60007106062600c441410100c41c0020841d001c03155141440401003031b12480c5441407000b651044400082421440c18041c1c42c241800041d03075002d1b8816010011507446107000da415030000e520820710441c00c10048203024202450b40d030605000c0040c20000025450740000080501070b40070f48115248010900041d40f06400341e99000c10401c0240e074486040810043d9400703410401c00404484c000c00005808407820303900f0200040d66000c02d94040c1c0010404450205080d09041b40c0186803840710b916003480c0c00e00e0103024014660165000b070303244c86d00460203410448a00710755441c1c0380186603240200d104415586580f034a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 774536681 1250 774535431 774535459
    0xd06140f060405040c0620030a020c0915010212071416090f142206090b10080a021f0c15021c0b0619050d02030c0702010f030921141206 60
    0x10f881498011900309415aa4041c2003482c180d030f600304500c600b070105c40c0d07605074200c1e55001c090003c1d000d000b03070303a501500c448814402000320b11403000d40300d2113101d02411803c060582c6c0004140e00740c01d148044c0309480d5850360a02c01100c040500ba808994014045403246084001242070705655034400d08000e002e169144003011101c00e009a6101804643d02084120f401000c0e02092038602c00100d20f0707052610780e81c1005923400007508452246071001440048010481c92401401007074005003403411b10345c5c0004001e001c0c080b240c00811583c402c808076200b4170451480404176000000189810303050144207009601c45001c28a802e40484442c80b03403104103019251035050000c1900d03007080d0110103100d0768000e80e40010000d12500300701e0130005441900241d4070805070000446e807221074034000507041c401c4a01039401094503100c00c2800103040811040700c1100d002c002c1003449000b5520540700040b60b403526508002d004030b94410721110707601583c0d2084409481110013003400b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 774537931 1250 774536681 774536689
    0xf050901020307021f150b04030c08061009020721080402040e01090c05040f180309080105060904080313140a060f11090603040602091309150b15090405060d06140f06 73
    0xc10344440c00140c010b0a030400350041e1103144c45c070a508541a0020705004403651180d540d140a5001041014021a04005001001911100910080c3d0107003080d40360481ea00c00c07804a0341d00607031003060381c041064010b02c00c6061526a81d80151405030700500e50404011b0071910044904a10603818500c0500000c2818020114499400a140f0070401d0030002000080c000481030310344020342d00c0c0d030345040c0044603c420001035402921201185420144c0540c00d59800400050082c80e00e403081c0000100040201c03540006070240c039200102a920348941c4052040e215040d0500c2072001040a02850341e1010b038258000b08410407000484203060840c601807103140135800b200a00014011401c0390300106a44000100040428001c2080e008100d4044081c1612401002d01c03800809010354440c004d140030044038040c0d0361000c0550546218070907003a10074001c0f9141c50105125844001c0300c02c03021a03100c00305101010505107050540da8040b25510780d1115038031301241d15410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 774539181 1250 774537931 774537937
    0x180a090e0c04050901150f1719080c0a020a06091d010302030c010c110603040f11120c010309050709391b140a05100605030c0303040e04140307060f05090102 69
    0x448007802401940c48100001004000d040004039504c5894006400300c94410400c050310980d41040f1204e405d00404c102801d44a01d2106c032a03900c00c07120340450b812151200c0c1441c5611101e11070341c1ea000480c00c141000139100f0002e40101c04d800380850543e070400e404505888140c400c14100e2011018041d841610a202c0030350103400210041005520602201042e0743c011000b40303164804100105030507034812502a108981420443c0302001841c8406440d1014119845010300c8003a926207910307564100c0d0020705042e070315a02c3d41d0800c41e060101500400c0d40d524100644035112100004502d01c00303415104001c81d040124640c00b0a100e911082140d66581704039861020843c412100108280c069a41e82d60b070001c061908842040301d004114843c00180030b0300740241001c04150340154101c80e01c0380e04081c0c10085242c60000c161000c940701d41d46070740481d4a40c0c1c103141d60300d0444180744030080e001c0003a00c201800215001000d80f00e56a0301c04100c0c1c1c0c0e5452400314202c1c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 774540431 1250 774539181 774539201
    0x906050a270b0402010e060403050304150f0c0210030509010b03011503121404030b0705161103070f050d1101090503030c06220519060219091805041e030c08180a09 72
    0x42c2c140c0740440c026502c16180c803600400082d007940d20b00703500d0740ca40905d10f4215a1107201d0380f05001c80746901c11640310105d18042d00081c00d0038003004c589540003c0f046080c12900c039040564900c0010b4281609400242c68080058002c021181884901b400154041d000681d108076a10000040d098030605000031019181c607207030340c10a811581c0d81844030030080e04400800906004810301c0c0e41d4103408102d641807150840e0800080ca44043c1414040c0c00c3c2c0c003920310b0090000040020340c890903c40e0000387e40c01850385106141c001c005951404090300800e41620010032001440a000242e490140d0704100810010600410640443c50684003005080c2d42061000e90110f500c5912035030340440c8207020260a103098019040c0901b48125080c00025000310002c2106880907a4600c42c1155888810300252405443c0c1c150207128100710700c42c490059402c034205141c42a03089608441e846458a50f0701c013003102c00b4100d0a8000c04180e8070074030b03144400040c400158400d0426903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 774541681 1250 774540431 774540443
    0x60501080c06040924120b060405060d06020904150e0901061e12110910030b010b0a080609043816020d1b060507020a031404030221010906050a27 64
    0x300e4209480030001c2c090082d0100a905d0710248101c1803c000d502203080580703000100c20440b44c003c0e080440d8803000207072090740910300c1d01003840070740c0d10381c003c00c02060342d0442c1c070140c1e903a170203840441c5c01013491400f0500e501d058404085074040503081c18600030801000248400f03521041520313560104c1080000301d02d605240100403c85401e48500740040c0900207240109a0300008540c04800c101c80072015216030344024010001c4030341752580504035080c0b01e603003000740c03c0d140a00040700c094441440b940c6140b0025080000f451391648400d03030840d000b00c0c542400c90851740558201c200e14140080e52510000742c072001e0243c41081b102025500400300f1a00e80c0c0401d903108560625203918411019440c0e00c00304841f03000e068081c05456004060301007490800400411140c00741d41d02e4000204810030259603080c0ea860f410030070b00d0400001c007650809049004200446000300060b060004000c01194154081200301c4000700191400c480e031801032175400071821b5002061 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 774542931 1250 774541681 774541687
    0x31d061605010f0e10180b0a090f05011a010e060306010c031803021206010f1707051c050f2d0318011103040b090f0603090a030c02010921060501080c06 67
    0x100400022100c020540104000520403078820000c90941d03100c0c1074410740035800030340c0030107038414244108080328400d000c48000f03c800580d00c00c80e60b410040c241a036100d49800e60b403010f01414140010002e507002e80200000c00c0b13403404640300d11210044c1d5a009c00c141454544003410a281228402c500580d180e01c191140c5907000d4902600c2d80c620300070945c141420100058a912203808115442003000f000a580f42c0420700f1085410782d04a94903040c5200030140e16640700080c101d0139100c0880d12a00304440880c072050f01005100c102070560312541030810341401000c2884103840910060034100140d20b181102c811003e07101041c500e6910402410244500d0790f4110441c420051400240d82a060540e0500d1038115411005c43d1070b00000c7d80c842e051400d20b0004d000e1520544116045182c403e01d480c3e2101c041ca40050107001c20700e9000401c5a110300c3e003800117841201043d62101070500c400c1d050200d00351108039940c1d86484004140c00701b0010300345060100041c0a90b103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 774544181 1250 774542931 774542947
    0x402090402240703050d0b030102130306020a03230601080702061909050a0203010c020322050f040b13050a020c06180c19030506011202131505041806090b04031d06 72
    0x4101c0c641c40402810b40380381204110740e5040c0c030000c0400c14069941e507034036048242d0401046521520f0f405129a20410181c22a00041445c1030304694120f00300689920046c4420b4020340b001d0410f000b548038813484c001c8400341d05602000e000c1c4038283d80c1d1240c0d60750707002d0013665654010340c1c0304039028030784101d1004102d0701c0e038008280a84c843c0c810b07564086e42590100e800c0d90250044840540c1001c01c060700d0f142100f004d50501e107403114610281c210302d0407005c5000700c04405a5140100d1720b44280c90b80750b45581c410900240c42c5150104141d2038840703e080000d4101c1085484940503000100b8074400c2d0464080e00e403005184040c1c0f080700103900802907039040c41c0981038000090a040000420300034003446000300400381400d07061103860702c10002080ca1841200540603e0042c1c42080c00074241401010348400b601d0020b0a09020116801c425039007400061803d0304180380c140030861842d41c81c9000b1880b0b51504055822004001c00c600f84c03141d2403c540007001400084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 774545431 1250 774544181 774544189
    0xd03050c162601020433080402010906080a09020a090b0a0e160c031803201210020c0327010e0306010b0a08070c0f0f0b0a14010306020c0f0a0f0b0606030402090402 72
    0x3040303040b650001440d080d80da51480412402c910951070030481c42040400381800e01603818200c10501c1d2800901a1070f060340003038640c00c4140106000c210101c1c0000301c20080c6584030020740c507001490070b45d440d661908080c0c06030980028107400303620040d0000a41c00c40100782c250103140203c030341c5880c02250540031034500c200ea00042e0304010000800440358015100c0c90700155001c0c0f00100340f1040a81c506601c0441d5040c400b502890720821080315100010a421040c6102c2c910301603920800e1a05080c030714007965050221103c0801d10302c08031804121102d003820f00c000e813036544140e900c1d60308260b11143d092103110301d4164200101c0c070441c0d2064030040c0e030211490030400c5e00c4402e5629101c0d500403100204496650044000c1005d000d40c0301c1103141d02860a602c1400030003070a46000040040620001709595000704881860103024031104000e030000004850700c0000e503080105007c408008107071110319500303000c12102d080c114222885150086c01104550301d890f0700344 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 774546681 1250 774545431 774545489
    0x503030f19050f0714120309030d0c140c030301080705010e01050d0b060f04081506040b01091a071b1a0301051806041b030b031018140c0d03050c16 65
    0x41002c00408000030480c2c0440c660107400d0740d40c014035421040030100000d80b460803510b207901080740c80080c0200300c0c682500004a5614040012001c6100000203c066500c0c1c0040b15188984a8000c204a5103d44001000d14100c41140044803030041e900c1c030040d07507030404104c0403500190041040c005001400e4011208000c8090a4a440c1440d20141c3c00c8050f0440c0d040b1203041d40080b0341e26510000a2100d16030000000c039001c01c142c1c450400041c0c00340c442c81c81602100602543da08070315440140c2a145080d41211101000a4000544401a10403409140d503494107090100d4500c602400035070341030b9a0007400070900140e00120b402548940108a0395110b0346580003500100305001103007004030750648010400b1802c8030101410711245504000c8540d20f41940d450386080414011181c0d5604010551004a290120a800c041c54004466007107440e4891482c00c0540c00401000802c0591040da1a41540800c141a41e058140709008070740340100c0414007040700800f44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 774547931 1250 774546681 774546727
    0x1e02011b120f0905030d030203070206060117181c020703030206100605090108091009051f091a0903041703040e01060503150111070906030c0e09030a0206040b041109041b0503030f 79
    0x400c0140f1555076001901e8618182c5034000066004410310503042d8041120507004070003400c0c10182030021101c0c10700301c00d00090603011031303a414003c07840c0342c8071041c050444c5820000c81100041c40b0200d20203591143e003444110014807800000489100c011404881036528581c0c0c0c01d032402c18850011105058007901249640c050340407500c004044034401c2c42c82c1d01d4401c201812078112158000082850380b080e014442074140000b440009250f0100000c0d090b100380250060b0f625148110352450146800c00722146904c0b800d4620340c50000000341c001c8946002c00c8200c280c0e200d1004881c0b5000948041d005890007600e0a4030945c0620051401610380f0001c840c0030998030500301d41501c110340c0c01525440c1c0082da041c80b0061400c013a00f64081c1c08040258a031040e030f50b43c001d54a40008001900c6181d100002c01c0801035514900740700e50b03c00401d800c481d400e1504103080121568000199021070500c0002401e0401209803040c0e40040c0c21068182140d04903001140b2412000e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 774549181 1250 774547931 774547937
    0x801060809032713061814010b0a0c0203030c070504180b16121404050f01090210030506040204050904050c0118050d030302030a0b04020f07141204031101020a1e02011b120f 76
    0x20540c0c1c0c43d600c6000e03001010303464901021603907600d0511a103680e03000301400c1c8071100b030909480780c0d2414018140503044640550410f56200e02900d8111659145210001e50500000800d100442000140041078a508403003c0083c4c2d0400700340d5140a004030000105225404c80c0010f8903003207484030b4a03803c840581400003086001c85214001c40b041c01daa6001c10498590a010034001c0c10032109507034542c000001c000042003074000600741c00002c4402c004141c0c076900010103a8440ba016035008010142141c0003504040c58480e45070001c40d48102e00180d1070030000c0c1e1014000c0703419581290380182c80170165140c0b0352002c42c0658030080181c042d60340c40e21050051600d0320320061030040030b1004425103506861070010b25802a4156180091b40030360500030031500d0440c00c550490364072580b403107161584240182c0c1442200040030302500d6808107000b180216082002e00b09030710036078407002141e1014207040403500303450001401c103240000303c043c0c40900501264070380301c2043c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 774550431 1250 774549181 774549247
    0x403020a080d15090603030503060d03110105011517040803060d061b080906160f03020a1b060f0e0304080a0f020d0b07020a06050f06220618060303080106080903 71
    0x2071940e078041d902c030006441c203940d903c03245041c14000c40f00031a005044a800d040c0072003403454400a00314017000e08818410310004600700100b600588140b214056200000d102a42e0340b102c0c00e034892500704d000b034404240341c1c2164000c0300c0c807481130003445994818440e500b5501c42c1400d0151008850b44100e907226500d124180005079100e8040721020030954030000389280c4101e046080c0040548080703a42e61034180300c0c000541d08100b44000204003407500503201c040d002e004032030000c03000f4525001a00c1c195071940078444560444000c0180c01d1409200c081c40d0189410380d40e00c50741c460365189070042154040020b1286400445080c0001e240180d8046c50341c4451900150945900003d68050020b080800405014040c3e002d02401c10003000380c40c0c0b50012a203081921203d0303d0300d0442104150b00c0301c030229803000000d0b05c41c03c01c41807058400c03109001c006000300e02003034020645030000012064420701c0e0943c401c1c0b0042000e1070030f140d211610703e048a08142d1186500c5450300e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 774551681 1250 774550431 774550433
    0x1122003060f1801060f0c0b040f210206010501110a241b0e0418081914071a150607080d09080d02031506130b0903031e0307030c1701030b0403020a 65
    0x30701d030000e07200340314101503e1503501d0020041c1c05649404800001d2001289005010a07060303119a030748590050900b403107010f0ba91030090203500300341300702d5440618a034a002c07041a43c0042e0480c10307260280c8030b01c01c10381e244c1d0040c1a503501d00300000070031240d0000b402a0915000b41d081ca2200c000e003400215104040c2c1e20b0b20302c440702203142d20b50001000c85d108402d1a01d02401800342d0616800e01340d8480d281d0a03141d079542840384d0110503941088601440a06d03d11070007500c5c160803040a0865201c81481c5004502c0e03039546803900c46003881807400f090010a078000d82405074034004164078900542d681e40d111260708081c56803400745680d00c001c0408550b80c00d00514060712a050010395a2401400c0403810300c101c0e00206008100c2030115007450180c10001d03000303641341c010300c41c0d461f00d0402002030b180d80300c0d05412142d0800001d4503141503911700c001550042c1e89544090242c0c0c0a2601c04803118649030242d0199020040d0041011a1159180c2500a8000e01c1175408c02e40c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 774552931 1250 774551681 774551689
    0x30902031905030d05061e0405060d051e0f01050f011e0b0a0309050618191719020f01051302010e0414040506060117091c0c050703030302040501122003060f 69
    0x1d071280c00d5400390800510451141c020b485404d51041b400c0390711500903036082c0b20740d108000c02500c0090086950b1b40200b5070a079500903940c911190310000301e5111604410480e044182064680900c1d44154140401030b18418010b55214401800082e0220b82c039280d0440c40c050340850000041c052100f4001c514504600010101c00005403008542011146409407900b0f41c000c051504003025000c946980b00404250400f680e0301040f41c100540c0350500301503296481c02e03002c900b820364001a41f2074035002224000c00c0301181c190280c80217050900b00c028281e540441d405c0351b00321542000c400041d03016006c038100c0b0080280001400c030302151104150720f03000f5038068803182e2044080020359a40040e14003040f01d4070200f41c105500b014218207540e10308903417100d85e5001803c43c8a02c016440f0314054100325410908840b141d90745ca05025000754424010580059240146108040528000c800d0800047c0c440004a605151040c0c0480c0d0030190045904c00503220300e0510b070380e903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 774554181 1250 774552931 774552973
    0x409111207210e03031602013e0c010e0606031501030b1b0d09020a05150f1b12090114040302130e01060503070801020909130b0a090312060e0405060705180103090203 73
    0x203031a1006581c0ca0400706d20a11a121000408008681c10601e1a42105141d0384075044100c030018003080d0130301c4408a510311401c0b10284504241c100124419001c4074054000961880214099070320a0701c403403051544034452407488a0560104c000100009403103804803590008024219459084411407414110f90289081000842d00c0782041001c2d8508407100000a000031a007003050036031502c10352501d42c024080d101c845890003050a0b1459140d20801d00d2502ca206000c0d031310403500580707a041468015443d2940041d05518030700084055490032601941d0700102008459441c03609000041d1880420798520b5540f0b48000180e80d0300c0410010004d0009a000540c4441c100c1c810b00098110041c80c261a00034208031440105601585a40d000b00c400880441d45107280d08068039440502c04428110313a2510000003100349155483c240140d00c104181c43d00b58841010449490081d00b00c4030260250780c6050360344560107517204c0d031020740c400b8081d6031555403034001d0182205 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 774555431 1250 774554181 774554201
    0x403051917010e1003030c0203160b030a06150e19050909010c0e09070905011211040e070813020102100e12030f011814040b0402041407020102040911120721 69
    0x1100025a40100e10075541054058061140c0d600024608410301d21400812480054184244804030310309544042c0300c09600708030b9031440d040f400e80d0342d800c584580b580200e6030000300a240c88004140380415595200c110780b99030b6602c001d8501d4280802219030040c2c002c3e00d406140b05000042d068480f4000b65108820785c20001400b00904040030b031070200402d500074850b108200402800941220521058683c00e203003403403011035103c030700700300406103031451040e074a4001c0380c00140680c120568511900c1c0d0380d680c42e6130b1502d51603d03241d09040013080090140c3c22000c0b458101c9045075112200207138601b022684008401c81c1594505e134001d80e0392106c202c40d090014000d556102004411100e048d0740308018030401e104140000030f0340a07200402c1d100c001c0003c1420340d4be07541c2110250000490124465051204029000f540b00e4030039a0741250521060064900515058600c1c0314100c1c456100c940e40c0e034100840c9c48030a406260100c8040c1c40e001000300824a100c0e41044e2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 774556681 1250 774555431 774555437
    0x306010902091207080102190c0206030a05040c08100c090602030702180c1c060f0602070b0301030b270a03030506120c09040503070c0e010e0604060b0d0507030b040e031803070e04030804030519 85
    0x48c92104202101126099032000c00d020905840c00010384500080b2640407507640800142a1076920b80001848966844103046110b448880041c009940e03210305828841505d070034841c81c1e0740f030000b6078903070068240c003035032110100e11a103c2c886805140c0a40c070540b5104018904000010481031100110709000c03442036030b802003800341e0440501035001800d81d0780010000c4a14005098039103100c1400010041650600402d0385c02004041600f0b2030310440705141881c175600c042042d500c94111000383d00180c01c0a01040ca2814a400c020700c4025414018000090b8400244030381ca14015100301c8184c4800c01008000c590483d0a080107441786030b290b10410b500d000400401c184002d801a88102c0c40c2c64010040c4001c040101c0398030140007000411580d40c1c1d21800c2e070084c900081002e81090504401d050b40042c0070004142c40c4402a001000300c06603c0181070b990398450282d59140e8602c3d202003004203002c0d84c545a4030901c03d2070b20f0f034a441406094441101038549240c004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 774557931 1250 774556681 774556687
    0x50906150c010623040605030604080a020a021f0201050a020f0f1602040e0d030605150910110303010f08010e0a02030606150d06140103180506070c03090806090d1b020306010902091207080102 84
    0x34652458401301c0f420002101d0034001c6504100c000b039155403002d00003c086040c00541c148501d03000b44888824541c00901410314400706100b103e90082185092000551815000078a5024148280c03415020002a500d090000940c012002e07030b440004000d640407403580180c00142e03102d006041041500c00042c2110700e00b00380b0003a0945406070089445846000350766040b10b80c1500503034103540b6044440d142c501c0101007090790b08401b0f140030992940400400030804205030f02c40d0a0407100f640e002040200c2ca0b41039407548070b41c4c43d100c00039031580005d800324516141005150302e03c2448002810310382030021070001c08403241640240310343c4082d0f04070381003190382601c00d04140b10403142440041003103a9442c0c94843c4401000c402c2802800b18692003070501c182c10382e01c0501240c004882c4c0c40c1c2000c079941680c031f10501d60840000398502c0c4450f241c0d191044401c11009501078028055039007030544041c040e402111845401410008030000d2640c010440344c801802480d0005075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 774559181 1250 774557931 774557969
    0x61b010c050c0f0a11041a040c08060f0303030421050c0a0f0c59182a0f130614040204080a080904061d01060810050906150c0106 57
    0x3040501500300e1900540041382d0001c042214506150024141103c0c000b5024981d04551801c89034440a01e40e086464050000300d4a034000c4a00c6000c2d030400c452001c1003107034041c101903513407204440003000031840f10880c801554284903d4264140c040c104a0300740404d401d2380724500450380800b910040f4030420b08405101c051351544d8082d048141d9440d84204072054080c082d42c0881035214200e4103070040341d0020214a5100226031100612a080c003030038580500c455a0740f058809039000540104850845500010b0443e04501500c2020200c45400e82e24807801d03131001e5001980094400c4121030352607580c00b00010301c0715180c050006020341461038440e0050646100a406a40f04004c10b000c003e00c0090b508079034030341c0454580d54424610020502034440d40e8458407110310320860340da07050003c907040c050586d0100e60b200d40c8655101c050350181e4012521480341c20500d00d00c042011810b020408030400d0300c1281886141080c280102c508445207644042c0c41c00104003a002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 774560431 1250 774559181 774559183
    0xf0910030c12050a0311010f2a050a0c0b040203030d0207120306080111071b05030a08040e091c0509030a0b09010b1e01080c0d0f02070602191d061b010c050c 69
    0x28103201448111402c100d03560350759580120803c084c05005006000349102d2009410410060320420720a02c001e000700350000c84800c2d15000804101074009000b001da80b4800c50a456058bc0c01d40d5070211070b002580c482425180003c0c00c1a078040c00100100c180c655524001412400d20549440f00c00e00e40707480d001030855400c0e410003103050b41403005102003445242c05541c035450b0000c8505000018508003680030300d0103a07001c0c680500600300110140075401021744103c4a041c51185110382d0741c64030071600d075a00040e403162022481410045520f1040d80a401100006011101300981b10b031900302400034101c50010030380e034641480e0849070800c2103141103240e00c03841e10007200684c1c6c04006800310200801e0000c408201095100780b60701c594021900b808032900c002c40d40c1d800d59007458006507000c642c2c880c6140842503844d8076003511440441d1800b83e00310310744011941055040040c5c0703601034100110500c00f58900412800401c1c803403112080c4094581c9940c51041107801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 774561681 1250 774560431 774560453
    0xc0a15090321020f070b221208030f01170a060b03010b0a03061d061e040f06090803070912051c2c121b010309060e0114040b060406120209060f091003 66
    0x48061501700c0c1030208022581d25095801990601d40082d205d0010245210405d000580c0b00c48040034402d4054810701c101400103501901316031003258483c0c2c1e21000b001406107140b0310304000c1940190440c4012418540c07001848800050010850000500019528500c15082501c243e5a104e0001e81c0d0b044945032048a8016108041c0c060341c506101c42c41c002ea03214102900c0700f0001c0c440005c003005a00680e5620003a03125000b0040f88000741803260a980040314601e01103515a080421000d040904003210981d105000700b4070f207440d0a05100c1c040000d144040140003c5020500098071006480414058605a080f8020b951541040300d0100240b02900740c40d005008082500c0308144446400c01d0020308021803510001d10f0503800510058079582d05175481d10b100064014070000d1100d02841c0100f13007942094840720100001c460803172040d41c0e00945000903210050400e41115035200c400207140c403108100d41030200304003178022688a16104100e10080c020001d40001c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 774562931 1250 774561681 774561703
    0x3100e070e030c0d020f09180706050415031d0a03030e1605010f0806150a0302070302010b120a060504050f06070203030a1a0108010b07210e01030e0c0a1509032102 72
    0x1088080a402102103a142d11403140300f035001d404600070040940d260b1106c940607212020b805010f181c900030031400030101140c3c000501d2401102c0e0002030a9100f070007610150350002e1711410b6074125038001a401444031701229414440c0c000300b00c0c56241010f0114000c254082d0b00e01140060196079147e04000b60b40301d40c4892100070780400e00160b6841120000b43d80105d0400c40d030562298400103540420041d80078241c200d0000c0c0082d081e07581900907102c90361190f0002e00013200514200010400940d034008110f500c0114010b0104a098110300d420602400a8800e10203030080c86030b040c04012100c660240e403000040c40005845031003280701140c0300c0b0422050b100c48a9000800c07841c03040c07144200c11000407607082e040c88003072000200d10519654007041c0441811202030419150b40e0780c00d5004c00d1510705074540300332000c10740302c50540e4000c00c481140d44c14044001c2290029440315010403002039030110002e0602800700c250300799884c003448846244018001c0c50f00315400e031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 774564181 1250 774562931 774562937
    0x50402030411090705070203030301120b06090c0f0a030603050303070503190b0d0f0230010c020106052107031509170a02060c0d150e1b0309120a030b0603100e07 71
    0x4204008030302e4002449880200c21580001c094564200450b045d000303881c000381d0f150000000001e40240c0740d06039581503901ca9600c04d002942c0da04100140588203c80b0013440500800050380c11064420051103503074080e04000443d1134980c3c40d46884c54000303c0710b80c00421000400d009a007070511440300307410b2844600034450030080d140860000004080010b0601503242b071200219514034000420a1110640c603800034000c2d8220080079021803014800300d9403a0491b400c42c0342c0d2042c001c190580714054000003088030413209081c40f01e207100003907a409001e0600040009901603038007502092807460082032381505420f10007040f14064184c4554141e0801c003040300c0390f07000301e001684411140003554544604000400140ca0002a00079060f9032100021980b440c0e000720b440c0c014078941c00350900d61024140b82e41200d102c1502c04807000c0c0d11500c0200c00e450b55600041217a03014034500401d00b41508000300c1c8039034000b0760b48010b007200481d005200303508400b240b40c2c0c0d11854520b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 774565431 1250 774564181 774564187
    0xe0612030c0706030209011b0b04020111190803060a030c0608041a0108101d071e2c09010f0e0c01020c06040501050720030307030c050d0e09191b0e010306050402 71
    0x200c11640d40c8502d44500400e241c1c01286000d5141c1c0112803400d1580b91806408039040300318500005504c0040314103e0100c0d800d0807030807031130140004406884242d0b8200107543c9500940ba400065003000748080e60080d4a58404000900310480c440000c3c100f60701ca030082814107141c0510080001c22408400104032001007240394800245501e0324062101c000a442003440b810505940303803c110305d0640c5c0b24003103001890b2100d50906001541c0131019214511351500340d2581240c00e4038004010b0154900c159001c0a802500d013203800c8145403000080700d55001d010713401500c04030218079183e908504443c3c50b11b9601403001d801a1401260190318190820300040c000f8001c1c85005441000c0d003c0c0803544810064400807011100241265180c0015141c0142000e1040744100c41c123008490b81014283e01454640281070401004203801d0303030b214031306540382d01442d20401e14520745854882d00e00700c000c1c20050b9481801c60b0368503070740f00780b2000014003940e12950245000d14410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 774566681 1250 774565431 774565447
    0x1107051608071d010b03130b010605070312050606041502100504500102070b0f010519051c020102190501150b180d0c210b0c0a080711030f040e061203 66
    0x654403d81917039180368001da00ca880b03592054a4100c0103140c000e1003c82080000f10b0071f550498080c0028600c2640c49100b960a415005025640e054860304c2d00a6401e0000f48070707003010401001c422a0203441150318a6182a18950a0728015101503624080f000724501100000c1c0c141742e004015242c000031440c071100103018a01d00000146850f00c00c840403000550035000790119141d003a0041e005590500740320301d840400c54001c0c4150340c414a01e0b048070640001a00b400700c2c0032664001c1c0318100d06500d00f03500c02c4108800306400ca0440c00f0312080791440703814010348040d0440c0944000a20a403a104a900306500b039a00031302c1610906004a111380c601c04148089808401e480d217250040640c41c0042c0196181d03000401400d401422000410b450f030f00313850001502410148202c3d1b280c44400342c016208400d00000060a2003000642982c014071540420010344821a460501d00c198031034090740041d04010014070200701400340910f45104035115400e0140050b610704200d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 774567931 1250 774566681 774566729
    0x813030c174e180307080a0f0827090a0905060a020c16080a0c06031103160908030a0816020c1011030f0408010e060a0e10110705160807 60
    0x20b4904a00e10144201001e2581e025000b06940c0420340440c1210810740003802042e800c64111006a50901d050010040c00910b030020b6000203c503030070005801848000d0b00c941c50164000001521080c1e02001221200d0308524078156000e05508140e0482da03081d4810002d2090014209000d0b00741402c1c1843c02181d000705400c2d03009029a20016900c299600f0340c5420120700f000700c902170500b44a0006050301006c1800d101326032160811051240e1100419030844e42c00d400254650801440060708100131070211044500042c10451095507580818515550096101c04002000c68003400080c0d2a141407403100b60b81240082d0821800003004150039a440c1100e440802840001d101a00c1a080c1f003100c0b2210111b401590b5203d48031001d0f24080e14521101c40c500e449001c001030242092440b074800080201c0024103030480203191050091b040c604441026050104030440c0020b0f800c212031000c42e4659100c400038917240c48103450800840e648680c6883d5501c000c40c80103290 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 774569181 1250 774567931 774567973
    0x9130213230a15060f02120f031911160b09070b0a08041e06091a0c04120309090204140109090b030721140f0c15030a05040813030c17 59
    0x403076003480498507034500b00c0340d0000c1c3c012141003001e841a40c41c0d01055607a48030100340c045130b44540032941600c1030445210b425100c3c0b01c0b080b0710005400d0000c1103440308500b41600c1c556545c00408500d281c030042411001d58000c00307075101d1151300c040f12401003014414106a03c982c00030054480035241c84030480d01403184610040070480f851001404100314220784045003010b07a403480a1140c4a8500742c001030903400e1066070031410700d40c11358800c00380742a1000c0c400c5440400c201c0c240b601e40b40305040c560603942d00c12010310028131302c0407418034001d2002e00300500c183c45148080209410000d880748403241c001465050070326120841c261030025619085440d5418152a00341050f5040740036691f5980c0c004045050300000c1c010b05400c0010725101e06a0035106450f0803d10141c101308803040801506031000d8802c0c4005540b0300c45a600c0f00d9406402080350b2403400600f01c00f0f964110410790021035000d00c0d02201404000c0041c00c419004024040080030074041176090254225 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 774570431 1250 774569181 774569231
    0x150b040b040303081314011401050405070f03021c110a031104061409061605060a0b0a030b0a020901020a080706052d0a09020102030c01022a0307080a05130509130213 73
    0xb080b0700b40401c1c080d020b17442c0ca070f4030690341200f0740312110811010000e018011140300000780001c10800403c203858603118460141d4026102d042c5500e50404003540a07401003114603940100f0980d0001100750640140b28080782e0b10300200344c1c0c840303d605c030107401c540301c15013150b2980c0e0b8180024400b40d0b40004210b100682da00c000300f51110f070600300044541c0700309000754404800c44030510040100000300580111100c100c10710160001d2404c2c01501d0703410f44400307401c40300c4100118034101d0755079000301000d042c188161585039100b500c90b8a102d50101c0c10850340d2550b41c03002c00c4030020704074403440000e12180604000c4a030080700820808140603246c4030800713503504904402c40e0300820807a4042e207007100c003d42d240c950010003003a141002c07500946030010554141807003001c012080b101c4190f031095402e400d004641104440940080c08140c030010442c5c60b011807295103c8602031b00c68480e0752082d07411140785105011500c000c980707200c0c100385e0525004d0001d4101c5401d5940580c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 774571681 1250 774570431 774570437
    0xa02030d0203091e1f03050a0f050601050909100b04030506071106070e13090b150906090408070311070305011d010c0f050d09020a0e07030e060c070c0b070501090501050a150b040b040303 82
    0x81e000744000200f0022170849640244e4031610170030b802180d0150030080c800d41000c0401c002c0b030f007001301e040300070383c0c10031142c081c0001d2003004003440c10318103002c0303083d04a14603403401070303200f51200801015644250800d89150384048108440507512042a0080b42a203034054078040c1000c01d400b41400b42d6198507035105111700c0d03107400b1054030542c1c4100d030701503003001c001c080d5820100b10041c0841d12200300240640c800e0350019080e070a0110300e090080d9440f80e003032481c2c402e070307510704446502c070110003400c0341d0003400000404114240030300f1000c00f0101184248102041c4509400c6445034001d51080c011a030b00658042074114040e0355111030184800f0448540c144002244502c2541000c1c0581c12540d050040455066005160385103401c4201e86003900c91489070b041d1070040000040075400c2c06002401210001030103003050074419400450b81a0f03150343c6590940704200c0700c4030b00700d5913900402d020351410005020014002044002d00c0d240c00e090b150007852141d80409014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 774572931 1250 774571681 774571729
    0x20706081905180c060708040e0603030d0504030f0e030a02010804080c071211180f060402160204180c1208040e07050f07030302040608010b0306010c03121d0a02030d020309 76
    0x414034103031002407041c0000300290b252003901c40080d0070800d4128185841110081e0391941420b10071600d4098120b2035050410749484000303078034204002d00c0c554043c0010f0001441d81c0701140500c9000e58032a4440300c1d4409aa1540201031114042040784241d000c60302031005030b43c2113022180c11176008002c1036641d00c1055551445e00103103500c10002020180300880a003ca040200d518084003192550b40c58503185002070b15120b020782d400990070408001141031032506500500070440707070340c2e40c00f4402c0503507400141c1203414100c2141110a00040f02e0b40030400c0400144020300304004800306482423903104d95040d0300860040003865107881d808228642d020304140c482c4c041d03030800c0196440980d4075000b80030350085e02ca0324001c500c039540040b030b0400c3c00c441501c0c41208107a4405034995602c0e1002c65138031780d410080c00820fa5480740719840c00181d40005d20070703001c2e15038000c2c414150984117141c41e160001d02d2120440d0018041c0c0e80c0d141e901c80188101d421490104440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 774574181 1250 774572931 774572941
    0x80d0b09250c051c0504031202010b03030d0c020a0c151205070c1e020910090605010905010c0b1801060b0406200705132c011b0e010518030703210306030302070608 72
    0x302c1c040c180c030720100013101c4d11001415000d034008003c2054910440e42c01380382d510104d600344c1c245c0301e40b05051070f815001448200d8581883c0d51055402d640d00b441240d1426490351590130002120790016100003c0407140f42200302d8010300c0034001101d80d810104014541040024640307036908500408039034400550811558400c100c5c14401d036002004420b45052032618141028824410454080d082007000038180d030064511008990781030b103517881001d6855907003408409009024528190070701005089101c001d102d004041d061500001d0354490170107030f000d0080e03003241503031010400030104c0256650074045840d508940c4160b541d10b03402c044004596011f00400d51840030190030010002c80c10300c900075201c510800340342e0002c01c60b204000d07070b0016401c04000140c6020a141c88200600f07944144000c10030145a03a20100382c00703002000003405d00045900a0ba44040510444c90000182c00c03843da0a1380c070203003802c014903072566401a460b0301e0300c1d22032041800500c0c40010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 774575431 1250 774574181 774574183
    0x5030c0a0e090a0516050c03070b13050a03180e06062b0e0a12031a100e060301030605040c0509130303150e1009060602120d090f080d0b09250c05 64
    0x1c001e00700000c0c26041103140c510b44080041804a40d100410303484484154140b501400403900000000006907281c858551140d40e00c01c0c001901e004843c0484c031a505e00410010310404142c0d902ca6610200600c0c1d0101c5860701d011030941041c00380c2045c44050200700d0380c80c2c5007182c440d070756501120740a809200300558008000c0120754100c3e541018685901d030500491410185441040600440360010303004034115440b540b10042b015110b202d41d0380b01850400540509041c2c107203800c455540c082004901c01d90000c4e8000c076074283d01c2e03100380810030040c6c102ca84081e100076035890300b49240c442991310403d83d0108003d0300380744e9103080294000c0158004040540b0102980e40d005003420341003403016012900c00c4000440c1f03050030109000b1710100340d0f010307a6010f101d051820314850001000003406800707811219030340800381400002d01c0c000080d100c100d41d03074400014440181401e12951400041140110380040b11841103402444c4600b007044000600d400d0200c07244500e065 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 774576681 1250 774575431 774575447
    0x1120b030c0a080c090a11030609061311030621031210120f06050a061d091005010f1706060108134206080c121204060e040c09030305030c0a 62
    0x2e42003980040e020402c00c0e0b00141c41d1480c0e20055a01d21942d540d06601042220710303c00c3d01140c1c1c004208041040ca20305005042e41081d00100b20413816500c82e1200011602c4a00d80da80c0d0fa5100401000340314036000a02c0b000011801400b80d510400483c0d007540c803445040103000100b050070010403c1c00401080080c0502141c0c414018100c100341030071440c40c004050215101801c010004407030200b180103450840c2c42d0003500700700c0d401c09441c0c008180100180286150300c14038201c4c0d200e40e0464003450703000b00b10701b64910200504088070803074041c68441c0d12702c0d02648a00e0500c1450b0b60f10090702ca5001c000042c2d440a00d00726450090b03d00d0700d450110100250510015005004c030003441d95508880c18103503808520700e9500751a00351000e5100e01c1109412a184030091410005e01809030006074038141c50780c80f4203052442c0d0007a001504200c0002d0041140c213801f0f418248141d141d8640c490402800941c65664010024800140b54807070101001c520048118014580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 774577931 1250 774576681 774576703
    0x4030c031704080115053307020103021204060914010c09060518030d20010e120901020f1204062a020618040204030b0f10080c0d0f080c0f060105060901120b03 70
    0x2c5c031400c83d03400040c01da506030324041e080c81561008400f08803081c003000464000c96110002c0c24840500068190458000043c168189502006010b441c00800c215017445030740314110014003d8402d04011040400f0f0752045a5503030f25050042000c00d0b000a00c8004032080c91401e00d554070310010111840c0c0394218070060b014454411028070440d00300c2d0722103080b1107040c0e40307410710311000385041c909890315007040d00340c0e94200c2c481600d500380384070006004410040c01290000c00000d0100c40c6001c506c60a816540030001c901131002982c00a9685c01308031240d015507000c00e0402c0440c06140302e4411b0000e1181c000098180151080107540b01916803006000315121696400e0007600c1420454184107616280c03400106007408a6030060300b929000c800038640f82002e1410f103c030740c110600043c0c4640408840c048001020f100003014282c00038006090700200740c1d50f00d203107800410f030007451081100b80308841c00750f68840c50040501040c8400841c8946142c40480d05100d000341c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 774579181 1250 774577931 774577933
    0x3170708030f010519060e3a05100603020f0d0c08150a0c0507030923040504050d0f0f0e090a0e06240a0b0d0c030e0d0f02070b04030c03170408 63
    0xb007007a0400800d14141c1204d0007540e00307020801e00c0620301315880c0690301480700070508500c5922070900300410903020000030480d030f211280504000c020000003000005544e6003d016144008108041c05040e090140008003070011505540c005a08000540046400340c1e0540a5010034001e40c203030000001c000f00300c00d07030344100100f40030304480c010704481c1145043c5c2450b010306801c51055088469250b010303601d42030a0303401d10075040041c0703842e501c0c46a014400c164001d0001c0d40c0c0c40c840d42d80518440d40040c82884100c1c800036200c03004000c20b13501400480c0340d0701c0c001e00341c0041c542d8070020340450f81d18685075503118107000148007200d51094248115002c21240e04502c1031501c080055840012006c8540c410410000000500a0050088090120300c41d24001c5401030348114007242008507504041070f21079072510f1071814061002441c0510310a801c907406006038006010a90042d40ca090304588880e0301403052072200070441409403c1900352290b80700255009096400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 774580431 1250 774579181 774579187
    0x20a0c02010e06250609021f081602030d2a0203030708090610030201112e1a030c09060d05030310180b03100f020702090405030403050c0d0302060103170708 69
    0x140144925191102240400c800718107014003440c0072000d503004014071118000c02c46004440d529440c0e80b041008a46258540402d00010780e038045c43c142c010080c24400d41100c0d440d112006005074805400c180d070034844041e400b42d4043c0c1c007004a45074814003000100f0a50201c000c815220241d80b000c54002051105d95101e1040d0b0100007103024030b1840d40c81d01c00644a8410480e211074044d20308005e00401703454100010350140c4020448a02180706443d007a6820f20703281c9900e10035075802e0341c4001c6d0200c0f0030401d6504035441200c080c0040740019014035003d00c808070f0f43d2051544030b4148212200e400183c880d03070b00e20f800c4811055000f81640d0f02ca050000b10042d4040d8140900c002c6200c2c0d401c0064442c40365407082c481c000348001c00404445903401560390040c000045500b25441e02003090001603102c1e8210640594801c40086030f07168036604295040c032003200e025074407070407501140303d0101e0360000e032040c1920380100b06424001d401e42200b29940c4280f52000300f94039004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 774581681 1250 774580431 774580447
    0x200601090e010c090f120c0902130501090f032f030d0302070c060807080412050408030403030e09070f050d0c0e0d081b030a02070b0309070518041209030c140d0602 72
    0x2a4100ca81000000d074002e000d2040c45840c1a200c042890042405400640768100141180b161900000c9400345402840700d6032103002a07001d076800001403c0f2607800340407007081556031050249004203016190364002c2410766656902c40a42c4884100d509001c4103808100108410b03007803010194001e04542200c020141d020300a500009001d80b100c804203600000c103a405103800c28815015503480400660f220780c0c40500107151a8804000c0000030310000c15140700c02c100500285019449040c08101803000300102e405006021000b00070b05122066405038008058030a03030500c40c1c1020811070709458003180c00100c0c50200351340c4441552900c50500c80e0345030081c0b00b11400788414109207610401c071180d0328440c0b20507150042c2d1040750304100c0803000030081d5070064501c0007511010303030751800054071001e202101e040b40c95208030140010410303003002c2541c0b071540c0390030300854461664440c090700302c03294443c994002502040445190380d41c06a544c14a81d4803400841d141c10348 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 774582931 1250 774581681 774581699
    0x10f020301080a06150b030604051e010b0c0609150112030c240b01020d0e1306031202060108070e0915040f06060314010614060304060b0d060e3406200601 68
    0x4400f4080d10b07010316043c0040d0210030040c103660192542d0381107003481c6440c4c0c081804020f000040c2400c410340b46200381c05511080013141e040c001e181610b50705450f002280350840c100000644038180c02e5010104809504509041c0c640c1180c0340f180c0240041d2603d42001d8480400000f402044420305441002c0a1042c4411482c1280781000c001c00001040030010390344d801c0013a955801150300c0194001c07251030005824150000c50203c00b1541503526501c0e1300c070000b03142103c02c002da0011700040c0112082000044000c000d201c1500b11107080544410392100c134003451809092102e20000703010703c01000078802c3c03010f40c80b107420013030307280d480c184281c10380389401503d03072a9424040d00103080d1851304484095104003c100f1481c50700c45681d402c0050211034001e83e08207820a0f41e80002c601c8ae481128a0425040043c03c041446440503151400f9606030190251001340c0c17142103050028813450040d00c8450a10200c40c0d840c0c0b9500c59a0302030901d514801c01c0c41440000710b4080c030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 774584181 1250 774582931 774582943
    0x3100606091d04030806040506061605060601080915370f0b03151602070512010506031c02102a090302030c0a030f082802011a220e010f02030108 64
    0x540802c010800840c900c0c06203420346010740d800780c001100ca0f408101b040c90250300c0a0f4019000070140b52400344204410411140d00c00c2050369140c00a408203d16135810040712644081d03410017401700c10080030300440c0102000b62405110040d01292074400004005030103c0151103800302d271651900c8183e00001506020024070030003820070500302d0440c00c00060b98003d0001d02124105d1030382d1280c05041c1944106204081103224007103000030240c07114040c1001c00400130b400852503207460020700d4680a80c0c500c00880400103500c4c18600e81e580418044c03038480008a0105140035105110040c4602c01442c0082404000d0f44503841250040c00c000d048034801d40503034034011404030411120008134400601440c0b004014000003611500090985905a0044800507400e01d070700c000a42c014901d414000d0f0f90344100c004100004d40e1f054034030071f103011612210a040c803624052440e8a00c14032410025071940f42c00001c0703c1003074026150700715840d1000c545071340e910020195586 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 774585431 1250 774584181 774584189
    0xa08011b0302031e15120613060f0212070816020a030e0409030c050f03070b010b07020a0b0f07060f020a0e150414030c0d050c0a060f0c1203020d15051309051b0310060609 75
    0x107035140b03480d04110404624140319180814034445230104944518024186d01101c040100c1d40c200911201407042d030400a0003030400782d0741c0d1603207454110a0314403c07882d00032080083d580b04130000f50009602404040c009a000d41d808501c1d04a24a4186c80c1946102002400fa01600340a04600d41000003e026441e00400701c1d110f080c1d0303883e0501c480e0ba20902c1001394000d00b46000c00d01c1070a0f0400300412006600d01d090910341025a10303400c0c1100c1041d03242c0b200f030310340010300c0740300070b9038044045c080301c1c03074100e0701d08811403107114a4903914440c1c1e120f103140c45500c04c0c0500003240d030203000c040e02e040c001501c4070072291060703d0002e071190f104550a91046002d90004594a4400e80c0c100720164100c0d03e90301c40041242c2c40301014a500910310700201a001c206c02141d500103800345055400e00788130f000f82020701301001c000d2040001ca0400901924110218010074000500b0f400b45443e00b258494a000880001c00c1c10481709a0801c00b210303040060000769141d0003944c1004807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 774586681 1250 774585431 774585439
    0x60311011b0b0705210609010b13080a030e1513030209060a0306020f0a080c0a021506120a120801051c0f1131050f0a050a1803050301050a08011b0302031e15 69
    0x41c00c040c1100178900e202500e038035400104580040c00442c240000600600e00405500704a407076a44000320b10b0316804090032400100120b5544039141004030030215800140591a82001640c0c01c404003103030850310019100e0070094001c070b00e07240c0300d0810b00000307160401803e555480b615403201c409648800c40560015200344001100b4401c001c082c0ea00c01c03070240d4081c000c29450303041e80380c0003a800a090356500c0a8101d1b0500d000711801c00451904a00c02d00c015000341c1c000b00340c0075010f504140e0119009580129010030a640050000380b841d036803040d80700f00340c610745080401000100c2000240c000c64452242a0b071900040b00345001c02c440040c07a12084841540300100b0747e101918580007006449001c0b5503450700d950407040d03000d4114400012504c420750110300101480140641c0410030000c01804503040500542c0060410100284001c621a140c0800381c01d1080a60380100b55000c000315042c10000b007080d4408101801c03c080d0a0b0911005800700d41c1c1502ca0800d1113 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 774587931 1250 774586681 774586717
    0xf150c1e0206071202030703180506100501020c0d0314090a0f090515060a030c0c17040f05060408031e04090906021207020705031b15030721060311011b0b0705 70
    0x1140d1000410b540b0410311a641e83c8100c80200102c0d0000c2d40006d40702c2c4040c541c80d000103008000c0c40882c01306595020300d00600b4a4103109074010442800f50304060b0454200d1440385207151584034003180fa49505140c4903044070095200c40e161402107022141e441541c01500242c40302d6416441c400351410181c00300410340310840706021260040c84500e8020034203000181c0c41e90300030703440172112441c5401e10034841403696480101c2c81200401005411401080c144541102d501d0f80e08051305050b54160301d8103085c19000c96403802120760000444042408409400c41420141c40c014000741d501800300910a19103080030f5081948042c9200ea08a070004004500c001164011100040c0140040841003045022042c0040c1c51081c1c014514007200207244e54101700840c4952080e5a420b10850150005003000d04620704210b61640c1c18040b00340042185401d041d54246000d00700701c0d03040190307008110300d040000c01d000b402d2500440c0801114641010042400111244400314 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 774589181 1250 774587931 774587987
    0xc0b0a180e0f190207150606030c02030304020d08090d0c0b0d180c140d0b0a091101140301060e040b03030d0b1906021024080705040c0e09040f150c 65
    0x94200c0100c80c00d800c070386210000b143c0d00502210524480c80d0701560054640681c6031540e020640389460302c8100c2a0359144200085a494415020f00064501c05989142859000605061000c1d14007400103a400144005503540350305081c404103601180548402d41d80e08101c0105800c0f03208143d441c0d0f802c11041c03251702c6030700035595244a80e05c15190306d0b54500b0081c1003c901e5650b0320034290481290418500440c80ea4803100380716184400c4080b40100103840c241a44451410b682c50510050450b8406801c2c0440c003581d054414a1030540780c003540f8200041c010b010411580e80e018040029003c421009642140740c1c1c050058801c146801c0403c01088002c80151040c000140c204507a00d0000c61a99048071061883c05a4241c0d9402c10b03118051203215450341c450704040e841003004112a09150040b60055107490410b022620149000b251007080000d000034130b0080d4030312202c0b0070001e0f1540c0305070701008428010421a40310000c00b4061851070048001009080300c1c402c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 774590431 1250 774589181 774589199
    0x515060409023309030a030e03010f1d1011040e090a080c0f070f0807050915061c0e01021801080403020109050d0e030c060a090b18030d03020d0b0a060f05070c0b0a18 73
    0x1d00d81e903c000d40100a407035100c0c1c804a1f54400c001d2340140d0706540301c130b0240c1000500d50140d040400001c480ca403042c225000740f41d51034880c07416072058509041072080604414424103682c101c9401015201300c59599100240c20520305510040005801152854440000056a032006180b205c2282d8000341c4076600f000041c0200e2007001c2d40d0354030140013403041d400d041e1041604100e01141d052624486880000c580e0380041802c40ca004c030041ba55a80542c2041c01202031301e00d00d51000314500405040300d00d031802440c280d041d0511628001143c1018400d500c40d1300c0780b42d0084203440c41100300c00320003841d80101600c014441d00c1075140c00d80c1ca9180c04422264202c0464503880c003d47e14000a28401d900070032408403000100c06216405518113000155100c0c2c1c0542d80140d03900c140b807189408460a1201c914000d1203400340600016802806407052503045080c01620f9144038600700186203210b0300507210200005c5401c18105412103510308010596155400c08662210501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 774591681 1250 774590431 774590437
    0x180b030313170c03030a031508150601090623070206120718170601061419021f0903090902090604050a0f0317030f220b0f0405120705150604090233 65
    0x2c04d505800400c402c01400d80640d000100f101042c0e4084440c107a9100d03000b40c1010221503c115040d80c40c807042122540e44404c040016241034144004401306c003440680032101e44d40d541950080d00060003d05540d0741905540c0c1400030742d09843c140f40b42801c0020503203140b00041800041c4049000300c6c079109200d03486c022000750400144070980c6406401c0701e0f00c80c120b200307003a0356441c2005000c80c000000b4000201407442038000309010710845080520030b2116280c3c00c15154a00010400001d031303c110a007044400302d00016840d6568240021068803d5500140d400100303800c0000b011034004001804490049000d00c680070040c140010072803001315208a5000c2078000062214040b500c02100320408160b414100d0709120364800ca40750200f542c3c843c00c14070082c41000200401000703d40d0210001071603881c142101a40c0d059500c540c92110078082c110300500144003900c459024141040e001415580000d1581086440b0a0014030004034040d07141e002c800c0710208002c0c01c0f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 774592931 1250 774591681 774591703
    0x6060902120a090c05060f0c0d03140610110a200906221b110f0d020c0114090916090914191401080718060609180b03031317 55
    0x100580d40c2c080b98030b00900002c1ca0441d1041c03c0c0c540c010a954580001501c807401c6482d00c403d0b5229850305a840c58070516070407020070541040026483d9582030050f07280c0010060310540c4181c8152403051700c01903c000101d4406100d030750208020b000300001c00c40040b802c2e55440300342c503803403034018007405400464100390801c440d150045908a69000f5620303002c0c0750030702c0c0020a02e0a800c600d900302c07070228500800081815099150a110078455240304008107001880c003041a4031000c5d4841d4003080040e030503c1040c2d02008203a070070340ba045981d0080000c10078544c5241860180c4c481042c00003c000c001101d070300012401404a10a4035030441143c24039005c82d90710304416002d4410042e910081046e100e00c194070400070b120b1420740c00382118002404119040500d12071145017840d8940d01c1c454203012040001a420103580015a00e9181c1001d81c0e140188980f1800780814070102a0580300000e00000c408020034500300c182c0d020a20f641c00054140348007a60f60b4005440c6c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 774594181 1250 774592931 774592957
    0x110321090f09060d080f120709050f03070e010915030c0e10120507050d020402130b0408150f070c03110601030c090f09050d0f110307150c050a050414010e060c0a06060902 75
    0x103040000304000780090308130380440003d0f451424414800034107c4a0f000d94042021501c240b5060200c0e103402c1601c04803020080d8010044245082c400d415600701c18030451000950b90315004d0100c01803c2403210246400c1404820741795500e0b03c4c03901c522102211040704a000428010900f1344c1100c51880b1010340050003483c5a0741400200001038011000c1207911550810114a0411090008030020803c81c0c4207144c0360303443e1442c56405d01700003a00940145034014104000440081301e915045a03062800302d00034180c51805581e00304540303600a00512400f000001000141980a02600c40700c40080c0013400395a0904800c1d00d02d510340061054000010208007a4420000080c2c0003e4614049005075500408a4155404041d0542d404500010003034940d120798050043c140d240351038064942029100c008055010390301402e143d400305901d240040303a00c60805980c0305000140320596441b0800001a59030040180440c5c1003400c1010004558129200b900d061090b120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 774595431 1250 774594181 774594199
    0x250f0b0304030e1807030b040506060c0601030b04080f161101030209030307030e1306090e010e0c0306010603021c0608030a03051f0b070f0807030f090819110321090f0906 75
    0x950203840c01c28481403c0707070300814600304c040c0c550202e03001c40a0150403207440014120402e0401c1c4405d94200424450065808200c441d417400c2d800035901c1d0440303400842e081003a0321180380050341c0f07100d8614010039620000c00e0740321140000000c1c20002a02c60f100f094014440320005509a001d901d004541c1500180400b0011a02810040001d010010598403121008004070400c803016500303c290100d558180074150310209100e06040b03000450700524031700002c8000a59600340500800d0201500421800c03081e000c00002040fa9100b020030600c4415244c400e4290350350030058401c80080e013800c0205251006600000e103954072110031000c007041c00c0030b54192081e401084104d8000c9084190007001c00c11400103410050702c00c2c0e644030301042c04074100602c01c602541002c1800d4014007601d2402890070409041001d038003500c0403182c5c2201c08002070805509440b0328400031f69032100c00605d00c40d01c00040c44501c0301180c2d4103090344141c0c000e021104c0d1088440d40e401004103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 774596681 1250 774595431 774595433
    0x6060e04020a032a03061202060322020a06111b1c081c02040e1621231b0304020a060309050316120e0910090b010908250f0b0304 57
    0x581c0040103108402c0c00c1c0450f4551944800c50408222030501c40b0040b1a0644101010741d81400340c4c0c0010210070019840061a50b000120070340b00180018100f00d00400110807201004078801c0411a0001d145c5100306a0b2000044c1900204452407240c5004451211240491049211421900241015500c80002c18405c2c0c60303015200c1007601d141d0424003000e034000d400c0d402c2404504a05000268a1324901500d030a51082c002d000226522100b4211a00255020b0460100a0789030300c2004150780b404036020000b48042220342d01c03450400d078440c2e8007088030b40c00400c2c09112252011180c0d40b1702c2044010f154041558003c1d4080840c48080107c0340c4a5044001b1850150341501c3c40c101844403021909444100c08544005d601c2d08000a83e039081315511000e084203a90550491070b01050a102c00d90140c042c00220903650329484505921450070007014196140c112005d452480340c85064030030420904086110300402c0c00314140d01c00c510404202e41004540500350703215 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 774597931 1250 774596681 774596689
    0x3021206040c050f130f02041403150a050c1213033c112410180f24030204180215030a09081207030c0e30010221010906060e 55
    0x450080c5640c05200c107042e0003c40d00261003071000e0360020311b4005960b54540301c481d40c0e0310000004e40510a03048805110100c00700200c0241d0b00c60b01a1600240c41c1c4d0f100c242c004e150f40034011289124008072000c00000c1ca10529002030554000d03298410640819074041003029400000c040440c01c5c1041c03900e00307070000b005d094102e106060030680100d0446888a501c2c103640942c1c0140e500842d00c0152180d07002c24440c2c2a04101c0851808a280b800d0400d541601d00f034490707210804640d90b001804401d03103d03034009820721404e000d09400c42c1c8410359003400c84642500050348540e10b440320403000c00c03081c103001c40919039000c3c0584180058000d01043c207900020903000c041a2903030b8249000031f05d444010000030719803024a40060510303c60040c111082441d881d424860303100e00e240300940c0c030040c80e040f85100b0250403e01119580500721540004000034841640c00401c0c80c0e0b49a000e03410207080050200c0710800340c1a07903202131850681300c451192502054007840e183c3d040c0d080c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 774599181 1250 774597931 774597949
    0x204181109220311250e010f1211010908030301090902150a0c02061308030a12050601080106050d0207020307091431060921110118150b0d050f060103021206040c05 72
    0x7040f001030b45e00329004618200300300d00395804003200c00d00a54801b403044211081c0124003408030890001501b60a260301079200240d540c8001e015032070b03c0c80c0700d404aa032286040c500540700f030409503038403540d44041c0030010f040c030b070a0101d218804100b10b51400b84011810340b81905030035955440355228135002d1045c10b0b030201c4081120258001800b20308450104001c10074403291f60764030410081d0070b29008040f680d0192102341040b0000b030040058039404000e071a1070640500006990701400e2000924001040d840060708a0522076421400510102e0b854442c03184851400c0d078541d5100700d50a0040200f04440803583c0c620908440030035100d610410310141f0425418441840354404032403c0e040244005002401c0c840690420000038060000c0680e141007020780448000c0c1d44500c8004401c0d0400a40107540c0d80c070111480d0f50b1340c10041080c58000095a030400d0481150940b294000d00050f4041d220049082200c0c601c0054010311641d0000f15a550041c01c020811400311 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 774600431 1250 774599181 774599207
    0xd240815040f0c08060c0306010e040e0c04050a291c15050703090f0f0c12030804081317030403060c0905030307022e0305100503070b1602041811092203 67
    0x440501d000c108041300300507040c0252081603401d5102d1131b00703d0004141c0fa10b000c1e2494015828190f860050b0b61001600c1d400b2040200c0b4082040c0d511841c003040101265902000b60f030915000d00810780c0221800b003080c0303003420345480903e00d01c2c5031800c3c8003040c5200801005c800e4485e103c1010000c2c40d510041c0c0200c440c1c035000c9110100c0380c035615000d427820001a46d16281801e29201000110b85141001700b14810840c0e9005c851500d014000c2c0313400800242010b480014902d024440d8007005a018003d200383c0301400640e1010350940ea900180021201140b4041c900d2038401d00400a2904a4a008006615101c1250309202c00b480130300003085e9505000544503031602499001d034104100c1c6a960014640c50151003006011103254081400b0b0f4100c41e42c20b00006541c13000700c8a03110120350008000500c5c510104000740380e86c0b42840e000d440c91010240c2009100c0703a45604480d0219a410050344540c40748180e80250417141e0482c041070461144006405100042303060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 774601681 1250 774600431 774600443
    0xa060612020706060b0a030b0a17100902030705030f0303040501050a050103152c0c0103180305070b0c0f0301091e0605010e010c020f0d0c08120406020c150d240815040f 74
    0x1071555180e240713070107401014941d4042a00c6480f8208c003070900880c6100140046c0100c4c107201c450260000d074645c025400701c409135070388071840001551030402808005000141c103c5034140c04442c0010303140e03001902e04880650a181c0450590481800340905903904800d8403000c00250f91140d400078118409050108200080030b8500d001d901144503880ca507078140a001c003d4100b20004040781c500103104803000c0191448800030940c0401074900c113580c020140c3c3d546849102042c4107501410703040e20200e040000001c107105c6c1181d00b01c0401901040798032462008100c080074203480b028001c86001070100e28040c02198455810450290b00251109045032000000305106840342c40b8140c4420300400402c1085440c200203038490000b45800301401d041c10715038001e480d4001c580c582480f031051041d40724003d00a0f14101c500a13586008204583e508140c1401098226003040c244040610400003801034008544007400801c44d0250710744690307030381c0e440e0780150f41c02131425114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 774602931 1250 774601681 774601691
    0x40804090c20010f0b01020106030f0602070201120915050c090102060403080c0720030c0105030c1218160e07110c09090111070317011502061303022a04050a060612020706 75
    0x500c1508a0014181d025802c0003c2845112800e01406961071703003e0b107504680c50300c002000417a0040300a551030a601910140e0784005600041b603114181e410500d60b56840d20300f0030701c02c00c008002d2244610b6844002400140d81e8000c2540b094041c10b050135002da00004001800680b103070722065070082d21101c0c0c00f41840c65940340e050701c0741c001d40008103681300b6420164a035840c08101001d1844e0092030304a01d10b14042c10010414060314111901e080043c80216420100000818403060041c2007115503525038840c01c00e1040d820741c8902005098100c002c1045030748031301d00b1003191104040c0204440e828503014454600c0005280340b0310341d542c4610810070390340090000c0c0b1039079000755a181ba8084450340d0010b100d04041c2e006102681c4000c7c0710a420a8010a0550b4045a40000d90804150758203059051601084040d000d00b25190309400000310003000f01601e00034103490801031076941c60322860444a082c003641d000308407011441101031b0f01640041600520580b00415 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 774604181 1250 774602931 774602957
    0x40b0a0e030a052206210f05090c0901060311042c1603060504020724090501111c050f040b0406060902030c03012909010c0c0503060a0207120206040804090c 69
    0x811a004102010000f40000032488104007030f440c03646401c04000d6000803152450803c0241441c10344ca20704401e0302e10020345600400c0d990794000301070700200c20f44c1417000d0b25114000790b03140c41a401416108401032400031484900c02e114845609508500c07181c600703805e0130034208940080030303070030728015407010a88110701e1090401a402441300c0d0300c150300e400341c0c04080a81962441c2d00b200d4040e42c410f05c5400e0108810081d1a5441034441038104442034800e0383c404041d2441c034002810540c00c220311901c10090040003400094244201c0c0d03000d030744001d2a0142540d2054401010000301d050108000c41c0441c0702c007a4000348105c5000404c0c513070b81c012110a0b82c00032191700fa481d200c00700042140c00c1d20400c1d034181103035071001c502039080c0516003a42c0e01030140400c914104800c4008101c10010044100c10140c00010304640e001d14215034001d001c0d502c000e400b1140340c140100030189480c00000c0250042d50320100060610342440e02090013440514100b008100312105003030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 774605431 1250 774604181 774604183
    0x105092a031f021e0f0a0509120a050705040b01030e0307061e1a12030a121808070803010303030e0f0c01080c0d0e0604030206070912020d03020a0c0b180103060e040b0a0e 75
    0x1915a034049100542c0303440c4000103224041550013107002c501003040003a0301200f0310003030480300100014140345032200b030785101107454911081c0d10401c84d440307003810100522000003a81400c41e04100d40c14000110341134011025120484110303040d81d4005c0c001c481c0007034016001285002542d08482102d904c420f404041a07400c04481003c2d174105029a0507501c2c10a00c52803403078256414015481c0c0f13701121300503c1801c00c008030708440c0743e40c0c800013400c2103260300c07a012007250040340e015210f10241c2084140c40c1e20a1204402103850500f50b00400b60000c140b2000e03040588000c8d201c00c5030350100541c0ca220b40240710152001003009400300c08502072080e030000f44000e03c0201303603510381450701900d4a44090001c0040c00090a410050300284410001c1165410380d80c041000c10203181c281e00d40442c43e1300c003c00c40c100811001c2002c6100d000039102c111000341d049844c80101c4801034003121854014444d84240c0040000e0200e41d950070361a4001021040000d40f240aa406035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 774606681 1250 774605431 774605473
    0x1b190b0a020c34120c050f03150601020705030a05010b1011030307030209041d0a050c041808070627210c081c020d14010e280f02030c09030105092a03 66
    0x204408440f0113040f2810b00a00c2c02410021306010b60b007407150007031003200180d944c0001c0a00030000e0640c0c8800255264030a100c0c5900400000c0c0c01ca031050a545e14000740a0151b90508030f0140c091301c1d8000c61098400ca002c40d1440c1c5910014624540380c007802103003e54080c444c902d0b0440e403100300300c4a9104074000301081c40d0159002034500c2c500146040340c1090940e90f1614411070030521203a800d400c5a00070218040d61004015560700e00c80e14050340a011007100400002c803031201d4042800c11080b500702a075522600d03041c3c0d07851820035281e51a4040f4054514000b601205912000032241002070034811a000100712070007418040705816a4060032004202c1ea442d00d40441511b03110600590160942040041680ca00540359038004003c034170300e100219101940e007100c000c0762075120510051050b0420755480c40d05040c0c80c00107502c0340f079459000390718000c00200003110101d25881040d200c804030044001d0740081d01e0300e0300018801c1c003c0e454041d07484d80e01004107502c001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 774607931 1250 774606681 774606689
    0x151b0a02180a0f060302100f1803050f071a0901110a02130b130603150506131113090c0e0111030d06120c050a08030f1b190b0a020c34 59
    0x10440c010719240112209540034010f622909504110082c801a607590103801b41080742490705030700b00c0300910001c8404040300790030500c6a82c034104010041c00070114a0802a030001c40c210b030b0000b565000074060039011450300c0038810301c040c880e062943d0301c96494020030040e20b0b03007110b2441c001600010303401c01022020180d5130755a8101c480007800c0c01c0c242541180000c2800b0440e8615507213842082150401c001000203a481001903295503c22040b40150042050100030a110326020b42041e60310400c504618032001c01c1c0001000440383c055210211140d84d80c240003091098019101c040348903003e1800c50006100e8502140b03400d104145c001c20780203032204410211801c08400030200d0742c0001d401420303100c03c00c0c4284a0300000311000000c218500d42d0303952811003040b03540005084180f5005024100000d0822501d040c40c10101d24060100c1c1c50741601d4400201c0220700c1303680c40d0760f051500880b1011303e0714841d41100060010b02c6140a900303045003d01e02d0b1410100a0300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 774609181 1250 774607931 774607969
    0xc010c030f06050102030909060907030e06010303050c101a0f040608030c010504170f180d06090807050f070609090f06050406170d0203070b010e10090227151b0a02 72
    0x207003000403030141000418080c0007641c506100c090125401c084000d0800d801034042e040032481c00d030f110351b020b101200c0103072069540303d5841c0c2c41d00420a92281405111a101d0404015010802441402298210701d031066070141c488030b0074056007210b42840c2c643e100e50780701000100c01d0300030300c0104402048080001810b14152501032030b80f0400c9206104125001c0c002a400750700b40d1000c03104440d99081e905259040c0703440000e003252030212002040c5908048680c010413070b007a00a0100248074005441000c0b0f05815420f0f660b0000c0e01c079036400104a00810041d0300095400b40391000a030709004181c064586c000700e0f0070345015038042c02100c466000f0305101c4000610604106854600c0594a41041078644400c071003410b018000c107259410001c604241c412841c0303800240030400742591150300c1c6013140180c1019050000035011000d41a80d945890000c3c6041560280c03ca6018107240c5c003056840c83c04001c5e16141003a40c071507902e4070b03400343c0d44242103402d02c071625034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 774610431 1250 774609181 774609191
    0x11a06070f1112012f0f1e12071b031209020d1a041203111c090f0305090f010509030d0c03020a0812040309090e07210b040b2212140c010c03 62
    0x7501900c03050045170001515018140d0400c00d1140e2444c0440b09020380f1030324031035100e0301e410759903100115801d0700920308071800180c8051400300c0d030103041d07200d1885a02c50b100d2000e5501120700a003c04194000e0000701285080d00030740700301b644902c803043d0003c0c203c950800d049690b0300303208410340d40040e43c49000900400081100c5c2c40d80d0f00910000c80e14040c05000161044400d06005000340d1078003003c80c06004044c2c02802da8020100c0c56004000400150343e5401c010f812503000054242c010680e07405040320359400b54044a40c0180301400030465080750320000c541d0001c2e1900100c0450055000580c0804c66034030181250a180716480c0405041031710f400b4100c510180e000790300e45400c001100b030041001140d190300b21824014a404100e440d6000c00002082016008140070444000e0105028007150528480e1070120b140e11020100e5044116911001180c02003515004140d4114118890070b102e0080715852004c00e4200380e15200c00c10b00f075621842d01b00001903620313 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 774611681 1250 774610431 774610451
    0xc06081003080c3a0c0305073309021c02060403021e0102010f05010803220f06050d0c020303101503020708161a0907170304030501020403030908011a06070f111201 72
    0x2050b55140c0440036000840c00c0340c098045410030341c40384150300030711a03204114010706021748110b40701ca95100c00b1a22504a140089c581c48040001c0c009552884003111412000450310030b01c540c054004084e0503a0600d900900080c0c203604d003030200d03040b61060200100607107078a840b40340000600782c12804040040c40009007180c00c02c185801165040c0b0b001040440800320413070b10100886550b140b2aa00d00001600c0e540381e140e4031142007051111000614651f2100283c00024034511062018607407031001240d032400152141042210810420080d803140c1c0f52a8507540329150a026003000090307101c420403500203000d41003a48003601491020090084a0003d9000d501c4154104d2400c0c8410342d19981d002c40d0140341e800c0400d11100051030b070801c005580065610034000e42d5910340300d15005020080389c1c0b05412180d070802030f82015040024131586810207000e080707142003000d5a01c4044071420001c0d400c5c3e03646078055100c10071940720101d40341811078441001203643e0641e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 774612931 1250 774611681 774611713
    0x11030601181104060909152102010801290c15010603050f0a0915090f050d0309120c08070f0f060614030c030609300c01140703090c06081003080c 64
    0x440303801c5450b102c0200030602001c1d80044480d01600d4601000180490796540e1104010f20660003c030710b482801c00d824000c0c000b0b540601102c245c800e0f0303140030366030741d03107507011500341426042c000d20111861002071b0355014154090100c100620040300e00c4607485441c03d003c01c22080e005100007e4480d010800228000c1c680341d9009414010204042450ba854030200c441a418510124546440c0d5031400d00c0480401034203029003202c04e5030303000100f60380060700510304211b0859521440300030b907a140038003c4403504211a007000b28113242c219030303540c4c107041d811340648100c076110b4814140002141c0340e40308071000b034040c1200092000121100701813800101d620800c1c4217520420802070320520108001c1100240180f1941040410484e40348110002080d00b03080300402084441380c100c41500705400c68010980e0350702103a140c1c1c0d80e0840c141e03005078201418410352140304010ba207201fa01101c1c0d10008412211034599283e079646c8030564032115015105034407400301d135411045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 774614181 1250 774612931 774612941
    0x27020c0304030326040308060a1d0a1b02030403081e1911030a0c020d0804030f0309090501051f0e0f030102132c01120305090904061401061d06071103060118 69
    0xc13403080742590004410703861035410f00c004000504000010004c2071690700c86070301410207040c610018030401d103d2407a10441200048401401c61410182c00c0310a09908920000241640741e01440c40c00741980c5810348554040c041c1d040d44901104030b100c3c0c181e0310a0740a001e004003120350620169200081c000c01e40d070702c0e11208011940042083c4020309070812018145564196010b01c0741c036550341002c0d0550301440d80302400024294000b002015400034a250954044442c2081a642c0b0345040c019800481a8143d201d04d060744294404a4011000c4100c00ca400034003404509000c14086400c0e80c02c02d0510661000303050000303002c007008081941e68495400300e0140180c0c02000c00c1030f01000010320031450401c4856984c03100303140c461011103184842c0901641c0a5050610f00040109030080d03400515461180002c196035124200340b18141041180c00f5071905031450410a6941c4810007c0710a0303000c0c0c1410000350f0b1024010f8070f00a160b0490a101215440d01c0c2071402c0e94 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 774615431 1250 774614181 774614207
    0x40e0c100e03030d270c031202011b0815190305060f0402060708160b010314011a030601330816050918060d020a0f080111040f27020c03040303 63
    0xc240c042074220035440c000140c560419101501041a070002848130460b01c00801d2040b41320319503564100c090041425102084034851290007912030403448080382221104003110505122244128860504c501e08254000c1c50521404030385802d403070001440010f4050f020b601e2611100b40810034041c1c24045290f106101842c000c00c20301d42032b4000b0f0080d21032140c2c01000d810001c02c0c0d0300c4650400c02814000207030311041c0c60300c0950316818080190341b41b0507050040ca6080001d1000700f2401d851a00b918100e01600030300c1680d00384044008490054107801c140c00314031210016040f0240013580e0b140381629200e02400d401c00032440c0032071129409407001400002c000e10515a124001c200c520840c1208006c03803240c6030a4000b80d602c044203035010354000d003010390114200000b0b03111a011525003400800422880f902c0c0b516807409544245106014040d10420000e515264846d144a0f040c0ea2440d07070a01640400700226000ba00c9068040c0c0d00216080c01050340002d40a5001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 774616681 1250 774615431 774615437
    0x302030f01063f0e1b010302031012080702040e0109020a05060a03023121080d0f0e07050a050a0f0e04080f0a02060114010302032203180801020306040b120a08070c0302040e0c10 78
    0x140403014580b04174144101003440c101039000000440e078500c04450580940121120140900c5243c01c085a10390803110083e845640790414401a51070144100070441e54054400d100407880c000c01c009064201c1041602419001c0010050940d01003445044c50710203503900340c80a5001e012051440010350300803210980501c0071200b1007041d5003d8070b05010358414100760b5190841000d03c8064903113410b03000c01540c100420b042d90420b0101d010025600281e8004819035aa802081100c100d01c1c81500d090040f0910103012000c0800e0349154014024500c1614160401c2d80c00842544052074440058111400510000c2c25011003a24083d400346000d504600f41010318000308460081002c1c0301a6007940e40b00304143c02444082110403000d803140000640c5c031441c0b02d020790300c11540700784154605040c94171103140c102125020800c40d18000c2503c0c654940c0c030008507078040c80c425211885032240010040e90b85001f10904a075648002d000e00c03805000910008480a02c4a8814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 774617931 1250 774616681 774616693
    0x33060605040e310b07030509010506010c020d06060509040f060b0d03050a030902030a05070f08071d071d03010207080403050f21130b0f090a060302030f01063f0e 71
    0x414040d04940681081003902240e90a103040d849500183c8000301c0301e208440c0e214403071203042c8030846a0b00d911480580d00e00303020300c0d91101038031800c03240308568080c00304004035060409414000080241030380314401c0020b07060707100c2001509000b03049074105c072007480c0d0580d4002045141c0c00b4801d10031a05031103402c01c2c503e066901a00a000c1d0324140802c1658402000f020355074200040c1c0a01ea4002003503070107054445600302d2800d2068003a00720390b0320800300006000c178002d450445195a51558220150b12510801c492110a21254000b11408992183d041c3c0c0e07003e100810b1064820355606607a41c0c81d607e8124240b14100a914403a40c00c074102c48500400900304055100d25050700140c1ea4115151070540d4444054004004030040455503501501c40040101340956080340c401e01c0c00c50f52080100c1c1070f44012110143c01084240040004501842c0e40c19900c600030f02c80f502802e1220901101101007a02d411140c019107607000c040c0c1c024641c46444440104078000d040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 774619181 1250 774617931 774617939
    0x1201061a0306041d0303011e1203030b060f0c07030209130507060807050c0a0b09070e04050d080c19022109030303010e070207050306090d03060b03090a0f3306060504 73
    0x1520140c042126006000001c00560b640c0d8030350340480e8803114010095400e09904500c2d40b44c2e250004d00807920019880a065038408179410714000880d050002c440001c4d8005039012800f0b40074040115800c50070511060b4444d401c49000351901d484a4001400700030701c0e600401140c0b403000b07003841c0508481241c0c0040403420215025042d40d0f03132030602c03411036201c4240403200c0303108141d601403050007542800010803e0a000711400f40441504983d2820344a8000406074041030b14020500d034403249090844c0c44c010302903141c0c4440d4035004103051006669400452200b040803450058101c0e1600c03070582142416130940f8089440c071001c0c181211200440c0ea030b444180070310000402c6100026005601c00c004220140c80082c0a451190410180490f43d9071410601c0b44040380c1070650204042d4207850a0f20b1082c4034800051070321000644823100c8203500803006450341c85102c03509142d15240c030351039490361281c010300840c0f0301c940000386501180d045401c010100702003000100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 774620431 1250 774619181 774619199
    0x3080d0c09210816050109050c01030b06030f0411040f0f0f02041203030b040b03070305060a05160905101709031e040b030601110a05070b070519080a050a210b120106 73
    0x202402c0007500c0811001e443d040c5500c0302e01444107003444074040240c0c0d180c10048190010b511840c445d5003100c06c0e8810306001074003590030381c0e941c17503411010074000103a4005103511030079080f50140101410040030070000c00c0540b950310b810080400e80301e8030350040c0c110440c0f007a0740d0300065084046081c02e0518450b0401000d80c15009800c25407a5100c04186503260b40c0542c024050007000c84907240d9032441d1035a2159411100480b40601d400001000040c1c07005441481540c0d50780d4502a035400c240401000d0b2003107652460401103101c00c01a601118541030600aaa10000854541ca041c9803a002c01c054100e182d03484002c8203000c2003041c44090400e80390008400d080a00b40c440c540c24865203010443c09010b046441045000250480050014050103018400361107810707500040d003039100451803500402c001010054150054452005400f2126040c074207690000b1100c100a48200c82981e03c0084066a403a203034103184c038000300d20840d10510f5100905c01285404100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 774621681 1250 774620431 774620459
    0x20c090105090a110c0a111e130507020a05010c02060907090603050606120f0102030406020a03060504140a0b010903140d0305010806070507030e010c05031b070f0506300103080d0c09 80
    0xc040b04540b03400680c0464414074042c5d80e01c0c040d019040307910010860414450300019581c0007806080c01020001030003038070310f1921001403c0a00300c984a40c01c803982030760007048014071203811070069035441000680c081c050000c041903198002c0800d4240074150030f00b440095403188109501e800001c10021708c0c00314400368010f600f107071211030100321040d405040203842c218040c0103510000412040000680c041c1031240c1056404024440d203034814001101e6002642d8009414118001088004244c0007000c2043c4185408100c0696a543d05100323108524042c0c44c4a405c4419103080c40c0d03602d8030800c0d006255580c02080103041005000d40144210800a030130064450745065a59001d40c1c031403804640d004040707a0b5100d090712121000202e518101c0c3d141030082d5400041c0345000312950f0003d4030002041e031454016005014910751003072540c28400350b50000e8101c4402c81120040c94000d60040c21980da40c1d2001c45440c02c12181e0002c03110341405058003003884407410301882 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 774622931 1250 774621681 774621691
    0x30b1f030b10051201050106021207030c0f110d050304080f160e0a15060816020d02100e10020c0303100609030b130c0905070909050c0307140d200a020c09010509 71
    0x107107203151662108210841e980341c0101d80c000c200c0e00b0051303000311030550019041b50901d5080c0c0d4008140c0104964403032180f0322001d0000f601c003040000c042003540036000030581c49500c00400d400c40400c00b091640b010510709a641e600082020080480c1c00d01400142c0d1002201400c6003043c0c04034030204911075802030301c03c516103081c001410001150b0121a800c0d00d0000c000c00b0565503035200903c1c3c01801c81c0c10958000344200410112800000e030049a030756950007504030b4172880c00c5900c1c0107104011607002c41c0c0c4108100c0ba80300ca649c030710023000d148240c28051640d074607040380c11219120456012408014916904101040042e020346420401a2501d406542c510703041c1901040003607084007000c140382009108110b40c110700b0b070804581503810144500d80e501c0246005502084890034040b64400348a660703100f9458008051031500300000140c013840c10340b00d5a2041041c0a104100e1000014026021540410404c1030b40c0300c04441d00c82c001c1d13050802144440070003a05c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 774624181 1250 774622931 774622943
    0x51f02070f03050706120b0603040606030210024201030b0f010b0703051918260c030703082803020409050f0402030a02010305070c080726030c070b06010306031407030b1f03 76
    0x14400c6c0c014050703400000c0c84600c010701c0356451b410700e4202400103086510081344030b40c40303405400600c6e9001040c00d02820800509501603003440c1c1550354049680c0c03001d40d00d040c020501c02d0071401c61070f841c0301c00c0c040d501510000f90140781205040c407402c007040e00400d40c07c0a062121100099200003242c02140e0303004429014400302c05c4098842c1500341039012109070103200c003c40c07101000713000c040408181103010b02c0c1030900580019103c41d840c800c1c0c150141c005802c1031000c01d070110001c140307031542621004209400001a400d40d4540c074521200003039000981000218083d018140d0402e41001003413000b0708090780007a40d1b916111a00905154980d800a0310309405100301403103143d040314419968148925041440e820383d401000354644402c401c4050144044003541d12400c032301040a0700c3c00380540c0f502c00c01307010014078032030405854030000300000d401c00200030b03900030001c8014442141141341c029684140100003007100c50a110100311000d0b903000011040386c2d0030807 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 774625431 1250 774624181 774624197
    0x1090e0a0f0305160b0403031e140610051201090219051801081902161e03080a05040501151401030b030102091e0a1a1e030c04090c0306051f02070f03050706 69
    0x40c131509400c5030031240501000380803000c02081c9038264000003d1456401c80d22000f1440c0351100408a0300c1140002500840c21b60008485042901020140104904229040c000345e50003d07242400309810012410b84c01060341410540d41003120312106902e41407c0b401c21200b01e8000d001c1c00c5044400b20704005c0d5040100e00a000c800101402c581008041503603141c1028000c6081040032000071205641c40d0004e2080302c0d5048000104495891303650b00c0c40c0c5840e2109010003034103029009076840e5603242e0030300c031450030b260954800400d05081442400145000050112140c1802e11806a4010040e50390943c3c0e034101120a059003441001c0394041c212004178406070101c1d000040c200000c00d65005c0498400302c090416480154840307250000b81403911a090b01094655544240c01070100b804400802c4d00080700710209850700003000c0b80d8410000b81141080000b089940e401e95031140505681808032034007410789008600022481c503910b4a03a43c4607203100f0901001b03100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 774626681 1250 774625431 774625447
    0x614190e040902120a0b090712020d1a041127060d0c1a0705071d0a0b300c09010b09040908071506051017011403030c010501090501090e0a0f0305 64
    0xa03401455103c2d00542000c1d01400c1440e161a911105031900761800043c03a800500c0c40340c40010a802900d500255860090f9503030360a001d00ca126440d0100c0780241c03000c07524611014001c03a001d2085005003490001a42d0010501407071341c00c40c1400d11484548145000b010100da044041e0f0400825200040d40c05040e041c120405c0215800001c0700013046003000380c2c80324845c006491068082c0b015901c50658552005c00344050000394014001c14810000d14110115031020104035806090055520250040e01c450b50b08100a050011103840c21509624101000140c4078241d00f40c03202c105650420b0307018081405285507051040d92030749445420040c22400350791a05900a000c004500c100065220240800d4003425004081008841500510aa1416020541041c0030401c1c2d03900300001d030000100c41d24503140e0540f10030862040300c030100340314050081018800c009050750400c0d020005842500c1c100403056030000351150081000301d002800c0c0113525051071a55030400b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 774627931 1250 774626681 774626689
    0xa091a07120e2206050f03070e071b050a120f0315030605040303020c0d0f080721050c091306090b010507080a110715020307050607081302090a020903160614190e 71
    0x210069904865200c40c001140f000b640c2d811180640c0c1c81141c03c45400c202280505507211028440c01c0b041d446180c0c0486c2c100c0b4060401012101040344005940348055115146401c01402c130490301d0700301110100302465401001401c020500d40307000d1014000e00341e5007018008841c04050250390341c8401250404d0b00990459036101c0c00d890030b465120850090142a086810b0706c440c0100d41c500d000583d4480c805c140d464607004a8820040300650303180c5001e0010300e401442d00801031400c11240c20b0f03c0d135415113520000b9002c050003044460800314102c0903a10900c1a007030500005009550005007200195113030540e49140c1a0800002c40107414604195075212103084082c000e20011403e60100003070406501543c01c85166455030042110b41e200100c07000c0d140045e00d140c0350001450301040445c1c00c520007c5000d428029404002800c00e0054201118902111282080b81c95040410115a1034041c11482d0501c490304030b407204212200d02d02e100400c00b0703d00e40442c2fa1b41c1c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 774629181 1250 774627931 774627949
    0xb15090c03090307170d090b07030c03050f07050d0608060a0902120106050d0209130c090606020c030a030905041817131401120506211b03010b0307090209150a091a07120e 75
    0xc01140a10804400f828231280c49402a0740c4200000d0401d00350107490b41c000d000b8a07002c2c0b0020020024190786480d401c80b480e402c86030351500c5080d250300f000150000e041208a000b6010440001447c141510402200454a1120a170543d04081c0e04000940e00d154102103c1c54040d41e60034500d0355840c500c00311800d210b0000500c00a034503c80420a40482d82c00842528501d400b02c135040d2181c0c2c2c00b015600c1805590040c00181d40160622080c24203030420400e80c8040e0b40c00110f6040507944000300302e11501c14180940c00049241d03008c040075406108010035101e0f4a0b080307041d4030300c17000a002441400780031001d03948503804030f1029107030301040290211945200342c24140d1744940d0f07070b62280300720200705c4c103480700b0702d400350000c2e140600c01c1e60101100100140001403a010325003001e50010a000c90f8000407074080d8002c5126a14000c285035091944d41c1e01e00700b0305051246c400c0078030b00b0300b242c9420081840300c100041d130044020100c0040c0ca043c0804104150400100307406 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 774630431 1250 774629181 774629197
    0xa021c05010f050a140610180b0c0a06060b03100b030403112406060408030d0e071805160509030c040e1f0902030c09101e030b15090c0309030717 64
    0x50720b030110021032084680d00c02401502240d2003405052140e01410901880c25030340c0d1a4441c2e0304640402003240221038520081c680c4010710311819903100a26081074001d03808107100750b000700800e88204511485500040e1201d05010380c15424814110344415109000780c0e16a04000004034051501a00c850200303030140c04100d9443c0140b80490500b221005101e8461415070300f4080303031f2140362040544003a54042e000031404c2003413141c08040a41951110400c0c1e42c01140c50206001c640742500e41c03c02c0c6034402004c90780c0d081c00c20044410803d0040010104113060000045554012401c0c600c030740401c60300440c03680d04c4501094100015500001070b1300340c2500c516245c5040b03a41000501c40e000718250b0300303a07200e140c0500080d03000c21240700c12900700745041840b601d000c00300b070855104094000000707002d46172f80c2c500c2062841030780d940300b03400c0b040707052681c403440c04041d49680040701900c04c0e815801c05a92103a42c0f4002d00c2401022a010400b030048510344503403e4540f44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 774631681 1250 774630431 774630433
    0x20a08241c060b03010627110313050c1c0219180b0102010b09101e0e0403081503010917210106080601180f0509040222020c0118050a021c05 62
    0x11200d600c001c881a108075801200c1d0a42080002c0e02140740c18803d8400303c800c0c44245c100915140c51290314582080305041100c143e49000f802e000301d03c0301700a18803848203041c80040481140c10f016107403102c2400d10350311813178100007011462031040040ca84c545034195425040c083e41242c44001601c459001041030810003201e149000e00b041e0405849a0002c2c2c0080105e58014020300c040c04404564903081c1142190341003001118a440005a182c0760001020b1aa41c5032104040d01d5601920141c0001c1c0480050060783c003524054200e1924046000b04010711040d50307158100000031819111543e008203012100d0300b64400c141c508200032243d007204560f1519000340801e27000f91201030001c6d005032003841c0802510880751040d503141585000b45545454108001c803400140107d130000d01c0180c003954081c1894004050079500d2000c05a1100180307000c56003158910048251500c241e5a0201c002c180041102c0409580603100308603480420200c880c02500c0c0064000c00c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 774632931 1250 774631681 774631699
    0xf120c0306050a09060b0f07081e090108010648080307080105010801180c0e0d030201051902040f0b130e0702160b1c09060e1203010905010603020a0824 67
    0x201a525500c51401c1c1c03042203c01040c00354a80c000341d001caa0060241c082914800c003d40c125108204003c0d088192003010664606180c180c0b188110060420304103004803000f040b070304255070b04842c0d003a002d001249081c000645445038480ea00548840c426401c2c4d4480441c04098401488102882d0030862120304003500c80038648000a0381c8102c50007070010b00450008074503988a0081c1504880b84205e0034519401c1c150315070401040712000307003424005036500030110383d220030100c25000b40c041d40001074070386030000381d00380e011210200e502c074440e05c10441072050200c000d00c0d00d0160b40001c09a00e440c0c203000052480595000d40212408441c04400c201d08140e00103040c00040c070344050ba1008065a0300318030980c1d401108040709104d480c1c5801244e90040c0355000c4100c190207410003061b16140c5d1040c039410200300a00340c4d05007201c000014080d15005006190040c01d01386000c51500c0f520360b0340286903031409070003500084c8102d522001e080110b2400c941c0740e0303103004002d100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 774634181 1250 774632931 774632951
    0x30c0d0504110d080c150603071406070b01081b0f21030405040608060a0c03090c140a030210031409061b03131a04030e040902100e0414070e091b0a0f12 67
    0x4801d800c074542101040c401d09054401140000d40224001c21f40500200105420480c0140c80c4c200c00304040c5412600500480c40807511810506000300138000113826040380caa210b030301c01c0c7e001d0801018003030890700200c41441c0d00c8046200e290702d02c50103800c2d07044d000070444940c00c510907580b14a07801800c01074041040c0e00c4c08140c45000e0020701d01c00700300c40c01110a06500b03442c5104406801024140e0080000200c4004041481140145902078880c0c60394005a005083c1c1141c110000c1d541d18a00351841000200c0035030040403810081070907292039a404158541c0220100c3d69142000c07020428402d0284400040903034400f2040d000000c00c01c030a200301d1201160b06800207890141ea9400e0350a0074801e40e558070740c01401481c006441c0c1e01c801c2e1542014224400d03041582c4007104a481070130b02885a000340c001d6034842694071241400c1180c0202d000d800c200030b90000302d6078403904014100c1114003142d03090800180450100b001661700e815070341e80c083c18a9042503c041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 774635431 1250 774634181 774634193
    0x16020a0503030c091c20010507060c031a01180302150d050702013e09031e07030303140c040911040e04120809030903060c0c0307020a030308100b030c0d0504110d 71
    0x4000c40300141c07400300c0100002d13041c01269010174800540300c0c1656a40a032542100c010750170384624410f04080e85003000720340e1071030200c41d200740724000000d55418118038001035a202000d0100401d1030b060604002d002554030f060300c201e1000034860840040304031503001090051f00c41905041c1e00811142c50300c4200680038244603444010521191081c850500510800103404071610502095014005100114069220011480d80341c410b03048681021000800c02604012100d00a0a207091035898094240c81b041115415030401d0320082145800c031020640e822550003440c00700d40b000058040301070921450308201c4c2588003010410041c8441c540f92203150841d1a910a8190341e0342960711a1079000c0c0307183c010307491340092010a105801001c094490988010140c910b070980c540d0000e4400d00b5280e0084020900d00c4003002845800388117103800801e60702003058610714049042070302c3c0303104416548109a50b101d010809110066800e80700c01c0b10003410707a80b2500c111342080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 774636681 1250 774635431 774635437
    0x3060303021f110c06010f171005060102070924120224091e190f270e0d031107032f010606050d321e0c0d1503080316020a0503030c 58
    0x41c0c0d601f811015001484d80210703008204000c1c1250040c2c40d42e10030304e140500240c040505550304601c00e000003c5174580d9648100c29902041400300c43c0c040b100103c501c640c0d1071071940000440c000008040c005030f1550b035040300f10189081c0304002c0340000c400c400d00b40c038006d903100320307421600c103c14400b242d00c02143c8510811400f100c100941301200003d0035001000c0340613454254051185c200180303d001000030003030081025005040c40241c0c0300e940101d03100301c08201d80981c441c1d200d40c2c0000d07825202e06074841d04101c1016190110b1524098508800c0c90382e00c07809881c0c0d03483c0d28a0080d001e424510b00007041d06000b402003594501c0024169049000e01004885c03500d2000352520000d00d0034038105101d403402400000481d0150403100342d10003030400c20303910511400e403207540c5d000700c402c28440c001070101c8544404034080c1ea141140c9507a002d0310200c101020701030000c01e001f1130540ba401200c0501040301c900d45114200c0c2860204407000b04984404403d0125500d030850207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 774637931 1250 774636681 774636689
    0xb0102060f090703081b2e0510050d0501021908060a06021b01050307030e0d180f032a2706090e0a11011112030f0c160305091503090d090603060303021f110c0601 71
    0xc0c400d54590343c01c400c0108e0341d0a0307596401001d0292401c10250070708143c0c800c40140200001800d203500c00e40458401200700185000181006c000c00c00c142c070f04080500040c00940c0b004001990103c041050602c1030400c03800d05110020000450f2180710303400c45440c038022402515840b136060b00340601200b9030259540d420001a8402060743c10208140710100c940102c0317500100c1d5140c48202007210070844907540070246512000c07895404514407181c40c018480384000d0380101c02c00904040b542c0035084902a1403c01c5d0300301648140004031820010380002054249814050041e60030365581c607502003060080015180d00c0030810f0019500c658200266604940e0f00c019010145108620201c100c007120580807901081c4120040c00000034050404503110008400803c15a0030441c1c042400f40c0c403002c1d41042569008030280007c0005080a010f020b05558002e501c035111035480c01445545140d030a4030406007500b00d441d492400418003a503400d08030f20019200d80003401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 774639181 1250 774637931 774637993
    0x10b0432191b140c0604111504080714010c1110030e19051009020102101e11032a07030c08160c06180f030b09010b03030c010b0102060f090703081b 65
    0x3420b510303900000f03012100780e420060301030001d903070ba65603440c0f0030000041c504d81e4020b81e0001c0000b500c84d19440c0188050710f0050002e100040c81c1641a116440407072202c60304000f9141286400500302c0b01010740c07813000403200c901000a4440c411401030003040015100d51156883d10582c0d03542800c40004074602a00c10760310002c45010044040d43c0c10450024010303070000c0003408003991150f000b03150803c8001225000c03036140c0c217150002d40c0c14141030b0810000303002041c0040000d031485019090703e8a5411505d10071003e20f9180d00c00e00810b0405014044001c0900c01081000c00444150010140220380d0a4209040899011625000301000b24850b9010f0428406a08003d07070215066011045246425965031400741d041c080d00103419503417100e210580c66502030010381150882d8400025403450b04000080c900030b00a007001d49102c292905200320100041040d00580c6e4110703200c0360390782642d80e0380300c41c201e004039030030030410f000d0083c0c02070b402c1a00c50262690790001302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 774640287 1106 774639181 774639197
    0x933051309050105120105040c09091103060907150806090105040908070b07180b04080307021002190f060b0105090f1302040314010b0432191b 63
    0x3400660896840e60014040c605040145c14512903840c3e0080c42103041544506444204c40c1c0500210561145502403e200c611741d030b101c241c894080e040740d0031460207441280c1c41e0030040c0600c10a01801d03001620b4494460901e5902030306009281c0071260346003104000007852440000c0380c03510300038080c40d0042110840b001d44180016200c40001022504c2032504c0c10800340c00465405105003c1441190786c000166134106505807140011040242c9013a490000000030007410720800d01c000030108040500d905c8035071071043d030003800714203110401540d040c01a0004d0507082941440075405515010003e083c00608004d8010325150b180e803240c6400d404040d11070030060303443c1c3d841c002c2d55080030322402c0d03000115048400850242d81c2042c1046c030082203584003240090002040d48641132641c1041d003000102e008000c03d041c0c0110902d03651080a07413000100e0104 = true := by decide +kernel

theorem cover : BRFrame.Cov 774460431 774640287 := by
  have h0 := BRFrame.cov_init 774460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 774460431 ≤ n) (h2 : n < 774640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
