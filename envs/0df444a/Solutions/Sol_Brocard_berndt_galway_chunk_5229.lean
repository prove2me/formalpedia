-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5229
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:10:32.465651+00:00
-- url     : https://prove2.me/submissions/a5813cb6-5352-4420-ae07-a32538071bce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 940287769 ≤ n < 940467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 940289019 1250 940287769 940287773
    0x3010602061b1b01060b04080109060b121b0303091c031206080304050913170409052503020310030b090708210304080a020a1703060414151201060815010806070309 72
    0x1580f02e418024550460003480c0700084001c00e502c03240050140000d500d41d990342d581c11301800f070160248242c0d079862070844c101c10301e800d08541c64428000c601c400703080c004004480520445044400c0c4d2500b51009014081142d211598242103054403030f480140c2050680c900204421301c50510102c140341446810030032882e001080c1c13010354001b04d80b40e030001ea44240d082071300003c1c3d08074007500b14102101e071582200d49000090041d60b90066080c891030741d80c6a0205601c610081e80804a40341603101500c0d80c5100754051500090078201500348180daa849403040f843c4142e50705001c5402c0710f541001040c0d0304203c00804101d04100074203604903a102d9100e0240402080601680400107554003c0c5100740444000d040d07105500e940703141c1c6202a140328680040b00c103680520303d403540b43c6c0e040e000c0e8001641d20071401d0201e800b072100c40e4072052011250300040024403c0d03485201c00700e02c01200b80003000c10090000d0b40700f02c4a6141031074061030100b01a0164007070526028940c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 940290269 1250 940289019 940289071
    0x8160914070f30480e04050705120a060b18240d1a090f06060403080408010902040e210c033010030804151b120f050405010905040e031204080301060206 67
    0x1040c0285454900701541c02c4c100d080d580c10316254292988903180104114206800030090450301d08211900c2c5501d03030701d0840403000c03200c182c0a24815000213111641084213609202000701c4030180c6080c0441c1088040c00c0090001001c0340200e03c00701180d80340012070244920054400c601a42290508a0f400442e0001038080d190741641d81000c400915503444540850f8000d542c80346029961700e903206843d9008014852080b0b01c41c41c14a8016250740f0400a2408020104580d03800c4103104a2148416aa401007081034a140006d20070b150744102c0034280a046030700084103a40016500280c0320004d40001401000c00e030741c0e80d2a0500200300f032441500c00743d03141486802c40303030318200c10f0554440da0030b0034204214000b00ad0246080088075078106080342e1803920758000603420300c14117a403503019900480d4002003181c40f040010703141c6a001503444010450079a403330001030110070a01150100d80598000d6000401000410750401c45580d01c5030410811451480302006065 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 940291519 1250 940290269 940290371
    0x6030406020306010203090307031a070503071d1201020c163606092d0c02030a0c0f05120301140628020708160914070f30 54
    0x600035580c0070000403e1a40200101d4519100080880e14840d0b40d924050f200d0b404030510510085803500c01150085008505490180d1419143c1607100c1402d20a01c515011b4012202a0310111501c0c030140b00d110203100409079442c07908068207aa8a458500121001080d0320030004480042024003001c1c84124200d29540c0954080b00c240d9100406048058102a007100c101580703003c144000c2d1509400110b2283c2611482e00280e004066040b041214805080030b009a0400c01000450500c0394540404440c0300310084542444075840d20380c50158200780c0c0703841019001005000041154030402c18030300301115824900010384442251102c0c4420440c0d041c1c0b082c500003524024020b11203180a00641c5080340c078110706500d1104640b504900c203200c80c0d11724090f80080b0342040d0b40b00390b500c40c180030b40b50942c0c2c8003060700c0c046070a501c000940e9a0700c004011154280001d50811800c2c0301201c0c8031011820b801c02c0c4049e554400c8203030725811007080803500f07041160b00e188040d403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 940292769 1250 940291519 940291523
    0x606020f1501060c1b0e150a030c1e0812090109080a05100b0d020405070302220302090414070b0310050406050303070b06130204080303090601080c01111b01050f1813020405060304 79
    0x4c00c0d0203144900d4404405004200211340780810b840010800c1034284407001d2040781020501e07075a0000071720501034071454501014119410540e01403000390b003020340120b8422840881240c0e815074482d00c1e80e081c21400c15480c160703404001440f018540e4400c0140c0050100700000e0888280107a0750325541d1800c03d25400c1c86ca5442e4040d9410682e502215081a10340290080c8814507102034014000d610120204400c00180c5645062000e2086081740c25030764050304a40d12500e4a880b4400c50700840e8181d8030700e510075480045108803c0d5030240d809071010010451001382840c5c00c01c810b4505a070041402644144404400f041300802501d07004017082c0da490f0751110100c900007020344100d030824002e0344000000c0c0004028000341c803504960500342038403461000900115601e000d484095034141c2c1c0050141000e0f0031110040c000141414142a450f15018500d0b00696400c2211524043c400d00030500c2d40d0307400c1600071102c101d1610001140b81605040001e21180409000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 940294019 1250 940292769 940292777
    0xf010501031d01140703380a050d08040f092c07050a0308120907180c09050901090504032a0b1308070803090705060313200a090606020f150106 63
    0x1a50065001028100c41e158500003030000070140b103a466480081515010300107440c00760b214460503a0085150b140d216010a070401c40c040c1c0c0e4019065401147c2d03010350b4407090388140020b144da0755140c0450b1a80c4601d950f592154508005142041407a500c00d070001420304414540c4a0b070b58821140c40c8200081e9000302441081200750310782600c40c1c105641041d80300c403021050040d20005010741c00785100014800303a440c06c410f1500c0d2039283c8640340040030b02c882c0c24030014015810800044842c0e10340007100c640d6550019883c0c0600b0f0780070341032140c0d40f0403d1000b41130384010a041410301901c040f8917240702200c121a006449a01c01410584805011580702800e044041c5495a08a0f90060b01d4808a080110496100341d0300840c10b031107120000600703030402c4070a980c848c510041a0218010f540d850341c8010080d0581008159041d000585085c0d81d51040d0050241503407480c00036155040c8203019240c41c002d00c0c1d20304500ea00100d42c0e80c01c1c14640c3c0c0600f0341034446e9864 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 940295269 1250 940294019 940294031
    0x60922050717032205010c3008071b0201020607050703031b050a090e010f0e060607051509070b040e010b0a020a0c12060b01081b0a02030d021602010e090f01050103 72
    0x2045030604100d600204031801101502e00c1a20300b002002d4a01402c92480d403c83c842d184d060b2410003603140f4407400d40400c4e01242ca07600820521304800c0c00001c41e40364519000c028894030164200c1c810801c0c10085040c04003401040383e44107000d0540e446850801d009440b05c030f9000270b5036031100240318200300000029041c0402d40700743c10031000c41131403c0111b84041c249400203031040e04100c480784006002c3c030f01e00060360303880090080c1c1219a9404c001c3d604608000d500c03c0d2900c401080c3c0c5400503010000100010f80810101d40103c403884001021340c00c085020a040c00d1159000e4490103030180001d1200040c469046411204528602c90741d41840368400d90401d100c12401900c05c446842001415003407801d07001c1e60040c8283c0d802c1052007080360064070a0f200031b036094140044080c82d096480403031400141800345580c01140d040258080140040e0303032210714052842c41c1046451011035801082c018182d40c0122502c25185c03510510310000c00d034052007418101900c4907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 940296519 1250 940295269 940295273
    0x215030703062309091612061b0c02040501052704020102120a1d121902010513091d03071a10050d0b07080a0c0c020f0a0803030f0f060922 61
    0x26010800805600003c1e43d000e00e07100d2042203280450500e01409210000005841c042010074400d0918407071000c28059a410145c24140c60364400c18211201642c54000441c62105107117100708000803036480e410740901600c10311042d580706900c001d00415001c51044980c05805038060407042c0800c100c00b40969580c00100c4c42d1410b4450300d5081e000001035900c80c1c035688141000012100500c00702107140d0307110244030b030b4841c1100201d030282c0c00c98842d0155103080001c1c60254180141340c02c50400e6800704600c0c2c003000c0d207a80259046036403030b458440152000e407900705c444200e182c0614100b00b2603403903038820352040c01031945111361480c001039080084000d4010107480003424000b841500c0380f4290b080c006080d9540008250528000358403034507c1d0080e40c024000c60f540b000341203c641e03800c1c0a010308000c50303000d51120005c240403403000742c108041e5201c3c0c9a0788d031a02c4650b003054088400d14000c003070030a0f40a07503403407030401c08640002d2a503002d003655191340007203087c0164 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 940297769 1250 940296519 940296521
    0x140d0c020d020f0a080d0807140d091515080609030f030f040309030f030c050114040c1e03061b0801060504080717011e1d010905070e0c0705010603030c061103040215030703 76
    0x50703102c0036881045400041182c00d400102c1010650302c47e1039850343c0c1c1d2100001590b00101c024000322451400b0059150511303c0e603045503890b01d01c9800d02c03809551a1340c2c091429902d05403082001e20f00038050030002c0006c20000c071030700030621002561920b90085401d1145100092401145500c17080228042610542c1b54a009503000040c0304000501c41c07400070018080b42a007a1303011340c00d1040007080f02d40082010350049500200c1e6549003480d103030700055680c10340c8182448889803028000003084050051511603102e0f4144103102a840a001819040044e0062810030409201c18040e410000410f030302036501c014402d80c0d00c01700070071616015226501007943d61003844c406c54000602560802d0b01000ca09400c4910030b001c0c0603547e01e080b5030704241d0141c4241d00c011070230040800041051900300c0703610030300f4a10340300aa8a549085d500b031031340100c00040000600305d0900209210303e00321301000581c840e242d82031903000252084a141e00204a01a000001c102c104d802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 940299019 1250 940297769 940297789
    0x90607060b0a081002070c1401080a0e150c0d050c0301080a0206090a170706030c0c0b180a020907081501171609050d05030d230c0f0d0612140d0c020d02 67
    0x31004460411681800004c040e40201c070b002c460740280c00e080464031124495040b11141c4c4103070740e001220307681d0001d0b09015190146250959000e41400290300b90b000d400c3c0070388510742d1a220710365549407005002c8103c440050031010461021700c018000414049000307011260101c0320252149800e400040b81000c81c0d501204c09480d100380444907866020520404580907510100100d000c00807090351082190080104040c141c48002415103410810100c1005440c1044900603000756010455000c03060350341074003180d55070b0200243d0400035005c0c1100a0001e00e0910307a4001c0202d80204003035000b8100b00f13a03564141c1e030310301d48151003801100010080101078000c01b03803040c10304945a0f4091803a0450950401002e0044100100c20403051000036a1359001c041da200c1240c05495089139a01070b810b12410000d4050034882e90141201030202111300e40c9009501d4a00705104005854201040e0742003500c00d40d03078541e0031080041c0642d40660b016100c1d109203200142100d80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 940300269 1250 940299019 940299029
    0x70303050c120313050106060f142a0708190f2013061806050d030807020f1c120501080d050a0507020301050406020a170c030103030e061e030615090607060b0a 70
    0x80003008014030188501c1240b503130180600f008104141e2140c0c0100c0b522001e1310034540105041d40c514402d010070700e2b4001d01c40d440070744a48030903e140b041390b011034250b01c40e0030707001441c0d002d150240414030013400715180b1621a0380251080003100d65500c3e16030740e55507034050301200c000e81000400b03501185040c990414010304101010941582d20b80040c07406004214040c4000707032580a12800f584030380d10135603000801000513440c05660407034850b4001407055045000c1c0c07003800c2103170740da04000421110b414030091711050700d4444002403086c1c0802107040706080c04d0000400124402040120070b024507441e28942d640c1041c601502d103482100d80007074056107003404003c24020243e0203414250a035554400d0401d401d4001083e600400b903503c4288030404100410000c1d0198841350744800c40500f40c04d0801200d5151a02468101030541090140c0042000342a24000c030802d0740603a05440c403141410780b42e1012030694010300c8001041c0d10759805050700030f0350f9003500c0c94000305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 940301519 1250 940300269 940300303
    0x23028050913020d1404080a020c0103110904020901020a140d1103130302040b010c02151201080f03040905180f0703020f04140411030f030d020d110f0a031d030a02010b090604090203070303050c 85
    0x806c042c50701c820240e103c0c0b00301c4001806141180c940c0c0f9846402801c0d5010742c0c4c00c00d0075050a0061082200960221f0800d038107600c00e0804604c0000c00e0a000c0c840411000809007501c24400e5802510651111445c0042c07508108045000c5046030f9201c0b40c140c07901914000341c42030b02680140d070440c4d24954003a41c8278006a010900e290ba60340c000744407441c80c00181c0754076641e8414181f40d6401c550189420345400030f20042c4001c05842d402158800c92805852800c58441d480e642d04200d002c1171550415048208140b0a506050700c1e04881d00c2025a001c003c03200d6036007065015864050002883c850580c03505800a507001c200241704200c03074606030307540c40c1d500d4040d220081d800b41410401882c04d10204076020f80c040000c4d0317400780b40050601d914104010340b0440c000d000416681e00545e02a030891070603080300f040904402c00050300002041e00e189002c020306c800d0002c003420710031400c01e8110300060324003149100c210303680760500310745610409000c5400d0207580d46407030f1450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 940302769 1250 940301519 940301521
    0xa0e0712050601090e0304030c03110402071208091509070603020c030909180d05031905090a150b010908030a0504050d11030a080703030c030c023028050913020d14 72
    0xc084080742d11030486035603000400000012899150301c03401603220142150b00c540d80d0400100e2610041e20b25809001400145010a5a5203182009003015064030000e4112010819441e030104003049054002c21074a420502d00700c201507a58140e24090b22003014ac010032010b0603114100113441c40340400400b018100d1805100940d140e80010702e00c0b4680d44500e02001d00c1245c06001203e01544920030f958800c0d03c00031001001814014004c02030910400780c480010a4400b10009142d9000d040c0215056040e00c000511801c07803908000702c41d400c02c100182405801a0840d0b080342c0c4140c0b04200d4200440c01d0010310300341009001c1d034260050902c1c0e030082102a00050200340e01c0391b101004002581c4408404440c941080f82c00542e020100081142d411944030384061040d0784540001d054041aa086254003e828084100b1074848031000345158085030344a2416058582581411100c1e00020100f205005480805650000c3c0c100301061058008a103030400e944411002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 940304019 1250 940302769 940302773
    0x160507170c16331106180106080118061113080d0311070201020a0323040b0a1103070807030e04110a02100f11030402060c2104030317010308030a0e0712 67
    0x156894110380030381007034800801041e85200c070a0103500000c60b80c08420308250300c501080845040803d003407811321640701c20b00a4414030410000348243e60680d4115202a40070402a0945926070050805a418116500310300540c801540c182c190b0000360118000044803544030040c42074440c03501c449000028042030101c4001581c090008a42d60304101c0d1102004501080380100313407000340141c111140c2d0101007840386030b0201051920144030301040d0b0b25a01140815070280c0e100400030240803c0603404260800c2090046c0c0d25414061461b0a1150740d0344401441a42401030078403181100055290b1100c0d4401803008201d6080c0580d0f50404007006076596004844040c010342c248028041d40711070318080c1080d00703003d1482050847d2a1a8200800c40e0000d03503401d8914410402e000240480304203016003840e8803080d02954440c1523050007400072190b03a10021444585400400010300300d5421030b984151040800290003241500302400d043e1070f5840541c080201c5018001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 940305269 1250 940304019 940304023
    0x2070210030902100302030c090d0318030506010312030908120901020405040207050c090a02180d02130c0f090b04060903021201060503060a022106180915010605041805160507170c 79
    0xd0403e000b151043d907103416a0b0011410792108540e2849122428007450055003000403012103e2442800d015100707401926001d0200d259652054865502250040042c000309000d81844c9607540c1c43c040c085940075481e154100d200b854a0b03a9143c950381c800103414100e003941500d01400c4000c10965843ea0b031810700c2541c0b204c88203da60310640b00d107000724810005920880307c402c0c2081c0d00035546280000c0412510310089003083e80c02c4090454010b4140d90303e8821a031032a152600c80c4600294440f00c0100011999080385151141c04c00042c0b0000c0d41010214084070b40c1100c1c4020706147c02000c65001d056140d0103550503104046c00c0c005c12050b90f4002d1f1100704050481c1400c44421003030b042d0f4090f1003c0d034203a50002107808103140f450130082c030410340c8411250104e0302c50808441520805039401d030b02c1240002c0000c281400729000b07104c2c1a842d11b14640c40140304500302143ca40c45d421400c61a0b10080c407400051070420030030a03054054149003000e00d02900c03621f00e201159 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 940306519 1250 940305269 940305281
    0x3030504080c0f0a0b0d0204090513031d0d112d24032e120b0109151e05060309150714030c030a090b0405010f0608070321030207021003 60
    0x15070503018581c000b070800c0c2002121150145401048050304a16105c0d13500030541c0940461000346808000c0401c02d2015402002e0150002001400c554030003070400404040c00602c004c00640d6401090142d55031b6964103160a203900301d180f802a003016036000651801500e4000c031044203144551003041d00040d6154008020140c81c501540007046078800030031400000200d0521600f400403506090341c0038420410003041c515885250741581d005090395034615440046101000e00302c0314104041d000509004200004040c4070405640d007000040710281d00523140044007000602103400e9864080e80010603000c0c0042d44c1d6400d202c40c0003070300d81d4101105001490740d42004140c90a01c42e0140d0101e2407069600c240c1540c565504c6100c180d400a482e030301040d912480c215010450880c003084c000d620507800004c0c1190000010003e90354981d105009941101100304085a1044980300c640600511403225950904800f90000d0040d10000307504031107940c0c0d100d41c0312901580301c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 940307769 1250 940306519 940306529
    0x1101180c050a0f1401111006050f0f010c0b06040f090b0f09030901050d020a14031306270b04020d080a09090605060712030b0a23090105090c120705040305010603030504 74
    0x20004003070300d51003400315010252180702440c01c40104200700740c440402100b82582e0701407511044040d12002d07018508100558944080c07582ea5504011a14000040316440d41d0305803540e01c8030303650100020780329910700d800190148031664001820395403582e0120369605200c01c020480d83c40e0f03d08040d115018111480c00c607a2042d98003003034aa0704008103440c1030b850169100c03440d050491012001a400c1610b0300d10a111114181030901c00c00e0701c01445c0324400c000d88000c230400003400c0403025628106812601c401079030385030041c0882c41c4007131407024070740180002146841e03920105101800c40000603111000100e00045a150301042010407aa4400d009010080d2078408100482c810fa035402484851460404085507000340c000800e10075005281c00d00e0b00d60303249403406505108081c00380f00500c414048040906d41140060f01610041e45c10a003e45080c0301545410311654103081e60741c46603a000605003c0c41034007210007655109000f031050559920740540181c1045c099 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 940309019 1250 940307769 940307783
    0x30e060a03021b030301030c121a180c04060501052b230f01080a0b0403021603050106050a0608040209011214010e01050a05062205071b0b04030212210601110118 71
    0x40f100ea00d400000c00d8074142e9422481030b0290510b08260142e0f425141c9404684480034016600348803444040100c6c89900c8911803d0700a0701c40b05c103168109070790150103074480c0740781c4003042c491641d102c03041e944444100e03035024100c454504a4560415088805015924144644840c00841481100101142c103034140052620b418800d10b400f98424011303001c031a4801108500418409407129170050300034010744030b440b20f0040c1602c81c061402d400c01d40e407503915080c04210710b0510086a900512a41c83c03d080c0c1030070a1360006d00034071010300c22007500e8500d0400040502130740703030b80421490081038020410300c41084151806404120f540b1841d0a192000258080c100300c40000014200034400d50840c0c1e02100c4800010300000d06040700700100c200411010382c0600024501c058021036100c0498035091400a180220310082c1d01803600007401016002400440420303840705106441180c0d9503507080040b00c03480059010321340650700b040e40008402c200f49600d05181809490 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 940310269 1250 940309019 940309057
    0x7141c0b031507031109040c0f021605010c0822060c020a060e0105070210272124110d050f0114032a0409210c0c0b0304030e060a0302 59
    0x82099164400d000401010b60102000914028800c0d1302000400565019581c140700e500004101210844890384011030800741c1540075154040181c140060040500c0c0d0007050300300710009104d074038805001003142c10007040000911405c0000e4150401441c0e4605000c0380e41c615000b000004006400e03802800040004500940301d95026100c2403010b8503820f107032000316030030312007405400356280c0100704841c00d200b00301241c090702e0441d03046400e0002400b42c0d414048490700412850b180211404600104000058240b00d07004104003e0750429205d00f0703041c00c2d40300b800350050014203940228009044d168001007a44024042c503000070511211340c0e03c848030900000748030390589170b041e0300c00302c1120341a080c0703c0e2803010000c0e45c0b01001c0104038010030110307041d600c030444126041c0c00501c0106000b2100c5000d0400352049070301d080484c00c0800d840b040000030b20b5000d054200d19000002900341400341040144440024154660382e240e0320500500035080225004d035903d040c4a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 940311519 1250 940310269 940310291
    0x130603180b01030f06090203030c0a0308161707020c09190f0506090112031e050a081b040306110c0f071412060f1b040609210308060907141c 62
    0x151810507684007800c41102e9085803141c00d091590700e4800c075036190b00d40100300c0040c0c60a00142202001990041c88003460a2402400c9910010b21491222202103000180c40d13a114444d03015043d003501c813002c040d440f00d010482c2440303210720446820041c500203200b000030b072a81c441c00d11101e90030710820040c0b890703080c00c0d400d80e4800c0e2035040d40002341c0c0740140000c2148005480c011840b0707090010f030729201101804e041001094445d000304201285114005800010040c0d00410000030b5080c4c1d24046100401c850023140005450300740c1c2d5207551071101e8122000c540c40b29070312204480c801c0326090002c0e81e84520b0350140042404072259607010034203104030088418030341c0d1005008180d44842d0310030290540103040c0d0503580d1415071070004c0010b4030030042016101d00d949842c2d0507410400149068004120300900f45000240300002082d44440031980003d421100030b000c41d200d1784e9080359118104403020400c0390380019003144000041c00303c8210814a0002404003510710 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 940312769 1250 940311519 940311551
    0x702030d060e15220504060f0c050a080a09170c060403020f030414060d090b0f040309050111100b010e061216030905060c1e0a03051b0405010f1112130603 68
    0x6448003c4200d071801521051450820102000340302c01c1c80303103c41992150340c00c41e01980d10a1b2030503201c0c00da0719080d00507e1520f50152820120890402c0d92801103a01c2008207141c0005110004e12680e40c10f0000800c11068880c1840c1c2d602201e0490710350305076081207a21107005580031000341c440c0b44042400000040192000c83d04c55041d0070030070100342c100344070007648a19216481c1c40d96440da12400074202c882445d015003003d44400c0c600785458540580a81c1c034541001e814040d51542c0c2c82581100001d508850450031000030410340403a0700180c683c80210850340e980004086120020312a40c003c0e00e80c8102c8280701c181d450342880000a07000c8440075a40a41180c001500003480111280010304850a100b50f600c05083e000524503400d9030842035022000039180e5041c0032320804080c0c41c3c1c5c0704848000c41014941882c14002a00c50b98040c4201018402400c00c045110041440303002080c901842a90faa80c0f001d007a500207500c480d500408010a140c200e800840500c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 940314019 1250 940312769 940312771
    0x809071212112b0839130f030309060302070f060209220e1b061b0c06040f03030e1207061b21121116050f101a0405060904032001050702030d060e 64
    0x100d001c42444146066500170241d0fa4246201e003403024040080e10590110f1901031801415030000c09403d40303045203002421003110b9401031040600500a407000304906038109011541d0010006a8802d101c40104201b580d10540400025000340c4002da440341c07542e08a03810303030360b0044207460070079883c48042c1442d82d034400320703268000800388650700c1201c0c8070000b9045040b0644d02110058001d10b400100e00c0d5105802c200002c2a1202040042582002840c014004111a0030203410408601c0c90399611852007030000700207803010b1a01030602d0310349030b05140e580c12220140712401500e0b03500701510011100d0304001000b0384269440b00080c0e1041c030030100c6001d80b0841c43c0c5503003400074004200c0d224200342c2d06400745e011391100001003000710300c240c000ba01d80c5c046601541140484e01103d5800741d01c50141f801e09013006000d542d1050f021f82d0099060510303809881500c0c0300c0d0400200c455070081003541ca480180082c0741d07000000f4100c031010f0813a003032000c107031903076900156520 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 940315269 1250 940314019 940314061
    0x608090114040f030c0c030f0f061d2a06071b060f09030f0c0b0307110105070203070b0105040207060615030e060a020a300c0809071212112b08 63
    0x108110f850300020744a00074280c1c1c03440c010520318614a486c1d448141d21001c01000888003500c0540d50741d0100b2015020302d20791055030380801c1c10052811900e03aa03d4003058002001130909000c408030706025160b0405021b103601529103525014246030030382045d0a00d45084c566a0200b41d00086c0e954442d43d2290ad821003180d403100c1b40c551440d85c40004000100c001219204040b1401041007078010016510440c4280d59801d1103800d903140b03917400c55001814450854004002e2580403a0843c01c566044410aa0340183d4174001410310000400036038201c24120200d0500342c804280e815008010422080401e07286c0d1601d40080c003c0c101d22564540e0b0011816082d003c01d0040c802c80c0066948006040814222186a010741001c40d2113810f01e2801141040040c0072401d4000c200b40d5001d800d06403403001e070f105015200c2021341d42021b1a107108020140000281101045c41000d1040705103a14020303451030b50b00703407400310688802200d4000501d81d000041001e001c074104105409 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 940316519 1250 940315269 940315283
    0x120100207021c03050f0d11210903040f29040e0a23130303091b0611030c071703070501051302092503020d060503070e04170301050303030a0f15060809011404 70
    0xc0708034904648950070142050404030768580c0f40010300e41c120f1006107504818400381404003501c144000c0e03049c0802620781007940c0e001780024803810340180020740035903401a0807081034080a9041d0400c1080b201a4404003a030045400139030220f1004141d4003400740ca24090001030034040c003841d2204075420141200c01018000b00b0076001d00311013640f254601929000c9440c0c8103c0c0c07140720001d00c64880340c80074030100c1d6004100041d849440071441c4005a40a18500286418050f90f110901e0281d40d10148240c7d01a103d050420800c4a1209078403100030710040c42e0211440e451304200000aa000e100f06c2c00c0007984070140034802880c0c01c1c051140e8180e5107400c07c6011802500712076404020340750707220004601c654003000740303100400120180c50040d02d01072400381d40001e501c15000132001001d02c011300c195a004425254010040305000552200881c1c02401a1403460486000d80d20340c00000b0902c940c0c072004130380c03151030790200900c004100b03290190114402200c02806803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 940317769 1250 940316519 940316527
    0x3060203040515090c15070605040c050109140d060b010216030606060906020a0c090b210607030c170402090a0f15030c1a030c130b0c0c19030503090120100207021c0305 74
    0x1e1605031007494040d032509400501f0718101e6a140d404072841030700c042e10b0200062004025a6920400d00000780907041d030f800508060705d0011070304030b8060417401421152140c00c0520181d1080151180a040410f0702040b01592814260000d103694000c86000170305403800466840c0c00021903020341d0394840070035a0464034081100b801040441c51040e402703643c00040303081c54400d441d580010501d0090240c800c40c00e0819001d0201c811000a003414448800000040900680500c0d51f0064068455125680d954140e49000340291541c0c2040c45140504030b5601a0082d01d05c2003d4a1142103105200d503250015003502c24500c4100c4c04505804000180140c8010000362024554501c3c0da00c028540342c2c03440fa00103801680680e592940900c0380d002c59880d01503050103021075090504907126045403683c40d2a4071828580e42e0502c201e444001841d40411418051040605000d913030f0900015451080a03512125081e4400c1d075100d035419100d14400c0d018285034aa141c0c0700ca0b854 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 940319019 1250 940317769 940317793
    0x8030703151511120c06090c09010e0a0902180412080901052205011d030a08010b03010e010b090f100e03060a0b0a03030c0503090402120a0f0912030b03010b06040306020304051509 79
    0x2403e040a420079007140100305042280804e40c0010f0b141d110001405402d0714600501c5040c58a8213400643d0310030a844030042106089107110507402403000040840d40d200343c2e0020541c0900e0b004240701b00c280b4501d040005110b082e500c00440601d07941d50b080700545401e1441401e031207083d0758190b00f45540350040380892410b9100b46d28441c0c40f580001c103100441c0044d170009803c0707145804507560400a18072880715402607000740940214419541994140514181d01c1c0a0500803a40e01590010b5865030310f65a0021b00000c80c170005054440c8811041d0004140c0500300352114024400c42000c10842c800c24010815200e0010300124065840c648041341d01400200c803d4a0030f020410081c1c0b034940b118001132641c88014000303595241003100040c401ca5202951511565240802640000e501111081100390035440c2c040350342407803e00004d00404410304040d40c000b83c009030000c00c02c141c903000707075204074021010307510aa4090060320384000021500003055070419411b800e5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 940320269 1250 940319019 940319027
    0x12120e1801061116080c030706030603030c02040b010e10030f15030f11011e02010504020a080105060f091005030f010c0e0904120c11090403120b1005030a0903110a080307031515 78
    0x511440d541c01215440310b0200c0424400030007640000c01641c01a581b4220241800c0003850b008050b2403800300400c92454500500712406480001e104503103d40c050407240e0311840e88261280d00080900404100540c0003500900c00b01c14800d000c282400f200c002c040120b200d0480880390081d4840758030705004e40d218541502c00d20726413414801800d1540b0f001091115a80c01440390a4000113124101401080203c18882e4840c25107603040030100595511000342c041c08444060f90320200c180c880c90503100032b51400340c100325050f210f00c00142d0054041508a441c24000d191501c1c2c2004100350300b0700009142c00c80300075140054030502640e003503108400e007801d203500818110311646000c00006565160079941940025800c00c50090420460311901d0650031040ba01e428041c42201000380203408000d0002c0b203410340d80c0d842c01c410b01d40648500505c0d10010401e40d00450068a06000590419a00000060300c1c0541d001c0005000d02103440a5564620611480110f00c40f4119 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 940321519 1250 940320269 940320287
    0x10090201202113090c021204211e0303022706030106050315040c081006051806160606030f0b090a08091e060d06090b0d0c030b090712120e180106 64
    0x40c0d07020b1010020b11480e0b00b01040e00e40d0241444500100318480001c02c004d2515546003002070850600300320820040410b964040e182c40004280c60100c406070f414034a440304020300310310b00700c8480101a0020158503a000740181c1d0780800302078450100b0f080000c014092042c01058200c203081005108584c0148040d40e07200013890021240501c0400200d0151884810140e000c0741032402400001c480a49a007000b5002600e0140c1c10032694544d039620598821a05a0080a002036044403091040546170440d940100d024004aa40c034603188040a8114000341c4448a140c40429001840030a134204200d801c0f01c00c55042101c51420001c03a01c000c40300221030304201882a06a43e2030b243c0123040c0107041c11100282152500b07006da401e40304c03070844262144509150110020341d20324038560130349800c60340b00303c07541d0b80c1c110105103411040d400c8079004240b0f0180b03807001c10890003800700c03d80e1880d030745560346245131900303001140e01410681c03501c1050f180014407015110f08600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 940322769 1250 940321519 940321573
    0x5160e090a150315140403020601050f0a080d0521010e0417070605161101060305033c090f0402120406020f09090a061d0c041a04081009020120 63
    0x504506401880300c1c02c00c02c56204458080880500c8204951540b0035030b04c011001d0f120810042c42c2c03c2d603000b503c40c0c1c0140030301d40c8501c44440750340015842c0c4010100142030b0b00c1003210b5140405000241c0541c11442e01803101c01030103101c00c038960143c50301c0c490484414645a411079180c41c0e90702c41e03180099844c540c4141e5401c0c442c80010030458000d00f4015001d4940c07108030b40225210052403001c01c032146500b1030303040a4041001410000440300c0504026042030070f0f001c08a07031300083c01040000d0242c1740300aa0613014450b0348241d0020410410f003280e544a220028000340f105a00410f15030b4008540ca200000e404245140c00400d15a180186264a00300b4001c001480c0410f0075100041c0303103a034541003840310151600b80d41c03514003109011000c591800d407214000d544590b0164001503140704020700d4040454100342d50207400e03d0b40c16a140d00902010703440081114090a0380080d90080e94002c0003071011000f110607140c01c0d1b0140c000c44081c00c215020316001ca503c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 940324019 1250 940322769 940322771
    0x305151306090c0315200304050a020d052d1b060c030721050702060f092707080c0901050405040b060d02040e01060201060504020a2a05010e0c030105160e090a 70
    0x4594005001880740401075482000056101815428004002c0f10360700182c0e9100c2c0d286c4050b82032114088515011a145d0600c0c0c0d4982e039a480d032500354100040080300a40100344c00c4503e8007040404a14240b40150090100c210741c07004520111102d20000c3c0c100200790000c0c11a000b40384480a41180b0340c241c0074100074500810303003050920319840b541d000c1d2042441218016946100d1501c09c8500841902e4a50304103500f80d00001c4d05440b40042441110000140705002a00c440e020540d03403c80646130703201c8000d05c0ca40e11400c6401c0885907200000c40e03140c0042d071415070f0030054a40b030f00010781d0340700c2c205070030f00040c04000c0400c1c60450743d12581c01c1c001204045543c0c002000238246101c4001050b501d07041c0081d0942c0c40c1600410700c29801030040400c44c0da07020020020700d00407417401d212404a40da4107201d42d030b003100340301400365428800100c00980d80080e16441282c0258000c0010350b444003801000c60080e02d079214002101c10151194514140d98880e0b00a400010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 940325269 1250 940324019 940324051
    0x15011401020115140f04090210110f03030c090117070806130e0102070f0201140a050304060f020c0a0605011d041203113f06100530100f030515 63
    0x601ca609841c481c1e101c40204007040d903480d0b01a007454517054548a006607018040c410407030740054071240c04602c4880030404510f03400100c20302e040010b01e81d14108601542c3c0d59003007030900d4106030b0380030300c105e64007040c96120b0000c4600d90b595111403060440e0f90f00e03c2042e0b00c41c4410081a884c0410582580c0b83e01c6c0c4941d110000b00c2031000b09249031044000ca0762821852002501c120740001030141e080109220325140c0031340003030440e54403d40c0300800080c0424010340c0c4500030f010340e0340d440d0360718460642810204000b551199058079030054020102c90b8215010202e482c000310f1300200401c04000502c95000e00a802204241c0b1286003040d042a0045030125805036080001c6682140850b40c01841041c00001000848640c00385000e20381ca0120301040409481d20400c0b006c0290000c1c103010480140c1124414500400d6200366245d6504504803c0c01a025500461205c0351076000040c003003c0e20003031400302e03075028000d04244e44000745e48002d603500003030644a403030705016 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 940326519 1250 940325269 940325291
    0x1012020a030e1b010f0528030f15030209010902040303270b0a030c180321121a030c0301140403030c120f0e010c020f030409050c04050306010807031103150114010201 73
    0x120002403d140400070390704800c0d400c0c0000402080c55480c01409100b001c10961680c1c00700c1840310408402000c07422a0038408550f42100245558080e240003940303445803102c5030640072150302c0107c078001c4804d040d1513600c80f8140c0d003c910640c40003e0110b0f004000c404027400e10220004a00c00001510480c41690340030340c2e0103280e01c00407601d00042c0d0b40c0c412001c41c4640098424086151000c140d80c4c2460031555a1001809144200c88650070440000c1007154401d20107419840f4040c0c900780004004484000040300c14120311030f00c64000c010071a00d4601701442140d404001c18900141c1d15151914160020043c016075081001502091108110120301900720940d540780c1000a921840c60546401c454644042000b103400010a19046010000c150b40690350521030004240c0c03528a1203031346230700c80d6030301490b050701a10000040c1500003003407140489010703030307900d00c082c0d0241810580c0750100090002a0802854010300c84100c20001913440000e0600000504200c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 940327769 1250 940326519 940326523
    0xd20150a020f0318064804090b0f10051c020909040b150a0302090a020d0902030109060e070e010f0314100e0f0c0d05031e040b070506151012020a030e 66
    0x4540403480f41d551115484c0300300301e040240e0f0f40d01400204040c000d1095226091109484518100c00c9102d008410070340b071224031105202c0c0c40041ca6000c2c695039650b84189401404803460740300d1080c040001d55800d181024066090b040c801c643e80c0b1841c200d100d000040300c90306605821403c29a0078050144291120307e8054011030007644400054649030b00c2420000308035800f028095010108104010303100c4000a507040f44e400440961140580500b075001000c003050007940c55801c09403000240300d40e0781d00c00c02c6d0801000065a41032034440c1161a0300701828861890400b989000400102e50b50504001056958034141d92810143d050320a081d01c0006031001001e401c4405d16014a00007040000f9441000750303a0040120255154a610703401201010603100404074684c0c09600c0c101c1049401401d16540340940700c0da2941030090b0b84110031034650403403e03640c050003040d03443c000100300c503010180d175903042440b42c0030002c81002c0e402c600342e14020b06480e001c00c80700055003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 940329019 1250 940327769 940327771
    0xf010c02070515071b0905010e06040c020a0b06040b091006080105030703051c030b041e05161b050a15020406020c04060b0a030914120c01050709120f0507170d20150a020f03 76
    0x3e06c031000c40d01e035060074040c0030300c40c5015200600c01ea10344011400b1540c0c01083d0b03803002c0c80d00610180d0040e070f54034002c2805030502e652403030b500100702e0302003213114841c41c0780020a545403503940112581c2c850050696804880c04080d1007070340301607140700703101c034004070b0005084d1b1440c0b401140400c07803100801d007503a0707061521151861103950750380120400c03842031581c031000d0107544450045440d180941100304e8840103914840440b6801014000f04101c0c4d15140c561150062a040c410840404006c0d0054094a80140103d41352040307149058050355043c6e490b0356214610b04004600b050700188100182141d000d011200c0c01d4071106401d21840e207048180030321b001c1c0d070b44d0049841c441c01c4650040001050180d902d81c140110031426106080f400d47c814400c000d00c0c80310703040443c0f81451a90001c0c0000410310015046044040b4407441c0300c03045611910526505013100d9660005000752a01c040d90180b01941d0940016840e0a5003141c205000107241042e40d4410b0f460543c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 940330269 1250 940329019 940329029
    0x60703030207050d02071a0f040305120408070b19032c161a041203050c0118030f09180b0f15030402090a14060111010209090106020f010c02070515071b 67
    0x6808180c2d001445020310100b6030350200351020b04550b60a000c40c4804070030321030311103241c0c06a011620724445541c00046902654108048900c4000e0742d0380c1c0c0c584203506c14054111070340141e460004014450409451071051410718507140e43d01904000c50080495890b00c440c14205007801b51310b10100341130b12000340b400503c043c01d00d5860120078200320b010075600c00242a00c400705200303090802c1c001507400361118a03e1b8481c4a05e80c900302100c05008001d690342c10742d440c01402e400d42d80c51510340392650350b1003500c4a9110340c2c1d03100e109803044812403141c112510300b108410304200303402d540408005d0400411a000c0400c500e8086845041c851030950140d210000a20041d490040011503100f846841e0a010100114400c0741c1c440c0c40241801d0306208000041d000940000c1d01034404500c0d000e0019100741da5034000c025501c02003172030350310419480c20034002c0f903091021039100d040c1d43c2d000d0700d0451000e50103442449290311151080e40c0c03044000e14104d030554501088200281 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 940331519 1250 940330269 940330271
    0xa020d03081e06030709020f0708190915080a150803070606080c0a06210b120606093405130602030301050406060807081f05041d060106030917030a0b06070303 70
    0x11400c003201c806018078402c8048164410b1400704545580c0c002601c00030344900c0e8801584480081d0a000f40600811070000d010740030104006401c41d40d0008110314454180d6915548130742c1d5019494890102e0741d415100054001002071150003ca40111f114410441680094140d94030851421600400c0e01250781e287c4441d000c000c080403c014407036482104a40c0542c0c40c515007000070300042c060075200300c82441d100c0c003441d0400c01c01d940f140620141c0900501d0400780c0400b461503c40104650151041558402141d9094190111004041c188050745000070051044000b42a80e001c4644002c1150030040c0484641d03400071044000c14103a0025034882d4180750410003902c826420450400403504100a8800da110707501c1d0380c210121600c03e031018100c104448009002581129401a00f848a110b42182200745440302c0301e0103110581d80e050340ca5040440580c1c0f00754801500d05c08c09d280c3c1d540d144100c1e0b10700840c1c00400b00c070b41c00113282004002003581508070300000d03000f00f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 940332769 1250 940331519 940331521
    0x110616061e11090a1d0a05130804140a1a04030f14070e07090e1e040312180201260606160b0403050301090e01060b03010b180a03080919060f030e0a020d0308 69
    0x90304280c0c0403000135011001ca103410246154218081401d0700410746d02d645030311a0301240802c01894491075201c0c1d080304003159101c0e2141c03614900c034450400c0c00b6001d248240000030302070b103002d1000a41d180c0c9441c50b0a184c030f8035603202d04604924114080d202c1e084e110352a900902e404010f180d008002114402903946031400011b4107c00b120f50044000060080801c102c0ca00001c18141090345910717090340064803a03060407555104441d0386807011519020001017490350724440c01e41890b200b40c1c0c941882240820180c990250b907a40803450141401c0042442c52a191380641455031070314100c1400c00d6000c1d1903039134038244180e4080d40030440c0040107005801e11070092400000d0004000d200300784c44e00e1440112484144104001d200010450b1040403992144200c0d520b44020f000120003a141d0600e040e0550262460611a446000d800c50f20301003081e8a0784c040380c0242d02d902900001c400e90603005428004044219405100e40c2600181d81d80c0c6624410346000790350fa4021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 940334019 1250 940332769 940332787
    0xa0905130905120322111203030912120a0207080705031903050903160213330807030506150d140d030e010612141216110616061e11 58
    0x108003c1c0003811140b000c041080140954100d0980c41c000580c4005042c1d40c4582410001103a51804042c25409680d1200032020740c40c1c000013440c0a01610783c251544101810303155825881600407034818821201c0004043d100340368064200e0a0168507000e180450075590b80d0b066501c5024440425140c04040180b0f096140c40b490343e000302c0300030046180840078415a102c4110700c0e003009215903002c052000d141c590f15041021400080300c6104020303c2c4403100140c88400042c0e00390703010000c103a400100140001005811241c00c10040e00c0d041d281e89940000094000314030540042e45900080700140200390301d03200304900040a0203140c3e201034401800e0b40c441817541c040580c182101888440c01a002c0b40048661041803c1d14111541480780c3c00c000740403240004020010071140c40c1106003c0c1444600307482107502401009607031040020b0780c00f41e00801805901e408c0d071600005000b95009001c02040e0b4540d0001411a11100b801030743d40d04900ca040001c03010030303a902 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 940335269 1250 940334019 940334023
    0x60503030d090501060b030c0909091e0606190b0409090f0b070206151e01050d15030507080d02210a0e030304061805040501080d2703060c0f02070f06050a0905130905 73
    0x1d00070b056410f0303147d400c00b104040c14502500224030321903030a600128462420400c01e0707a001190a8040040c0210344407007090300e64108481e83d5010300740c2031110314062004806000207590f101d007209410107080007584001001d291108959a00d000ca0307669020a01c003d000720300c120582c3d4010a02443c3c502c80c0154a0810310701d08900641102c52108068408005c3d620545d8100780b92244d201d10b001075048010f0005052006a400600800441400b1003c1888400e581034182140d21845819504071307610800c10348c00740700032400d02c2c01085003c03240340010400c01107d440c00859014040d0300003411940203034890404a881d0001700c00188204407920402060704a804108541c90040c0345078884810f841c0c84001c02035203005c01e008200c400030301c460740c14070000702c115015130b00c92070200010f010f0b41503818085030b080303400400b40600c00185079007039400b2800000885071820b0000d9415801c460300001c148003504001045076180e1500c03c405544c00150041031070281820628 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 940336519 1250 940335269 940335281
    0x19050a06050f01140d020604051302040308030403260603060115030e060702010b01120504080724110315030118020909030f07080909010806100302100507080c060406111204080c01060503030d090501 87
    0x703020385c50243c48100540d42c0c4800f910308841d41603602503489501c0d04d58000081c440da410040c01004040184014980d1024840d00100040207074020206940c28107040340850489015503d80d0103100180003180d07c192180c100a0300d10302340840c0c1c0b1655101c2c40ca041010451b403c00060b950b92a007039019603444254540040c1107803d00708800c1c101032301d54040328820400c3c0035041c61006240b030300d0380940556a000302e4409200041045003003140030307142c2c1640241d42a100d0b0050740380c072003a01031a042c800c900070584035014048810764664240030508000410303c0300103000c01c1c080f105134940c01030300a00300300d4410030751195118110002c210200b403041c1c01c0322040d0740c0035004001d9030f0350990510500ba80e4040b80c507480e000e00711003401c641d9446441e000414801000c507401c405c9900010310240240c2c455802803080c0c900d071405039152800f84015a00c11079440c40089000704920600614041c401140080340060703d400110b0315691202d04010b2503140d5032600501404000c2c8200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 940337769 1250 940336519 940336559
    0x60d020703210e0312060a0f030807030810061d040e1204030c140303031305011b0e0f01030b010e040b0a030f1a010515070201110c0a090c0e0f010219050a06050f01 72
    0xc2040040040c03c1590740e00982a08810b0085540b001c214560b594540c2c800041110303140040803691a0b103017803132843e084400f04502044c03450010866259400c41d01009441b0180d4440309450246100b880700074140c445055041740d40d0300400c0300c401c4424051054801d590b4440c0303030380d614651b2406030400340459003e1144170118178a03544aa903000300c11603070041c012101c0902d8800309030a041e801040c02d88d40e001c42e268034090b002000c0ca85c000c8640c1e200041c0440d1036404410b1070034010b500350b443e000c82d070900103120249400f6182c41c003075200644808001e07003252030b00c2e501e9545c0c004103600650400c3d201c40d28144881c12024036400300a1380986002d0b07401451003408d2030301c40402030180e0710001307040c42200102e034000d0140070052103400c1d510041681c0d020b21b83d200c0008006080d0249030a0000d45103030000d103003a003440c0ca2240e02d20f40d01a07004205c07510350942c03203041f0050345035011203036070040c2e851800108205001da24000e00804200619335407500e0100c1607050b01d010340c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 940339019 1250 940337769 940337771
    0x51206011d07020f030d05040210080403020d03090c0312020f0f010b13020d022a071e09020a140a0e0108180604060e120706060905011a0a0509060d02070321 69
    0x5100340381c40414000400800466074280580315660306138202080c00000450a10010412901d5005030750007076401035000707488000d6044206c00084454000484015000d079102d8500310b03500f0351003640709004a5000b5011030610fa030b125038071010300e100064221001684040200d01400d0340500c900c81340c05c00e04800030483c1044100125150701d03003e1685100840c0e02141d0b4088030021781c0c0458102107203012070400480018286031101103a904106911407099000c04101250444803201c021a9402c01c41e02003145411501c5c006944016010801c20413842d6402804200d02805407000c089540c403080e2405940034001400700e8001400740420140364504003200950119101e9001500700402040000302814190302e00401c252000060500c0010340109001580c4d02c01800e60b00402d00130f01159903200b10f800c802464059036020b56590401a018149000c0c400a0013030040c042e28042c1400c0c000c9840000700e810001003500482d0300c0c42400030074250610180404034000c414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 940340269 1250 940339019 940339021
    0xa0f090b060309070e2e08011a090408090627091006050711120a1a090604020612060a0905180c04050c0a0804140618070f12030c2a051206 61
    0x9100c1c0d0364010030301c0fa1142070210f600208628061b540068030104485c0c200c00c020102510349146d40383c181c00d01c5000038035461b0406c100e03d0411284d1810b46d4041d001805009103484613140c07031007658040d52080e64088000c06c061b080d800c22000d064001c0310340c0b1186144800d1200d0090260940000380103d1400b280ca00f0140300d26a00601900d01d6a134020404005207820342021800c180300103134503180c180c864181c3c5c003030810001c3c000400141015182044082e100e04030801d40d5404103170380c02923000e8414000140d004a904039030541c0701ca401800240c2007a40d403e0817504032103003a80d001d24000226210150315000411110380b11000035941005a443c1c400300c038503068020780d20114100100c0382c02040034000c4026000c08131544100940b8002c0c1001c2c40c012007040001541401e190044410015213481d0000c091004c82c0e800b4070a19281002c03690b4200e690314107102080b200d002c02000512441910129200614684044071001c16030070281005900390813024180f04a0b03200394 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 940341519 1250 940340269 940340281
    0x90c0b0403060c0338040626010b0a0b07030909091505090706090b0711031c020d02060106080a021c111305150a0c050f01050f10050105030403021c0309020a0f090b0603 74
    0x805e95000d401000b000385410360702c0120300d1054a442030496a0302c213080c010b0100b414040d0803a113240c0000c008181e0b4040c007001201450176220719981c1c20364080308480c0100020700644004045aa00c42d24105040300e4a48512904956260b54296100c2011400c42d2254401510075550040240d000404403285850b40003004458580107016030050040364003c200200104445180103008065504c01d10840054074241200e603440400184070b8018510915400412950f06903041995404d00703581d03810301040c020f507000b040d02070b5529081082c040001901d9204210908a1a0890a0340ca81e0900c40041c10800580c100700c1c46054216807912801c10b00008485d022012400c0c076000c12001c03401c000b8100b5601d10810300442d401c0a08218044044483c02c41c880d440e0801c800b0400c80d155001124580803c1b500100583d0284052035144a40031000d50a015250314000c90880c2450780401c850070329076804103a59187c0803500f44038282d038034020004a0541a039046040d440c1031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 940342769 1250 940341519 940341551
    0x70f110703060c110102030c030624090f30070611070e07090f0e0103030206150112051504020c0c0a24030c0302040e0115020c01080610080a090c0b0403060c03 70
    0x41e100003065030b992503000b0042c0a016011109460704400c0086440b403030018002501c60f03004594143c03003007460407070440c000001c0d401c4000d80c01030b01d210800d0804d2a40d1050100181e28603a5a641c081c0046c100c0b80501c80d40c00c000b84240e0403010a82c04000c1c08020803e80c901965a0400d03014402a6070748440d00c0b4030006518404c80b00ca1489030241ba885258064641003903d410007040d904039410003103180310b0945602e604903442a030854400b541d84ca001b40c070121030b0710400c060000d03c1d42001c4203620b0041e0b400c00380d002000d14081030100d5450138002001c990010503598510740008103405100e250042d21100201400d1102081240f800315000020141c5c00408400781a520b00007100040d202c0ea0541c2c0c003420103a0f0902c00c003549c495010040000c1d44082c508018481c00c41c10310362651094010074081c1901400e1100404100c03201a9850708006014412a5503141c0314480424500e003a070000806481c2d0501da9a2411401d000702502c00b50b40c0003030181800c11803082580030748 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 940344019 1250 940342769 940342783
    0x1b01021206040c0f440709060c0f050106151805030c030d120b03070f030b1806190219030c0f180e0405010e0a06150e090c01031512050303070f11 64
    0x340c0c0341003244aa003c90801000c4c0e40c110016108a00b000c0c9050121746000a040010722041e00400780055540c9460440381d91400c0e0140c00c00041e0a0b5400a0000b60240502240c284c42900003241141e256421a801403400190220020306a0070010b10304290101d007001c0a020309502406170320065002003079580c03500588400030080104548607802c1002d610907424a50700805990680e81d603001ca1003100c52050106940d1051000040f5805201001c2c65041c1708910070081e10159451740e440d03d60b100e030550104410560200111a0f41d0201d000c26a40c01c1c0310300351000510030301940d00090906000c1d0f281c09050081008140c0c80140400f8080d0f8202c4082d0440740b02d05603243d2825501400d0291504286482858224020890710b50062841403484100c940c908a44c0d8446208044034156522802d81e004100c540300254030a4110340f01d182d02ca03403605050b103507990b41d0044a1450b1030600313452581022080c480c1440d0700c48203000381c1ca082c0340741110002500704c2c90341d601c03160 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 940345269 1250 940344019 940344047
    0x6030608030933030a050f060a09020a090911040609080f031210150f02122704140c0a12020403020f010f2c040e0303010e0c0f1b01021206040c 63
    0x121401d03e140c0c0e6034250008115003e9484100141500c0241c08400e46907003003600d0325030305a4107240004202111946109108510040c1403103589440c01640700000c0d8808580202002809100401c5000d07150003102c0410659010041d07655142100050142007960403000d41504401000c000d407220010646641012010070500707607485110580404072a1070b404080020748940c0707071a0704c182e0031000c849a0700980b0b4003a105c0300c5000d1200600d40c0c0c070424181c900d484903034001e0030034200c21070140e4018506000e4400107000c0341156200d1a0000e0440d00d04152110018001c81000d80c413101c02e070886030842000758206410341d070000304500940c0c8402030401c50304403d01300768a1b211b490807030703401070001c0090381410640c0504900d150740090031041c01141440094001c2140c0001181d040310b403051600042c58540f00c5903a0303810740c4440044071004030700b444240800105180c4210702c0300030200005a40c3c0e5880114034807603420042c040782c0309902d00700c0490401c680100c00695101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 940346519 1250 940345269 940345279
    0x5041b051803031b0c03070602160614092d0616081c0e0f0f030307090b07110a06030204051f09050105070f0b0c040618051e1225060306080309 63
    0x24141e00800d165001c4c8040e501c10000d001c0040406910010410540d000405d07010f0741c1c607954076003500b0381c0e0301c0401c0c00f0026846001440d04004892180040c9424124030208031031030603c0110018010707062403100c10b0b00000300d0594400c07007400002603107000120117913181400c10f40d5074164118100c0d44c030341e03015120400009030b0b0040244514080d50b41c0320b900303410401c94501e079404c08a941e03000908000c2101d10414414818040340003040e80d01c140c0d501d1769101034a45c204040b881440e00410001c82e1a01110f600d0000c6555900d401140a800c103654010f889524003010005542c4021480f900a94001c025182c00c4030741c0845898103a400038280709586418900e400304540e80002405002c104ca0740e818001420a86802001158950340c1c4034042000700c81515400d808451080300c3e4021404040c800611458103003080391500f00409680d0380020410100d1705006059240d0510750908049614408600110340c201600d864034041095074200005180e6078410700c05018840c8c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 940347769 1250 940346519 940346557
    0x71203050313060501090b2803060b030708060f1902180915040f0219021c2001020c010608070b040b120a0b0d060f0c170a0e011b0905041b05 62
    0x2288080c0d2000c00c103143c0c0594108411340e5a80c07103507002410a42c060a20458481032002c1411100d12244000070b560a01c0b1151507a00d195101001800000c4400ea098040c0402c00503070f00000713022261150301c101e103488916207481c80c401c030300302c03140041d0442480d4070501c04400c244200201c00c0604031015649250242c460121760042e2024004150780d000d0f00340401c0c4002003c0c550040d03c5070180c44c8800407504641c16009076211032841c021b5503c0400e0415440702103174030904450030300c0c1c185000301e101d42c0010290000d00f607900c0f028248a8a82d1110300401c01c1301b100b0095140145202c070182ca06150038135692075060711032070300d02c800049001030102c4d01060041e4000800218000c0103241404154905800035100d041c400144c21840d210050700f015003d85940602e4081c0c6030107109c0070355680c000620060030614401c030744039966020112058818501604001000c68490180700362410040000751203100d40a104122100c559582c00f80c1e4202c1c09440c0e014000344054041c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 940349019 1250 940347769 940347781
    0x2210d0e0f030a110c0103050f280617070b030903121803120a140402090105011206030507060e0a0b0909060d0f060c050702030d080c03160c0c08070807080712030503 73
    0x9004103901515080380000106003211070780001324980341d0201d00d003e0781c0f07000f0007403001541290b0701100c482e4041120000054410a01500e00d4000304440d041d0461600b02500840c0c4200d074001d0308071700704c00340442c4040c0c0010350302082007800a1240480c05d6145151501c0300e1500c80c00384020001c03011280c40c01088814148112601c4e90052840c201c1c0c0c0c940004900024001c5019030390003a00c0ca1500c141da110910035509014030650700a40051030070f0341f0344401110003031640b0056203c456030300e07040800041d505214190042c0401d03502e00d26100d103c0002c00200d16030613070000f0024141084203082c03540b914421240c1c05082140c00c44c2d101401801c1050b0068204d40f0014080c40c500150031032107a4220014106e1140290100c40400508080039169180f0981e41c5001c00e04090000603c05010503003a4115a00340e8600b10901241554440d034111446070003044140e00810320902c41c0700001c0124400a0881c10020403d4504c0d054201340300000088015040100c008000740e8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 940350269 1250 940349019 940349023
    0xc0a330e0c0d0221070305031315090b121f08100b09160e1f020601060e030109030806060d060b040321020d0f05070809090907170109030e040506031c030c02210d0e 72
    0x10361f007000649503100d19084108c46561564002e00741a0015000c20401843c400e202c44800c2c3c85603590041d262801c908240d0341d10031001042600c241504941c2c103d10744181e01c0080c1c000308010f01c020194107422001102c10b0b1550b14051074051412001086080c2c0e803032400341d4004070010b05102c5c5140d40d4410201d20803030803145d0150f142298811030000540d40c00503106048411565500d80c03400211020503081e6030300807002900168042c0040703411850300c0001400140202100020415640c40103112103802581c010703510310319102c44900e1241101c80c0781815001080c400782040c00d001020180c1002141000a0100400824017104000640045800704200102103c20501e080300c0500d0b9515507502a080710703540007941c0c02d0307040d04050044c0701544e540f51301c0d0121101181001e004c02480020f240c1036041c030072250203080c0e00a0312580d006480c1050303a80855080c1c1400e40103403800c2554030040ca02e1b0004405103030011440300c0142c4841400700c0402003000c45060851034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 940351519 1250 940350269 940350283
    0xc05420906130302031603030e1203130b040314060f0703021303020901081c0201050907060e03070e13060c0507200415080a0501110c0a330e0c0d0221 66
    0x250459030028030301c02c0c0c0030102008103040b01d00c2207080710382034003000d4404071111815100003400f16512100c80c0d0020b04d031555503000282200c00490b41040541890550b9440703059100d210314001c0041c003032040c452142829444812440b004081c1d40c140b003103018803020001400c405c205640881d20340e80b070148000c4036100940e0014154800b42d6180c0341c44944640031400000c00070f0f668000d41104090041c011540709080440182c00720918140c82a500c0d10142c01c4041e40c14091034101165030142c425820b03005208094103140000703091315201003254004070b1301009110040c0303c1040040c0c070020b07120480803400c062141d034000005000c24003038005031001c4584005480340100d0881c0c0300080314814180658028801d007a1100707443d0469205500311150341d030b0040351904d80410a0502c04140c206000b20f840b5100360b40c50303420840c41040c5079500b00b03689611102201d40391070b02049154103110049a500b6408000365002a601c15440581d4482008810b27400c80501c107002c0c0500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 940352769 1250 940351519 940351537
    0x3040c05040f0c0f0c030f110109080d021306230c0a0c0b030a06050a030206030606070c091506030f05251407110414040b1902040902070c0542 63
    0xd200ca415585042c802401d0004450703c00078000340c0030890058810345c14681415056140c84698a040c5801111000384c14003182c0010740d00e4807803040004050034001c012a1100c0d0000503241e040d4440c1c0415201074941c00001001450341030840091814500188251071510445a5400080e940c8a060055000000d084401c024400080d401c04400055100703070030380101001410307151401c00c1202241380c00007035000b000510015045051072002400c009015400c1e151807190b403000c11f00c041d00e801d14140020260f440408010040d0507008112002582450030b01c264500803008a045504880303014113007400700c0c40c12041541c0910401d2001012602815594880398100b400b5201d000d9040c6034007070f45c074000c140700e0400d0108001b17600950b400100c0d044240c070307003941044612a00070798034089968200000501c00000303100030810f0b2480761030201d8100785040100040482401c021942e031003100a1080010042015481003140e084480b289500030f00c244005a54042e130440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 940354019 1250 940352769 940352771
    0x70207090929010f080118060218030613060f0e100b060d1409070605190e19090c0e06090f01032f070605060303120114030a020306010603140903070b0103030503040c0504 75
    0x400042c20360090031903070603103038140d000740203d560f0344c103980d400c07600c04840740d0701c1e0080d01a04e44400030740b258001303110104103103801d48100301488001030b05103081590381020b000d0402540b00d0420000380201e59810050340401c0000c102c84000d01d6132a1000c0c4e400602000359280e00300091952040f00741c6a035642c0c1300314100300311031000b503200d41402420744410f2072900c198100010200e04c40c000300c85a08203080480444081b0078101622114881414543e1081038440d01c0350742840e0034059807008045054011941c114906400340402c00c00d01e44c1c0b940260002c1000500c607840b200d40c8942c0f180c0b400e181c0000e012800307040054900300c414408820303030710ba1042d08440a40611018044007402481c0402c0b81e92038010130556603210f405440d1030040503503c01000b015102c00b00601c42c004001d0165501640c890b0f0020341007000c241c00c8000840da6400d80503001002e01d0911f60b5105e041e910066280030410b49564040c904140300040c20000d001000404000482900500428002d04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 940355269 1250 940354019 940354073
    0x17130503030117150702120c03070b0408090f0102060615071a090d080c0405011e20060717091519090605061003021801080703140a0e150702070909 65
    0x4032a6a805030395200700f541c1d01c1041442c0070308a04c1c0c0c00d00a4010304081e001482988000030b50b1281d0358120101443c5240130030b00014021450b81600d0b00c1c8943d02c5064203a503640c60110070000e61400c00705400e81154004800c0050300c1c4c44241d907a002805030302c3c010a80b15038451400000640e124402c66540c0c0d0701400900841c1d140016948081c020a0345440740d0541d6007616103400f50045200301c2d030004a402110442c84198007881880b09600351400c4405092203509440902d8080034a0135540d501c82000c204503994800d18651140c18000041d421134105003042c25034615254415190040d901c001040c00844904840072490031402c00900c0820300c9402c0030b40007094200c44113801103080950814074a84a8402c5a40d509042c025400364805003400455507100001c00038000d0542da07400b2440310000c010040741c4180300f100804902941c0440c8224280020400f022510390400c07014058542c1c0c020403600262507594000240ea08810304142c1c0000d0302e604148004001a82 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 940356519 1250 940355269 940355279
    0x30e19020405130c03121112030c21100e060105040b0708030604061e140109080d0309020a0f18140c070b10050a0305030d11041203120e06091005060907171305030301 73
    0x30245030380200007034458040d07c0001000490320f55100d0b124684041d60308100150f6603000b0800034203030f0460786c070614004804412600100a2400b59142d43ca00c4c544c5250030880c048451107203c0c1d020b00b0a103403460030185001079803c3c1c1c40c040e80c0c1c0e00600c032040100009610361550752201000b0016401d4004079070890f00b54a540600700380c090004030806260365484154000c02c0440110b072a298001d02c0d104c6030058046004008a40080fa400142d010002518002c0f4081c03400180031001514881500740c1041841110780000c0001c03051043c1008100000070303840c003592071b1250040c4181405d03613030f58101520003441c2074202030390041c90102c01000b40080040a864031141a040400c101d050f404005c0c20103001d18420210400c50313034100c44c1c0003e4410003c0c410300302d81820717001c02c84940072407a1608080046640403440d9105602403c107020303980c09200e400040545100c0b40074205030000504989010b04070001d01d18601c40441d0520440002410901e500002940d440b5619a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 940357769 1250 940356519 940356533
    0x40b0f21190f11010806060412170a120509010b0904080706020d09060506010206070c080409020c07051509030d05040e04080906070203011a0f0a0b0301060804020604091b030e19020405130c03 84
    0x9070702603c40c044841449032042d401018400c0c080e00b402030075a0308041c50440c0c030f01071001c1c50082c12148205028020340155032a440544140301c01626005441403a0350100781c02c88800a240785180d038140400c0090f84d4070355500c3c5980183d0001455952468a410300001901c1401d070801d04181c0b034144d0030b2090011035400240104030903800d4550a4803105801c80350034480c0341000d40015810441000f0b820490f41c000c000168078803083d10001c0ea034840000780c021602e185481c0030310f140000c65000c285401c2c4100c5107070800c24204142040d0030325440b0400100000c000070941c01c5c000821494a94a001c140c88806034018000d201d00e002007424032140c1042400c040340120000142d03649940340442920065400304a219801c41c1c4c0303841400c9994503000ba1003640c11120800010442ea0018000d05103622040c00e8518199103191030010b0440700110307400c14a0f500030110341c9804a400303284103c88950125400328068031010008000005080c400819480c40000000100064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 940359019 1250 940357769 940357793
    0xd1403041b030b01180605030f060f0a140901060914162303100501030b040b09130c030c0305030406200a02040f0219031a060c0616050d020f09040b0f2119 68
    0x1445d201401883d5541c0141a56404455040500c541042c0000346400800500081c1d00c4508410701052443d2102d9404402032026280001e8594654000740541490341c029a5510090066000c0103403801840d0035450400c565801400c0100000c00d1003d650859140300751000380d580005941c0e420308660b622003121b07544c4155408a0304048208903076207482d120304e0710071404c0034003d03000942e110001003401002910081382c500704244408000b003107000c003c2d41c0255108030300a580da10b00300b040103030905040c1089a8180142c0724641d038404400880d10040141d415203010402d50182c002c00c80207030280350300e05146001c3c0152000c1a00d40d040d007062a00704000e11104030b40100c40000d2295500c01d4190307141440c1d0000c000300d88884201c00d40c0710410b68284c0b0380103003846460400c0005aa020001da41302e030510104011000b440c061245140043c81204e010041b400c8410124404030b10322203c038582d100f040c00c2501861002486040c951040d044001410324000f8079140b00702030b01e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 940360269 1250 940359019 940359059
    0xc0a090b01080108011107021215072604150203060a0308160c0f0b03011514070b0609060a03170d02040504060303020106180207020904020907030f0903020d020d1403041b030b01 78
    0x2c1000019a00006110300044c0c00324000030b543ca000000c4e002d002100c040792507842c64502c01d2141044117600c03c000c0c4070b07028040590307507c0c0e03d030b9400a000c2c1c02ca20000c18101c05001140d00140000166400c443d101c40100703501001d602ca54610001030074225056001070248140020307141c40d0180d0501004503100d01c00e81082c40003a0b1105903c01c00c0f080e09001d4450b00201c1000140314800044a010004d00e00c01d142001924401c1d4072481c0307042d00103c47c100d6000001f0030900c11240752075074001c0d0b4000c20a031003070801c0c40d10f15140c1001e00700c0c0c3e2007000031800717200280307082c40c42c00300f40c040750064500030f001402180d07541d1400034000c06440c0714644480300020340d02d081c3ca111500031240e00c0e5800811008041e140c580070410b5510001d415142407582d18040d580b018071040c040c0140f8503000c0c0c4c020300030210500030040c0c10480384000303000420440448040c40c00c0c1c81402a250810313044580a0325000c00b8071009082d09030250005000662203a0000a040d0b0005050143c628 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 940361519 1250 940360269 940360277
    0xa1407050a090905010f0b030402130e0a0c14091b040f03050c03010b010c0c05040b010509030a0b01060f0f0903080705010e100c0212040303023d090204050f04030c0803090c0a090b01 80
    0x240c0e032190003c048078001e019002c07209507505410402400c1c0703400510b4006000815883c03030410070221100072103d201c0409006900041d80700c506000c2e0107483e1600a0128207020400c110342440019240b0b07800038002c900c0c01c0443c010a540072440302080da0003804c03030301080c40001e940303d05201c3d0b510441e07009910b209609220402003c0c1d4440c4251102080d070003440d003500341c2d080c1000c0002511180f008070317040280030321030001580c4c1c040001c01030071800341d54508180d504180004010203072102c880014898451110150290f21000c003c08072030300000b0507520362440d8a410b41c0034010849003c0040e101e0b0b13500c815180a003d038080102c84003607400303c41400b03002c0030b4064180c1c0918407029000da081741210300d4403180c0000082c3c89242603024503100078020811101024501221010891035841401800714203052060582020800c03510521515043d40c00825110000600038480040030021410350582004040e5900714024800c512940d12010b1240c020300410810600007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 940362769 1250 940361519 940361537
    0xe100539010f0204090c090e01170a0812151903260a020601141009060f02010f05010b070201030b0d050a24060b0306011709030a0e0a0e0f1006020d050d050a1407050a 73
    0x1f80590450340c100d80000410100740e82c80c7c1485544001c03510041c0750050700a904031007001076180c034000c081a5101c91104040c0381000789500300d8000150130304038001e25020701c50b0003a000c0c4900c441e204981d41701805514001419803403412580b82c1c2c0003c011426804a07809031034035000300750941030311124003a140b07003901054104407400e80c0ca0284c00c000b09041d62018054140710315074a520804590001003604084440e9100403940268410009980003254043c1150b0b4980514440c0c40d604840f4204500c0158550340c0c0c54410600c801014912004075404c41081074910310014420410010000d16681c4c3d41102c0c801d40c801c849590010300011411044030448110709405407041000645c207200e1080300598002c1844004980e004c0440f07000000c1104820020611488a80c0f405880f68208001c0740c0e541d142c0c80f40c1001003550821808120402c1d0700c10700307503050340d018000041080c0c0c8803045290010201800d40c04c00000103078041103482a0004001c000c5544260799801031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 940364019 1250 940362769 940362791
    0x20a02060f151c0213020418060803191803030224090c0603060622060216080606090a0e0102070303090c0503123103030e100539010f020409 62
    0x8100d011101070b000c400b078101c6030207003d0a02c0c08042a5045031296000c418100300d8000401050002000a4520750001802c0c065032626600c5504203e40c0141c0074081c3e00e0404c642a6203d000303525603242d104e0481e0160505452088101d03031900078042090420031512402e0088d19160b0543e944040304840c91a0a28080100301080f4070440050340134124400005080102c0f540c40503242da60b003d02d050100c040440400845015003844203070b03003190710919144001e8100780603c40051500c3c00c04402c20040000e020550543c0514119400d180550f201d0840100a0141d0780f03100c0841d6201064210400da05603100010490240d030f1803501459540080541c4d540c6101d415504044050164070141c0c00c414020780c076031010074a40595030409042103803002040350390061b0009290b18900800ca400c00840c8104406528940a8500b010240b001c00c100d803442d0100031a6920070082180b04100e5196029443c940d40344024000030b4030481604002c0e400c80e0044281c0780b45000d0413500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 940365269 1250 940364019 940364041
    0xa27060e0a030209060103050601020c180f0604060b031501170109020a23070f050a140d120209010c0f1a0a1401140d0201180e10030308060f0a092d020a0206 69
    0x2c80394003d00e0a220741c0e5413040118003425000e02040e040d403095400c0048250b68001d00ca005241d648060f000140c40d11040301c5a034030f203028000314000c1e442c000f4180030880d40c080c2125800480d801c2040e5805103200c004071108080180100039040f1241c001244202880d0001c0c021001a50b981c804142d40000c44811017051007a001d05050b2420011980001e1440703407044481800f481c00d840340000151a00d807021442500329007510f41210040304401c582011201c660210140000c604120343c041c0043c141203440d19000d07106050420700a07081200b441448148901600003080c0d26003000040280230b01505040345000c440300d42e001040984c1110004c00030003900804200c0c044070030360011350f0740c6843ca42e00040054040c0802180c50071403074103114000d040c00f4038010070062960600030190740c005030031544211414044070182d07980d201c06860580b0150080080e81d5130b82a80380013400045018520164050445d0030162402e1381d078041c1a0408890702a11130540e06d0348100341c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 940366519 1250 940365269 940365289
    0x515010206060d03140409051e040506060108090a121d0102030909040605040812040503070c080c030606011d120a030201180f06050c070516050109060f140a27060e 72
    0x600503400307080091814980001d90464540c06030420505081c02d6200c03082076603010350091040ea070703184d005000d603212080340004d8000b000b60702d0240e12401c180e568181c55400250600c0e041094000100e14182d50502481024039401151565403a10b580d0f03000d0105445030122039607841c15045504400e5001200f1241c5c4c440000300400c0321581e0307659800c4020070011304140d988007000d00500401e6168482280d01030760207403004581302d845a180c17980da0301000360400c240c15040703059880c015441c0040d08a40140003401c01b0810102e40d03072941c50141042d461681c3d4440500001121100c0001c2005408030f4000d074000d121148413008505007060940c00f0040101c890b040140e40416000d501c030b1500218901c1c110b61030103040361141860150b8441c502040e102104134200318940c1c00c200844010040390402c00851040c4d44405000301060364114450050002084668584a140f81580d88008040390800b0038004180100c0d860880c0d0050798045480e08003044d142d8a4070003072407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 940367769 1250 940366519 940366561
    0x308010807060e06070f050a060605090a110a0e0f040c0e090916120317191a0f04020d0b06161b0f0303030213031707030e15250605150405 61
    0x6400f0001004090103003941c84104299001c07401c0c2d184a5000a1051104215a03401a0004a601c80c00c00c01002212a0040c010691841c40c201d012034508101c207090b82c9244019007001030402c03001401159201001d1011564082d01c0e0002c0d0180280d00b03c0c1c210f141080d030a40701c00c10542d50390000e85075a411041440c004030b050030041000030b4400301040b2003c0922926003001241007030009000410810307201c1c1c45426070386000c1e070001207504d44102d131a01400305594140344004032010513280b00798403200780e020340d40016106081c0e107000c0d04002c00140c0c000d002d00c1d0b6202d4580301c402c0c44581c000902104d2100e2130b04416500d4001030301039881502c4503c03486110103881c5543c04c2d030007503101116501912410420000103d0220140d0031003800044111513600c60b158500213000d10500c0341454814000513109914030007090b420340d0f02c03685d88107404003a01c282e0042100d00c4200c08890007008141084204540303004802001d00041d01d040d02e092000d91a1403c03100c1c9021405d5842c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 940369019 1250 940367769 940367777
    0x402070f0210030207060501060903030e01080f06010309320d093b09031801182603070606060f02030c211e0405100804050c0f010302120a09030801080706 68
    0x3003030001d031034440c0d80360446080034203005107000340940e40e590549509038404000304200d90740810526030001c0c1c60807844102440c00f00b10626204550140c04031029182e1070426680b4807880b003c0001c2016814014040c01c840000c41b030504051502d2010040039580c0d00e00d020340008480124011550b00302910990b000e441c119040caa003281d402075541c1c40c1860211362000c1079134001c0c503c0400440d07000b00240d8016540da007052260354040b011010090b14100035a6012150044041000b0841a902c4d1000c680001c01e105a00d00441a4107006280c946030200041104c200511079000740200d03000340e240c40d481a0302140003a81c42780900740d0194510341068400b80106181880d12800c0d00d500e155000f030500140301d0401c3d070503104001c0141031490000406010720300e0890903107800160035281840701803034580d45003078440e41c1201c5054052208a120341451740e019405459141349842045202480d282e404030014000c4a201507003ca84001c0c004035003010042540020f0b51070740e403a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 940370269 1250 940369019 940369043
    0x30905014d03071e180b04060507060908040305060c0418090b040f140d080f0903160b04020f060c3a180906170d02070302090a05061909020711040207 66
    0x707254a2141d20007000030301001200c501402090a40b081c108150003120b07559190703202c1d5408801c2400700400d4000404140e0240004c0159640c06000ca80b001039100402280074a0a458400b0b00381c01070f50001021402588204110740c002d06018004940d40d400c0580c80108420034000d0881e0314901003e0070200f02240040d0100e0f0300700740c11307000f207070320030380c806490b022000744014141483c48610741b0020301d64005005c14042e132507400c3d0707420958480145140c41044c3c0d8034400c0c0c56101002c01040b030303401c1d2400202956520b50781e00803080d10192180784d035400000e07034035912222400d000070100b042414030f411016240d0881001c6101c611201c5103049145028140c0d81c44d0700c110046d80b189500310301d010a240546006a500402d0350403400c429200100041a0401d05840c0e0210115444410300300b0240c1d65000c609508030010b0701c030000d82c40d19821b010460007003036141581d9614249881c0001d03070b01059070041032028050244400d002c0c3d6a082040180e104501c000f40c0300c060310322 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 940371519 1250 940370269 940370411
    0xb090114040e07050913030e0a0521120406111c0e0f0607080a0f021507020303010b09031c050a020c09090d0e030a061b0f0c031e03090501 61
    0x544403502d0a16100203c8405035503c40c002080c00c0b204942040e90b03042d20318868002c268000d502c0405512007165040040d505020102d1440c03408000e441c511604084035041d04440240480c0c1c82c049004144070342d8898072040041c1802008402881080c40350701a5a80c031611110f010800d4244030783c5d10b400100100104000c03201d0012aa107507400401001a180001d004900070b01401c44551908d080d100036050001e03040210300c850310f0340044081410081079036400700880c7e040d40c0c50700b140180c4950f9804c4c0442d14010b400d2240500d02c060314074401c00d481b80c10901034041c1c440f05500312005c0303a9220060100c0c1d2002910030740d01551102003140220341c00f0710b890340001c12014017107465424581c0c503100c1c1a9054484d46800d400340024429910f99401a0802d40c1c0207040c1c140490285200d80d40240307045450b02009040d8a101007204071020b01c40e400480c840d030b412000900016102c0c25020f2090994092041910400c40c2c00880f024820585400c001040750062080550864 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 940372769 1250 940371519 940371521
    0x71223120402040b03120d09060b010f3e07090509010605010903020d03031806050f070503060f0f010908030c0106051f0518010912060b040b030325020307030606180b09011404 77
    0x400c4180c5c1d451300400c4200000e210b01d80001d08080e805188010030449128200710003211510421541044074140c01078410a81141e0401c00c80103510610ba140c100d241d8030200103102d03880240c80e0a4440703205520320140d50004a201c20707121071070402c000303d07180d40c9441400c8810520420380400c0e000c203000c2000d450280c0302808598000d042c041110039000782880301c082c64000c2c088448070354032014802c11140d01c1c0d015560080c0d0b03a003000c41c80e60511100090304800d03201950b6100c2c01803107143ea2a6a4411902c0400a0841c0000c6940f1010750704803460180905001e91402100040c115a10380c3d01104081d15511000e51500342ca000da003085688075850084000307505200b8410300c0000d9a401174074a82110502401000031158003210400007600c0010244d584a03500510501c12030011507450000c504403440c0c51520034844902c00b0a04103803480e4400b502407843e01c04c000030b640c40c2142500d11954000c4a00304a2281c41808201c1304050030700038104013807132440030080b0758105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 940374019 1250 940372769 940372781
    0xc18100e0c041d0106051b070b0d06030204051f150302070503070605010e0f040b011809020a030b040516061202090111070810140c0a0507030507122312040204 70
    0x65285550425480384288440ea400666000e00500c1000a040280040c0302c08104100407000d80b0400065240080040045c040c1201c5460703540030b164840c00c10b682c008c12018005040c0e07008043d03100e0b070020754030100500d00d5102c242d0099050800250f0090510040d107440c121001a03140342039401c146220010020b0f081d40e80b410302d9420040d600124004201610100d0b11901021409604010b4142c40c292000380a9035034a0043d00c0c20300000549140000b030549139407040c40c2c1c000408424813040901511600690850b0100c0400b00c1403283c6090898400e42c0240220384032021600b65200c01c140040c865803002507042600103003840165001441d0309801494000414118500001c2c1025050f81c010010350f80030300f141844d017120034012999400030084000b04c05203080810102c9520a0a030203104000c80001d210003014014015514030980240110071041038403007018080c50076100529028061025138080c00030842000c40701a185201207074580c03230f142c035402d00000d401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 940375269 1250 940374019 940374031
    0x10f0209100f090806130303060b210a0f02040b0c011b08010608070c150c08240402031008070b120a021602121c0905041a011d06130b0c0f0c18 63
    0x4007440000c1094080180f6400364a003042050017442547c43c01900700c50860340030340d404207010b10020a56203c00340c020440380c10b02010503000b41d540c0258080c000c08c447e40c407a00c003035031010030085102659000540f13501144040204101c52081000c112952054022140055401001440f41d80d205101c0c1503044006418041d80403603403940c0c1c800c403416102c800c500100d50b03110130941c032642d03028145640004030b20701b400646c0f00007181130300d01080b8820045401503030000007041d44070210000c00700c021301410007503442c801e8680c0a501c140e079100d580c0c5030401036140408200303815041d10840710309c4420391900c50304e1204141d00b480218440c1c1f9411400901540460664154200207083e09092503035454102d01420319042104890790180319000700e9a40740c6e25110540d8004040350302152502c020404c8040c4c0001c000760180c401c010906401845a9600180e1620344034054210021601d0540f9440002040c403c0e41d24220700e0381503036006c2c0d40f0610704180404028140380d00b1030303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 940376519 1250 940375269 940375277
    0x203070828060912020c040501050f0303120907030512030a05010b04050618030a06020d0e0f0633130605040509120301150207031202210c0a1509020a06080603010f0209100f 76
    0x1c9107488880300000411401409a081100300c03041b076240901c02c03036026040480721144400003a8010903500e005d1200d50a10020101f404a1010182006480004c6130b1220486010440c00e410b0940d468109440c0ca03c41c03036040c0000810250303950000d440940d400a410541051241c03408030401c61a80382d4165018040ca4102c0c0d008585503000604600c51180b07008a00f0b2042240030a20f0408180e00c00d8400c3d42161082c4a14505051245001d141e81845032070840f169204250756600d10901d0000d034040800d156441c0d48030a0350700000100c800c102c2c1c080182c3d50f0f861a1184d200c440f0507000200d212410001400071f2082001010552002c40c03040b900040e0f141e0b03980a2070055400a18009070b804154a40c0800d42d03580310f02130103000c04002c21803c0c50380000315603549404ca404020180c078880340b110103801c482d941c000201c032500108a2080d0030303070301c0002501c0b45000b40d80040c025401c00e540301c3d020340311a000701c07204500d0107840900021620a0110f8101c1c480010482c100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 940377769 1250 940376519 940376531
    0x10303120f15090e070902160201030506180f0106270504050a0b151905040311010804021201050a0b0a09060308032d180d031103280606020307020307082806 69
    0x540010b655410292400440c001040180800010b01d00b804943c89031110b1401041210405803000f0041c100707190b420700b80071600f0740740c41c400110280c041642180b146a244420401d840b82c5441c2440d04859141e100d000720061041c040c40e01c0d1020b080035002103195520010022400c1c29446940e02000202c0c2c0001c14211080003e1070f0f070101c8000ca0000100d021851500c441d9001e50035160ba80c030f0a046c0a85000d00c0c540d2400c2c0d04502e81800c10b410b00c641d40b0000f4055494220074641c0300e8003400001c03c6545044080200148003a2081501a0100c1c40d40030451710f09610a0206032908480014216651289203140120100c02880f0329000c142c40451514010354000a00600100c041901c800700b82c0c9511a00d08101020101c080608088084070020301680499811511603c2000044a41c0c15541e004809921103500c1c001403800f40c0000d14154080041d009280c8224244c9010a076560f050581d41d0190442814803203440c42140d040340091080010b400d24402d14001c00d203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 940379019 1250 940377769 940377791
    0x11d01030204181b031e0c1209030816091a030a060803030108060103030816080a0c110d0203090a0905060906010f02241e04031418090c0406120203010303120f 70
    0x40c683c0030003440309140b601d560114800f62082c0c0748034224803074039140c00c104080581061b0b040f41c0d18034000300c50000d9a2043c401840d80d104e064107141c5044042401c1c04a80d0b0503141c001c1c040e8000319541c4226581c201802d065aa12440d900812200c0034000c0119840c88010031102078ad2014050700302e0b042e0b0350100019030703900c00d00280d80248031800c00340180350b241d802c010386060002048402c800500c40213035400140c0216006802c5640c10000140e4804008815527541e00030300034020303952060451511201d90300200070b01c0c0c0a00180e400c1c58441e95035040303910549109455060b400215000014615441000c3e107414101c030610480300c00c0e04008120000d80d803200141c4501c1c1c801d0020400880e4061351007030221050400341100c6151070181c80041c2600103d07500450703141c80c0050302c41882c5170f82e40910903070303101d00400009642c28100d1004606510a106220119a8200e04d034000c4084610a8038101c940581b201e2024554596800c00201300307410115403026910600c02c02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 940380269 1250 940379019 940379039
    0x5040b07171005190314070501120e0d0503070c0b0906190b030a02010804051e0c0f06131e0302060f030a0e0d020c150c0d091806210203150426030105011d01030204 72
    0x50300d40390308040e11f005800c0c07e00041041040717640740002c041c204000d9841003640050011485080d9140003910394540d1101140c100f1031280029245501e480c050198040c004564a8010017180c03100160000e0714042c0c0d001070303803800000c0e40e6044d080b080d5074a000d940603c068961092250054900081c804400071400a0005e13078004625401047c82070003500740203801e030151001c1140e40764101421a14862880100f5028140400b03d55201c0003502c0051000420060355005222548645107801c480f11603030003c9403403c141504000b030b160050306011448803000e1034240c0c040e004c0c00c90140244071a1114002d54a81d8240c03040020204905040c403021075030200e145d850b840032134508a9100070b10002030764a1120180761450070403031020902c161052035440c180100100450500009080122100e001002108404100030030411021400000d401e03000034242c8030003110702e02148840c042402480d01068007070601c0803002d00b060103414040803051501514190b01c58500705 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 940381519 1250 940380269 940380293
    0x6041e11070506070201051b180111010f0e060a0f140f0702070306141806010f27020304031809060509040209060d12051e161e0605040b071710051903 66
    0x503006075944e20900664550000c46028040c1c01110041d0800180907960400441003805e60707414003402050382030bc411001e4000340100c40070281c003002482d140540c80d6890360320840740144214500210003505100700c5c85500e0188100d48154209656800700781044444060310b10801d510807000300000141085c0644096664000102040790802c00f00d0300f20a5114074100f000c00b43c0000c00140040b01050100f0011106000f02ca0100c52062080c01500414140e0854240d903000000300002e054002050511410250030400c0005d42d4400c2900c0494441b4004d05900c03140c2400482c0c0545001e40c2038a4004070001d1a4401c0055140d403400a0700c403841145502041000ca0b004030a61100c80d41e130741d0141441c0c03501a02d8214911481914204032160040a603030f42d08401100400e45685001c1c0302541c8960100110b04050030044601d690803202000050f08046012813410250f001a50141071002002c4a035a8101801c10160100c0c481075589201040000040440c82031254a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 940382769 1250 940381519 940381531
    0x905070c03080a05061509060c0f1e1204090e1903080603070f081510090c050403021516121202131a03040f1b1805070806041e11070506 60
    0x990510049841c01a101c000000d112840d010714010800c08107464141c100e04001d1281e4030155650020b03400094401d0089140744940c40c4202c031188110301d40d000400710f14585d04001d588407450190085c2da980c403c54401000c5428406200c104150300310b07034009146c0b1076811400d441c001c0003040340c0040d44e0764164074142c00040d50b440520200382070074046640a48564080400403900b0305081c0355076000c4060802865600c01c0000580c440310014076040681220101801860410440185242c109000583c401e0240c40c403500d2080c1c007000129413450341070350003401c2c10054907152a403402c1c3c904610314082c42512030103000600355900c002c0c00340e2814598142e60140c1403180740040c020402d08440c400031030400a110108480481100000d41e01955800f40f03654000903081e4880310690109521045040b401d0035000116003040d0700c40c01c2d0596030300103555196070030007060310540b03c3d041c0c0401a1803a01c40b0000b058503040a180c03441242c555516004a0707a4500703103800030443d11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 940384019 1250 940382769 940382777
    0x17011e0e100608040311063405030f150d030c03121406010c03030e0a1401050601021f020a0201180521041413270c0803030f070e0f120102040603111303080d06090507 73
    0xc0580c02980d006030b52100c001184044588c0d600b20345401621a1001800c1420003148040016080080300c100100381080040d0103100c0010b41441e01800042d00ca41045001c5603898001004042e614801d9083c4035a14810304c41050301c5c1c0c10010340d9020329808041d0205600c0d6906c0126444d070401440c0c01d0305206143d12101040c113101c41d1801c551005d401030703045402550120322212340c00425220611462400165210b41c03080c0c0581c01005440e0340d0502030903014081109010000c0740141c002c025500b0040243c251001000302d6500c1140103a10f160380414074417030074038100b0041c0415045000040043c0b00f106041d0190400d480e00005076031307040c4010400f04204500d8100f0725000300800c0009506506201c41a43e45a00f80189007a0403c600d5001c44050f42c0c1d101c030810034140c00041d00c0418203000040f25207020398058001c003004281800c1d07018101c05041e60464210000c401900e020740f60031a43e4441959000e400f00c09078070354079420f010498107580d20405015010ba512 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 940385269 1250 940384019 940384051
    0xf08191d010605040204060f1407050706050a020c0d03082d01080a05101e0506060d0c111908040311011211030613141617011e0e10060804031106 64
    0x380c80360a40c2e0303a82d080180030314014082040429040040c5400d96070140c01d000080302060925080580107612000d01140b1804000041a82d0810018440500e01c0e50958031910142c1007030041294100c040100004c0d1483d0003d0341c56420545046003954072254000303d20b4420003d00d54030b421080e0000c0300160413810620b410030100300180c1e841030015407420b0022420f40c0e0301681921943c155141003040c1c650000403c580e65407012a401001c00020030001c071801002d00900da0b0524046d01080e030b00c689950300f413000c0038443c0240982c580c414003040c9040c0c1140c0d58032041c04503550005050061032941d240c000e19090040d640303160042c030303003164482ca850710401c880610042c8a04d1032207460110100c3c04910505120356110700c011f001d8205074017031600c0440320300c510103800d90a021900000850007500700100c03c0845a000c0301c0d03000d002d0341c8034190203a51080c00d0f6100c0401181001003001418059000280c2c024005c1c10f22508694000a0444c1092022540c5007a5815004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 940386519 1250 940385269 940385321
    0x812030105040c111c0903020d060b0306060f1c1403040312090b25081c051b0f04140f04020f090306090d0c0602070f12050a02100504030f0819 63
    0x441402c00c6240149818085030445013443d64032000140817140d4082413940350418080e024504002c002c55010740300c80884003680c20408018000030910911a000302c4002c10035526151980381e00c8003c005055068181d51050b4883c5100145242150f564030f0100d0f0520604409201810085006800c03484c020b0310091002055841150024a00a00c041c0106c0c600c1c2c2d6940341c44101041e90383c0e06155000c00a50618400c2c030f00900c408640000400404046e03001a01e8001070300031680444007001e04000c06864000e0b5000318031400e1075000c424002004021401c9144035a43c040c090a0ac40758031091001013801c1c1d078002c1424814500000603000c41604007001322a80c0b2a1007076010b00994130320424000c0540b18146005010650089408428400c0c1d1240e00725900c0c0d400f000d000c2c80c200c58201c0207800e640200130044007602030403e02043c4050030b4014107100310b515542d455080828a2800c0d00d1444000d0b10081c2518611800fa52401d80d26209811500703a95543c0e06072410011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 940387769 1250 940386519 940386521
    0x7020105070c08030610020f0304090b0a0e070519030b1f0f02071a0a050c0115260d081f09051602150a09170d021218060a0f06081203010504 62
    0x1404040030400c0c1404034001081404084d00d82084e000c954620740c52070141c00481c689000340125903030b40c3c0000100003034016a245d219548011081e05d41d41003c0c1da0340c150b0400c0c0c0c070400b11454030104404105607443e21020130104611810b4030b040018465030980301082d0404a825800326000c40c1c10900703400103640118480d805003607188018561241021091341042d20110150012000d01150b215451030161060b2500e04168070000c00030001d00c16002c4207042d10f90320a03068042c404440142d50f4000a074462440c0506d00001004005065441182e60a8000301840c0036003031003c08100252205400550040c041020b01081c40d082c041004051896030145036010741d80b00c108001708180600940643c003400d00c102c0010001c1c0f890600c2c0c50807450a0807001402400007480d000d05200c1903018003640403040003240d41a42c1e42840f407100c03052540102c0100c541c40b01001601e2200f8030381000084c9220401c01041050362140702c1e501e400040701d940420300d140800140b11034101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 940389019 1250 940387769 940387771
    0x1062601152a0c23060a09080a06090b07020303090a0b041e1518020117060612010b030708010f03020102150a200304050c0405060a0312021e0a02040b091506090307090c0807020105 79
    0x4000c110503a00c1c4554084c102c4a4011443c050301400b000f040703c405c814000d112520080c0a0041503030300e504581d140038801052040400c031468680303c008a01034910001c25030b48207041110080101c164030340c8411610500003002100c41c0b04c0390700d044242c07003211707840603d01e07181c4280204030404100e07400e02000c0d00e41c0c10307041d00c881850807800c18001d0307a0701c83c0182d5a110b44041c0b075030580c3c2c1c6070070780071900500c1442020f4501020303102c00000c800706000000c44c41144a03071b68000c01642c03140c0158411942d0380c880680168461011349410040c5100c803140c015000640018814210f00764070240c5880300001d0141903e000700401051100134000508035410885c0c0c10000d61408400141040740e840c04003030041c00c0d900d4040a03c99000f003020000c5c501c03007140e56032441041115003569503102c00300124080c606250f0b4460030360424003032a86c00381010b5501004104100e9042c02035035040382210382d40c0b610600100168000e564400c00200540766039a2004a1400040107425600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 940390269 1250 940389019 940389029
    0x20c1f020a090e15090c12010e0f0109020a021e01020c0114010e0c0c0c060301090e0d0c0b0105010c0c1806050901120c0e0a0e011401062601152a0c 65
    0x3004001c2541420303031102e9402d0540d64402c03e84441525140300c10035011040044864200221006000700255a100584103001400720034000aa813030351303140e1038a0f0106484080c03140b19590300500c03140c400da0300a4090751009104031451111209a006404881e2050030300440c5d60000b02d81c0b0040a00b80620808001d510200d201e0551401003640703980c5000030140300c40c003c0082000c0b0041311041c0909000000000c5c181d9841e561541c51820080a041e80f4000d060b10401c95141455409080032344803603500500e030a1040d84c40d080055404141003081251070510480d0086039145117510604240c042c0a00d00240c66800c12040c004241010381290000380e04146080000a8003106090700ba14004001c1c0c280b1303034030b4000c140005800e40943c01c007061350030000c007586ea8121103040b0a04a401030360300e815040c1c1070714000301700b046441100b00480500d43c00040c090b00c0700914940850061520b40408003054880c0c00c3c2d0812100700c010310f20f0701444e070b8001e0b0040c054010780000c0500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 940391519 1250 940390269 940390271
    0x10c02090f012105100c022a131506180305031b010510080307021921030e10020c060c0f06070216090204080303150a090204080619090b042004020c1f 66
    0x40040c1c50f04d55503202000c1070111403544540b800c42a184c4288090017581102c0804000c01c00070024528090110291415000d481c42d907000c000782204500031104001e00c99054120a1801d042c82241c400c19100008001c42d002d003600000040c00400003006600700a904c160281f0f15004d442030700f5910302a29085001c0100d120600040f5400300444642c3c95040310000360568042070460042c021551020a8403500c100300745404140c0c500e040202140702c0e030344001601e5088400c105100b07010802600040c0d100548000207402c0120040c01e9660304081254407101c07002650720701d8860b0484203400180c0041c80820078408010300c24034003500d4001c1d0154146810314005070354900000744440116a4840316014007529104044000b03000c0085043d5035840d2565100c0e82c1c0c2c3e4900782d545030149000e451142c41041803d1140401d51a40003200300290b0712640c0355400055a0209800d04004480c800d0b242c1036680c80c40201300524401c4043c12075070010620301e0381e9442501d00420401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 940392769 1250 940391519 940391579
    0xd0c151106090d08070813020a09090215031911070203070305070e01091109010c140d050702150403050304051e0a0f030b1006020c15130902070b0115020309010e010c02090f01 77
    0x1807504600c9255004071103103850300187d0b490b0f80d800383c000340c59604040e410010108010444405503005000c1c076500030780714070300d902142c801001b001d440f044444d96920b4459540719100c04003680c00054600003543c0b0001d00700b0100390002400d06100d07500c01c5030543e1283c40100201c030281040b890042480c028100507603103c0443e01003491047c1c0540b68104010740b00c4210800c50707400f440380c5402409000301e41c4403003000a0b014006502014040e4891004045c0d5081d1260000b400c075400c4d20350103c091030400d450103040c001b10700b8007036580c0d10300d60004450540c17540d05c07912101f00080a01445000c5224a54208044c0c104405000a40c0c4035020718401d01c107a9400041c101502c440c16140812444403806100c0020f00076110041c541d0741210307500203182c0c051030b0068061075000700242131190366202c1005407048008030204000d6007040c44100c21940c060114051405018107098051210580c0062130034541121038003d1040000010b204a040c1642d40c040352405008511440b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 940394019 1250 940392769 940392793
    0x602060402010f0c02180f0712020403083901020d0b01020c1503060103060305010509010b010f02030c0601440609010e06061e100f080c030103110d0c15110609 70
    0x9440c0c5080c02e038004d01007914100d00464039141171b412070700c2200da41c200c449400e1100300500322000a440e50000104c00e010728040000551080340c04883d07114508a14203441c6402120b130082c403001070150454942515083c64104003100d00b011035681d00001030307441d03110780f884030704441c00541001c0c110f41c8040c030b07596a50b031079440354a6140780f030b4041d0440e1a6501e0500480280c00c0ca50002071841d4240410f01000150540004440030f0007600c03040412603600710202d94038010a91407031150380c02000104501d01007140714400312950321224010308440000e003490404c9145840e0b2038004910503401c003c400c0e09002c402e40100c0d0354002800707149010074000780d40300c50180c4500c0c8102d0400000c0ca4000c0c801c2e06000101100103400801050302644003d070150700001d0f07940740451780c2c500001300c1328405e440c02c40c3c0c16070303a000300d040ca0000081002d0043d184034044c000c41d601340c10300c100416050244019500810703590395840d003410b005800c100c0e0500c18040c0201c02180c0c41041c001103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 940395269 1250 940394019 940394027
    0x2151501080a1506090e010515030f04020a090603081b07080c2707020a1a070c0807033e0303010b090603150612180a17090102010b1e0a060206040201 66
    0x1a24600918025509441d0118400300816648140c081d200340c4901c400910b907500914148100c80f403150302e280c9140c1c0d07030b0307824025540300304680550305e100c0801c005002c0b142502c4035141c03c18000703030950004980b610b2086d01103036001d070416100c140010408200c0007205420b0340d6105042140a000800e10713001049a03107206007500c8900c55814981c2043c540e1010300095410216040d01914080c1070081019494104081060354207440741c03049a12170050342001e0500548003961908078040c1c103070f19a24069001402c007101000341c4c0000074007180c00880498075000c80003104c142a0b003c0c00c00c0314202803540b81480f41c007107a04207000400c51401001e00340c85010000f680e41070703680d0350f608184603481204503070000d6121901158085038083e002c0b81c1148541c00d00110b00d5140c0d4080407a940e500e84013400700030700040e046c09154421a80d084054003a00d44180004035660b15104001a120102c0583d003001469407021588964a0a020395100800460019040c6d034103290300020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 940396519 1250 940395269 940395301
    0x20d1103060610120906110d1b0c0c060807050c0d0f091a0409091502040e0601081e0c13052101051e1b040302040c09090506060f04090b0102010204030c090b010215 72
    0xb01503540d42c0ca069405100484d000660703c41da84292690b5a02c000c03d01c5c900c0104101e00c070340401c2041d82c9d506000708034000c41c1500c080980102980d01e0301440c00e071045906400080228003040002e01003044445410414228031017856243c0d8100f02c0f4501c0d1004026503510342c00020b4103e500140d10070001010021503042d5402c050f40403402c41a64201103030802c0d803c1c9010852941300080c000341000b0340b09115809036009913203040940e22001c200b0303c00c094450403215400744000d80032420039001c0070300411000790b600e00020850340d600c80c00501c004000310401020040c6200c07420300317207407405e11846512840d001c400700400c00c40c110000e4251480280800d500c00c3c840014000c1198140701641c00440c0d0040050054205d00a8010055a0240b1503030f0091401d04000c10003c5c9024026030764410304182400d81800d280204803000741452700e04060565508000c0403000c15107410009e4040c2620010200c1c0c50400500020f15210030b401d400740069020200b402113254840070b00e8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 940397769 1250 940396519 940396547
    0x30a03051902031308010207330902010e1909150b0a1803080d0207052b030216020306041a150616110a090c0e04111213020d1103060610 60
    0x941108400c000d81ca18071485014018041c00c0381e071300061702017054000308400c610441e009032585c000300ca4210044925201e070f403500e4044078980804d44142e80c0d03000701e207200d00514000d12040c5844020404984581682c2d801185100e0400d01896605008070a070340c0c2182c0f0030a0000515000404c00b041c0141209841000001c1520000c040108060200559081445281c1d40d0080d60b200c0b60003940071400407141802a40c440245900266809050804440310011044d00e41c0000c02c40082d070128051141c1c0c21b08a110358000341c0c5040110510503032054200307090b03942c0445000c2d0380c0c01d08010220004141c102d9061300c0183c903850180c50301026550781d0150041d515281c0528458062080c05400098608000846422075000010200c403580c481c80307480700c41c8005000aa0b89010840c540480e02000000000408000d1003a8000030f25501e0002446541c7d0001d880400007004c1130303440c01d8144024071250700d02440040c0e00044103e44481d04641e40350400b030014501c941003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 940399019 1250 940397769 940397797
    0x30c110a11190f090e0d020f0303010504090f060c03020306031c02030a0c03023a090e0c0a021e060f010506070506150a0b0d090c0b040305071a07020d0b01050906030a0305 75
    0x80903407500d00804140b030152410001c099011500d5400c1e0200900710300240075403601c03514400b09001d9001080411100c121200611701c0c47e070070201481301510f100c540071900500f0ba44010404aa007034031a80702940e02703980d0050f80d681804801c141c90500c061084591102880446008081e000003c0301c0103002d5078140b0781c1c140180750809070b04240500003c440c042c00e600d10488008a402a10a84500800030182d150003407011800c58551085000d040c0319189200c0100303005114001c00341c00200007a2044488503000c400209103400000f041483c015444002845110500040300d98050002075545030b0810820f600e9460341d80c00050b154110b00d041000c4d94810341d40b10583c612010b03080b80c00d08166035920441d44240140705200d001c1e641c0c0910f6003c0403651500c0001102e0459800400518021741000013400e0b2448240001c80d010310000c0080303100507164040401940e9000c0c0c505286250700d44000e002c0503440050485220350448180e6400080c0c11174140c9005c4000c0c10701d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 940400269 1250 940399019 940399039
    0x406080703020723160f03140115180528050405011d03121b0a0e0301150305060a050106050a0c0b15032a06070803010e10090606030c110a11 62
    0x2410341c020320a0401c0074103011030808610f24100c5038181203052080b001421900c0446144101910010080c021031011071210481000820700c0c40703100007080c0788a540000b0388032400000701d201e40c0604d503100620440440d0300c0c2e02191082c80c450181c2c03001a848803201e5500c014500a07000f00303820318262032010795a8000c40c0500c03400354001c000a2510203842c010480c0c140445995035085800b801d080e051403c000107601c880c600c149400005958183c984c10311129242c240c40036035071003140036015940c9442d0004000c1700c044100d0000c5000c0e00180586050454100b0250740050704028103004d42000b204480c1075010700d00e0032f62103401030501c00c00d0340c1b10340c4a00480e000c2d00e125140d0303040c456081100445000d00040c030f0310070030104a11081d121440700c2440341c14050f441003e07100120510040141200040c0101d50096a001860002c1501c8100d02011241d9581180000a580d412078406c82c41e080008400c03105c6240000703001818407135817510407122941896500900c1946 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 940401519 1250 940400269 940400281
    0xe1f08010c090b1602040e0c191409070e030a06090b070306030c090207030c1416060c200f12010b1503060604090e1006141003051608130b0f1e0903040608 68
    0x1041307102040c1c0c1e0042083c01005031080c002540d41408003040d51040070842c20b030480e913450307500c0444100c4802c0b409502480d00c2c40403c0060340b8070010b10b07801c24090010311580d1241e500380b100c104154494900018100d81d241800c5d03041c0c58008203990f09261400038144042594805100111041100c01507500c05181c90200d90a4945050041907001402003240702c9a80106503041800818030200e410103941381c4d412034000c140700802034112104106e801014900c1200102040380c0060305010b808642003003c58504c0c031000c0c1c01441140d40d81c4c60344100600c1d00e0420b42c260b0100d00030056080d4140a030002d070f0184500d10412071240d940d1a0480c4070560140310b00441d10907054800c1150300e598044038a840c50304500840c1c402c4a0001c1550b0246d402481401c0c055034262400450078803944c2c03020344041002408460002000c20085030010b1040c140551146201c000c80d01194181502c0d200d00100d80941003410041d10201000290080003003941c04403038140c034007180691600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 940402769 1250 940401519 940401547
    0x1021f060e0a09120f051815070b0103050d0c02011d0f06040902130e22030908160513090201050a1803060204032003030306010905060708040e1f08010c090b 69
    0x640c0c00440480355540400800c2619648803140b00790041801101007090540d0440f4002c0070100a170b00810424040c007001002c81424101c0b00090281c003e54446501c21780303409440d006188100c03800c815550040c800c000b070a01044074549050b007801e070301c449020390028041d1450807180007038a915080f03031050aa51403540710b0038000d0016100554490301c0d0016000a13600444104400740320301240084c44c82101e10b4000c1c411603052030318104c0200840303460621002c90000a03001c01c03c45050101c1c0f001820f20580f03800340003543d5909041884d12b000e0100d10800780d90380f104290710305101c0c500541d030080220ba10760384140ca8611030f9810384038002d605501c0d90b41c1015200510100b000310030403c04292526000d0041950700c020001c44804066480c07008590560010720041010400d034102000074041c2c091003440d05a0406407208000d0128003002c4a0640000c080381010301550452154900007500a9100903c0107002000018040750300b24031a80000391800500b040e0b6846079 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 940404019 1250 940402769 940402781
    0x2c030f0a0914010807080612070302040f0b01020c060307090303050f16030801140a0536091e01140601052208010606200a11030307061b0f03050601021f 67
    0x11900060315254003a60081c000c800700e0065000da0820720341c4849041d13002d0680c80b8070403000c0317a8810503c1c1e6a820103211030718480c0012461284141b0b94080300603920b81c0103125500303084050010700480804002403400700c0481c2c1c6c01d80500301c1001170024450340410348009990700341c01c02c140d0702c002d54282ca0383c41e4460402008840d0783e01034050000c05900940741d504903082603001c14100e00c0c520742040440200c2d4030866606c005042105c202070310102400601c2d0300c2107420991051160362401c0031105a048034900002d80007103200341e81444c3c081d60103000042e8a070340200081240112140c40b0404013900140c1071200c04200c4000e0001a03403803022851380008cca81c00f95582e42c09005020b00800d014000c081070301c001d0749415000c0805d00c824005140c050040480340703a03079160009091000044242c0500040040c00c0114940b0b00620140c07080399045101258100b4200904004030024031404050404081c80181e80e400501418000301d0307411604e101c0e08410604c80c2c01407038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 940405269 1250 940404019 940404037
    0x40e012f16020f180103060524130f0204030b190c02030f07020418060207060b0906030a03120902060702120318011e0f03020c12041703091503040c0b0d0b10032c03 72
    0x166213001104110242d00100d0098031b540039000c3c12001030036555105441e0140005030000b0000c035130703268600080d802030b80c1600c60134400103207441d407030391908444200700703c6d030341ca60700d84101e00e192021502900c030788409030905102450802480c40000205441140702c0607100b20780740c078481010000044c04045945501c080708564800040c58000050044a0051071084403031000007421400c0100e20b126030503270b050340c402494400340b8003402c006000b010f5040e80c21040503c00c0341e005854520208035242842e030015515000c9078000f04030b0031071129500c141082010041d003c541c0ca0521071303d6003880224207002460314003188080b4028020054204081d224402180d01c0c6000d10000900555102824103135298086160803586c900c950002c0d5504141400d0607408500c40c40c2010310740241c0300340002c081050b600c40105021783c002286140242d5070320000610b080c40c2820586904d107841c0e007010f203e25070f012007140170260344000c8540000307509010140d0201c541403084600b545 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 940406519 1250 940405269 940405309
    0x80315010909050f15030304050a3c0f05010c02090c1e0409090218012108071205030a05130308070e030705041d06010611031602040e012f16020f 64
    0x102d08080030101131001a108a101120000c120760010b090200484054510140981902c1c41c80c0070010000c60184000c1a03514a036600031841c0344a5505103034032100001980b801840c1400c11080d12054080c540c041c41c180000c0c0012100123840d02d030101c903444013540320b410703171074004010001207000c3c516034288611035070005004c9403071507e507401206254020b0311304410182040c03003105901c650a0144005021003514a9010301d4540c03002800041d1260401c1424840302d03984580c9810031010444000c64000300411400304024842e40f40d01805400f0751060300e0362103481c0a46842c602800003070410078102d0724400e05850800040e4000d00024004202d5005000000302d08228045440c0c0554090800001003481c420301c0024025400c40001e903191000810900104140418080360402d407a070000d41d40c0b04800707100c0c1d10200040034448901d0340303140701806e260584034214071401c0001e09111922508819508101040380e05490785412400c0480000b048000d4188ae4a1182 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 940407769 1250 940406519 940406521
    0x1b06071502040f090513120512010905151f080c09190e180c0607140607080a231302040e060123150703030c090503010e07180908031501090905 63
    0xd2140ea03402402120141c1d11295107258956a0ba1400e6650a0340c1800050030450354420210313491000d00707944200c160030014544600b142c441800c50009910419102d6940c0d000c010b103d003a20010b454400004584010b840b10119640039505e640700c0e500081000380404c00106a46a454101e4042c000010201288020608500d003a40803040c01248084103407440411210384142002c05031307181e034100150400320504030038440950000e282c20340c2c000e2030106001720051014021a0f00034089079841c45400d140c940b501c0c3c810f440c01d4005043c0d44080b407000124207800c400840b16045002885090016034550000501400796498810700600501000043c950616a111400720345200482c03074048912008200c602580e005402458140c204103500010784070380e00c001443c00130380c1041c40d0707410348500c0030900b11810254910200da004040521001800284584002d1520541403000c10410f59524a69000207007160b80407048241d1483c5a50303026245100203850040410019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 940409019 1250 940407769 940407803
    0x120619031103070609031e030302121303171009050a020405040e03040f121e26070303110c28051914010e06070f03090203120301031a01081b0607 64
    0xc2001c1201180e200c0d00c9805000a01540980450303421240c2002c414440c401c0c031591a04184d030710414044041540c01c100c03140b0390301d02801c1c0b464040c140c81500f50300032041034a0007501ca8041d00401c20740044025042001040510b00e01c601500c80200000c5595150301c00940d000c2c1c0515004258024100a000444560000094812a1000c5c40702c581c0f00c43d902c50071207803521800c0b80b0260901040160403aa20700e0003502060f5118030404d00100c000001c0c1d2980341110070004d0400b03220100004400742410340c58020646a520072203231103860301210340c031459660b46da2011a409548403500a00d02c00d400c00720855101c403500201500c0010344224007011540c8a002d1044a441820800f5007014480c14420f100004902034005c0c850307030300c820805840345544e100c080380400d0344030703001039006890a1140140000114003895200c0d415441c1129a200c1c0c0440030101c00814000104049800051000130001c5600c031001c2d4208001d00109580e449100300c09040d581c610b07020020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 940410269 1250 940409019 940409033
    0x80d0c020610063207050106060509180907120213050901020310080a110f031009050a03020706110a02010309030e0d03230a0e121908031b040b12061903 67
    0xb1194000e03142050099464800641d42042c804200300c1c207400c02103200e401c1c2d00b002201c405454096001c4101d0600100b50350703050965245070001c070001031021640d4000c0d810031420387c80a94501d00c0e82454a454400038660f9104031070b00c40c4014512104c56450107541741c820508030402c68402c024000c900d8a40c040c0350113584141e6a0460154031020002030340c8101183d8108401d9001c0801c10400502004000b648810324a017945c0c107015030090b00400c080188201a201803140014220001860802a0030a5403580c403174400e000103c0d0128114441c0800d03440c0400d81d09003030020342d180c0786040444100541c0e88004c0c3d080000000040140340c1c20042494180d12080d076001020a1445100d8030680200502c9602240c80022140c541d880c2560b421350b1a48401c400311039030030981211902d2040c03d1081c041e00c0c40c1d030340042481031045075005104000d09120481901d01031504850070355920665404160b01c0e209075011442594552500003001030005020f40c0304e43e6241d050944c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 940411519 1250 940410269 940410271
    0x210a180c0302030d11030a031a030723030102030903030a0507090312080a0509030f0412020f0306180c010305011202060304051f0c02060f010503120a03090b1005011227080d0c0206 79
    0x40c0c40f0341309103411301c01907910441e6030702c0c0305000c00009941000f4031400190080c02101103550007141c0444c03000711458400700403000041c18030f8040118038141e4488034ac3c900310380b00b2130043d010340d00401c108000000000704994001e04030b44d00000d41907444d80c40449101150750002007941e07031340d60164074a20783e000c6c0841e4080c61012034100400c1c1c95540b110343d074030b1080c0031072208018030a203c100000f0b04001c040e6060640040c240e142c1420190300080d04183c41200c0c100001080448034064040c000c10080181c49020b082c104220350401c000d0b009030380071406d00240701304e00001c001410800d0610600c040b911107014800b480200700300c4054003514a00010704014400c81e0000303181c01000d4114941207400c00b8000e000d0640c007010300300c1801e5000715001401c1c103440b003d40200242a00c94041d05c5142d8400400340180d013064001402c025441c010142c000707040c4100060391400310718104450340c12080c140c0444090618ac200218012030600311203643c0b0700040003a40580209445e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 940412769 1250 940411519 940411523
    0x180204030c0b0405100c020a06050c12030703022505060103061a0d050d390804120f020418020f060309151603060e090a080901030b1320210a180c03 65
    0x75105d41d60180080b1849041604041d502c203248880c2004040d000d400204400038015046e40c034281c03a00d075010042ca60003601c4020000c0d43c00106144101342d4580b14640046022424005c500540c1e00c41d0341e95920103000107414079a4403110404064045950701860050207800c025592070305080ca40d48a4400902c802c011030710344c510800039800c041c0e000300e416000480e02d10345901f54194101d1080341e1080003c9481d004204004540e4850301500414494450014541c18440d0ba00c148003d542010108aa030721210b04040070041c1d40702c2c4040d580c0003c0030703201c440d240d69400070074624010071100310810302d07803201042c170449000c44419600351054540341401013a6403103e030000003080803200c0301402c6d00100500c40004940e000145030440051401080d0541000001442401940c10304000e25545202c0e0344065040416002c0c1a113035100541820a60f0160010140340c1c47c600d02d15a00c1c020603400515500302c0c40c0e01031550302c0440005003103645810310740300008642c0c034081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 940414019 1250 940412769 940412779
    0x603030306050d080f03100503120c120406020a0f0813121707021008130209070309060507020102210604020d0e0303010e0901150501030510090c120b04060302010504180204030c0b0405 81
    0x301040d1824000b140303d2150303078403000b05894621940b030110b8040e04068050a045843d440000481d13607010050070111200e0718401c0f556031340443d0317203562800c024120b04030400070007440200070054010407240c9540350010050049000f00e032a005065128000f0340c5003900d0701150b404a190035002130b008003640d2040e094075202d4100741e9910407030b070300404400a51004007400c0303d0381058818110983c115280ca03101c40e070910307400c0c0e002a01d41841110724100099445610500b44001c03030203260740040e494002185040030708140d081340106110700e00205500d01e0b0010801c29125941210386000c0c850008104400f41c2071a1030ba140e40c803e11942c1c0181c1c81c04808580c0009042c8180c042c001000364000c10301524040056010b810b00a040d003860411040000800c8811405065140c0e4801d5488152000c801d00701c0b40100e0301d070546a14000c0c1e00d020380c1800181d800c40c080ba800d50300c602142c214201c4c145400c0b8000b80c441d0350002040040a02c0c80020030b1400d0714082c0c801d40c0c100b118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 940415269 1250 940414019 940414031
    0x1502011d07080a020d0c0305030f311a0c0d09030203120909150d0f1506060806060a05090604150c0c1224020c0109050609070503030301030312180f0606030303 70
    0x41281e581c5080d000c0c03440141c220869140c018905040d060408a2040e118031480c240e4a0f01c889081d900440052540c602000903c009250182d880400c0c43c080404c0080d079410800310b440f03c040289902403a400314410380c11800c100da14003400c0d035001081740012102100001c210042c0100c905100c101d002e072003503041d094960100d40e025140d04220180c9017400c16a074102c071a100050701c00107034507009540c0c50064000300b6044d00c01d0103d2540904040441d010a1041d00c40482d0450b51062080002c0b50f0103200c3d00f03944560464045060a290003506ca104400004000703118030380c061030800052010030300910380c0112250000c0c41c020507248100c81c4c1d03202032090508818401c01011101c806041070514220800008603c07008480c00605001d64150744500311020300400760b405520201c100042c85104204032006814160061800c551660740c000e8010075001c402080d00c3c50316840003150381c280b034400d0414400c1e089481400d1030030701410071000902140c04281c0c00241405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 940416519 1250 940415269 940415321
    0x90316050a0e0106121e0c09050a0602030c060c07031419030b041a04110418090c1409070f0509060324040e0c010c0606090618050703062301020106150201 68
    0x4103000d040310320300e8807841400581120700800900803640604504181c4d10191b01c10b10429220342c0450348001e450351030040d4200410058440086d903c56400c641c0208048101078402040942c0c121140d10f0401e5100d9405280595108441c0d0201c0b440940011402c900860005101e482489a0544040144d172510b001440142c40400407800c000c0b010210034562141015030000c980c02482c046260305260311407450311040300403001444401170f11116614180701ca000880710091420307041c84094034041001050b1040d070003c000c0024001002092110540181c046548515004100994034608414582c100080c41014001008000100030140742018454550302d914600000d0111885034401158014100d0108031030700e9840342800100b1030310500810002c1c10401c5c0c0314105050110f2000c5084480080018041504000382000154681030349912038035038444452400a0710000183e008d456698086511101c0e9444c01450f0f160b4194018800d03100700030881328410900f8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 940417769 1250 940416519 940416539
    0x5030a0308220c05060c0c06030901090519031e0504081f0c0906050316020f010f0504150b060301061b1a18010614040c020a08030408030712050702070911090316050a 73
    0x2c84802040c040c1043c078140300500d8035030702900400d1080d03001c5071040c15084000c5035041d0010b031620f0a09a4694281008005050000144288001d00c80c501c80c0007241e10001d00404c6920320f1001e204d40c101800c66010ba204004403806402c01008030b6035906290b0940b008118407800385058040d10300b407110700310244243d5015045560a0f0b64480c255200c000c081c1ea8076a0540d00050250f1003118810f801d9890700f07000d40d4081c0c88102d500081c242c907250a10b030a40c0c8182c43d121a0040341781070601602940e510702030300e041d03c9651a02550404402031120a1107008140103484130f5100c07201e42c40040505034180b8424501403426241c4c480c0c061010600f07031000c5020b0f81c0c100c0794102a4130121828190305c944000380d1144112400c031685501c03000d40b2070707000362400d40f0f00803000810440300b140c0223041c07402c40041c04d0401b008503140032034000f500d4042c240216880d164984e0003c840110450003601c40c41c05005095480c10b5061900909011030948100c5015030a180d200051118003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 940419019 1250 940417769 940417831
    0x3a1103040f0618021302030a0c090b16060b061605010f0e1009050304030b04050d0e06120f070302190e15070209070c05150115030609020f1b030405030a0308 69
    0x1c050114041c44186964038009000c110040c0f840300180301e00d500300941c0d038031a10302e041c0522682e8010b0b62401c0407590401500e140340c40c00b1090120520081000316551401c444e0400605105500780c01c032980707040c1d0045c04282c030750180c1c045404642c074010711416003007120f00e06200340000c00159200810b40400e441c42c2c02000c0c000c54100301030301084009d860b0401001c461103401070302e00d4140c0b240d940a0944105039405d4a0342da00c00720b42d47c3c00da113422240c1301d4a940c00864417103044ca2060721030625400c200a0100311502080c01c08200c2407400398040d681074002c900400c0d0038500c800e2400a0a41c110a4102441404503c0e40300c54030f0b071000c204a41e0f4658000c0c0c2100c0c00f9680e80881621340c5225030300102c03035500c01c85151051051048600d14040c1c400c400400c0c5807510901801001e8a850390400d1145520420540c514000b45c40107c0e14004101d1a4441140b4800724015095004c0c0303034840c58060103800b10410030542c2c080451441803240ca5411400c4201c902c01c21864005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 940420269 1250 940419019 940419023
    0x141c02091206101809050a0503220e04060e010902063906070c050a020a0e07080f010f0513020d0f061703031603050c0d06031110050903123a110304 65
    0x14080f5092004502c8244588507880300a000400c200c0a0b0b80e0f00c842c50a1a0484195100d404c041074507280300d543d24104c2e450f1010340c0010740440c40c1c1005602c401740312000c1c100429003955581d05c0501c204003900a81c04042c0c00405d156124601002c00c0c0c010404600c1a640305c041d101e40242400051060000c01c9070310300200100b46030b5552640c1030f40d250312024003e4a00b0310400e0400740050b40d904444202078088004824000d0402c00006030001e1001f0b821003405c42440401030251764201d003410011200b0494655100c3c0e1655070100b0024420081c40740d040b5070801c8100308060005401180c129981a5803100120038080c03040f50301c81c001074070030081c80f080076211910700e240b203038020540107003040f02001d19145640e00c840d400c03030f5005e074800c5920140300301e00040189491b01144503422901d04089251298200000703840320410036524001102c089074030494510a0351005c0c4d002c0001e8070b001030241c0042c0605540c00303200017040000303250030800508581502c1a007500e005503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 940421519 1250 940420269 940420291
    0x110c04110f09011209050c100e300a05030c0c0d080901140d0c0c1101020102041d07090f0f18060803181903060902031e030703141c02091206 62
    0x6481c070280c21401e0703840048150f0421801903922a400c1d096442195529441107009042002d00b09090043d10303040f00301c01c1401c0c056a800c000c0b03200d44515000900c10b410004100d025400b1395601040300b01c3c00010b45c02d0303140c400d950b202820000004020329840049100f2112908403440c200406042e010070028203d4400348000d21055001d5011002d40d0321400500b607040410ba8440402100c4000741d16100007413003c8040000d00a101e00f04845104c1c0c03e20003945040c3c01c0983c0281020101c5801210350807440c40000d007081d204101c000040e1444040401549a481140f190468424007501c80883d480e9881203108020358400c2034111246000550f00b80341d8410304020005170300049031030b0450114013006400d916218040710181d8805c4400150720070346801490328082207078030306182c8041c102c0d5642540301000002d8030001541460211031169800014084a01521800100f0000c0ca00c00503a0103001d250068001090300750396500e2070007809112036684580c1070715154146 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 940422769 1250 940421519 940421527
    0x1503190b0601022a0405181902060c010203090d020c030105040b0f0711030c0d0306050414060d11030106030f060f0c080705180934050f0a02150106110c0411 69
    0x100c0e40c40d861984180d0500507a03001a00e800a00b281040c103010f41380b00c0130f0f4450041d1003543c3c03515116040d081200c0352000000d0114a001c05940c0e4414a94403101c1c65440c941d0328401c55641004540e886500c100003036451341090664940d40b41c48400c00c200c00360040c44140100e50405100707851156400c240d041c0095104c6a40150001d18040c05503001c001c03c00807460300c401d070301704002d280205620b0002c0a03402c3c0d4005008040301c0554002d58030560810780c0211000c0c8000030040c1e00f1590407a0300f440703103907024500015480d1421011a40650a01d031000041c44665810444018004c40c0c0c14050700c044071005100321155551359802040f26007020583c0701d440f450180c4405807002012041c5101c20900046116604031410342181c514040040400791305000184110048002600344031191400c015215000e00d480200540001140801000340308101c10801c1c1991450110b4155866090040403206801407014092240100c05806428244108001c441940749020b0038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 940424019 1250 940422769 940422773
    0x50d05070b1801140702062b0c020d020f01090b0705090120060411010305071d061c02130e1e060a0306090303051609080709090c051203070303140c09090703060b0c06150319 76
    0x44040c50341e40090180e8612a00004c0c40803241c440c4278003d0720141c0082c02e007042105002450002c1d2a44054020b034100b900b100c0004030542c22940c2c01c9065810880e4503100f030f00d00100c3c1c0764114840042002d0300043c2c00e8060001c0007080340b90245000307010224024046400543c182c40d0241c5031400010348400b0042c4210132028550f44170103e001301010302d04201d0045c00140d4030701902c20f243c07a081d4001060309860540340303403000c02014030300c001010030301e0907405112000f05100c91101142580c00001070199440080000c061030703100500300054401420b000300144000c550303060403c006501303640c8606000d20510780c12504194021310410f4100304603040506007807502103414500c1a08003081c60398aa0f0041b24451424000070f503154211414020306955100302c59070030701703900c542c14480302810000856820500070394100c00c0e541c842d143c003100203000310b6001c000620404161090f500c0c00c0499841c0c02896400c0007540d641c0507000030140c5542c6840798540280b0312140210300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 940425269 1250 940424019 940424047
    0x201061703070657021009050304050a0303080709140d0809130504080a090b03010501051812070f030b0604060b12071e030203040605070c0c050d05070b180114070206 73
    0x400d071543c8030f10390b501d818240c4c000c040022200c8200c040080b1201c0c40d0a604402c11910052200403468022440c1c10300b140019444541c00040320120704d80382c42d01c40042c08410012a8020729000e40b110b46102c1d506c1c10024003404080c2c840d90001240c030400020402000c043c8508910701c01402c0500207001c5035220041d540c03005541369040300d0004a00005e0040501c10f840c070807800b41031125601e110f034000040505086400440c48140d0a200500140e64403d046c2e80f614035220001d100d00e0324a8a000a03072202a20140c80740700d10881c00042810702c1c081c81c0b144116441001070b170170a03842d07000c100003d45140d0f00070000804400e010100401041c03101d01d94000100303041c004032050450485100c1298059034035000729130000103100400149114060b440302d00e903d0030018440207980d4204031132600e031154501c00e41e0725584220620070140b02e8903000f0000a03100c2130ba81e50721444109640c10724070070414046001c5446250a8684002c101c9a00a40c001c0440e07142080c0c0c0c560500b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 940426519 1250 940425269 940425281
    0x9061d030718090828020f060f06030115240203070f020f060c030d050f09010e10051905100807051903170909070201060801050903131a16030f02010617030706 70
    0x506229151640d24000c264480010680d400c080201c140003800070480c01280f800b055003140c0215030207640e00340d000c41f80104030544c03c14031180e504145600c0307010009003d8204600886645030582d0800500c10344500e11481031488401800000100c90a1090741c49005403030b009002a1000007082d001032500381880d0381d946800030603d5080066103008030307156400c6102d503100c0155840d0184014981c0580311a9031040014000344a10000801d2458a81070700105140d442c5031214046100d610792a641c0411010100004001d2498074542ca400100803522540c11309020340f40f40402d050601d105800f5000780c00c880389100040c075690780c40c04150309a41d01d01641c03000a2160444e65030741c81e150702c2e0082803540d001080c4142420411401c4400240400f80c103517004216000041050f11144001c98411014030100828800e0b4054918824020720406e42007059210504064201000003103100e096402041440d8844041541400700070100d107805520a0007440000764244e0040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 940427769 1250 940426519 940426559
    0x22406090c0708040f0f0f060203070b0601113309031b24160809100f110c030c06070206040309030209070c02060409020903011b0e1908060709061d0307 67
    0x60324024042c3c66800c8203400607081031041c0b07003211204004a524180d03099000c0c0110344041c030102464a24040d5417442800310080c001800000062030320380c0a4001d0b1100a8224425959010b52400740303a2031811002c0b80150844907120306004280c003400048510030032448004514000503600006120003000b50f03440c0841c0f0071649245a004010141c90280340c4010b450001142080540d03580245085010b220411030301d00e00b0000e02c1d03000010500c207070304400350300010040382c040a0000a01021710820000c076000003a0745000c0d820003c001c203629038214090703408a45405100320780300c0000b0381c3c2c00750006205140070700241c41c0800b003d5400a00a040c5028840c40c640c0c00302c2c0154025034408810b032580482c81900c3c9090078092402e6011010396000340050400b140500900d0a2083c0f850040e00440345520f1180c0843c03080c00042c01c0b50030100c80c91450718000c000c180802038000e00000410b01c00c510091109090b60032940080014007401c84103040100d44550100c0410036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 940429019 1250 940427769 940427791
    0x9060e0928240509190c050f03011104030b04020118140105030a020d060306150605040e0f060d0515061f120f060512030406030506062502010525020102240609 70
    0x1803203240344001105090241e107600101c0c0b1450011941c9040201c45c0d8020404103181700c40b00300c0020010305003401a03440848034503403400c044e0b60100307005110b141800300d00b0410018010040c08000b00701688540e2007682c6854950f805041010081d446034031500601e01d01c0100c0c0079035650302800107180d205010b41d4005040c84106600074050300d62580c4183c3c0d44507980d0102d41d20345817010320b062029200c0360402c0c6103032a180016a420640d00240858180d01c22500072600603a02c0204e0086425000800c450480c2c100f5201d4103a03040e026100a8480d0215040d0104180d0f50303404801c40d22005a181c0d40e014a0003c64100050501c40d0100e0010642c3c80d0300209180d501c441115180c401c40310002d546550402038080c0403540068180c40c420311040c0100d481c00d062108101b050780a004a5241170300155200603521405400300d03040300360705100380d21911301c2064802080d040d03000f41c1c00c40340340718025448015094031035040c0c070203841c640c80001159410503508d55504690004a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 940430269 1250 940429019 940429043
    0x60f030c1b0d0e03010f0e060a0e070503060f09010609090b070c020f120709060506040b0a03020f091c0c0b0f0403020d020d08032a090d030f09080709060e0928 70
    0x8001400c040000b4840c4010600e0f04401c02d0140c1424403801650500041c2c08108900e801c41c5485d039541801085481c02c10384981010010301d1091040304000c0401408641d19410402e8031346e07540c0407080706d0614040d803270141c00242c002281d000e8260400d82111410f82d40c0d455038901181c2e240c0c40882c090360003180c0301c3d140c030780c550b1142e40c3c00200c2c140741480a40f03165400c0c440a03809a4050740e03c02d602c119000d100500004880e9400c03240000a0750900681d20b001005000140d405a0328940380d124400c500382d4548203c096400c0c84840c1d108905542103075848500b28a02d502405529914400b0148000e000504090b4400c01100340014600141c044190351600d00760f903c11680c0807168101260340c10a90200110a031100a20040000e0b0814010700c02250080da00c1030406010443c424540104241c024581d400281020209580169840e038003404003500c600c3c03290345032042250001903080f003000300306004109110440d1007295402045451440041200291610f2288013 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 940431519 1250 940430269 940430317
    0x61107060e0a0c210b0a0212060909030406080a1113080f16090c02030d0c09060207080f0d050a0318080c070614030f190c030522210201090c030b0f06060f030c 70
    0x51058424500c4c4c40e0050b036910303234070380900c0c680c0074002d0556401000d1040c24081c0c0c014010007134601781d528078030f8104255900d074029040903050b03441a084c0b1036800021580003c10441807400160b42d07101c000c0b01c19042d5800142603a904106841214510101c0b909016801480c0c03c46283c0030220310442c0d09005842c0c03c898122103400d4000c0c4040b4488003000c1191079010b218070002020000e01805103144c1c041501612460450101003c204002a108141d04e0099120742c0c035000c0d20b880350f90382032007583ca090b01c1c0540c0a24000f0b40188107a06000a0040c4074905584c06c42100e0f80c480303411915510302c00c3ea4040130141c100200300001048182444605109520b00d24002d9a0040345a00b07214090f14840310740c10345190300c82d0305494040c1300480d030b140700101141c1807003028180b504800c0610490041041d108020013050a000380001803050348600d480c0158200e900c0650303140c803100c0811007248106800020000c10500001d40c3c03202c080000b13072110180410101c00080100c2c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 940432769 1250 940431519 940431533
    0x8130201110f010617060610050732070609091802040c020111030f01060e1c0b0403020f100f0b06120103060906090b0109050411041a060f07061107060e0a0c21 70
    0x264200b00c0c080c0720780041619440501b00500c2d034000c501500c0c1400789403c4010020b180744185035000e4a05003081d080c008101d8800d0420340c0040c0941e92103c1482140300e04800d8039650240305103400941e03080c401040440207031103511031943d2011406481c403103142c0d003840042c004d840c0301700302035550740c0c14580c40c1e042801000b10f01c40c502440380e0f64083d43c1018030241000383d070140d810380191800000729281c1c1c0d034001040c0005030740000000980e6603491408034584800d0141500c01c41c0900c4210303940d0b0a1640d00300080c2447c03440801d04c40c451440301401094000c04d907080c1c1e4402001030040010406d80da005c002d80c503004850105001c8071f07589411412800a902c07401185659a04000c240500c00c0c0c00403aa894049906000c03144188200f501c1c510400c0e40d000b031040e107000034045031a001d50000c0f60112540900184203440c60b50016801e03c1e0017a0300c0075101d150424a0102d02010041842c08400340e0280301a0855410003040828034a0745101c102c04558111041901080d09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 940434019 1250 940432769 940432781
    0x10c300501170d08060616110415030303060803030702030f0a032a030b040905100b0607020a0305060f01060206190c020c0a08070f09090209010e06010207170d080708130201110f01 79
    0x1a00c1562001c0c482e402c80740d02c0c060b840d090000030003d20f0f8040c00380340c2c3e48110496603042c00c0d10000e1034103608a410103020030300c1d11554450740b04e840c00d2450220500b44203445030440740203407810098103903192001c603240d08c030499031100140c10820441e2003d006d41c40142c6401070143ca0000f8001d0fa001c95051502c2c0806c8400410040841810491a607854018205c004a040e42d0900070403020b030340d4065482c20440d201230207141c1c588203101c003213031101c030f0541d20100d03001000310201c145d882c104961246070136110b01490205040000c5559800000c426000f0382107000680c407030362881c031200c0c401051074a0712441140100d41080100383c0c0c2d050442c030060106c030300281088600d84280300c1c2c2e00b1045030703000710030076810b080b803c9025a4401d80240d04541c0807c41381200c0d40d0b03805004074105001608002e40900f1035842407a0b040314002011301c203900c0203407140c0006484c1c0c4c2900340d8410800b16954001707890344022050040d4454401c8000c00320740030044846410114050310b0079114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 940435269 1250 940434019 940434029
    0x304060306170102070c0b0c0a020d08041d0f0103031b0b04050d030b180109020d091e03080a1b0c21021b0d0201050429181002010c300501 61
    0x18603650305002c40070a150184850502c454001c61811101d59030f52421001544107042d02c100000c0740d034080000051041c5401300b5401411042c052002e850b050155412034050808800e180240d14604000d24001c0540590f00b400520710290380395a0f002c0ba000b00748ca54000c0c10001d0389151480004a6034061240924800e101a0204404000c0e0040c11149030403c414803486981c201105c0d2080006520307815607070a00405039070740c40310301c05000161240c184010103405101c41e001c0207184807031100e1030080c3d100342d071255043d46485032240117842800d40782d000801d03080c00301061618002c0203041e046c64410382a2001607003490810317030008480d130400c00000d41c11080f031008084c504100503511201c0221500f403041a09030f00001c1290069000700414070130045010b0000c0c00c48000c1500040051040703403540c0c3c00003003502e0f400810714106018021038031070048003045401030050003016a41a03487d20101c0c114481c101d0140520245c1c1065400400900311540b11990b0148078040c4c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 940436519 1250 940435269 940435271
    0x608010608130203031e07053f0c03070510050106030b06040b0c1204060c030909020c0303010e0408040902161110022e0501030c06170f0105150d0f05010801270201050307020f03040603 81
    0x61040d007000d07410b106040700d188030b8803c030f04200c0e860b0803540b109d414603a050b00c152182032914007100401649205085180c0460300c80401c50208000300028042d4840d104c6c090300382300030b90741c0c0e40d010b8058980ea00145540300d5014801400001d0720f10001d01210f4003a0802c036000d41046295896295102c4d070030150028001e15580c03c107050300301c0f02c03085c010080c81208501d00700c02450360903240e000602400e400c1d0180c01e0080790601c5107550569010f400c40e240215542c2c1050b030345140c00110002d40483d1500a180f02c100d4041ca0602c0c68180c503c4141d4000d0600070305448034403000c525065101c9601164600c0c0190031800891081d5406144605841a243d40c2025400b401c411010521b400700e85070441d00b00003d001c0e485034118119803042d24003c034400010311031411907000300b42800302e1a80c9040c42000501c440c0b5003001d4101d641078002044207200c0b01ca00c041d81c9001d507021344400a00c03240107490040d403065004591110440c41503a82501807a1115411a0b115034020000a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 940437769 1250 940436519 940436527
    0xc02092a0903030316110709020a20060f0a060b0403060209011103030103051908070813060f052d1e0711010309030f1d06220608010608130203031e 65
    0x1201980000c10034039480010260034841c0000000f9540e2200500694901040381007601480c0d0107100e40d1000c6007000b01c2580c0031981c64844040094010001031000501c0c498482060807080445c0162007813154400340460382c0d90840061aa444042d00c140021607540f00c000540c1168031018001075403140c5405070391064144001004155102a0644c90b07400030801040020000944a40040214118100030058030b0030106002c0c060a0310240c00f4410009846070001200c201c0001554400c0e101d805804804490450b42c5008205490101d12a401146050720810902040740040300300005c1e0700d04614003044c658a80c0c0d910782c42e41c54060010919408002c00f004445407403610a2a00308181010b546000b401c034401038134a5424440c5c13003072100304540c501000c501c0384100f0281c4404d0380d44d04503a00a8517400607000311203910000c4940c01049191003005500d040321005d42c5d4400313603911104c4140c0001010844126031520007044200d06080400c444d0f10300f80d4000082007a12 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 940439019 1250 940437769 940437811
    0x200f01090b0f0c09131e0608010c09090e03040e061c03080123011d030709110901020115080307021309510c0c020604170d05030402030d0f0c0209 64
    0xc91000500050a2950148a0309866858114000c0c400c0a0075040c0800d846a0003075207046c0381004030b0652030f8007505100010403800d070150000c40d40744a440e590840603aa60f429284101c42e0005c0d40c401d103581040108000c6480d855039146d40051004141c0c3d10a0f5004403030502c00030142e40340440100343d2550040214291600c500c1100303210801100c7d90046209000074002c41c45a1090600314101d290251142d4a0801c04100070303091051080044441c10000307065980c0000c40054015802c02050b01c102d000c40c0040700c4200d40d443c80080d400c048850703007002043e00207041001c480070b13624032040010504401409601d10080c80141010955629000780400136400d90320250710541d54050036440c50002071010214a6410000707000041d01d07400f02d03621411564042d41c4151b0105011681d080035000d06400501020116494081d0441013500c0301d0008480196154009031041044503004004102c00305074107143c1202101c00503400a5034506043c0c49066a0402c0d070003290351 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 940440269 1250 940439019 940439041
    0x5010e0106180303080411090c0405040f06121217012601050601021f020405062106090c091306080d1d0607210311070308040b100303200f01090b 64
    0x2000d0111803401e0702c08001060484100c0150911000301000081d00000b404d1080d440800303165248003c21035202800c01e001128200c1d0094040c05100b14a082c0c82c00c1200040c51044004503131400e0440c1460b40501c1c0c440714079944000208030280a0b107008840e21890002d125240a000c82c4402c4c0d82010b5a101c03241d10283c80b09044081450703140038240501c2e60b07000544540d419019908000750445d0300391000010340501d90089400c0000400c4184d03200c001882d1410010070026005100e541d139900800901590944d8400042e841c20425071046082841d200440c01050745e0300821241c0c1d894196524040c5407000703040001d034602144410b0180d440c251400c2e40d52040f110f06080514580b611504074641c0c04104005c13000718038001e0324945c0203822100b0315800ca140b800b500c41400f0b0501504803001280c00301d8400c56a40f0014812901d20745c20074084c3c0b030300b66940d41c402c0e413091403140d080301c085000c40b0a040d01c0307a07140b8601021401d00070b08a020f80301c1d0061207110706002c4000703a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 940441519 1250 940440269 940440271
    0x15020f0408150c0315090a020d020d061805010b0415021504050a050601060e0f0d0c270b010311121b0301080f060604020f0f031e0c0405010807020a020901060e210105010e 75
    0x1421200100203001721124a4201c1c0e204641c0100c5030006280c0f5520040c60083c491892101d410380d0001c181244520303032560081c2c04445000141a200e0b00c4002c07003810071210240515403030f00c10207100900c1142200c8002e000710b0b19603401181d42d071060f00305113240c1d2414212002c407110751000380c181c0e040107000d1000c50300500043c1404a0410000c50000e84000020410640203881554011080c080044c40302e0004200041905550112080b1800c0c8032144503849004c01380d080101034040c65120b0310450300b5030761100d410035040c4214042c06004d04d45010300300103005941040ea91900326600c8001710300030b03d8100f0003444920181c00d8064100750b0001c080600c110710501226001200c1e030b500300e8101c26008041d09075a541e0b10108840500030700402c0c4543e14400c24104014194403500400a0b0740782600c400d03150303544102c0c0032607a0301014000290003071203050040113180e01036988110300103001031400f190556000b0040c00f000b5113040c900d400c0348c0c0d1924010040380503401689 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 940442769 1250 940441519 940441531
    0x8011d0c0910050f030a1208070212040e0c0705010207120503090f0a0b010b0319060b092b1407030605101502030f0a141c0b0109170a15020f040815 65
    0x16240625114800302c00e40c11261080901403501030b403840c0a0782c1c0c1e080c410040090343c4411040880c01c13200100402c0c242c022658140076114640381c015410108005030b400703c81d1072032005d13060740c0d50f04451400950070081003190b01d9074080c00824009540320480e080b1024071551748079141d180000f05a40340545030318031070078941c01c4840d003103021552140c1420305564134031298513074036100c488410b40408120140601c00a16180b404982280380703500800004d13404840c0ea04082071413040c181c1c20300c0c140400e004504000d034898030340040d10744801e1041101c44081541c20306a038075190711040e40e41c200c2d01110907100400080c064420b8030a440008003940b8402541080300c42841c40c4400e104d001c04200170301401030702142e2000c815604442c1885800300400030b141c44060340d00005440c0020419000ca00041c82c00320311424000710400005500c1e100070f0050390000d0700e076651580100c0121090fa160204a01c440c4042c000c0d00800c0103020b507a00508002ca181c0d41707031006816001d885 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 940444019 1250 940442769 940442779
    0x6010c0c0824011e05040902030f0708030a0f0f020d11010b13020304060c020109171602120a060b030c0a030303020c030f0408060f0702011104030209070905031f06080a08070b0403030608011d0c 85
    0xe0000d41650f21044d50658000b07070b07000030700a4041e00001c1d02d0180b09000900710745c800c0714004540302c600400581102c08060b158240304500321401a910482035414400060388441c41400b405031085400c4905c0300f034082e000140303030005c0d24003080300f11481045810342c0903000800d10040040c10320508600003802c1c8000c1000b00720603543c650041c4071108086441901c0840c0101500e4019503844038004d90091400b0000003114501c19159075484100391801490401c0101040c180480d04012040004007602c840a0941d50190005d400c0b00c1c1c1d5040f218841030010207101c45202d0000c00282050038002c202600c0c0ca12402410074400030200811039050841c1c04503004240c000f40c81c25070394100c454445075981c10104540561842d400703154913105110400d8103099100e01024241118540700f1300c091615031a000c0da0311400c2e84002810900204000c8000c10f0101410075081440381c5008940340f80d03141035030790a540d14205400000f81c10904254401c03d070800c9071a43c119001d0320b03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 940445269 1250 940444019 940444049
    0x90a1401051e1f03060b19050a1a041203110607050403030e060c0f01090b1008150f18030715141006110c03010510031703090606010c0c082401 63
    0x8101e0b5061500c054280680020500100d424000c440b00900840d428102e15403902c1c2d07560741010030290170310584441c006e81c4a000010040c0038400050000d9542c0608031011b140e1900d5820742448047c02c0340544079070014403000c11a0a000b6001040f510700a681e48101406000207681c28000050200410711030304010400000e40c104480c0c149418003100d0090722184090650b50801030f400010351015468491a40c0801215448260003240c880110204058888203c2541c038a140340040c095124650002074000c8410503070241c3c0264580702034000c102502d800070746542c00c0010210344150800c082145a01c0356403240f159100f0700c0780c0d8002000d0a20f4807080c0d0303104070140203a0f01041005c1000d002d0032002000089150349014000f000710745001c888001d03005034a8001250030a44911054005070060400e99001743c40f22809003e4980b1500019a80b020131045e049412428035100002d001c4001e03c501d12009006150524a24200e000e00d06100f000c16002a00190740b508 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 940446519 1250 940445269 940445281
    0x210f0106020723040c05160b011a0703020a060f1d06150603040201120e031312061409060a0507230c060901060b1e090603011502010b0d0f02190905090a140105 70
    0x24002103400f03003050b50001210400c08000302c905c0c0c42090744210718a95806010000c11501198a50480320449003008000c0c0300c03003141004900c554200540182d000d2541c81c0081203090b4001054038544400004080c0041075283e050f81d040b01101401c2c580240003040110759034040341100c084c0b01100c0241c910326080c1e0001e804640e02e002620816035a0341c0c1825a401c10810481d110000950703032a42c85660369450603100e203030055200310b8038a4108060090896a4244418010009540600450b41d14281d00400501000742003508100c1b11401c14480b4140b030402d41001d0a2510411564030703181000303160b00d1f180340079000c80e1079689088410805081d94400b9260901c10006a040c0d40c0e4052582c0c6001030301448600341d9021000100009110418038566030b40c0900a03002401110003c008004c10b400140c400607029440408100c4014a0052050042d020000a00114680d02d40d000300d007c031407040b242c1002c5075021180110602c1300500e05050034060300e1000b07004a180039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 940447769 1250 940446519 940446569
    0xd0b0319080a02011e060306060518130809060f1207090510031d010212010503101407030b0607120f0e300a050d0c0c0504051b210f01060207 62
    0x100180600c240482e1039442d40303200f90800ca190900c8484210001610590018001c140600c0110b40305480c1a100040f0f506000f08071030b0040006001844165889007a488250140c022044421190800c400ca41e80e9079440080d003420180c23908120f482d10340100192601100180007842072080c296003c00207076460b03040c0740091071000d180204008800d4103903507001d441a0840e5554a500102d2500745540d1504140350488108070100da01c2c900300c0211050031a00c2c0054040b15a4854034005081d980c0031340c02800850310701900c407510344200c03a1a108404288000fa07036000445030884020616449402005020300403210f41b81c628015403100c0f00d04060071a45600310740f41e5201c968a90000a000b2018215000f1003274881c44402807800414510284004031b5011084010104503400c0c5481110301ca8030b024241000282e560761003026a5400c200c2c0c4240c2c14148500e41541031301200f2080d10b0181c035600000304011f50401d00040e00700f000c0c60300700800880c840c90002d0020821 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 940449019 1250 940447769 940447813
    0x1b1205100e011d010e0d08070504060509010e0d0605270304030204180203030a0201020a090f0602300a021e0120031b030f04050c0a05031513170d0b03 66
    0x90500001d60341550619440c00b519a51004001e03404100c0084419880190010b48504041e102a1001e091521a040d19000c0c400c1d940180001c2051000707102c0306008800800c00d120050418074005601440000d0400c100d500b0308403140f903103030014800e074030700e002010807613141c01401783e001f016121440d40da40d01e014600c00640302c2ca0701c614400070700519030b410340b17810960083d013a20f80d0f4100112010f400707944490364440006099030300008400d4050104030007694000d82c007401004500c10507031081c000c0c0000b5612030019070324480c5401c9040240041681542c0c4e0b40181c001c5641d42010700882039104944504664180349850221500060f40301d051010300980d603580fa611034140000000300000f2801302d00380c400005110018000083d40c034071481c4550112004200080c0910001d12042d1144035050344c421a25120000100310443d80c0c440404001c050500c0032a40702c0480892400150014240d0006044002c4a001d409185030a400680c024082ca0482004040c95524 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 940450269 1250 940449019 940449043
    0x80c0405062205250503101202010906050d0e030a0e15040f0b07030c02040501032301150909080d060b03060a0b070b040b070e03060106020718110a1412041b1205 71
    0x540c42c000541d143c0255400814224001685040505003404c0c014000e0350080ea500304101070ba0340c5000502903600301c0a4510540c0c107954110110b442c00006554640243d1800c03a1183c3d04c0d0f03541c0441c105010030160500911581e80c9507050719081c01406018554a0030b0740120078400c01c021b000b4142045c01141c00c58420102c81650780c41d0509044580c21003401c4002d6015060000000c00d1040c0350000c910001c1c01504041c007031200c2041502c1c201c0e901108100c0088503c0b5000300031100f401d03442941320b5409090182d140034412800001207505640108047e401c010081c000399044c010820009012900100b5151100720786580c01d031340780300900041131040c0c1000000c4505210749600c2c186203070060304442d19561603c102948411b818000c40b18801e110012007035443d40c1d43e0040d01182450340c280e030b500d0441e14003c01c43e001102c4150603025207804118190714a1070078403c00d84200e000f00788003003084500e241911032480380d030350060110503983c84202003c150041510802e0301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 940451519 1250 940450269 940450271
    0x1801090c1a0f0f0304020906010c02130c0207030206030a0615020d080a02070804081e010c0903020f0904240608010b010509090601030b120a031106160c080a050f0301080c04050622 79
    0x441055519519442030700165030b032405001c62507140c0c141250024500882c802c503014041a40e80600445000710b0320322002e580412561502d420031011580f140158110b00d10503144015242e401091031948280c2d04e068150b5940d240820003c01c81084412440700d442c07000e442040806607000b0300383c0002a044101c02c03907000419200b002807000444005224140546141500000320061203d60402841100f54245034015034101d200e1030202050f00d40c020039070a400d0308030000340100540004d02c220b8904070100f035407004550303140346030103641c038030140c1d02064960038240c0705800d4070002580035040c04014425100241e44e84494254000d03000e10b0009402c0b041d40f00090381486000c80110140e0245410800515900c40c201e5031085414008646070392301c540c070403081c18800e0b4426000002d40c5211300800021200300007003460b005203260550038199416210902c2d5032081e80f2810344d0382d10a0a21401038103203805150361003101100c0216806001000d0f8200c2d04000011009050b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 940452769 1250 940451519 940451549
    0x408120a06090f090c060311040315150f030507060309030e0409052806051003030c02060f210a0c0e2101060b030f0f150f04321801090c 60
    0x41600d503201c40014549450140001024501200020828420162007040c400300011402034024010441d60300f0b60003041c10314051541e20344243c0e0412906000c041140c540303400000a030308001643d00500a11460071000601d5450110304c4c221302980020281410300510a000c04c0d00501c6204040d0019103011404401b5440e0003030500d0760b400c0030000c0018140040c201030308891411a034095200c1c80c410455a1982c0403c480311003902d11005001401819507140181446006465000c00f01e140c181d080096060038102409000369000c0000091001088040baa540c001c0c26240c070100e05000b94003845004c0454030218031030071032a401d0400030b84004d0052a00350b00c42c5000301995030841d42c890500002c110010702c400d80c1e175441e0059119012404140c2c1061843d0808a0000c101c044101c9070308080c0f1018155980d1184050b00701e1003007000401044041020800754031a1210019291840004409620340d514000c01603140001075000070b104100858240c9400b41209250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 940454019 1250 940452769 940452781
    0x16080a0801062c012d030605010c170f0706050c1222230609030406030b031b0103200739030609060b030a05070306050c2109031902060915040812 64
    0x18031803800000c11284014000c18544485c1e1243d0844520269020301c00966107400440306d2904011003d00000d10007a00a0300f2106004018403440c0440202c9600305071a40e15100c0c03c81c0e404803601503c0100000c1c2140340d0542800300c06030b00000e40c5003201482d141c3d4508500000e9900c4400030959207992101c20802e00d042800d10300501000001c4421a24165140e2910384d0428407411012a05250813a40c4a180102d0070720680712031005c1c00b100c0c5200c0f0400441c0a072001c031140f2405032100e00b0b07040b000303001100014078400e406503485d0b5010300c820b41c190b200d10b0150001c4a0450401c100301d81c001d04d40d482420441100d4210b240441c4580850034498000c111455080350b1601c1080c00007400c20202041c2075007140d0141c030782000241c0d42c01d40e141200384125a4080706020303240e03003908030700d07640c00400c01d0700701d88800200c2c0d0500c0744441d425480205401e08a00c05a403008003040a01c01c1c040100308c0070400350f01403c040c1c6040c17595501d0b100313005800059840c2c8144a00240c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 940455269 1250 940454019 940454027
    0x90e0c09070311130312020f210403060e0d09050f060906030c21100905150111010f150906050604080307031209050d050a080702070810020a02010216080a0801062c01 73
    0x404254000041c3d5880103013034000383e40d011007841300701c560f11900603104960ba40003041110902d41860060200302c4034a5007600b25620421480b00244007091001001003800e0b031007044204c00e8980000c058803401c41c400a408044a03601c02c6104030750000401d1036a480300c1d4107a80c0c0070300d016610f1030b0b201e444c0c04010f03400700c1c000e400380e04803a44840e090322031880d403941c02c119004560103001c00c0001ca49640004083c2c90045035844246c410102895003a9441601c4d41c80480c1510400040c000189085100c1580d001c0d2038480c05000145000307021043c030340d2041c00000d000c1100c82526040c6007208480e12800340716406070034029001105627034191143c01003c0419404004d07112a41080c0300003424070b07003100750000c0c00280008001207078140006884001d4807003050007400081d44650720503003e98003850070b03102155002c1c405408941280b5407404400b5102d1070421340c030b4940c3c0a40080030702105a00800c100f1240d440b000343d0780d04e08280b1070810320084107901e40c2e45d2218400162 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 940456519 1250 940455269 940455281
    0x20030a050f070f061d070f170a17042102090402090915161b020d02040509010b03070906030203010b09071b240506120d020715030b0d0302010b030601090e0c090703 72
    0x1505041c6046181401c00c24554403a5103905c907a5036054190403500ca21255403200b4600070085d0034030118805000f8051030203004074507101020103d590b00003059a0307642c0191101201c00c0b8200c000490280145143c40e2694003444990380d242414001c1c198000a01d0100081c0010b409020040040381003c281030000300341c0c28100c42c0c0e41e810310342410500c01c1c400c0700030901c8840000e00300c0144a0003c0c9a407107000883d050f00108042d180c1d00b015002c00c4000c14018010845541d030703501c441d4096483c20310060ac003d0014200c001101c0b0f146006150943e11540041880740301944200700e0819000000700e00d0300040744100c03013044016445c10140d54414490315041101408112185032080c07500858030074203042d106c1a9200c080402d0741592030a10298020258101407424414000300c0b501c04845c848487ca40441d40404140100f0310840c07025030700341d0050b5101c00641c2410308040084900400807003608101402030150141d4464021a4480340b00321210404285a103200c0c0c1c11403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 940457769 1250 940456519 940456523
    0x50403020c1c030e0a061e0e030a030c0506010614070303020f040f030b091506030a030c020f150d0b0a1505070609210e09100e04030c05011a0120030a050f07 69
    0x903200300019441003140c01c0100c0c54201c00190a90000c80c1c1310f82004181d0508880f0191281008052140c4001100b41000c203600340420079600d0070101d82c0d540400032440c50034000e448800507602a420000c0c108041600000d0501416100b0014104002802c03501d445800d4500161a0408d1401c4e20030144504d07485110280080f09001c8140400c04017a20702900201d0100c070142205500f03d4401503100300ea0702c50341038002c8000300c1e01080c061186c84040910090812046001d0781002072076504141c003e6828003007011490441250781c40c80f80c91201c8070304850440220f40740280b50100c0580100d124000c00c23001140e40c0041200c560060f1590301d50007525110340d04100030311944103640c80605540055180110008c80303042c01c1c3c0c2554000c130220840c1442c1e0324181001d1011048001d041101006801990f200125a082c4150425220308000c0b4016500031000010400250440c2c1c40c0c45840b0003003454000000008101c600c0a81c03d07042803915030400f610f0b80a1640564100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 940459019 1250 940457769 940457779
    0x606080c034605160804020112020706020d0e0c031509100218030a030513050103020306090402060a05160503070b22060b060f0409020d2a20160e01090905060a050403020c 75
    0x15140d0701c942d03142c00051013400071680e0040c1003c1c260b10111540c1809540103804940b42040705140b040e0990001c001c25800780e0b00140c0703040e000c4e1710302908a070034400910041d90440c1d8060002890b0070b0016640940c1601043d02c15400d0000811740c0350b180c2c001d003868009070300245100010181e8441400f1b800320080565996424504010341113a1140001716190f1100010104e01903012740300303507401680d010704040c401f540e896082c0200c42d0711441d001828003000344000742010303a54181d600306192144000d59100c0d42c1603e4181560840a401e00b000c0030b00301c0d0000303114031001c246080c440603008100400c401000c1c1e40814103c1c0700b50f54410350545000640401c2484054000304002c442045040002d0320000d000d03c401165041211139650140390324851200d41f04d0041012043c00e0744070358001c244c801841c49460010440c400f00750740440d009040001181d450364483c010541c1e04c1c1c06210850700ca9441946981d002480101c000b540d5401040c2410310801110842a2002d09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 940460269 1250 940459019 940459141
    0x1305010e01030914061008070b070615051509031e0604022e11070f050d03081e0f06010807020609031209030723010c0e1302160b07030606080c03 64
    0x44005d858110443d1010740c1c20101c2c903000120520005020411904422580c50400380c1540d2008081c1c451100801080f102c040c4021625980c3c800c5d0850700480080d0199540307044071340c189410242d11141480081e134022246081c0504089900384d80194122420101c0720301a4620001d100c0034440c141d24481442d0111480254004288181002d095030850f502d85589204a4400c5400da0088541025201000c500000e00942c40ba0313070051080741c4d544880502d16154020204030840300d122140c0416400d000c07180d40c0040c0880d4000c080c503c0640032a00d04810305c15501e11882e00c80c0702400d41da150014004001c18810f0355070682e072250b030481212400304400c07581240e9a50361240d00e5442d20143c0808903000e4030040d805c542c1c010b011b62041302e2081c0f040303070000e4000c40b042c0024900ca19042900003009076010320321890240e100001c0311410144010803280d07004044045102082040c003021151025139040323a403410f2400c00381c0300302e9074100300004c099070b8065460382819080c1d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 940461519 1250 940460269 940460303
    0x91615030f0623011704020a15050903010207081b0105101403010905160e250f05070f06020a020d030203041e05030d020c011b020a0b0f130503030108010b01090b1305010e010309 78
    0x20009403e8400740c2c1c410703c843c00000b81c0085030f1003042d00c0080d44a0000b4804010011142221000e02815801c00d10b01340b092400c0841d00366440002c084a9218000a031150300030300040c00000d00848000c001c1100740b914020030000f50103035003d100803031070689004108540d1309400408000da80b0900fa0750140014140740c64031803800e4003484074810306081c0065612031782101c001c21b40c201d44203102882040c0c24802030303c525504a94907020403100300211408181841840d119003817060100503070740c514500c0c009007001e4031005078004040c010018000416040039001480c01d650380c0d91103503e0301261800b603146100d882948034245001051a090480b410b50022514401442d502e207019110340310304984030380010740001c01da800d180f80840e50014211701c0300c0da800600c50038041454841c3c0e03103e0a213140c000b40e10942040c2e4480700b02c070742c555a011414100901c0411042401d1031201c1c0c4210103100400e0080c40d04028042003010040d038840c2d0030414403180c0120045003d0310003d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 940462769 1250 940461519 940461569
    0x901270914270a020d060b061c0b0123030a09170705070506034005031b0304050114130315020307140901021b0d0b01060503091615030f06 61
    0x101e8800ea003401400b031070042007803052a1a40c0028001002405a140259080003014803082c40c0560710640c3d00c1c0384141d90707030b02d034803000700b464007a102656802d100c5044080010303268013030381290400a2100d060034001d240b810340c0c40152802e06d00049d80304d82c0e0311154900204913a5030041c0400340008034900c0a90341620041c83c1582c042d400340d420564448042c4000340c84141c900c40344c4d076032071111001e100d4440354210918000c044603181070b0120740e0b0b00c00c02c01c00d20150034050300c0540001500f40301100f039061040b46109540800345003410311304070002e4840410008032410652000415440d4030031003910040207035038002c10b0503981c80810403040d002500200e850b000031031041000704101c40610303801c2c2c4d4480300c0705900070a40d0480581d40340c803c50502c0030607150000c0e00c0104050000c6c009004050281083d982c50a07101e107807600c01d8606d0681070003d1400b100d0802071040c040f102e03a580e0800c2d2680010304021500750f480c1d004a0009012962220303420350454404200d040d098 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 940464019 1250 940462769 940462771
    0x6140a0506251b0e0c07020607030e041109190308190203160c030b060a0b0417120d05040c060507170306180a32010608040f14070e0c0901270914 64
    0x900405040084c2d298111116400d005a03043c0c84022000e200c00c0d4010b24000c00100243c40c828681140c50808040108080d02d12507030071054805800300d101462401d00d40d507041c00103c1e10b42c0c0c510071071905c0e5880f4803000348a0b5060b0540b088040011402c03e5034000c00031074078180042007107448a00d040303003800c40e40c40700c450108480c030840080100300d00d4a8194000313800e03544a5800070380f070149050301c1040c4c0c510001c00100914046c0001c0003d032001004083c003070b0650851000300d0f55103050700d0b1014048c4480d030003040c00e01c401442051301069182440590308145d148401341d4a8a0318800a00c812101490226207420f0b03040c00c002c125411134210303404c1c4926aa0040000280c90140c500320406680f084050f4442e2800041004500c0380700c03502d801c40d0040002c4d2404144680b2031000420710107020300100c1d404207500b045020016401558042401c08403e8200040300000901c001e0050810b0b44901ca1160400002212801189401004900e90070003481349489090f05207004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 940465269 1250 940464019 940464053
    0x90501090f1b080a0b090f0106020d020312160c02270703111911100b03101811040e0102040612060902091819050c0d06140a050625 58
    0x81454120000d0044900624040300c039a00301c09068070341d401204030f9003140c0061011078540e41711503025040d40c90705803480b4024000184540c0c02e540c10048007a140c01d40c0e44200c0b00441d070040260800703510818a0050700402902c43d100c01d00c0394412020dd5100706055006940034080d100042629100c0071500c044460b14018030741c05950358000103604451b11030302c0040c2044810000a66400e8560946119000d0075007003002d880d5030748048a03458a1300740c00120041e541c0d00c0c0c0a004491404200e5004901410442880982c060784450803a91429130b2000b00380c480c921241030a1036840360401600003849500840d102c55490700c009080e1520f00001e40c142914148010400003174030700840b543e000000d000001d03a14120396a14070079940040000b031840e00c0f240343d07070002c043d0341380901c42c0100d40c02d0348601d448e44090b50303244003201d1281e800044c4111500d00c3d00806074132031309004c4013112401c5a0f919200c040d1031444c541118015603200f0400c241042c40b06040190010144030540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 940466519 1250 940465269 940465271
    0x1507060b0a08030a110109050a0503040609120c2112031a0d0525090f0209130c140705160f031a01081002070302150103150b01030b060307050703090f09050109 70
    0x48840280040070110340140001da40007040070130800c0f8000d2042d842d22403103c2e000011160010740f00e20b401d0009484089030581c100190401861340e2010085001d45500600c804034100d095503002550007261143c403c200580c2000d407030b500f800256180c80f541c2d0304135528010509040200500500d0f00c0c0b08900309100318820000c107a414070100c840c003d940d0040041006615080d0400c454080401c0580754425150b00c0c0840c1802d214042c080700c2c4100c1b99800350700c4480c94020881d146d400d007001003603403038038000b40c48460651000e0741807001002045140c1d078404190501a00349920f00d2022806c6125281e030000300640304054a0046a0282060b80800704031040f1082c0d20300d400b0b200304003860344a007071891030445450f40103007000d610a00440327110b50680808000ca801d404d038410b581d011040302118942035000c1c026007411200c24601040881c070103400003059400701904080401801091550400d8010000200a092407140907446542c2c0c075403032480074003003d0007440000b07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 940467625 1106 940466519 940466531
    0x708240613091109010902070f020603060406170f0f0303241f020c012604110a05130504110a05130c0315030503040503070503120301180b150706 64
    0x80c07003030f8007409010b0301400400c0901d02c0141d0226a11500420004000070f490741040181994111960798403916444045401070940740c2200c0440c1451141c0e044003c880012089241d95200080f00c4030440304150032a1030303020a4406c0d482001d1200594502d40d24409152142010040c100704a800c1c00d190303141c21148685c15401003d608100a0b102c610b5a0100760703802e24007415103502c840741103080210040b5000060002d081410000d601030b00c595128103020f0000c14005008400003032034a05118001c04095804641d6a124070112029070f00b8070840301000c42d8030007414040040c2c404c0141e4400341c0305a001417000c040d0388004100440a2020703100024502840c01961128205002d062506031180c0140d482a4000603420884400310b108aa0642d080300310402d401d0340d405861003000d0b000c642d001e40d501c02c1040d00d00c00000402d10014042c0c07a40a96014015 = true := by decide +kernel

theorem cover : BRFrame.Cov 940287769 940467625 := by
  have h0 := BRFrame.cov_init 940287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 940287769 ≤ n) (h2 : n < 940467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
