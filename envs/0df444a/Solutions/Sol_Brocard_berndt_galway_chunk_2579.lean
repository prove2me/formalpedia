-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2579
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:15.507795+00:00
-- url     : https://prove2.me/submissions/44908d78-ec87-4eea-81aa-b324d4cf8f53

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 463669064 ≤ n < 463848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 463670314 1250 463669064 463669093
    0x30d050f150109030507090b060714070501171b0d090c170106050111120903031308010504020406140307030204051506030408041a07080708130909030e0a0b1204060c0509030a030f02 80
    0x8003041313981140141072558200102070000e440e4403101150003400c10085c81002480c132100035008461840302030507100e400c203800140b9100308000418036084440c401d03c108071440101861840134030008030b40d42c070103240f500c050182124040141117040d14041c00100247c6054091f00780d440128000c110ba25202c0d401564820241540d071151540815000814190017000a05a040300141120b00b08016510200c484917042d800204059440b1b4052008505003030040001520700c540d07080d40403c03100e1010a954006c64840a48103a80700d4021401030f800c000079100c14204080c000c160340e031509043c8848158010b11500601580141403400b09180c1030042d40c0410398403c920354684280382c0c54001c01d0790089010000521030b10a0005410031481c801e81c0c0d00240700340c840f0f400c0b0111203003c0010010940d40006020700c2c0c01c10100b0340081006800b65441070380071100007407110501000700c6490003410405909841680025414113070003050354500c40c5c506a08852072014030b0b511 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 463671564 1250 463670314 463670327
    0x303060e0a090b1906030f0305121e04120e1c0c060f05041503110d0e0d020c060a0309051606020a060b040b0616050a02060f040e06091512030d050f1501 67
    0x40103803c0030031400202d41c6103159060604140650b0342e4011444907181e80b10252a045061000c5010940005003020b42d04004000f0303590012400c0101e17108400007550050340340000030001000d1400005c0070710065801149030601d48040506449405980aa9100c0d0000c1c5034907400e6a040080c0a40020202d110b03814a01d00209030ba0345032818689041106c0341c2e00c1802c00100814107465032008040c0c0c0318040f0240030344a80c241d0380462058058047c007410944080002c0d400c54200070041c3c6199141c03141212100701891400042913405400e0050815040c0d1802c0255050755100026500d40d0006480405602504040181d030001404000403685182d0005d0b801070700c1403000c0c402006540c010b060400b4016402e030b41c10b0b00d58540c00100039901c00324890100800c042410301c400d012201c3e003158480401c3d039a484450034210380d1062509680010f80e8400d0010700a1a84407170028011344001c04a00e0350203007da03060124400c6161403085490100d03142c0501101003082d0311484 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 463672814 1250 463671564 463671581
    0x309141201020415020f2d0a050327040b01050405120c06040b07030206070215010501051809040c090c0c0b0604020f0f070f11031f02131701090c121104090f06090303060e0a 76
    0x3004822207500c200c0c80800e1803039010903e00d1f8240916018100410001d0005084400c01c0072116101103040d820364031005a58010311900540c50b0104204640e40c0242c00c80d4103907001264070104040606210310310b051118144244c105102150010314500080080c02e9586e02c60340a40e400c640d80c1080880c3e543c0d40284062003540c0c0100010040d65000d00010040d441909040c2d101c81c900b6440400e162000c19603044030180e0b503182c0104003000070f80c415003003e039145c0e10389091030202c16181e102094001a029030321456000a01205c02004101114100040c07003040f10746941060a254200030282d4400b6902d00e0709442e5401e501c0d181c00b08540400180b031840c1c50705000c0c01c400421000b500300f213410082044841401254054140d914404908552000407504041034075120318032007940d90000c20340007520036801c80004c8076409005c2c4118000da900049440c5035041802d0326900700480540841c0c85c05501000f85541504401c041d199415032400e45900e03482202c40c03c0303d000c076 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 463674064 1250 463672814 463672843
    0x1021206010e100804020f060c0d0f0201050c090102031c09150b0a0f0b030a050907050607050106091406010c060203040f240b0108070504050904050c0612010f0f030309141201020415020f 82
    0x2500018014a0b207502e07c034450300c9005c0d00d25030424403601c855500e002503071001d02c000714070900d03080c241c0c85509010341c41c1d220b0031380d9440c907003000b102d200082d5072030040400e04586021040c511a02c1c543c07031a8418203285412402c2281c0c404190f10441c402004000840340c0214000303030011882c00800710340a002c4852002d10646075944001c1200000e1002800300505070241020020341503642002600041e801040000b803002c1c5481c0c04002200c202624050614004408118840e07800c001c40081481d0401e902517a070b50b60307900c4c0c42e40310030030b040034000c105901c6112140d02c6c0e115010107106494000d4403003001460301c40001501e04c030000b100c00c01c1c0026010081804a0f0900ca61181d420512650465108188250000f4455000040801406103801c2c004008418014204134010b01840c000798498508586008102a40030700800030440c842c00740c445010788854040903000120500210344854480f0124280000c2c2102180300500c1032450b4040c40e0784002c1402c0c0c402a07c1c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 463675314 1250 463674064 463674077
    0x4120b06150301170d0c0f0f02040b060d1509050403020a0f14100f0515090610090510260609040b1314060709091104060c0f0c0e04022110050a020c01021206010e10 72
    0xc1c2e4481e9540040314000b2600300ea200d01072f601141d02c0d482c1c00f600940492040100b0340107540b0346030a25002c9503a20a680050503c0c00b4080480e030007242c055401908001240c0c281012828020506143d90030194503034812420500072000c400c1c0d105800b5500c03840401c2c002da40781c0340c3c61602c4980f00c2c2c402484e4000e6917200410128034002c944400d001c041d6041c003038900380e500c1000981040c080c0c1d0341d800c007044107583e0640307a091026598440748400e0010040b4a0305209010030f2000348001e100502150b030800116100306d02d8204051940d545c402d000c0c00f101c007030000103542c030343c042640c1e103a0115044041c085a61006800b44003440e0101c0d50a07542400d18100701224140c40b00e10b4107860440142c101907012070110602d50300a0a80b4400901290030584107101151402010804d00040c018200880201d408240b9040c601a00b20f008103007030300c1c4c1d40a2103000780304041c100c2d184c9600c0080c0c222040240c041c0c0841c45014242c0f201c01e8a006d80c1814054020146800100002d01c0e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 463676564 1250 463675314 463675343
    0x1401091401200709020d0902040b03030a0807030c0c210306120206090d1704030f020f04020a0e0906030c03100b03100209010804060f020708070308040209090304120b06150301170d0c 80
    0x500e0303002c5002000010441d082240c3d207141080c100d0f8002000d440c081511a440c0d0700c154106400f51000c2c214050380250302c0c040c440c0900030900f080c0504440c0c02c06407100111039186109005070942d0980100101003545900550f862885a1012001c030200c0d0801c24002503101d5501710940c4220b4029041c1464910441c0030020301008028040300e51810f442614201582200c000e000518801c2c002c044c80e1080030700402442801110055114500400403c1d0072180c0c0606900d4030b069007601d2060280d200d07400000e003040303100c0e600650580f16940d41d4034860a407641141c042d650096080e180c1d0300c903200d00c03810182c4c0f04018409000c26103911c04200013840603806680d05080304a401410b1084554449500303900c40b103810343c00501003006000652030b03c6001140c02601e5000110314051602001d0064241e26910190003c002d60b4006219903d030b00501180041c42078035103a070340c0d41c0c48810080007040d001c18040402e12440c1709003014940203442800c80981c019210b03840054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 463677814 1250 463676564 463676597
    0xa17010501020307022b0f031701180b03010914160b0406050a182705130b1603020c0709230714030402220522080307030c181401091401 60
    0x1a100650032050841c0c1b00709040d0201032811140d1002403051010060b20040303803e00070000c001c94a020352403d500c6c000100141218528600c2c02c0c00007102c0d01054034400c030030000e401058066400b0300070406101800041c0e043c00303e4202c80c480d0305108466406500d8138008032250185000b2a40803178010000e03441003a020f02d1304181c48054243c04030352547d440d0500d030710031442d00344485448521040700d401d0306060329015103607020403820348150044585489100740001c01038450340c6114000042119982d10a80494008014450403102036640d03d00c0b1010090111000718001d41250b41c03628110a90b01d68a26409100d1550754211110074045200110b03a0010307100b01c0e80726a0000d203896403101c2c558801c4440100c5610f00145034503024002c06022403128140d4405190741c1004900050081c5003926000b2540740b80026030040081002d41d51100c080c3c0403002c0416079450300060031042816407450440c000c0c0d80b0180306540d2107003d01039100480583c6808698500c0f00c912820 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 463679064 1250 463677814 463677829
    0x5100c0f02091f030c03120806030d050306030c0613030c06081923040c0f06180e040201091a07150603021e060f04060c11030c09010b030901021e0a1701050102030702 73
    0x82d4480444144055044025090302605500483d8000d064800070414003c0540220a60a107e07013010b0440f0320388600000d80354411010f100c1c3c02e0110220114400c0c0d1410007040b1050038002c4d29a41d551038105421481c0d0018074481181c1c0c103944014041009842121164040c650b07000c98807140000f02c6903410041c0103075a0f0f045103482000c042ca00030b542c0300c3c0e051880c06140240b00078802c06007880c1542c000040c00360060424000d1024000004014801c00e440880703901c0700b41c0030030310b07107403480100e9006002d41d00404101716005483e286604518000704145071080c050181c18065031810380d0103039203080c88080e621000c0030161001103404c120000d802c40b10f0007804c207447d010007980b81070066040354001d1000100025125410400071265400b00c3c8001100202030211094001a20f0071405000b40e003501070300070001c610308400035019640b240360300006425150110440800c0c0503082000341d0000910f0000856078800d01d0080c00070306030350042e800b5500c0c3c010702e0f40a10034030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 463680314 1250 463679064 463679071
    0x2061206010c02060a030506010305010e0105060d02130801060b032e05062a1b03070f260304030327030503090f03030403050a110306070f0504060e0d120905100c0f0209 74
    0x40c0002c40c018000103a075000d0003403d1000d0303540c90008113400c05500041c12142c058002d070030401000d10061155556440903106c24045264001da40c2d0144900c80c0c1480300141da008a042c0d608086000c01c0055190026601c1045c0100e4020004040c40f1311500450340131400321185015541d1060105e4102030340200a43c2c04800c210068a00c0c8489005281003500b00700180c480d0460001c07a05607848624051410050403002803411038280080b07045112600d120313403484245106840000400090314190100350702105403912180d0780d0030003074480d01e00d02d909100c015143c0e5400711000c880d0706240505803034008008500f0840c03e441413001030808508210b6140c8030510000002031010000b40038079174890400c0c0c03c6101d04d0b8005040c6012405019501032095291000074296442000c1d28101c07100c40ca130003540200360740e010403900c90041ea4098002d241c4000722000158000034000304a035001d40e0203003a841d01c255400c80c0d8403d4281e400802c86802d0515810245c5010401c2e50707007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 463681564 1250 463680314 463680317
    0x1706060f03130f0c050a0501170f0613051612020703020a11010e030f010f110a0c03300504020a0f120b0c040e01150201050604060e160e060c010e06130206120601 71
    0x403010142d4840900c000d83c0404102d0328000f0600b402e00c15410f101c2c1100d0002e10703082c200307446c0803464181e000d142401c0c01085000640380c148001039a590f260031906c01c501131407240401c9030f41881c00b50000b00854883d24200030030305000c5100703030440c1e092080b10341c40b9400d5800741003540030f03d41d00c031181700e0001c10304103040010010783e0801c9503505124100b100102480001401c241414001c01555181c0444201407542403284c041c2c2250801c903606c0903a03a151500d800403038000c58036004499480c4a0440c41242c1d1880806450a82030b4004c0f0f0241d4000c17039568514590f41d60301568144854040d040c181da8070746030480c0000b8003000099070440d105140c4070b0f040580794100b81c00c000109071b1100d4440c48003001240d142c1d540a1081a400c02c6003903800b0b103c0603003001c1ca64201407102a20604510040354400c04a2500c1518014014640142a00da51300c0281010038040c215181c1e001803640220408126005400d1640081ca9540a0402420200700100070441000000c02d040d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 463682814 1250 463681564 463681591
    0xc030c1c0b0a090203101d040305090d08030406050411040c021203040212061306050f04030f0e0d022214011203050d0b040c050711010801031106070f080406080103031706060f03 78
    0x1550b4114540000d001c0344a0016102c0c80c2403000c0c0300501000f0780c4040150310540c1841b82e4018400c0a41940c059014144141d1700c0303c8182c00302c1e00e160007200000c0d00c583da0100c1480100000c94203c9400356014408891074015201c003040210f45140c2c40b270002507440828400c4541c5084800303164010f00050000b0818041d03965118203003c0c0c02c541c0380c07000c806004030398810406180f05068104030b4405000d031a038a0195805410300c920001264180700124071a000a90340e5422112102a40030308205815000301290301c0324411400b402810050501d00d600616004000319a8101c404140c89503510325440e860544140d4800a12a4081a00d9501145c0d4540302c90003401403d0130103560b0981d8400d001d0506e0827410302035009150410100100402c0422052103d43c1d1000d0022503c051381d4103080d01c1d017051306030010103004000800104001410a230858a20f80c103c80c020340320302c56201e40460054038080340c221020765010009002d290032115189000d03580c000c59146408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 463684064 1250 463682814 463682831
    0x8150d020904050f07080102090105030703021b0709020915090d14100e0304060f0206070f2a140601080d05040303080403140711120703080d020a09031205070203060c030c1c 76
    0x1e021454100c80654855008040324078a14604000020080603400003c6041c0608000000d001c0e10000c0c103070008040c0c0104552000907102090341040000c1c6000710380b10641d0b290304050203034100d90390703035449210140d140a030485905000c40d096118024170410040000382c0d2100d048658840c074461087c8200464500c038004240b2480018000c000300941c4c0f903601d0079030020800c0b01c501d0203050031500000107200c1d0712a04084802440c44c040d080070318489c8500e22418109110001c0500c0c4900b8110100030180303c0c3d8000440445000c010940f001c0707a88407201181d9840c02c58282d040010020002040880d2103113821541040c803070300c4d042d08a840e00742e404ca90316400801040d41d001030174418125880c9004084400f821130288040d203105840d5844145030750107002000c6140d280c001451001c4280f1840044019542c0709003c1c81c4400d0f1104001045500080b00c03c0b4024460070740407403d1010f20701d00b581d05c507000034440f4500d03203161032600300031075101007400e80222601c95440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 463685314 1250 463684064 463684069
    0x3031903090f050a1b180f0b060a09091b021005100306060e16020f250803031906080105010e04020f0f09130506010509040206040302060f1204120809010c08150d02 72
    0x2c601c2e414000c00040115525070704040ca00700d0b244c8015909101461103080010401e00c803880b40c03812503003a0000800d21040c01e03154000d044c0b80c042c525401940000c040c101507070814903030004d03508245006c2004900b074100c0b61501d800684540809a8001e4140c922900c041d500020350081041007800078442e581c2d80c0b140700790b64503504201500701c60f090411102c161041000b140c0700043d40700900a0b00c85081076071303031610350314a00d01043d04c41110038051100c0d01200190000c0000c002120703580c0c41c0400c0b840e4000c041d070142e948009400c010380000c07415014055141a107408285a0910752119420040c5444900d02c0c3e0b42e07001500c80201311581c0d51460002c82c41441c842103000c07603c42ca42e1030b042c0c0c00e0182c140c02c11841060000141b1001d600c5000039a001e4035415160596200c240015030368440c0a601c9040103281034020801080004481c01c51011118a403a100303000c4e00e88403401c81c284c2d01007107000400220386900040b040c175401c030b0310039a08110240004200030f416030007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 463686564 1250 463685314 463685333
    0x210090306050106050a030c031505120313410405061c060e0c0d150213090f06030b0610080a020a0905030609301207091d090c0d020303190309 63
    0x102c0b000c1840070404406c1503030140296686c44031140b40402000c2080c030040d101001c030340d001d064090001c50300c1d2a200d500c4208210b500340743c03150040c007108599801700203400c10791881c200f01048034060b001c1c1d624603100921074112030b40030b140d520300084d92090070f1000606000b071266a110a00143e2160389021444007503450714065400400e00f0400703034040910300302c004121580148442c100c604013280d500e0140784441c114550003d682c1d81d1003240c007003212510b141c00640e0900e1500c84902c11030720320366120703404681c0310710072403d001c3e42e47c002005120501c002e10400401c444200003004004143d004080032090760802d000d84d1a26a40401d1a00008640d80e0200c4d51014448602c994540c11081082e88012055034402407803800341c110581c0100c00407850245080c2c5c021800e150f0140060030060489000403010399041d1182c0d6260602c4107403000d10703c50040210a4603d41400d00402108c150081c000b10b181c40c80840b200b00c110f00c10b51801e5801c06596018201c0098400007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 463687814 1250 463686564 463686569
    0x501050f0414130e0a0201030e0c0a14040608060f060a060f08062209030302040f090507020a060c201e0c0d020904060213081605060304212d020f0d080402100903060501 74
    0x4014146170155200250440c3d510381c4031080550b000c180e004e0324075995410150182d5031608490304008035070801003400313003140703402220250241804000c0030540e0180103920800c0d040780da020041c2e50721001501c6000d02d2917108400210803000140b13203410700c0c40101e80101c640380314045140f132881c1c0400d8200d40180d101240002c3c1c00050401c5045a0284040f01420210784204100d08001c5406580c500034980014042512000d40d186498014546e002d07649290fa0f00e100c40071611906165240e081400c20880195001c1507030448400001400f40400c102c0036100c400102c0b2160208041c5240060003181c14580811074802002201010100141742a00c0103000101d4020092004030240c3c1d0846401844240104030114007011100c0003e8000340803185111400050203c86078030992404440c980241601e025401040d8040500010b071103a0030b03a00e00e11181800030b0345850040c0703820000642c4441c00701d405854070342c894250b03030f04950601001240e81d9a4818066030404d0f07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 463689064 1250 463687814 463687841
    0x7030c06021f0b18130b0c03061804030503131509030509032e090204140906010f080307080301060e130c0f03050f0907140103091e020a0501050f041413 67
    0x10030780e034075141c40003200040840078104040c8a00c02c41031004c9090345800d40950480f000c62480828110384011001035a000e401803c09500e925000740e407141a07600a50349180981c030441d0b0142a0222401c0d85039024a5169960a2a40d129400b0b6000055102c1205640002c4580309401001000d0321500050384e00c00d45072581c9501c5da0500b090306000b15281e04440807200b08131074002040541c3c500d05694250742c6000a0040c0743c9002043c020109546010300d550740101c1408900e880024013141264030100c0c910041689034100180c40c0c0c001c0b488010012070b400c4c030042c0030072801003400e4404110b0240034420701d58255109003059440012034140410750070a9901700e000d40c94000d86a000c900d134001030300e203400c0c040c0600f82d030790200381b0071940c01503000424152168880c1d0000a1b003190051020001c8195094000405641d942001c0340304071b0200c040004c01d0b5000f88151540400c8548040d41010f00d030103c48160900401e0105034091614004c4180e1308800744902c29849045c1d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 463690314 1250 463689064 463689073
    0x315180c0306191806080d090303031d06250c110f1f05040303030b0a0b19051608132709020a23130b1c080d0606081914160207030c0602 60
    0x81c0c2c03844c48200c03217080c0c0166804c4e8000035a140e00d0590815200400c0b25498070300020031030702c07001d00e2420f0046e110041c903485000e103105010030f00c603941c811800f541c9603410000700380201c2144103507141f54203144000d2110030312030088030741d500e040040f9103500200548243e0520414610110000c602d0f000d1703c1c000302c0e5012a0038400d250341172240000a5500703841514210f410300c0105440341c050702c103e00142e124011403200b48580306e00c2c140c42510800c40c103e41c44443c040d240c00101600030342e906032001500960000b84080303d5903099201d45040110390008043d030440364a015000e1114141d0b00320320725003000a003a60a400710030502c0094548445d602d50307a070804100b56544058804081c0505200004be0030b6521404a440711203407070503203001c1840003450400040e0144184c00310010b407505100081c201d412000145c40750042a02414001e500d114018040325440b00e50007801d0000140000c0c0030301c4100f442d40d0500003c0d40111001a0fa88c1d5403000c0e94800307280c00401c0140c11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 463691564 1250 463690314 463690349
    0x3070305030f0618040f140d02031c0c05030f0405030702090420030f030d020c0109021005091023090f03163602090607080304080315180c030619 64
    0x2200d803082ca4210904948403400d10040c42e00801c1c82150103003001e08401c03800c4101400300241415030140300704182050b5045498180406902d0b130700300c0946480ca000010512140d002d005200d15681610b071038441c0790454071000c1f41c200360414001c00865040c402008040c0160b6070308240782e8411403160004c0066a890040c040214450b4141000c0c003036030000f030000460080c044103541d01851003140c016102e1300c0030034a0318007504a6040203500b203039900700c28001a0f64010b00520445c4002e5a030282214507103c0119000c580c0c813080700c2d000303d003449500140100e03100000c008245008145081c007004410006c1e0402e000c0304820110003040b07400801c440113410b041802e1141c010f50314a44a54010b65000011400f2003040340e88260b80020898070076601c00c0d0a0faa8078039040010152a89014038001ca0b00750302c00e840c1d420504410030000310701480c09080110160401c1c4070124821780b0741605500d080e403c0508410f44c4a043c100c081c840e90030004011800074030b0364528101050f05d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 463692814 1250 463691564 463691581
    0x709060902031602030a140c0a0b0a0e07050d030903080d0605182208030610170c030f01120201020309041d160e0a02090907050c01152c15040504060e0307030503 71
    0xb1441c40f4000c20754109002805480b03412901b88800000704030349940d95000011000c40c00d11541e008000c0c40d0322940c1d03061244201e07140d408a4003050011301216402c81d25141000a4044076000c0180080d403a24014400518160040c10701100303102800315010391204001112816040d090000f6030188208000980d035007410980790303522031100401c0300014180c440b800c11f403000501c40c9000d10160018011280d1060203d90000e12400b64070f0700d000d08007019041d4007980166010748280303080e40008144902040300745103080364160011031400701315005020150040c148561030000301e03501014101c0380d05200f04014a0214640142d0f102d003030022810090034041c06440c903e900c10700602000e40c8900f1000c80d008551403c000f6100d140c0c40ca00c1c54090007091062a42400b07905000096030080d4108040c0d1140c62500720901480032000c403c401c100b800c8030001100a17210b0340c0401d40f800c02d41d21040c1c0090046a010410820f0108201c0c91548208000c0700000c40001c200800003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 463694064 1250 463692814 463692841
    0xa061413090b0414100b071539050a03051f062606030d08130615150320090102100606020a0c0e010308091c020a0e06310905070906090203 61
    0x354034462044444d400d011030f14034551901d07130103280d181070300005403001440f507908131004070321000b81c10603c10f80c1c44540d142d140030300b42900901100861400d0500e00c0d1056078013000c0d00c0c2c0c2425500c1e80c1c10420207400072000742001800d8684c0b0b44140d00888c00305e00481c50304d4140039001ca40c031403904988102e9040b00c1800400240d1619034484581882100e650224201003800210b10b00458540c031003038a0f4007441c442c080002080985402c1d541c0f003002d161808074104444010103c01810b0b0301c4100240d0980341d0942d01800c006003624000d0800c03078051409001052010b00c11150311031041d48040341250f8890300800301580c082001c00007000400030001c1c000e0301c0301c6401c01800e0b52640e034500c2d42d94043d05d198148581500010014402c040d1406030f90099001011001480e51790980400e98000c1a2050b5000f440006542c20b041c100500c2038580e000c00420a81100d0b10900c3c0800000b001061001c4078640981500001c5c16840360240c4405840310010040e5a4100900080005c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 463695314 1250 463694064 463694081
    0x1407091b090302031905190f02040501080307024e0607020f06070311091825080c090613060305010602010b0a150e0310110c010b01020604020a061413090b04 69
    0x420040001c10702c0180c502007001a8006004000c001c4900540e143c41802c000494403100d14500b030015001d01072005040704546101d0098078100300690700c0300e4066859218110001c2d410901c04441c450007070742e030700d0444103240071006031000c0012048003640c0845000715150700751008100380943c040c81030134003002e0b42000381c03070000700f10400b90074221b151a620300030301c6002856515401d07000c0001d0310808070780308000001c000100d80c00c05194002074509041e6180764103c8407043c0440101c0c5801c40e410114503102707407038031003050341d8060441200e41c1c00703102d0312500f0441c140300340c00d00d640d05d05c001103000e031600f500c0100303140d03040010082c00c441c1c030a0040c500c64000e20313604200000c19030101c04d201c440c1c503282c1150090008408079161400480c4440106454a18000c2603c0010406001d0000c2010000e0150303005242c012a550b810a84010358000d8854000700800da00448052000500021a00742080d091606282c1d074009145d00c2070192544449100c146460603201c0e40e00c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 463696564 1250 463695314 463695317
    0xc0c02030c09010e16020c040608060906010603290d0c03030804030f052814030c070311150123030d050a081b09060702040209090408090a080307030c0206071407091b 73
    0x556140640c0140f00704806041c945d00c10032400f03840c4030b000c0e20030702c03254110b450068000e21020382c1d2554039039070302e1000300d0742041a4002c280000c59440c2c8a40181c0c0b0720003101388003e1409080010303c105001150301c1c11642d00c00c01801215000a000b001000000d5003c4e84894095142600b0098000706548140000b00710041056054981c10300c1c2c114600035100025061054480e080165500c0c075113120300a145007408020004000704400051170007510030365900e02c07139210700164950343d44d491404034502c840074800180500415010100c0001c004a054452205110030100e0f050041b501c1180001800010f0003100035500701c0c000c0b9400100f180000a214504251024454011030403610712500c0c00094420030765540350169190503000804a40a9041501c2c01044640c884003d40d8000e64554000003407584c0c1c00303c01e07981140d41544130054421060742c01c000319503110034411a0440c0c0102501001004200702100142415175000115070054000800c5104c003040710100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 463697814 1250 463696564 463696579
    0x10b120d11031306031a180118140c160f0f170c15060303070c0b0702040c0c031b020a09090b092e0e03040803030c180109120b0402010504090c0c02030c 67
    0x603101c0b8050302e0f040116585441c2c0040c1c01a0010746810144816840301548000040d02e085110010358010a0403130300c0e14400014903841c240d0307c40e000e407604018880860002040000c1e51194020001c0c10100320707401420308040403903680d400100b03200010594001c83c05140000800c1050050201241501e03849607060000d0343d064240d0b034040001151208200510120308140c40810560b640c443c2d00a00280071680c4507020604182c010800580c07107a030a000070440c003d4015007a01d03424035003654a60700039600410f01220026140c8070205c0e0441c1c0b0101000844440a11139071100512850820702c95052035a01c9900d00381c0f400041412200521603000755145c04c01e00b840d419210f01b0f12011811910310884a802c43c01340d51b20408041c000002003020b2000c90303100910281e00c0940c488000c07420920011a00700202d0f0280417426030100701c0300000b00d000c0102031944144149841450280c841c040d00080e242d120089001143d002d628200461034148207003100340c4801e0b50f801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 463699064 1250 463697814 463697827
    0x30c090302030607030f0e03040608040b070c050d1407021203030708060f0f0d05010b0a03240501060801031e02130603140c010c120c0c0608070806101d03010b120d1103 74
    0xa610b4943c00360211051582c1c807000d8001d45051504034640c00e07000c2400741e9840e01da54400103400340c4800c40707080b0340c2c2000c2c3da40040c29440c002d4005889050300b0030001d0100c0003614800b500c800031401c107280100c0740c007032100078010b07500c00368104800d0101d20040c0d40c4a061804c0060030081e00a850035100340d800c03030b080c2c0210380c542490a02e100281216a0f0170b00e94030505040d801400c0c185032194000c0c5448002105010004130810040780025484040c49500d9450f00070448800707018078000660000e004101080d40c281c81c00c0e091031381c0f801c0341d00748002860380048c02d0041040c01d030886007900c81c80300700180710b010348142d440c001e0360001804012445100090149051b00c01c014500c0d0030101c5c11006036882059030700340031540496440181ca89880025105000403503086002031480000540b031030030043c407000c0c0e00c1084c603155001c0c0702d017003149001c2c03508a50340c007259055035071f4542902581c0d4410540000ca0300200001c1c060004c0224002041c8540c050962031042e0310030040b2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 463700314 1250 463699064 463699069
    0x21204031112040b0910020d02120702010e091008120a020d12150e0711070807061b05100b1338040f020703020706020303010b04050402030a09061e0b010f021b030115090b01030c090302 81
    0x2b10581802081c00b06660b40745501c0140d9170101c1c07054216030814901ca0400141c8070b0f1840030b20302500e400d0340c03c40d801c0300e07040d55420041d40709030f054010058205840440130702d4043c55115a50a000c0c4070080390314100c1e20040e0340310441542c8041503103900300c030900460b217402808a030803030310084c806015403d0901001640d143e0700d034480c0ca0300b000710000c003182c2c02d03c3d86440340400455120090b5007c0313070342c5001100040d105445c0722a00c100c840110749580c0d542c0398480c0c500c285041900300344940e44c0503056085551044100c21282280078a41801c543d5203900c01e2102e2804040c80050703c0f5200340c24024a8149541c020b02c00390f600c10001801149001c0c0c040c1c2d4103c9508445c050703541d68480082a000d08192040109410300701202d800c40e02511070b044458440d05420308000890440c001150081c0b030008800c00586c101e10241c03000790148014046150310007600108924103640c06000022800741d010441165640e482280150380c940a2540491650701c0e10004940c10f5800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 463701564 1250 463700314 463700323
    0x9170712050708030a0201050114060a1709030c0f0303040c14010903081602130f0c0503070f0806181306050603012013090501080a0302060109021204031112040b0910020d02 76
    0x40020403454040300408201041042d00c0240c820700302078075260070280380003a018150a000c0da1071501001d04071402142489002e940038030a150344c88054511484110f9160098080c000b991940400c111082000004101c02e446030b420290040d82e0b01d01c0c3c603003032451812005400441c2d5040001d0b04890251b80d0100601302a80e40254003150383d9034000c00e0408c3c11038803942c070080d00182c0035035640e8075404d0036074030403010b036032807500244100e090011003240d00380301c126818004502c00781c402541c00d42c400c0400f244d0010014001740224846400310b1070081000725642c11215105072000d004010060082c035030042ca0560081c0103070039140740110307030301e41c140001c8624a10005c61130741001110704000c40c0041100a90801055071201d2000c0d40f00c25802d50140c01521600300005400200d80c421511012503403000c1019540301c070b03641151726613014400c46609104a00c01c2c0036600300001c00400041003070242a0380d8507600d01d424000300042c100000000d541200c042d20140a4000c039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 463702814 1250 463701564 463701569
    0xc0f14190e0f100806010e041b06050f0d06030b010e16082802220f0f24090306020a090509160f08071404030507030c0b07170d09061803091707 63
    0x21005042e550b92800c8204030410541d2101010388105000001e03682d0202103590b001d00d0042c0a0918110509130a078040e0b01e80f00e105500c0000c004020590b00754042201400303c003584002e01041c1c0c19a82c1e12507800801c000e0b08200c02c00110b50081c0601101c1000f4495001c5100f82448c03000c0b8a01002e082c0141762950744004080d0709920380761041c0d079031203504607154032000000003080380c0c2501480500c0c4601c903004600402d41401c80104240c00c000000c3c2c0110b40c0b0f1a91102840c0c401f01d0900142c4505103c20801030003811000403000030110300180945016036680c0c15200e502e07050800075207002c090403001e00003814041e0408200d07030084400404824600306000385880d40c507800c0311000d00214990040e03540124000c0200b01c1c0c04104441180d00681c00c141040b511015156450302c61820018990024030203d00d56241903440580076014070040d0028207640075480c1d550607102c0d525940c1d40fa80f85a0800c0c0420181c005060720090f04005416014030b404101c28030340e490b101e50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 463704064 1250 463702814 463702831
    0x60d0f052a0909181509161a070f0b0403030e010609060605070209040203070506040605190f051c1514090a020307050409090807020a060f0f05120a090c0f14190e 71
    0x3a0000361080085000e40c0c0280b0070f02c0048551703910074440400c0e83c0c1242030720001c00b24019403030044102010440e00e501030301e1140c82c5004440d00014044441030f800032804440c05d810304240b1a000c154410f010324032a031300a850116540199100007400c440107070700122030700c0b41303440c1081c8a6540c0c880107a810a650580305407206071101d000184ca0b0070240e44c440341d80000002400b1500031381c04400f0b00401c41d086151403500e4240d06000387c47c010010000b001c00217406006920044019070071107103078003039110800622201c2c17a5441c3c90000c00030360410031102440c94020030041c100501c006511404900d811411400e00200090480c81030b4800d407403044d505d81d104501800061021900400d80c01007412000b150380b40405400385186100400108441082401c1c004e80280c0c126203c0034000030340500a65140021030008040400065a092a040101103148040e181c1c110000c1c0a001d02d03200a0024090200075070000c43c0407031802e5450400b0010428031000302551504004e10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 463705314 1250 463704064 463704079
    0x601141804021c0803070f021e0c060d0204051e0118030309050d0203120a030903090f030c031403160302060603071d07050a1e0e010e0102011a04020306060d0f052a09 73
    0x10103402803503000e84443c02030310b41e12000040c04001c80e04900000200c6005400b0f0716159051000003403032034480c202d6261916003003641c0030225403410000030510000042401820a52a5030105500d60710301c15003490a207500c01c90f401c50541e00400d8441350b42c00654038101aa130304543d0024036188080c440c1a008481502060302103540502804403402400042c075030f2a044414401000b61120150030380200d824608007182a0100160035401c1d01d40095000301414038555400151602440d81451140001c0c04210340b032032a2840381e007006a0203540200401d042c06c2c0c040500300344a03544104840ca0610020040500050300306682c060703020b040854440c011f01600b502d640c1c0141508158902c01443d26410603030f000241c1264440080c0d076811035024209005900300d540300351030f030780c9600c080c00e9641c0407600d4103400031070780100046d04172030500c5441c0001c0004c0d03803030400085c0d550b0307501c410400200380201c0c103145141e500242910559120b000152400c244a600403c60043c1070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 463706564 1250 463705314 463705339
    0xb030c120307080f040311010203190e012a060e0d090b0f090901090618020306060d05040206160302100509070e010317090d050a03020d0f09120212030c060114180402 73
    0x244142d404842c1c00c00b0140303980b0803920b40ca402440e03000d800101e0f0160448440c00354954400025034081c040200307208294248010000d590300314150f40d42e079040040d05a4911103502203281080040352130318100003011003991a00400b61500c0040b080c24581c0100031070ba01d05a4002c62401c1182d03602c43c21941d43d440c01c00c1c3c8403545031081d100e00c5034201030031000001d540e04855002c1021100d9400c09600030316003140f41030040e480306480c07140e8011424008a03035200469400745400502c02891030340b404445407035020055100170401d40250b004500c0c00d070b1107a0100d001d840c0e440b03088600584802410300c0300f0030304d0140c0306000160403500c00c003e080c64044002c2045403040a03000700580752018280c0b0782540d5a49040004800500070310018401140c01122104c0f42034042d510350300c4071581031415442d0310910841e03080c1d038061114818010210000e00062100c2c101c080050205981001e000e0841d00c80d5400b01c20340100c40010000744410f1154502d01d80065049413250300c1200c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 463707814 1250 463706564 463706599
    0x2208090102210a0309380c090604261606020601080601060503010303051c1518110319090b0a0b2713030c0c0b0d0f0614090c07050d020303190b030c 65
    0xc0079801c0340043c90b400c5082000e050821528842c0c0c0410100301e0905a0b6a41f1820841a0042480342c0360480400d1109001c400c04010340d80c4046058041c060409104031b1082c103140c401c48a403441c0252404070001d12980303905110310341c09041520000c0009514005006149100511002d001c0100c04174500c01604401031401c0000c01d100b603000d01c4941c503200329104500859209201c165428503940ca50440440d015100f84251006c568900f1b6036111544554a1240c02a0010903103540300c6003280050b02c19503913207000701d00c030307030f000107000c85001003405a0f940390308910059090254000030241098540c003290300c540c45032035481c40410b25103015070700c0c010080d078010030308a5852008101c41105c64003405142280420038003050040e0b8140d40102c0f001070040d202c2c036445100303491400e81041c44a6a030400c010340c00c1e203072030130101d51520313402c041c141040d940058000009000d024000341c0441c3d240c2102d011000c000f8a01903000203965100242d20741c90043e03094211703200020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 463709064 1250 463707814 463707833
    0x60623070311030415030608010c021203060406050405011d061c030e13050412020705120703062d0504030e040203151009090f0f0f05040510052208090102210a0309 72
    0x201e50308980d203664682c085e10302c6000c480300410b4002490500005a0813105001e401100e960079005025004011413131644d507030f480140070681250300c0e4200099a0b8899114041c020903814502c07880d03080348140c100179402000741210344a8000c0da1602c1030038050300050708101c194141004102d00a1400c007041d10004007020200c04c4503c2c0004004c1806580c0820300094081075003542c2c081d588490400110f00040c0071003100650001c4030500018100b54442e0030450307000b00d201c0684070a10303120b85d0300c121a403034011103410b611101813004040e0000e10404800c00c0803201981540360441e054a501c01c50681e070644103004883c2491103580c014980000500302152051084800c0d03c84890013400d0503035801c1b41160300d0580b100350507442c07520a82d80100d500102070069180355500c8800a4040540f0091201020501e0600e0000003040c903242c2091181c049940c450700e010300003a090042302d1604807070002c012101c5000d122440c0302226032030400703810002054145400e01404c00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 463710314 1250 463709064 463709087
    0x4060e0f281d070e01080709020c070308160302060c190e0f272a070314190e090c0307030905070e04050a2f040b030a050d0905040606230703 62
    0x100c1c41d0121141d960603020600b50703480e40111046031002c2c1e9580040c84400c1303d00b40b01d16a11500211414482024a0b0300100020b01200c030464a46940301c1c0c66464080d0b200441c9030342d120018002820405805011075035102c081c2405071803c0490302d05150690070030102c900b0f010441144220641541c2d640007440c005a400340413400c0310702901c06c03580303240031842d0003011a4540140000d500190880410480c0020f4020001000b0000000d030131200e4110f00c00440c2402040031000b541d13000490041c2c5045911180e00724880410020080d080880b030014040c040d400071000c0003505011082201d400004a280c002503003039182c1082c50400300e2940040b10720058a809000030302c540000c0402019006038500500503141f1010f1034484818090140000d5017681b244611500e0a0f42c0041c240d02400340544160005994a66080c402e040d401e88000c01c03e0b21105100380d081c9845144c0c0a0130060900910700d0305d0003810071421b01400502e180036420001074510401d4481c542207440d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 463711564 1250 463710314 463710391
    0xf030a0f2f0a140f100207050705090606070b0a0212090c0901030b0c360321030406110307030911010e18040203010e060109141302180702120403060b04060e0f 70
    0x140e00004030881a210584c3d0803400503d8801c032112503007503084078030031200780544c024001c05c0d13001e280000b4072156407001000160300c88014048440419604051b04e4405c180d40d100042c0c1d03400460501031107001d0003030659200c940c4461103003034050301e590408505403600414000b05e56030381c0300350700000c40c420041c048140c0e40d148120101580d5104000c6842601044828260420020241a070b2100040061807858202031142c0c294444c80800035901b29018000104018020f4041010541e000342d030000006913480790030030207100c80c0311140f600c004002d10701a00076040220000300f40c03070090408506202c61003c042400c540d02544021118040c1809803a141d6955000c444018840411085807080c800000140d81a2108480f80300c1254018006c4403000341c10b441d08030340039100804100651240c0395501c2e502540403030262005611170000440d03507407c000180015682c06070b21001c49520b50406001c4480d030028042c5610100004035401d401c14008520880400480d0343c038038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 463712814 1250 463711564 463711583
    0x3020303092e0506240904061d0c0c0307020a03030e09010e0910020c03040801050c0301061119030305040309081b1203040e0c07030315090e19020609100309050f030a0f2f0a 76
    0xd26046109026100d405030031202000842e43d1407100e40c5032035505414441270b550305d41c1d0021b04000d0341600600030102040d0308803410240960302294042c541900705070f010400c0c600c420062031070215211400b404954007043c000342084d440365540c0d501e90708035128682d500402c148000740e5003042510000c00d080e070300031312081c14907141030300c02d980c000c0c001d0000151401c07480c0b1407440f030300040c510741014031030030744800c40380701d40c1c03001c0b0024013018004804004141000140401082000300e48240807900c1e03c1d680c80034200c0170841c150f8007504175000503800601041050720001502240e001069800e0300d40d43d5115440c2c00c5004001180580c002c20340c522001203400811640801c803008911021a113100c01442c1d40c6003131074010020004d5102100f04504022410f0000f45004100a28100465009066601d10b424400025401c40450f807000c100e400710950f02c10400030602c0c3d41814508bc2140c21032070f4204000c079040c43c000d00740c0040c0804900d1002000c0001c102050380020192 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 463714064 1250 463712814 463712869
    0x609060506030f0102180618040e100e06040c060c03090902031005040c1706060d20070c051507020607151503061514040e0c030a03020303092e0506 65
    0x9001004280e406034064030850b90000c241c45014421502c580c01882c40346480c505030103041040b82c2e4412262040007020041003518035440303078040c44080034844000b0300500c2c1202090141110344811014603a0341c441c6003400086403400203648141d40c21454001500034040c2015109101e4680c070200c5450710000400c09183c50103445c10080d607500711410310100310701900841d02000d00c0540d0785448000540403500c00d140000c024981c4820080c0040391010101c07102007070705050408444000c80d400240c0d07800708000c2490140107820100c1b0120740f00700e0311680c1c00d0168010b0b480002e001700e400150b488203202c804400140700107107084d8203000381d1180141d60b150000c95844102d81907414240e030643c080300b07a030b4030900540b003000c940c91402c240e444080102030700449403490218050602d92820507201888204440c501030740003150343e8207160352242d21b0114035840d1032600075010023449140100784e43c00c40c2c203d159007110208491b1030f0309001841c6c4d6450303540190701400007803050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 463715314 1250 463714064 463714073
    0x2060a0906080c0a02100c121401031703010e041b03020904120201060b090312090a090c0908060f0f0415061701090c0909030e011d09040b010503011d0c100c0609 71
    0x2103069844642d00c1c10041d07110600014030314004d0f00ca40d070001d60454403001500705850303444141c030501503207090b2031600d0b9059404170882e030f42030740da015100c0703240300050040c80b040210640d050703018603164a01d903625020305004410409400102600402c00e1800c01007440e050a21018640081650120303050620300f4204002003852184059401c0280000c2c4200e110700907030320708040140280c5036109c1c40d00c0c4480355aa102c0100355034801030300140800d0b00100344c4200c03404004251a0100e83d1410818a6460701c0c83c010009000003003914100f015051420441c02e41040d840310f00800021782d460000c00142400790070643c008a0824846c00420300150411000030740201d10700a24541c440703100c54103031404a10060045000c8003005200381d445680f00011040a4000c48118807400e000004d015210540b01a210172008400602003443c1c00e03c5581c0c1c00080e66030a191540500940841c2ca40d9010710480d403141440740c0e0a408040d00401640700300542c001010005421240380 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 463716564 1250 463715314 463715327
    0xd022b021c0b0a06030b1306060905100303090b0a020a060902060910261005061e0310031509031707030b030a08030a0b0a0e2205030c010c0e0f13020304050a02060a 72
    0x3a60b1100c1c203a0045000300700d442c810134064a0700001104800c1d1b44030807461450601f600001c4420300c2d600d6200040812951107840e005040384c2400400d103d00d1403e000300101c0180d041114402801c020f07003c0c545070002012803050344d00400c0403aa0441034000200e80b80500401c2d135401910503141801c5440c2e001e4100003034140305030f00e1181a5518101c030960b051000301da0781000f1445914003030042d840c000021780604c110200350640002004c2c07000307540c1500250381007201c40200721418020421122000380b407542c25185d0420084e915901c00a105c0850159520980350058000c502110b01c00e401005001001030100c2d01c0340e17081c500e003e810030703803089503c544114606151000240f500600b00070459071616210000d50700e035840c0814100001a40070000354501700d84210000304248050701400480000014030005003180c06402062240f094510440f6841c10080d0280d440c10b00e000c48803441120f0058032a504e91603c58602401c0079000307907105038082028a0850780c00385 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 463717814 1250 463716564 463716619
    0x9060705101505030604150e070612060603020f070f02010306050402130815040506070f03090b040302060907080102031e0405010b06040e0709060f0e01210c050c0c0d022b02 76
    0x10410002600c410001c00208481c02911350542100c3c0100300800c458003170b0007080c441c1281c4005107011240003a24034010b0030b6448034002c12007030404c81e8030007602c2d0f100e194020300c5981825407814000040440151290f801d00074445107002030b0301415640300743e1201c8040e100c00740045580d01181058904101c0032071068400c0c0c3c1c400e07030340c0392051001c0a000d81030103185e1102c000c0c200f940740d43c00c0c19113210010111090406984035024404140c2140000d8021070007600600b0141c04c000d55000c4c00d010240d005490b035680100107200036491030005001c02c14031881c034010743c0303501c071407400318058002c0b143c426500c00c1000c10003003035800070300050303d000b0030490702c40d40301c4241d59460968180c1102003010003c10b00200800c8883d500440d40c4404416001c001c21503903000e01212403007103c02020749038001500110302c03149005c908010420b845013007104c0740b510780c80b080c1d800500c080300000c209108030540f0160000b80003583d05001e81c0083c0e070041c500e0035209004419107044841d500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 463719064 1250 463717814 463717843
    0x10b070c0906030b0118020f12060f1504091a10021e06040803130f020d030801090c02120730020610050906030a06020a0507050f0c0f0109080c041109060705 69
    0x100c5000641c040c60b481903600300c03540602c945056031318040703105460a4000846540a64080050001c0b1b8100440101b461020301c140304c040c141040c0c000d001c0d01400c40240e05020350410348241d0401d04a00c4280d4040b2504d400c000310301d0316140d4001000200d800c5410701d800c151011105100150041100801130b0505041c1503006040d480c24265151000e48010b00b20700010070110300c0001040c18181a0701d4000d00b43d050701c15916034042081c60540780340c1070300050f855000600001d80310780101061040c0500c0103013261050105c4030406807103043e100a00e81200840c00c0d044800380c90301c03a603401c8459022410700002d0480000b9465100032900414101d04088000c41e182c134040309020302070303400500100403400069071900002e5000140c03900510a0500800c2c2c0005c500b000103140504d0440c000d0180c400005007800100300703007601c0302810300ca281082400100000500345c04240421070700440c00246200d9200045e00ca088501d5410850000302e903014004c0000b8202000d802c030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 463720314 1250 463719064 463719083
    0x609010908190b1e19020c030a0305180705060904091b0b19140d050c3001060503040f0b040f021f0f05160831080c030601051f0314010b07 61
    0x5a034941c5006010302c04e00002003104901c04114005500078540303c03009131741c00340180740580c0c075100980346812815880c00003940303e00810030f80080e1a0b05200b25008030600802800c2c3c2000f002070060300070700d1441d40c001c941d0b0312500c3e018013801c030500c550810a84c036851410300d0f45070300c00f11120394000b00710928581018082c42c0e200c070303101e0303400c0f00c5101e03000c08500c0d810710030306c45480f07005450082c001242841c0c0a203c09207a00709101007001c000860a01500001c2d2450319501c03488410503805141801810720801012941c603842d0150344030b92101a03504240d0b01c1e85080c650900c034001010350440c011401e4800d450550205501040040e600c0721035000310087d01c100c4084c0318100801c89154295102c54000540d0600544501b200c8280000200d400d00d019100c01d80d030000018601c4c0c0002c03840c0070041420309014030191108181c0103042158104400301f81380201d0541540086815041d120324001c2c4640e00c4801c1d00c0c3c12004240c0d5007540d642c0407040140e0401641522180ea9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 463721564 1250 463720314 463720321
    0x50a03140705011409040203090708030c070608011d010b0c190b04030305060d170f0d020c0601050a0b041a071b061e05030103051507020f0a06021b060601020a020609010908190b 78
    0xd00c07210b44c0d0028251031641e280c102c00b48140f1011f900081d01c981362a11404101062001e000e00c06031001c02410002041c3c8030307140020040c076a00301a071049030f00010b0000031101c005140e00f101070544008840040d5640350b020700c8035140c90b1440c090480c0c1010159514000c00550105040c0590b00a640c10710003500d4050400180302c0304000020070b0f21703246540c00c03400040403001a100f1100c03402030490070550700d282d040003a44e004000d858160341061005010602d402c940890183c544d202032281081d0902d25101101842400700c0d01e010b03c8003250032010850741034011401b0001c200081d50403261f4400c8013400902483c021083d904030303038681070071000f4426425a0b0480b50004c0040c207a40f42150303407014400302d0141500c03045004480d035011040c0000c00180c0c05140c414000141d8514401c519105172441054980c070742500400140310310780c1e80c00189409843d40440e484ea90340c400c0000140c403000c800381d10001090007180e46262701210700f50b111901305401051040007964 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 463722814 1250 463721564 463721567
    0x4031106090904030f110303010b0c06010e13020603060a030609140c040e03161133090f01030b060409060612050a060602120307020a1a270a03030f0204050a0314070501 74
    0xa6181c0d01604041c04000040c0424450304032049480031905062075422030311150141540e00980284800084c00190500155000c00160340102104820f66102d8240b01050220540034464042c0c41220040003042013640c0b02c1c00300100540c1e1290040200b5200b03440c249d0600baa5250783c01110703005090070b0300700f0381c02c16000711044d941621001d18603004401c0d501900e103140900c000d07035030421580d400c07a241d40c40e01005880c41140d038003110643c00002520742d10790940079034801c0b10060b2042c8a50f1341c00d5154100c0d0303458880d90908000c030300300c0003450202e1024041c581c0301002003030424400180321178114100e10f0050f56900700511095a440c40352105880942c826140142c0c01003120710304000702940695040385261058940c40f89450b110309003600c0c840506812401110010f005c2180194883e01c5920981020502c3e4441540c0da48aa00c40c285000050245070322502c000c04400686d50407074014180003003041100c513480b420701d0559480b80d00110640b5115080c004209503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 463724064 1250 463722814 463722817
    0x1a011e0906050f04020c0304030501020f0403060b03030a050417010f0c0f080a05160804150204090c020d020f10090c030203071509270c03200913020c0706230d0204031106 75
    0xc51020f894041200d11201c1808001d40c000035035070140d8007050001200007032080c0000d10202d90416540380e100c6045081a0040701d03403c8217164425403007000070448040e00141038404a0750142580c1b601d41c1e0a40001501411300543d200c1c0304ca52601c1642224181c1082c400c032580d5042d030b500d50310b155a84512640480310169064488541e00c101c0000c9807a226444890b80a881409402d000600c20001441aa003040e0080020f0644a00d20051120303410003040d500c030345140c4018001200d0f130052a546840408809001258484540300140254640c2c01d0004633400f600300e95030341d6a40c04101030352250b21400d16002940d044400951003421508004080030f9110882c040c01202528900040602039081c1d0133054441c0710604841c600300c1c0814041d40c8035070f84040d54410300f800800441000000703038050060320502c000c1d00340d04000220503058410303034200b01d100303450f0301041c0d0300540f04141001c03203052400050140d11040b5a40180080f07074402c8400d2000c04c0b4844040010a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 463725314 1250 463724064 463724069
    0x40605070f14040b090316030c210c03020f0312040f080609030703080f0a090f15240b0a0c0c0b0d060509010b0a2003040b09030c09061c1a011e0906 65
    0xc0e40b4041c001444410300d558014113040000030101c460344080014005440070fa80e500699000c0c140207010061006610408021540c00d80b0121030180c0d465512a1040c2c280340c00068010719031500c0c0c1c51519102040030a8000001001c060307201d960360740f40d0001c141c0c178501a00d492402540f005c10f00721400042a554520781c19164036401d0754840018000d044002050750304503540b2a0f6821000c41c075041400c0660b0f170b0145605001c540b1151984600341c600da465080c071a401f123001280913001c0000c02c03120940e05812969551100c48510032250700510006c06072071000c00c0440003c0082d290001804c210350300d58020b0040030b50361020003918640c02d22410600200401c4007001a502c61710900100b0390421040c6c07220f620610039124a99006038021181c1004001070340c24091400708080408400101c90740000c600d02100441c0d4407040c0e01a0034503912810b014017004029070300007091121260b00e154002079684d038541c2c6450b40151010411841e86100202003000c6032035004450a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 463726564 1250 463725314 463725347
    0x1501080c120d05090a12030e0a0608130209040609061d06090102270406030c0f091104030302031e090414011e05063c07050d020d02100b0d0b040605070f 67
    0x2201c10b400010f49a42d031000c260710364002c89801c4041802c0c204c031044210314500035611070040c205001c091102c4a60203030440010311640b041000320340145150b40300310040d41550343c608503440e42c1c584880907281c81c10004204c0c60130000304501024580f02d206014a401d07600315003180d11130006442c00c1b445103100d075820105204a40c03a003040c0d00d40a299041c080040c000181c00c40d40c0751611400b04640350024039580c54948801c0002d202d10303001d94481c125600360202d14241c03559801965a1040d03242112001c1d51620030140a148100151f03101d041003c0c0003031000903580000f030003200c40309018800c610081002401e0384100180c0e1f040303007900c10280c001450b06031041c5005c0c42c04840d041580e00e0103042200000901c542804210a810740001c0041e038440882d450003600b031004100c3c08000715401200302d4040f040e800607070540445204480003550380003c2000c10452048074001401c00307003040d4240010845542c0c001032150006d980e07007000c1d410214408440d1206901c09121 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 463727814 1250 463726564 463726573
    0x7051612050606011d030f0606040c030b0f102d1b03020c21120403121107030b04060f020a1706040b0603040b0a0212090106061202070807170405031501080c12 70
    0x64065004022410002c407854a0b80e01d403022903800005c7c41e00c82e00035039200301a00107109000075070426000d01d00c041115414103200b5002d000010820010020014510482c2c030001c440d5402c5005285440e80c010714104100c1a800c1c0185c81d100042c0000c6480c540025200034009500c4400d405040d1007844d03256000e04004010882004040902141e1020400c441c817104880c0600041040030f044d050000c4500703885500c0c505224441c48400841d04041c03000410807005502004948001901da12410071111a1140d06215006011150030074101c98800601c08200d183c121000e4001c1c5415800d554010350b89200c188400c0d0b07640c6c0004250003007000e20100700000c46100b40c10b540710544c803000600b0003118548a030b441c26025103499400fa551900c06101c113640c000300b0602201e61031078096250201595602049110740b01d4041c00d00181c00c07116440c8a20316404983c01040b009044a69209490381002040c05080c42000424480e103581d0310354032300b0901d070f162015082210242 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 463729064 1250 463727814 463727821
    0xf050705060f03160234080f07060c030203040b030708062407170c0601030b0a0608060705030103080a17191b02030702100c0b0406020301061101050411040c020a08070516120506 78
    0xf15100b41413000b900e419406098601100200502c01400d00da419803c01032003100120300c4100000401c607001105103070400c034107184c8941c00c0040d4680440c1d01500d40f144840c10f007824124210b004541100c031800340c0010a104141da071010390140100303008c41c1ca0004001d1070ad400d41200160705060180520014445200410081d2105081c900b01ca00790480c9404032048501d814090240c000710740409001c000e00c1100c040034071a00c1d001c0d000c404010146403c1c14080980b00b8001440b0080203c0e100241221053744078001c1981d40b42c0b840d051554050400c03800c14800c00c100d00c41c8000305145006403488540c2400341c101d006600381c0c1c2d0007940c501001c40e000d01030800c0b100742c2c0d0a424400e002c015240043e01c0b00200078421400f40900584a50403d0001021846080780c40031140c0e0500060002041041168035a441e000310340c001044a0040001d0381407991a2501400c3e2074400300718001448004521608030100b06480e0003842c0b600c3c1c0c1c0c401480165990b01c090019030146000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 463730314 1250 463729064 463729081
    0x718031505063a020f030307230f070e2d01061701050a210c0602010f051608060111010f0f090c0803160f030c0b07090303020c0a0e0f0a020708070f050705060f03 71
    0x10f0b488018009001da00982c011900803900d0b650180e80704403030b81c40b0021000c40d9820488040c49100c0321382c010140411120b000031144d52084079015403070341c01c001d050100740d00c00c2d5aa14203211401840d40d00c6542050500044280410300348542c070040ac2080b060f119085a10b041480d0584800426507204c0500300300411700941d480e0036207040508084804400030420040c443d1004201a03400458410318841140c2c2c00e40340d011707055001c0c6103401c2e01040ca001d038003e01d10036884602840c040000c4450316402038003400720640c0d040052807411560050318140740d000322a08074011511401c01a03500c08003180d980c4a40f8a10101480541c120400001c40c1c1f100d4641e01d06000b454448035030071141d00c500d00b130414161555008145a81c1040003010b80601061500a50441d04507803858900700c40c10300012001000c0341e410188010002e00d0140d1503505413406150030a6849456068a1508145446140d123054516108000d0005110316001007110020040320000a0071601c071b6801c27 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 463731564 1250 463730314 463730419
    0xb090c0303070320070302030f1b0f030606010c02040b040e210c0a06090809300d0e09040f050303040c06020f01020910261003061d06071803150506 65
    0x1020348890042d05030002c0965070811000e000300704810007601020420f100b10500b1080321440181c002d03414bc50b885d00e1203580116900da4061028204807400c0c1c1c04510008000304106c800d9198860b107410782c0408009800a05803520815880c00c81c3c5200c40e101c4d03201d03c00387c06480c21800c0d4a86c403a4640381c0018a094000b444410b20585c19a410700608200280038100945a03052111140f81c0c41003611440f052380f4618a03e52203c09801ca49420300c20080c02d03031040041d41d50041042d000410100180c0030000d10b81c4c030760002d003903e440c0d081620380046444c1192295200520031034800e000684410700c21141c411200400c1004034441104003512149404a40396a1510300007000002d403001c1e11243d41d10405007004007010705401d44c40d0120884080c80000c0e40c00600380745a50100034800510290400703124100f2013038945540d130403000d044413180c000901110082c558010b40e0f40007600070394000e100403a803001c0b001e11010017141000c045950f02c1000c0150004c48407100d003800e0b80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 463732814 1250 463731564 463731617
    0x11103012d031a0403021e030a0e0d060204090b03060901060f051003020c011d0d05030c030c09280f0e040c03080a02100e0d08010f0e0f0c0d090b090c03030703 70
    0x8803040344069590f1542e00030b081c00c0b214102e0880072440d041204269051200031b90420501742100d982d0135a143c05556203020b040a15824410700120f10086650742c1045100503940c051825951641c448882d4405030151552a038082d10550001c280c4058040c05007209454454840307100320f510f018204040c03140b41800d00c005055080056510490081c0208014243c00c0c1c81060710204180e000071345890b800c0c0e9074000800c030080c01401105407040d01101e410010710b00080b6215441a0001034146070b814510000d4208132801422014480304043c00482e02c041d005840300c19522846034407040b01c101c41c010084030404e00d06000003290b400c042c204000051040316012040c02800904548480b07a1410310780e4041e0f0b01480d10f0a5010f82c070b080c00751008a002c11070b01450030401c05540140582008024100320740000c010300109800c0e240300b124140400d104031a0075060282c0003400a484550356401080010021400c001040712115039140c0d07920781014240380303981c44840400c403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 463734064 1250 463732814 463732889
    0x30601030b030f0a020909010c050405040b04390f1b0c120602070512090d030c0609021509030106210b0c04030512042903010b13030510060801110301 66
    0x21038035a41e603920200b00d000704008102004046070602c0c0d004000725603000415404040c2e042803203070726100f0740c04015074084540c2680d020401c90609000180034000405080e6201403071902d100507107a100c411702400004008102c500f0003c05040704685501540d010400466404201512001d0a40b18a180583d0080c0b0221500303d840b44003c000f8800c049000791030264010900c0c4091180a0140042c07410200c5135061800c0041c0300420080041c150b0050144415240b410b01071080d03d0300036092150340100459003880c0c008003030b1816600640e404500a610309103012580d40f643c0f10450541d16040341752510b030107055a88000400308020591b00c0c030700c841400000b001400801600c3c110490184006844030b0030a102d0456a000a200000e41c80c01c1c0d22060480c0b44045104890540b1011460303e99640c2a0b0100d15100034080d6200812612030219121141c1c00b46a01ca101a100703000c009201100070450742c5041800280101402a5001c80300312000b855403040101d2001c581 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 463735314 1250 463734064 463734071
    0x201060e0c03130b0c090439050c03030106050406031a1c050307081305091005060304141c021606090803180d1e0209060409111c06020c032a0d0503060103 68
    0x2960b5440e0310f004e80640c0d403001c4060010801040500e058080c03030301c3e00400d240ca006107120150b011001d0040b52440040340701008107503d40360482c86001200c803401060000c403aa02d59440e0b00081150b8002d21030900024501030807004086190b807560300074900c000300705080a17880e104000b0b00714040307410121014402003204200007012100609421003941c2601d6000b60300d40800e012610f4401006c0c800c4c1e05020b2641800665680e034140e9820980003804610789071403004c0090301e072004541c50151048000000b0840c103d0b40002c0b8600c08665069130441101d9031010191014082d030701841000d134206000740708a02011364103181071070740d00070806070351159192100d14841d02440e110740b4804000c80200825800d0420245402441c10342c0c0c1001207103c580c0303443d1503074985506058865a0501503004070050950402019143c000e0811980d4180803a04640d0780d1344080300030780742c6c0b1340340a807042c1c01e1b441c241709400040b00415019084c00e43c0790107800c4403c0d07440140b20b103040c90365 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 463736564 1250 463735314 463735351
    0x41b15110f1209010c020406031a0603060c070602071a0a050a0f0b0307150903150209100e10110f1501050319020114090409060504030503070201050c041406130b280201060e0c03 78
    0x2582d006100c01035000300d409079180b5184580030410740b031b070040141b403390b4003520911804510352011a14072a070814001600c5400c54501000c4500540248800c0349120310248462010994440c40c021060050b0802c030081c2c1107591841910405046c0c6981500070f02010482600c100911071644d1410740b424000041e142c0d0f80b92018000c07070301c05035500c15501260170140c81c10042c8102c1000389503410312030011030078040014200c2010b208280704200c0d880351920f511003410051207a5005800041c1e0354080e503400c5841c440110b0900c0b916109e0712800c0300c6a211107a01210350303501242c040e541e0030102c07449a0318041e015403209400e030350810b0360745061401199140c400c1500540c071903030342c40c3c0c1d0f6401c00420081c2590383c00341603411000c030204000c00034000b02c03400301814003074140c1c1c03504d844441200300040d0400c190303801800e48610004480c22100a0000c0f00481000400880c5c1070820311904c2c201d003220054080d0705940310413000410442c0a00c04083c5a00c14907208101d034241c40c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 463737814 1250 463736564 463736569
    0xe010e070605040e0106020724200a210503040b1b070807050618420103050d090807091a040603060b010e030303060f010305041b15110f1209010c02 65
    0x941580700300000350000c01c0500854040115a03801030800d44001c0a00a003480742d181003210020044c4800e00080c6442030914034060a02041603008681640156120341d011b095240d07000d00b00111141c1d1441840248011803005809066000380d544080c21582c450b030310003881580c043d1036918207070340188088505d039000078000c0031524402c0320b0712922005513207441480c068010f840d40541c842c03800300701d40c040b80b4001001c60204035500203008015007031224140b8504501412102c00881c405041070514100d024203504aa1181003201d0856094000032107075120746004d000140e8010030010032103400c1a81081e22200300314800000b501e007041000800b20b9242d030b4021104152560034804041d82c001080c02c0e03400c00d056001e10702e03501e003a04c0002c4455440c811401e040c140d481d8046024080c20402840440a41c09640c480c5681c8070200114005107824528000030f0804403c40d0300030320085581012124683e009210400105d10440c81c5a00041c80c1d542c1003241380d1180f0005039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 463739064 1250 463737814 463737823
    0x70806011707120b03011e200f03160c0809012f060106020106080d05070f030302160605040b0a0c0e010c060e011401081005010501020a11040b041d060a0506030705040e010e 76
    0x15007031601d40910b0514000d98400613a28442940341c0b02e80d2600c001c52080c106400464582c048003110002a03a03d001820703400c13030f0581312020081e51140414a100c0350305c01140118054181c4d4000a4030aa05441c0e040303070b0362600b004005020300424000080c49500403410720034241080c1c408103200c14010001e40c07041e20341c262071517405030f444203004000c0c0c0b5070280308000c003078240701700640000c40028901600500c141c4000034046130521203000c0505100c0d50544128214810b40c0204a01e010705000c03020308030990301a280c981080c008030388015403921401c07074102100e403918026101c81e40010344100d81000e60684142d0740340d079200d036000c001c288160640310821004002055040003851860085403511140034141390200600c02a0303000130f02c180c010740d0b000f1080480600300d5004580988401c4460030740250030300716811104441c0018010b841a048000c50f00182d540703a80c0760054407420745900ccd406230000350041c0582d060076007000b400c1005000000c1803c050680c001880c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 463740314 1250 463739064 463739071
    0x602160302030a08012414070212060a050a022a010906020c010606020613080301050909070905040812090109111c05060c09090c12061315061e050c060708060117 71
    0x16000064908030480d0002816405000343e913611120714140941c00c0e900c100601006d18060151884120040110000c200c8002c15805418401818071807031499545550a90b1510b100b1800e000001ea40420144241e4216200c00c070511182800300d0781c2000d5040307070701c040c0e020025500c400842001c18100c1c0010030358501e50304000542580781040081c00d111010348090400a50452800c001c00c6103a002e90303054400840d442859901c40400b806d00d4800280e220210160030001000180300f480006800110080084805140d032030481a074203c82d05520000c1810158401c100aa030030002003031600110f9108030000c3c01c200d507031241e510307003d0104c58017000c03d41c0c00204003200d03040801500780c0142d140040c060501200151b01e810a8a00400c054018008440d41c001c081c4025004600b4416200e0300c20340c04540c994030001c00c4803a040c0d4101c2d00d403220440c511031903c0e00c5481203c0980c452a00a8050b640b00c484003200d116070050001030422996280f1041404104582c0501 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 463741564 1250 463740314 463740317
    0x60c075d0c06020d030e030301090b010c0f1a15010c060b01090e04210c031d0d120e0301111309091a070c0506060108010e040303050c0c0706020312060d170706021603 73
    0x502d4504001c0c0b81210001e41d1404141c00d0203000719640702e0001c29a410f58101050109200f10041c1c0100c034111000c2502600c1143c80f125400c007072003441407020540c0000a04512071a41c1c80f00520450134001002c0e584c00070f0038900c20000818081d6020000c061014940301000301d0b1b41e620700b03600c200020781e4203a5100b82c000344521240466046015100d41c042e0902d50146100c9031005844540141807481c4640e4003c0c2e00c4098039a98103a42c0700c2c0080d031140441465001e2803900030212140c04501a0280d841d1042c0c02080e24080ca040d04c14683c020b01d600c07500b850500824202804500404a8070134410441c0503112140c89410a88540c0b02a230322403030700c2c03503090070490316003d4084e1010b4140315002005000c50700800404942c4140c2506000c501600c0e00c502c440b41510948103413401500a510011036410f6001c8014581028201c00084c1c3d40d03280c0360200580f980140800801c0040201e49107100659000082c01400c1e01a040040c1003c1c0c40d071080070000780e10040102d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 463742814 1250 463741564 463741583
    0x302030a032f2a0706080601120c020a0b0609091f1104060530070c0c05040e1f060627080a060b0907020105060f010507060902060c075d 60
    0x4103c0307108074100354003101c5907074000c00c0208104040d649504481c0201c10404c0380140002d030680c0d0003058918141303c28400108118080b4a0009441c0c01c074000080300c02e0014600820264030301001151302610b5408041d01c106681c07024201090103a00f11812001a210640781003110341da1009080101503945030a0780d1910455012048104840c800e401f0a0910120022110031045c2070b180d804481401e00304c80080e610f007030291002c921540f1940c4c3c01828130203241c9190b000072035a1040414103221602d04000c503c1070b45010b90380b550043d07400052012072181407002500303034a0380b10140021010020151200c490722b04040c1002000c1d5400d540b160809060760901000d030782c0e8801014402000700f8100200004c0719030780745040305410800c1c081204801e020540e802280c4c200c1c0c0c001c00c0142c0d915000a0000d1701e41213184141c8225001202203501110782c4d240c02d80714400c80c4031038910031550540e2084035440f819060032440441d148210180c1c0f0f03070040070392440e201e800380c411003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 463744064 1250 463742814 463742827
    0xc3b03060c03090f010204030809060d02070516050102010f0608060c0a110f1b030a020a030b190603060b1c0b0105240a0c0b0a060b04050405060402070b042d0302030a032f 75
    0x81d442d051200415603a05c1e0320422042000c19030400c1070302c40f80c0e0380859046503200081c515890207402008800390481c080c042c010701500e50410907034000c981003a0006c1c44503090b402d10020480d46144215030080d040000001c031001c0c2190020840d06000d0704003840c90f1707007407500c44074030706000c40303402480c00d40c020410348064529200d65482e030903004900800440000b507002ca001114541700040141203074170007181c150520403110000104481c0002c03c06030f6600c0c1054005082400140c5000705142051008000703950500703080841d4001402541c241d19080a01119a00c07000f5820015036049216640940354007000305002142a9141e100c02c45880c10b0000604102404219805191440810580710780700c007079a04507001110300080790358480c40481e01038412103000070a000018020001040040d0b5020385000264900340d80c12001141c00d094101c83c2d05204c003a015920600a05850f00d1203500316542804030510140f08a810b00c000000d02d5601c0c454000c2c07080b180200d40d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 463745314 1250 463744064 463744081
    0x150225060e040603150c02030408010c02151803040b09030106090e0313060e030a17070804030f050705030309060304060b010212040605041e2111150d0c3b03060c03 72
    0x91224604202d8042050354503650300c8081c2902c00740c410000498546142d120114001d005032002002008000e03c00181e03600c80094640703984040c103100701c00681012031240c1c801180000303c2004028001e42c40c0c03a0400608102c103400100c141c40c0c0c10b640b81e5030041a150030f5400b41d04c90040c5541e0081d503c0300b24011a100941e045500644100007030380251072400c0c0d41c002100003001c2d40000100e13020404403001c81d0000d1048120103480000001030000c1000714061070415441c0c00340082c2d4142e1500c403070401d038a80c46144011380c6e2080044c03011030007150071a400304c0046141401103070703c1031829011036441500b040d40200b0204101003403c210409003544e0003c0b00100c10f01020720002d0030800c1d000000010003802001e80d0a0000c03025081203000d02a513040903e00030110203810700600c54a0800d580b020146070f10380350030540c1e8018814042c0e5022510241c40720545030002d90410341cbc0c0081c8030000481680807071040764000321162800e215650140c3e01207600e20f0780e2841d0101c071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 463746564 1250 463745314 463745327
    0x8040b0f04050c010c03052a0d0c0305040501120e070b0d0c0c020310150f2907030e10140705060906060d030f120209030312060a061815022506 63
    0x544080c0140020070403001075004910600d604109081900e070504183c1800c48542c051a08030041805015110000b16070100b0700320307035a501c071480c21249101c0440c40111207102c0d0b4840c00030007041c01408180901e6010304040c2180d01c0e010702c1c00284d4046180915417802005030b003c83d4120b880014a41400c81282c000d031000a0301604280c504039003190301003030340c1e030035102d10005405549084041c08501d044110310010503100011300c20079915401d007400074007441c1c90070880e0071104080c031800060300c2401750b448103505502c4040310b00100a0074071078400200c58850041161100e078013150007910101030800b09000c0c1c2c00814492625145180c6030030405056180300d102c810300e000c0c3c0000e60181c0602c0aa841f21b141041800c0c00c81020340340a40540030300b0302d9140c003021a950506440d202c42c02441110112003004045548140640d08000b04104040302d15242800600008003980440c0b000c0e030300140304503040e03412240c90309440b48254064400700d06800c2c28080007216400300c6c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 463747814 1250 463746564 463746571
    0x181806040e0304030507051203070f03020c0901091118040b04060608060307050406180207110d030203070b0604021c0e0c0603161101021305270c0903070f0803040501180b0a08040b 79
    0x100440c500f03411511401ea40b21401e200c0c6a100300103040b000c01045109000341d9840741c0d800040d50180380d00b50300d8007a44031900469003500803481c4030f00026240d41c8900510500d0303075901c3c0c1164030f09a070701c00000d040158091241d03a0095102d001065071030722544038500c0148410b80d1004140d0500303500b0982404050307404079216508200d024002483c440451207441c00017440c005903900713410b18240c19145441850355038171014600700720040c1a004001400305030710941c0300c1503541c1d480303a0400c8128013600c1a030015908903541200f000000644c4490484424101210401d402c81c0b000a512540102e03004015000081c0f104200700360005440c5164110b000001c0d810001c0b2400c103080e8900203807003018403d06100740301041419110303803a4111450181503003034091808503038158442d0310074040c040c0248031b20000090858160300c030a0301541c5580340510724052900c4011180303041e0560406001d444d00c07903800500d20140c0340052801822a445003c0d40e880c042c1400c1c50010b2006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 463749064 1250 463747814 463747841
    0xd090509060603180a021302030a0b0109030309180204051302070302240406110d15060905030606090103060b120d020619021602011b02030604061d120a0518180604 72
    0x25000d0108541d510401c0e81c1d131210303040301c03507400e409103018890f0b25126006101a41024000d0820365a51260780c00075442640b8040c014052448510011036861805210140025403208824002843c00001070785d420981d21001500306901d500000b070302c03041102003103520a0f070700050110800d40c0600580c1c3c08809425844900740c81c1007d5407100c080e2f00144014140c2d0f94442c00c1c20003110580f07054072001050320004024003a404644426104c11900070080450181d40340050036240001c1d80c0c502ca40f07000b0309800c3e007a07440c1d59194406080000412680620081400b00711440100000c0e0021400d6030f005080c6070030041100040d80c603000c3c85a00c074a5004001c0d4510a041d80504258065420f282603900460151030419486a100b00b00940c1400788006000500000d03400401189501100c001d03064201c41a00994440e2a41c1c0c0303100f00031000344941c0a42c1e900a101030070342113404e00142042c0e07407110350000740d1480c0516407040f40c4807240c0b000d0140710b00f031070b114545078407410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 463750314 1250 463749064 463749079
    0x1b05010f0923060421060b0a1d07030905032b02030105013002040815060306090604170d0c031b14090d0f051c020c1c03080618090d0905 60
    0x1800103004850000550030403480600000582071903c0b110102c4004203c10358560001030700c007020b403104903221040c0030340e03680b8148480b516062910100580440302c00c01c00c5040904018024945014801002101416a02c1c40e000340892018401051080580c18040000c000d08001c041440203900b440c040300d407131040c001804180d0f0010f500103404000c51100c021030030309244e03003900c081c80d11503043d180300c0f40003082c0010b0b050707400035070030a0b8004d4a00b80c502c800d55580c0c1c203240e50b40008841ca1100740d81301c01302140105600801803100000110000d900d060401c2c0301101c143d03095000c29030b000907a640c044030710210100402040925652410184a41600805030001d00458020b03d104010b502041b0042001d54804000d0b1960302c0740035114480b06002e00600304402510303403074000d0700520350300550a10b04400da44507401040800306c0314107203160b01d04858840c001822141c20281046030401003d05120000703109400e5540102000308000e04002d00307000c1a03a124901481c1c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 463751564 1250 463750314 463750319
    0x603020d0206181e011e2f0307150b0a05090a0b06070c2408041e080919050f1905010c0f0803090115080d120e010204031b05010f09 58
    0x3100815201440c1e0102c0d403842d2030740e072564000070001c503884014640c062400304082c000c035603d452403200c0c004030036212031224407088201001c61130a1344c040700002807810302c2e05003092251000c02042c01580034400000030740f10b2040c2035140d40c0c400030080c0c0b500441100c0c09004c083d250701034014468420750b01004081d1070031010031400400030307001800e40c989a03e01c0f00341030f454440540704280d0708000d200c000d83d5a51482100b404801040881e4540c0c0140151020180500706843c0616444440c1c2c03114072503444503031440e480000c1c000f12202003042010740c400f5680c1140c841510241c02d0b132043c000c40d142800300300c1c00410340388900e800740c88e4070340d4040da4440740103a0b00300c1120300a00b481e40d048141880e110f504c000c3c00b070300021b000d098003000307018107240154800c040540e502004c8407100d60302c070010550303030b1000031030701c1c1c0005a040100464584915084071440d901c8200015003466100e95628511804401c050f40c84104002000c0103d9031344070704003a0501055040030b090460 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 463752814 1250 463751564 463751569
    0x160606060509130e06150d020303040902040611070803070f0804091401240203091905030a030e150c060703090809040c032003060319020102031201140102010b01050a051c0e060c030f0703060302 85
    0x940046c442c450300c1e1203070000549252103224090801c10350013800e49039115150000304000303401501030a030019007500240218800002400c6041c2c81d608801142042d195580e04c1010003400c0034100c4500d50140000101295240a4294103000540030540c0a42c1800f200b42500c3c01000e05c0d0800100c2c402c05072544040d00482100c0d82c2103400c2e561007440502c01c0c08400e0440c0b59641c003294040c070411036001c040c1548030b008121500400c80f403c0015100f00220201a8014040040090f8101d500424800341c0264440c060311032082205900f03080e01c80c00014101d031080b440100c0400c0d11014840c140f02a5240f01401e110b40c0003160600318189080420b598496400c21000001004844d001c250ba00810030b890014040806040c115a10b0f036580f61000d04104440601543c241880344007198007d4080d128002d1007980c4441c28040c4d0320b0340c0c4000a64010303c20700c3c0071690b074100c0c0450b918800d0190922420300c81c112681c0c1d0382401c0c0c00f141e100c030000411480c101840c01c1c4080c00141d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 463754064 1250 463752814 463752823
    0x15180c1005071b1214150f160309050d090305150f1303020f010f0e0d140306010c060f0e0607080c03010f0b0918010311011101020c03040902160606060509130e 70
    0x941085001c2c6129408030590744401d0f0294200c49070a0f180c50a00c0307401c00110000f190801d10b00c9900307607800c07914808829480340ca8160b0380b8182000c1110001a20210101c1c0f0b920b509440c5441e020401d1405516100c0c1007003a81e10300000001c9030304c00709009101c82005814441e600b55a000195407801040203004500083d20450540341c00301c810704103240c0700300807000440c80414000c0100c908030020340c000800001b0340602d030701d000d94081ca6800c6c600070340b2000710600c4914260303450342d42c035540111107444410f0f4040303901d560389410100007035030148501c01c0c20280c0c40c0d00400603401c0100001d803007200c00400449200da07003000103014900450ba40001100d1401000c1b5071036403c04030000b414201c00b4038010070600703c4071000005002189194484012003a2a050901108801c1d028241d20661f900e48a07035030302c10042040035003500d03801030400c0c044141c00f00b0013040c01070340c2d00030903601c140e030000300003d07404076018056241200703e102c20350800540030000d5040003143c0984a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 463755314 1250 463754064 463754077
    0x1b2e1e0515190306090203160f060912120819060b0901030b03070f03020616020907080103030e040225170f0c070501030513060e0319020a11100c0f0515180c1005 71
    0x800c0d210400c400454a0410040b050744003000c0348c01c100e458a60b00c007000190000d210392000640b6121002610307a4140f001150b03816009030081031030006c01d02095130011b8014003000c0d1442d0759840901340005c3c1500c1150058144145265640e03041c1c00001019034507620031140c03083d000400104208400001d10030103ca506482c215112928651402030400c00c04002a4020302d6810030031500c503a12074400d40c1038903c29121040100b9003d000d10089004c5c0d280319841441d00c0f200c43c4030080172125240d059080c85222181c02010694129400030780003040f0030800078602060740051000c00780641c402800c1e0a2030200103915211424004201c849000a00b090743e41d001c0d9001c2c1424144100c0344910002d44424a0001c5404402561860444002c0d10365040c440820046c510f80540c50864498550791065001d00c05510f030aa10115010800c039072901c642c49503088400304c900b5a0a200d01091900e9000c1c1210100700141403918401c0121703ca030003100520301d21705400c0300036100c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 463756564 1250 463755314 463755323
    0xb040f1502032104020109090209060f0d18050a0c05010c0b010603090f170a090b1315022a09090f120a020312010b1b2e1e05151903 58
    0x5500c001454281d0540c0710700003183c420001c403a54000e0f600c200c489800c44c040d80c07003a40d82e40400d580d151050001c03800342d0500c040c1d00c480b08101c0a902034000001521a0400c9940c002a08808175401c0040c01050540200c9940c0c000d4007907081880790420b448801080c4c20b007092070342d04846680d41090560140a0b02d024559241420814032040780c1000d20403d40c03000d16144802107445a44020350000c00300b14001801444020840141c0541a036988405d1400c0f8040c2c441c3c1003001d2120f00c113200311407400441c03281004540101c040c40504a07450001d09006150301c0150394240001041c0c02484207405502001103c2004c48000070a00309124400c8011030301d500900c034040b401c5100700c2c44c14803800d0403480c1c0040ba80c0d140110041400075051203544c5060317040b5098440d00e800c00b40d1a40101c6241825848003111103448444500c45191307400001d84a81c09003c02c90428030707111303605d20b41651346c1c0200400055116191031201c0317000c440e400a004545000000c0c402e00c1c07800020b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 463757814 1250 463756564 463756589
    0x303081f051203072a0605040305070e070c08120402180f060909010906020d061409010b030106120204170d030501120f120306121505070e01080402090c0418150b040f 73
    0x1c0200007841030719144c45d404041c010020226880c2d01ca8140c81441c90058100000c00c000500c66000710111422640d120001e040f100c4d01d00803442c07400b02c50080201040c40b0180f1080030004140c40010800f008400a07100c2c41070030302d40140807440c40d1144901c18020604428003601d4940c83d12012307401031045a03800007139681c900c0307203c1c00b500c4030940090200c3c3c004281c0303140c040d809401000c1070f01c81420401c0b1100203084108400c0e00320078030804203500c40410060026500c54006d00400c06940c0c54094035040c1c0d204500202c41a00d004254450380200422038585a0b050240d10f0061540307000130b8082012070303117400100e4071217940c2c018418401c080e0204481806030300400001c048070750003901d001d019400d10329240c00303601d41d1840b04185054002a075041c001c00c0004030207041070f2345084081d50350354248000642c001e0020034000c00f06110010780642551745070408518840c0c40416403c042680c00d000101c1d03d50030a03e00c445043c0702c00e0050441e48075281049515913102031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 463759064 1250 463757814 463757839
    0x50307082113121110050103020f0102031c020304080f03011805060a050f2211030a0c080106120207240f0e12122503050103050d08040c09110d05010801060303081f05 73
    0x60707810100741000500e803400b81601306140c1c45c4c1680d11040c102c90080c0ca2030301c40c4408040049803a03101d81c104032070710350f031925207161240d00c1c59078040e50b8403500c1080700304d140c0136034070310580525002644040600600969400f034604410301415800038000d44401d10b000c0d041400003000003025441107402040444400f914030012841e0302c5500b811050420009001074204880f0254821600c00381154205842481c24501c9090114105d134030750707541c0390ba141c10f40e415843c1c0a94000b04003680c103525150000b00340c082c00055450300041c482ca03800aa007440302c04502c829a04240c00841080d0000c007480415254100b0448031405101d500822051741c980c1a0b61080030001004801c80012840c0b0718206250107900240c1a40d000b8411200307042d003400d4048402403022640100a101c140c1000c00014106801801600c0c142144c1d1a0410381221070140440e10243e200c001d1580d101c00040051507004071840340c0000860005103510401c206020b40d4424840c411a409403100004c40d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 463760314 1250 463759064 463759067
    0xc0d02040209040903020604021e0102060c0d0f0507020d11010203040503120405210901093501201b030f03040f02060906030a06030c170604080903070305030708211312 74
    0x450b1103048000340208035800c0b02d41002940c40b0001caa04a0041c0382d40000380801c3c0a055030017151210f01603004107d596900380d2210219004049110420741e03c03600100003600300d502902d4803580260b8002c0a01003d0fa1400809401c0c001d02d041556074030420502012403000700880b2907409941140c6540c50300c9a15140e45000c0a0804030710030702c210307446000d0300c882010006011301002681d410303240a8513902482000350a403ca0504058012181d403143d18126800503010741d0030304400000c04100f18201e8076207022300b09035410342c080c100003030b10400c010540b0380904d18101048000c6044ca1064080e60b00305210140020749502d40c101c007048210343c0c0c0c0104407003000c0c501801841d101c0c1050144c11300542420300044660b92030f22040801d5035003803a4440402c0095500040c9419140c80c0c45d243c41d16030062881d0354240c0142d030700200210b0000c2004000292081060030380d15260111820800071400a0601218045406201c0f4401c880c0240080150700400c000a82c99080c120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 463761564 1250 463760314 463760317
    0xb030f0405150f0a0b04050112150b150c0d050f0307030b04020706090f150b03100f06172401050109060e24120a0903050412150218030f0f0c0d020402 66
    0x4910004021203000c110320f401ca28403e003801985041e40600101d0280340800041d02c3d82405101c0003281400b000c880841c86003400c4021403107100b400052052103c9000c2004200f503038007003001c0180c0c0040d92920400b400c2203070384103184076894079908004802c05000c04034030019219404154075098032004940d101d60446041d1603102d003007000296542d240541205483e440180c1c1c00c1d01c0c00c001c43d140d4400b04ea0103056003043c002400f8000300702e000c0c0c0341303803008003245001c107002c40b650b0300c001080904020b404030090f501c00070000d06100c1c603450326205400e290004141c5107441c2e40d100412160360040701d0b00c0b0554503103041048050514502040030036183d0940c503129a010003003803150181c1544018039034004044081d91190341c65420840c140e5580420040024074104010002407891a0364002500d108003110341e007480c5621030010581c0c0101503c203601036a480c4090030285404c0026181040c609805030603250248000c1030b8a9444440003d4000c15152101d0011507546a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 463762814 1250 463761564 463761583
    0x307110d1a100807060c120305220501270210020a170a02010f050103030e0102010b060313020f120a060b100c02031203131a0702061e070507020609120105100f0b030f0405 75
    0xf021945034554501c0e0040860039004020343d00021000114040745109020b072234410608412141c5104418804c40b481c60b00d0784001c159440d550b121700f050100001080c410090340020b81c09100340300c129004000000380500c00c144159030100c0b8520000dd10303440090000b00421949060700c0d6691020b00781d01400481e5025250b0b54507050020040681001e103e04071400c00380d000300700c00403000060001c2c1d40300a80d04620030b1680e042c40710380149400040f182e2074600c090104a00340964903405850011005001c443c0107455a40300303c858100240c4c0d05409244a02d800311082410b900802d8a69001e545000c105d210b0000008441041d40f03040204103c1e4882041c43c01d84040c14200b60b900042943c1010060240e00b003c1425401c030250040000f0012155407e110340390a00161841c2d4401c1004030f070801410300480d451175075050b0006031007040b0680081902c0c584008807455900701c40d0001d1070071084100041c8800b50325032040d207a000112140c20380d0305480e1410814944044503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 463764064 1250 463762814 463762829
    0x90916180612032012070f030e06040b0414060a1e020f0a0b0f1b0a030507022404123605040204061701092a0e060307020307110d1a10 59
    0x1003540c020510720980d0300300c21000404e400c005102c60b48400f4401600024900b040c040400402c0341d200707010740c0c03052007414440703241060800452260b4101c3d60083c903e1140100701009000d020ba4900304520300201c80c002e01e0042007401c0602590b00401e004048208441682a00b07075008010200800d003c0c2421111045010b00e0003212450044480d02c0b2400e0480d00483c8000420a00c50300c000d064200119061158542c0c0c00c400500e40186124110b124080305144d02c101c0050b2189042010088031190900d000d0419040e4810050051030400900c4441604411040542e10400c2d802d101540700e1105100408559480c5d0725400a50f4800d20000340000c8030340d0030484084070208030309040b8540b03070ba03241d002504545042102111030600724040400c48040340ca01e0700620300e40c5003000403070f00c40c15002240154000300d45450140e0700014507001401040a4500900c24007107c600c2402801030b40c0700c500050440300c2809001c8800340200b600d81c035482ea6910040c0084 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 463765314 1250 463764064 463764089
    0x3160b070c0305031803010f050934061d010e010e06280314090703020a0e0a090f030906120504050a0b040218040b0f0f0411130608030304060501050909161806 70
    0x156030031088194011702e038511940c03a20980041c80c904a01805102e40e9450028004130b180005507442103050542444030b5a00100303007081c03208100b042002014040580d1000307600d480126110114a45070a0075a040c88034516404090784c0e03000d140c0244114066030541e03140c4084035840f980a106902c0e00049440e50481c00c20007036945039000c01030100001d0290a010b031143c81507a501c802c0b5600029400160101c0e05001350302003148400d130826600c0da00011b01e071402c4c0d210782c0c3c03a2a100d01030072070014140340010003a044d48928000f0310840136100408c82410169526603a440080c00000d02e2240d1243c0010195941d4050801c503010740760220034101d140030714014546080845a005200b01c100d404501035200c003094483c031596220070f070404804402d20400c0030086050a40d030610581750fa10201d1040c5050002d54000d502c00c5602158079414601000150310f2b0040210741c1c0c0d030303000801500c80400b00c50550411a00c0c02c000303074804901315690003005415903800c0044440d48 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 463766564 1250 463765314 463765327
    0x60915090c0e090c071b120f0f0209190c030204121502090604080c1008041a090c0303070c1a0702060a031509021c0b06040f0302010e180c03090c03160b070c030503 72
    0x12640024012103214010103201c2841d4005910000400c47c01464030303103451810724000040c41c690620343d005005a1310800c004016500290401e0011152106640c807016404008c000c42c2c0e00411806041504080d41040c1c24203103410111044504084c082603200080e88003c8222a81120710340900a410603955503102d507141d0395140c803001e101a009050400c5624070703051140071020b025590106066504d01b5012000001004018160340c03281d00807188050001e43e0200014010300384144018500180b5121a600381500c03403d80107580070204016550041ea958011209640c1d440d04000507a8030000032000d079107400a8010702c19031480051104101080b00707000300c0044010f0301d4180405030003041404035601940c45944000d0451090910056001d0483c420808401601c03880c0c040c40390000219142c0419181c100580000100340f207103801c0180502c4d090150164001c0c00000428a4204212200d81c403609045140c049400c02c200301c0c5140d00040195080f1085985a42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 463767814 1250 463766564 463766581
    0x2090a060f0308130902040308031611061302040501050a052b0c0f140f0604090905011b0c0b010602010e0607031817030a0b030a08030a02131703040603060915090c0e09 74
    0x40c8680180c1110130649007001450a26600840e015a9031204032141036495420b0180c00d0321041407010824000c0510516907092130405c130440c0321704d14054111500304d1090040c07108445c4183c0081d40103001209042c401511070307980c445007211680c030080e0b1701065a0381090b01c10140180d002002d041d0201c0000504004450105041d54410600c00200380c12200c1040203d2650030035060f00080b09110400c40300040b54420700c1124090400420340d400b1000640c0c458070185168030000c41c4040420006106401e00150302401d500d0008001c4100700f5001c0f6962490020012000c0640722107000c0c8181041d2261000d110390701a4141a80804002c14650300c1d800491b0307a024524a05440d02401e403400045a50000750009016451926121800c07406503201d002c500480c8071190000040c1168010b0100c03d01401c2c0c50069504d50382441402030544009512946400341400b6405110000403d4100300300c0303140ea800001c4942070302c40c05031036491400c02039603440001e2804016554 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 463769064 1250 463767814 463767817
    0x13020f0d0506010b030f06030a03120c0909140702060903070c03060b0d020409140d030207031202031b040602010203060f060909070e030708010606020c030d020a200f0d11030106060906050702090a060f0308 90
    0x49200d00d440c46c40990f242c4082c15551102c010000d00000c1d06014207011101d2181c2c40668102981d05c0d0124005407a0040700702550f03084540301c1104511b62023042040d40d070512101da08030f035003000594038102d40e135207070410741d01100c0c040034044030b648003e20002d036501c80b000c2d01d0004c2c0c0e0150044c0039400944c100f5a02d28200340d81c0010360340c0030b0442000181e920910898020b20343c141c0780c00010301d0b01d01101400941005200e92044183c4411084580d60743d540a080202081d900243e62071514000f400200c420240c0501d000340402c1c041c80106603a100b0299074071020f545800b0026655000001e032501506502100c4d940d440e080002c184150301092000081000384c08a5088082c6078804aa0766244990702410702080d06120216071200303003e04400100d00107003000441100c1c00002100800d0b0b08804852408890519245504003800369000404407400c00d0858075240c0308000e8941e00c58180000c0c0706043c45000900003100590040025000400c2840d034500d0302d03807801c0260f5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 463770314 1250 463769064 463769071
    0x140c010b1206073f020c03130f0b1303020f0f061b0c0a1d1021030305060f03060a0b0310320106050a0f02190303020301091413020f0d0506010b03 64
    0x40c00100115044004c80d1503485400b0307010032445489905501521140c0500d407011107002d041d0200030041240e01c041000d00032610b4000c800510880c605081c1c1403040c10558000d00f001c0390203002c010500181c40ba01c1400b1260150341540803c04c4407400612401151801164442c0002c40c1c04072402c0060300c4000e2841d10741504503aa4804500104001c04003240300b0340ca0102e030b05200075003142d210904d0440d00410381c8008101619120b010f009420195402500c011803840c041400616505005840d0405001e883c601ca0000022022036194180107000e401c286844180b094500d0724104407010030b1054080d401c01200d903026180c9482c0001a80300300c0500004145400c600a001e030407040e0490301c0a4444c030b40780c031501c070308103941c4c5a0510300d40900354081e124410003c02410000520700904ca030390b005a803076040017440b030204d42c1242c000c48560500c0500304a07580740c512241e03010407601100c040189000b14000030700e0400040000401a008407000080d000d0700d04e034040c501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 463771564 1250 463770314 463770317
    0xc0c0209010e09070e0c09101101020307030c080a150b130308070501020706050702070e04170705030307020d140f120a020910020d0201230f040809150d0b010201050403140c010b120607 81
    0x118180e5031245050817103020364a405003203004000700c10b00780c500074460380196169803d20b0034001a04110039800c9810440d14080440c3d1107075280700e1516880500c0302da2201141c2c5081205100380c0044240380711060040c0010803500003005100003003002c00c460020765102040039580c1c00b00d0f1030014041e42041d00101c801504080102c0c10b000e0011904200392908100181c90591b0355454009800d40444003202d03c0c0700041040c980801c205200562264403143c00810207030081c0e08004080042c00c01944055150a0040213120700605044581504034202502d86035100c2d144604020311904483c02d41c00340c944449a801150046a040034508071a0020071940300b0f8503501e401c19140300d170300c01001010103400103001c0030410745065420a0044c4001ea00b007000020100e1a42540707180000c00c116030114038207002c500c44d8050400900420310003802142406c3c0d401810791808441c031004455008140009011801d52044106210041210b000c100e408034101e40c981c1025140d600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 463772814 1250 463771564 463771573
    0xc050c0105100503060f060d080a03090c05040606121d1606030501050301090c03080a02100c0e120f060105011b1509060507030902010f05160506011e0603060312030c0c0209010e09 79
    0x104202419030702c1e038007120700c058081c0507196108103d4103d20a401490650322100310003a01c00400d1520000c1e2a4100c041c0c2c400103a101ca007810400103585459009a10030707428440c00b40603c40d484410260545d03444400850603102c40c0980b0800c4040d0718003001f1040c4140c456008000c1c0341ea0009508481142c0c86c200502d03620b42c0181802d079501d006000d803c580b200f290800001d0004030041001c1d040e0361040d19030804070001030005a40c2020003443c0000d600c541440340c80e242c1000c100c0307000e400100082c44407002e144c1401342c40f64030521402d810300403802c500881c2020004031071209541c1c411040c907c15244842c1c048014144104241c50084c500000514a580280304000a035034050b100c81c000791512800807966540412111102014030540080c00a04100550b0f40600b00e40c0036003489083c810b0301a1507140b60183c2c400300401d81082070030030109031600c2107809010700074500482c0f8191560420359012039402c1c0000d410040303841c000951600350b501d240c0c0c001c80c403c0042d00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 463774064 1250 463772814 463772821
    0x5030706020909150a0311040212280204120f030210020309030703140c0604140f010515040b0102060106080112061b090602010b0423251d090403021f020408010c050c0105 75
    0x711000713001984038542010482006001165110780c001105460041c000351509181440550b0903020982c0d500d4003030b10011003082d9440c40340004089032610020310842c20545005a4007040c0c0308010000380070703c480b80000805151003806a002003000c0e0100a5549040c0b0000650307981d4001c590560009091000b01e400d41054a811140c1c16105035000f4003a0303440703a84580803208200d407410003942c8100c070f6480150140a01602e88610010824141383c200b184043c001a07402c423400150448d007080c00140082a04680355505442e56141c0c01010011613141401c001d11a900e515040004500c030340400312030b8461103e400ba6040f9900a100d171900d200306000688a0500040e4940d5583d50242402c646a50401562100c1c0b0000c0343e00300d0460613000822140e003080c02610014514195039010300f4925101021456015030f1401800c3ca4282c03002234541c0c1002c080383c0071190011000c100c03a881141c044c1d4000e132038950000c01c2920b0112202814683c0b014072004419420b04002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 463775314 1250 463774064 463774081
    0x1003120305010311092203120b040b01080a05070e09011509090501060c140c0d0f060c0e130c090f080304030501060509151504030c0e0a2009010c020d05030706020909 73
    0x11207040781d41c00481011600c02c0607042100d901c41c018103407130306140d82100c48182961100d920012a07030080e11410303d0080d10b0070b091016525515580c6012b21705184480f031560741c3c000c2c21998400e21808001130243c485400413244007103118079696010309070200108050f4420021081b4411441d25101c40c043ea440c1e5191040e68424030481001c00e00b4480e142c80880d007d00000a44c040464040c4c03a680606440000c40500007501c041d0380d40c0c1c81c400361034400c02003a132080c1c1e04880481d0500e40d00f100840d03400501c0034800c018041c0710b0680ca4041e03511707505004620290203050b01d01c07401c50301c140e01d50405c50b41ea50014841070302c0355030819000242600b001b028440c015090f514562070644889420f201c40341600000407500d060303007008000045a500d2040c1405022003001850260500035485000d45a40402d4080030045400702c110380400410201c8081c1c02003801d05801480c0c0d103000041d1008614603018080b4040013a40e942003101c55401405844d50072106518552202c20b007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 463776564 1250 463775314 463775321
    0x11e02060c210411091501090b071b06020d1803050c040905030c01090501020c1b0616230307060e030a080f15030114041b08060106080604020403020d0b070e0d020904060e0f0610031203 81
    0x20680450f001d03c40501c0001c41560003001034134013030340c26400141e10300be040e00080c0c0040d50000005800c005130f60301d0690380c006400f40082034071144c0d081000c0e0640d01e41c0340d1100590540c962049a0740e4000200304041072080c1d42c0c03900c5c526030080090304118100a8080c3d400440c90b25070768082d1980703510b00080803605a070b4071100050041400c1440001410183c4914201c0641d2410604083c002c3c00250070824105000310359406192030b0440f9240c40b0b030507905010200c0c81960402e12181455540c00b50f007140d0701040c10805020291940010906468280d5602c6034144d400d111a454200c0c4040740d00c240541c0c4914551055000420740c44942c1340c1e10342c0101c00558001c8001000141e00c0380242c242c01c0b0034014801840c0c90307501c5c0e0008019070800c42003110740b490b0300000c00546a810414200180c04190385107181904d80e1307400074801260060000b0b120540d18080c1410040081103026203501504048921504125100d80441c0c0343c5480121000c2c0480008403000174440c0c003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 463777814 1250 463776564 463776601
    0xb060a08030706020a090f1203202d01111305010807050d090204060b0d0e0114100605030415110c101e090201020f0d030b011e02060c21041109 63
    0x1400741d424824640d03110030107507001e1544142005508000030a54444011114000344251191180201020310b0042d0048103090800c0704414062030903030146003000b060b1007080d440b8820200c0014004881c03640c107429404000c0e0031296182100c12060340d1060401810301e0502d501080010aa4880044039864401c46001c800248140700303c040801c1d884c0c110607205d0340300800208006440b1740a03030303a0b00c1d0005003403540915150b000031551200c00707205001c0c0700c00484040000c03e203840d0903a80081c0c0b0542c0b007102c0030004000300050034403481c90740c1e0320fa10741750808c2c060108290b44a11014950400381c0c59014501407201c4002541800f482111100c2b005280200803400c41c04000c00010584500c069041d0300403820041e0902c0818040d810440e25281c600080589541d000103100702c00481200348c000d040003600d01030054000540030f40c00440b40306135583e200e848140000d0402d00c901c041c14500c038025000d200c20003a14201d1070040d62000c1d1801422580e83d4189144841c8110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 463779064 1250 463777814 463777829
    0x19020c0d030b100f1101090f0809010e010f0918140408040f0b120a0209060d0507020f01150e041e1a06011205130213090f1103070f0303092c0f040b060a 67
    0x804c161030b0071a014181440c0d940c01144d00014030f40882d519031224040501d20201c0c2c00e4100000d0303040703566801c803822806200d428a80440d40415800e800350494190f40502c01c001200004a0306c082d03400da070480c03144041c0319129003000c1d040a1401b84042e130094041e40324011003881001c80c0a0180d07030282d42464200c000303007000780d4507000100e100a5006002040d045041000002d13901b41071402218004c01c5140d001f000001426080c05003120729941d50210310540c289002c000b107805070100540c03c643c00c048015004800b0080c8240341510000000b06220b00040d034144140d002c03242e005202e51002e88a540707901035003210f40300403038004482000003500ca24a03c1c40c098101149440c20303101500d030000840610342d844a00d92002c2000b001c0701c8008109091482c9418144402c600030701c400030086849508603900501141003901507010911000701c030364a080082191000100e4541c0c010030300e81400c0207070140d031880004075010b480c20100c200109a02d824120220f50481d03902 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 463780314 1250 463779064 463779077
    0x1110a020a060c09350309010e0613050a0801050a06060f020a0f02130f0f180804090e0c1f0e0a120602071b0b0406020c0402030601090303050319020c0d030b10 70
    0x49a89010003048800b0f414400c0100c0d051000c903d01085040304424103400501490608000e540814100c0719400340040240d007041c00035011598112803140242c800844801d07884007260f034841c456540d841d074003240e80f118500c40c00061652040d40702a01480440c031050100c070f80c80e45019034400c0b2640100784010791000c2100d1020480d803e1030b4241c8944010050300310500641c002105a882c2e14408000c007541d59011a01008414461500301121070038119500d071400b1340792040280690b100d0b8022064440390784c036582c483c041c042c160703954500a01d0f40648a028840007001c10075190301d02008114000d545171b503145404220107007140c403040c66601c0d24140076074910001c0c0d007160004072468083d100607400c408081c03e4501e005480485610390f1580d15000300280342018840c002d40c000c902c104140901030340c0c07004101c1c003500c2e01820f082d40d41c0c0d164403801c400070360382c40c01600141d0b038800300745600d0344040400d8a03c6802c3d0181d44c18030002e640d000c2003026540d40501800c0100790f4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 463781564 1250 463780314 463780333
    0x60603081b2d070e0c09040b040605091306060902030c0304020906010c0803070e01090803160506070c08120c07050a140d1e0c0c08030a05040302040e0c010804030818070807050301110a02 82
    0x11403654000b00841d5041603651807940e84c40c0d010f140200543d228000d8100104c0d4a41c1d240c1032510504004140440342481064a09008103025550261420080d02d4001da400000d10400342c1286004040d088000c40d030740d10f40311814501c190000e4030224466103800740030900c0c40d0301c41c803c0c8020b0603401802e42803560725091002d5404140d00e254540c1072182448001980d0102400540510303160720b03d4829058001e8030300075082510041c000814019841d200c880498600c60a41d040b0a100c1d1811104ca40ca41c0c51140c09036006051004142d442200340140820a54006d511214a04c050444064140f10a4280e8200d01c50780d410514455664901d10010340c460360300c02c0c40060084005200c12611802228256440400b0780c2c0041031000604000714145442002180d92820000e8034031440c17003070002800114003420140811002c140890301001c0359680034803461001c0f40071100420340c0c8041c4940c882019100e07051081d480c0200e84207001040d0b0381221909900795024080540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 463782814 1250 463781564 463781623
    0x1504020f030c1813020a09020a110a120e060d050a0b01080601030b241e1305040e0606010c03051c1d06040c0e0703091a09010c1b020607060207060603081b 68
    0xa004000c581320f940001c2090700540c5400c1c4c1000c015102e81c001c00760740e451001c075001c1c1400500d10255180ea60008454101080e009104031525030300760b140410030050300b5000105140034060103c003005150406000001000e40d01106080000b80c8456242d5a01e01d1300641c00c407480c9060b0365030010000410405110a412072410616010903d41820702c01e00380f0305807044021581d1070048500c400201c0c50042041103035a4002400125010b025501c5500c802d01d0301d03000098180360504c1907902c010b03420540140141c505442c0ca03800214101010303644504054084040006089402d07841c00703000c08800030a170382c4c2c8243d821616207070300140361201085103020300030710160405948104c040f00190500620310041c1013842c103d0a00740c01c2625400382100c0c00e6a6521040c0483c00300c0c001840c148100b003c0c03080d0354046480f103440300304604003000a4071815170000d1036a03181070300c04000c001802d00500000039411800c140038003040149961794925260700b8280d0885071007030039481d81 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 463784064 1250 463782814 463782859
    0x509060c0708030606040308120f1302010f0807091e06031a030c0904050f0a0605150907091202040e010221090606010c06020f07020d150c0516060903020a051504020f030c 75
    0x1010140c052446c0617500e440b1030310304c1e40080c1001180c0f810f920090000c47e10000360042e8004c103403508580c400300f00329030020748070340a2203840c541408451400184030038042c0c9001c81c0100050f076400c8401c95551404080c91400c1c5028030710119103030a1901002c1003e05031400740c4140040e0040400074201002c0112044004101300c805100340031032101050320601c407401d1114820070011905041c1035940c90381a41c6143c074140e000c1c1c0500010049542da0144200c0201d640b11509a850541540082405041060320010b02580001264403440001d0030015200003c200d4841c01c540d146c40c440662101429101c3e00d000480031043c0c0030201d11560f004100081c485100240740c01a80d43c04600f0040e001001550b41844079260020740d80201d026882048543e45000c6241401030f02c690000759000740b0303000c0e0440303540d09082030415008115645089400000300c818035455a4a40c079909442218102d01441e041102100c01c1c1c14006402501900010320b807c0c4111000140000318 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 463785314 1250 463784064 463784071
    0x219020402160f060213050910060f020f03180420122e15020114010312031401092009010f1d040c0201020711030712080a021204060c05010509060c070803 68
    0x7500440c5094030300184941e035009014a11400300980c69406c01c0504420300407041d40150300900f02c0104200d03480046c482d1041c141c42050a14460201d00100300701d1614821107c030718403504c030018503001c9060b0604481c4180781c00031201440b054103400c80d01c00c600c840d00706010802e4903040c4202e00c100c021030f0002075404000c200906c2032a84e00c840c2d51880d034030702042c9108002d40d0000002e00c40303001d130001000082842c500091004a80c02803106401d5941448080e2820a410901d101d001d8480d030011150040b169104001c9941c403100c80500801a1081c0701c510104100403628116a8000645203001816101c00d504a820b420080c7d0b40241c01c10700f00411491101030404d4940c0c0c4908c80c00d400c1007079540c001612031503a842c10301e5109246c070311800e02c41d82c401c00d02003141450800f100740c8466482800c8a407205080c00060f071420109a070f01107040340002c100451000d82c40a24607a22600501c000d000507107038002d0320707500c4900c10340d82d03030a9a04040007800081010320b00210380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 463786564 1250 463785314 463785337
    0x708070b0c030f181c1208060d020d060b0d030207080c011d0f03070f0902070b09061501050d060503063301020616020c0409060e1c0f0c0204090c0303020f010c0219020402 75
    0x4424070a000885171260300800c4d100c42c10311041c0c42c5045c00900181d10510700c22030b0810b0001410041e0000c2c41148c1e044030020310a14401d85038500304110f60304070030401c42000c2c01078001c030021403078003070740b1070b802409525072603c03500c03124070311a620401040b41c03030075003880c8006031220700d0b8024085005008000d894040c403c0c07600c0000c03400520084000140740d084001601c035102890402e03604c080c040d1442c000c6034002414402c0c00d0050a002c401502c100f42080d99640400c2c4800074007a002652200f80c1c180038201c10081c0d500180ca0240400306254402002450070005c0002602621401c0e0a80181d210000181c441602c035143c00c20300607083c0c0100c4810102400004080d1a00250300721841911124100300000007006009070181040c00172256080011070024840c1b080c510440c01003112442035a07042d1340f40c03903110030051a08181e4000700b50b40c403814040d50710075040310b0f03c60302503281c014180922840030800f50802a124207809400c400c42d5020407029400c0080c0011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 463787814 1250 463786564 463786597
    0x20604031e14030408070602070b030c03071701060309150507081602150a0219080112020904060b040524180a050405010b0904051011072307170708070b0c030f 70
    0x90120b040d0303a00421080d20880c0045613070360300b4010020b0410784c032544400195403064005219241c1e42d001941c0e8456031200d04152207944502048504044410510408100c4c18002007210b91b815044083c8441c0101d0940008000204c00041120012954000002c40040100360700d880d1025040402c4055481100c0d14032000b1288003c0c0c4490680750f1450145c1e000481140c60b500c660030030b0803400400d0a10b80300d150714040300004000c03a061802480345400100180800540303030b00ca03914845010300100120720303101034640008000043d81c241d40040c800c101540b580b902c0c0824400400c102d40f4140016240e00907031b14013400001d0000c039865500e40610100f140c652046c1300d03100f40c0c010f10061842821040a82007100d85c0d0a19400b0590020003009010400e4410000009500a42d02d103402101403095a418583c036600078003140a00c140d10242428000a48001510392030710503600e01c1c56550003452524400c00c0f105550613003082c0480c0c4081d2607150094102425400d801c2c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 463789064 1250 463787814 463787873
    0xc030a031d0d0c03201605090702120f0f040b0a03060503030c0d120902092703030f130c030b100306050105101e0212030703050405011a0f1905120309010f03050402060403 75
    0x36041282c048214030181d000341d40703c6c2480000320640f00c00034601501c640d41e20303050500c40251a911842140c003545a8002400180701c2c08007000c49030700251000406860b10b4603240031820a5000c4110200000d00740100172890349008001c0fa40703c0c000800041c002819902d8040e514000954003164425030f94104600241c0c8806066521030440c20325421119403a410080f8071800710f216201c40347d54410320030011207482c0c0c0c0340c0071070300800f09034140100e10388103242c03090042031b003034200070030b46503910050011800342c019803102903a11500f4144030310317070300c0e0014000c00c0640c050031040011011498000b4003581e101c0ba07040390440d82c1c41a035040780d1410180c040c203688151042c1c80043e5441c070806c81846400c2c4900008003140c6003440501c00105d0340040e081d201d480c140715109408400207440d20704191800c0394000c200107080032800c4c141c0c02406503100d401411101d404542c0040303914580c00d2007486254443c2d54024080e604040c15500c139020107007201c42d002601d0911b030760070a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 463790314 1250 463789064 463789097
    0x531020c0106030201020f0d08010e0916060e040b060708040b0c0a061406040506010c11040c110a0f0b0601020d090909020607050610030c05010e030618070b0c030a031d0d0c03 77
    0x40c5905261500041001c030b203140b00080c588221042000c40703640000078440002a400340d001411280c0000e2000031903211000d4080c246943d441c0490002a00b140c0e000407820740114442000701000c4a0800c41484501c0901c8078611901800a185040030041403000d44580d0001e44404006e5508075440c64050740c0d1048116004d14950307a102c03c0141c4c040260300d14090007400d0f4442020701e00110100c1c100da45513001c500c8040382d22440341d84c586401100c0309100300c54820022245000b01c40c01503400342810b4007020301e11101610458405800120b582d40005581070741520142d072a40e001c00c4c03130701070384c0c07c000d291201040364020000c001800c08118200600c90041801080d103050941c51440c2000001d22594056410300a50300706800d0569804204203a02000b0414a80400d1402c103600c58104409608805c2080d000070901201044c0004017411505c030150318100031450340c403031540442190081d54035006500104142840c10311401280d48818481d05150801d0075002c40c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 463791564 1250 463790314 463790317
    0x130302150c0702130b06160204020903070f080708030405061602061201090b030c04050915060315040f1703041101050a170a150e0603070e0411060406081f053102 71
    0x4501080c810081a407100f540340114540005030108001000050001c402080c0c0c40d000b4062040c55060307007640742d50199102c0b901111131115005007036400441e00e031403c844000d01d06000d04201e1344181d460200d113a080c004101da050710b000400b49800c10840e851261400f80108000700c0c0c0018050002c14250269414007078003801c10601c010030416584401c0c145086000818030388594201000c0c070801d01404645005480300407103401a0660b01d10011034a00900c8070201c03040490754000b0001809400c00017464143d224488884c107107203480310485658041510050410071100402c1807266014600402c0d40300c655041141e881005103807103013440740084408040061312102c60030307401c160505511010f081e03092905c1442d81001c0001c00d5544041e4003510100c4801803000c034061000c090291001c1d0f04001f800140e60355101c2c07400400900080c1c40018401c814034a00c0320088184040b01750131f4807000380c2340714020011032a00c03200035056044800441e40069003101030748030b007500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 463792814 1250 463791564 463791571
    0x91e08100606120b0a23061b060703090302100218040903020304080106050603012105030f0a09031109041505060406032015031b090111031308101413030215 69
    0x80d03001400502d0108060201801c10b9591491146000100e82c1c240d034412607580140d901002e00031410320040410a000d0203a00c01d02d4580c13201010600c400390400d052403503003140c06188151540354442d91400e03001d0701c0000b0001800340c1c010903600712141603a40c0c040c1c08411801c00c0907254081c42c08010404480b81d980c02640147c000040c180708219090041d1401048140c0d0b10a246600d0120010754140460380c0800e540c9a02050301c800340704080040d48c2e42d950b40805040e44d190700c07030354000c1e1142d0501c0c4822112621001c07036022840c9090000f15214603086954a101500071011110080c200100020350069807040c004c00440c07403800c00014003c0940d4692640609040e007040700030203c075001d0a80301942001003003107501c0303410200e0015654640d601307522102d1000040e146014400050003841c0b0021841000c14142e0340d001d4001c42d4407082c01d40702c240d070850500b20150307110404540b101003100d03004241c5580b1a4600e24401a01910584c0d462038540c0a1075460101c055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 463794064 1250 463792814 463792843
    0x16020d0308100f14040f022115010f05030f1f0b07060509030a0212030a060512010903030b0418110d0f03021b040b090112060e010216170901091e08 65
    0x3101000b1481c40c00541c2c42d0003908224000401d5985400743d07800c00a0810741545020f60303101d0300030b4201c1e00d046806451014849800009001c81045410074500740b084440b1a401e0709030048820640d4090103050b050100702c1d07556240745548207004164603800c00b403c40c2a8205c40c003017043c1d078004640a4800c0c09400e41c242065603840f5181001d006a81d0701802c1c030007544c0c0081205480c0136400080d006125110140030a03261780d02c210151000309450781c4280d401207208120740c19441c0c410343c031507031100d8421748003040440050f4007800215800c0307180040001c0c04450180c40810400e0380074850071300c0010a1203145040564400c5130031101790008401507400701c582c407500c0c6980e0f0300c0083ea0785202501c04000a068900c000390310040e042c4200841c5540d000751510a226054000c55001c0d08181c0082d0750702d03246001808032002c0046400d0b100400c030b000940d0801c0303180c50215003500d9016910301314101d0803d07401d0752442d46031400c1c81c44200940f800c0050f0311901403040224041c2c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 463795314 1250 463794064 463794077
    0x301050106200c0307170f0d0e030f151b1b0d09060503130308090102160308100603050c0a0e0303070b07030515011e0509010210020705030703090b041a16020d03 71
    0x542c502809402c40c96501c0e00d05801010b900081078030001200d50485024514480d140203c400e003030b508022078075544210034068440d9a84c00c9540203c0540700c000d40a808032900c191022501c2034581880f141800403140c503503004122048042e1b0b0300c0c40d0401d007000380103a15010150030155080304051820070155041424050350003500800c2c200002e0049080203895441d00d501c2c20303281d0100d803090040601a014011600900095050f50310180408c658030300b12020354200541809401c41d41c1c4407a0024001000c030b6120300c240680e0b40500d54a1410505003640c0500681c0c40d03c01491125406100502c60000461407a80030306008006a4600145900b0005030b84c10b161030b0080310090500c00b4107041000605580e14004800c43d001d854210349407015207004070706080000c07040f200032900100d603040138840f0120081007524841d860360102e103580c5000c00c0b2401c0c02140300301000b98603405001c0d18134221030b5008212070307402081306914410155001440300c1c0c505610940c00a5071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 463796564 1250 463795314 463795337
    0xe01052b110c1009171c05100501050f0711130b09010501050901080a050c16061d1507030203072c0906010504050319020a09050c031605030727050301050106 69
    0x40c0d0784036001a6100c034581c940c0ca0078040d0400d40b03981c1c0104540180000b40d0303c0c10075070300307100c064509071401004d03841c100d07591900c40f070114074a950040400c904005103440d010038840700c800b03a0140f0481c1c0041c0c507010300b02540c0034011b2800307801070841030346c40020351140f1007140e50784c3c011140c4d05006c0b0004005200c2c05c4510174864035001c140c01071810f103c000c00c40c43e01c03981c0c3c1228081c0c0e80b110101c4c00c04079450b540c0d4401d102140c041c0c030074040b030702c45084203a88041103510f0b08482c0d94892003a08440489441d441005e03900d02c0c074030401041d02c900100c04140f9107031294008560100c00e83c1840d000300c102c602c5003a5a50000f4032004400c807c2c00f480f03000201d2034000b42140e008002442c100781083c1c200b000103621580000040f46207020310070000011901c03101555402884020010800c6203080f618071f00d0140d008a80c031210009528541041e0780d4002c0041d039001e40203d65a00030090190840b0070703002c0c6400c2404500c00c002030000041d403503909000b854060070aa580e0308180d480c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 463797814 1250 463796564 463796647
    0xf0903010c0f0e060a0c0f110301050a1a0306011230030204091508030a050a170709050316030b0109090218040305041e051305130c0806010f0e060906010e0105 70
    0x1248043d02d00e01c01c40e41007100100b0b03180c0c00340006c40c1458000345160542c904070325040c40d069402c1c10481c0d8141d42050700700701c1d00c0200340e4000c65071400340071710700300e1110200000c01d80c5501c030902584138034030240b03868180800e040e051504444c02491124041d14010750303400c00ca0740090780d80c404000a0b000a0107101038030050003042c0740200c1d0043c406285500744580161240500c0d05a2401c00c00086a100d078100e01c0341080d00c1c210904444840d481d0308187c4402404280f140c0a0319019100b0481302d201c41100880700a030460f42c10600545160b401e0180b664050090b07400180d034000035041c501001802c4c0f00d202940a1880f03034881c00da5640c03a1110021a41241410301c3e6a6048004400c2003a40c83c1c11407541000080c00100003125518900c0101f448244100041c000070590304020464040008641e4182c1d80b944d5000c01105558206410101004807042c2c2e4210407000081880f5500071801c0006801d0141809420700d203c0c8a50302c007000140c6d01f200c03103020b03200c41340c0d550161 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 463799064 1250 463797814 463797827
    0x305070609060f020c12120f0a3c090b0d05070e030304080a06050604140a0209010e121b03070b12061201150b2b0b101e050f0903010c0f 60
    0x30300c000d0501221015a003040070f1740b10101c45010034001d151504440f005000d080c8119011302030000003503038841061b4113070f514881e080342c10a040420260001503c00040c0a03207242d070059640360400c2c04980448500d4403650b0091408001800026034001c0361801c01c0d0b0000d00307280c0c400044005000d10340031000812080507662514001d404c1008180b2070140003082c140c08050304030710045125216040414014100c00b803901240c0c41826051100c0748680d0f800138203420409a0320b043c00c80c210302c0d0410a01d426603d0030104540e004621841481c1242c0007036020741c40006007642c401d25030340c1240081d5a0700c100504060845076030104060340c0b400f0065102c003078603a10700802c5000d0180401150360045400f656440003000324210000380569002162501e04592003180352020107000c0c440079141c2c0c820b456101300419046030b500d01c0c0c4aa40c44240324410910800621040d50304160303a07076480303400c103810b00d08420820310010342c5090048408000c4945c1c7d908051185014000380b50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 463800314 1250 463799064 463799069
    0x70302150105100e030c0d05060a060506161211010f150b030903030c1303021e010e031203060409031e0f11010204180e030c01050705090a08010b13020903160305070609 74
    0x804035120060040743c4940c0302c00000c50100f82805144540c0d55000603180a0440700e40a601c0a800321440d81040404620726006a02c00d0405102c9507484108100850180500081c1181e20942c011404648022a20101c0341f0550030311800d505203d000f1242941c1500c0031802400c3d8031140444d8040c800d81c00381c0d10040c040006441c3c10b5041215010b0b07224030001d010300000d80400304d038126100c03040755003000043d94004c1c110070f0345051200340d111207003a0700648103021070304046d4030030b02c9070030b0100c1c800709110fa000c80c5051841c0d85e08010080109803e110030703410451409202140d0509142a10301c444500d9101d0070400c10040000134021a0b1440768022140d0050000700081182c0030b04600c010403812a000c994200540d51651450003001c020500640c240018410f035144c00c4401802c01d5203060b9101e03104503440318045800d840d42d42201c15046804c0103e08260350f00168040c204500c001001d0f68000f0201c45000219445d40c1d42094516400c410003c0202a4000486400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 463801564 1250 463800314 463800343
    0x80301080d08150409020a0e0411040b03210307170408030628050607031e080703060503030c1209030307050d031a04140a1e0f0f060816090c0c17070302 67
    0x2140381201800b4000e00c25590f41a0141c1d854850a104642e6520119000351902c0940d01d0040e18143c11b06581c0ea819419a2030701451402c82008464200402d4140882170082c9030061181079111f01301d501030b07000621031420015140c00049100050200300780c0030f2801407403d6a207034142082000301c414070380e0900c081420a03d110301c0d9100b250505202003140c4007100c42c1d50b22000903050645801002e4403c1c2c4074683c14410244000680003000c42c2c3c00340b2080e55041185503110ac051590340d10a2060200d4241d100701c240d140c500300c0300307801092110700c05000c1e6810060303245d0b6803510740b085a060080100f40c03500d2115400021841040c14540702c119428040201c1e40710f41503a08000182c40c000000d0f40303c840c241e020426000c9940042610940104884040c0301c580c600100400300c20ba48241d81444000106400005038442c0c0bda90700b2407000e542c140c5003142460003001c038001280c041c010a41303040000f080500428610041c0001526a0342e1941c601e00203013040080000e081c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 463802814 1250 463801564 463801577
    0x20c090a050906071b08040306090b0901150b0d0603120507060524121c020c0103060b040b04050d1401020a05120a050c0f0a09030b011d13050309040b0d060504080301080d 75
    0x2020740001c805803c1611420005e00c0302041c1008103014003090303980074110400c00600002085041d82c499032986025000e610800e0300e81050440c2a60101405595008541c2e44140002d105007401020300340d80d640c03400034806a403903880703500206403108140d011520114481085c89490700a071035005200382000e001582082c20f0024904180b018114010340b424141049148400c1064020301c5200d075040e40d40c5c50603c03001c025070301c0d108a109640043d0802c00001094070081c000d80e41a41c242030b240605043c189000e0215a602c5403105840d500d5101042909c0400300b8801814200344a0f0b540ea41c0e507c5a005c08406a2000a41645007040c074210800028152140944208060441450b582e464101008440740c25041e000a030085007600000164a03045a07040b08000129001039045a600c2c10910ba0b4601c0c40680045e010340c0041040010310301c2c096001840180000f0300442242080e134035080c044810883c4c007155101c40000040c4203620041294000c021780600e0080c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 463804064 1250 463802814 463802821
    0x1302010903170c010501240801050a03030e0310060803091e01140f040f0b131a030720031902060606040623040305100902010e010512072d020c090a05 66
    0x380245030354070002d44088000e502a6500c2d040c4075084078508803045009100c00d58545005040d14116001d0303140c10f181d16416000075807801035181a0403500f004141a003c0b0345142c5003a02d403010705200f0660b140c0141d00b024600301205100d202c000d40280700c003c580b655150340c00c2c00116215103a04400382005501a80c580b681d0096031202446058015540c81d058602800c0c0c0e0b142c081c41d002034860003071800303000c04e6a0880304098010b0504041c06c620489a030790003402c1d041040c10031803c0600700c0800000c1e01e401d0141c1d150880000301402c248401e514050322a0742190403500850101300ea541d00602402d42e0f04000070f80d0004e0045840780d01d0b00385400000b51000b25904a49103541d0100554400c203071a0080640c3d008507008010765991000d0004040020608420103d0102d110900510419442503050b210240e41e090344503686134941c91015120504070500d40814100504405c40c0b032046030000d640e60341d0007541c0003171400c00801401c1161b10340000302003100ea1031800c1d081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 463805314 1250 463804064 463804067
    0x20f031302040e100203040204061e09091a090a020901082802150406090f0f0509041103010e1207113c0406030c03060e060705031b120c0c06130201 65
    0x4503500814030020120914005201041c0a0720484084288900400140e032400075590340045105a00c00c0341c04001007a120030003000c101030408480d2006204903e0280440000d80c0d011b0780b1064040c101030216145a481e5021441c1e0080700c91800903000030f02c00303008504020b00a5400360105401501030006005070a00c0e4091841c0c541c29982c4c0d0398081c103070095484110019108041c40030440341e981e81c0350f9402400320760042c81118560140540c00050188916000b2000d940d8010300c04c8400e03446c1c544600320f0a17845484015819503803000c00480f03c20040040c4074980001e4140c654544410b82845000002c1d41201d2030b0040c4900161402c2408010103240c5459049001d2041c12030610081c1d80c01009a0010442e0001e00e0401c0110900090609180480c0e01c544018405400140c003c00d45640c8141e80c1080481c60a01c0819518201c843c42d034144032001e90f40c80d03401e0041032072030b028111105803000200d4480000703e42da0301c90000c1c05a143d111010864501e0403400e180d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 463806564 1250 463805314 463805317
    0xc060b030c03121309020a02030a09080c010e09150405151003050907030f14030c15010605070c0302040f11070606140307150503060406050d0302011a011103030a090503070503040806011503020f 85
    0x340a51140c3c00a1030f50180d00120315410060850380710110748419103818007030754a9100c02102c8012410385440000c8005001030303401300001d010ba40d480415402007092058801000c0d20f4404e1005c0c8018100c0c1a903180e511a90340b0070440c02c0c5242000580344001d200c400c0d5001d203d010201400c4c03004004c0e050000050010440c1d40c000d60340c0140007000e081a26100c407180c07001c1c81d542c0c000094040380140e030000303c0d0700b10a070808170301c1081070b641d450058440e0300c40c2a60007851000c2c021300c02c001624003640015000890303000041800d450301c0b00b00303004c1988110030845500e9628241030010440b4001d40403006001a401042c64900b408240101c48540c580c40c0e0042090000c00220703640c4640c2c10201c010711002e851a03100f42c0040ca03019000c1c014850088103400074618085149610071030071840080b4401c800303145141c9581600501030255104140ca65203c208981c2c4000381c0b00b08000c000070090b0700080c008035414001d6407800c103440041d203407007014014000b01d41001004c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 463807814 1250 463806564 463806583
    0x271f03020a050d020402040e04050c0108010609051e0a0f0902180a1a0703021f0e150c040504050916080d1b0803010509060d050124080304060806060a050c0703030c060b030c03 77
    0x8800c1d01e00550b11348009006031060707401409402000109010030400300280000340c0d040240c8032034042d07130788030901280d4140b1039100e0301d0703032041041e5000300c6016940c4c2500c00d0140d0015004441250305c680c8034840f072701040d610000e125680096403e20340d00c7c03094903100180301c080350003502e164585500d00c2148a0090300c074030f0004800091140c1014020010a150b03505440c0361081e0300103964801e42c00401c10254400d2050150301c0382600c0000300001414461010503086c43d00f05410f00c402c1c00002e1200400d048441d00c40e242d102d0a100c91141102c000070001c1e980209400918004000c080c00510384a00e11003200041004000484450980c0d0648a041d01c00403400e135101b80014100c4001140054015443c2c002c640d415401100d0180e100c103047c1014030071500ba6505003c664910452066400048055011034640d1508400420281c0c079a45411030a06040c50203a6040200642c403c602184040440a04001e101e002d4402150412400343c00c4400003080072039100e0250700c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 463809064 1250 463807814 463807819
    0x40204050d1b0f180c0c05120c07050d060c0909090f0602071a070807090e0105031e121204031202130504020a050f130e09030a050906030402271f03020a05 68
    0x140a89198005850454401030203044030900c403030303941c0342286a80c0f180f40720000c02c1e844c0c1c106489a4012070184000d0010036500c6401407290f000203c041c00c100d0740005000440500640c040014140d4400c68683e0004d030161000007030781030381c0c0800544200015400319000c103003460500000303e240340c44545111604000e0142c0d81d81440d01d0034000303840c40300701071010311503000c014401801c0d1310a031082c1c4555026200c0700c1440f034640c143c40312502004d220740d03a03043e84514403e40c0c01d910700e0042d40c06c8182e0044100c2c1c42d03101c4001100e46c8960845070740034405034541e6003040289640b0206c03540e551029603030300310715054100c011112021124003d85001d107070006507156600f80701d00200d5800d400c0180295032240f102000c0b0000d02d0f0360300d00c50740c0c14040d00407010550501c0040f003120304003145600d07014581141d0005000c80b5030230050003664001c1e240540d003040c640c2d01f00d4203504007038494040d80c060341c54141e000040d0586c03480a4118191803e5005000507150031502e1025140e08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 463810314 1250 463809064 463809083
    0xe1005010857190504091505040606050c0c06070614070c0c090b0609100e190306050f0709060c0804090606030c0818070311060c030f0c1216020d060f0203130302010b040204050d 78
    0xf000ea094820b07200390360100f0141792401c0703240c0407000140190314050303840455090007401c4e501d03541160035019407502c1001c690030018140586180100007048514070510f00402c4103c0c21040e1340ba1102d00803070301400450501c0943c5070400c401854503402809081e8020451b421034400498828025441910b0140715441c1e480d5601078061030110300d0800c030044c00450160f007035586002407000710384001c842050808022400354407004400078030902071a0f840c1e2014510f0404201d60145c804481550413100400000c01c0000d064014200038105589000c00c0c2002400c3e00180003c4000300560900d42006019525403100800c40308112030700b06884e08010700315803000030105d22615035013500503c4002100700000d029013001c1c041140c0c2d0304050b1807800d4a11041b0304001d02c10322b0095891011043e0982d001898054241980d050140c0000103075103040c040d00c01d08030781c4103a520b0340c1c10344841c1540008040d42406210b0180c50142c50950401e441e21000c2a08000c8843c80102610300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 463811564 1250 463810314 463810357
    0x30d0f03090516080d02061302090f04080405180103021009050307260a0515010e010b0702011409030a0b2a0924040303050d05010e1005010857 63
    0x800c940707a0801001c903030204609980b84d02c1181d8074000c001c100ca0140c02403000140608013203203c804034150b000382c803111650f034822651054203034004004a82c035120500000c1450348840e0042601c203484400041c07219415401041900e13080701c007070b840c10080b42c08014011502c01180c1281180d88040d0601244103005441071034008690741d100a152040c0e503601000d02c400003038642200007103241d03080d5443c0d88420031007010300c40902800308085010407201005511410089210001d4411458201100030001a0034501d4552050b035078200c03c407042c031883c03407000304410001800f061894280c8031141c2035245180e001d25603a0f80d200e580e2900c004010014820602d404800d00c180e501c950360303501d80c0380180803600030030022420146483e0010030000c0082009a01600310010400c168500d01001121800c2d0010044210310090f8070042c0c0c404080c1640660140c44444c001880301e000e60f417628607010101001b00300c01c040781c2114107529409210100c1e2112684021251085407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 463812814 1250 463811564 463811573
    0x50306090c120109020d060c0e0306091f0618060305010e0a20240a03061205031c060f0f08010c230d0912050d060f150c020d08040e1005030d0f0309 65
    0x11305a1000385d00042c01100090401440b58402e8100c4849034854045200f0740c1d10525983d103900703d42d4201c082d848034a8206600000780a81c12400c01c514002048680d01c1c2d445c940a5600500c8040c03208548a810030f01c1000780a0258859a403440c8000341a1100107031201c800000381c22039404200f4540000146107074031840841408503401c80c00c05103203607802038a40c442c154070120031070002a15040f0041420080c007002130b800036801000450800590684010340031680142281e661030f0b4801000a45091007904480144060340b1181561407910020340e0a44e4002e4240c841081010381c908100034035245a1001141440b20b201900d5005030121407000b4404404098135581d598000f80c500598400010109402d00c0f20003804a00da88020300b08610400e80606540211400c0001d00b40c0303446072401c1c0038810700040030001c4030007041d1581c0805500c0354001100c115006420021040003100c02c600c0103010540044c21096041c80c0d008040e40541e21880e41010f8a0305414000d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 463814064 1250 463812814 463812821
    0x60c070803060307080d0804050708031318062318010b040b030403020a081314100518180a050717010e0c0703170c04060306061d2101140f01050306090c1201 69
    0x45c95000101e0b01000d00340d200c040c1440d00308550881e0035100303660000c104654044266020001c0d5072045070110b509000019603545400001c3e4480c407941e9180000b2510812181c611610301034100b00320311000c0100500404104220703144114415050040185200200031601102c010381070741c40d01e944492408a082815524000d089650003040c49002c0b00765003044074045450080d610a1440c13044c10902c002c86640943c0d680200e481408540e07a444080503940040000041c483c1c00014940c081d10b005a010964100903900d695104002c01c458100004013800080c00c4d00c02007a661400c6442075880900415030440020040f0701710301014040c003080c140801c0350310191103551a10602e58101c6403ca407096000090800c500081c1b011b004504c000c005981034030251044021f11418810741c0c3c6a26480302d200c2d6800c441c0d2130107615800b03100d101c2103801602c0183d195070074079252502c508078068021034485e81001d030500820f405c0c0041c8141100200ba207003511011700400303440b07004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 463815314 1250 463814064 463814069
    0xd0b070e03010207022407170307260a0e030d1d0c030a080301052403190c0e03060c36030c0a182a030506031905030f070c090606030c03050702060c070803060307 71
    0x591312078050841c134544075400914881c0a05a03149551030740b102800030780b071103d1035030322f00c0d0440f20000210710800070981141c0c0a440c6e04004aa10340300b82840d43c03404494501c0c80b04074540718025214a0700c04070612440080000450003084100c240c0d494078017241c40103104841c450340d16800d84c03500e0303200300076a0612940040d0400546928000940440791500814052942c03031501c041030400502400d410501e9180150080140c0e9545028200c026801109800310700070709034249103240e0001d07200d0b890018040d403900e02e00d410407104c18146020b00c5011440d2107195070490504c642d400441d03440202e0603406801080099512046020502c07500300440c1501e27801d4a01454140c4c3c25402030b50080c00b003602101d003600c0700801110804051490f0080c90b68100308000b510b89110603002c2d0584e18003c041c40321040743d442c3c007200d044403a558001c002013074444091800c0287c02d449019440345c02c0b4001740c240b904d0700700381780c0c4814851014002c044880c0840030602c02c2e03c04100d074801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 463816564 1250 463815314 463815323
    0x90610090c090b07150f05090d0c050c060c1e06071407060b061306140702030604030c06180c05090702010e07091509060e0f010f031509060b0d0b070e03010207022407 73
    0x50350600f90601c05c00740000b0040c8103100300d050407100d04a11b896445211b100d20f40c002d0142405401d9000210342413034454005640e02d02c910400e4010365919103004007480c114800050034a60b00c441c204607504445121080c0540c0c10100800496903000a50403050a400c80c1c0082e54695103071421200416071b0584107a0403160100d180d12402d4040a0644280c40c0070b5103560350a009c8600400b20148901900250107400402c04500000c1c0140411107010b440303200c1c0442c0e07003002c0320406654014110001d45003010765640401c41f03805c1048505800c400e461000340002040083d06507540c0031140700d002d200e10395884420040e00e0110a905002c1c150441007844100d42c2c510240303d07a24001d07101d21104d402607000000341004072054081c12280d01c90744200d030380802000c1c490700901070140165000c580328403040c034440d40c41200c0c8110b4603108c1e015030a801d04001c2c0c002000503652000d01c5000e60310422441c0050783e038905810101c08100081078112541d84100c501844c0a81c010050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 463817814 1250 463816564 463816567
    0x80d0506030f0a030f02010e0106030203070303200a05061b030402092205060c0a021e060105010305041109071107090c0e0d03050c0a081c1e0f06150314090610090c090b 74
    0x8040690201a1708141c3c0121781c000c0c0300c0c035014920158203c4201e440001d6040c1c0c0540410400280115000c083c0300b0390b89145036400ca0076a040050520031400012a2503401190421460032040c200640340c000c403c84002d811490154045682c0d8500a802c1204880c456001040308004805001610f43d6000701643c140f0300303001b001074160f034012805080142c062035100f80c50000c018518850100f920700001e02d0642d00c0e100040d8000d003c054010340300b034805020b0b01d00440e1035400e9901d000c7c21085c2d44400c08442c10000085c14030032183c100f16401030401206001e442e6108034000c1541030b007211940040411483d0030b841c0c5205500c1204000d01800340b150301441821000380c0800024851201c4940706001c01c3c070001c44421100800700d490801a01103200c400a81c441c00455240101c001803040d2a4280700c0b08110801441100082d10740d1143c0c0d4110707140750381e1180c021009000804140c14030400f12030095410b0f0065055043e561810b00d8440d510070a40c04004208a50728103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 463819064 1250 463817814 463817833
    0xf0b0405010b0a09140c13060c0602160b0403080105060a020304030212160f030303050705130306091505150a090e0a1407030b0106170603060108030a14040b03010914010b07080d0506030f 82
    0x7400681510544600507140042c005486d618601003200c2104000c0c4905402c0c1b03d042c40300954401c000b038041513640b140d00740004145000010880404c1c5402200c1c2c500c4c080c07401d46001440c24405070065400360b001172001e0f2401c29000401c0d42c052b2a4100e541382e800020501da080d2810b40c40c240c40c2c4803c89034030000091150002e85a850580380a55418002039417841000d503414411901c00d4071504251000410208125500c0603070280d2041c045200b04940322821001030f03480a9a100101789800280c8481503d0301d0301c2c62100511440405114480c800c03038815840f14100000608020303a4845a80d21103d03003400070102841d0f01034200b0000d541c40340c0000705110020500907031580d414a000c144940780024a4904990f0782c80021441c00f0210074040b5007000b0086c22030a80448140700100340b004110001d18084c041e46203001541540800442855440691100c1300c0350200b00456004174608400f100c8181010724404103883d110103020030316100000c0c280c00224000c0300c100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 463820314 1250 463819064 463819079
    0x3040603050f0c070201082805070e1201090c0b0f0d020c1e0f12130b03090c0102062805060604080d08040605090c010504031506120309031205070f0b0405010b0a 71
    0x20342d01400d04030801040d00d640f00d01003403d00d44200c000190102e40a01c000070441909210292a1001c10b4140a806169452458410345009070764a00214200000520403814030080b66010904c903800244404121600c41201f615168003c0300c1c85036000150000740301b0418001c9603180208280c0442d5640c8039409a240c0704c0d11402c200e00d4011460140c02c882585c00020b041c1c2e204400b00002c0c042d2061814500c203c2c0740d1080024812945804000040852404014503c02e120807806003190304100e000081c1440001032101d0300f21040ca80c1c1540e110b21082c040700410070840c4c0000142521104005480c42c000e80c0d0082025208540071400c105611a040d40e009621484003071040c4d0303e444036041d0f140c1400c1084940010402d00081000c01c040e05048000c09500704c50003e006902e400c3c00c1d00d0500301c5078000741c0200d03c8640003042081301003080c1c2d0408117064500305013800707140c1d82d82484810100c03001810f810200d90202e024800203511111041000030061111503640c1d074507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 463821564 1250 463820314 463820321
    0x3090209010e010e180c130f0c09080d02060108061504060504020a17061014072306010f060203040b1603021e2404030c02010c03050d050a02030a050a06240507020303040603 76
    0x4450b00d01070031001040f28003017100c0c070460103400400013a200402c07414003845a01ca0540317601300d0740e05413101c5ca01350207800d052140302d140c3d034a41e130350714800f15082102c840c1c98825a2450384007154440e000401285c1c0780450040c0e0429046801c1030700c1180da541c0050080c1001d03810035a445031002a14200054001501d0803004000302d075a00043c2e5100705c2006411000416801c01048800c4c40c6980342581040c0181182c6d841807440000014404007415032062004000d122150b100300010710000004c0c010080080c03c0a01c011481c0504116050400d4000e01c2e044166484840d20380c3c1c0c040500920540c03c040c0c07049142d4014030906c46c8070480c0e441c100c0c1d410240c207021041c0711038512105507081d064415038140c0c075140c0496000c0e44c01120000c3d03241109a040100c18007420541c4101802460f00505001001680340c0c20080b0341002103840241008180d50f2420300308004800040691095441806909000d40c0003080c0023902c080c86444402903150000160114910f501740d070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 463822814 1250 463821564 463821569
    0x9050d05011512020f0d030906030216080d140901060b04050603071e0306140a1202060a05120a0209040c021501210f0c36052502010b011b0305040902030703090209010e01 75
    0x2038a91910100b0034046c0304800c90111b4025002480705282442224002c2e0001d10340145402c850102220254440d04140e4122481041c2a683c8510780c3e0b5166043e00014507400804120081209500d80351000420788620322502d801207601100181c102c0b401384a0b049044920038031190000700d8951801402881c1600483c0c1c400008600c41c0700c2503081011000d01655030ba612102c0808002da004c0003641c0c3c102c0e207903680c104082003103c403040502d540da06070300801c080e680142c0c840c1c00b1a0304000079100c041c02000115488100c0003444040c950000604559201417880b403c2c5006007000481e50004800142200342d4407c008400c11018003441012520802d850548628003900b54000840b03401a500f40c8481c009510070f0319281583d0320098000310f030301e00c940040204407204000014000e03e80c13480581d42d142a1100c15580000d0700c801c00c84480c43c076a00c05403410f80d4014000b0b00550145416403a40400018002da0203540800d00e46030b0000d01010041d0b0707490340799100411090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 463824064 1250 463822814 463822819
    0x51302100e0f060d0e030f03090105010e04050a020409111c1202010b0a06030203071803210509010f030b0a080a05161a070219180902090903040609050d0501151202 72
    0x15010458aa1044070035140d2280c0082c0502114503540c8100038680e000811240b1015607101003500c0340040800c02440c8040c0e800c4080ea440b0300d81820304600b114016402401040518420040080d8000c0b40c0c1001442d4110760002c0c2038607581c10041d400e914150380e19504072b04800010b1b0900c00e070020325200741c0703403045034500362044280004900344c0380806041ca03001105542c1c24000c440c0250040c41c5e08c40c11034601040031354032503540c3e10401e8200d0741c02510f144200c000601c40310307841c0305d01c640290703038441c01c04a1800c0d00000000704401d030f907c0a030004069641c00d42d45545e555620403100144168011a10b12098500b49140c0300d0410807460032510780d07800b4000501c2d411040400b604880c014184a080c141d0310740034002e02d01c06503408411410751424012519103445801c904402030304801c0002d031400f59205110303a842c4064202c9120b64400c0c401003140e0303640501c1003030980d1000c0e980700c02c640b10700345440c80c003518060200502c502d0400c50f0104620f04010210100107008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 463825314 1250 463824064 463824079
    0x1120905030d09020f0f06040308030a0e0109080c1006061d031009030e030712031409030a05011a0109050f0f060a121a01120207170307020a0506090703060b1002030306041509051302 80
    0x1010403003030b00313240081c61f50848800e0004202260b00000550b50001c0801800f080110702c0c51851800c444c20030800300e40024001c01c61008141040004084a00040c40e00f00021400c0660181c022481848041c00d0b0504000e1031485644062100342541460a50188810092490046c040d50365000406019216150b00000c140c000702caa003442c22500340e162900c2c2c1e155109034400160380040741c515014810074a401c0c000074000d210b02020344506c02c407032801d8845a04001015456160300840c4a00010741640189595050250301c00c0300b0220b904584d03514101909440c000e142d13076070b00c9404e80d150034483d4510b00c0740312800e01040c08090780c904840e14a500e0300c0e07200b2130040d041c001d00310f844100d50b268101481d05c0000c5030040140d004540840000356600c80c0782080468005906030040c40d800c104201c200d0148240e408422520f04c400c40004042c02942c034040100020310403600c56030000080220360092038044d0054032018010f40c501400c10f0100d480c11001e00320f004c1d904 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 463826564 1250 463825314 463825339
    0x507090e06131a04060b180405010605012609120f04051302162307090204090f061818060603060e0c03070f2c0708011e031101120905030d0902 63
    0x10310444508250340e02c0000400106100003d00c40d582d88020070441d08507940704a0039030183d880d10318207010380362040202c81d01740c9082d1610b40d09642c02e07540410b061181100035844242500f905c1c0c0c00440d82e42c8150319500d0340d0340c3c1c901c0d9490001501c0c10350441802c00202912a480c01d540200b0544e20156103625116985032081c50803442014448142d0100842405000032440d03000d035110800c225070251030b40302c4100c142c076080c500140c0c450a42d8550002c1c040007400d13900d016108510800b100c0410078285042020a049811a100c41440580d6040720074404030f800c4100500194110301c082207103680340c3c60804020605030a100303501c0c2c0301c2d404a00c0510b00c5c00217000f10a0310850031000b80b03854505680a06103801c200d41d400038060070421030340c0c80c0740b10a00311a4440c40c100c1c0e40d03040ca9075140c440000307800c2e1904515007004001051050020031400e500301c0b15044000e20b80000c044941004c454000c0c41300c100c0c0100303d400001090040c01810f034109801303090007100e0026510b007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 463827814 1250 463826564 463826581
    0x21060112080d0f060506032e080d1209050d03020d150b1912050a0b090903070b060d0609060e010204050a051206070f021606020d030c020613080a05070507090e06 71
    0x14210303100406281d410031519040c0031464010100401840102040c0c55403102c0015042d90001c031880d990642da40c5100300301044406c00100c01903074002c0c40e8205000d040c07026a9448445402c041c0c010310000300d12141c20342c0d0311135006a400940140560b10200b41c54440180694460b5080300d030071604020245408400d00e45034441150380d841e001d0b40c41c12115042c0301e1406034004a0340c5083c4082c00740300401003600d6004061240762400030004640301100e0400804810280482d1210f50050100d07400060b40c030b08415401c000c003290650319420341840e00b0000381403c1034005000c5824004900046c2c40305401800035140304580229100d61500280007868510b43c400c9491544420701056100380602c64010002d845403040da45500303100c0c12000b619004a030f21250040e4000201455403581c1403241c1c007120091403020b002c01e400d01d8801c0c858007082901000e00b03010000906034504a01540445403c641d214064402203640d034400d900041580c075411382d4a50003220006503028 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 463829064 1250 463827814 463827839
    0x4020d170d1a030703020f0a1d091507050919030f05010609060603090b010b0306010e0613090f021611131118030307051f02040512010507020f01050c04120c05210601 73
    0x502c4060010b01070240b540c4c00b000741581c903040030300390405501d80b8049900d260300c9520505107004400c400409040c112021454140b4031071400789401441c0741800316850340101102d2204600708c684c403034a06c41c100d0709015031020a50000b0501280c10309400200303c2d040d0041c00444070703617010410090b5a179031401d40036900840001407101c4403003c010300034a10030794007840e00040107151890341203501c180461044da02c00c40c0300344503d101448003081206c24a00403035640140d4404254200514840c0800f403210001500501205407121400302d1500d070000702d55001d91142e002403107051540b10702c5000917400604540440d500f103036400001424004101c4920036072001c001d001035480030348030490707204522808003d041e80030040010542d80303801d040511100a0400000c5500300f464010b0715000f24400300002c4d0b641040c040240c4011401c0036202280e044107002c0320700384403e241120340d0081542009900100f506642d0307081288030300d2101c0381800140102c030791698956a402400c0f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 463830314 1250 463829064 463829111
    0x10e060102151003080703080f062707120c0c021503040309050112021204110111010b130b01020c0d2108130f050309030106062609120304020d170d 65
    0x15900c02d4641c0301280d00e0701c000440e0310510300c401a0000545980d102e4200340e000325016400030b101d000a1282c081c1d0752500ca541c020034100c540b8482d011400030705058440401e54064a15050280001e41c1d150081d019107032510039416003003085050151001d4100754012100341c4c000e07803500d4941d4450003c80350440c1d00864054894415a61400340115244402403150b420060f40a015082406070581841c5004a12400d40b0140f15841c00000410541c00c02c00225601d80c18980203080c6c45c0c4410b844843c102c03400c45004030302d40e80c8000c0140d02d4610600c030704940cc07241d00b81412041c4118205040003102009804201035503150004641d000000d8650082c000181c1c500c040010303405d039000e0506a440b400a9a050403a0280045e00710382c40b5602c207201045c2e201c400c440000c0e212015040c428100024022064241403090a0f640c2400705e122005500d40000820300707543e100341e034207402c2c10341c4440c00d004105220050412140c000c040807482850402c07010a280300d0417290400c0c0c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 463831564 1250 463830314 463830317
    0x1080106060224090a0b091c051608030a0902060304060606080708010f060c02130e1608030703020a060902060f0d0902040c0c02090a0507030204150914060306060304150b09130506010e0601 83
    0x107001074503040b44100d0781c004d00300354542d02c40d003020305000076081d01c0c0a41c03088000402505000b60250645a400318800c0107803001c0010400000d01440c0303014000244040d00201c8083d160f59800782b007040242400000039500803c0030040004020158200400799051540c075041c440d03c480800351030141d0280203d00a10721a0b820510645104988540d040e50004080c20f650380c1c010b5002c80c0031500240c0041507a508000060b030404104081001c008100420043d45401c0c4552402910384204d0100148000c1d102c5084006641c0c4040944021002254446546041240c441e0000780703100310341240a00d0800c4440081c00d801907241c10207041e0050600c9240d90b0f9a12081c00046c41c00801d401c040c1035090101140760174951a102d01d208501c0e4490408090400c80c52480013911110400d1040004108004494031400150b9030040d600c20030100030100300c41d50680140c00c402603021781242c3c81e41c04000c2d58008221884000b5402002a41d00070303621100484c451000031160b2a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 463832814 1250 463831564 463831603
    0x709120b22080313080d020703030c0806030f0d120225030905090103020109030803092d070f0605090d060e031216022a0a050631050a09020f090406080303010801060602 74
    0x1000c0c0c6484c0c0c044a483c0903c2a40411b24005560100104981046509400003951242031002c801d409c03914944c3c111104800802040031441540c45c0e8038968040c01c9003c020072286001e40c100155010b440c108840021210202000c0401820207007654103025000505a49030000705803c1080361a416a50113946204415040d501d5211302c55002500015140c400d013103401c00401c94055500009035400c0322010790011840209910f010215005084402850101017100a0304001182d00d170140603a442d82040045042ca0f000a0013402c000c00002c2c00006407071012000f80c810200d101d5612655807401c407020f4007100b03d90f40d042d403404401300c802003003410041d249000c000700495540010640d501c2103444d0804100140c200740660a5000e029030035080360841c1c803d83d495511510b82140c8002e50746040d000445001051155200c030341c4d4001501c2c000340c20030300b045814a03840079006100b0340396144940341d41c80d402440b40c0561540b0b815030100b00140301190a40407049124100c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 463834064 1250 463832814 463832821
    0x10207170307031407052a2d0105040b03190e0f0709020d020903030f0a0215070210021b030a0905040e01020a1706010c0f0309030203010605010c15050709120b220803 73
    0xe07550000c134100b0700da030152000e000350070000b01d08020306402500e549495288080c00c2c02c00110f20540c804080380d10900d2040314034080c2c891002c0820b1b60002c140280850420200300058801d4031440d0090154600004100580120301c2210305640711130306030040041c0c18051205c261a00580101c0d181190011305d001c00030040150040d20f4103680c0c580d40140385c0040034000030700d194000c0700782c1040550702042d041502a014000a1845004e24040240034601030300002e484000054400c40c0469000c90342048400c0e144041d030007004500c50440740d407866500320240161050740304180c40b43d03040c0f001d00c40400c007041c02174803d0000745072181c1d1891003210100031004a001408107041207424803142020452018000996034060f864030142c65003940145400e46110b81c10690510282041d40400102e1011b15441800c2d13000000155588a80341c007104c60501da50320402e03030340038041c8651040c00030400c0300782c0c001c811115190810b036001070341c5403404060844015041c10002c2c40003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 463835314 1250 463834064 463834067
    0x103090b0f070e0607050109020a120503040608040501200903070f05030c010c080c01020f0d05070201140c070c051302040906050405090705091308031003060513080316052701020717030703 83
    0x5042c0c01c50b20508110242d10441008200d0a80050000b076800383c0d1121188001d40c2840305a403000780104540d072809078079164a400340c0d81d1295110721020824110001010f201c801c1d0b002580209441c4d01080c08580030f141c1d00d000326000f0b03411162107406914800070390700340d80360b484034210b81002d0090080c08500000655083c074002605585c400d200300301d2164440c1081c402040d8505071b0000540d200c0c019032205604480f00101002c056a05d40600084244100d254596202d0544044103544203210f00d01000c0805060307000c80d0700164101d000385041c2c00369030060000d55403924420041c05036510b04000c1540c2c4141c55840300c0b078118080503c85c81c00c1229003958031103550301c000f12440b000b568890215034400c48091900a0340d0501c14000c000c8a0300405400005400b00d00510a915843c1d00c005844080e0a4204030420710100e000e120f0300510507200040c911a00e49600b0782c0140c0d0002c0d1001040803600390060003000b00c0070403401d5880c81d1140c541c40741c1c42c004500f04803070b6030b40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 463836564 1250 463835314 463835341
    0xf040309060f180b030103050d0810091802090406050a2714030c0a05030a080106020606130b0f040504050606090f0717280b0118050306151906020d08060103090b 71
    0x34140402461000800d10f600414000000411490321010355035891410000d0915589072610010481c0d030a007488420b104100d403040039150350610000381c41d0f002000c01c126880d29214001d4009081e10104402c0c41100c2d40614030402d0303600380c00c0c008140c40c002800d010360b00c030455221801020203090b8000c0381e8850000754004072014122440c142584952618004000320120703800d42c40012101d031034942c00b403c014014903260000b810a405c1c8513001400c003d038800d0032040000d50303400c08a84140c1e5a202440c81a4102520802980c10a03080c51a00c401048078000c0c02100301401189101840088276481a0415514a09680303c46069010a65000382405001155010481c0c210614401c20400316400d050400640e00c1c00d1000050800956420f000284801c0d804081100c2d8401241256105081c0b81840041c28811f000140e64500348440b81200029104408285182c001510f0b41454400c5c1e15400c0040c0d5034600114251208007100a10100851b000f051450100b4113 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 463837814 1250 463836564 463836587
    0xf0a06080714061312030f030618270f061107030206040818060f0310050102010203071215122d030903030c0f0516050f030a030c0b070e0303040e010503060f04030906 73
    0x24001458106840c03140d00014030990401d207241c401e600484410147c100040c1021000203040074000380d85407e441c0c2da00a41040b00b11038040307031a0b10142c6548240011812400d80c51f600d019002ea091074204a40c400c0c0155000300c07507451600c40c0d01c109103200001583c035401c0d4158014a400e94a903071f51070106800a4540174003001c5042d11020403550342202400d426002c0c00c81140c3c607032816020506501645a1000d03040d6407040082c4810300c4c0c1d00c000343c440043e81080d40420b030703003083d61402d6001140c1c075407000b40400c0c210300a40040080c0c0300400880d6840d800c0000740590443c0c440c0c040700030003400d001000f180803d80108000b81c01040b001003681d004011b4421002407a40360542401350307201915820f400380d6078050281d4036007200782c1c1200d1041640107150b03501d49681c010389405110f0300c007c1c100301c84803400180c48900c905071049a4860190940342c9999480a400c00c1c1f2000a00995100340030b1140014034810400ca000c03403040c4e80564410500f140762803026102010401d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 463839064 1250 463837814 463837819
    0x1e0819060906020414030c0a050a05040c14030c091005040e0a0c1b0b01150903050d182d0522020a030f02031303090b040f05090606040312080f0a06080714 68
    0x80c100072021408a202820040c102c005400c41c0c92075180b010542080302c5000001c3c82112081030078001600d40c1c81c00c03142030301d405540015600551910944030802100710a025070500001009050340110000c2d003a0008161584240921401c1e001da5080c0228055804a42420400185660649d070404820a2001d0030084418400c00c80344404140e91020b00307803000c11100d8010041c0f8000100311800264880c41e10b1710f01e050540d95525100d60003410309404101800301c100d0700405251046100a111860102c4d8400c03c20f246546005542d50044c2c80f14121400d100140307908101c0d020041c03086441c07114034010700d0400e480780002e4100d0070081082550b1601c8807200c1301d4083c40114000c00c2400c81c24540000940380040850704c040d003000000c0c900c240720400c1101e52040540b01640c2c01111440140c3c0d4401c2c01094480c01940d202403d001184004070500c3d41c0c0018803d400340c8440245071003160f9601e1441000d5500d01c0c814484a40d00c450350400407100704030758401016000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 463840314 1250 463839064 463839071
    0xa0318060c080619120204020a2a1106030402031f022106041b08040b06031f0203070e030f0712020a0905010314150121050114070201061e081906 64
    0x503031980d2003222441a0100041010702060041a28150ba600d2041c00302000700c0c001d210303043c007040c0d14240c0c16032400280201c0d00031849421040c02500d0000420f261035203612580ca41c40100c40001601030780040d100000f920900b449a4182070044910454010300180351601d04003900011b2850009007511840c0d909105180b0051817003002441c03200041c100c03482d0507040000801048410800b68000103500b04064080b205400281c450742c803c0e04840305180707507030702c0c0c80c040b82c140b40408444900600a8840c4000850740b1507024502401440d44d03582561806481410307a20314041c01143c0c0c490384544400c000c0c0c0c490032078048403441d02c094001841c0c50b0356440c180080d81c00171b0b08103d800b05555140d01d17521f00c90410054402141110b0401d06075450070100e013400c400100a898090341c0c0c00c640303100500c4402d4008052205c0c0086c031170101c900d80303014028001d00c41c0380202c00101042c1314143d2403c03802c844000056800c208042c1401320742c0e02240032203490b56000101c582603203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 463841564 1250 463840314 463840361
    0x3030510030c031407080d020a05011103040b0408130302030a0309140a0e1504110703230915030403022d1905030d05070212040902030a0509030a08010302040f020c0a110a0b030c0a03 80
    0x407e00c6411001c0540e500105000801403030b05a003521099041405014014030810022820030125140c000e83c000384107076615040d00c1d00d041800005030300003030f42611415610030205070b40401d0020455800154050f12103680344208003c2d11018810b8070180780130350020a0b06618074841805c4000c03001000000c0000f40100304110340d030011541075001c034040c1b81010501d0f40c5a90410030440c0c680040b002d26029403c2d001902c0d1003c030004105d8800d1010001908050080201c9003070710340014840c626080d1a02c02030030450318210410301450080a0848110300455248a103074907a00801450070103000b044140b00400004008004510a240c0c11002624420000f0809801e01c0c0c50003507543e1500d59585010b46e03030050040c4485500401680202c9075000c0e40281c1541d0381201c000c1441003090380d08901901803000c13402524050206044200100503403152030b00a015140701d050a0b035905460841e60100b150180014141001b600e0740c102d11a50044c0c0c41341418018a41c1c000c2e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 463842814 1250 463841564 463841579
    0x903060402120f0f16060c050a1e151d03090d0605060607020909010c0306051503070305040c0914010905090a0f0f0f0611091509010c0303020d060503011803030510030c031407 77
    0x44c819218506036401a40004d4010601c2544400260055043c000000b454540d95079036100030031400a00060445001078403e87c1c40c0201c41c84201c0c0d00316610045040b00a1118001003030b1160140e2100c1207620800d0303038030a40100a4820030000100396000c0400903413a41030113018020083c9600c50b404110007401a81c03040c50040c0110001c4000003121900c47d030015088503242c1e00058130030070700c1e000409030300500841181d51001440c50301003903945a51809411800301600300900341c43c106208000003900d8402c00f94100e9020303850030f210986920410720745800707a103500540040c504020307820104404078000014288030b84150550091191030390300c00c071035190609840c04034000034448003c1c0f0b0401074000400c8060504a841c01813000c001a280c0c5a410100070145a00494108950642c5134482c1c00108000340007800f94070a000c0b04011040d07842c00c0c0490200b8545008144020b081213124400d80c0c0c0c1c0201c0100d140c07400e40e150034500049609030254644915000443c101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 463844064 1250 463842814 463842823
    0x120b18040309030605061903061d030a0509041508075406080705040b0402072a120201051b01090f0308071d0609061605030403030509090a020903060402120f 69
    0x5500a07902c0454007030542c0340030003d413070000e842541700318080f030707803003820740c04008446400c60b03501c92400503808a0780c185020030400074400c0d14506010200340c034075020307401000804000100311800c0100c1401e84e1076044411545014000d081d9100810030b000700e4290b0408841c0c404c004d80381c00c5100384c3e000c0c4044c20001040c035040e00b5524403410520103840c00004d103115403125005c5000e2103842c2c00c001016544282a1040c10f11660701c80700700f0605516950b04403104035400c014a2900943c21083c040301c040402c00303442c0b40b80300210ba8000f500c2000d284104403a00e50503940ca5150100316000010750040210420030313155607a01500000403010640440103510a88940e4501c0c902428040c100f07410701e01c4660041060011081c079681d65150403540d50a800701d8180d0b403241205140040f00740c60080c1c0051480c0300010f004030906804c1000340805200444210182c5e40c2d82d06648000d902032a040250558084030100d00140381910348141e64112140448100c1e407660f0146a150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 463845314 1250 463844064 463844071
    0x70210140d021b15040b07090305010f0203090c010c080d0b011b110108150306040b0907080d1806172403030a0507020a1e0b03040812070e030105100501120b18 70
    0x1403a42c00603034603088901a207000041000824040c000302e140b81c480301d15100d00c0080008000c40c1300e6200050b041c0c1d00440e1444003079900040200031086074181010020760054541d110700c0d202d0200c030200e2641c811581c07140550303888182c1c0c1d0704000b0700700d070200c3c040c0116100090500c4a644180700682c910800c8010920f0301500c1c0c1003d403089103070005094410b000d420741c2030b44024181030f4516605e00040403504603610050303411495075410260350610500d50070003400c5014084111083c540d1141d4554078400001e40046c54150382ea00c801d451001c0051514181c00c1440c000040b0005003211940300314040600d034103c840c5032031400007400c41c0e20020210010620110303100080d814206103042c041d0640080c003858502c940f44a8a84450140c4284c9440d0720300003002030100400c00d0143e0750030001281d9800940e0030310000142c2068400c03048540203600e0000054042121503090104485068441b0b26181e0140c1c0f2026010302a928202d41c0c10800c004900d04151580540e803c1c070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 463846564 1250 463845314 463845337
    0xa02060708030703020f2b0204080d080603010b3028020a0f0603020a08010503010c0504180e0706081603050c0901051b0d080423030a0e0d0f0b10050303070807021014 73
    0x401502d0300001403001004113040d01e0341f040c07040c00b0074003240c400000d44600510303240c206034030255500740010340546241918076810054001010124445807c007103044c25106c0c10740300d85201e141c0d030322344c523a10707800c901a0b60301250b0301381e400300d02001a200c540f0001c2400500000394540c5c8480b41c3d00100501a800100041d90000b0352000c3c1d240e000d052280507003070031030003403101c40f9a1000c02481d40c0aa40a01c0701000d103101414200c0e04455400001030782e54240503103200d40e07079800000c0c01c1000102d405039980c03401000003e50491207481024410480600304905090701c910044441c1d82215002c21b0003e034000301400c1c03510000f081a408104d403e070350360010501d05498080d09006440940003d0070803001804403406c0c2d1301105a0f100a100c9161040303441c50020300088010b440c45001412a041840e444000e00c0510019503100d03902d007a4100390400e64030000d042d07a80c131901402030880c0d03005002840041c078002d4808244885207144c45a1220300c010428401035102868a0702c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 463847814 1250 463846564 463846597
    0xf17010f052b0b072003030103060e0c0108010b13031406040507060c08090402070c180c020607020d091e050910030c09020f07300e09090a02060708030703020f 70
    0x40709207030851014440d603244440e5010110b5400e4030311414a08907200040924a440000441c100c0c422020820420180c225041c041e144c0545620340701c0c0e001713000c151130007824080c500d200003000103a20a003140341079550040340d1b0300e0f01081c0c0c81c00307130050340902c20408442c020000100c0c081034148400c0103c1c40000d410070b41000c0c41c12034a400c020758000700c1409446400300e070102c0c0f00403055650044059070f015036200130a08d080b5210200641080c0000130420721007001e8800f840c3e01c500403a00c0241c086070f5090312500030590f82d5070841c0e030003000040c807920001c3c440043c80000035084502505c00f20f1000c1511400000c6079010102d030392814160712aa410001d101080345200c00418802804514011138061090414850502e0140241c1c0342508402904d820400c0418400508501c00800101c00079000404e00d0300703400403c9125400840201d07502e8840030400e100c010f13a0060001d0310780450b50340c4074a0302d508000c040b2001e0581c00c0c049000c100d0419401840c0c043c03000c1ca1000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 463848920 1106 463847814 463847819
    0x90b0a0903080c06070e04020405030309120304030f150c0e0d030e13051f05060c031b0c031c021c0909090204020405060711010207150e010f17010f 65
    0x2031490b84005800548144049059030043c1c209945d118080b00c80c910801091780a1800f4880d40340c0c0042001111034a05501c880507a20a20000e40341426600d849a0451461603202615294210303410b80f14071000510031400c1c26001030401d540c001300d00304041051000f81764070042c18000440c81e0740030103030350320041e00b0b5241600751030034011840c0015060301c81f40d03404103918008403403c01c0c01080a203040400c0d20901100e00d0300450801509a220040302c804140704c2e09030ba402011404c60290f00c09000503d070035000100380c107800441441c4024648102104012400480c00e00d0b030b2059a5403100b025000c0710107403c000319800c445800020000c6c072980d0700c501e510a40000f2114100060490b407004070050036004d5031112075481b02c65611665001c61800300050016a00d080150f0003410303070038511078191501030f9610140d10b0540b00500c1c07080c4c00c0f1100f1600104401c = true := by decide +kernel

theorem cover : BRFrame.Cov 463669064 463848920 := by
  have h0 := BRFrame.cov_init 463669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 463669064 ≤ n) (h2 : n < 463848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
