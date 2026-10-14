-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2856
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:56:22.978233+00:00
-- url     : https://prove2.me/submissions/01e64470-47ba-4335-a660-979ac2c68c4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 513489208 ≤ n < 513669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 513490458 1250 513489208 513489247
    0x1d060f190903031e031401091a040209060430150b0406030206030a0c09091401170706021f020d050901020a1202030103080909090708190b010909020d06021b03070620 73
    0x8003891030b018113004d91000c80c001c101640380390080c2d540e000d00019000701d4582c090703071000c251054100c24810700d000600080c0e11522030000d400ca6000c000404c01e088444040e0518950019201d0385240e24802041401e904143d805440f8002c0508c1c191314811844e214032600d0180681c0d0510116203160006401400024502611585c8560b00844003500c60000303100a0b0031285020030030f408101200d044900da0074054407002005245072184035000000359107007100d00d582c0c0100614414055500700d043e500c0806001c49a400340032f400328000da00d001c2e85100b920403500050f02d80f205020b0092003180085003110300b82c0d00c100014408501010120f8800f008240e030801aa07490f000221440c0c480030383d20005960054026420100900400e04a003160242c0c80d64a03c0b070362a10300e20400c5800d50a00254090500a81800001d440c0d0300030305200301c100110091880340e2103000f241142c0c4110002c0361a180e0301d83c0c100c022100c0600d599881c84222200c4141400c1e404a0700032100c207103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 513491708 1250 513490458 513490487
    0x50f0417090102030904090602030f0705250f0209161b080f09031513031805010e010f050d060308030a060b040b03010b07060f02070803100905070e011d060f19090303 73
    0x41d0806a40d000704200c0c2c4c03455401a1041043c5642e506028000303420a0b40c0320401d001400c0302003102c0c148504103850510040305494003143c074003030b05500c2090910705c000702c1d02c8611241002000d0303035070104440e01c00c000400c0b0021001046000080c1080d12489040100c00100d541303c42c0800d410b5020703110710b0003000e51030300c0e5565003050010385021044102d40505800f08020011241d09484903030b46014400c0d20740e43c184800004003020640c005000b0540060505050b201c0c0f0b0f5072146400d800e00d0a030b5400c0c11761030240c0da90452001d036841604180c444030030005c203014031004d50b40300f501b00034001d1380051824a07040c1005466148410310401d102c2c88404039010061000b039038852103840104490445d0ba440b41c3c1d2800c4034540d001200c5180303081e00d040784000b5482507240a054400c012998640451f4010f003001543c0b5030003850900004c1310480c42c08003155442e1500200181040c01c0061034a40c1c25103044940900c41050b0705404004003071070f0400029801c005007494445 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 513492958 1250 513491708 513491753
    0x5160b0612072603040e13031724040e0c0d03120501241103091e0a0b090901150905040515040f0b04060504050f0c0702062803050f04 59
    0x3110400003501c0606004803040040c003400d9400501203e0307151982c0d110440440c2500c072400d007040682500d0703008a00c140c0b0007031540c07080019108803485041031a41032080c00d21031911004803004102181007102d0715035801110400e0f0740c0103c5a60030800c06c98040844040c030050034000512500d0b0700034068541c1c0201381c004020001c040c051101c84103480403d000c100078035a540d000b5140c540745150511152520441883c80c0054403e007402041401d0303604c011860034601c241801071010903052641418a8082c8840c41c60b075580304850f10042c0042e603c9152a4011102000941841070707100c41c03105241100c0d1101216004030403a41107030022500041d10307680d100b03092152504413598159116240c20109081044250300c4815299070950342000002d446001340011900700b6a005d02e812401080059401503814000b070002520203000b46007444080d1002070710740080704521941924014440c03182c807a50500c101c0368050100305020700541000e032a0382c00591113800d044660f04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 513494208 1250 513492958 513492961
    0x1404020a05010f14070f020111031e030a06050a0f060314041203090c09051024140a1106040809100c210e060d0e0d26100302121c05160b 60
    0x3140615002c0c0c60701c0c5010405a585c2d46880e1501040340d00850300e080740410034080032031544207400003e60351a4907501f111940440c0003804581d545400040a101c429a101d01001c6069100c90280314018100150707110030309814a900078042e20300203180c6011141900702000003080114054544c941c000e800c00041c0d509040c20302c220100820b4211040d06402c00040c04948c7c4084101c900446001420010603281d03000c9084503081500d082501c0000d10744140d2141070480d0400411410800307080c070901d000512906981845403c540c10380e19100c0128401c865420b0001c810a00c50229250601c1842d1007030380d5081402046410941c1c440d84101080107005000e03148100c040d24005203000e450707500e22044440030704842e42c01204940111502401554020800315070919401d403001010300c0780031032421484200040034040c1d800c210507800400340e1500d40d00340c107201c800c080c05000040d600e007240e516100c040d404107104100040210010561a205c01c1040c11075001400002c103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 513495458 1250 513494208 513494237
    0x12020906042114011a06090a0330050f0307030527010b01030e0a0305070201050a02010f0612030206100e1b0f0f0702090c030c0409050603031605010606031404020a0501 74
    0x140200d401c040b10300040d20070055201484000884a5140f0400c00b5902040611601ca42039400303014264002e1215200c02102a15040c0c014110f01d800c040c10755080c0d9035590300d50307607034441e112000e44018a00c4070350140800701c0611046892401d07e4140945081e800c4500030007144070081480702055520004600341c05920400c0c3c0c400312074104201d2400c0804246c00500034214008a1400309142050f8a442e4410115400e010541c054468030b06040d110780065905038040e10100046542e04c8100c1200102107210340c00103080c01d464108a03144240c60064580035004d000000a525621403c1000314000b854041c0d10008450b80003801d84854441040640a00061000100c00100d000d20341c243ca0307840030b1f1840b54003c40e800303425501c56521601e80d074070059901c01d10401d800c0105110518058000b80d801c0080901140e2070012003074504070503401d03901c00c1110b01d44d458240401c00c46906004c1c201c0642e00301060b800c807d040580c001800301000c0c1c421181440f40c6100c0c3c8811 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 513496708 1250 513495458 513495469
    0x10608010512100e01021804061410050c01061503060801020c0a06020f0702030a201c08090d0f12020607050a0903060903021207050c0301050f070c02040b030313080709180201120209 80
    0xa690400da0400c2c44030303181301024103010b03402203620070024178111001074070b076807810380100002c0740c1409240c0074110340d84a0600030400040d080c2501800400c01104900010034420500100601101c08104840b0311100500351880b9601c01d0340107030700510020070030880101e034284d0080e070b0101005903100520456002c0c58042c1d20400713981030158159007001d2104032903982c00c8000a01c06910480080034081024a0200f800e02c40c3c40603d58400d04000584080c00030520f00e80c0041c040c0c68242c2031039445102d1070040c204104c5111640c3d21032140b02da501044259040485800d1003800e0501c1d84030005c041c0f03009440013401e03160f115525242410700134000f20102c002d0005940d6650642c5080080d1368501800303c41d4000e619040011306a180406080c074020921035031100300600e0f02d9002c01c000f40c481c3c5114a0b034140020001171103c003a500e0f0400c4004e1070740f107015054051070304146c102100d00104038960000a0b40ca14880140c0e403101c4460313a41000d05c0300060311004200049038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 513497958 1250 513496708 513496723
    0x30306050d080d230708060a0b0a0503010f0e1605030a090609060209040605100507081c02030c070c0b03011a0c010e01020c0a02120a02030d050d1e05160903080912010e0105010608041a010608010512 87
    0x50700f80400590060120740c40b400a40c144d404e0034072600c40b41cee640c843e0f0604030a0030440720420440700ba2501d060060703105800640d000300f0301903000b140c0300607203856000c121504190211051507001274007881c40c0c14a80034200c010141203032019440d50650402a02078030490b40003c0c02900c001030503000007012000ca00700701510f4840c01b15100c1c5018520030586611010f026034200104050021b103100e2074600326416100b149480c440c0d0b9071020042007900c0d82052840c45019520380300c036012884002d02c06845920714a100400d003401d060f0061020508400304110740d69005892a40050f03280025221110180d626109076505070250f00c0c20700906800c04c2e00003001058880340d0010b403155030041409180c1d001850b1400a1100e0402d951034041444001e110103414002c0f20f0040c0391448502283d0610000045928000c08243d81c0c21201c00343c2041012481308000e10051003044085015240c80c0c1c1a1481019414440007909244c0140703c0d4503c2680301c40600082c00c0d000f1f02030003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 513499208 1250 513497958 513497969
    0x42001020d140705070f3201050904090f08090a06050708030f040f1415090a20030c1c0302010606020d08270d1e0f09030609030306050d080d230708060a 67
    0x5c1c0d03001900e0350b0122504101901c00c40030303111821000e07000800b1a003208004160035841000610701082c20040d5600e40007902c0240e0702a640710340c0e001c00715201e0b84162903141d10680e80d40d5030b2400000204055603104d03821500c00c1010038000d050002e44903504894102c4040141c2c810310359108d251058038039180000003881c00c1c100c68a050801740300022045806880c00b1200003032075452410099840d900040084c02440007210300308200030401042c4001e444001e0251540c0c50300310340104d040005460f061600d038421952a11041c558207220309805040b0038400f5041c0d0105400c001008a030010300f0452140e48d8101e00c000100c2c2c0106a203101c0440c03a041179500d005014000174001c0407911444004032005100c5811210344200c4810002d80481c0e20380c6401107085483d000010000e224044081c1540d401d00890f1990356402410b83c4e01d449842016901c41048448205480344641d003d000b1206201c00d0241100c842081c080e400074039451312060310b035100300020305149400e0b80300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 513500458 1250 513499208 513499213
    0x20a080d08091c0203030f070207051203091c0b0a0e0118080901030c021603230a2d0b01050103020d1e0903020f2e110a08042001020d140705 62
    0x5008103190085661881008048207640c800030844032540901450f007400712006070070400c00100d920b46000c040e00e07000300ca2071040f628499291408514030302581c606070350399540082848909860001c2070007044d45441c0040e20307001c1e412540d070a02d141c1000b17081c01192076100c51101c44612025406502014040a6002c42400a5044c100d50130342c01200700d0783c0000c5c03c2018038440c941c00010025810030388051441c2c0e4561031a00d42d1142d0000301d020103200c2260a041d94520404100040406140190039421916100d034403034803020503c005600c55400365200d02040441d40381e0a0709030440390f084c280540c1c3d51454007003107402807000003906440d00001d8051038403000c400780c0c13100210a109408440044100425455452514221480032030503402e603500e88c01d4200c40f441c5096003100220119609c0322400030152150820090700000070038100400c82441108400200340e82e06000991070f0002101000075260b80b8020145414892030a040c0310600b00d4a1044480840d0810705 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 513501708 1250 513500458 513500473
    0x150f09030801081005071d030f07060503010f06020601050307030308190504051b0301050408091012060305030310151416080403110f010908190c0905090709060f08060103060207020a08 81
    0x300682051020f001e01c1e4042d1044c5440c4541202061040c2c03409843d9549414480b45112000382440041c4010101c1c1c150140307160000714600c00b0070541c00909800d40b1020345030740c1400c0c12100980d0941c4d03c072500319070142d00104180d071004144001070ba5090700e48031131a42d0f0340709140e542180312511601c116525000400040c00404607550798209184070803204a1405e1004041c03d03540151805407000e4010071541480d0314100340b00c19101815820300340d140549070420441141d40a90017650550000001c002103a64511f054030090700c0d01d40d0311075240c60321609008180400780c1c10940c0006100041829450501da000e0f801003c0e880101c031a940c540fa441c0030b0084038a17030440507000d90f000143d5120f041d07000d81c05440682e12000c0080a05920080210304601122003055030607482c501004640119140210351190246038020004d06180811030030840d005030307214694880125005000c0c42c840400c0d442e0440c0d800c0700015032900704600010709070299992042607107104510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 513502958 1250 513501708 513501713
    0x40c0c17181c0201090b040f09020c01180305030f01051017061306030503190c0f030c0f02040c201b04020d0212090a14120406081003140708100e0a150f09 68
    0x81803001071510170385e51036035499901c03908090140540e0141c0311030281d80860500540450f41d0240040c3c0c04210300119001d00354103501c5604c40c4021030144c00083c0c001080040445086603c00c0c01003c0c10f0390312017111040440001c0521440007111941c2950790000b0072842d0381c0b000b88050a1200080b0b00b048496078038030f011540e030360200001e0b40b10550014100440140601001c40d034643d0090f04070010001c82d560308899a03101c0d240300725802c09000410b10b001d41c4a40c07080509520450f21b07079001a800204400481c0e01d0601c1700300d500da902480307400c0f405001c1445100c40d824025900545c031401c0000c05c20010303005d00400c2c0054070341c18200300b2080305000968416144e0041c00c1c0141014000d2024070303101c281e9510b0b2a010450200000c000f00b603c90381d4a5a0300030304800c0d9075140d5540303950f00c040c03c201425025060715407000900f8000c4104c1406115a01450000b082081c08000340c003817900e42c00300d400c01908002950705240003107981741c2c016110b800005c250804c007005092 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 513504208 1250 513502958 513502999
    0x3070b041406070f081c050a0e06060405190903090503251a0315060d11040512010b0307030803071e180b0a020606060c01020706050a0b040c0c1718 65
    0x80c411004190400301c540030311410300300200c0d410b090300058025070f00082130b1103a210f503602403a000844a01c121420380041c48191040c98000c80041c180840c001d04622855403400c24090000d5104a1400c0240122040e000f00d4203030300c001044101058010103400e041c0c40c41000303a4804c40e00741c000c203200680059a440e8007040c1c80b10780c1d10b5543e5001790b20340d504d01c20b12011810740810f020034204003141ca40300556000340b42c403d20080c1124509103640780b107039041c1c0385000b8180c804020041024091458164175150a00100400812420160400199035140d840c8806040e490000001c21070281c86140034261820340b06943d4001e480f00402c005002076400e03da40210007211440c0400e103510480115521400c60707500904142c4c4950080180da0341c841c00e02d5880c107660820a0070300140060045038402d40c484800010303c64059018042642e4441010404001c141500400064854a00044150810f60045072a0690301641d8850002c242c2e14055011400390341c16205c10024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 513505458 1250 513504208 513504217
    0x412080304260f09040b0d05010906050a14220c030b161d010e0307090e030306040b1215040c1a0903070605032710050403090305010b0d15090c0503070b 67
    0x1070706620b50400001540041a03815a0b401058054010800324865454440241000207802030001505500d8880010801c440f201411101e40e511600d0b41414007181d4410258008005002400b1001141c0c9010002c0d030740060181300806806084200c426101c1c12011114a500c468403501c03143e01c03801c1ca10000310086a80c0030844c81e04400051000744510008428800070602110103511200c0041d80c50308503404070503801d44680e00b4005503800c0c25004140d60302c01c520000c2d40c1c0d80d01384407051009907050b90034094010845c1140010980f00d00080074a0421001901c0c004591941e103482100c501c2c0c998042d1500c0d1a8070404c0820b41e14401006204822045084854150351b030407094959000880d40d8480c0072120004841c010303020301c04c1e14125031840009540c080d068000230002180d0041c1c609800040d880441803003044400d10401140490448150b9040b01d11035443c10a0401c0354110252026220310164040010100c60080500401003c0d1303404951206040e4038240c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 513506708 1250 513505458 513505463
    0x41b0b13050d02060a082e09050c1801080c09031507080a0917281e0215071d03010501170c04110f0c070b16060c031418030412080304 59
    0x1a144005a186440c90740a16015805040304d0300700f05a0040541c1c83c60001004102d0b8050604041c0c080000400701a00507003400307d81c20b060141c10304007850304503603000744041003040c010094460164400304880d4048242440d01503181e55070581c076890326002d16082c4035098420010018880c2020302202d5115910330b596524250740c5a8010005641b0640c6000d0001d01d0402c0b03028410540ea500113000e4940e494844002800c200c00c2c003010544007107a10b0a0005080000078030800014000d030510407013480c8010000b4404000d121400040c010b020041441000c01d40ca40341d907801c900d501800680c1c010020440703903a44845150032645055800901c50240c43c40c0d9040c00e00d4107205140b0120751500410b030600302003c6a0099551004076001c455201d03940300000c003d1b8002e030003407005100c492301004480071549080740c150707442221800241810141c13a0403506440c8090744d9401080041c400c6c0350302c43c0700050581140718580100c4600c8840c03100c00c80501500d040294080c3d803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 513507958 1250 513506708 513506737
    0x309060e0f1003050606070c09060e16020303011e080303070207060311120402090406141003170f0d0c052a0601080c03060703020d15080105040b1f030b041b0b 70
    0x1541841008004a551107100c2e51000500c1d0098214a200c0d602440d41301501404080c6003800070b40b99100080625440200b032aa11902d082c82106288200c080d0000307401851400c11903482540070b91a400140100d4045089141124800d400104040340081880200f40da640741001381c4000d440740740d01d008280209082480101c2104101c1c0c045580000d18441c03803220720784540e400c000714090058010740352692110030034404c01040b03104c440e01030041108400912451482d159074000c40041ca00011004240040d510b1980e007502250302007054600000303008460303400191414000c00240301d0380010030424491440d2013680d004903e003103412080f00c1e400e03070f600c000d200e58980d090b51180d40c040d0042e031302141d01c541c000d4020f02852110b1a10200b154080c44801c4000e4220741c1c0c0c4401d04d02d030b4481090006021400c3d0b48290807107045d50003418a411a01c01401241c9143d100003040c14032510700050a10000c2e500d004d142003102d240b81c920a90b51803500f4031164201ca94a44441d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 513509208 1250 513507958 513507977
    0x405060a031b05040f0618030c1203110a11090a060b0313020f100c080c010b04090602031e0601081618031415040b27010c110f03030618190603030906 66
    0x2980a80d064604030b509036041d1700b2070141004c200b214010341e04402080c4000460340040001003083c58071001402c86501d01f240103031202e083c0104031225003150004990041070710034001c03840c01320200c805064180c500c1d13407890311041c180074004c03c4a81d01a40301c1a00c080248031a001c1c0c99015901958000c840388001603221908200c0c034820005030607404030b60700040202c006503d08010b803086403101c1380005144015480401c0680300311041c126180703a070000800c41c030b251074505002001000c04005c585945015000a403510001814076000c031100390f20608511885091a80300c480b8602c0c00000c0801d680e0f19200d0403058801c600804030b8007d0700b564102c418030940c00a0f10560b080380d01c0d0080c1d078542c0f5401305940c01e56442801c1c13072a42d0804030071560720303424011300341650b00560b51010204c4503174018609016200d080d14403036810820520849036074992178662610003080b190701180c0c4070000e1000111060b404503d01d294180354001041c1604803602e0000c41780d6540314100307203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 513510458 1250 513509208 513509261
    0x18090c010905031c27060806091317030c1e030405121207050711090708010504060807050d06020c070302100201230106020d08060a181a0411040314030405060a03 71
    0x8440203079840c68070391884001688030313162040a401d0f10b18140004031404044aa0580c15140381c429003150000c00e051505100c0306062100350107a01c900a403d82c40d200655130358a4490345032219003031120070500400410b028102074000c0707441c8022400f211301c00c0c140c0101844685070300708030b600742c0d118010220000c5400c81b1030401c56501079822400c00085548004003961395400440050f034000545416180300740d1140174400340207084030b031a640e02c079600d0f0400700410f9405a4100060503041580c08100580340c0c01651400c0c580d202c0300140c1c582c0310b00201549403441c1c030752010307501c108180c00c010301494045d403184252042c0c1342d021710310b1758540b00c440b01c0c100d04003803003004010ba016000c001070740f5118148080e0462801401d12800941c0d41c5100d4014100c000b5504000540d2110200810a4420000034603a00152030920150000d0141d04126005500c4080c1080c120400c0a003d950014030440b030103044000d20041d181c240380381d401802840d0807810340a102408005030000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 513511708 1250 513510458 513510463
    0x60d0e0a021302090a150504091404050714010f140708120f090105040b01060f1202220f0e06090403020703060c0309050c011809020c030409110901020d03020408030304080918090c01090503 83
    0x1202802400d07095401d86004128003440c10407001b080f0800c00c6c10701c0080752900707117401b8a000307000704119020322905180c201030741030043c282e00400015048440c010380f184d802c003000154200b00c909244101c4080112601240d04c5641801003030403000158080c5400d80c0c1582c0680140c14015005000350f591414040c00c035103055902514403052100100002c41c484c240c01c1c501d2454600e4070b140c0001354154244143e801c00780601208200d40300d0205007941c001c440410003440000d81c0018241e141916614507100003078845801110154001014075008104500045501c46401c0140c204004401802800064030407141405160301c55101036204070345500101c111010425903d07443c2100784030080d4000d40f030340035141c0014000010488e94070301c0781c0160004280c1300950fa40b1031f090002410000a03c2c4034805141c030522041c01000d60010540380c2c055840010680c2c0c500c0404006904420f5004101c400d039100b85040082100001c40c21180c000000e803100300c90543c5a104058 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 513512958 1250 513511708 513511717
    0x618030302060a02030a02091908160e01060f090305060703062301080601080618041b0605040b090f040f020d0f050702151609150807020601120305070b0402060d0e0a021302 76
    0xc0050380520007081c400300c100c0e4011038110703441080040c5402c881e400400c00c070300c6280c5015204d10301c14020070481e0601c103000c039186000700300a5400300c250800700c803041c0d1580180240001c1042142c0807046031030056200d08061074012084030750500e000c107002001340c00940520f54032080c00c40301d0005507400d03004041c1031124058440440a0381c6010044030302c40300081c80241c1c0030100400003d031400c0000b074042e016500540c0c0d14017035500144649000c99050b41d20045c03c00800b00b108011910701d01080e25101d030b44c1140c2540d83c0d8070400b800540900208090f206c0b100d0310020301b80c44805410740c401ca06003210b100c2c00f0b01a40c0d440c04000e0740c95000c80d44104070000345640019200c030707001c20102102003c044c1062100191a90790740d0340c103096090207200105013404140700742d640e0100b100600402400e6507032480400e20366001060390244090040400d480140420110750b28142540d04496140030300f0028224510361003552400d520009078024a1041810300782c41440b8001c56 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 513514208 1250 513512958 513512963
    0x120c0a06060b0906220510020a060c020609120705010f020409090201090609060c020d1a04120305010509011208031312030212100f06050f0c0319120e0705010c030203040305010e010204061803 84
    0x260500b2018071131700207202c580d041c0a840413007942034041126a80d26003840c054616a60062410050310301d05282107415400d161019540b20f001005480480012107882c601c0710303984071039114805840c02c18094075540d2038203c40a8004680801c0c5c0741d00d60f600c541c00242c000d0b40c2c0c2104560340c580060350004030345e00075400050080007800000d400e11018040d0041d11546070f0468000d404140c0362240c44007900d04940e40a95115a5804150b1500896016210403140c1031155498181900c0c1c00c442c000c503000f44404008000101503854002d82120a0b942018000b1040c48800c0c2000b802540003c0843c002030b4a0301000c906000c5c091010340054440400903d820f450910704152042d400c524030410742d100c0104400203140c04103001601611000c3c2c14080d0350301d091030401802036041c40700c41001e02442c1106081003001d0008203002240d500b820a01024800c50404174154032454102402640c2400d80024031180305600400407241b81e99aa030034005030000007004200000d1202 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 513515458 1250 513514208 513514219
    0x6041406010e0f06070b0c132c07022e0609021e03040c0306061e05010c020a150c050102041706010501090f030b060d02040c090302040b060c1e120c0a06060b09 70
    0x20b800203420080c946040ba80300040015080108558440490285c103d40102e4840d40c04500e124202049a411001402500b00c6912440d4142c40490010310206116042109404000305111900900c1003074140056116000c913a100d2030009001650035204500c80582d191030300000d2500f41920a881e0080201c441d0b000f4044c0c110030200c2c407903401c085d1064444440901c0000b00041e902d110301c5005000c2003540f2a48200ba0310140e44998220760b1100303040c80031900030399005a6130b03005c0900a0f00c0c00102120590480a001250f50001480d0010030a6200103008201c1c00071038095806240e04510841d8696030300c410044540400c075102d030104640c12682e05100080119114a41c03208001d010a411444140c0000d800e941055850b040401e085000c1807065040c02e018001083e41c0a54025141c0740c0130705540340c1d079601d08803000410200503002d01c01c01100c0903c4081d03411002110b0490700c5019400000380c0380d03d440c40041390500d2a040d030000b20b4000e100280e40070100002c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 513516708 1250 513515458 513515477
    0xe0a0201090906061b11090915070516151d06090f030a051801050f0a080603060f060a03030c020301140f010e06090420030a080c030406090b0414060706150e0604140601 74
    0x159170560045031041280c3c250041940004a9180c00111502c00d01c1018001d00d1a0041c080e1300809164000c0c00001c1040300c00c0007d070580b680c02c0b03001c3e0030403158440c84100704000c4030a0170800030403080d0094031b0b0751210b913421040c032807000082150084030700b1402da8001c010140071259a0b4807030102446e002c03400510400700c8448440c0318003230005006040c00c5181441141c83d103050f07540b101d0700e001d000c40d1042050002c281410002d41d03500ca03034003850805650801600041e5800c4003440000d080120101c2d000c0704540702904151080c0704103602c1c083c1142010b6031020a80b40090043d41c0d01d070aa104005001464070380340c003501507504903115402405a17268118540141d02c10500c2e0035100700c035030b0700740000c6446004001901d44107010356104c6061000042c42200c20368801303090460107200500101d170078040c0f41c680c40c0e00e04417280c2e592690689042c2010300001524100c080320309001c0014202607800301e8138459a4100d504200740c0c480c10042d901d8643d07080c4d8900d4006031000302c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 513517958 1250 513516708 513516737
    0xb040206071106030a090b0f0105220b0607230d090e0402010203130308040503070603090c151419030b010c0b0402210304090e0c090c0904020d0905010e0a020109090606 74
    0x8081081c0514035202c000c490400110b14158030544422048542e240d100e1400d00111600140d0082c1c00d488020003107514103030014140400c0040001d4001c1e01a1109144618541d03101d481c0700380b0054446a16000300741441e5600510b801142020343c000030340102000300d004a80c80700c4040c03c07602c81c0d0300000e00303040c15981707401d100420803415032108212030000c421030f4801c4507004501c541d80781d031303079071820303c4103060614603503602500515042900280010784030203e14000e485044134a83c0c0d40b2a103104e401c50b244078248060869130540080d90840e4071240309400200c2e2603070f47c0c80510450111030011151000c030940050410b103144404500185014042d1440700c00c220f01c10010200900c001090440c0e2090b03100510b0103035a2551408001c1c0280b104109140c41100d0b030b0352951800030340707070522403003254200c520590340002d01d040d00a0403070740b01c005d075141c1001c0200241114a5003c035a1407804890603400308011040001c0c4a1203e40952025207060b81c2e5104050441003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 513519208 1250 513517958 513517969
    0xa270807081504080702040e060a0b01090f2913140a1418040302240405100915410114240904051003200a03021002011407111005040b0402 61
    0x16504a034007641b0386103681c00f581010030084c0d0003a2b240d03c40015901e600307040003401890041c2c0c00781c00c000302c21150401071340580346a0350480110110820036100e4070803c03151544c1c400c803414908255403030100441c907a003031610380486106040e40c0300c0f80c000391110340c2c14694980c0e000d82e41d40d0010044200c044030a00c10041d00c0c2c0c00030700c240115002d261104084000329585c03402c10301c03540b490000412044c44410010b450604071205020410a5415143d41000c1114038000309042034071402d10021081c03107140000c1c45c040120003030740f000da5031749200d06006100a1040141407080340d000402c0c00048207144004440c0010705034802d003110b4035200700790b50f101c880d44440600c10034080c0340c403141c03030714000c442c464020107072138641041c1981f52003142e000c1c042200b0240300589080081050b150042172605607074045504002003000000105d02602c48a031710070710100c44590500c12000e41000c02d050b445410031080d0341450076600034000460310b040f14042c0c801d0707410b480402c0160500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 513520458 1250 513519208 513519217
    0x904090302122d0307080103021905040c08061207052b060207060c20060c0f1b0303070909090c0b070507080304080c090f04020f0103020a27080708150408 68
    0x3801a00c4120000048001040d0442c941c0260500ea007010802143c0c0c40f00a00400050410341459013582400342006001140500000f402400081000320658200c421110010320b40140b0602c00c1c000000030007801c103130040d241d85005500d080700c10140c0910201e00d480c01d6910151451452140c41b0104108001c8001d071851810300c5c905200101080580c001452854080d5502089222500d10001d0031100450310800a6105510f00704040305c40104005400092501c0390741e4560035001040c004921400e20848104011503011500b40c54020000c1c510826084d1103050350703640d59801e004240e0388480d034001c11031a0005001c1c010100144041c1503018029422641e206032202c0120b0b00d150f115400c5500c0e190f000c0d0045035958582110781c0c0b503000d600b10740502c01c2814a0341c04204400c090000d103606064001c0303a406010382c4644e0304145c1e18940140c003070403d082d502c441350800741c00e20b0207400e04a00441c9408540301a000600258002894144142c1951241c0703070182e45801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 513521708 1250 513520458 513520463
    0x91521020706021617190c02012f0d0203040f09020313080a0c21020615010509030d0c050706020c030d0f030b040603060e0706080105030c091e2a070206090409 70
    0x50920240c0e0104110f4805002c110780c0b01684825030008606003800c40b071620742c40c8411041000c200c080c40036000c000c11424180c0580c00d12080043c02840140c0d807100150030610380d009540b000d8a0190b00507218810307070303901010b42540c1c10b14019400032a100c0c072541c051209a110185d00401007083d00742d00450340041d040078494180361040d81c0e0f481165019a0000c0c0004400070300308400d1048000403409c0e690b0f042c15812401201c03540010392a00001060702507418042c0d400c0c4102c0340d0003a8102d40c90047c0080c1038948410310b20001800510040c0c4050780c01c1e01c5078250100d510790001410180d41c1400800030102020107242c103c500c444080c0c0304008254940344c4841440e02c640c0a2a005540704980200b00b00c43c060041034505600365000b0010800c11400421a43d107001c00d0107000c01405548654aa90351940f4020f0b40b030716060740203a0000650000c01c20a000c0141d04070036502030460a0800e409407044200030301d03010340040a5400003040041095900d040d40c028010b040c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 513522958 1250 513521708 513521711
    0x1021e0c19210f1412070e0f0909010218030606090105090a1b0507050d020106030c061b0c030318170d05030702011404110f031504060908040305010e0706091521 71
    0x30820b00000014030907803290000803c8621240012464108120459907003140c80d00780d00b400c908003040d15140301e0281c11702e0248103500040d03403c1c07510350f0001070003103010142c10400c460810050f502c2c000e500c1400180710b04c0e4801140022245000300c1c003640545002003041381aa42000704204c0940c82c050040c0c05410340d03034295040072611020015100030311646030389483c1d130030034108182019a03401c030316030441e40b41c042d040c40010310240a120990301c103450814141c0a07680c2c2c0c408038018068070081d02010102000108040d03002e800d1215070450380c1c0c00e11340704640d200e402604031110a0501c0142da04141d000c95103040c8035070040d60b800140c620000c1840300d0f8100c02d40f0002d600aa4080e0760807011074034120451309100111406a0758254000c0c402500c00d0f0f404800780303800c05840101140d0f10341940d01c051011280c10749003c1c0d600075000f000300070801164195101080d200f0000490401240001c2c0441c000c0400d4002070400d0302c8046c2c8030140205a07000500202e03001a070700d603 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 513524208 1250 513522958 513522983
    0x23060c15060a0b2110030609110a080a030206040f03120c020a061b0203030c0c0309060d1505060903060f1f0303030905060906070c0303020c03160501021e0c19 70
    0xa40040100d0380520300302041a42960a021041c003403841c290f908184801c82c4104600704100d012010009126200c02d401d0050903103920f485d9071a581c0d002c0d813024081d40d051840c9002400320241003c1c092100498806028960b030350490750700c03940303030810290158010340006008200061108480c1921a251282d00013010b610884101e031040301c0e9020050b40700c2c03541d5800300304261203114140c030b1070001040e2040f084550f00030740d04e100041c295804a00d0201d22401e03090010000d507090b684000304910303104c10b070840004c0c0017031030002007403102004d0a441c005011305010301200e403604000313400b03455543c2e108090040784030009130215140c510759000c28140d0300702d00d56150001d1442030340c1c045105001800d085161400103051842950000700900850729004580310740b0407a89402c1c0580c40d00c0b0404412820742c0100b07002c8d0903000c3c1c51000140d04015043d401000c0d0040108680040c0a04083c070606040c01840034a4180781c0c4201582c11000322000d40d21180c00f480b42009500d207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 513525458 1250 513524208 513524227
    0x50a21030c140a11060328021908070e190308160b0106050a17090604200901090615020111040b0904090f03050304030f050703170a1b0807090f2306 65
    0x1512200c0b80410307003a0704842c0b601c100b005501030310b0005040003110450300794104042c100364050072039103903084800e001004003104110950161010302c00c40b845004000032101a024041c1d010484908000a12401c40714460b0f160200a5008640400310480d030072030306507074810303405500c5002c41041c03529001c030310300c1c0001c2e56031640140a031800e55141c5840d004020009051a404101c0712500b9007013030420801c0c00d14001132101d1b8020f811440700d01115111700f01030300e15039440070103080e00300c2c01c15000481c030300c46540c000904039840303008401640c40d15180100c0c201d4001840100c00305108010070400d202c50302c00030344000140103000281040c3d0740d549100d00d0880081d03003100881c00100401c014550040d40740d140c1d404035424098502802941c004040c98410203009039144100000720f00d10380380e140c1c400c000140507880c558480b21184080508049405c440c1c80300002e144000121f0320304030301003420084031801307070480c54182003680a528040d64040c1c4404d4002d481800500302 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 513526708 1250 513525458 513525473
    0x31703150409030e0f0d0b04060216051b100302090d14010e030721020304030809190b131403010b0a05060a1715010806090435070c090501050a21030c 66
    0x4184a9110116500d11400a10440d40000b2017030f10303c18041005104046204c001c102eaa10a5019400594559100503000d0040400000150941c0314045942da9584500d61060031000d40840342598840401c21040f4140e10075208040e030001220b0460000050b518244404156001d40c00843c511807541400d5240d608081c0058400400c4c809a11f210055201480c81100a40748003035072815007140ca81c00158807400c10f605004054420840c06100740134019140a8001045403079a02c4000d84038001c0b140409000309203441c83c0c3d030003a60021346414421901018005000c400c0707418a403c00b00300e00c40e00700c1c6182034144200640050500c42440e003030700f44100070404904544000c4003000500f002001407115004030004000c3c0710100f0041c0400c1a8031200401c0e80e007100c000c07800700c85020681480c0c2844801e0f080891800100441c40d000d10080e10b44030361082202da0307a200304010038680640704480c0040c1c0a544201085402c1c6002c00e643d043c00303418224243c0b43e20759038070304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 513527958 1250 513526708 513526721
    0x150409020f12030c1525090308070f02120d03140115121b050a0909050c0d0203041103010e010207140d0807050313020a1202010807032903010e011a01090f0317031504 73
    0xa51802d40030030425101c070000c50802a1074081b0012401005003200302402100903404080c083e401c0102e811800c10082030020b41f181c0384c1c050021740f05c1c0070b980c1400ca82e45680d41d51150b800b00e800d2501042001100005e024126050b20943c94a5031090f80c8041c2c070725402e41d14080250648900f42031450380084407140030100c11642e1019a00d101240005003801d03019003250783d4550400061210310700c094401c0d40c40c0842e82110060380e0b40c0b01c901c3d0801e8a9500b08091503055400c103231241c0d9034408103501404005000780384422002d5524029a0788840c52800c9800109040c4808144050300c03400180d0b41c001000c2d0800d0b000c4600580000c0c0c0400750aa000490041c5404030300e0045591018600f9000308083c1000d1041c10420108254185d0b64002008540707905141d0000c4240d400350417103401e106843c0c000b0491407080340b003105d03079148058840d00d02082c0d800c540001c51401002c1d0071011240c1103a00449540843c2149144551000e007a0310b041400094445100390350b94898803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 513529208 1250 513527958 513527983
    0x1e0302091816020f1c110d0306080f0604050604032006100906050609150d180c050103110a02060103030c0c0e070905010305010b0a021b150a08150409020f12030c 71
    0x1040c6a18000d2003580d00d0b211078001050840d0818401401c00040005592654036840640c1140340c807000741c4210307040c1c1003204442d40300d88512803000319403c1d01944180240c514810a950151104402c010354030141034038020243e0381304000049c0440e20079848441c02e10000c0780b00d640d0024030003608914250040d181d040c0b00301c03100d0310f0412141d1303903603c101d600070941600e0071410285a0000100300c50100700c40e4074101c1400003030304040c07020242e00c80c80002c0c3c80750014012200003814124601c0d0704501441c1d0109203400401c10a50380700c801950001c5a181d40103055913800c5d95800c40f03c44000035400c1380c001030500004a084400d07040500c1c4941c030703903540d40445103161500040980e10180c1c80068840e10400000c0c2c901d81e40421403110800150749a52252040880443d2804408039080d10b4640e602190940a09a1010312075002d0301b041012040d0360281c6070700304400c5807040c80c0e00962002500141d0b030740f2802d020086002c0b9100d5030056900b46120a85480c4c00c0c00d00e0710284 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 513530458 1250 513529208 513529249
    0x1b03040b07110f090403020316061806091a0105061c090b04051c050c0d08100801110a02072c0a1e09020a0906060e12010b220b0d031e030209 62
    0xc00c0c003810300040043c20240120b58030182400c29407000b039264442c401c102d8840d84280c185e5001800b0f025080b000f09506111480f04982c0c50302d081c02801003180c031500301e41c0311f1080001e50302160401610f690590300c0c0207013020b1070a000c034000e10411540d4841000000b5440e03036184404503c00700d03c403d03c81c0d030003103014041d0000307503040a64868410200c0d800a0100174000c08640c0100003030403901c58a07840c20404415140c4c15988100f0b01410703442440d070f641c00d103030105001168941c0509200302c115001c40344099124070400040040013a8005030030025041260848a1a01401e68001c41d0001c0006042445055080541200381c0741301c1281c2901c43d1005011401c012113190002c10f540b0508120360390a0610090480114400f0103101d422204d6040310001e00c02e41c0040400100240382442e44100c120709488042e10b41c26000d4206464130a8134821400d08020303a010143d855500e1450a80e44d100c0e000300c0d00c200c1c819800341016800c2c03120301500e403650203031742600222140c0d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 513531708 1250 513530458 513530483
    0x709110c011404110d05010e070312110604110d0312060f061103160308040c080312060109050402071203180203010e030d051015121e0501150e01051b03040b07 70
    0x305402c0d03925030070700540700461600030000400da010f030480c1e0f2190b800311400c0d02850414285180541020140843c01e80103114000007004520300085800801b0340c2c9a90030485111000305071550000c40b0080c1034080c0800e0303404e4443c940610b00d21038a40c031030b0811410340b100700c410b46000c846160308507003c000d4074050b09000640e00010544148003c500c0203502d420070028044240508044000b01030001c1403010804019070402400003600e1800100c0740c41340c201e8030300d0b0950341d41e050341c4250111340420404a01c0c0e0429000b2a0310094200d078400c1000804203a0840c010102141002c0c090003104401d4001030f0340038080c80385d014100c4c0340211b442c0ca0400b46070038100c0e07001801c8a81401c0c8000d07070800903c02403859400c00b139201420070360040440751094401512014900b284402040b5020400600e000da101a0580e6549081480107030000302c800c0d20250b0042c2c196a000c40d001f400058030030031100807034602ca024041c05903810581d8801281c041c42d0080d4108482c22443c005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 513532958 1250 513531708 513531727
    0x70c080c03120f0c0c06030c04060f052a01060b1204060f0b090a050c16030215060a1d040f020a0312120b010804060902040e0d0c020a08030a0f11070911 67
    0xc42200300510460240007000b001c10700e202c603188500c400b405140c40000c9000f140640040c412858404400760405980b1b2400a89a4217103504c00d00840020036840f4009241962040e0266035002c0d8001030a5011010b004011404000080302c2c105095900c0d8140490380c032440340c0150a240b10355020750081030603d440c20805540365400c00703039a81032802c0703403a104907076903408003a40090350a00c000a140e112615910800d1180b46200741d0881c20500b00074003095400a003608080d40d6a103000c01a607281c1000300101c2640521680021066801080707214480c10448941c00c0b600c12a00d03040280b07403a0780465460901c1da8402e5074940b100e4031229620300c0d0000e1000407050f200b243c040001c1d10031400068000c02018001620b100c2e075030303020941151116480792000102e00c200300d0b000c20554142c01491000041000c900400e5000d100064481d030000a40311200d100351560a00044500c030220791407042404402251301c03070b0600014242c0702030702c5040d004480d00c602081c0c0d1614100b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 513534208 1250 513532958 513532963
    0x2109080309010e130908280e03030406030b0d060f06050901060903020d080901030b090108010b01021005131b0b030109021b1906020d09021e1c080901030c03060902070c08 75
    0x5500244540d00200544411030380c0c81402800d041c6411580035a01000d4504100300811800100400703490001417201404c2e40c0e51810b0560b8510080303040c040d030107000c00c0211921800000030716010f52061000707010060190300545814440500710125480702170b05d60006584040007000c9240740e640c2002d00c00f5042400c4c201d40906600d0805101051450303012031209441251f01912440d00072810415583c842c0e001400c4149005000c02d8003541c4502c40c09008024a0b032500340540300c3c10310301c1c0180cac1c0c1c024001d803482104612a804080c1c4030342e46941c00c000120142c140400380c08540f020440255010255028125004006803154404454143c1060414101d02c607164408060040c0c03621410080d4550075074000c0002da1202c01030b8031494054a95014021f5125550100344040b02925580c0c078040c5a0007144e0351401110a0050341b43c004414001c054401c0404000712403681d4060341143c1240911840c000039031665400c1307690100d80190404540b0404074001c10030404004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 513535458 1250 513534208 513534227
    0x904140406050a0c020f03120c040305011508070f0305120703050c03041e2709020303160302100f022104020d020a03050d0801060504080304260601270504030516020d21 74
    0x34001044a090400030181c0e480c0140c10701e140c02e2555508c0080d192031000d8007230b01c000350341c420002e01402940d4400d08021001c14003505c0440c1c4074841000a0703644800350000d040320780110140801d900d0318900b56034075034409601601400b1042120060500c005c00003440142180321000c5001031241d440b01028068a0f07102440c4545c0140c3c0728618410b040b2160f42c04a203041800040007032181c40400d0a60103062404c3d004142840106030034590007165070b20049a80e01d004020100c0444128022409038071012070641c90903a40c060780c4c08600041694106000034245c41d1035000c20f900041d008207d6810440d2140c0107850404002a007242c41039005d021103080c51030501d4145482d040e9280124480c0e41d90458080c0034161103000264074900200a100b4103907030f090340c1c41c2c5502403403200d040a40c0035601c0100903450440040944646401a40d243e42d6a038545580702c0810b415010040f50243d911440c084091000a1555150310b5401d00300c0038101d00300e0000811015203000c0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 513536708 1250 513535458 513535481
    0x7170906070b070924030507020f030a020f1612020112020c010213060e03010b1f050d14160512040b0603010b100e0a08060105060a05070c0b0a020102070b0105031504080904140406050a 81
    0x4448040d6005c00034201c0f1032412414903000030540d4551004a24051803080703000420f01000070030908280c0e007c94030100c5054901e0817140b5003a1448881e107a61000c92080301d82001d4000d4200005610030002040d9800441c4005414813403041d80e19030072a44501b079801105403121340104029070304110744400007502180204441080180443c16541800182c1003c51403200c0c9480150390048050380d4602d034215000704242d64290740b00041400042e26142441c0c1c8603840d090041c05c0c4580100da8006d40d081030360205584407990345000c4a0800b6010030b50554075140744140d80e4484a074100d060f219240e80380c01e0925802000d00c1502c061030f4000682c0c64000d0340041c000768440b08110342c85100303149840340d03403042c8a050603051030900f900000b0103500300240307074143e00c0c0e81500580243e40c002d0b00104450303660340c4201a0744118488949119041000005000c1028000030385007246001d0700c04581241003070000c89090b0001c4900f140c09540e200c0600402d000c40c2c2c800d1001085 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 513537958 1250 513536708 513536729
    0x60c050705060103080309010f0e0a1b0b1804020409091a01150207050d020406050901080307051507020a060c02010209040c11060a0204120807020102160e04060c02060c07170906070b0709 82
    0x507101e00761160070500028240e030703100002145c8111000d40c13090488008200c001c000b81300e081028140c8424450800766510a034500040f004201d2201b000021034a440100600d8043c0d0001403800f0a1b4840c1441c9601c10790038000040c0055542c0202e80003d80301e0990214006846200c102140c60181c20100d80109a440d40000c400d030006039034016100201c5000b40d40003580d100007400f606842e00029008040c10000141106002015002c543c1c895015902051564203408503c41411145c20005034090303440f480c0490000ea000c0821010a48000361038507150f14040740070703110304900d48400280e0351219100031040c14011560041904802546407501c0d040003007030080c8a800300600f6000c1c0001d400f00071680208a0000e030306020113610203100e40d4400f50f500183c902160269902410812120017151004c50307510300ca6005500b03d01e040c01500c3d01c1d000841d07034500d000249541020061152160359040280c40f03c144184013032400d91409210007083d581256210030301a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 513539208 1250 513537958 513537967
    0x40510050303070611040b040807090b10090b070302071512060806042a080a0305070209070207180906020d0204270203070e0d030e1009090c09080d08070c1203050103060c05 76
    0x41c0e40200c201c03107409400041c04540c2d0150002d50b1081e80c4150360020b1041c80002800182400d00030071560111668180c0030007a584040040c00400e001c0035100800040c004941840034003141030141102c180240f041f2001c4c20b856500e4240506680c40c0740390702042d004242032880c03406502880002e080c000c4080c0009043c540e903031401d4803103640701501195407400d0002c0f001329065000389006100c00411079128890a08020703016a2188105a014a00b60400510704500000700c620858a100400d40041200000c1280c002d0000b900222110340e020480c1c44190308890015001070440c0382801c1d21403088107031312030480851104000107054014420071031803942001683c0005201030300d05485030001481c08480084ca66a2280d91041000740900c072407982c400518015108a9002000118581142500c00da0054425280c003680081480e01c3e441d4070800e8000c2c0c0252160403e04035075181c9030b803880c0c042800d07400302400085e0755000410a03c5043d0141605446541c148145803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 513540458 1250 513539208 513539219
    0x350f010e070b130e0613060e010f050402120c1305030a0809030d17040609020a0e04060b04050606091c051513060b09060310090816050601030620030403140904050405010209040510 79
    0x204040c1d440f030445140e1513040000c12545a450401ca44059901010002c07162180340001d0389500a001d405081609014040345504241c400c03161030b2203c0030b0b1101480c6e540d0100e5075405a10019003000d52400b0320000007400e031010040040c1c4644035a051a807102d6246042c9440c1c154942c8015081101c100d0003150030351002908c00713410942260f00420011040d00105229400b15402000003d42c088204020300c00301d170344541d03512581200c0a205030303100c01e02045841d00807e00003c2d4040d800d540a000c1e40c1c0798105030340c82c01d1440f80081d607220310303031107403500c1c0c0d0b006021202c081c00081c0f001000d20420100380b080d120095400c0345c9a00c0e403420300d8404a9914962403180c190700e20352715222001800b0300f00c2c0a0b44c40740702600440e0300b040d102520701682c42d13290038841200c0341c50400420782c960b1003d04406004100d500000c80c0d040d80e655450450b00340004514805500104010b02304080c7c699000e1507100741d0182001580e0f4200d150140000c071040141989042010403106214 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 513541708 1250 513540458 513540487
    0x80f0403080402031f05040302150114121009030518030a030903020415080607200105011410051207030e0c0d0309060f2c03070f350f010e070b 63
    0x208103405107020001d41e5601e01c08207103030680c08903401c00502410100c61103410595004a0710551195080d129091248011220001070a003d40c0c24400c0e031186c08a41c0074100000718a0140d1801da0440d103241030440846411240403040c01d90001e40001050140d1421006043c8001c038000d400511a6450307581b0001c2c00c0080c603000007031085441703614032002c0d6291241c1041c080d2028000b5180c1070700f40310381c2c0504203840c00820902c0b803036509a4803d440c4003040c0b007a24102d81034141903103004500d01c0c0400100185400744407081c004144880490745000894040c030400d22500c0000d610166900c1081c98100c800d492180b00d0120103184400180c0e000755032070100c50241c102407180100c85a02070311503118803885100d010f120708603003040c034821414001082002c140d00752901181c88545201e00700c3c82c00d00030344d4000c881003480c0120041c014144103200890310158080b10349803882c0950705011084544a0b21613450702494540e44409111020040846500c1c00e0315251001e1525217 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 513542958 1250 513541708 513541711
    0x8011406032412030c011a06160305070c060305101401021b0406080a080a111603020f042702010906050901020a060903110d1d06160f1112010e0607080f 67
    0x5060b542500d6a032040c0007600416200014008010032990301c4000141507580c0c0180d803000da850360802c961300703402600104002d407113070001401d0b01c0d1408052100002000442c00002c400f000000c00000003c5964842d01c00040c1c442da6501041070b0509000102003090700d03411449000842102403035643c3e0b000210b800440156500c4521161140b90001d0005c001c558030603841400b03000c00d090100a000e100034001c0441e00d132a0607440c00b240032511691a40090001c240900000d0030900c050310340b007107805513091002040032800c0c40d040c05e1707108140340704607031440748440f0000910720031580c10445150182140d45840741c186064840008d41c4c60305050130241200d45c0d00c00400e01407500c500c0d4200300c0b0003102000c86464180001c1c0007024812040568514039200d401807424510b04001101ca80300b510094007452180c441d2950300000f01c104608075078104000e010561700751900040031105003c00000000c80c004040002410070304000e15120401444401308140c58504e081001e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 513544208 1250 513542958 513542971
    0x30c071a070228030b160908100f020d020d020a0905040b060d090c09090311010e060c0a050a111b13050f070c1713080d0801080d0c0501021e0403030801140603 70
    0x11142102c03c0759201401c0d8005600003003400c800140030041c001503600241c01100c3c80e0341e03000d124455004040319100c0311401081141d400c400058502e864443d00442d4888507605401442c0c442e203c00120102e07484140056403094010540703035450ba0304960746100425042e5818403c0710b100d100060468070440031030546250382e40641300280071740c8900c1c1402a02c0c81e44420070003281d20f82005042080b001c90401225070810301c11000c4200c001c0358440c0030b800a082210f0514070382800c262400c1e00700760b00d01c00801c4101d03c5004280c81080004005120b03c81c8601c08202c00400180000290005013580280d418403041c0b001c8501e02a0480d41d000d81c4034a4030b1041c8403114582131812111100c0c0f030f00c20390f080124100d08412114101041128001000c44a09195a40040d02c40043c24812042d003030b0400c0c821103001034042c40da00d00b94503204000052500d05141e10aa500c1903074185c0d082201000402c00b4010941c00015075800f502840540c001d461100400003103d03440004d040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 513545458 1250 513544208 513544219
    0x15150414191506050a0201150e040507090204060e040b030c090f180f07060c05250e160e0f06040803030a06060917060a020904110711091003030e1504030b09030c071a0702 75
    0x41586040c030079070191462211405100c2309040e42c3d0442c00213a42403c0e58196501d0240c44c8001411100c0c901c00c80d01110071a0302c0c0c1d2140101081c040100800c9100180b980601540b4010b02c400c1c0c0e21080b021b441244454410101410700040c01040c080c8a1951514141d1060322501c207111b02c005000c40072262a880c0041c070500307052405500705016224500003075030580c0c10040e4a01d003901400002e640c03610781c41405c0c0365954188060752040c3e01d442c4c00003050460a88042c1410050b150030f121542c0500410b1411365549009861075004130b41409850f40d0f60b50041c040142d1141e603100050aa61140322503000388485042d4640c0c4c006026510700d984d0000e282d9625485541228280f125840a03040c0c4900c1141008181500c1c00d0032194450b8030103800261151842860300c00a4a425680344802d980b02e141c1032107130300d005140f012155610240710010009044d102028400c0d03880001840c0c580e2414a441450034250b50803544a0450000b222100d40700000182d410082d0110340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 513546708 1250 513545458 513545467
    0x4090c030212101d0c070f02150a03020414061c0515061c110f070311010b03070f031406011a0a09090204080123091515041419150605 59
    0x2419002803161252111800014804100b2035688a4268208680030f4054640d20400018a59240c940e01140e0300c2444210510008010071000404003060910280011052000d10391a038010383e04a01004030019400060521009819202d600900c0d8010303900340d0309003030105040401062140c1c0c0040701c40d07641c54000a8200d011001c1003131217010007030700031a5107a4030f9040280ca100703240741c44030007428102b18014030480300c0e850031030768550040385085051003941e940403140c2015541950800c0d43d00c65014181554061012500528480d09154581442c6140408554940c0510801e440d000780c8010080d2082c1e90341031200c0c1117006c034030b040d56446a451003690200040d4004d07515440c800305002c541d400f0154040704890030020914144000400710400a80c4c0003100d60100d65003000400c2c80c540e10510140a80090001d01030660000c920b401080864408a041d680d6200003070041c011080802030110101d00310140d001d000300600d107401107000d5152842200c0400c0350004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 513547958 1250 513546708 513546731
    0x30201022503211e02071202220e1903020c3705031207120503040c0305010e061605070506181006080106050a0501050c0c040f0f1404050f0706050409 66
    0x1c4078031020399848004108007400c52490810000710b850115404901c15503060300100082c211007000141e4640e00400c0018149501c0d00609107030380c1c100304d800c40a41c10920002207072904c1a48525076441c030002440000f00e00d0f00518080c2001216607018280a0032300c80441c0e80441e11001c2d12000381c401603807050f0b071031030034000501c136180e09601c10303427040c0040d14900f43c5013507220000c80d50100c0c02c503080c88a50000080503849071220040115500400400c0894002d00c0078540c001c3c0942c4030b03c12000d0b96500c80e90300750f407111034510100d9040752040015800300542c200c002c2000340e10700302c0d08069440e52016601e01c005009081d429004082d0444000750800000519a0300746400780601c0c0e5031000094041c0c000350203203500c501c400c0d07400851194819029914005403240c010440804040180310081c203e04050781d0410f0f45a021051988880d07000c1c0c550b40d0064044442c41901d42420402e00341640d8a9015485c1d030002d040030000c2c95071100c01d4400769101d04030000303124510b48 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 513549208 1250 513547958 513548023
    0x402090d0602030702150603070e04110d0819020d0912170c1501150503090312100b0a0c0b0604110a050904090605040b04030801060e012021090f040603020102 70
    0x61005201d1400081045041c65000c01c0d12031030a00000f81036155611034404042e2121428001c1d1034000d100c1400203404103241e501c003040445c0d000380c994954203c15446040b01c50380030000c1407000138030b51010122900d504000143c48040d181c540082070300c0c10421844207040342c032a17015012050301c65048150000150496004800d2101200c180284c6084a54901e00d004d103e030500007002442d4100c407a41c050b10460b40704442c900051071038080300c07100c1c80503540320203031800c42200da034030744041131040d5060002c1152138082c1d11010a01481840e00b182e9864005101c24003490034030b428030550702c540c0d1003a545242c4a50500c1d90f1034007814004503004048202d400b4000700d04240511051110986e00940541c0c001c1d5101c107496a00c40f0030540c1c840d03584054150014609100c201c5071820040b42406001d03a0560585d00c44038040703184028020b80003410003540403000502034610380b81c2903101e02a000c1040e50240030452550b0000b0703458410408a40a141324040c82d1030320301c101c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 513550458 1250 513549208 513549229
    0x304110d0c0b030108010e15100608090c060708040504150e06011b0f0602210f180a050d0e0f0d02030316050a06050a1b022b020102121302190f05040209 67
    0x203100b00944a40e03451022a010304a6640d0113039460180c044c104030100f02810140703100c0e4106454094405103800001c0b6086007008005840d01d000b4510244003640d5288014480070f4010008942c8450400041008681d040040d0b02d101e0718415008001e1126820b10342548410242804c9003200c0b0304c6803280d00b01d109585001007400a0911883c020010940d001c4c00c03011903a499a2081902840c203210034080d41514001c00c0c42402400040041e41000e80a4800c01005410b0342c50500840d038172603141041c1800b502010030070542883e075581c204034000c5400044126884e60042a82e07801294072880391501d160f690004008112042c42070401c48141c04c1030740042c0400c11840c0c10414107005140780103a01a0074086102c140d0308403480000c070f020f40b0070b084076245400071542a116a40461080c9811020f46d502402648030b00e44403500020711901440350a904e43c2c0740c0520401c20814030112940d03950040d5070b03000740020041c45d840401562401d403001642c030401e0600080822070b8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 513551708 1250 513550458 513550469
    0xe03070303050a11070f030b180601030807110904051c03090308060d02040b031915060b161b0f03291f1505090a0b0313020103051506040803030403140304110d0c 71
    0x180c20f80090081022440e01b400c80e0700500d142010741d1244860214040c0c044848414a80d000800510210f0010001400014421045011007544040101d803d585084805543e15045019161405100704161034050601c0f403804110b00015940c02a0028401809503030040200c1d400810440d03d40350300007203e10b04014102c1c1e02c2d0381c0c1105c010001e541d0292000f120400d28110408404d04190301072002561980f107500750922904252042068550800584203402c4c0b03240d62424504044150300040c00c00c0014a510710b03070850030016174800c990210788210300490305c480d25559600b2010301e80c0000b140741d2500c01c40c01d40f00070a1070700030360203402481a000c890f6404140507074110000b007030300c90302c10f4440917441a03895451420300e0204982c0f80401c0940c0c030b42070710b00640c405e42c080c90740300e40000d108001c00700c00480131030314581003030700f203100c4030b0344000140402e06402c0303030455800e407400d1650bc0e491460503684070444400200060703402030700b40c02403840c2040303040c85604c800b500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 513552958 1250 513551708 513551713
    0x10f050c07030f0c170d03060b12040206160b15030f030405090c1b010218040b01090f0909081204080a02190302070302060705030d090c0501031107170c151003120e03070303050a11 79
    0x13040c44070390581b84c00400b2075041c0800d1601d000020503002d24015a080007e5040103928190b0303694007400240c0d808040e4007040f1021a04290001500e0b08483e94040c104008224845564130b1091526290455034403407010750050100704425a507008403103620042411a243c2c4a460224a00b44401d03054058040035500100d02c0c0303403400c0301000c5040310580d01140d0500000031000f0041d10b1061042c0101d2011041c011014400c0c4031b02c83d007214040341d100c2c00d009450941c0700f290204401070183d40445018100081d00c2e400554100710302820802030010040701c2d640c1980c1c01a560744560b00c002402005c1c0481c1100c140302041c02940d808064000003440700050511b418403003c00d903130180b640440d143c403e160410129002c2502e4030a58801d42c01c60740c86c00802103842c00c64114450341c281500c1064816142541d0340280603018100401040415078118903006102140c10389103d4104078020085410544c0c000901e403084907094240103948405540e0225103250000c03d401d009031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 513554208 1250 513552958 513552989
    0x9060d0b0612010909020a05040218040c0c150f06052209061d070807081f091713030501050a050c07030c0516081606180b030903091e010f050c07030f0c 67
    0x134180e8000d1640a031084410045264031030041200328040d14602d200c80104840111000341010361144507800400d041c2003904030142e0f41c8138000304c80804a8010602c0e110a402900605680506c0c40030b803504840c5c0075400841034128030b01281040e00002041625030940c0310511107190710500f101c81c4140c0c091300841203600081c2c4d594030321500c2403090500ca83c0c040015000c402107100400d000064a1180d0911500700700d10380581424032090318139118a4a41ca400e6801c40c10062802600d1074280c1200186907003009802c4807002894200c0d2642403d042058064080c0200d0701c050f0b40c1810001c4202009050151429100e400d80034020202c030350011075186400100900b8110081400d925800e80324401254800324583c1c0c4402090041c003428480103020002950f0300c0f0584204890410f0341000c000b0f115150004104804030141c40c60180b10303560b06c030001c01c4082c4200c0c249907103401c541d4000680d0f140304510026040b0b42104014004100300f02c000600289070704403420550307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 513555458 1250 513554208 513554219
    0x1205010303081512070501141b0609070e0411010315090515040e0a0b0f180607050c150402060315040902040203070203040f06020c0603010e180109080a03060b09060d0b061201 77
    0x1030000361030a00d12002070343c5040d0b4483c0b40c01d40b00390307405059141c05030410620303207401940c1c8000004400c400c0c05105101070006110100b0b442c010150480b80205800d0a000641d103051148981103440034080540412000c030307281da082c0c0183e884082c6000529020501a694861015600a20740490030703c010b0100b11040b03142050341095080750100072000311909910b985c0d036280d181c0203154501510005120802d13840d103050384660f0054010454240b00f08a031410514100c03007a03c0482c10105150000718010048003030034444040b1405540e040540000b0035074003005000249a90000c0d090201c00d4640d80c000e00c0b10182d028105544a080c08540070317450340c11500401c0c040f074400b410000b5401e80300140124417080040e01c06895642402080301030781a004207940740b07903501c012040b5080c8009210b641106c2e4081c507400c903107030903a40c1c0c0b0040c1035600303642c0070205021041c089501c460b0b80b0941260120402150000b4003070b9150004981c1e503010310300a8540e03108a0b4400000c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 513556708 1250 513555458 513555467
    0x607050306040e0601140d05150403020307120f02101805070b09040e060c0711040b060a0201050106080a021809040c23130c0c1b1203020714060403051c1205010303 72
    0x1440040b5428001070603001c86440d0303510804d100b00e21140300c18429100c0b050618400800050b0f000d00c003950308903102c6420388030b54404280d03001c07001a4000207519041c4079005416401e00759151034820b03049001c1d0100255201c0b408885121300e643e541450301c220300381103400c2c01c084c65030000c15102c44581c0e41d803160082d0740003403a045000d0360420b0150f40359508017160300c5106007403a0200701d0604040341c45007400003000400842d002555542031522070380d1070901900e10745000e580040f40d59810124010000c010117410883e0190040c803002c0c0e81c1045060301101110015103041a1a595a00302006102d903a50b1101c1c0c0b042c2c103262003085030420341c442a40c94a10083e034016500c6490710002c401264031060802c00010303804000000000c4101c00c1c01080c003808661030902490312001081003407000084101c2c056401030342c040040c4218040e035000f9100041321540d042134070b0358841c02d031503680000d04014000c450040041031a801201c910381c04410381c0c102007080c0e41e104d20b030151 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 513557958 1250 513556708 513556711
    0x2090f10020726010b0105032208090927010b0d03120627110403030903021905040507030209120303060a26030406030e060f0105060f0901020a12020a140607080c180306070503 77
    0xf0400d50812030003c1240d40910120f0f405451003c40300203c0701c1000e100f0500c8101c44c110103c80810003003180046541c3d41078002400368400f42103050a0381170920412141d0030700c5001214a9904203010080703d80d039000c5521203200d4050400e614a908140c0031000244215008040c100320340a000020159029030103842c4c14819000c1000340c4400f00502030040e004910008002443e1032509200600340f2145200c0700603880c0c6000049030341c84100240c140c940446110780001e80c04580e6040c00e150820000d00452502c0c40614514140100450f8402c5102d0050340b41003910003842d4541c0118802c120400c2600c0b0300283e0341c44a4071148000c0180000c841d541c05c55208035800703d00d1040c0141c8815040300d1005003094640000c080035a00c40c0c0e00060050790541c00f5014403140454a1030048940c1c03400c0b070f0344c00b0345039011403441c1503031425440900c1c907111580440700304140f00e50407070f2801340c01004120041b511100490314604010602c86d0b413040e0180500b105102210782c2110246 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 513559208 1250 513557958 513558029
    0x13061b0908060a1506030b03010e1b0f040b0303090f270a050c090120030f0f03070809030309062a1b010f0b090f04030e0a12120302090f100207 63
    0xb200c00d5102c040c4480300395100b5040700600002d840070308000d001d010707034002940741501500101d9002e00100040341004903043c0031002c0184903003c04c0c2510300e07201c0004082c0c0c9000301d0341008045200c0011035600c1c01010a803e008070f10420301640b1176900d07803080601d022504144407549510010f82c0c40400c201c00d0340c0e91034802e402d01010a42e244429001d45607404010703901c2e10a2903140e440380c1403840304950445900b500040000880808401004191091130b0f2500f069503420090700080441c00001d0000540e90014020b01100550106215410841c0043d42007204034000305508201e0103042d424641c802400500a4400c0c0e0480c64007100f91560200208221105000802d05888880d90815403107194800001c441101c1245041c1d00603019144c0303050791100410115180308081e030822285e41c170f0300e0714200c000c01007185405a80304146283c25030030a18100041651130980210040c0300c2d820000f400301d0010f1007045240000c5c00300480000080768884c241c40410341840d02038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 513560458 1250 513559208 513559213
    0x190b010e040201080f18120405031507090e04031e0e0109151719090803040c32030a1e0507120302030f0a1107180f0506010813061b0908 60
    0x20308411001001845150103840e500c0340c1e540c40c00752190700c03c0c0b001081910000800ea5013941002000c0003008001c0d592042015038407410142010311301b440300b00c0c1021804000b1401c211105600000c40c4046450111042509807968a419103410041a4940d110320070802148441c0c1c43d031010640d0001b120a80320f5015640c0c649200d0302114641c8600d05020481d1903042c0d803a00840ca00d070300381e4000006480d405c0c0c01944540584140d86a201040d51401c1020091009214000b60840c00a1142c59640b5610300300b10b448507014036141c14a440301e4410300764036822407510103100000405500800a0b1059003d13a03404040700c40703030f503c82a509442281404142c8100400b00d216049405400450510031400c540340c640764002c10b00c0e01d04222210241c2c0780882010803010015000f041007100140b40300d440d05200b11303a9069526000c00341800c2c107002c1180d801c41000e541242601c6c040030503282c01801d142e005400034805050260a20b0241e4070106607102c0c81003000c2d103401109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 513561708 1250 513560458 513560461
    0x110301050c0301090b01030c0e061e03130b0c04080c010e0301200310051c020f01050403060c211802040f0204080a0f03110a32030a020706020706030c0516050f190b 72
    0x44080f1040ca031480300114132780d21054007041c0340c5540a0314615200a0283c110700e10b0100d0f0900864009440f404000009648075608100808144a034040100300070141058500820540e490741388104560500400c1124502c030b546080d0020071100d03103425040154410345041c41d0031258011104c1c11044034080d14041164500080c1441c2010795043c0c049011451a40801100300c541402c940e0502008100003c0020018040c0d400d031084162108001c0005441407400c911154031580c540051800303105112a40000002c080f405806a400003450400901c09030024401c5804c40b541600c200d1113110100100c080324200100d229944180500c0c0c03e09103195a07880b100d0750300400d00103402894840c58003141d4602c9401c8a6000d07800011020781d050401e0035907100d41c4250b00142c00503e801e100064040045070000c0009250070003854144000027086070288100c18103601159032140b000b0300600b040100603010030301c02601da6080004410b1221503071001c1c01111446003c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 513562958 1250 513561708 513561731
    0x8010e0a060b0f06031815040f0201031802130f1508070503070905010e04060905011506031a0a0b0d0b03030f041d0c2802010e06161112040b07110301050c030109 71
    0x41d18403606083c040c1140341952030b9400ca440002880a44480491040c40d0601800016003450721b40a80d00655229a441d10319000050984490290900341d90111034008001038441c80ba01c13540c10315807450000307400c00c11582e14401a00d4007421003004009454804101e860000c1011400c5070000ca04580186581d0304007142911403d1149c0180c0606000000d0082100c507000300145910440001806550740c181d90141408903822100c006907840317031410b0001c041030300c0102401c0e10445a40325064a041c150220301d10883c80c180f1061900d03003040e010035031400c2080e64004081011280c0e21036480301c860030585504030001143c442d414102140344444d5010485010301040c9850b08000e801408641c0707140c502e400c0040c4111341d642ca4034a603a000c400e10031940035010100408018180f030480040c420800c81c942440290408505003101c01c0e10001114212030f40d048403940c07942c1180c113082002106940c1456007550a11040041016114008505991003a10100590034425 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 513564208 1250 513562958 513562969
    0x60e010e2d1f0e01050d080f0f0d06090e0a121b150209010f03020c0709090212070e07110f071a0c010507020a06140f01030308191103070906020a080306150408010e0a060b 75
    0x4e11420f41c106d8016551040420500c0000700300310251421140e182243c0411101c505602005041107a1941d070b02043c0800751040c010340a85101e000c4c010114003d1585948a40c0c440d10b001140501035205205044a580c40310745030521500003200000d00169a4881400395201241080c0000c14038121460014002d100340c941503541040100381f01804d0000035802810011026644541103050003280c41c0c400b00050307030180a81d02c5d01c82000d401c12410180840002007040c0d0b40540100c203004200380d0000641030b007154038015401200c40800c00f400c540610500410b001c155080000b0400700940015040c186148240b50801034000358011300140104240d4000100c45008401000131034441c10072160094099050404907400718600c0c94111071000d6148070060b4808010082402d80003420310005002c180043c051081150740c0b092201d1100070480c520540e11044284148989001a03401a0001d04002c02801d181d1710345207562540060000c4171200d090151154107802c16 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 513565458 1250 513564208 513564211
    0x703081305120306040207060207031206090902030c060322140d08010e0f1008070315050f070c080a050409050108340311030a17030406060e010e2d1f0e 67
    0x201000d000b62050340c140d1000d1907440500b80e168080d03001c2c4104404100c480c030050142c94441c4d11403109140780d88000b0020349200d5403080b00f8083c130f00314a040158401264140d013210f0201c403020368a54441c03074101c105003490000c401c144440d032059541086034000000e411000080120b8589462007542110015001d000d215030300f030741f1540469208842084650340040812628501da50788030b4014501d03000e0035034020345841400d480102c41026451180c60b80002c0c50846070800d52515060103048641c0f1312400800c1da000000d905086c99120300142d50250140a0042c4910f5a5400030702e560b403030b40003002008000b01d02c00c007600c0d6000704100800110b41c6103680b00c24202d02d1611281c0310a10842d4000360940079580b1150000b0b0005224900c80c244c0000310b807922810b144c1045800c40b8010703080404900c85070001131010803c0c0030719007a030000341450300c0d5038409103100c15070b40f030407042d480b09105034481001403001540300503103807601d00c800b241e43c0a80003950b107003078410b080d520 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 513566708 1250 513565458 513565463
    0x6060405100905060d020915190609060507080906040303050a021c020c130e100501240e060d0b030703030206150901050d08031b040807090e0a0b0609100302130207030813 75
    0x2007440c810000c070100358121541c0a013004044c0041000d0743d03004078920380c0b41214141d4030780f8805c800012003407400d08040c24203241c0070400b4029040c1040d1025103201c4040c01030704144400840d14078100708050088036003041e000b43c2000e49880d0b407032501415a403c4416404050b001e2003069080276180241c00165145855004118180760030040c00700c0b00c14a003d0200c659034581c5a180a6008200712070f0a200c08107000c0014507601d0070001d94034040a08100745c41203203600b506c04803c41d030b0020121401210880b00d15a480303c0d0081030b20000c1030128400381d014002c00c0c030008241900032800601ca4040b510110015003101c1d020441c03009000d000d40b562012201c803c44001c64030381400b56a02080c132005c0c0f1514480300100100e100d801c594044502ea03400f8000c00d000300344545c00350094170801d0400a1601c012103130f5804500a1000306250701440d510030000303152902034000f40300115009009140314503481c1411802a5001c0c40059001c1a0440045041042e007082050502034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 513567958 1250 513566708 513566731
    0x70b0724150302011116031103120a09060f05091c0312020909271207151a01180f030303020702030610050102120703170c030a0b060913150f08030a0206060405 70
    0x40c02d590056451800780c0c202d17002588602050745440900b000b5600020b540610060440600c6d1070080500d000d5050f6006c01c0c2290060160140d803503084910102524030505280c0c0e2020a048012161401a005c44d95845011081c08202c28444816542d14690003540d51030308180e006030301c44050f07100707425100345c1104a0800080d80441510701d481480450050131014444041e50660302d00701809035062040c0200154039020006880301d00b00b440710382e0345000d2000031845120010400c02c1c2c80b04480c1841303074061032850701402851800c2c0141c506001c109440940f6824002c00a42203050224042d1044a0101d40400214654602180c9050b030040c5030025809418450301c0d0080f040803030901c41401c80b0281c00414155240d80315001c070b0110282c680c64010003180503100400c00580c09100f04002d0b00b440d64480700341c031220802401d034001c10500c03041c080c110305112071644503025409a02ca000702e03403018003000400c045150750b07003190855103500c020801290001c0e00c107003c3c000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 513569208 1250 513567958 513568001
    0xa08010e0c060904060e040b1806060a0b0d060b0a0903061a0a06110a1a04050c0109080c06180310140703020412021c1a240a090b03070b0724 62
    0x10325210000f400044800b900c0400c01c0c0c2d5440c0740340c07040303810140c40c2120010310603010882103110718080600040c1c1160001c10032418104042a002c88860041100f060b40009441201807010303007180c070052a0728a54507556044d0114000d11505540c00210307a4507080008240b00b22803188240810814000c09020640e40f50a0040e0744007002c040d40403c684c0a241c80c2da034049183c0011781601c1c1c07411104950083c3c42d0a02d007840c18440003900290500c02c500038240000e24000407458030000044d00c000d50707120030441c03581d02c80d80084094158140310b80201706480e4012900001e034000e607a0b901d00c0c0102e0b21264026003c0e8012801b92400380200080640054500300c06034035889000401500505100c0382c80b0124542440d070180412581018140714072455000700f82407031044d14820302c14501480c0000503d0007404e601c98402182d84a00240303c440c1d42c2448040028050550821b665000a2600d03140500800803900705802160f11450807a0503240031310350034001d0003961100c03030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 513570458 1250 513569208 513569233
    0x3040e0703050405100c020a0c05030307032313120b09030f0307050d02040519051e0306040b0603011d0a0309120f030c05070f080f0715021e0307021005090a08010e 72
    0x40400603c01d032003130b11a42140c007042070110b10501d241a107031a4003415006600d420710440d0a60035901040c040d0b1300030404103001ca80e205213403184603010702510b50a05403d18030344850a000700c0c007215508801243c8001000c051034491071807040e214a254504c0c6540700c0c4242522402800d001c0c548c00c02c4c0c10070000340b00c0e6104100412006000e83d20060801d51100049000071041d0104070300c03885141c04061060386441d001a11040740390101c1e440d25514002c022075200d6502800086c800c21180700810ba055500790424549107121400c0030b4080445070300000d0361014040025004201c03489008207200d0003040c0d0a50301e2542090b50b0403480c12079503804661003003450a080e45c00d801011000310302c074040c00740080010b2466400800341c101001a0240c14140d65030303c80129544200011144503402103440100500418049a1803a44001c240744c00c2d0322458034001e40c0300118050b100b0342c5270b4020001d400f8200c0192102d000342c5031184640d034202c580104001801d5407148400e0b040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 513571708 1250 513570458 513570461
    0x907090303111509010506010905120718021b031306031803050a0e120703050601080c010c0f1103010f0207110f010914120106090e0d091202010f0c150b0a0803040e0703 74
    0x282004003900b12a00400d101103140d20030b0f50b0a13945808181d45901c140525580d0020b110009084203c83c030b11602030317811607070079502c110602c1584100c0403545a4810a0381890341510004030310108001c900c1c8031440b0803070381c881d0302c440880700342d290307008030041a514403a02c10030001d030b5120554210018504d841c1940c698011b001a4000c02129003035500710b6860328241c007007190105100405265080d85406820200305070014040e03035100355100c507800c3e0381c010300e801c007102d401901d004500f440320b062154032180301815568041d0b080a0032100c55400550043c010f45009002c01c0303100500c1082008144100302c039071580011020202071281402541c181189100d006002c8078610407c0302420f03003940d05a611005100b60b640350500e041034001c1c8210304900e510392400702d42481c1460f6079901e004120345400b0f4100a450310140c5400c0d4040c1c110803800907085840301e004003c1e00c1655001030165216241d004244000000840ca1000000c0c0c07802d171200800c81086031b0361401e00880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 513572958 1250 513571708 513571727
    0x902210c120a06090c0807061e051e030c030412020c0d020405180a050321010609090504032606030c030a0f0609020f120303250f0c0303061508150907090303 69
    0x110640111002c20703000035110710401408074400e0900e1403020389005203441c10200c0e6544000c0c14005110400328a50701409c801440e02d034903501b4990b44500c1d07440903080000030f884e43d4120000b500042880781c0c00c003682000c2c42c0310303070f218010005200c1107000c012038585440702ea800b40c00c031645410007030040c5426089903610041182c15059220008202c070f51500c0803000041e80c007a00001290007001d0014150034405e40c2400928915552600c040100b03102070900c94404c440741da904c04142090720135400c948a80c03030400c0601042419060300041d507114107480041c030901c6442040300e12400c000c10300402154101852045101803501d0f100040c0c04240012a40f20307980d100c01004940c1d600c0c0d102070842070703007030015926450094005040c2c0d4407504004401d20143c0e280c0070056561022406640e250780f45411601da501c2480c0590140001d600110100146054803504ca181e0080c50a80f203403040401d9403029822030b509200350301e002510213a0010740100c0c0e081c000320f805000d811 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 513574208 1250 513572958 513572989
    0xa03031b02061e13080a08040909031e02010f061e090b0d0209130b0609010e070302090a260601090608030403081c02040e0411030d121a09010303030902210c 69
    0x186480d4890060010b8840403140d49110307500d01003031802461320031100310030103003410f100100703491607041d15450024007840c811050996111301d1080101440741680e041090400400300329210075001c4003038064138202d03006803070f914070300100006d0074402c000455681c1c0100c3c0100e065400d007000070540c06072a07108007243d000b03031503011214010307198040c03064495070501d04508071a41c65498012100700b80984540e101e501c0b04401401078101450b440741c5c1041d0541030042e07a544142011820038102640400b40b00c1e1400528005d503011040b40c0c007010f8030040c1c016a10303140e880e400146c0c200c3c1d80a028821007a030042c0014400900043d00400c020f442c0b4441a02a0f80c116400290690703219070070026140343c4403002c0c04108a00030024541c0c10204401820084984400c0140700d540e501800ca400ca540760304c1c40b041040074050346220407607406405005c01d580c503418060b000d03041001040b40201c0440c818007440044035410100c5c0e44c4c69000180c00300041718402c0015200b076034143c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 513575458 1250 513574208 513574219
    0x10915050a0909050c03030318070905150f0d1b060906080c0909090712050d12020a121a091806090d090302042a1d01020102070f02120115230a03031b02 67
    0x511100d503800308040c500ca80481d0342e503140c402409e4144181000c00ca40d01c00d6102900700810b105034080758101c6000c1e0400300b038030946440805407002801c2e50081d104094505102506290850700105400d0f03000c0d02e000780c03a540d0080b5079420086641d400101d8134002c2c0e480007408800610310b010070780d041d005444041202c440c11b44441210032100031199080303c640d480b1100000c01c4a0f013242c1c0510031061910000c40c01c2000c541c0c4060700d0300c2024450b002c47da0780d480d052445081401c40c1c00e0381029001422a41e0f5501d01461400644030028a5004280c402c2c600000d1036500001502c80d402500c5507141403201e440c51b4240000780c500400007800d0710041c1005c1951845a040d4400485480d60750359006c140312000c01460780002801800781164010011704020420000d144c8107000e42c1078829410443c0c64024090040c80019080c48480300d0600c0b0005a0703220070f00c09200103182403810031507081001c40c2040382c98940c0b0f21008001c01d03e00c445202400d080320384014035240c005040e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 513576708 1250 513575458 513575473
    0x12030403170c06072706051804110a0908011107170306041b0806090705031e19020403051c031401050402030406060902030c07060e030703020312070207030b01030b010915050a090905 80
    0x42e1410715404481042c00200250142e0344401804141c01e000145299840708150f030400000400621030a042c1844400070301601032626160395209510017946544682d44071182078600400c808900d200e40c3d5007642c00d0011030403404103160308541c0440d0f442550072481c070094145480664000905c46640710750789121341c00454040e41000c6c1c11000a590b10007400d03190488c108150b580f00505080d040000500800070900450102d070024174800501211083e626010750f0300c0900300403a4010121400401e00004000c0e0004110360b1001701c40c03840818003800d10381c041303044032480c0011503001d2142c0f2004200b82c1c1403039402507801c18000c441c04280d954440d0301070002d99106840303101321402d00040e44000d00c17100d031081d1500201d00601661070818142c50080d581c2c0903a41503809030020100115004a0007080484011030f40700403520b501391fa503828080310207202442841d00341410400303602c0d0440213502c07010043d030350f0040001c44428205040540101100001101c8601c260340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 513577958 1250 513576708 513576727
    0x90106050303120103301101020717090a081c08041506140103060b180603060a030b0705030123030d0e131b020c03030703080a02090a1d090601051203040317 69
    0xb00910341c0c0c00f244083c1030401c1d40b41d40381c14407882c15020300041e40706c051240200030108441c9090120b00c0702d00d151070307d0b1f441344a03001c0c40c3c024428a44014844002145243c40110148000d003168010440c1d001d011140e40380c1c0d0464903103240c203801140c805080d5102c450325a0051342400d8200e402481c0d410080340d0b490b01100c085495a4000040c010b00c16070642e0403d40c6c1c14001c41c1d02609044e850281400c130304140c8405c1c00d2007040c281ca072040401200080c002c0d10380d249450021908142184624101000050305540c000c2c05003c607114441c0e070403201803040340740c0c80c0044000054000c100c1c2860002d011505080150840d0780d1083c540b2010070b010726050702031109440910110302c8400e820b104000303850441c2039903007103009170000d220441c086078001c030300f550780111043c03805a992240600000c031201c0076900050400c40c0141a9101c0080344588bc207885000c03050100c0b01e20766250b03010070164400300200584168000c00c421300025a0000ca08a1007280351f01a071400c0c0a100f1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 513579208 1250 513577958 513577963
    0x190306080f07030b07020304060903060e030702190f05010c120c080d0f051909081c0605040c2106050607060e01183008180a020a0b070212030a0203120901060503 71
    0x401c5841d01540300c00300610a2004040d00d4030781103501800118030f000c1c50200050b248498500c00642002d40d03845c50080094010700072039603c0b69008000000b03040220132031a4065011b0b01910403240310010380481c0039405200c0040445401440c100c0c10841490b600b202c0030031880104490f0310000340f1014442c0d4005000d4032041c80030011010a03640780040b42c00494101d408034406540707040c80420340c00b09040901700c0c0c9218034a00c0e1843c0c0017130070a1032540b0240001e544101c0e041860204501450342d03000300c4903ca400e100d001c500100020303010088090311040e001d110360002041010000088a581c400440628500e0021072401c0341c0789007080c40ca0382c60304400e45403038090030400c1c00080d2681c0e4500030789680400c11100d000c1d540c000011f0407a00024191000042e1222142440e03400c1007141e05826075004009000c441d480701c04240c6c1d25000414128018000c0c001e8417560594044255208454558015420201d01843c108100403001d0960389403550b07100300120301920300303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 513580458 1250 513579208 513579223
    0x10209010c081309050924060f010807050c1e0d0309020112021c090b01150309031409120717010c05090d0f1a01031b0e06100f050f0403050706030612030519030608 72
    0x1203002402500d546140d0b01c25a40700300814085031f0812150030007410760354400120622134400c0ca00544295034441e41903030648214400c800080c8500c910702a4001e07242400844140201030507a070615200000c250103490014030001e001c903010350358000500445601925800031051400c0001c0940f1016500c1180c01ca0325007a0f4002500310014070810140300300000700c811640c40c080000108a441c0100400d6804c1d040c00c01c100400a0f0b01d221799070701c3c5034012404000e40360a807000d9030b03a214901408448040407a45181d42001e02290f150cc0c00748003510303209a40501124000381e5a5030750701e680d003010508110760141101800080030031051002e540030314441c102001c02600c40328081a07201460394400d110a40761881000250740305d06505480d200c9050416003001403841e04255091300032800c4c640b8411101080c00404c0c4030000a4000464a01e074a040000b2902c400c080305180700d6101010303012030003c01051840011b80080d0002001c9107140000b020f44e124407072282041758 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 513581708 1250 513580458 513580471
    0x1020d110c060601080108030d0b012d020f0706090b1605060705070606050f0f0906040b0d051c08090a030507080405130f1a28050604030309030c08010209010c08130905 74
    0x40114501190201c00c00c038150304000242010089507144c502d42d00c0c0d6a03ca0400300d00c0e1380907200d5411440c940d018080301c0c001e1400c80c980038000655001030f5891007031550500c9400500c5400c070349030369013000420b5410941d41c0a641d840d00c90360801800c2040c0d544250040450b82c16000598400700c0e03414041180944615550705684001a06090096030030b5600013510ac3c02300c0040080c0c040d80c0b902d1515012040565012105a64140014005010000740c1541011002146000f0000b01081c030302d883c030403443c20b078022074226600201c814034030071105840039a000910301c5000c6402130000d480404d100d460143c1c0b4003615540810415501d03803000c0d0810a4491044104550300380c01101005000b403910502001207a200003884032000001840312060850008030040d890001110064000608455501c5030783c0d01d001030000c0f00500c0142c42c1c0040c00c05021070044418000c0396040c1d5416503c940c404221500d80003207540c4a0b05a18191307855007400050580c2c801d0090341e10860 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 513582958 1250 513581708 513581741
    0x509010b030a0507020102280c0212010f1415010516080a20010504050c19050409030c031d03030703120212090c040e06100b0c07120f020109171e01020d 67
    0x100385441400f5602c024207007500356401403003103440b100023030301a1110100c01101880e071504100101600d0440c802e14002c1c1d00709188280c03400e02100305400001e803000d43d80c81c04000301485240700410381c2e070f02a0f038040200500443c81c1082d96100b01c0c0507002020802d8402d40781c0316131030781d14040c00e40d1180010340046441d0b245209080c84594089800c0d90000000034001c0e842e00d41e0700d9030f48415030108c0740c0342304010720b4140e04d10000081c00c084018010143c01017052002508005d090610704104c101c00095800040188041c1141c40c0c504440b4000b0303005605015081d1b034140c4100e403541580004195007030202c0007410344010000d900840d2080d024080341e00f0345806000c2036480c54402e81540380e0069061010050780c410a48080702c803110900f80c0c8561801d841981444c4103507016154085100121406100c030007100c2c20b030414401d03285c1c40d402596a44500c581d290940c0d6500c0443d0300b160446c1c0c03014106000010030920f1280c0001860504d140030700501b12410303d8a00d41045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 513584208 1250 513582958 513582961
    0xb2d0106090501020307031205090f12040f080d0801060c02042705100204120609050c100302131706070e0102010e0f0102030907090902060415051c0b0102010f05091e070509010b03 79
    0x454120403650003030720b02807025601c1c3c00107548000e8009211301450070b01c403581e034500244050505100c00300c040700882090f140710301703103d40085001d60003500607440c151481032000200002c00084c02005402d4076200c41203030341e2030400c00f59942c200c2403c4c01da0704145c882e17481c010740c460450b41d03604040401c0c00f035000395031070541450303490841d10440004a6510400c414400c1e0100f8049034222a6885000480c051040f1318010b4180704c0862001c1d600042141d1242c402d142c5c0640107880d50b14010f0458007c09903944c03141d600d4044140c282c41803030340c0202c070118074094824117142e400c62006000100d03000b2001c09120380f410b078810240d1a5243d60120030710454141c14070110005085510741407040e01d007590001901c0d4813440c464044481e0303070a840310b403174107000340c00b80d9540c00d02d02104507040303006c40c091050180005c408014010751070490f84c65902052445000c1c081c44012005040703054070000030300c02e640100c001d8101ca0f84514000001c49981c1c0d0710328613028012500051751079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 513585458 1250 513584208 513584219
    0x406030f1203050a2304020d050712060e07050a03031101110c010e06060f010f1101140406060e160e04110c0a12020f030423010e0d0302070612020c0a0b2d01 69
    0x201d883c041c0210150300c1c280340700f40b1018400f801d01300c5808141410341e41041d840741d20000c0c481400c6118002e0481c003d00390300050350000404603801c0b1600400c002e0003200d0281c40c40301d48a00141c00b945512600791802440483d1040c00010844030860f000001c060700648400c40aa400280c55a00143c0d1648289456080180a4690000340030740f0303030854640c80c8600203804242d17414900c1c010800f180c2c03c0c41d603200609401190741b00d14001c00e44030f60303418503041c982c01402060107048c04503203004011840660302461082401a0140d5425003891380c80d100700405040ba035458008001d03818002424103100c02d122021a840c840e03101c8440394040444c020341084c051014140480c0c109002c10060742d8491030192000706041c00101004005190040e81c03070304001d02c00d4a400060031001e003410141c002070b8601c2911003c0e200c044008410007100c0d406d9208103001c0403220f8001c070901800140b1030048003074000903d203944424260705a80680c00400001c0740a844000003400100403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 513586708 1250 513585458 513585461
    0x307140a05060711060f12041b0e160311040306021c0b01020a0305030403030c030e030a0201090b01050607030903021e28050d0b07140f0c0304081c080f060406030f1203 74
    0x404042d00d04a0515001d900d4040b84e0100c840c5a0034000e92002500d201e2049500040701d001c602c4039000c0c07210f10309060a14170820500b0031080d074580300c09500003103010084450240e1003005070a112a88038400c0201c12405080c414880b0481d04805210110010744039001820b5000c6011081c08005c0e00400c40c84410b13208060440380c19500451056004030b6806000c581d400303509420040380c3e110041104400500040c80a550240404108581081e6040d0031000340305004000748a881e0b62241c1c100030380d9220344d5000601280308654100010704001c88c0c080350101c24403020b61441401c500204000590203030000420110206900703206034500303014a0090103055030007101540322665584580900a03120320240301011800c1d4259208440455410000c18002c00382c50302500608591380741c12a009903041c500400c10460030402280310200d00c414001d550303560f100d48400c0031f01000c405000c1c0c6210b42041e11001e001c00481c01d000100e0903018403505407001c585208440c001c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 513587958 1250 513586708 513586729
    0x2001021905070b150a09090308040c051512180118140109080405130f0e0a0b060f06030c031909080c06071d120f0105181e030d05070e030714 62
    0x1020710500340240c90104054142580e44444401c1010000c0341e03909000503c251420f910007000c040c00c1100c80001c050740038041a006511400382e40054903103400400001c800740e0301e01c0420307601042c00308a070107080c00c400e850f800c86640710703100c03460140c01d01c981c600355030764094040288209113010400300240c208140200c240c0040007080410b0041d44c0700e140902c01c40c441c0a10480f00400400c4c21030065611403032001d202503004022015108015039260004500b099480c114130f4000104241880c20030f548001030010805495030395217901041107070700f0141400f10700d03551585580d103122000e403107100c840303c1c041c0c45c0f600d0702c1d81c100000552130804010b211904010200e52101081c80070981d6060185004484110810403a01c007940d02d0b081c0d201c1900c44256080c002407082070003d034591704042100d0041500c0078482e490515024035100b01c8502800c5a00400019907003452651280f40c015201e460010740005503100040c1c40e01a90b03070401c041140103400796031703914900200241c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 513589208 1250 513587958 513588007
    0xf140f030307090603020c1c120b092509030b0709032d06020f0904022805030708010320040207030e03070906030209040204020a090f0e1501090321200102 68
    0x114a03515040b5070040201d0110b1140009254000c42d4540b201e170000d002045000c080020103010307021491000034407880015100000040ca4a04031401718209181c01d1803103020f840305403000c40fa044c034800b50142d807842c0250078100400d0140c040001400403111354000c080580e101c0c41114214100505101e003c00041e00400e0b554403500e40c01d4486000101d020b09400003001600c8021b20440010a44140c2c65042c0d846440040c4449519000f5006a0080c40e4107120149106900d448141e599200a481e01380100e07218100410001b0948a00100036440c03035000320342400034040c085400c0c2c0e080207000710080340842c02e00300c10a0800300b02e018001c0080c0d2100307000725440c0d5008144a0710014001900131500001e0710170405000e604017000a0180c080ba81c580c1c19560807035040c1e1400e082c0c0385105511340d01191400598403d040e01c0c000e40e0b030010105604424401c000ca4002d00d01000340400b4002c42a110340c0b0301d208054880400c5d814040005030307554403005aa0381103280e24a080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 513590458 1250 513589208 513589213
    0x70305270a0b0c191a19090326010308040e1306090f12021f0f02070c1217040e0109090f080a020d1808190809041a011211030c0f04030f140f 62
    0x86000c1065100c09210120039517201c0301341078480b011806101314072028a40946414400e14004055001030103c1c0c1004859071443c5150361000315000c038002c004e1101600440051009000300c9419921071500b01241e840e031640d402d0a503545e8a800d841c51040c1c2503030003045100100342030048102042d10a1280c03840605145008030300d03240c0422040038a8100c1881d41c80c85640320146050741122409070300324150417001a40c0f00030078502221610822034260410422201100b0115410340d4282c034a40f4010b008941e080c4225030000300400751058500c40a00c10000740418141c0004112041c080d0380a0901c032440f8640260802c59076041c05040031b00c80c03403c10081c0c1e0303e0104185000c10b408140c1c0d40d820951034280202240920304040e0f44c41868865080c0c02100c0b1107822400b600d00030b880b001e030300c25940310321142203030300a2281d080080400c0002524601c0312000a12200f03e0707030110307a814252662500320720250702f80000c803158001d03040e0403a001c00080101c150f060588000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 513591708 1250 513590458 513590503
    0xa0609080609010e37060c0210050112080702030c0d050609070b070206030403081f0b030610020c0a0317040b0c0f0610030309060c0303020408100c090b070305270a0b0c 74
    0x15944205d10b03617503088108a406046115001081d070b0305680340c4110301341d0740e5034a109410000000c011308080900984244030296240e81503900445040722202c0010341e102d00000c1e2500d030010b0780701d0390049a041c0584a02030545a0781c4100f586005405034008000b41c0c9000149035107445010b401010346544207100307150060b03541328100d0b0350040d45840c200880d81c440d4220000782d062200034090b9503030708903030b004604510b4510145d031081030202d030103003c017600c0f04109a0700d0724440c46032140c000005c0d2200380081035807403005880a8800d5201c1518141d5036008000c00d07a08151498446500401c00103400b01808000c0d0300c0d0010343d403000c054562840c0d544d014103d51001c0c8070780c0c1c0612149a41c0c01e01454003d41c1541d0041c030042003071350400018081c9040083c40104e0f002404203070308003804905500785000b541d01e2142c1c10703103445107040c002120b469019002c680c07a0060b4400d80585880d62500e0780c8070464020207049580139110414020842d062115800448880c140e83c80c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 513592958 1250 513591708 513591731
    0x70c050f0312180607050a03120b0f01022a0307030507030c0501140a030509010f1b2d1808030a0206100b120a050613060609051315170106050a060908060901 69
    0x50031100f8059000e000001403d10b81c2c004140d8074002c1c9040038085000d0303202c120040c560070000d282c0580580c1e403020000010742008002c0848100000c2e00c2c01070b40b1041c4904c84101e0038409003d0740105403003000e01d01650f100c000030710302600c1d5002201c041c0c002035001c1040000d070791508809401d007402c1c01441050405a030340014010703088440b040644030000314880c0c56003940a00311a41c0707480350a0003400b2007601c840100042d95507000000603505005107805402000c1106400703544440c1c5400d0203010020202e038407480e5004000c5051050b41c80028070003004000924062103290060035036803034648503414103044903911000d4003e9007000f0945084000e00c8006522200b40d41000410381c54010108071074003112003069401364a440d10104030150030a10a4044900490718800840b42d0070382030700140c1d01d0160043e641802d480340c0074400005c1243c018400e880c60400000b5a15903a0f0f00082c00c250841c1d400880412131b180024000542c09001c02a417140369513009100140011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 513594208 1250 513592958 513592993
    0xf050a0b01171905011413140112171810181505090301060e091020030403020307081602040c0f0e22050a0509150903070308071103070c050f03 63
    0x1925966600b285040000e2406201c04000702c084207400700704001c55a121011001c400c98613000042c801e400000800090b01c0c1140a407030070713940c2c0203074a8003100d920740f01500081c0c41c0c4800f821944c2d041c1500140040080700406459554020b07080340385c000801e8010f0020440f0301c0c103502402c0080032580400c18030020844031089031002d40b401d80c0c594044d908200d17298003625805580c15420003c00107519180d000c032082c043c424000540d04445c8040707003c40c2c112540c2801c3d0800501c402c48580405668542c00f80d0380c41070180c01581d1503c0ca55540380b80f01d40e40121002c00c03200001450480550038603208500e582c5070703d810b18295510074460042e01207120b2444091050715420240e04101d4840c82c0442c000d02000c6000f400b182c20100011401b4150860300404148215018050010300344000309000d0441140654500202500c00300d5070707030000428100501c907500507481500340080000300340b107502400301c00d058182041d04000101e103082c1c07400ca04c20781c400d607007201684042d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 513595458 1250 513594208 513594227
    0xc0a05090106050a0e0103180c05130228051204050609060f1e040203010209120a0219180e0a0c1511010c1d0a1508100f0e070309060b1002010f050a0b01 67
    0x40e003041c9654000440048002c0d00d04400c80042171320354112500200270100b10f8020a4610480701039070703011000d009a80c00c03401344079282217030386140c110748a010342d034880c0d00c006071790045260403443e210f031030705544c40110010340b002c070f601c0e6122404104070750805108454102c82100f250302e2031317420074000c58042013002089000c40582c2070300124086640c00d60482d004172101500b5001a062440c5072192204003c0c04268020015032001c1700a184144001d0700c20b0342c003880d10404588040003000002001110700004051043c1000100851902040300300244010900c21400a0700c03010010303d0303140c0000030240607078101003400d105e280c1c10560907900d08181c481c078040300035071010000d900e0601582c820803801c00d556042c130f60180d0b8030140c3e0510500c0842c01080c0340076aa4041c0e0321192086200d9915a0228075021079080ba110380c008100f658000c032000f0580300701d01c10000744840401d130a4500581c1d5600a000f0001d00607000311540205040340810049a00c140060640c0b00c0c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 513596708 1250 513595458 513595477
    0x90303040c140a03021903051606090f15120b03010f020406020c121903031103070c0c06050703050d09153b0d0305090f07060302040518040c0311030316050c0a0509010605 75
    0x1d51b220302d0004032000104002150032404450b0740c10301c4402190903c5000b400b482c00001c00c00071010941c40404000c60781101e660804010558581c071204550300d1030380d158201006900c603841c011095409025120042001040050f600d901e4440080d00e00300c080300301e403401000c81035508240c3e440007103001e0700b41ca00007070b4000311094014903049005001c00ea0781c1041c580c4c408411b00103480d41c0000010303002e80c80b40035502110354030b5220540701800758007002000180304110200300607500b9048101c01c036126098070324400d90050100b40c280c8140085001011071039564560031a0000101d40c88058150302c4640d0a04004018041d03c6910b1000c0803021325407540c0110328403d00070405109051002425210307256140c0784002c01070340c0a0701c101d500c034004000705006403075003840d215401554048000261645596103440402000d0b040d0203a140c042400340360003122082c0480303907105100d24080d1040807000d2040212540c060703081140548008801803261036080f1084820505 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 513597958 1250 513596708 513596719
    0x712020f31031403091908071d0c0a030f020c010c1d030a0b070507020a060f1715013902030d050406050d0f1806140a150504020708040509090303040c140a0302 70
    0x801e4010311524511034000390311b8010189441c00103100151702c2c001d0007552403800642d0042a503c100300700241080420301d00012000300085414604110000d084c1000d0317030305003c03400341c003201606002c2b80c00c014030410103651600c00c4160900e60210241103142d22458240d202c180c0c010707002c2596000440c1001740000c420102045040340a281907034602a40200650040394035100000c0c00d13203a035803a424001c84c41c40152013184420700f01d441c030700c18000e081e0100900096840116000c02141c6403050101c1c07420303070202e040c0404030402050040d202c548510741c0201d5500c181440c080c12052002c0070030005001c144031f0f003640801262214601e009010540a01103c0600003e003100300403d80745190581c400000c00c0f409811071403a9005500999a403941c84c1c0c94944280c1e01240b030f41010384481d8a4007030090340760a034040c000d0b0a0142d4400c0381001e440b500031614151064800e20707450b920120401080004008020700904176403107100407000d807403001003950b050a40c0002031140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 513599208 1250 513597958 513597983
    0x1b1606030f0b060406020a0b0a0902010e060702010c0507080102040302190303022512140d0f0503130606050d060209100e06030a0f020712030b0a08070e01030b0712020f3103 76
    0x2078190b8100052000300180300076a52603031104061b47da40f0140c20202d855008007000901c6885652258211050f01038658240003d0200c04001003580002c0049041c0710160501c01c01207882049000301400010000681e11429070042041d0386c1d14a48040780b10202107041400040e501064511400310500200303e944a640c001080303054025400a10390040c1e42001f103014028000080c11030907601c0800e940a20301159400c45081110942c2c90000c140b081001c40d0310201c2820703c80510302e0040d07a000544a0b1584005610358061030b0041c2c80c02d40d008508103130a841d2001c1000c181000b1400d10002c58820310b4089482e90000400c0801250f0396804408002d50160f01200d008541c02004c1200650100324058018860941c0361030064101010100e203d0800144e001c05440b008a81c83e1001c0c1e1841e03444840c05000202502c042101166007540d404101c0c5c0003500b02290f118030584e480314018004d51302a04450041e00c0c00b000085200261aa003c0c440b0020503290860013404a4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 513600458 1250 513599208 513599231
    0x405040e150702010204031509110108130f0506040302070618031205070204022101140d060903090f1d0c070807060b0a1e180509030a0e0a0902040b1b160603 69
    0x400c0c0340c0311040300c06074815004205001d030f4107600410603244034075141990707003a1521086085407401c400080c0030483e1140c000e140e543c0119419031f800145403000d018807407196a00c44040b09885981110342e640481e00384020140c0600c240009041646031041080c44001420000540c42d0320001e06143c142c00354204c0c43c03600ca0300c21107190540240c01950f64041e0740c081800c0d01281880c411030700c10110703030011596010a88104004020041040e1404001c83d2501d100901d20074100710b050141d048030000f001180c08558000801480003601d410b82482100846200701c020580d0075082020443e420004507110140c0340400d03008a4005072207140c0d40085032036400a07030440e074040c0c10490241d400350301c00d2050050540303540c030300044041030f0100e568a040e244261000029600140001064a40f1400401d080100002d22541240c1d640760703825422680700d900316440c00c28001410503040401154880c0140811000a00d4600342d40d100050700107141c0d0140d4020161070301c000f02d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 513601708 1250 513600458 513600463
    0x30a0b06040f051906090e0307060203100306060605030901060e01030c030803070210020f0c300d1107030305010503150403022802120a0b01140f1201021326120405040e 74
    0x52800300c031001000f00782003a90448a00a0b1681c1c20240c2c0d1908103000400c120405010708070410641c90001e5062000070303070780c03000070b9040100130308020104a200080803841740c1c004d2000030185901d49966a040000da03880c203444907a0414464200720400402c001200d420030315003180d4000301001d4603601c0d082d034200d0410180000002c803450004c10071082880a40c00101000907040c030031111f81c984002c034556803c062010b54158901c1d804400384685010000040807456141100000d05c1081c50302e0601c0395070849901600004d0b52280107016508003040020441480407050f904107241c160b900950b510358003201d10940000325604170343c88581900c02210000c1d8003c15140c2c02c100d0200d00e80d5615000220705850b19001c0d0350002880d15020300c5c0d60307618030402038a0f034040f001054082c80030240407801c65454541d420443c51441c0c81d40311180001414050000308071032000068081c1544241480c0c103009c982007000d06c10042c81040c0708039801c4a00a0302d01262240440c0902d90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 513602958 1250 513601708 513601721
    0x304050c030a080306030d020c090a0e0a1e02130207150e0a05120a0f0809030d11044e0f020d1202030a1e12050c19020c120c030a0b0604 60
    0x54140c0328620401c000c0005410113148100c00503000c41d000c1d03154000b012650703403402280842c0c0141c0000c0120744100142d4100101d04182c0004880001c860b0355509101620001110f04000400322490f10840c5000046031417400000310065060180c0c0307455121400f0592900f4000f41541c0303024400e000030061110b604d0094003c0c2c00e980000f05040c1424150340d02c88813030f20002078003030748421080b175000f92400c502034806040118200001103031040000d003a00480d01031003030001d00c07000403030040941c410906901ca42500002c41e6038180d404000100d00842500740c0300c40d80304050403c040c0001312012199070032041070102c10400c0c3c00890580b000405010706027542136000091800e400000401120300f5a90701c80c650f02c1801c0700903a0780c0081c3d581102001400d81c108491f850403ea4002d25046856202114600a0f0600c80d00c09440301c2840c1c400c015810020034400c8600c0c0034241401c010318a030003d0031100456200181e100d10b248500140001004804105079884a13070141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 513604208 1250 513602958 513602983
    0x11511100e1006060c050346030501080316060b0604030203030a0f08090a0b0a05060a05060a090303030b2b050c09013c050d02010311070b18030408070605030405 71
    0x70000318075031080041c1c8603a6414119058581000c0d00000c10510484a0f02c8401c1d800070051814032051203e002243c0d41000f503141044240ba030b50801d080380c61000742d014125440c4100f0404410052000703029110140c0c042c1c10175400070722404160f0300e021880d01a06640c0002d000440d0586800019081d00a0b0b800194040c403000c519200c0442d0000500a80c5004a0300c0c1c01c036550b95001400c65607085e12007401030185040038049901000d480d00601d40000c0000d0031102103d8544000c101d068129034600000660300b690200306050309032084440141040d0b50004500c070082d03142c01c0312640c20b10104032042000b2284c040620206000410300040700601c0344030701d075a40c1d00c09810551003a4400b852f49000f00d800c00c07507100218200d541181c14021030301400345403a240030800d000c926458140c2c14184c0300c206000105a17410010704400d4440e200000060400800040c041c4422007880e8a070f07a4000c001c148481c801c001410011164140b0b42250b40780c0d62458a641480000f00c04c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 513605458 1250 513604208 513604211
    0xf120c140310031b0303020307020927070f0e040804050603090a08030906071d0a17120301030b0907050a08030301090c11010c020601090e01020936091b060301151110 73
    0x81c044180a01c92031102180d005000b084c142444034010596a102d0f00e200003005030b841001580014100348010940c0310000408194201c4000e81d031404011041c15070220080e0000b5a05110401c12000c2c540d01500840c44184000e143c9a41d840e0401d12130340c020309104001c04000100740c03d0042005040c01a4040f56850b283d0134a806801d03503809040d910795000c125440d17030007800a010603c50440080300141400c40c0d0628082c840c02c1c001140c60340d58000c502078551038031020210a80203500070b61007165420700c0c07454031096445c1494029085648500140358040055050000c02c3d00e0542d483d070400018240300868042c3da04500c803c400c0d04c8070307501704401d6484d010b03000f0907418100c2c1c110b05028442000524141403c034810412202d13445107231281e0810b1891700341352480001104221030802c1455518507441c08c2d801e01128160300540c4007044c25071080d04100300c2c00718105401c0d2a00e5003907506000f1071103142440f54003881c040110812401c12001410003e940030301010000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 513606708 1250 513605458 513605461
    0x60307090903023d02090102010501050625030519020a02310b030a0c090207020118151407050f1c09030b06010302160c060906080f060303031305071d04030f0f120c1403 74
    0xe500303005e90031108540d809540b8010001070ba5041242c1210112480800e40071541c214030150b804e000c51511b001901000814800b407141c03686a1070307a050a403519900148120300030b43c410070681820340c1940d40b030034050103030451040009410580300d00c147e4900e0041041e115450203e407812080c03031005032011000110028444035664010b10b007481c001c1e6248140d000590b032601d41c0303041c0e0a110300b26580120600c211145032103030703541421082940c00307018076010054491a242c4030385909102c2c62030f00102e800e000d888889901160394a015410501c0342d040c59512605041c0100a1886061540000c1c1c041c5110000300b101c4000b0940c041c0c40105096200c00d0020220315240c050100450046800b00791191055031046104180082c0150b00e142c0d40e081000c6070a0300034410441c1c09100c2e40c1c5000c41d1880b0f0652000801040f01943c0307111602e8a820001d240361440c051020600c141c10407400e40981c0c1c40080c0700c400351a54440800c03660310609007261420854500c0303910142d4080b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 513607958 1250 513606708 513606823
    0x3090807031d030705010f050a09030b01090203070801090c020706031e06180605030a050703032f0d0e0d050a08030613021c0e0303130b04080c0f010506030709090302 73
    0x30502c444a00d034484110302080c00c2c2c4041c0b660321545806440c2c0400c000001070748056200c0c40040001c140549864100940d036591021032246085c3c10600000c1e80100c01c00000c82e81c0a140c81b4014421520140000600068040c0d01c6080318003034903041549030701101028410071030000703510b5040e04d05c0800c00b41d55a1100c011055801c52403640b4220304040000415282c00a0b140c44110313001006084ca040c41d665040d07500309000015101004a005c034000d00741e401c40410400c0c0300422002800041c01207400003086410100041846a9051100000860303c0092018185a40408450fa89460340c0c40060781940c0d090a6a0182500000704003504400340c0c110744c1d600b078641540901082036000500d81d203c0c0000c80750b4050150680d000c9102040701d00803038a4005001e210390503d01403901501d541800d82240040000d41c0d180d40910039542805c203c900002e14990104100038912954021344565104e5020000c59480c240442c3c402c407030801e112410780201203041141596075a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 513609208 1250 513607958 513607967
    0x70203160e041b030209041b15020304141207060201090209070c05100e01020904020a17060d1a060a1503150e090a0b180628050c0306040228050403060b04060b0f0304030309080703 79
    0x840045015400050b00003551000300d0407c09d140c40e1294014500f824280740004000e1207a03240c044d0381c44480320081d610322450a20180020f400d5907800030420300018011701c029600060507540406c0f0800c04941d0204502151911300008400404140c40407101c0f051b41c0a80100c603246a8480c0c030005031007080c103403c000c416020031481c003070003196a9284e01c00c0100d48103e050016101c007007165140030020301c211411a503c240018000e02c1c0258444a43c015180e544814440100b60745241030250964a440104010000d441c042c0c007191802102450b103a040440005180daa00030300812400d9100c0c010020b281340829086036460320b80307907101d04500300445d64480f1901312802c180c0307000701003d03024061055850014552441e140c0100b4440254080303080c4105010000c1815010307100345007040390078100300c0c1d82d80949071425810b00c0301c111101c100d201482207243c048100020944503060781c820070121449583c0300e0356107050a502070302c480a4000c05151001444d501015001f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 513610458 1250 513609208 513609233
    0x306060711010903021306030215310803030c0c0105240f010e030a0507030b1303090510050c101d0307200d08120f0f090616050d0501080102070203160e041b03020904 73
    0x2140c840242440103d090302c4203100701690f1880b00c0c5c0400b0300c401004505650f5000c040c03c180307684030590964334400c0c00e0a60304195500308a40c140090b105079002e1003400b030581c0052054805075911100d003400201c0007005041200e000b00b03054090f6000c203078001c1d016407140c81030160550303111030414034041d0b07120b00c1e044c0012a0743c0c1c80224003280c484414207442503100c503450b41700e80104034107203004c1240007500210300d9030030070400f04880c5901040502030360640d500800c80114481d1442d403041d030303821000c4c0c50f20080554001d01070034010074580e50f50341c03224100c038140781015070301038101040c0c202250713540107004003000040c1441804c640041051040d0360341d090351441900c860241441014003510030041950000d03000c1034103a0003000842c0707e2550305062083c40d1461000010040d00c40907840280356950101d42d54055003001d000604407403030303242400040f09040c9041d06114120103003000c0c1454407118a80f00800403c03110b1500034580003841030500745043c0c50641c1c0000031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 513611708 1250 513610458 513610463
    0xf0a0e0709051b030c0d02030c0f07031709010c02030912030909040f020103050112050c04111b0616030b0603040f1514090f0c13050a0b0901180c05030606071101090302130603 77
    0x21583c501505416500107407400380700018001840d01804100440107504050448865007501b000300c20003510b80c9100410585210303854104869009404000200384c00030400d4030f0030b9042c03501d800074455000c0100c0d04010b00131154000c141100c02c07038080c82c40c042d038015550051400030500c801d110300c1d044240b8503103200740d03002d006a81e02c44500e07440c81c88911200034116805074608841c54130703003034000c0f032001d012807406075040001c03d04030003090312800c80d9000569002901802103001079850032070513407105c82c00e09110000c801004140d003884028005810b5068046954007084040d4071030740301d064a10b80d0b00744101c1401c00544182c1030000e54506646100f550f184219003100400c06090310100242041c1e010138491103044060300000f04103c5e01c80d5654508005203076102e42405001e41900407403c40da1a944044010407100d040300d50806014061003000411356403181203d40d42680402000041e508460051340c440d641358000a6000d0014035540e181c0301d11135440703903086a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 513612958 1250 513611708 513611731
    0x302070806063a0b0a060e10050901060807050403060c0305160e130b0409050607020a0b072f01140c0a0f05160803061f051b150f0a0e070905 62
    0x702c0b54003c01c44411429206680550025204480e100d035845100c600240300ca0102000d081c400c3d03039104010448210356210741940d4540003409080c1142d1400781d482481c601e43c440c00076003400300003065000144a030705d0800990400064100e4441d6050b00c009540c42030003807007130400550f401380103040112042c40b15003011410303065181b8400c1e1082c1c21104030280c050307142c100ba8121a03002400b0040e92094000381c5400c3c100300000c1302008018803a4180c0c0c1e015011004191801400702440900550104030158941102258a1014a15040704c0c0c044880402121030941c10b40981950344c000040c07141a00c0c10400303101c03910340c0200906c00080e80c5d07110346201107410582c1c03980a0a82c0d20b401003044c0700c0080000944c000000c0d40c10240040030b07155602e0080441c0c800249414110000003600444c8520b2921981c8141030111080003001c1c1c14100e5a0650584000034000c12201c2941c1c40e03600482c0711401540d01c08520a8001000e40d40255221007000000e420300740e42075034104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 513614208 1250 513612958 513612961
    0x15020316080a020a09060e01021608012309031c181103070f0803180a080d030b090f040b0a0504111203340b0601090b1602030c100c0212030c0a0302070806 68
    0x88551003113860060703198032645012400c06004482e110f580481807030552040c210803081080c0303a280920010b045101c0085100000b0145000d418085100c0032500004907038180510300001205940100c1110390612080581c4145c0000c007030f00b090000c4044840805007900305020320b04c0c104404410007641191041540da804251031600188030301e00c01c43e04248000801c485d4071002001820780c2c0109052a00d50300c0700502801c11442030071080220303a0710301d4070341000c1c01d240e1a0300340d104140501b849a285401d40310040ea242c0c2c01003031940d119079140c00084c1085100f507071078040039070f01130f014131040c0300c400d501107942c4d40c003019032a03070004969401c5039110039480742e0001d0340081410038203611241e11b64902d81c40060280c5001c0c1440740d501c001092403040315003d040b0142060b1440e003010803050041c1424894150107080c0542218007800d00d1460b0051031b040419581070300e2041d110203050b25414118042c1860750125402031091080926038002144000d42d8400c80c103039280c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 513615458 1250 513614208 513614221
    0xe13060608060f060603070c0f020a080102030c0c0f01110f340506090105040f030507030306091104090c0c0308061201060e0703020304050d0503060109090c1b0309080c0a0e0604091502031608 84
    0x2580070896904002940960314200040c8201007003927046c51014200c0c00490340c0f148002826038208541440207070a000c1902e0840c244200543c41d03041074450020442203070700c41e5083c1c2c540d10440305908049000050350400d660300c01c01040780d0204901c07403104104c422442084102940c0494240d60301d21030040401c18925041c4112030080341d1041161012140344e542c25181038004c504e0550034103580303000000c0c0c0410903010b20501c5100ea50714071642e40d400c00f000c04040f40ea041507410100880c011702c08000903008141d00da0402002c41720314a03120728800c0e116015000c1600030324800c805041c1842a681d0f01900614003880c401c0065628100c42603c1c102ca1b42c3c0001ca4900740040c410040400c1240c100d0780c8008070f2130841d807402d00d4550341e9825201c003c01500c0c90049000905191007044520380900800c400c08000f115180c82c5240b90046810305100041d001078842c554030380c3c0c200200701a0400002801c0042c180a54a92a05101d030304514031200d805500411a8000040c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 513616708 1250 513615458 513615469
    0x3020a03270303090c08010603080d0e01020307020d0e0a26011808091c1b0f0807031703091f060905060d0b0a090201180b1306050903070e13060608060f06 68
    0x103000c0c181c40c0105010101a2000c078050400181d040c2c030000880900842ca9100a01584000d907000311102551128030300000d00c00c4030344880c24003065920520510010759030104040307010406c28030706060304012140028440d03100f030fa400000070900340400024919800c3c1c2c0310003c08010300c0000c00c881c1100010f049040d0300a00790080a007441006000d2552915a00e840804840c1c030039281d410b4091641c503450842085074540d1103050003c80100510103e03606410044c20400b000740680d00e1460ba11851003003000c40404807030070004000149044c0c000c002885403940da1040c40d100702c20300b540c0c0f8003000348800c0c000d0003038160800000503041e042560070004403980c4030694000030b9036094005800ac00e81e00200303c0c108620303845d09520300c502d80d64444000d8280d6842c3c196591034690b00d0300d9880f02042d03101c1070500c007042c420740407103540c0450b040e8200c070360304824002e40c2d940e0311140600c100581c00000f4901032422101181d554400034000780b0a941569086283d911036804019 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 513617958 1250 513616708 513616751
    0x311032b05040c0905100f180c0e0a0303031a0307060c050c0d02130c2106142e020304080a0606031b051005090f031506150304030806010f05160303020a03 68
    0x80004000601c01c00815000f6030249071b00000e0000e008034603a407a40c0d640c24081010f9804240e0100e0303040e103207180b42c207098850305c00f0b0b004560a111095001d01008100801000e00c00034080c0f580d02d401c5140c4060716184400200038004044d2200562140300c064400350b5841402e54452003805660703032903410840303040141e094000b031181c403600032102a00000381212080351020000b074000000072a85041e810383c1c44d4075a1103000401c905081110302d00c0d4000e44600c6152041030301c0e9601519004102e02da80d0496501d400558503110100310b81a85035200b07503800786103180b00302e07207640052140e194400c2050b01d05c90050501200016003020004030414010703640e11808003d44124540d000c0c100501c001103001c1c04000810185200107400c00582220711000e0300644e0302041101d103040302c94004460020b800040c114209506d004045d02c41c01801e8a042c800a9100c0c1007016000f030080d144810b03942c0f0441c0540c80164500100650042c4c41500c0120b0300345500c0c20605c540c1d400442 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 513619208 1250 513617958 513617963
    0xe0d0c1a0c3a031803030f150b09060703090308030c0711010203070c05090a0b041806050105030a03050702100c0203030c16060c1502090607150212070306030203190311032b0504 78
    0x345001c4865100249180340c41000035003d16544000d451100205480030030340240c041c0c0c0b0001817080e1441c00c2442a01c2000c42103409800007903405001a0b0382c0d410a94914820689a254840c1081c6c40e05603440601a08003038000d60010040048480b11400140f1140b4400c40c0c90240c80401900166039038000c404005180da030710840c0510a50500501c810f41c00800307040d010503404022004102241e0441e071425507425055100f881c244071041c020705005020540040001e640720f43c8004100d8000c0d00c01c0240720f039400c5d6000300241c41c8100c45079500903030020152980d902803502c269582b0a1608269101d05a220100068103401103169044481c0c1181468648201259190009502c442011640308409000f4a404198124242542440c440c0070040e925a00d903207031007440e164002c00c20401c042c20200e081c0010303100820a215206507944044844400510707017950a01101020082c81380700c0400d0310306055080b1898005e040300d04210040602122249220980c0c2d802c4401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 513620458 1250 513619208 513619273
    0x11030405030c2e0e0c120703020312031b0705030d0c0507030206090303090703060b041803051c181514100321020312070c02091005040513030e0d0c1a0c 67
    0x1240c0303c168864101100e480c0300e076410764401250110006004615a03044034945501003201403045041c20000d5802201c200c3c0d40c0c045c20761818801105903440e241c100c450144070085204420024100141c5030100c1d03050006008a00c170b04000206140c00c6400c0a40051255602140001c800401101e019408520190400314210b0b12404c0181c40c090103030b41d401030780d03a000400c0341e070041c10f062040f503510a0b5200b9030f83d61070001c6641e00305c210340c0060070702b16840c0030400400e0052601e9210801030f40302503084d0b14074030703021060b00c020903100103500c00441c2404108001380ba80b070103044050f02c1c812440d4580c800401c4091110000d03084116001591080000c1400000061070f280e512105a01d005500104030780c0c00328219100a40f20400d60400c0c2144c00d016500c0d003030040700d500c8032001003491865441a180184441d043c40309450090100f10401c0d010721640c0c0b803114000c1d02d01000148525100302e05142440e074000c120216140c01061300021a49404603141e0300c240c10b46100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 513621708 1250 513620458 513620533
    0x20319052203020a150204080607021c0819050412030e1c111905011508030c280f0f031803200109091409070503070303090e060411030405030c 63
    0x1d0101048441c408290194414080260000381d0985008001c10307000b540e0158a851070030200900c1c0c0007014020000755003001700468a11580f5125151000440380b4108126454622429040141208100740910700304410002401000e85141001014035941004400030181046482d5004681f1007103a848040b510170052a1103082c4d4030340c0d02c100722001d40f04800091514564107605000084407542d450300503a8003e0750352234007444000c05402001c0d601d0200c0081440d40c541d0350006028400003c06030210f030002000b07984540d420b69021040c011158000e0902c20307075843c0280021800030360600702c001c5a04019025640440741c5c88100043c841c481040fa004601d80007103181410003c1c01d181c0000c4181460040120990002d40070440504050b05007a0a21005421090180d40100350402c0001d038040c2840048a0340c403040a4103076118000040c0c0904411650f03010040d03030101c00c2c0014840d01100420011003d02d0448289030391150101141e01080e0b0003025104c0003044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 513622958 1250 513621708 513621751
    0x302071815050f120a14192a050a0902030907120b010e19090b06010f0302030c09040504060603050d021b03011404031209021f0305010b03010e130c0803040902031905 73
    0x24401d2080002c0100c00a105001c0c80b013485c0200125003a602c20107603e0031004403500030320600d01c41d1000b1811500070322180e51a015048800e5036103007800c8904e0510841520080000d111004e0b0100401c0d10400d196900d090201a42069500f000a4092200c0000c0c864080ba211034200c242d0020301c1600e540c1c40c0c07060411810034010640b4070b900821440045c081c06041c852400c403940720b03030b400548600f00200010030b00303581041c14030241441001400700e0003001000f60340c0c8044081300c010031250f449181c010060040c2c0d91004102d403082403000c01c1100d0700032510440110620b00301c0c0740f80450a070f00305401d9403c4095142e40c1c0c6048c031390101c2d010a12400074800e000a48050120345800f00b40d0201e4580c02d01e40d111805c0c100004c081100c90203a0502440c0e00500240d208070f8150f5040c486e0910402c000506010546032118003540100820800d007540103140d42e41c15a511a40c0d640e01c001c02079403084422503500b80440350f460a502056106aa008400c03503509511481e0340d04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 513624208 1250 513622958 513622969
    0x70e0403090605160609120206060f0a14060c030f042c010902030c07020910090b09061008090a0803070806280302060d0e030301030501020a090611030a0302130e04030207181505 78
    0x102000c1c1ca003403148904c2d42d40400c42c2800390030380d204e00c20640d15481011041e0024109400a4100c0d84a08409842009943c0d21031100c0780541e021002c80b84603441042002603001c0c485c01135202e079a4080400c851030484c18150140003141c04244481400b160b004082440400c0c1e80f01c48683c1251755070005110940c61680650740c04406a410103203008540e40004076800d0040ba0000c4d41c40040d0401403204260324041c0260415050b102c4a42c00e08250001038802e02500c01c44004001107500000c2e00d14508020fa820a0b0b0b40205485540e400c00840c014103800c41241c502e4061034482c14510400080d240203040f03400f4001c26130143c07441c1503074200600c6500c21040d894075587c88086007800b10105100031802140b21790001a6651002c0300040c1112030240d21501c14005040d01d4542d10003030101c00c8400e1610a0f00d40160765842150209110402907000100301101210404c0105600080c0980507140301e01401106448280b02d1101513a04d0390390f000c000324244410800460411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 513625458 1250 513624208 513624217
    0x100c0906020307060b012609010b0d0b220212010b1008010b09150d020d1e1407080702011d160e060f22050c031506090f06031b1902070e0403090605 65
    0x500d0207443c060101caa0a54400e8042c0000c8548010301031f081c856604024480d010f40410180c0312443c0c900c100e030301c4020891800401d041000101c10b06106000000360500130045640100641805681c489003036008104044440307025240810981c0360007801643c415048070f400c441100d00d0201200e050050009800e450001d48002c1840b04408401460002d490089491030002586001000c0a44440d03480203485101c0c032482d0072001114034645400080d4040c1c01d5040c9100d90b500d410b03000f02d006148a40080c00c00d284040000d415050b8040f6280c0030f0640f007d12402e10068594152442000040c1d0b10f050380580480c0d45110a820200c01c00d0694001c80303488085403c0742c001e41c20f816100c0448110b41c64003000010489540c441c021003045540c03054079000e044c1a103170340210390211004968948a42c001000240d02240c61102d2145090902e800b81601c8070120728556000b4503100242601500a0030008610916080c103044d1040d5010780d5849410b0785015402d0710707258003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 513626708 1250 513625458 513625481
    0x609040b2d09010915060804080c071d0f22021201020a030903120605030307061a0409030f03231b120c04050406083c010e100c090602030706 62
    0x566204101c0780c5810aa15030345500c0300d00000c8407070a08008208602854160404c9440c1494007425100c2d802e50f001d41c0400703031812810071070202e0301d440c2442c0071240070b440e4036840140304070039001c102016220440c4000a070301160881c1640c4030151001b1516400300c5090104d08a5101055040c42064801000d01400900004520a9040240c42c2686d11007c0a40d000c2922802d1200415a100000455014103842d04200890804e00081d44900c02c0d45c5014115070385840050030100c282456014030b018000b0000c2161b10180d19000e4908190aa56500442d18190121000080c103030701c0194082e0703511000440da0b0b961030300218154404103170744104864041c080c0481c0200c1c8615094052520003038080d071518030309010041990318642082d01c086d00302e80c551070700d42100710702428a105481c030b190090400c40c242c00c0030040101d20031154100e40c20844107034640c1e540410503011151002d5024065582041c2d4141c5001403d441010f00690007000740001040981c3c0c004e020040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 513627958 1250 513626708 513626719
    0x40f141e060a030b0d0c1a04140f040b09100303120c0c14030c0f030405241801050d0f0905060f06030d180b07080309010501060906050708090a0b13030506060d020609040b 75
    0x1140c00003c05c4009a5041c0f003110814800ca0090205413070910010310003e039500c0c6a01c1ca0036041c11300718909060001d01d0b40d030080380c0790170340001c03990307155003054083c59005883e85500d441d1100b00140030701c101c0c1c401940850204894038103844808d0017044d108180700e0312801004180c62351003040303039950780707912215a001c1070208800d80d1809100b142c8a82100000842c2c54a003044108000900304c800e08a6030050b48044030071075407050328243c40c02e445a00b10036600491804e00140c3e42c1307101d10105040300720b242c02c2098181d000190f001c1211140200100c8005599a0000d03042c035030300507212075a143d8010004e510044c2d2040b89601908100300c0b09449031a40d03113140d080782ca80c025a900300c810032404400c20607000024402c050060045242611000c0c0c40c145004d0003078031490001901004c000194041e0f1034a42510000007400b003401003a9a80c0c0c81c1c5a1980c0040c14580000c50700381c020340d804940140380c20f403500c29200b0380041017146800440342c2008002c00c1c500300c4180e0003e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 513629208 1250 513627958 513627971
    0x30c02040b06131a031005100c0c0801091a070203041e03170d0b0306150402070c080715170f0c031512101404081207021002040f141e060a03 62
    0x10384810016241d100e010b640f00e031030f1460424143c1c0325074110b60554020440418420440c444444007528021504107031a44803a8131601d44040b80c500c40040c00180110300460000540c41c0b070154410a01d0500884c810b4618a000e02e10140d00c481c420b54602006038424401440500c034501ca0808122901d0105103104603500d0340c1d842c2042c8400d0308034403c07007400890f04411003201401242c100300c604034003625192406404d000c9004520340c0110f40603075030200d0548100b00e80c5081c01806060103008a034070180c2e0b00c0e02c5c0507541d28002400c00d800503103580042c3e5080c0b0b0800c0b0341a0700540f1a1224410990303a6049002405d410040c480f501100b01281400403030703151102c490000f4980f0001420101031240624002e0713912001d151a00740c4541c108010114004509407041c0e58030409a034221034480120413403400440041d0403000c1031000900103403141c05070305690100ca920706c080702c103030b40b88a0080140501030021010400b1056400801e0646413020040460710b0300c82c1000a81e8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 513630458 1250 513629208 513629231
    0x90601090801090c0e01050904030f050f1303110411030106080115031e0b10020f0604080a020703080c01140604020403051b0103110408030913110a03050702070314060708070302040b07030c0204 85
    0xa507000b030141604d1040c0b5480f024040103ca003900b0901414050301c44120500389660000c0442c8250707001070080043c00316090843d407007140100e0f9495500d00806019441d200d0401030a4103aa8503030706031089152500c280701e0f410320340c02603030704888036074036154030071ba20340500841a5000039469001709550b820710003400805030f400301c01140d004040d00181c01007903581880107041c3d0b955a0030017550b00240800460b000000345140e4801d82c404e00d4141c80c2c101040040e40307044900e400040680030302241100000d80e0550000b020071481c692a2481741d100c2d60203000c100e100318000905142c01c890310354090310381c080b00d01c00343c8000103250001d0a03e524004110082c4c102c0e403c4280c0e1504000f0b5012164989860302c4d0101182c0721204006060340080d0450140c41100b8a0b0800d040d12034000407a828002d11810b0011a00038031601040c0c101c0d55401ea8031110104c4003003002c1410314000c50800d600c20f00c252802e580314241d180d86000c2c2c55450a6491644982049900c644c035803511024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 513631708 1250 513630458 513630461
    0x90a06020d0213081603060e0f0109140c0907140a020f010c020d02070801050c0301051c061b0f090b0d020c0a06060807030519020303040b030408070614091614090601090801 76
    0x14071070528800688540c0d02c050421071400044d80709407450340c440c11003515948a180103040c01c407940541c0c001031884520340796605040d40900810420352801c080c40c0d0a016980b98507083e000014810340d125111040108402240143c83c1e9000291019881e005409104401401084660300407541301d404c0c4070002c2402d440003981d0000050300a40000d0a50310780401c48140503001a500a12045c0341c6007201f04000d00052142c640306072094441c4c18001084c4907203203942103800440500100801d00a200810000c07030030603600141d50018020b61a40c0720312010010359042204003440e105071072407e640a50410b11441c50f050040d1000940050301922400c030090400c400600112855820076500700100d0840c0051441111400b500c01640d01000f149c00f070311844550300340c603602c860420f04800d00503003400600d591f02c1e000e01c84182c50141d0250902c100d00d50011200c0214004035002141485440307659204080d0b11910161481c1214409600c80d1040c0341140e40c03641c0c0d5900050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 513632958 1250 513631708 513631717
    0x30309090e010b1e101704020d1a0109061a07030e04150e16090602030c030901030504150f15050d080304140a0f150b18040b070e060406020c1201090209010e090a0602 73
    0xa582c0200224954113034140b000d05d40040000d0b504204480115003506c40e0304262005000910607a02121814200480141800c0070b080180302d03443c03941e61312079a014001300700038010040b40c5030307001130f1303650108060504681810380e165860502c800c0c0c0a6082c00050034810124500c11250783c44082a1003404454152003450040c0d4007114400510b5400340544646070001c404540041202c10030710034002007241d007800000c0c640054540d4075410618007c0300c200380110040c90425020455201d855000031110001004030010340c04e503120100040030726410340c020001c010a000150106444580c02c00905c145041580c000441c96a0303520940085200210351213140c42c40400044203041c804c0350b0381650103440809a070141841c0c0c030303200108020801046084034400050406d4800d60482035803507000380c02942c440d070716040044e407624202160349001c1c1c0b0000c00400c01904050060005a5801504690300da07402c04101a0215034000d240c004517101d20410500010664030080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 513634208 1250 513632958 513632989
    0x308070b06063a0e0a0b07051204030f090e27010b0d0503040e0606130e0601090504020c0c04050a0603110d05150f040201080a1401050d060f020c03070c0807030309090e010b 76
    0x4a9000103c00703000c509844041111500a203400c40050783d64100061009510740c0040c4481c001c0c0c2c0d5040c40844441c840e00001801c0844a0401e01082540061003007074440c805469444036151101c104046884080f68103504c10030242101400301c00f03000038070040111400d000071528000030404036420040c0141c04071110743c000102000118000b080701c030b8001c44200d0b4035510f405004030130704491002d1401140d2902040d14042400d80e03008040c66402014040c0045d9100c1500c0d4008c81d44078850145800d00031410200010081007840c410001500ea201c03048041000413001403014007006a0b004803180c1c03254051405410030801d03402d07482141842d503000310920f0a0b2000401d8020054401c1192504000721218064940340c4075a05503401079174143c1094282d4100400588481c42c0c6603001284002010784400c1c0000c002840ca2600512158800d2651200e0013603903107400b480041c2c005081000c081c01101d40da50003400300d051840300085252440038001031440c00321003508 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 513635458 1250 513634208 513634267
    0x30415050c0a030c021509060d0b12062401030e070e28020301050a060507020109210803010b0c16150f051b100c0c03080c131a030103050c0a0308070b0606 68
    0x13040451a044070380d0f04040c85a1a011030070b2840c501e01064503806165401d440c126190482e13440d00762180c680d404451042c2d1021525103043c00c0301301d100e400303600300f40c60b030400800c00200d225554028040c400aa500715401807004d80e03d014030b4150b140c58090031130b10000d103603412344882401074040c40c128000400e5100503520752501f82000b40c0c1d0915540704030180581489010050303070b041030300842215004200c18034152544541680e60040b400f000a06040300400042541d5010704043c085026255040780c611501d030100d00442b0a02510502c546020300720b40d205a810f00c5017602540d204400e06009007400c008074060109408661808242e81c0e01c02c45414010462900640c50034100c503040249200301541c8000b40350320001400c248600c40009002400c10700c1100306070b0000c06800300039007031400b07082044540b07640c402e110a0313900340304200c910855403500d0b06c440803c60768417500c0d5916119581d5104810000010010703580f0240612261061801120840c0101c0c0040e680 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 513636708 1250 513635458 513635477
    0x30c1407031b050f1621030509120303040501140f0411030a06090b060a090605150f07060213060f0302030106050318120d1d07050d030c0c030507171509030415050c0a03 74
    0xc0713142c900140d0302001e02c041056100100074020910724a0100b85825074102801c0c1c5240d800c0a40d16440391020342a046620740e03803552034000300030019600640c4244000d011070342c0c019568846040c42601c0a04100c6a541c1c0810000b41c604411400c224034050142c5825881e2900c071542121150801074481861050401c599403a000001c280906943d0904100c41c41c28107001c030b42d030004003c400104a003c00a0180686841c3c003081e0b46000b98851015581c412190b00c00140d80c1400b4803540010404c0300420040443c06402030728140c07060755451600750303038a074401540341a42c860505070040c0990381c050000303180304100600300c4250b0000086554440030001c0c42a4980d04010725881d80c01240040c0300320b03520a80e00b443c0181d014941076000c40011b0400181054255100611a226540c00002ea04d51516034901050301540c0940382c428809c05841c141e848804c940e607005e540c20401c0140421642501141c90721541031400c00c0c100983d42414074030b002c801c0c440c01d034080b074080c02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 513637958 1250 513636708 513636733
    0xe0d08030a14010b0a03020f040e04050c030d020109020303090906220501060f0c0209060d0201180e0105040c031b051c110c16030f03051b1c0f030c1407031b05 70
    0x2d145240c41c80505114403503141050004450189402003010590001824403404006d00160b40c042c00c8048109142810075140c09136030f403007000000d20b0084c050440a18126401841000f03c03da401501452a02443c04100420f0010040090341d009a520641d2005007150032803020302030624100010742541044400740c00c06104424a808003d18036407420f0041c0c85498419820140c2a034440d203040e2460b20043c5e641d01c14004004c00e501d04040c800249210385142034504885095400700b01d51003c00f44210f0688040c5060f00d40940c100c0c1001d00e07000d620510017007070080c044094465800c00005501c5003540c0013100020bc419a000c50090200e58061240050341c00101200c40b02c110328681c2c401096155014002e02803140104504143c08809001c0c2c2c0111100c8800b66440d03030814840d481101b038107a9a0310b8000551901e075000312640640300355001c8000303035141c1102c8450a02100c000d0307030303018420480030000005015102c02d000343c075410800c0c61048020306145203051303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 513639208 1250 513637958 513637961
    0x30204170d08091204090c091502011b1b0209070e0d0605060a1203020d030b010302120a15081b060904020706110406080c04270905070605090f040515010c030e0d08030a 74
    0x83d02140040d0800c646441002442804540072544d5400010800c040102c2007030320342090b0f591015940304d2038071010049040d410b511120302040b01d581c040060203004c180480e0300c6684914404901420901d418015180c43d540f00c943c807510320720741030f009070000740041151280204011105607460f0703024801e06140407a548800b500c20540c0e000110074090b2002580d03070104081c040306055071000a00c070185d1281e0101c0d15031041c0c000503900b19040c45080c2e000203011a07807209050b4040c0301000704811002240c500381042c54101800e0316102171300204102688102c3c24254020340c20072482c800511382d4014414803408102d03c0c10b03103075440c000c009440844000e04012550a08200c280300c40451548080c10701600f104000b0385201c2188401c0000f04110034015026100b044d0000500940c04001092480d0043d1a02d881c0414a607051000391042550041e52136007030140302d0306440d440341d40e005030854040d19107441b0301150b00000c240c22030000b22098828140c00000c020401419 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 513640458 1250 513639208 513639211
    0xa03080c0115080307060b030c0a150c12110c0d02090718120b160203040819141002030709090203060a0909150f020703110f0604031121040614042103030204170d08 72
    0x540242600c1000e100c00903030b80c00340c43e00034400c07403202e842f44813180c2d64071400002c441d041e400003030558440e80c0840c0203003041401100c031030740a00c20300a0600e46400d0400ca0110740700d034081c0006500352240242940c54041c003103c0d400901443c49000181c150003401090760042c0121155251800c10710845001d00e1000d00c0310700203541c8200420002004000f5900e0103c030488441204802051700d02074060342261000ca1903244903007590008084070301d90056000b02c0068448000d0340ea40d40c4500e109902049414640c4040d45460400c40d01809030800d0100e24400c1c0040c40c1c04a0840040d030f001c0764421210500e41640c00700d1528101070300300983d00b001c0e400480c014017074440d02a200130f5584000400050803c689891405040c0008020011940310740240345206551810300d20581ca4116205120005032036190540c0041c441d40c0403101a540385030f0f502c209920754140303807103813401c030140080742059401c20001440000e02101c0380e111100c1d2001030300c0a90782008006007100d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 513641708 1250 513640458 513640481
    0x150b010c08070b1e100510020f060a0b0f0901090245210309130c090306020f12040311010b01030204060e0d05010e0601030305190e0a03080c011508030706 68
    0x145000004040340707002003030300c0708580d000070400a2a62621444840710055025460041040c141400041c200d00009602519000d4034800349100091724220baa8203c0b085005106401880110f003d400c155003201507e51000f030000301d0b0901d5000c0c007249006601b60301525155034041004400b41003050002c03000310006074070202c0003841400030001d0155600715001030342054458132700d01ca40c80742c24801498a884641c00960840c04001543c2c8a511980380c061041032820344444001c0b00314419040700c101c4540d0382a066500f90381d16440298450240d50707d407010140540d60106064014480c401c1d8401e0340c41d11441d1080324045400e5801020bd4141854010701c070520450b540b041148484500482e0a100a401e0b01e0030164010900424107070329a01400e800070090580100c002c10194500303e03d9901001e105502c02c81d5820305130311125900410150302040440c0e403407000b0b071910444100001900032034034a070750b03205850540d2091605402c042261010b000562007142c10546 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 513642958 1250 513641708 513641717
    0x7142d12240f0f040b0306090309010311040e01060c030504210614150103110708210106080c0d050915070e03070506040e04060c02030c0604031d1917031303150b01 72
    0x60110000410700b1100d82155070050400c055412801c1d80c0e02c1c0c000c0d030050100035040d54a58140342c501240c50340e01043c0146e0220382401c0c0d282c203a40b01000304607403c0764000b145100e166400d040c01101c02c084401030690030040b0038000441c0743e81c1c1660b020345e18600100c00c501c891902c00c4c40d2001c2a106a42d8040351512600360402411114400e6404007800b401d10f00007510850002e0300740928002c0c014013410711040031409980385451400c00700001ca0310400440c00070703039841c01c04031401c403000c6444609240e81403242d044c540040782c100d00d402410040943c0d25040000b019800311100c2292081c0010f0364000c3d41c3c00c40c0d82001e00508001e0442503420a280c0707402c2c4200d0b0344800c640a030000300801d60b035101c00c601d0a03209105030b4015400b5001030360010709081c02d00034801c00910228241c0c0001e4000c0c04c01c803524100d100c84150210070b42d07042d25210304c0c2c1400c070305d950609181800d03103602041140140c030f00c154001c03c1000d984507030241000402c0880b41c00c1c00b10b0b0002d03000e250610 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 513644208 1250 513642958 513643021
    0x3020a023a030e070e061201020c10060e100b370f030e06160302040518010801110a0206070c020118030501051905101205070b0c030304060507142d12 66
    0x405004c01e1540a8405032955110035403545e80104050340800c01e4940815480071480c20101d03500450713000d0088880c00c03407e00120b9251070340c4009421090b0360801d03a0380039480003040003940c14000303440b400010711200c0c6400b501000c260400c02c461440c200d19907900d403a41c442c0e08150044000a845070080c1303001c0122041211003550b950102511450302600524101080c3d40c0c800d4044a01900300a4507580c08801c683d01a440c80c4402802034000650a25041c940f02e210180e080d10300e00c540a030f004100a49800c44117030349400030307510107070304005900401c030000c1201e1003003020085221703400010341850402850908846140c0441c24070a040000340b11014241841e81d0040c0c618000300440960158a0440c3c0b500781c49034002c0600340c8000c0340480000354044061481a40104410b1000395200c1000320398041800104c140c0640092107020850a015811010f110101c200040c149816220705140c0c0c5802082d0030071804a040c40402c03000480440e801901a4007044481249 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 513645458 1250 513644208 513644231
    0x905060a05130b09100c05030403090e04030f0c020d0507080a050c0901031a100e13120f080127050a0c020f0c0109090f020d0920060903030301030303020a023a03 71
    0x45102e00b10060031010040300424030210003070001c03082d039400c02c41041251640240d8081d150b90030072682603001ca074a202c80003070424448441c1c03e2242d6815543c0c5809205610821f0b185403419000c143d03000541a010f0000150082043c80081d0030b2403401800c03c4c0d1002c0c80c3c114500600000c2c4140110308503401000000c25000400985140c8140300040d5a0b80e101e000307540110980d4060401c03d808070701402411003044581c05c1011b40513042501e4400c3e51400185c483d0302403c29104c00141061004004030080740c00205e5244d80079034100300303400000460160a580095581c41c11071981c0e0f02c5100c50140c0c0400590041003c08000b400d0f8140c803480010380078102d94824440070395201e24030350010054980c1187d454610441003040b030040a8100510000c503030440b00078a40a02c4101c2d1a032a241c00710507910320000c0100118074613802c3d43c0d0101c02a4001d0810300f000c3d40b094a041490030025071641e996403400d2001400d61420821109841c0945d1155401e001e15107000140d610 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 513646708 1250 513645458 513645481
    0x90903310501110a05010c2102031302010f09081b0a05012c0f2205010503010e03091507020d060c12090f032307080c07081623090108010905060a05 65
    0xc4a03000d081c0f084418034a09007040c20302c1e0020a0080035540f03405031501025800600c4c0074582e0319029816189880c1c14034121080340300c15100020384500703281c002d00c015842010005081a618944546000d0703845c005103140c48000c01c80380a0412000504d0812401d01c2000d80000708000d18209000d0415403101c80a40020480c039600040002d050082040e1035082d00819a0a40039018240b07107407104541103c04800d00000125050500000090300c3ca014000c5208502c1c18101a40c6040080410846030080c145180ca032546e074203100c00c00140c0d88900740c0b025030354010f001c042404284c000340140302c4000c101d02c00f9111484d144080700460f101ca050324071004d60604108040d0880c9207000c1d42c0c0c40408001080759020005045002c100f54840039200c40c1d2080000c4031046174031840015107078548880f8a410608100310104851003020f0f0710001c0c400c12524281c2c01c1c020b8601e0200d041910240c009401ca45e440d5140402004010000b050707101042400c100700701d0400c10064003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 513647958 1250 513646708 513646807
    0x18040b0a0b07080714010507020105070906141b060403050a08071407060515030d0f090f03051c03060504020f2a0c0d031205040627051207030e090903 66
    0x110079440c0428041c08101c003002c02c9400a075002a012644c04030200401c81c00303488103c904000550801001c211b0f92805810708a040d24495200c40020b0118034040000c0f9030440d0441c01d24803a285100f24503100e005210f4103000c2c4d0300940d40c0c19543c200840029005a0f0003401135003c0141001a144801020800b510759160f0300000c003150301e40750b007030080260300503003602298140503190340c0206080d0041001c102c0c8000948800c02c0d40c591b228001c0d4203488040c84042d0158024824400c1210070b102c011500082d40c2d410001a50307030312800443d080740c0182e80c07500e4003180700199008104442c40c1130400e070071900b068040e010f120a1580d0a8640340d400ca41640903c0c100c0c6401c00815000300402c02c506101c01000304006d00e8036040c1000500307400c5602e0007182048480d5981c00140180100e0030280c1c010000b44031014dc0724020b020143d203c204154100301e0780115071603141d40c990800d680540607520045850b07000c00d1100d610442d0a1204204d0102141518a07461001510081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 513649208 1250 513647958 513647969
    0x120c0a300302030d050109230420030a2108180705040b181303030c0f0c02151c050a0e0102040503060610030e06130b07082a130b18040b0a 61
    0x140e503051261905a146004403001184018240344c00454094a00e42c809983d08401804103901454070740601c80f171505042d2000f0b080f01c09600c80da0014003400303022943c003a072005021201041103645500703410008105400c5a00c007200031002151035032150300b070360b0030500046003603162445007a8410396030b480da48507a50003242c032910310b031070300d0f0b0340b8990b140003070300e040300c004011a1400a10285218950071000c42c0480e141101a2003803911030740c90b000302c1207078030384803010b40c3c0e000c17602004030082c1c40c040c5c0000500e00c00c00140b00a010b846510310780725081d00c00c0204690a2400c040703410395010346280000d03a031040c04204480e1380e001450741e0f00003205403003c4808000c03101046010b08800c4085600382e00c00c80c401d1001c03084000d114160382038040d01c40002e4680b2807540c1140c0d144801d48034400d81c0c120f0082002e50001c0304d40c9844080f8400110f44074030b4101100c0400008100e80c0d482800800004110701034140c43c10202c2d02801e210403541005071a00200004041c1c42007030184 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 513650458 1250 513649208 513649289
    0x140306120106080f0703140c0d1e021507051219030b032e0b0f090109052701061809170f120f180705031b01020c120c0a 53
    0x20512a038080d4000c1d405000d529003030f1340304c41c210440c4e56550350b50180700c212185000d0b11804a0010b0303010a010388444c2008100000101c0340c0d40b138a010118801080800006004148100598540700307206210740049030074940b60416030800c00e080000c3c1d2082d01604410030014400150918411036001000c00c1c1000035952803a280403034540001800b1440008001440380380300c2c42c03c1503104c040c02c9003d550044c400c481c61082130101c10328854500c15084814038005025080072504004e030f00c0194645c1901aa44081403d03158203a01c10b00812800d9644180c14004424061140030b0041e0303041030103000000141e40e4482c0f082d2000000920140d502003500c45a41c4001c800712017100e040c040036159507041002c0c0358075a00704162900341c0c00340c540104a05004001003016000c9450043c040c081444403100c140300c0340d02c1c02800e00750450007000000d480030f5540110305400000aa40103060702c81002c414001c2440c0141c02c158210340d443d810b104000c01c001140d440083e48500304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 513651708 1250 513650458 513650479
    0x50306150f190b03040305040312110a08160c15030609110405010e0a0e0a0f1b120f020d090c05040c050301080c012114040c120b060402090609031207020907140306 72
    0x890b000360442500045204030b0004140018103034018060300643e800340760100007102902707409940c00d8005440070f182c503810040110300801c4203031001c0c003201200c202c060359010140d80d40782d607803c110f0303504612640100d11004010b502d42c14810314014140c4403100300700d44a1840803d452034026446141e0402c401c905807805941c9034502d00c04001c001e149607800741424032651003000341030707076500199000389400755145c401d06d07081c0c4151140a9032a100c1180c1c1d00c005c5607142000d410f00e6407802c42500e07020801c0381020400b903c40c00410900940d007401c2d01c00e0500c010081a5041c01c5c1080f810460240010b100700c0d1004142c0c0b10380300c0003d080c52910910081802c1e9915240002d00d0300c00e080c41c20302d510288011018090384030302d1150040e40c03592905c1b0350b0b804266040810000c1c20b4a82c50000140176402c10341d004021100000b404681864409000680fa20b4a038a01c10b41c211100070450b03d08608000313400540101003418034011400000070400014040206501d01c40c00031040e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 513652958 1250 513651708 513651739
    0x6090102030c0610030302010c08010302101d030d020105010e1b0307030203090a06020c06060f01090819210207030308060405060105090d020d0b130312113a06050306150f 75
    0x32508a542c80030b041c2c46407840c0c84a082001003035a88030590241d400c0c4000445e4040c4640d40303540c10380740e0007840308043c000705200172038031408011001c007441030110000b00816070342080501c0581360560300106040d8104520101c0314031001c2c02c4242c5480c010001c000400c0e804c64280c1fa4847d002d4500103851b5070b04d500250b881c001c0708942c05882e1a1000600c580072400101c2c0c02ca1043d00e05641100c1021240c000444894505104074120383d003044100b000a240d01c03620004106014100b140707405124030505a03079490003100e0303480c05a40103400820805400130201c81d88000200d508000c1481c0c10400170f8140c4c030448402c54403840c5549000c01c00c41d0b03508d06800d10303c1754005041c000c05180100142d5902c400c03800003a40886d200ca51045a1461240640003640000350601402c00e000c9006c1c815042c4841c2d450324806090380b010280600f4404a0800c502004840e0302285261505007410708061000e17103240c0c14800c80d00c025681641398612917800c0120251019051900c00d130 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 513654208 1250 513652958 513652963
    0x90906121b120f0201111f0b060702040c02160f0b031b070b090303330f030f0d0c14010b10050306030111070b060901120b24090a0609270206090102 65
    0x5811400140c0503025444082c05150b03c10586a24400c0c0c035a000c02c030710100400d40d500c02c03800b02124000c10505080400482c003503040949100400792103d400c00800b6400601504c4100047ca070040c0d1090034140400403180c010480240b0207654501300c01420001010400d100040c0404107503143d8840e00740e80244030fa000c6500c45a0401014612070810400c1f181e101d50040d54095410485200f03000c0c0611400d605029001003900c540005100c20310007440103038464400b50a516010310100c050345050709000f6215501d41c2c55990f080c107600d0700c0c584442e000c681c02c038084503107038500411030750692140d1860f0301925226041c42c0e5140d580d901c0c0001d0161900c0c14001400c800f010400a00300003070000700f039001e04411155001c8507a01e0b950180308491107a400030b4008c0090501003404507880b00c500364403d55075030004000803500c92010407003010040d00c14100140e9542c0d000c1120350380d54440c21589001c1d40c440c4008038291954000342c0010107060181c400d03840016041c1150303008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 513655458 1250 513654208 513654263
    0x5010606181a22030c05041107021e030313050a06050304050303060409021f210c020307030c0c030b01030f02090903040605090411090a0b03090705030106060503130501110c030a09090612 82
    0x103c01003480c3c00c0c80907600910102490300c01100c00113601c0340089100d02c3c0c076001d03126070050710410060501280c3d80800055551258004901000b1140446640e80b0b040c0000e10050305e04e8454400214580818400d00100380d80c00441085030134014840040e0010003280e030852822240450300c15101d000203442c0401000b04c08545420f160480914140c000c442d8028412104918610010003049290299466000303242d0040e0810481c29001134010406071030014002c60a14482039101d0703491400001c005e810035582c0b082c041d4407000031450300c054803580c0561400082d40c1001d14082018083e4000ca0808510076a00d0794481c040d203240b140e081c0d4051100080081105030364508c2011503d174810f4034241c0541c0207455002c501814140208412101541c0d5910b08e0b699402e084000b030741f440e03008125020b548484080250f06000c1c00a04520900540615980c140f40c18026120200b030340c3c4034171080d509110b0304200d141c0310442c40d00c0c06a41c0003500d40210a0000d42490521500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 513656708 1250 513655458 513655477
    0x30e030d2003090604030305030a02040f061215150f030e10090c0914040602030c0c0a03020f010b09010305060105062505011b0c0c03021c02130905010606181a 70
    0xd40e140501400d41d10504000500440d500015100d030312580c41c0035141c0c483e4040140d0460010802000080e2103480119401040d00c0c80c01030400c0e840c0c503141000d6241ea64481c0c0001160090300da0341d001072600c101c0844001c2c4140c29a07010b0b2800c4010519200c440a5007028004003400c80c3e800d0380e0003a0000f00b2000050010b80d41c44028007410740300280144507007642c0050342e0f5880403403462405e00c5800d40300c4000c030503a10150b43e00c0f6587c1d42c0c00380d840100041402c410034030801c81d009108128800c59548280c01401c064080540034500b120300c501c1245200b0803a0f880100003081c008507605040d5001a00c032544c0e01e0200486141100360b49274040c03880c00110b507056200380001035124030052110042d846000101c8140d040f0b803807480b6204050f1415100c04410401880c00411180c03070b045a92000c07080c101c01940001e20414420070b81901900c0c1c0390740221041000a02c01c400241100b03060040c4c0b40d0050141001b01900755000d019001004820f448000010f5001940d180c040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 513657958 1250 513656708 513656713
    0xf01082d0106081008060f0705040e0a060509060409020a032a06080a0606030501181a061308070803070b0c0a0201150303120c1b030e0f091014030309060d09030e03 72
    0x1040105204181400b4841c0320001180500400d074640349491295017110150401820552941009900c040e9005804c0c2c000b071041c20400083d40381c000c0403906200d80c40030400081e10b6454101840503428008003282d1003180750074284d80040c1d9a02c1c0c50a01980c5c0c10018401701e0710134051030910044610340126815150f40080091801c0d072148415110718001c9a05000407640e9081c02d4081e100203000b4160f034101414644401c0907955072003280e00800c03098800e0711040205010550662009030340317000d003500910b4240451041004260014a2580000c52a10720540c50b4505840b0000e001c2241107007000880c84a800d200750440c103401c0303100191003950766540303140142c8075030050f2100800090a049810301703004d004448034140480312080c0500c1091056030201c80030050350a070503a102041c0310301025580c95031002d03144211203d10340d5019850814030700d42c22000031040e0b0684258810490500d541d00d401d402d84100c031044175008140d03a0001d240545210002840c0140c062 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 513659208 1250 513657958 513658021
    0x61201150303030b0402090a0f03120f0e012105011401090e01060801030b04050a05010609050a05130b07050a110f031b0a20040e0d0203090a170303011a1303030507020a140f0108 78
    0x40b180307010750400f100d00c01cbc070b213100c00c40003074000a640c082c00900e20b003400b061040d1403a010b154007545541c40122030103d600a540e90600d070002c0200c840a8000d00c00460520384e48070590758103c09a00c0c0501101c90103c0119072601c03400502e1220140030091130f03150306001040403c40100314047d00c150f400002403205a0701c4140700b0005141c00c0360960a05800c200204d20300407291150400302d2074220384102600c1d60380700e034151140d50051a010f010000c10300c45041d500442030240517040c80117440a956a0ba000100228003020004103c1d4102e411465014001420540040942008190440322200c0701900054000e1500060094080c041c0303001022000e45e01000400f1082412600300d12100d03224000d41c4c070203100814411817036510400051244400005042001102d04404580303441d000b034074507001c08440355000300d0100304003044142c1180f4101980002030310f090300703a402e80303003240c580042c01c0800c0505038581448210004039828682101c500d0f58141010090403c44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 513660458 1250 513659208 513659219
    0x703140406020c0f0609030c060a0c021504051f05091302042102190303020a060902040b060f0a0806042309010f0222080604120e010e04050c03061201150303030b0402090a 75
    0x80e601200c001601c5091680f4143d5124a0b1a1083d101b61407405030003005480d448606020840e8030001152042c400707421040b1005039204000d801060075080303d01c030b03200c0349001d040c088184100c00c0c060b6210300886040c8240658880d00307603007924100f1621049908428480d8500030701c250b4100b85964030380340030300f0314130f007840e6031070b800c100387c1c401d66031581c99070f803010000359500d4007601004005230403000320b1101007820303500008131141c001000044d52030b0180300082e480d6807090003400303107001c40400c40c03240440d044800740c1e5104005481c140b000c1384280c000701c0b4a0322000d0107003821520356840410350f801d400b5070000c80b03070001c1110f0840d07030784002c11465160385180c0c5003052031030031030b542001c10800400b2034001d014941c44504600344024181042d500101c3d60380840d410002e0f050701014a07aa06d40c000c49025513030002c945541c90030315000740b00f000b243d00b1104600681c10701c0e200350f81d840d40f40088274040380d0b014a00082d0f42c90000340028041d205050459501c4000c1c001d020a1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 513661708 1250 513660458 513660463
    0x804030803180c0108010b090d0809120d03060905040f020409050c04021c0b0613051002151806060a05014409061b0405040e0a02280602070806010902070314040602 72
    0x12203442d1100b140d15990641004454a038003d0280008805040c801b10000341130100c96918450701c07070102e20381800c054401241602130780039580141ca41c0818810200250548102805002c552205100760300d89911019218203158400030300883e0740d1030280040c04820301c02c041800070001c0095503180800e50b003007c8508918048441b203189011113100b10352030140204c983c5d5211501440f103501d4070b03007010040c3e91201200d405046d4020901c2141c21071034052a8140700305d01401d0080b4442e40849026494204020a1b040c0141c4080c4030502c00c613038102514001008107810080014032940b52641440341540c0d0134607451244021880040003817182019108a16400880701265200420000c1e00110310942d04c0710084100400c1c000c40c1007640100444422507002c880034000f085e804141c80b055142206c0d020698524100c0c140d403200c5041f400014084c038402030510358140004c4680f0350a061207620324041d40003c26000300342c001c110080040d000c4515903a00c0c1c82d0740d854041d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 513662958 1250 513661708 513661741
    0x2a06050f0d0c120c110703060e120f04090f0902130209120a081801090f1401090308031302030c04141815070302090306070921030e031f0b12060c070804030803 70
    0x10312060410f984502c1d1507100785d010410502204009091251464039021f0060003150380c14080c1d40281c140d94001a0b1f40701006041d20800f004405a403140741481e2001210b5800140f1660103083c075070b41e04056503071f2210618400e2444000117a0710341002c4005080010040d204403480d000e41c0302c2c15420300c103403440545840040300c1e0900440301c0b104801190039420034080d1001d424a003440c180300401100714004c03100c29040c101302c40c0c5142c9030307107801045800480c1e19000303a00039902100304504060140e034005e081e05503014010403411440c0d02140020061420607040e403040b41c624401081000302c1c04054030008900403690510382e0008001c1d611256800c3c0c001e200715408550080e101c0c01c000400c903003040c000e1092200e144615030002048245040c2c08001603048646056030701403040c01305030041d6503a44003181c03100c22082000e9a4400300180c1c42160b5461511a001e103022403959440104440850b59500083c54680f041e4088e0741c00c0074000d4007000c020030900110103110276 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 513664208 1250 513662958 513662987
    0x1d242d120f180a031701050108010506040b0f0f0403211817030d020f130e04020d0b0a27060b0d050a12020f06010906031a07050423040c08042a06050f0d0c 68
    0x175409a883d0b20056442030801e00c21582c2002d01080100003600c80200030b01403d409158200789050300e080c102010540264001b683c1c20304480d000b0b40314844c0d41c0b40d0800590541804c0604c1d0700c0d918881c0080d01c01304070380310750018460011015040108184102c40320040303c54021504c1d4500c95010344510f4001d000a4002e00d00c0348280400c00c036001d40e1840d44601ea0050424a00e150b0fa40e80e40521108003401d00007516445a10311485214064041041c100700c41c030070142021858100a0242d41d20f142e0100d0203008030840c240301040c0085090100300f038000c01c0495050180c0d620480c80c1444e80006c00c1c006004100c00402c40d04504d800c504100c0f8010f001030301030158030340c445a50510040d215400819410407082014801d00c814915082500034010b00820000d40007080c103682181c02180d0001394401e081004020b840d40c020461034042401441000030b4191940ca642c042600841c1c0c00e001c40031a801c0c2c0b40016841c00c80303020318040b05040c001140c0410f0f026110f032172080c086 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 513665458 1250 513664208 513664247
    0x10204090e0709090206071101031d010509070f0815040f1704030209070e030d0f0c0503040312140c0307020f04020d0f050411011d242d120f180a03 65
    0x6400f000a00030003a84580042a040c45c02596940b1044003020400105042c10349910740d00380d501c00503901c3e1021703404d003201c004140c40c0741c6070b10600e04010f0507420400791062408001e00c0000d070002003c9071107503542c4091081c030740c40754200b2110002c1140c000402d05034181904c505009550307070207403048034808d6580036529112018255050203001368015090f612802c2c1c0c442c8580d109800300c040e0100c1d5402e0090800889481d41c50566000d50401d580c0400700c00800e0f48141c3e401004030740c040c10f00d4018142401070001d0034a8892040d503902030b00c15410900a400c1c142d4856048850110310b5000030460b480e9203443c2d4402414003180c05441e10785c002d40030300e0015400b035855070781d40b004048241094452128100010250103407550000c511003100071004030720b00040103000c230200f0760950403031801910f0180300810780303007162040d0000030500c03400141083c14070401e50061365801c4010308554500c1c042e20000849a0726000040c895016480e0030b040d00305c0c0c807005a828030442c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 513666708 1250 513665458 513665473
    0x21180d08072f0405100909030302031b0406140d0f0f09020f0613090e0a060513120309080d0b15360a06080c16080309010c02071a160203010204090e 65
    0x5150403124400c0c8080c07962010044541021890f095009030b6104600210300c805291300d56015000701e65049108070301013030b400801d005010a0b0307000b5601e07109904540c0d052a00781400c000400c4030840c1d640f500c1d029400498420071403051604040d40050b4800c6c020001042a4652a4064441000c2c16070080000d001d14130480e0400a080703c252941d02c100c0d52001c185005400c00003000000d400c54034a0007403220190004243e400707564054002e200740035078600044c0c2001b1643c0954540402c0a1614103035001001440e840c0a8402c3c100205000244402004001c5031031400b55030003640030041c0024807802c1d10741c0320104198008a0700854041030f0b0200c0c050940f0340700300d00545a980254003010401c0b001c0c3c41032000ca50b11200c02a0301c2030810064000090318098906000c4a81e8a404000c00005117000d114a5404000c076200402180d45020b020341d1091740450b149a8800c0c03000209030807060000d20307050408640c003400031580c9507601c0c9800340007032602d0940c540041c0a03160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 513667958 1250 513666708 513666743
    0xf0c051617070302060417070b0c0d02150f04030c0222050106030b0103020708030a0c0504030c090209010e03010c090b0a050c071e06020d0801051e041b02010e21180d0807 75
    0xd1040b06032030340078201d00d240c581414000c088500ea995008606440b400d2000301c2c0040d03d4501816000c80002d005000015180750060b0500710300951036515007994604201005554050b6580c010f80c060038826400000e07400400e0021400354240750407140100c00c43e003e0990f181d40647c1c101c07200e0b50b608001301310012004409a101e40e00c2c002e0555801400441d0580520742e0040c6407185050030100d180c03c0e5a5541d2900003050780d40301001c4158046020446560007101c40318401170110001c0000210000740902901c0640c00b074078602200102c4c194125900400c12968801c250308215483c459549490200d54050300e00c04101e10444880c001521a00000c0d4030802500c0c0b548680403560b081c070b03050100e80340e802c584080103040d9001e101480c0d40c0721031040040d550f132080f86150f0402503e2a0207030a4828081d100a0554410b50440310b8101240301c414081e2541902c103145c0c1c0d0901045c03042040b681c200310310760740800721031a04001c1191810050a9451046d0301c150310f2a622170 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 513669064 1106 513667958 513667963
    0x100512030309010510291b1e1203160507140d0315060203160f06050907170c06041701090510020d0b100f0f0c051617 52
    0x9102d0321030303401e0040300d0f4060380704071031180c00328078210582d00e00721100340e444e070060311050f612485a00000c804581e003000202060008811004400d66218034240303c40c070900c20800c40340c8403d10b080101d0348440f11298048590b0440d5500b16800f07070600150f00712041002010401d4500240030564000d0340300074000010000c24440000180403200601d22500030b10b00c0d22a420447c5c03590000c1229401c00c1d1605100c4502411450310091540300e00c1c0740100b5890401e010400252000240d00c801c4565401e00000c901c0c40031581641c60b202c3c440280d6401080410061210306204000010b90701000b10000492a5468441030300f03003020b40e030700c090013980c000a0605d8a4480c0340185450804100d40040c1d0b400010b90010f4440e000c200d5042050100031035000784010b0180c40421042c81d0800113690350800d00291308245145103000e0702c40c071301290482101291100 = true := by decide +kernel

theorem cover : BRFrame.Cov 513489208 513669064 := by
  have h0 := BRFrame.cov_init 513489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 513489208 ≤ n) (h2 : n < 513669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
