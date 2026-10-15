-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5200
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:04:39.332039+00:00
-- url     : https://prove2.me/submissions/eba9eee4-12de-41bf-a0a8-cc654b08f863

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 935071942 ≤ n < 935251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 935073192 1250 935071942 935071957
    0x90605150f0d02010c080f0306090c0406020a03080c0c01061d0601050309150c070c06021c143702280f0303020a0905030609030c0705040b06070b070e090a050901150605040b 76
    0x50105d4034101094001c000313442e4011880070055a40c6c5000c0040044034900140101c1408a0610081c000c0030703800185400c400c0c4e49418802d505444a507080e00740e500446034848195030070f01d00d002c03604800980d07a502a0201c0c80500586a488100040d00c0d540001c81e0a10045e601106c11040b4005140e0030040c2c10400d699101031a0140c16100c0381e140c8072050700001c0169205c00d400702c0c1d6150020408070260036035032910002c44000000f038200b180c81000500608a142d0130340d40c0b070f000214940040c0380300030144800d440704600b114003c0c0d01c2d9001000c2110b07110518041e0207454846009400407816840354030701c106145282c0d0300394003d4100c0c1c1d10355001c020302c40301d001c0389684041140d14000c9400100540c5c8030440d20400c203280c42c4082d040075014a042c28000e030000e8a40000382e0b90041d07400101d19a0b581c1e00c1403c00c803a803900c0070034803030340c8018014284986529140d00440c000c0e61004002c0c42007803110041c4420084840c030507040011810041000a000f04101030902c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 935074442 1250 935073192 935073197
    0xa0602130e0c390a1101020610030b0a0903030e03040303030b0114040e0f130b09070f0b130909030507050a1a07020118080a03060f0f0603180f150207060f090605150f0d0201 76
    0x41403012110f840c6403094050742114002000d400d044055078040100740c4e0300c0425211800c41003410741c1e40f030f0a80410040c00c0c07182d0031038490104408040c040e8101c3d8458492041c00c0301d8446659007402005040f40c900c00601041103041d80d142e4a958041c1180c0940f1103034401300c0d02d9900c8042c071040c80c4000c006d00c0e0b848190440c032504c1d4000340d0702e24050350080032074000810840b828841042100d44160384001103001081080c2140007102002010454450003400500710f910303810151303000c0c4a20140103000340680f080301e0042042d03409074481000c0304101242c4050f65511016803ca40742d500b0400401159007148100152543c001880a07400502d030108900b9540c03c0c080340c1d003502980101003607520ba844140001540742c40303994480307100e481660104040c141c80b8009410715038440a0401a29866070382c1d03590310280c04803240340c4c5d840340040125002d4402030b44004c1c100803508542c001e0400c0b012840300d0851580c84c500381400109a0055034011b14100051110005000c178103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 935075692 1250 935074442 935074537
    0x20616020d05060601080705040501272115111e091309021c031b030509100c05010b040203150d0f021801090615140c0a0602130e0c 58
    0x584400100c151881e104078010f00030350901030009408000010a58805c0201c140010000341ea403000070500c6c0c40503895802080c041940300301c1c0e00c0590082e00084007299603158a03100081c9682901807200707020750f941b00d1280c6c560030800740503505040a0008504018403c2c00d0f440901800400344034030f40c01c0140c0740340650380c401007010712000c01100410140d41c1c1401005600f0300c484412000005044142c00391180c903900986492903418501c15900100c10044d41098007820860302c02d0200241402480c81d120b5100078000282503038100c40070350070a040745c1d504e41420b0003968060303410444100c40381f001fa501484800000458103440c0f41980384141070143c0c641030f400880c103c182040c44e109560410081c034055035a2036000d04800042480f0704190968861032200c000540c4e51041a519441d02c40000d01d40480d000000d00014070012341e04460000c00c1c0007400485524241d15041ca17990500008440c0c05404c0000b0b220041c20035800004200706001c1001e40b0200301032081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 935076942 1250 935075692 935075737
    0xc1701090204110d18081b0115030c0501030e010e122d040e1003150506041d0303011806080c0111190b0f15010c02010f050d021206040612030c0206 65
    0xd0940d900c9403d0030002040001d0311600c44181da0161036202688250410340d4400c983c0da802d500e80c4241c1c0c4145d684440348640c0b5403031100d420f41100f005000300501e44d14160391681012000070203540715180c042460100000705044042c0992240b80d5000c202414400c2120b00c1070035840e90011a0404401940340c40002000142c2c51400184000380c04d00951075900789080b00400800245c5110981601010100006690421101c504460014001c201501d6040126010b0001d40744001220000710103410741513030b40000031714120340f007000c020075a0f0a80003030490300b00c994178010106981c000000000041d4050011030b2085c04400c01219078000710514048a01d210b07851048405000420070b00c0007142c1020006a04040c948480b840ea144603040040c00c0c413154004000d043c401e000300380c0d2350f500b4080c00660380780c0716080b00155034031011002000104403045980c2e03881149402c50200752802998503840ca40e55140d2070f54002e6801d9502000f0040d04003041250710410901640c0d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 935078192 1250 935076942 935076949
    0xc11040f0608031e070803010618030819030b04090b18030c030703050919050105030f180d120509160303080a061805060a05040509120708090907090e070801030c17010902 75
    0x20082401c0320180d41c4540c05280c907200d1100d10407401e10f13440d1105001c0320010440c0c9004036411140355090003003002485002c803100b2042c080e8005003001a000c81c8008508a24180302c0e6501c1c00ea59604100c541c002c5000c1004072100060f02802c5003c8840005204400c0c1c03c181d8030a80c09404212030a01900b0b80d500d41c91a1b001c404214000303071020545040b903082084d40f4640f074001680451702d64905000000b0b04500009001c0c00c504682036000c207541004540000c0f01811080098a284407803680c0003510715181e420b04e51000070320308000600881d0303000c980c0380d601c60700c0c00c51480a8030b4659242120300f00e001900f035860b4255a01000a684480580107045c01c4189200100d400d15080007000100311841d0b0005019902701000c0043c0c034480070800044000280080d26251402070415241170f016002c0d400d900000341c8814000360a03000941d0f58100c4001c80c4001e10142e9803c44121384c01003081c48020461082c00e60240804c210400b4400c2e02206000c000143c4e42d1583d4000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 935079442 1250 935078192 935078201
    0x10905010c0c0b0f0f04030c0f050d030b03120702010818122107020d09120c0f0801051b0702061e070b0c09030c010201020f090108100e0a020306010e030d0c11040f 72
    0x1220101d0480e4060310b0800000c0354220b50b02c2640c410300410245480c1c0520200202c000b00010104200d905c000350070840c800d540c000c410303038103d01190042c0c1c52881d8060002c080c03d8218a11910645007000301c191208406c8824069042e521400543c40d41140440c03801b044299000c1903000b0500642e500640b40c5d009041881c2c01811207180c1e69243c8210104e03a0240a0015070864000754600e01c50345401c9012003044030700c0180b60110360780b45414040724042c6c094000881020000d0000280c11805400041c05007601c03d00309416407041c802c01000a208a1100a401040c00d01115541206007084039002d46400b080380e82c9800081c1c1c0d0b80b0306141800720307440c01800402007030440304d5050400801c1811b000a000071840d0001820681a4034050072090768100901d0320001100403403140d001c000108040381d01955682040c41303005000c0c1d001101e41038001511380041d025a0300d80000c1c2d0130000001c6032280d031202c0d401c41c1c1b5030384e010100078035120342c00640702c0805c5110036089118 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 935080692 1250 935079442 935079461
    0x20c031c091110200f01060803120906040b0a0b06073924020c10050717030609060d0524041b03080301181503030513050405011a0c01090501 62
    0x180041c00540c03915048201414078841c29000b0b4032a0008a0440c0e600700c000e14040fa6a04102a1848403140ea015442d0001e0708038845402d508003034000890783c1000001c5c00d41e05009a0000c00d4030b568883c0e9455a40720700300c4010380300c0390f200c50101d044000e0642c400707011410003626042c5003d1a03611000c8207000c00d0340301e044058800301440700c42292188410203200d001480240b0140e450007003418000c001c0350038840c2104032641101082c441c020420500012000341c4041c6402140700c01c040c1c0203800c128005d0340c01040d0080f10845800842c000c03a489400001c0c00c000f100e8860509110003d60025411246803050203004950600d00c071f840740450706030390300b0580703014945032609010602e208000e0458000301c8036400d00000d034500b0180c03819542c038840081e009510b8809035a0181031204805400020581c0010040c10381c407200402c1850b6000070010b25140c1e0300c0047c401150301c00d00c03c400b8414811500c1c0c20403a203000c402041080300c02c0e00041103c0c6816126242190003145 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 935081942 1250 935080692 935080747
    0x1020d0612060501170c13140108071d100909170d06140303090a0501081302060301090c02010506011106070f0c0212010501031a0907060e18100f050402070c0504020c03 74
    0x70250402c0080c20300485015100700b0b02c04105c104030011003283d03902c1826100364401d0030041e00c0350f01e03616410751105454003015070800103d942d5031400b040c3c680d0f98034016100c6090b00101c4002d004144038211901501241c121440d03007903d4000080b00420708160122071002000b41000440100440540350f400d29041c2c00040c081d02e0302d02d556901e4110707c2c0a03a8080e0700180700100c000d6940613041d608444080c06d118405954030b6010648020004c2802940404088004500160b595000a0382c22026030002c111a881e90001518a11b00d10009034140e0780c08080007581c0c035403140207018100080341c201a5024040c0f540025001800b0b000a0040c40e90742e8401002440313141000b41c2c01c0d2100c5920f08095500300790800316240c0002d4000c42080c003110f0030021180d03440d00c0700340c000042141d01c91150030342040c40340c0384040003d40c0300340d144102c0b03181070200d180d1509200f2105030551021120300301624282c00e010294101b10401c0c0c415010a000c40e07001310b403c1c40b20004a44041e107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 935083192 1250 935081942 935081969
    0x9010611151f0504050112020f120a0803040204051305072702070503130e0c030f061c11010801050618090406090b0406050601170606091224091209030a1401020d06 72
    0x801440b000d000b81d50b40030038801c6040000400082080741c000165064060340c8565020724000085881c40880e0440c05e0282d2040104900c140308801e0091800b842c82203034140700e00c1d1034a4a0460401b0081c01c070250664001c03c07002c002d07040c20503550000c400501e401840040800c40417a104980140038243e070349410010b02056044121071b010005408a0150f0040d542025046009940001000711125404030342c041400c0341d4408404101000000014051480491a15698101800e144103001c00c03022b03070010a1703a152040075204000b441580c2e442f285480541004003607240a04282c858543e1041002d002c103806103031003880b681c004d0700d011a15041840005041e4161104602d210840030b80600c895030b940c1030205c500d101011501611408100c1c010b117400e0072401312041046070035400039640d01c001c9000c50544140d50040aa40000701c9005884242e4860424101ea054200e100f00200250701c0e8a0b09a5030107040500050403c50b4129400c41103400b140c00c00071510960 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 935084442 1250 935083192 935083231
    0x106050a090e01050f01080319090902070f030e06091c2a081c080a0f06081b03190b0103240f0615090e0601120f020a050a0f0e0901061115 61
    0xd0041d030b074112503503030305c500d1a0350300d0880b07010b031a07016452a5000394940b07140864503041c4101801805880405400c643c1c03003400d840d00074401c6070085000c80110340e00380340c11201481d2480c20703640d070043c000d810480d8400d83c014003040e02c1c0c98040400c07517000300c22101c40c41400100581e8010720840100300c0c0c110550804203440d140007120484d40c50300c16008420f24600d60762096003950040c484607004a41e4007641010080a01000e400c103100c144142e66224041c902000b15a01401c00144c090302d001240d999900e6610030000b69024040d0358030b40004000082000e03522040808808100307200f500b03016500350041d41c7d120040c4000c0707181c90f88024049901c161101c000400714a0402354941d03803801c0317000e0422000c000c2c01607060007040080d00c2284103246d00035a80c41c1200380411562864171000c041d202d07030800104000050588413406500a002d21080c1c0c00080c40208404a9a0b10b4000304948448503013007000720501560660f0100321320800c0c4c0e058011840d070300e10001520107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 935085692 1250 935084442 935084471
    0x203040b18060c0a1409151c140112031101020301120c05100e1905220605190b03040303060509091005090c0a03060b01020102090915031c0f03050601020106050a09 72
    0x860302081001ca0b009141481940315800c001c441ca0300600b8249102c0c0c0703008092001d400307409003110320303070b0025130f4180c00070303a884000001807032800901c940142c5600c10740c4d80c540781103ca42222200350704403c0b400600140e034400089292035803080c603040f00030280611006080ea0001e074400491190121040000c00c206400050054542681c40c021020000c0800500e8440c0403841e10b40980720901c80b42050403070018a02c40070381400740c402d002100c80e01001214000c409042005801c1c604400440c546c07500240170000d01d20341542d801c540303e04104600e6001c6c2d002620032410f140d52707402c0c00100d503120b0303180d441e00c50303140c19015180340444075050205030340e0001c12444c4a900100008103036550703522007003002d07070381c11260000d900d80901006034024420101d10641c00f841c00004c11005c090316005ca07060354034056041d961003008076140a450804000c641801007504040d100111a20036030016a0100701480041401a13480740804c18010803600702407003460300c6055010700d603070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 935086942 1250 935085692 935085721
    0x31e0a03020111210601050c2b031503060203070509090a2a0215040c03061d120406050a120605040c020f07150c08070804050402040b09040e0109020105041a0d0203040b 74
    0x4000742d07091340350001c0c0c0144400c680ca02d84d000c9806801c0300c4008503419034858000d4a822501800c02c0b500211034190706c803008282d90540342021020680000098a8480d002d406510070407c040c1142042c2165560000b81d00000c141c9001c00c041405003080c0c075076605900c680284080c61000946006c4d2210317841481c5070020285101103291a41c500003a94002054082c0440003a0400450b0700d0780d2038001e01c44600ae900251800e410054413480180c40c40100340d4080064000f140e0741d43c542d00701284d14a0140f8899100800e00901013400c1044c00781d20036048050400b100022020744550000701140c4100304100f005a00a50f80b131105080100700340f5000d8200d0f940c00d20301904400f00c0003010711103400d80c020400c841c046004402c218110041d1009072000500a545494641c007150320640c2005403240c0c400d03410b100a80d0b200341018814030420780d406a44842c03801c1e04103032100d041c41c6060100c50ba030594041100d80b404204138400b440c0154410701c2d2461050401c00200900744 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 935088192 1250 935086942 935086961
    0x30b0105030d1d1e041518061401030203060102030c0a050309011103071725080d11090907050c120f040305010c0f12150e0f040302010f0b0a050f031e0a030201 70
    0xc00803421490380202041040c40403824120703940c0400140c110030320300307620072101c00c00d981246c02c0c5180320720010312598001c3d059034128408050035001000098080e00c51912070401c0201d000c40c41032800754429001554002010f0049a03d020715182e4070503d00702030000140d03055080402c0d07050700b0750b034041110103500070070304011410300c4103540780d04200d5036109a1040c16881c001070207804260040c6040040d84011400d004403e0b60b00e8180240d15900c80010918050701d001111110040300310240c90203210080d05841c256511071905903119070002c010100a40300f42c20710351704c54203031050003441d0034204041c0c000d407a00d1031441e015080d00d070214040c030b00303008500780d0a480712640545c00b804005409480031444008801d09a03a1101003a04442c2d00c00a000302001540254000f080d406248664000c20403102090110300845000c92043d5600c0703030241004005514059a048a615030000c0c1503031060410030700c0114100c0700040d1550b1507904009141d030700781602842030040c038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 935089442 1250 935088192 935088197
    0x10f091a09160e2716090b130203040c0b0307050a0806090f1b040b1c0e01020f0a0c02040b18091501050f01030e07210b070813060e0109060c031409030c03030f0a02090a030b0105030d 80
    0x80403501c87c00030755580a14840e05890300e038013000080c2484900d0000b940103000015040c1c0d964204204020a903611010203d00818840c50204490341890700b15240304042034290345950f9103651000403403409912039000d0a0704c00c1440007050441c04100141541440640038020b64010729500e4000d4810260b120040790344107211201c09120075000700c5500c11a00d00c0d100100700721030700c001001803004010954100700c500c001480380f460b80d1040c1310b029908080464510440070340464000c41800d014580d0818a1496034403041d5000e60462038641401a041c0ca10b200e458030400d03040302841c008919802003405c0010030600c041e140606400c50000c4c54840e40c14a08605c1c5040d900c080d10000170111640d50352001500305c800c2d0702c1940b915038440340c18402021303521030040140403490032440c2c030165614081401039500000305c800b101a00d1010b1070540e61110a1140040402072150815540070000c800643d665070f943e01e805548640e000340200e505000c00e0524054100c3c10320403d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 935090692 1250 935089442 935089451
    0x1005032b05130f090501140a08030a05160b07020312160f140d09030302090a090b03061f1a040609170c1002010f091a09160e271609 58
    0x111404480d80c400450450401c40d075100910001001c055400d68420344400c00329900204020869422260484885010190408511208000800000388a511415401084524100fa000c0c001800000844280505908680c1d494540c406502100c09a0041c2c00c0010840d680f280065100c40e000342400e9400e9046008201c8050070f03a1110084d00750512034003560b00300202c2c0da203030100c803452644130310240100c0c00c6914000c0c002c0c1d08607014251240707010f0403020500c0740d40391082120700300d00100241020745030843d00340c2ca0500d0003510320015041400c3d01080f500c00c64a00104200d105031411540c6925040006140f609181c1051905000094003c1d0040f580003508034413200c000c884103003101d00c1c40e5405900501409400c29040c9007480c50321000d0000c42e400c0e0314001024440c0d042035236990030f1016074486c0c1e43c0e10316901014820040600002c901140c149070711a598151415481d25214500420715140343e80c09202d07544003400003a481640b0001650091220340c03410302 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 935091942 1250 935090692 935090743
    0xd0c031b02070303200d200309060d0b04230604050709060215150a0902040e01140108040f02010c1403130b040b0a350405010b060304080313031205100503 68
    0x9448103181d110240401199411030041042100e05c1819801403003022940d61006480b80070702040c08140c81c54219402c2c0b1343c0814259007021007142c0c0422401482c281c80c045140340d907500180b00b0581000d801a546201c20201c006a1403400a84006403450226940c5402c1041005461000304840104207944804000481d00021411500380c41d03401c0c200e0460fa103111045591002c0f0700840ca511089214000442d81490360041003654405e214090301c030b070389400071180255010000c1d103000410f032400040c003140c45400140d414500c1403400d4403205174583c54041103000300030f0b4403156941000070100c0003803d101c8203030f40040c02403e1420307040503d0000014540c0c042c01c20f0300d00c10f1081207680340741040c140e0b40c0030b007200d0b1031010a046030354014040748100d852000c0320200e0340c42d8a0300742440040d15115040d00e00c038552090805207140d42d04039100080c00708904044007400ba0542c41e030b4401c850720703020741882025030780d00b40341d02c1c0c91901d0109858020250f02c0c03035102012100d0802c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 935093192 1250 935091942 935091947
    0x6121b1e030331031a0a0906050709060311310509010b120a0b101b0b011517150616061e0c17010905060d05010c090f080115060e0d080d0c031b 63
    0x402d900c1450171002d400390f0760b41c1414030b809070900301c800519191a040030000803d8000c54420b0644401e44e0341046070340307580800f070085e510070038a00e41c621390398109680c0d03003400481c031202c000c5511014030030402c59030396004201d000000303800c00c0101810210300e000701000604a059070140c0e1801c0e051040d40e42c0040401d200e44800c82100c1c080001200c4905002c11400c811b8071100b5a004054107103540e9200c0740a00320600e01410000000c00444400c0c00901d4005c00560191651194403c003804000702000780c25031180c15070403040100b0310448008035103075104000140e560750700b0072580b502801c08050101e951920110b0300741301b0500d0408400608010000b03054035610100003074291222030011b0b04440807001c00605c039600309035221075080e51080100046801c07440c2c2004005454a104a00b66220034035007000000402c0400c10a040c412003c003a000c050141100b0111540c9031030380002c0794400c2d102c030000703142c40d403401d000c010b0390620a05000007105600d80182d9200742000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 935094442 1250 935093192 935093213
    0x90603121d120c030609010b040c0c080d0f06090f27030c0b101a040f050f0306070e04020c12070209070504050603070302030a0216050606121b1e03033103 68
    0x1d01d004022599207012544410450422a00c4004040700c001d441c00d64030b0980030f0182619414003580c142400d2203590760060000707500f003d5001c1c2c040d41c10540004140e80050080302d1002841945800c40025106010b22890050b00e119030400716640c0c422440b41130078440d0a944a0b02038003403040c1071a003c030794820303107100b440c41e40044031600c503840d00c0321040251a1107030894000d03404501030f40c05840e28201c00801c121507458020000e0182d80783c0c10800070700d44400d00c03e078041c0c002d54002040b042c03140c5807a4440d100e00800060800e0204103d407440c4c8411214903000b120400103024055281092406034006200d1070101d02d030a0511000c95964000036025205140d00440440c1404c0c001e601562002203001c03c000041c840f0700e050a541c0d49905135030350f50060503a0543c084e404100071aa266056018403611440881610144180d142d0301480e154a000c42c0d40a02e5486e0341d6003480101500034010b02240c1d0720003009499000c180c0e031a051201c511420182c0104005141c503102e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 935095692 1250 935094442 935094497
    0x10b07110d0221070501050405151e03070c03030f021603050a0c0b040b0a0f0902061935070509090106030b010e040504030f1106130209090307080409060312 69
    0x148402810100105401e220601e800950040c80a19080c0aa046506088028420140440e0300495aa4005480600c114000e054101451441d140e15108030a0010801500c0b02d0000d03131100c80d02800c000c0c0550b0001d0b0390070000120281320aa0505905018511003180c071500c045240c4800c02d40b098210300301d00c01004040c00004103050001c240150100b2400c03d0b0040c00c48400d5140500e4858031201d022641806040e14007140c91800700070521402071566405480b4600d00202d444090690b41c5020070a882045814010b486010780e0550110030308800055807641026100d0202020031140200341c00704000c07090208419590b283c9002904452280c2000114202c1140040341c1101c0f200c25090f400c54101020703c802c05901c4040e01c1c0c540206075442c82411020402110703200c030015541000003c0b4012039500244c0343c51014681c00c0146130007203901e000d80ca40d40b288d00640081d0b01018586640c1c031020400d00816483d6000703440c01314642480c644410a41500c0000102d44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 935096942 1250 935095692 935095703
    0x2060c03010e1b041202040f0903090e0630010b030609210c16260a120c051c122703023d020702090f0712050405150708010b07 56
    0x100380165100c07181c003085a0800d203100f1340c0d100d869952003405145442400c174040d40ca040405826101140b0506040c0d90b41542c0c0d4520030f43c07402480c40e003102c4001d0481a840400c8100c0c0404041050506107407d03904240710010682007002e6003401c43e0203a01407a40039803c0301003013211219000c00c48425038500000710410300e14005202c0041c40c090040c1c2c0214070b101e40da03444500b420b0078616070011a0390300c0020380310190941e030654405d03284981503404280c1c84131112000260200c00e100d041824281342030080b010380ea44171546080074060300014a650b07a88180ba14860b80419424100d02e8145400c4c094141d207081c00e901d030310301c0480c01d000300c00c64101c00d40020144288040d00305490070414158a40d49410034481c918015501480b07407101c504452041048514001c1d16071480e0000c081d41016900c10000a03104079000305000c040089104443c800e000c518855580a50b0180d0020603001040895114000c20040c0279074091002c42ca0040011891a1040391102580302 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 935098192 1250 935096942 935096969
    0x7050604180e01110f07050d050a091a091c1106190e030a0c0f0501091706071b05030301150206060102061015020a06050705031e0c0d05041b17070602060c0301 70
    0x2041d20074010441030684c0070110f88005018003030300741c9071000340c07005a001e8816110301d001c1d1160162228810002880040f9405100c200810f105551100e481000311082541c6423845800004208c00f0742400f100b52800001041030b01032020040340c101154605480852905180105000b04c4081c0e040d512800c115000000307116a49041c441002e200d90f000491089050b1108a484201502d50080724002a5006000100c60f080c014a10781411040409000d041d202c0503011140d100e554540c850010883c166a800003036800c00095000300454400c41302c8a0418a80c02403c001c07025080504551058040c058460725444c1000c080345d002200c226901c0c140c10724140d09080c013030400640700520b48402c118240e038020008501c030700302d50402c48442e0241002d0b401400700c82038581c01481c5c842400441b0341c604003a4440754015000740d070100d00c5041b4018001040380180d03000f2208403c05000455115041041403c010b004039001402161034a0030400e1241c5c041446030080d00b03100c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 935099442 1250 935098192 935098211
    0x30a1b05010f0f020d0b01080f0408030c040305030705030702040501091b0e04150f06020c01020a0308011e080a2607110603061801030507230108070f1e08090705060418 74
    0x354000010500e40d1041800f81600d00720502c40203400400210544600b40a0141d40179841101d58622419803850800c4041d00c1c0c549075a20030f508010210340107540108004000700306c0c10005414a00d00c15002150795030614414841a0313075042c0c0c0700d03022041c145402c111001c0c2c0d8040780780404448030701d0140166580c020006014000b03080003d141d074002ca01c80410200d0300041340300c003503c0003038003194481c44410f0300481e9951080b40000c2c00245550700188000e0462a042c00006428505ca14803c952101e21080c144206d4040c22079032250092611440e14480e004c1448904500406250900040c0d8035000d14407400f109005210701c5000001514903941c2d01c01d1810a0a5080c61030105982c43e460101e0b0360340024041e0385845200c16410543c085840902040c42e040e041e0741d1140d05445038201511003a807510794240520150807055446c03040c04c8071240b000710b0b90380d0340d130110242065070140c0c1c18001c030383d00400c0c001d5108000c240141d81d0011300c0040e1540f035245000500091 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 935100692 1250 935099442 935099453
    0x150e0c01090311040e101409011109060301060c030c080408011a0609010c060f02040e07080a1b200a050f0a0201030b060f12041b03080a0809010506150c0f01060f0e0108030a1b 77
    0x4622680c810301e01d19082007c40728a20810180f4070591900000b008441c1e403103262480a40500f180d12176100e2020401802114401c00d0102039003486400c12481c00007840e540c40b01c1c80d41080e04051884e0799955415504040b03000c210b242001e0003940e03420304c0c101d0f04900091280412131009003082e40c0300c033b00ca141042083d9045500800020074010403d0400c41002002c2e0801030f2102c000d002e081483d4495800d1004400f00401400c84d103d4040302c14015081c080c0042d0b1000021a1038010f41c602000030440a208903035001c4000c0d00a000e403920307103100240895031081711242c020344007403090740c040b032000004a80b03008100f0a0300d0701d07865960345800743c2540002c4400c40103a04c2038140000c1001421405400d14034026201e0121903902d501000c1e00301d64080310305551010301c1d880c050600405400060010078208029603500051003035a6600f95401c40c1e008038503152014100b04800d20003540301e540507010b228083c5180c403030140c00c01000c504e010448031041d6000310300003d08200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 935101942 1250 935100692 935100703
    0x304031d130e191a0a02210901021c0506011403011412070314060105090c090f0103020f12011401093c120b0f060406030515070c150e0c01090311040e 66
    0x84400d20300300b50701d8010301d48410180c0c50316404003c68544040404d80000250017551f142e0440c4011059005405040f1030030204005414481c80303544c00c025000021400782c3d5901d040c1e0001e040301040c1420a100018441160100c40c9071040c2d03c14001448445200e4400c0c14419408803280d84512138001d0000c2c1c02c242c51540000d1030b151030f07146510b07001035000c98610b048580480750a900c0e030b9144030458005210300381495a1090050301d01e0000c41d170082c1d003e0908640f000030a281480407051035901100c0080e00700e408451482c8000130965a441094640580380c01814905441d59200c50302c3c8480403000000841e200010840840d0012002d0742100200059010501c440d1136a040000c04200140d0768078411310354010004259060602546c0100e0380d10000414640020f401c1840052401070410b070200665425441c01248a40c1000e030b044c80c1044900151101e0510f0349540b801d103081e2034241c1840100301c2c0800104455407809840040241c8020075503c00c520301240c01c25 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 935103192 1250 935101942 935101963
    0x3040b19150314120d0e190203100c030216080408010b040b0a03080a2f010c0306150507020a0e09060901050a0902060301091d1c090905040c17030d0f020304031d130e 73
    0x30003103034250b0381840310382140003920141c0d001e54a03070000d8400207c0ca0b12075006000b0707415502441801a070340d038255105029405003890010f05011380190700c840a4801d00c0400c3d40e070f82c1e10109091001c46800e2141c000001c808403810417102d51514041041600355200c040e01040c408513008055501030507511010240c0f80354007418110959071180f5100050340c0c00c11055600e452a0112814000d104030400e540000c0c0303145280440c0701600b120b06500800b0200d80000345408005049120580254000d03c407940c080d095038686440c000d800c5520007405010b02c40d0034455031001603100e200032a0306444040d9000700310801000460540034103001c0503847c0314411440c0030b0320364204280c0e40f00d101a40030b0380d440d1040742e80d03146000280c0724191340241403602d07600d004001890714001c1000f2403001540c1928100400480314000301c46084800340176a94002003040205544072248903106148544201809000c00e030124420014040b0902165907071600c903444402010800a4680d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 935104442 1250 935103192 935103223
    0x6060f0a26010c0314161218020604030602031b0f040e040302010e060711100b0603010b1c021218031206091515040608070507030c02011202040b03040b19150314 71
    0x3540c105090040081c05c0e0b00c807908030420302483c00b050301c80300c256004170411452a51100f810450002c042c200404041300c12011a080c1455020016100c84001d0300056015800060b01c03440c0010700b94400c1050208075441741e030b200700001d0701c1000901c0103481c02d6800d050380c2c3c0000d030b80d5180b50982c014502181c2450041c8620410440b02941c85200341c13403003230408029138801c04c180310703c18400d48440900e640d030700590920050041440f120050940035104000405041352803030015001c981c8162842861404000100b090f1501101c1c541c1884010030401140f8240c04129800b100c01809003a540c81100004041b9047e041407811009078201c00821140c1b099802c0301c035101e07855109200d01c00100e000100054800c50150099039881a05030b240c200101000340d00441d500c40041030004050b035400d00001c11203a032580090f5108030f05c621003000e07507801e000400e8003130190502d036800700313541c1800c030010fa245500f0400d81c01200d601008007241c004845402030300344141603031190324 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 935105692 1250 935104442 935104451
    0x1b050a0c112d060a08011505071a040512070b192003060310060303140c1e10150f030b0a3e190e01020109060c030c0206060f0a2601 58
    0x402c03001e11074101d0010600c041520080390242d0511070140602c030792000105440400401800031292502401d0781640d00e0001c1c909800c2d03a0350403912200280007840c003880340c1c0d802c2208110b401c10007102e0031601e1042c0103003070071029620081c107481300520242850581301039001110429030041004440a50080c295285640d210502d03a500708032102480303445405c5115100040910920090381d07015640c40e440501030980e000c00704d600c010600d0000c1c2c880c03083d4030001107103003440e542489035541c2c01828882110030304460998291020100002d03000329001c000d0200303450003075802c4907800041c5a00039030352204140000d00300600a1035254400c0755498401010000605040012072180498807500001c40001640945440850707070f1264030054a8035a070041e9006c0b42c91702c20520020810840300c0e5600350a90b440300300c001d4046516020754100c0c258043c411303c2d074445029102500000201030004103030704854454000c5030f400110980059034400f0940e507075030260342c00003400b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 935106942 1250 935105692 935105719
    0x5241206010b0a0e100905060f040305120c010e0c090106140c100504050f030408120304110a23012102031b03010f06090501020a03090501032d020901031b050a0c11 72
    0x101c00d5025450007000904c803c10341155a01c0c1041529008643c982d440300c030020b040509020056101c83e040301c0d405101404004009841000000305000500449680301e60810115a083d18a000070302c0c10340e60401d11340c4503050307128509a10b04440390b910b0a01c072200c45100000e0b0107480340950100c414051440345d900f20f28456000180582d2044003243c1c101e07000290b03019200d0045002c2d00d010364101c41e00c52070300d201500c3c01454015001d01d6004800f4030b154400200c2c0b141ca980d012266414001004c0f8450007403220545110100a00f848203062204a0102c01c4a00702d20112014190b80070000c150025107014620003150f6421011660702d503141c0da1a41c020580d0f604c5804001410742101040303551001c10703c000890351544840d400341d03080c580190054940304c0520380d21011020719102075240420b43c1b2b000400004440140e0300d210354000181510350142c01c07800d550605d40c400000c0503602900f01c44880d10750b85081c21140320396250001c4410032515041c2c0e40401c144495a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 935108192 1250 935106942 935106959
    0x2a0d170705010f061d0735040b040213090c1503110309100507090302090f0702120a1e0c0203060103080901140a03050a0f06290723100524120601 64
    0x8016101051017003c0e9821801c015060099000c0743c0c000c00060f002c00e680203903105003809103c44907050b109811956400b05000c9119518100c60a80b00f105503a0b060006509003a0b0700120200c09680040c40380c00d050ba05c501c9482d03001c03486540052a402d8440101d8184603510892807440002915aa06d0600305555076440e2038001c05407442038500000308800324083c103050001c507540602461250790340c01140006105000b00204190301079404003a011264100040084500c5a00e4074160401d1183c0252070b0618208070000507c1a04008400980e60024843d070460b50b000d4034080e52052100012981505080048000481c000c9907480960b50035070092441070b0380d030f50801c0141e03101c81c0065409031110342c4140a0003001800114002203000c3c00304005034151844140d20b4011240c1e9000700e592a040400300406c802c50244180d28001031100c6140c0c1c42200c0e50501880c1045200c912078000114907522940b060301501c102180c403003192490b09117200f84295000340d07070744501d403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 935109442 1250 935108192 935108201
    0xb01180509032505010605040c05070605011205120d18060f0e0d05041406071a040c0b07050304052b05250807030807150e2a0d170705010f 61
    0x958441608040015000100000941d202c200b2554541c01014180c03800c0c0902c92181d0541c01e0301c0319521005c011940c0d8445004442e10f40c0070070b942e41076840344507041520884106030451100c000c154030780c7c0b801091001506050382c00a68510a5603042d03000c071100000c2400c900d042c8009005003030b07c01e0501c0066401030b00074841da0380040c0300110ba0340205644036001d00040d40c003c16428402400000c59040c032442002c103024205a14001c0303545c854044840c2001c060400000743c0f10100400c10200429040c0141000350090b0700307004030342d51295241d02941c02000e010b402c3c82d243c1403810110f80b0030038480c0c080030130b40b4003030000543c0c2c2005611149960241003c0060f85001c0b5466140e481d00007070304842200c409421500e05568407080c0c5680414010341d030002c0700000a00700100303035101e024101c1c03000d240200322381201c19140038010f8424100010070104c2036040e120140e1203c0c1c944008556200c03001d81c00403400351480d0310481c064a1000b0700b040d031030101c155100022a601 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 935110692 1250 935109442 935109479
    0x4031703060901060318060507032009102d0e040e0d090816030b070302190306050f12210f1308062508041e06140c0a090509090102070b01 61
    0x400d41e0160f07884000039400c6d03801e001c00310f040c04451070710000b003c140940c0c441500403500f0301e00032a0728000c50301c01c040d5920844421208810303000404020a1803c5109503080b41501c0c20006020508204035440392081c41900c1e0704000c02c030450003002e0318418190540e101000034020040080001d80655075804440c1203680030826148002c50f25140015a226000ccd40c0502100440d81c227594501d852070401611160030f2507002e201c0c031503502c0d501c040c1c144c4800419a90004045140400300003400d0170310400309004031440040c41d0400030010500240230362040d184500d10071404515810305104a085042d0b1070400411003044055403079061fa001c640852045450710380b00d010300d00c0812000c0040083c0c080405003100e40c042802206c40c240d025000307122f5501e000b10340c0107524030080000c403400c4600035074441c80c01052048c1c500341c5c3c0d42c000b101c1d10b000c10300340030390000040c0418140340102c91080080d03200080707500700309404456a09600c20034404a03540e6a0141403003070341510a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 935111942 1250 935110692 935110699
    0xd09080f090915030d05160506010303021507032c070b0d02120a140424061410090b16020d02061204050f030c1209041b0203130806060f0103110403170306 68
    0x101254011800c0004500f16400040140107080706041c000d417001d91120007001003c0d001e5403108408a035061002600a40c041d801909581f4020409600b0901d8001d04003c1807601e040b100669140900320010000180c1c2040821061604003034246084101e07070140100680c00141220412015006010036201e08560002075407501400350068809650465a00390749000004002c204071180e07504c11304c0007080048070314200642004c4241c0d102d5402842c1450401201c04200f400e0040300e208002c2202c1c0f4061200600303080c01c005140c400d44000e040345020713100307451080d5078501c40100c40c0140e0040456070380e0701e10040d149050000499054549001c2d0100071920480701004507110b0b09039040c041c01c12101d560b90050a9030300000541034000c0d5030380d07803210025601814465150207040d002151a060030003900d00001031a50003000894002400344030940e00c0e4a0410f5103291700909021808030045040400503010384d41c0040c0c020b142c00d9028400100e030250085009000c00c1c8c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 935113192 1250 935111942 935111959
    0x130e010f09020f220212041a07091e090207050f01060b0c0c09310b060d0c050405040201051608030f0f070203070303111603020c130b060304080d09080f09 68
    0xd041010444040400280d00040c80a490b0f061618014103c1840b61000300e0b915980f1011540155049030003d00312018081074400612040c40b842c41c0840d1001e40725181d400c507003485c10320300040c40d900d403030310501000428410810300c146050041500191801310300071521441281800c03a45c0e02c0d0618451043d03035103829400f2560380018011500c002c41414000c00b81d0000070b07000d10200c100024010340c002e071400c682101d18030005040700c1c81c5007000d40501c400008483d0508543c042d001038122403254003030034041e200040382d511040c000c5500403100000c0c55600d80c00182c0d40340c86603100c244000f0100c11401c200708640c0700051b42c042d1201004540700b13942e500c800c00b0004102550300d040581c2c0184590400a03201e904040f4410581d180c0c62818000c10440d00d20323400b07450003c2107015801103611005941811000744121810700700c010300241c0340200c0856003a1201400103030280c10000781c0b04480801681000811551280c15107640c0c0c08651006440781d04441a01c3d0b210300c000e03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 935114442 1250 935113192 935113211
    0x60f030a20010e03070e1905130201140a12180203010603050607080709050d26040602010e063907080f040303120614130b090406020703020708150103061a130e01 71
    0x4180703c210b0038901a000386000c0d418006480070000b801000c0010481d0751051400300c0034041d02a5500804251000d00306030811403002401c250203001c07240541003070620410901079845020b01e426844180f2000420100c0408106005185020080d416608218002040010000f0141d200340195035560302546c4a0701c100b00c816003501c1c07058651007003860203d0008100d14184040303410910020103085101020715510b00c5030015441600543d56649154104090610441d54009290491403900c1c0e080f05c01181e005840f1042c0709441444003a0f2140c03640d40c01e90080f0360b003040e0003000c016200c207000e0495212035400f0380802c030006045180c0d03890051119004140540751040d481d140d21041d00b40611401127491840000390945980c5500c4640d250315406c64051402000056501d090608000e80307044043d50100420703611200c0a0301c104420080c1c01810740e64030440104411094920916201c1c90b401d01003039000e45003038404058501035038410351003040114000d1200520 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 935115692 1250 935114442 935114447
    0x40303170403021002030a090c170c040212070e060d0501300b1602030d02030c040f120c05060d0e160810020c03040b1e0f0309011401031505060f030a2001 68
    0x1401e50700200982e0000080410f400c51507000341d6800100c0100000701d440d40d43d141c0800306159640154410008009501810a42400821850502070340c0541c546040902c40140d90480101407908200b440e00c10442e96583c0d06003140d10005402e9000c2c401540c4844501c0007a201c0c81d004240020000f6050501490310115081481600700c00d8112150b0b0340c80380540f0120440a02410031400304201c02d00c48540c5c180301031401250343e100b134180c031981052920b03014844c260700701e00c0c01c58200380c96190001d03181047c8a4280d03003054a15079155041003040b4806800c103041400c4050040030382d5600381c4c2034481508000c4510b080e003124812000810110124858103004c071119820402040c010101c80800418079450182e51010241001e69050341d26900700d400741180081000050185008090086003580c0d10000740385c440c9545943d80700c0e1442c6820f071b50b458850b181c490f80054855600d07054806540074000d800d03280b144d1294640b003012808481ca58021201c1d00141120341c552 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 935116942 1250 935115692 935115737
    0x30209040c050406050103051311121015080f0a11040f020403030c0218010f060c05070b161209050a0302091503010501060f230a110c19030201020d140f161205040303 73
    0x60305081d41c0d140c950083e1540e00421051070400d81d000690b06240341082e01c000c00104155040c0c07110009040380b001604809101d00980c802007040d4000100701070704000118440c5166034740507260150100c081c07030208000d1b20700f08219100d001e20110f00042415000100302e41060310854109164204001c0c0d2441d407103100303004462494107880c00610243d800707090a074140034043e03002c50700c24543e5080c82849540c0038090071440e0180d602c2007134040006c41c00c1207c1050600c2d0400004141c00c060104d00d40e2001480064801e040c50790109003541c030101c0d050071040c00301400900c40d039a120318026082d882d4200c001700019900e59940c3c40446005440c06403e1912680c11030310b0520b00360f41c21104220380c0213824846004100100711180d5030416114810120044d15200191460002900340804c00301c1e40c0061140700e021b48080925200112014040040402a2114103854010f07021001c1d01c03a0080911004038914480c0070341000280007164426500c1581e1100c1c401c070b0582020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 935118192 1250 935116942 935116951
    0x6010e0904080d0902060c030304111305010b0307030504110940030c050f0105090703020915090403050a0e061303170f07060f1112090d09031515030209040c05040605010305 76
    0x28010710042c86515604c3d04450411400100a28100f51401d81554107507841594121120380b0b1500f404003050a25021041e40c190400c0000c100940c501418a559484020004000c1640c0c0d040024108040d0700b03403444101c01c0c05021601301f8509002c0c019413502681560020381c0c51034014400405041b0624130140c2d0706001644044240180d80654254604a01c00c0300c2a000e5240da00b80d115800344222881030341c1ca90002c10b101881e5005100352400c0c0a403500c2c9001d448030040003165207402c1d1801d900540c0c140780040c0c0c0d03002a0030041728406080941035a1148c1c2c0054100210144061303040140c030301510400d0351b146000f60011070940302e800002d40c0e010f030090040b43c01145440d400354085072405507000c545004c410b0401c4156070310180180f6011b103011030902030f604508116211000c003250600150060540d25044444c0700c040d00c01e803e001c0d0b221000d0496030f40640324808010b40d805004003c030317424280b41a4401801a01900c0d020760706d46840020340313621a0007800e006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 935119442 1250 935118192 935118203
    0x906030d0210051302030d0503010e0a06050904111504060810080a051e160305010507020c0301051b0708191106071404421d03120c160603020306010e0904 68
    0x9459030349a0b10300290a0040046010000040810025031400e118151444099644443d81d07076062003002414864041d01420320180f50001c2441140c6030747d0286900140c0100041d41d200406500150703500005020343c042e4103001090000382c90f50050174060085c0542c01500500545443c0041e0303503503050b024060300c140d120b4046090307040c0740301050b401d2584900c0e082d10202600d02a464040100550046901d617548108100030f0725418021300a00440031002807007a4100310659204001100083e20300d40040010090100221703a000c0b5480030684101000d032070000c5450107400304c001000c1100c03071409028005001b2030311030180318802d07101c509427040c240360600c880c03000c520703d0710110a603c5803404848000f03115507465111b80d56200d041803034040d5110f4100005d2801d50540714200380d448183c1d52100e0141d0b00460050800d40341d407100c0035125101030812900e810600403141c9200d1030b42000c0410111b601d50000c0d4854902030322076020300866039040c40402036044030017500703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 935120692 1250 935119442 935119453
    0xd0902030705041119020a020406270b033a020706020d0806010206010603020d020702040f06090e03210403090b0d02030a0b090402030d0f0c061a0a0503030f070204050402060d14060906030d02 84
    0x45c5151842980b041404180c4102c0c2c1c0c00c8482540031a00306c1e480c540041d4581c0c04102880b50101c0f00d004010707460f08440e20418400344810b0740c04a5601c8414182e04a0080820300035181e20480c486414084a400201201f40b900710100001c2e480700014095500140100c1039901d00a034019031035180140011b03401042281e103400811002500051441400140c0130407460000d40d80302d010303c00700d005007010006156490002610210360710700c00b0600c0c880c2c00500c5550301008001c24091404900d43c0ba11085513540c614084542c640150885190550086807090144600c0da000d14890030b4203d004004054070202040b15012003150000d50690083e190a040da500c00c649503003180069040410b086c4400741e03607010654070b0980032445000100c030718403459442c140107130000400c0140c0241d441c22020305103080c0c0c0c1c0c1c400c0b000040d002c0c07501c54000c60210349503042114210704101504101112080c2e2034440300304025280076110341b00030804544289800b081c03a04044200360010b14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 935121942 1250 935120692 935120707
    0x60d1505090d0f0912140f1b030f070e0c0f0d0209130608031b01110a02030705070b0f0711130f0c0908060603030d110403170a03060e040804050d060905030d09020307050411 76
    0x465142e085c500840703c00c4201640044d41c480100b02ca408000a0100544030301d00610322076070b4200e904d504600344254820b94000241030404202d080940d1501100014540d0310b45a0503043c40c8203040c1d42500100b0700107164408007030300713a025002e80d840c216150fa03500c0c03100c0c40300c0300103440582c012100283c108020305640008441c10003214040140c00218982180811a5815420462580c00940c20001d0b9607420484103000c10800b0309181e03501d95003050118804c0d03154500901d1402800c00c00c0100100d0b80036a00c0c1c10302400600b01c40b500500c1044000c1c80401e002e003002c15200c00110315003020100e414840842d991f0300c03841e0044c1c011414502030380740030400f80c91003114411340402d0820000c0040342d14000192440001c0f1510650f42c0c1c00d510000500f241d40682c41042030018a0741840700248418048408030b460032070b503000301542a410b0240080000c1500101184030005603418007183e150400050203008038240c0e00201c1d0b40790107010a913962014940c0740040b0401520 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 935123192 1250 935121942 935121959
    0x50a12030f06051818011d012306120c0409030309050d110c130b0a080d080a0908040501050306031005010312021b0306070804231501120b060405060d1505090d0f09 72
    0x441c2c3c44540c4820310102c80c0020301180f0f0071101000368010b80c0002c210509903111009020700b41d0b40350f0300d6034061500319262741d01c0e100c200f5030702074070903842280340d0820900c0642d0200b0900c01041001041003008421078540a4010070900d60215514042c40c3d02065505015410110449001a0113400b00420354000c0100c43d061003945018440eaa401d5005c201b905c0c3c1114240103040d0220041030007008048001c1c029140090068105034101100c0340001140e590a07501120020b080c407585075110080003030300b17142c0b140400c80083c5182c18000801d115614145688403440c03502074400c0381d42c030546482400c0248240341c9400d94403203404105124070a64855030b0080c0546020b809560501101300040307014a411400107034400468036a2000f40e11042c0d0b40100b0601da80c044000b44181c0d150541c500c0d004026038455030340c4000085907a00c501328918421640300c0c541e40c0a214140c0c2ca49001410306513040044d5124400c0b1030341c41240600011003140701c1e01e40710713100e00702d2401925 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 935124442 1250 935123192 935123239
    0xc0804110a030b0c1b0613080d1b02011506180b0c070503191707030f11070902040e040c0b030103020307170c0d3f03090f050a12030f0605 61
    0x9450304944074a60000200720850205030040c40d0f80d040c4036548940403911090015401d21805400c2c1e0080030a10000d0b07200d0050744541d01da40501c00c2c0340c5885000101600400100c84041c2141f0650146540c1d41036040d030200761411a200300902140c1c0d181d01c0c4c11140b05107040c21142c1911000d0005100d407409200103015002d004000311161076494402190402e00c040d01d160728000c1c20b5034100310405c000c42a101000c40000e0310214100030103900c008140702a82c0d4940028031400240d030b08520241442050041e0080c1c0c107080d507451b40d5032400305260000448045d60781aa0307070070000c1200703402c24048904894000700104042c40c209034802840c101c0c1400c40807420b114540302238011f03440d102020302c03145015a0300030342c4048048850b000209010441c40882d11140324038030700340b40104015003545580300c1c0750000e5510303114070341280c0106c40c415020b009441001158820000c1c5c024000d03417111415a024440800010681025901c2c0c0380281607100d0603502080d60130342d030312188 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 935125692 1250 935124442 935124473
    0x607030204141311040b13240f110f160506130b2b0902010e040e031617120117010c0503281a150405100f0c050105070f120c0804 57
    0x7001900824804c1c14400c1c580c09540f2006200e600030840940b001c40d07001000d001003812208601c08250603450f05440c0740c04184080c41402100030890309407911444650a4120900e070031955108160b010701640c6101000320116600880c030008242801c141c82500c1030500807204c5a0341d42c174204601c0c0d0505400c07106a00c04c1600000d4200004441c403541000700030315440f000060700d044580001013140c901c0c81303030440c0a030f410503940e0f54241100008550207199800681c948456042c5000031280440c400c1d40d20110201194501008258410450480c1d040030320421810100c1190369080c1e402155a000105c0d07024800282c001c07503506408200c1c200c1101c400d014150380700b60418100c07040c40da294414034642e00ca545005040800124200700130045000e41401d00e41400035184210030070a1800b040491982e00500d280981031111080c1d07031000090025141c814001804402441e101d0800621000d2100120f2200d522405003980e41036540c0418580c0c594403581c440111044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 935126942 1250 935125692 935125729
    0xc0f1605040c110105040309050a2106110715020405040e06090604060b0f030f0a02030d03021804020d1d010e0c2d0303160b181501090e070e04050f060703020414 71
    0x298030721003c1000303110301880b552094940f00801800c000034002505217903003085a02c03a0190b21103100450307d2485100220350310000115a54248501162580c01000c074000c00102c54540c4020034803155801800030707507070269820401c036052086450742d912416183c00d800c503000702c00841c02007600d503000040d0004029018800c0200b8010101707140201400700d07282c0c1500310365000000c601e0140607070101c60129140641c18030b0280000880041c11144e031840c4034a50006420cc0754054030b4110a000c0c809208031104a442c45002280c06809810303401d80ca24000c00b41034418510380002e43c080110a1004501c000030366003421400300410450742d480d454402800f40c0b44038002c603c3d0b00703918060711944c8260440d080451001100703d0f021485051207410844207040c2002d401001981124410b4001050f84c0505001d46410020282c01c103840e44400c20b0200401d211001a84002565007001156166a1150001c030101d02480c0504610b0a0b405a842030580c80d0024118070005081e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 935128192 1250 935126942 935126957
    0x501080a0c02010b060c011b0f02030a080406090218070e15031807091505120d05070f0c0308210f0709050d02061306030903140a02030703031e0e01020c0f1605040c 72
    0x40d00090708070340003003a01d111141c1d10b4500c912346180c1d2075240b290b803a0087d41442183e0708034030f81000c0d48074001c50b40f0724400c0207680b100244c18004142c1190344004d4004c4c203507071400300c60002020070003241100d54002080041c4031308001e07030038941a0144c41c2d40600c4115070564030390f06040d99240e00403180c600542c0c0b2581002141c81100c1e480750003440798000032620f4189281005020040e20b01482000707858000100014005801c80102c1d810300c1d0f0b0150000070403c03940d103055495050785400242035a40007286003442440440301f0104045810900340c1e200b81e455241c43c0300d14400454080c0001413180c0400c0142c0d0038081c000a1403144020010780c1070450124140100b030407664403003400a51141028030034035030000141e10b403200455011503d004071480f80a5540d00c60781d40300604040c0d032518610181088040b0101c151440c046050100a03100c0621324042c0d00300218110a40c0a001148078603014005528800708002c115080d484c14540350420008126940c103420a00428 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 935129442 1250 935128192 935128211
    0xc020d180612050c120a0e150405030f09030f07152c09090c040e01140105060c03160c030f061e0902180702010e0f0a12050405010206040210030e161e0501080a0c0201 73
    0x4801764450002c107a0001804148283d406180c40620b03001c0240e01481481480041900031048030800705072060120b503203c90010110349404030800b60018a405410386c08a0480d49038480012501c600b80d0300d4080900300072454001806490340440040100030030324016a06200c5a4240d0020841c1b083e2607000c040325010405407181c04603110000e03507541c980e09911400300c41a090141006071001e0303040c6403200134460395034424111501440c1628100500402c011400d044002c2c1d035000c01045503200061074804003510801c01c00581180d541647c2c2025400a07100700040c1c10f40040840030981400424005240400ba1049045540b196440c45040c1c02c10054006140e81d03100003058401541e08100000c007000ea0110300070408108020030141ea40040c1d901d40180d011034140c1f6043d046108280e0080042e04603403032003070003090202c0e03940001044507041111aa100c008005e149064010781d9802054042c0c80c1c0030494000c04250b9800080c1d0113000081098000019010704 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 935130692 1250 935129442 935129467
    0x30f05210c0412150507081e04050316110112020f1e04210b0c03070e091906080309010e030a020645040b0a06022e0c020d180612050c 59
    0x203d0b10007990700b83d0020815850300600d520545e81e00c0a0a0f02d0b0252040c1000d0085500301490080e45100d1100564007040c10700c2018811201910700a00b01c0300c8081d030303e510340000001503a0b40d0b000c1c00300c0c01c50800441d01c40c2080c0200c82010340044c001e44d1a00b0300702c0f0710b0704009000351040301d5aa240140004a46410b0a80e085161020380c210144605400c0341340c0183c10100c001c004000944007441030001030380d00484800c1a80c1c1c001c4400302c01c00d540351114481c6403107544640e44c4046040c9a400a10000003200800180000380e0b41e400c001d84d410b509241c0c2c0d030f42501800a4210f0020015007880307192070078038000c4180140c0c0120892142c481310b0100752010591402000032000c812000a80c5031a05ca1810500070503691150305619280c00607441e003401c012002083c2000c04245c3c8064140d07541c280d52000d5903d1070401c169001c0e01c0001f075856580f800740b440400c45150540e01d10641b00c03604642100d52546e01e001201414001c0c40c03005c0c02028014681015061100725010030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 935131942 1250 935130692 935130719
    0xa030e100e060415090206040605090d1a1501031a09040302070305030d0c08060904050d031806060f090e060f0103061d030a0c110f13021806070f030f05210c04 70
    0x512400a00b01c505140c144101003082030200031415038640709000c0016126079040c0c0301100c07020300b4420744585600000c035400107101c0400600003083c2003240500b0000b0401e03034900401404040d60f125030301801c015000ca81c80603540030b10306e03200c0300f018102e9850704003401070b401403191040c0e42200e940c0e5981c00e0318580016014900198440d074940101baa13200d20803075071100003201c51000790304003030300e9007030712812402c2c01d03202055151000c070140c83c00d00e11403a40e40c6541c071a03010084981d039a408141d03c01d80f6402982ca50702e00301010513040a0f800600c150182502401080280c0d02c2c5586100051070428104100ca0003024a83d41404000307002902c030300c03052a102c1d81681d01652400044101107480007501c68044001e401c24191224092000d02c0070300740800585d02d1320781e9062104d40ea0344481c081c96100c203001072290b00300b14041e60300b22030480c8071380c0350b004000e1082e1200b920349000d504d11404203d540c5800040301e070f4441036045900044241e222600d001e4a40e1018003011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 935133192 1250 935131942 935131961
    0xc0f020a260c060f2a0307030c031b08060f06070b1501180902030a1113051c050f0a03020f060103021c060605040e0f0c0306040209010506030c0910120e060c0a030e10 73
    0x242c1c0c2800c101c41c02c4030030315840c4845c1200e240b03041c26581900901000fa40006000f00c41096580c54200c005240030350301c500c00c0d103c3d0402d504009050400d01c0103104060480d29540103d2901141540c24184442942c4019900c0742c2404030950300c8000c0a04103460f5540c00c6070410043c5a250281910164020006003003003c601590364507200c0016420360300f40c6054030461120070070400e9910f40000300740302c2c26140111a0040c510b81d40ca446414810f00082c400b901602030041000814000042c143c40e000344281c007907581c0d12200d004800d469003402d12020390040082c5869010026082ca90b120400748100c200164482c0c403000468200c561050200c0029030100f0324192040e1810007000380170260440082442e4a401d6011500c1e0340c0c018840c1600600012004c1400340592030705444240c180500b02c0380503144111030060000c000650705e1604945468404220103402083c060322418040c1410740c602781c3c00402c01c5008110508800a440c00349003420b41903403803a0b002e6070404c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 935134442 1250 935133192 935133211
    0x30c12100501200705060904201b0c090f040f0501050f010f2103050f25060c0503090a03080601200a0b0f040c03020409060b130c0f020a260c06 63
    0x4a80c10140050b00298a5100124111105400c0c103c89032800203131070800c0d2403040e2800c80d101d0200070302050141c02036500700c50520004e507c441e01074103002409801446c0d12540d0f1621807140b041c101c0c1d030b02c07504010b0410360811841000145081c80c0001c078140c0140c4614140c0020350980e840d000d0841e00c040c0c0c1c0c1c1603850541c61004100580300c00345000e01a0400030718804030400d00c420040261044260001d083c0100443e6a0b403140b03c01c0015140c4049079099180c0203080034a1200c6090003c3d101c00311001c0d8600100d450300e182c49801074a00c68000400281804250b0361010741d000a0024141810041c090a0440e040102d82008400c0f800001004010051480c501881440401040f09030350140100c200404960102c46050803203070196400111101181805809009030b044182c1d003040c0410007441c10540d081d0b000941001d0256984e070701c031040300802262160031040028003607000051880c120110f0302401c0c1d49070079504249141c50407000041440c100b00c02100c0c01d148 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 935135692 1250 935134442 935134471
    0x15050403091a0405030606240f1312051f0f0c0302120a050402031e07091d06091603060f0e01111b0606010f03050a060503030412020a29030c12 63
    0xb4014a142c4101c50007880c400d421400c0c14180404643d0314032000b814240308180300d0030b0340c6482c0d51052030031811403094003043c2ca50328158040e001c0030744c0d88080611025070302c0f980400100000c0e91403c6150300c5070b21001030014100b4542c0c04810a5030508a0aa200b50f95035125841e606200c0c80750110303e000781c3d00c000d600c0709149180060141d50007012074a0700c03403c00b400c1200603603001c522882d150800c4182505400100c0450b18070340310320b68000314566450201c4080492000b0050f41046080b21411124159142a6855156074641480c002098078519041c40012415041040a80343c0704000144081c0c2e0b40b4000c0f400e68600300d1a0102d82d41d40001c5031491480b0811820b020071445000501c02403e1a40008155001d0140094201641e80300450203881960300034400500c0300034216074503107440305000e8230307441041c84e41203108420140c00001c40300503a1444007031141039282c200c0c0140300001d5111304154001810784103010820041b8a500200303040259008103251100c4a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 935136942 1250 935135692 935135699
    0x10f050f0c120a0e01120c020705220c050714070f060e18130b0a05040203030714011b0504081501030c2c01090b0a0509190b0d05060f0709120b01121505040309 70
    0x140a000c0346d40d01440900c0c10b000c082c202c2c03143c001032040111034040d41e90504400f0407000c0b03032b01c4115080360194000c609003800c00c411a03520102400e0110301840000521000d1080e03d513a03911110312a0440b1516000c03410011a0301400b8601241100608603494100b030854130083e1064040b501116002d130390310ba4010901046040403940012440380400040c24a43c002030fa030f9000307803040280711401110340403c60301402e40007400300302110030000f4200040c98601a04c04c0e041402441342034458490441550051140d0640c12a5084000d0300c024604294210009038050f0700c01070044040ca5090303900044107a86000d000740b508400018648900c0010040d80c055103a100c54842c44404060000100302c1442d9990103c1100e540040d0085c42c0801003a200c4c00b44c25070103403003400703100c04104042d680054650b21a6070995211100c080e1505200e40c482e4001e20006080415204018051521444400580280140780070b803010441c0c0c010700c60030780e48115030803800105061003c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 935138192 1250 935136942 935136947
    0x10e0d080c04330c2f0301020d0506030d0f0c260a05070b01060c021c14030703020102040e0f1003060e07050d080a0e0418060b210604050c010f050f0c120a0e01 70
    0x20102c074035061a19202030b401c1390f241d548a4070b407400a80034002c0c49a010300b03c640d00d8010341d0a0003044025009548401614101c2c10003408100c9596000f8000e11200001162103115141c4401220740c0380d41c52515130075110140441c81d041318607405c01030714010040d40b8100410281815800a070f40e12a500d25240c503100d070700104180c0c48041400030031030362040140d644c080c59403242007510718004e40c2010b240c01c2109800303c11244010903400002001024145d064005005a032040d046c404140d444446440c040da0108850300655500540020f20002d02c00d0380000014455980445d0b1503d602d400c00a44034500d002021100c103400000d11000040e000314802c3c00344130f411101080764504c0f103c0742a03551450440003c00071580e07400fa51000b039031511103640300c03042100385001b901d9440f099060380c0c9e030b10155003e44041c070035840e20070031640c81002076030724107401c07030380c1b45800c00c040706010145d280c00002c0100e82c2802030303074100d080c07000f280d40181c0175280b9165a4100d40d2000309001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 935139442 1250 935138192 935138279
    0xf120304080d02010204050a0612060f0b0403020406080c0108040b040f0b0c030712050402030304090f0204090509160b0c0c100c0506040b011509050a030206090a081606030b03010e0d080c04 83
    0x3902e007075900501c03041010b0303990014100d080360710343d0518221012240c0f011200900e9260030090980d00c1000c000315000c4102005441500e109540c204800c1d9140c0b820075543d9400c028a4500284507480020001442c0d480801c4d00540b06a07051000950196640020440103c1f5038414041c00030003000042d561101030400394410260003003040d03061a40100351203103e00d021359803c603071711418182c2d140043c95046500400c1e0b40c0b0f504202030b04210041603241d00714100042909031100740d0101d80a1107000072505d800d1100001004d12040702c005010400826030a0003041c4030600104101003502031140b5481540300301d44a004a41c10000e401c05980b440b000b00904004492600340100c3d00c800c0d02c402c069a4044401139110455440024100f0240360030101c13613030248084c4040c00000010344072050b500151014001ea141c0201803500f02c4035404000c10640e0700491114809900130042550030178070040c0d9607460305855941a020752640e20001d6003412081408408846054020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 935140692 1250 935139442 935139463
    0x31b080a0b0a0c030c090905090c090114040b0303040b030609220f12020a0f060b0a03021003020d0c050f0313020f0409030206010f0605040e01061b06060b03070905090702030d0b0f12030408 83
    0x60421601503c1c01c0001c000303603294002c030700e00e030b640d2380e008100e90b843c1c00c021075044402e0060010180d5a1200005011451701c0100e49008900780050010103241c080b09903000da0341103c1e102801c5943e00c00c100b00c600100540706181014081161415004a211040819501440350b11a01d4400d070320b816800c00240710400300071500414403090000711466510b00c4d07641d4112030013041c0380f9582400290790952650002390310010751380e078241d583d9405401030300f00f1510f001001c018480e00f0600c2030f5610300c121030f0003242414040000459004503400e901801d140003528490310100b40c0b0f070120341101d580c0d0100b500503a00490040020f5480100d105016003890b10700241010726201b04a1100203060141c1024000141c03a009e00120b090001c0080781e6411500c207002003030781d507008449951320548045001800d0b0101c08100c07400c0603400140a069190300551a1400f1120f088008064920b09140d016034002084400c0d6030f202000352101e20b00c50005503a0700c03413915645914140f525030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 935141942 1250 935140692 935140697
    0x9130b0a15120b1c03121a0d020108130b0a09060e0d0c02010f1b08030603011524030e010f0b011205070e130f06060e15070804031b080a0b0a0c 63
    0x1420400c0541d114030300015103a000a00452142ca2020014081c804c000c0c1d501c0c0401c4c800d500c014404d166000a402c4e6111494103020000340c040300c200d400c1d5014901a405800441c0c0a044200551045404a0780700d000c5051074240b16000750388541700800c040c3c81d444042c2c2e4450400c1c005020351441400d20403d0700c1c5000341400e90020401030800300c241340d0b0190511102150820003540a1910b5907034a06c1080c0c0064000c0b0720500c0c08400540094581074041e601c0c20590341144c0110102c1d00c002e5401403000e01d9070070b0341e0704001c0000c5500c04d00ca28104040d12680465046002406131340e00d03512003401e011916580900c00184001c40b400c483c82221420281440f079030b99000601c0c0c1c050080107440402c190641141440301515090114415003450038100083d22035010710450050001200c4001c48548070542032031640c021518060609042088100000f0303081100065501031030b03110390745025607140ac4241c280005044190341103814141000018200c1c3e204200d12880c6a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 935143192 1250 935141942 935141969
    0x1090b04050901150c06020310090b061318021b0a11090f0703020f0f0c01090b131523010e071407050d08192406210b0609130b0a 57
    0x480010308081d411300c15400c00101c0e00381c0900c83c00d0300c2a80da89040c59000304003555a41424246c1c00306118041c494003450070b184c035a0b07035482480c2c22801c0b14000702c0c01a400314649414420304400d904072a0a19501d4140d0803c040ca140202845203640041c883c3d1014094a0b08a403c29000c0350240070f441e41d03c82c01442041218180400e068950010901d10b80140c0b103101d9102c0201941c4142d1101f80005800860b09000048054020120351441503400b4001500d505000c080c1e10481c02c80010320300000b10054601001c5564445c64079003a89441002c180e041c103051100141c402a0007855102514208200b12942c01c109100c0c50089055020f925009060302c405840314000450001007000580125084030406810a040b0304003400c0c0800c068210f2500c403070318078003664604004c504010a070003c0c0b118000d203100000066a0350000c43c21300c0c44d6036031040081507a401040da0003071080c008a4401d807035141001031080f004d40c500141001e01c100c00c000d5800381d942d0003181007984a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 935144442 1250 935143192 935143199
    0x15390720030f101506091505070b01090e1b210c040510080729030a0e010e03090f0406140d030201090b0106090326091207030602120f1602120a031b030b01090b04 71
    0x1c64415411900c03800c116071f50150f00c000c011178041c0305404000d81103210b500c0c00481c0000c42c0b81e011400500859013266041114142c030380c5103d00c0544001c9512101050400241124000f40001031081c41c00170b0b5004071661700009000c581080c0ea5501000320700e804248510003040081e03001404a050706400b84a40c4090900301908884610448d4101c1c044081920903046030424607043d44c0081c000d20840300c3d068225aa81e4008400f01d51007040c030440340540e00d061034070401c01680e180074500d8004101d83c0303051291040f042c1e0b02c100d0441d940c03030450001140d004003119001e04815501c0b038000c0c41c5181010819415040592244650942121501c2c400c1140c00c949451400b5140914a4005001038508011150b440a0030703107400007c0c1e040c20514114441c5209031a040c40c0044191214220010a2910491768901690003460b4420f0f0a86030340d0013402c3c100c1968500400c0700040b090b000e15501005240c920040ac2d03c4074038118243da04000c0c0c0c10064018056031034102480c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 935145692 1250 935144442 935144447
    0x7150507201e01110109060b0f0103060503060f1f080a030e0909100c050c0102160c0f06020a0b36010507110a0f0515390720030f101506 60
    0x10202051541508000c902c05090740611800f01c1c81d01c00034402041406c903241445c402a02c00070032064410551412419030320341c000d00c20304042d03880242c000c2401c1d07aa041e500d041610300c09008181b40d00e0251848040340c2112190311005002c0c0d29020b00300c440240e10380600150700511005120300000c404120203c60300184030520140000d6011480610068042d41c445c410146405169400090070000c145800721135060940d100b0107121104550318140302034101554003030400140c004e00b00705008a0140118503420a003003c02600c0e4501d00801d110400d040c01c0c665041281100d18410206800c007032050b16031100d418200012160b200c0840039440d81c0752188004e01d03122142030742c50107106d0104500d8006542e90344030540c860800c00441600b4518607000e01d010b00303091071400d952589070240700325800071008289a05040d00d9955088018040348500c1c05007840303d0780c03240240d55080000e1225884a00b01414007070450340d03550010b4403d1603624030510401c0444c100455503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 935146942 1250 935145692 935145709
    0x4060624050315011206030b091002090307090b0103020405040608010903021605031504080c0304080616030912030e013b07060f050c0f03040b18030a20030715050720 73
    0x740000303000110503070300500585840080356000401e0506d003c0303020040200c5055114003d840001c1251070b04080890324a00340d11520810342e4054204080400003000039400c20100000b05041c05403c00340c44201046c100d072020340c48500640c0d1500c0b0301405140c5c0622445210620500803504801d04002c0840e03620500130240310b040301c41120001d000d110000040d03c20440e5644152980c6959030740e040c0d50f68010541315a503440011102c0080d01da40a0300c91b482d82e441d03004034100d01d0100801c2080e00144000d00d10390489540b26504a0034140e0804007034a4070301c9540d0712041500c100751400da498000c04e0052040305134081c3c802445055004031041908000da460a02d03921034580c0c042c51b092002d40d4076890600e10001c2008a03006601201401480c04000e8062402100326810550759001c40180034001010780c889001c214000403001d459000000750855000e030341d844403a090440c00d04201a800900046404030412114000c010400000003509189000c01440090702e042d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 935148192 1250 935146942 935146951
    0x91802060405010f0302160b060312130902091f022401030b130f060e0303010e092a060f070c050901060906120c170a060305010f060b040314070509040606240503 71
    0x413800505803280341c400d40480c0c04102d40c0d020681c41400252905a220f40c50a030780240c864041c80d11503c841600d0b2074140c0b1100030308482c80a08061405480c0d800940c007040c82e031a04540b402802e010146207150400315001d40b680d0041408158003030480a000300112601103040b030200c0010030100d05080d500a030000b0707404410500c0070b0a01d140503501d842d080403008200d01d09141e80301030300150120107036040b60001c00002045e562840042d40c2c0b03030140181c0c841e0821081d00c1341c89810700b11030041c041201c0301c0034006600c0c2c42d0070912103000e1500520380c2100c0030011001e0a00441c2001d281c858014506800c6c1181d0707075400c01e84080c0c003001e01490007881d401d90390030010451503c01c010031440720f1560190b5a1180c00c1c24008035002c1c00e0036020907500f5600b000a201c04801140c866001120603402040307062071f0940e0390f403a0100341c82c2c0c81c1200b0700d0700ca4440b020940d40d0f51400800d001e41d00c00c15001408510f01071440c3c03004207907040308500103014135046032501a040710890350300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 935149442 1250 935148192 935148197
    0x8010605130f060806040c080c04060e04030e030f1002090f100507060b1f0806011e090e0405010e0313090f05040305040b0c07090c02012304020a17030c0d0909180206040501 76
    0x103010b002d040791000700f00c0380e0300032103244c424002440103100d51450f164046d10490001e90f000003108a003031200391070040c85420700d0f000c0c0c56000500032900c2005003101000e002403e80d202e01c20001d28040c9040101c0000903809503002a0b1112145071044002034242d405444e040e6580130b90010151050090103c040c004940301d03841d806045c2c1d02c4088481c01060080c81608003140420001003440e042155800d01049110010003146000d0f00141e00210905a0341c0c02240390400039207882400001c2c1085a0319901c40f21031100481c0d05102034905c0e40c188044190f0403070718100030300c003c0e66141000300201c02d10702000d03c8080fa07404400c40381604c5654020ba0f9840500041580c075101042e40090103c40c580801e42404950640080018080c111b4907403e01d0407001c80000c0d640c40050300c0080d0700c036803490b00c01c0101c1c2011a4490200c034203030702c0a69003010300c041d0f100d505041621032010005452a501800f01da06240704804013000e07400840d40341511541d001c00c020f131003280240e606 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 935150692 1250 935149442 935149451
    0x8090d0807060504060506091509070f0309062d0b09060d03050c010606030f0f060b09010f1e0810090b0102120f090a120309080d0518120d180801060513 67
    0x10310144904407035506a01903010801454141410b00081100740c0341c4511884600020910f0100c4800e41c095040c0e10003804c984003a00c0e2288155841c0861002e100300340b588911401d00452150310541c0500452080716019655407100d4948103050040e490005091400700380da032064442e200c5441d4021407d941c0800c07540d950f4241620b00780204413460b41603600f0080e01041c1194990440359510507400c0d8144103042c080f10482c015203005011b4034100c4c1d102403000c90841d610074101982d078000c0c941400d150001510f03040383c05c21070040b00482c0100341d110b002e0001e03080901c0c2000008240d807503010820b0300c0426000035100d1a51588541c010040801d990210307808800440d01c00707410041681107120740c1e0350303881780c04980040d4054010032000e280004418001184150948010b560384901e071040c40d240078aa80121810b200b0b42200000012403c6110200154011a03600b0b49513090046441c607035649034842c50303401028099043c000100026214880344822405107845c0125 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 935151942 1250 935150692 935150719
    0xf05030a09050d02010f06210f0f05070b0a0206060111061f0f03051c0c0201091215050a05040b09120406050915040608070e1f0509010314150f0d0809 66
    0x5020680d50150550182c40c6207103400c0f60301580101d210007440b21082c0316041c3c0d5072207482c005042d0100070407030403481c404440000682c0501c85000952245120350101c080d9500c549182060380d170000884240d00207080c0452030780411140c0e0707200c502442d2020f0140300f0004803548400002d08208003802442121074101c6400c8202100640641d04044409d29038a060003590344041c3d004d000e480e5802c15000c1d2905c0e510514004260359010703150502d803586040c40310ba4007038500c0c1500f038075140920018071400e02440c1c0a09030181000c81e40100d4282450300704102c4641d80071707001e1009944840322444a10640406950841c0c0c00c0e41007181e00c030f0748c1c0c1c807000c03882c0500e02d51058000800002000702e84103800c41030441c007070a0300350355440700e019220301800940104030302d048250800102200400d144240000c109081c010724000c00e9a195803200c80e1200700060b86e946959005580011050b410080d0050342c0ca03120481300d4003640e82203515000741c0780c8203e100311030040e03d6510140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 935153192 1250 935151942 935151961
    0x50a0515220c090e014101140d1a1005030d0915050703090e100e070e0d060203072c01021b0f040506010212031f080307050c190506030f01080c010f0f0503 68
    0x25452150b1102a0007a03000203c41070124100c1144506d0840142018040b2000440500f246040e10f04040d206000c0d64010010450741100c041c1d402c481d554003c802e145500c0101d0a0707224010310381001c01c850030358101002c040c144801c03114542c0c204440124201b01e1184c513000941800403150410917034a614605003200c141066806c0303903180d0981002031010102052101c3c00840f54140304109c0d1637100c1c020129441c84802c030913968408601040c10000c101c05900a541000c1ca41c20a20403419000d0000c01c403401e441c481314601d0300d200c00e141c461907513014401800989120702c0800a07a811910004054400d01c00300140100d030345000103001c6074020440040070603081407180d0384901d419003000500084000211080041104000810301000000e40d641560f010f03018100550110090004860082c54006c44494500c100007525440340d5000718060030420290201c10360406030700b40c0c0781c051502080c6041120311485041c141e580612505681800c41ca0320940c0d07070303c440118 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 935154442 1250 935153192 935153201
    0x1050603100909050a020a23130e010915060b0406200c2d01090308031f0b0d02041e08061b070605091c0918020304050a0515220c090e01 60
    0x21540385143c6143d02c014018002240828a03100303d928045181e1610044851340c44444040a500b00c0c40b48090401840c2c50300b031098a03680c242c800014041c880420007400d403203211000350703541030f41d0103840161400e45001d2680a0480e00800924061074010300038000200c085400151f00b1951101020146c02880114240480142244d0b501c92030010300c01d40e242c500070702d203400e0a076818031011029402140104100ca4104900e5411543d800384030b229900b61028140307214a42038a804103800c01c03d980a0403144240306001030b03d80d0704107a001c4004482440062801850094040250032000101c4a611411486d0807040740594034112118501a92400a20040c2032070304000000c43c0c002a1000b4400ca2815500000900004103440008107070040548502e24000007400c100195001035800a1168044402d07480c403a4907040c2c141a42503085508090940040c0a40d800c180c0000003120302c007007000003c240381641d07540d0b40701d0a90b5100d81440c0684803418000039110a501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 935155692 1250 935154442 935154449
    0x100203060609061e040b180a060e0913123b0d0503160f020102100c0909090c0f140102060a0c0f0e04021309060501030c02030c0703030516080d060f080f060105060310 73
    0x20150f01d0f10389442440720030b60859440f21f9070442c04907442c1d80300d52a1030900031080300d2403500c0304a84c16240da42071000c0301300018420054185211315040004440700307801c0b01100030940c0e60300c4820410b90b10080240d07190a040441c01c2500707201e0521202002c03907032001d80f03c8040342c0c0f4003c003e1242c500141103000d10f8060824100d000003109050004d070469011089100341e0a03a2000012030811070100d03448403030054001016035405000d40e40b241d0703000d568018001c0055007102950350302c00c060285200d80240049080580e5480e4280d44c0401281d40c0101e804442803242901f0740e080102103021300c0c00190b08208100900c05070a40361a4100d84000801201e0a0b0a00d91a26030741800303031003107103d800e0000307280ca000120158804003d990111118401400b00c0394515201200e8a40050306512451400080c000000554040c018081c00b00c0380c0710b002c103815140026402d007210f40ca81c004101c680100800c180030700c0e0007080c004e0544070f08807965074403078840c03081d1208602d10707640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 935156942 1250 935155692 935155747
    0x605150d0e2a010e01030504030e060d0e0f0a050f0706050a0806060d0c0207060e18010e070512070f0e2b03030e07080109021f0203040603020d090b070804030210020306060906 77
    0x1400500b11030146a0b080d01e8a00d0282c84041c4074014220045049500403507000e00081c0440729804800e250a00003000070409030708002c1041c94020000f181010f851100351410b03640008400b03070030084240310002d05603600a01603c8150302d081c002511610450300b01c0010080414000350044d50f901007690b880103104032040140060640e800796484440c1e0103030034003080302c880c0001505d180003402c640300b40c48146069442d80c0d03c0d143c6500d4842c41c0180400051000910140314a04003040290344200b19a40e1010010303000003002820504044403824041d100c02010500000841e940144002c0005902d5100c14152820304400611080034501160b000e80000010001015000703081c59034000c50780c16000e21380c5e04c101c8200c8a00700503d0784015800501042110a010341d0140080c070000710300c013203410403041d9075a0182070000c44008010035100810b100905034100111075251103e0741c0211b00e1400c00b4030001d4910300602c244035110f48800078000c0102c2c078000050515525040c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 935158192 1250 935156942 935156983
    0x90406120b0414120703080405150f1b1204240c0e1903052a0405070c150c2f0d0c0203160f0e0c070c180605150d0e 51
    0x92501001c0c10205440030b50720303c03510080d040300e501c002241c00300c0c11068a07a80b152601c2c405580581d03031010020020340d01802104800808a04980003140c4665603200500d01d15103081442c000c4c82110300100c203030b071616040c025000a898410065038000303400415a0701d6100c1e00d0001c4e42802000300b00415001e41c02c00142406094002d120344941e034000311628000b00d070198200c41c036560700504c80a00964080054107840900740480e00030b1288909609031903920082004c5030940b901940c1910009031031403100414040038145560441031504000c0c40911b0345508000d018021b88915124002400580503041420894099500300790150590709844e407500340c06030002da29441d0680c000d0040c116445920390110b039540d01912080c4d800c02c50700c2810f00c001c0e400c41400041140b540707620108000b02c04903007203c1d080402010360010b9185602603a10031681030700c00c1d80c0d02190055158444240c2c001198109071400003224801c0003448480c0542940d00c0e00e01407507028001f80140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 935159442 1250 935158192 935158229
    0x8071509080309190218102301261b070f0606031a0103030f030b0112020c0604020a08190602030606040f0e0603010515010e130605040f0e0c15030a02090406 69
    0x800c1c042d5110380d90075400d81c0c4940710030744500140d81420f41002580244201040b0b60b40300351070340000381c1000350b40100c1c0a03070360749984210380c1451201405140444c401e80c0b40c041150b90084610380c0a6020f0120b00c1014030f00a0b0001d212a40b0290901d000e0449a0802054082c81002540d0700c198005690480896040c20220000c204070300003691000030a244100b2540c030010401412a64159a205a0105c409008900402c400c45540b8100006820b1009000d9024005801c20903180f0000d0107450401b4810008501481c2d070003001950000b1050002000310020740000c440c1d0480b0b409030b0340b603607040e002400034462a04580c08102900c203000c501011611b098600c20401170300200715946654411784000a51103070007a0000b42407022010003401d0600c07030f00982c800901008103c65864500080a6071088501454511380da1002031841e400b081200c800702800580740e040d0302c0b029942480741d41d07200040040300105d80004011040392103940c042401400d03100c000944d40c024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 935160692 1250 935159442 935159453
    0xc09090111040e0a0e010905101a180708090f031c060510020a12051218070b03130201030b04020903121806310803041e08030c07080d02030304020d08071509 69
    0x42504d0381284e0b1440c5c003100301c8100005100c0c040961b90003000404007403c1d0350361403101412408045034440e55500146140540301c1d0901144d030f225070b40103160355900d45500c2c000c008010041c003c03003a690041c1c0c60b081c040e4002100f140c070068030b09651410426145840b98001d46181d621103034200d0310003c407484420783d01081c0751100d144030b45000381550342c0b4404221143c5c0910406800d080180302e000c07801608101c85107a145201e4107045d5040641d86260500183c0c00c103c9029002c0b040c50b058003411903074180310301516a14201c5017103003840301c4000881d6840044080d55082c0b03100025140c4441400e0712440c00340c29600078215951000944a91104036001804c00c02844581c10a04450101e000c6031070401d58001c403008500381450300c0c150303440c2d1704882c0ca088005c00b40c44000200c0c801c1e40501c020440b608112005201d0146440c80440c40d00045c5015101150421300500c001030369181d04150710941c01004e42512000107007018a00074440641200d00180340041d40010040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 935161942 1250 935160692 935160719
    0x1703190203040e010f03110108130c0f0819050304051c080d060e0115080408130302030a08031b04080a080a110d0e0406060c030c08070c0308030c030a0c0306080c0909011104 76
    0x3c44404440d82c16907030b100e41c0e0a14480d03083c0001000d419100c030b003180f142e511030841c050f44814032142e035112525031501c81c0444496503800280da14401c0030710620a0003800c2200c0c0c000840301182ca0030740d690365a1180343d1030703000380e00845215443c03c240010b180035585410740d034502d4005074107941e100c0a080f0300d60001d00301c1e4451940e8698041e400021042c05959102042d59001c1e00c484240307640c0e44e9140c032402c1c0d11a074510390420b07040240200140c0c604221114141d88544401079a03820011044582c2040700781e410081050200418030144001180c0c0440300ca500101580c1c4601c403005050b252440781c04051032040c4154100a1079179648210085e1044405980401c0141d4441c002102c07075410100000d00450140a00300001541100c020a40280680c9008000c0750703c070307074a1100c1a402611041c240c0c20021042c0802c6c140c240c4900c19001c03a80e81003c01c6414a4100055210504050090b04c0780d00d1043c00200d03c00070a4000383c90010000e0400c8ad9900d89a41c030b40f00010307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 935163192 1250 935161942 935161949
    0x40f090501051519110307141002091005090103140f1e060d020f0d06090f0b1f0b0a020c130c03180803010b030c04050409061a19170319020304 63
    0x40c109000040c1a041480d40ea0301c01c4070701070f4000d52500365000710880c1064410000c440821422070401c4a400350284040c0051034030501503021074400c40d580701498011007444407601c00d0f1042084500d150389003c20040c1d5680a0300304036844481c0e0700300580040010007003120b8400140000c100801d051841003911a40c40603101c071201d0202c2410142850000329051038105070816400d40161a020707401c00b5061070000e00d20014140305503a031600fa2134035810700f21140192480d428080108002c0302a0f405503001c0d0211000030101c000458110000d807080e030790706150015030070452074402d114107003a00e80c0240c40c000c0402c0c5a401e1704d40007801581caa070000286030080a442c5052503403000466503800040060850342000009202766201401c2c5641003801008000380b0f5844a00918a1070341c0602c000050290300c2c800c0b240020003010240b01d10821030301c0c0900d0501d06070000c0c0304080e10500d07401c0b20400f040c100644d521b103100c0c600c000e124880d5440c01c0390388916400001070040c7e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 935164442 1250 935163192 935163209
    0xa091b03051c140c01090503040b070c081212043f080603030315030a1b0306060b0702090703050601020a0b090307030e0102160302040902040f0207060b0a082817040f 73
    0x124030031010744500b901000c040c00c1c0001c62103842c2da411288180058003500041a000055400d03055454a02c1c1d40c0c800da01010068101103283c1d0240801a503486000700300c074078080d0610101004080e034152041c0300c21584a00c40c0d10b000b09090100005908180e0340180388500d620b18451011381c9042c50396984909011000d18510044440c0f107050b0160007102c02800035402c42e1580031021030200d0b20740c50707500d41621608544801166807201070403950004a585000c4513030031810a2010388801b07421030040c00c8000c00c00100143c0b03070aa000d6500c203000e4a03001a0315140c03980102d003050800100609264070740c80502c108408040010301003580320392144020251310000590b20b40b0b0b4206c0c4510001c1c0340d003d50030405801c0580207000700c00d20083c0002001c0081d40620003c0760070034202500c08940c0d4840d43c0c015070030308220b5200034002c81001848292508565811146d99007603401d0450003000c0c2c415420003d40105580652140c1001039407500e4803070299001003801c502c00d0051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 935165692 1250 935164442 935164453
    0x2503140109060c1d090603030f1201060e06090112050a150602010506270103030804150f090203010f1a1e0411031605040f0608090703020301021b060105091e0a091b0305 74
    0xe00d4001c200003501111548080502c4d4190341c010001c003901c00070071264050004029012003030040b0b20007000e5004440441d1a50b03035040920003020800c00c401064050142007010382c0e282d0f078000c06540d01000103094003141d96580c82e40844003800c034078411255403440c0d411000c0781c419019081640b00b050b040d616044441c00c4120b5150014034050081220b20300810010f0000c20321406039070758414000c1564040788290380c00d083c03003100d045200c10201039989000010462400303000712104d040c02290140444094024403202510100c208184240c01000d001340d4100340402107034032a00d000402c1001a081e01600c0030b00a40d1007255200d0140c2040068004c510380076009407403d07110300d0214007841c1400c264003038920641c0540800c5a9105140b800801680c00340001c010b02c0010740c02003c400c4d41d2025100f442e141044e04a9807159900303400704003200385d07000c1c440040f0030b0309115070809940b581905407004005444003e4035204c400400c0c0d040001c401004c0d801128407070720442d030b0b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 935166942 1250 935165692 935165711
    0x90c1e05041806050603180c10211413030e060403260a020d0507030e0d0c09060501021b0103050718122a03030e21010501060809070305250314010906 66
    0x30220384060150617800f540500110302d0000c40030407000b00c0c019144040700e086083c030400045140c1d2035146040c000458a9840c00d50b9221440c6040040c40e012440c2800503180400d5000300d100d600400d0000000c1d0340c1520b5805143c850644181040c85c05402c059849031603040120a0040e101d0030080c8202d041010780346c600c4051001c45200c0355060340502181985488103d505a104000a03401c005102035002001d644030007031030210324401d10114044928000d80700058070041c0e405181035400140c0c50095250322540d81d456224000d01e07000035107640300d05040d9201c072160007003460030700c1c0708000124203c0004180c1a100b41c1c0280c03901c03943c100241144403448000b1000a0030850070405c07003000080c1c0a14582c10105c00c0080411085180e810a24000003001c42e0f0a116542c0d120801005041e41220f0742d2340d040b4203080080c1101d1030440d103034540d40700c00802c01818a013000602c4030413040300b500c40a50180d0352006062004628070900e4501901a40c0c1c4182c40b06860080c424 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 935168192 1250 935166942 935166989
    0x706050a0503040b06060903030c0d02010e0f03040b0309210a080a0207031e0909090506011403030906031f0302060a1d040b0319020d1208090606090c04090c1e0504 72
    0xc55541400d80e031414607507521039071446007103003000d001203801440030b000c0c220843c1e9051010f0220004c003000141250140c0301230003400e48943c40e0341d040345600641601d40074450048225003c2d1080c0c145840d9687d04c40c803010601c1c00a10440c0c14800300c903d0032001c0344540c9540c0003404440e00f030b80d6441490740c0352009103604034810244010f000c0b842c40171405410b011a007841d0b48100355607041c418031081e075401c200d102395880c101c822912034010030014404410559a0086440c40980c0194207102000020a05620028003600c6003d0f0101d83c1c00c81307134035051501c03a1014641c0640300761b0b11801e00f140040c186d0103055521841210340200a81d03040d042520075950603080080003044100a001d98200325810310f502c1c10381e00550031010303c001080300e1080a10110704544c0d1080280d180000410781043c40180550307214584001c18048100a10016102030f141503c0c000a0000c0e0800d40c140c030343c03084545070701070002242810340c0311103030300600a002100c0510001452001901071030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 935169442 1250 935168192 935168197
    0x3060b040e16090302090a0e0f03030402180901061e03031d0112020a02012306011e0206150303120406050a060f08030403081b0106080c041118060903010609020d0905070605 76
    0x8400d041502440080c81d00e90000a00e0000b607501d50034000ca52507107a4000c40c44120007100d22040b107a451351120101480b080042c00400307002c43c8013460460506070b0001c0c2c0b01411010012900300e241002040702da4900f98481001480502c0c204081748404c0a100303101a401d903c000d5010400880744071081c02c548c4032083c4401381050703594001341000f561070400250001c5080004566840500d8000381038911110031202100340310340021841d10360001082071105440810311806848060400c0030380016080d50041903407401d80e200e14850b800420314600a24200210b4441074005000c2400459030000d030281203060000c0c456540c0b5a030f00844130300f18a1181c41419841003204202049420000d065845101c03511803805020521000e802c1d82c0880c0c100c0e03903040c1c21106000071949060311030004690100c0b080941480c5441001046800d141200700b8003c4100090010703030359a003944808060f0580107030454440c1c1d0403d42c804024030403000216528460050003043d210b000b03909 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 935170692 1250 935169442 935169449
    0x906110a020918010e0c27041716060501080f03210c072001080112020d03030507020c0307030303091101090e070507050309040606020109060b0603061008130203070602070603060b04 80
    0x900c40c410055091012200000b0721078200c0428814841404030401e0203251144080180180f41d407082140411240ba403c0080d040f0800807040c3c06080400c002c07507851540141c00080c1c03a032400c1183c0300119201d2042e2000044601c0c50014144100202903201c24142c80300c10007110845455804907503501c1c45034000e8644000404000f2113074140c16015000e901010f591030040c1400b00d290703107261580521b50700300c00707035610110805141542e02ca103c3c140106000c8045480c038405035004940002c0040c04081c0425407074400113102640200b0400c0310320400a0100e501e00d550306c0c24004c0090041d03a00464401080144034140c0f503206a8902d003c2d0384803008151650b445c0c0e02e00030740c2d00d0350001c5030031607141c0810710803940b40f562188203110003408a03400100b5032078600e141480449154084d1f4030f00ca101c0c1841401400d07128900e2281c5461440e048c00c031541d44074050480e00c0d44155180c001e6041c0b103501d0700030400650120b55501140d4040c0c60500c05651518000c800c0f5020310300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 935171942 1250 935170692 935170727
    0xd0c0905030a1518050a1704120209040201090e10030c0504020f030f090c04060e07020d170c13030828020a120f050d0c0203040f0806010302130e100f0506010906 71
    0x1000c58040b034201a092441c081489900098515642d26955055001035105417007940141c0130800601403507180000c0e00c0050301c1403541c681402c1c402c50b200a0081c00f540030303010303c0740b14002804590003401c2c0c241c0031b031120342d0410307071203150920100c004c1034101e01080f248412092030000b143d052600a6580b0904041c003a181140d07a8181107401d40c0c8801040c152141c03149208100d91034a80344500ca02624440c00c11081500d001200a440c029440e1400400c0000707a00d1150f401442070728040e50055080111181e841540c0d0742000b0086445400103490881e0000341800d88035405180000d03204603846c0c045a551440140990300c80341450b03c00b80462444031601d0b010144240d030817508182c03040c10058100b014a02202040710700500741c42015a000180500c4481d68480384080289691001401a581964041020118070000000426032952904041c1e030341c00340702140b03421842e01da040280c03c80c61340712200039140aa41040c0802ca03601404a841486a080203a0168402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 935173192 1250 935171942 935171953
    0x809041a0d081e0c0706081e04080c030706060e06090f090303060f13020c0a0b060301022703070b070501140609150108070e120a0b0f012601060e0c0d0c090503 70
    0x20340301c10a0703e5025215100d0803c2541004081c03070011000030305003104500e80203100c218106580509002c00c0500f1038080c0e11008849004015460000b8645c465031060b803064440e120220554030350f0041440045c04181840d40126520341080710aa100390011a91107443e40c890b00580c15241c1401d8800e44043d8104000045d0300c1d08101c01c0d195104040a4410b91002154044110890301b1200c510000c9400200c18901404007070000b203600940210021881c2c0b00d2109002d6030290010748805a492403044283d038040c3d501031060710001d0980795060b59903103c0700e2800754002e2500d80c1c58400c0407980c000c007017102400d0045c40280f0030540e4401d01c000d07440d070716030064038603400050090040120041207210140c560028002400359a0710040c541040c991034091900480106110984031000004000510000c0c11244200c124010809044044002c040d0b01600701c070b4002c480c01440c020144444211180e00400440f40b511400304000120414125551002c502c03550790f043d40003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 935174442 1250 935173192 935173219
    0x91b0c030912030507150f060801021908090f01050702031b120a030222140102242701050c0a11011a011409090109050717040f06110c06040809041a 65
    0x100e4a8101070b50003810180e042c1a17103640ea98256504a08410704001d85a00e003940e0614030a0251350081c0c0401802581004404042c0f000700c00b04091001c1e0130000304101280488905100d0641004101002800680b8100c040a983c0350303c03440d04083d81e220b6240c0381510310b00010510501d1240c4140415203400c0c01c4101c214069000724a40d1781000c2e00300911403c003a070840701c0e80710052490720a0303088201c1c100800641003071240e15040aa040c16000d13901580c0094100d007980c001441003d003564440d50b0044e09003440740300001c504441d840d09040c0058031183e0005480a44050f40e81c2081c807920410003103007070303d4803199806042c40e024031411a0350340c02040c02c8841914813403566814001c440001421006081e0320440c0c41ca5a52702c1400b440320350094014024101c03c42454006040c19030301e07109120004040a008a5610340d68000c0f0711500700e00303c0d003c44022204039002e90400e401c04a40507400703050180e10851030051f03a02d0490949040c2003122000040442e0600c0c5075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 935175692 1250 935174442 935174459
    0x130519081509060a0f0e0a0311010609060305070b0a1214060906030d12020a1202130501110304080d18050904030924020c0d061103010b1801030b09070c0c050a091b0c0309 75
    0x24080081d0322030801182c2c441b410031183c400a4080c0d0f50305400c203000d4010701703800c4603c50341140074518113082c020b0004c1600001d1000445e1b02c0603003c581c0e1000049012540800940c00420500b41803442001c40c0c02c050f001d003035000e03103002c4500300e0f290384a120401d41e89c0d00d5180001800300f20038642c408102c507a264003410303850445040c010103092804104074201e0340300710001d01100e000b0800034071195911a6011452045250041d4a441e0a01e03042c1591442e002006801708602c046010203005083c8a0040c01800003905100a07418540f40207809800d0900a2180c2e540d8050440b100b45040f603441480e90032455006824000000b0050050701d203041102520a1034990b40e4450035201030100850091110502240d141c419002e188580f500203504d6050405043ca502c2d4035550341d420481c01c6d00b003038403401c000c14000b01c0f80c40c000e07030880f0440e8007a80d4041400500026031402d15082041c4d40004212604070520714088107540240c2d641d000940051100c0c5002e00c1446c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 935176942 1250 935175692 935175701
    0x1503060403081906030602040801060b0f040b03151203090424050f0604150c05100606050a1d06030106030f0501290f1e0a12060e0c130519081509060a 66
    0x45201101c3c2c0b43c082011040c14040e10019441140c450780d00040c00c003d900001e11402014100380b0202e41c0ca00004030607403100a000b1405141b416400010104000071200190034101c00c8001e000160f4025194106030740340d03042101c03028040c50418081006000c0c100704d80c09a1100c400e41018500303030800703042c04030f012520400706030000420030010915038240c41000307039041d803180d0340c042e506810fa10300307030303042032002d141212455081413807d0124a4203c002d03220010342c3c601d8024112482c940000190700035090000350401e01c00800800ca03d5415044440085200300080c40340c3c7c0d0b641e04000f9950452200241012220341c0d1000d984540b00308000d102500c0d0f003002071400c00c0b105424000300b25400411101003144005040300c900c0d40c109050708426400e0400400c800e0385002500042e400008008036085100040c811601c800b072200ea503c0a03000103040303000b031080804c90320001401c031790050598522034203103110342c440e524030342403445006032001511541e00c41064100282 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 935178192 1250 935176942 935176951
    0x906290d081602042318150601030b010302070213061d0c090402030402030f01060f05040e0c0a091d060a1406060f0a1b022211071a06030309060c070e150306040308 72
    0x113403200c0c4104107140310441720b202184400c101003c124101384200e401e00c00c000c9901c0b00320f250444900c1d40041d0102e210042da100f2001e090205d091000f00004800038401e0b428020340c00700200c030000303d403240c2aa00100035100d0100e112000d05c0d410307040d400840401100d40800f0740c0c8007081075142504080e0003564010f4409001c64001a01c0c00c81141e09507105500903190360035803c2c00030001440d02e030041c1c44603090700502a00d24198030501080000340e1a00541007425103c0b4401e00f048e1030035121201829000009460f01d0341440c03510750020b0150214858181ca29440100e003191811030121041c2007503055038540b4040c0303c00c05c00d44030b14003000c00d900b041c0c000c00722400000d032b00c450040702680e40c4484411089400c05900a10844100d240350004203441401036000151140d200098440c2d07005901419590760080041c0c42c40c8600c5940940240d000305541e84500d00008505090307030800f054241041d40c58548a49610071120000365040e03005001040c00f29003c0c1001c584c11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 935179442 1250 935178192 935178199
    0x20c0604051c0206270409120804030203210a0e15150a03140105061201060503210c0a300909020706141501080c041d09010906290d081602 61
    0xa0042c03a000108260824081c9000c60254085050700c00080c50b1225078505d102180c0c1041101c0d01615000103103424803c400040c484400c000c242454020410743c0c85554004210503107a90045101d071039070110540b9400380007820b191103002044070100b0642c05680c0d14061a00480e994010b01d2880303a0810f00c1e0f03850300074180301d5022021448584828407111030440000c02d050038440300f03008035070520415480041e454130005000d1680d004c640d1200300094240c1c0001c0100a00c01e408d1624172036182c810f45a8813410b44140208130a4920310b03034210001e1850003420324514640041c003413000307072000d0001071550b42080c442c04006901601d00e10f809510000750000d0700b550900c180d808244e0b8074004003410f81d40d201741ca540c3d2008000d940b200c96400e103d81004c0c070b40008610a400e0300000c4006810113000024845c1100354080d51405421003c24000700705400e0035007000ca035201c0b40030354402508040c440070b03a040200e448a00c0e20f078400000c03458140c11300754810407404000e0040340d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 935180692 1250 935179442 935179489
    0x108150415020a05040321091419030b060102100209090402120a02040603063611180c0d0b0609030714031f0209090717010306050709170601050f01020c060405 70
    0x20701e40c0da18400703800c0e0b42d5641c1e160296200c1c158289a000702900b40750250441d400a48030000032980191013400300d0707245000c9100c140004000142072802841c01000c0e8050250300c00005105905810300d02400b000e03001d4589814410440c102644628640181c01c8240c0700b0200c0c0040c203050103182c03100c800742e02c251002003907554005401d40b0b030581c1c030685519864440c6815918114400c1e5445a03130064803240c050000117401c10005200800007800e0600c41210b203ca00b0303200e660b07034520703c40d007610300f001c03070300d00c0d102c18003002030740001d8034514159241000b0700c0b81c03030f0800c10201c400d14a00100208a05840c0c1900c1c170303805c2202580780c55058001c01c070156600b003500220f5542d442d152240e016850707103000c0d0140301c060040280b4440400c640040c01141d000d80c81403d150649412150204082d0303620102922040300a42c0a00340030314110b020001b24000c08501302d416580100c41590441c40200d00490317891000880c2180d21800411042105141000380e010001c022070030301d00d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 935181942 1250 935180692 935180723
    0x340311030f282d0606020601030609060608071e0e010602060f0c1606021206040504021c0816030c0c0f0510030506030a05070602070303320306010c060614090901020301081504 77
    0x102681d0b149100c10001c41002110050903003e0f52000704212140d01c08100032903480e003072009642c0c2c9810310001d00140d940380050401d104e503030f421900c050010a4100c409440d525424190801c80000350200c2600b000f500c08149003442400740c904a07040b079402400d044c1c6a035050f584845101808079851030b00100101c1600601c660524900c2d04c2c002d6000503125070a124041d41e202c90020300c0c00f0303c00d514040030000180d4880c20480d21210300000040601c4900c0d1074607031030342d10078051f101c41d040c411520380c10304150707002c1d040c0700009110307503007111040f0b913540a00c2c120164a801020f07440492102d0300b50b01d807841790f84996401a801011140c91140a49032030742007a1a5070842c40c0180c000c45014014160403d07610520031042c1c041403440305a09696000540e40010303240a01c4040000208041e03a00c1407003940201a0003240c104070312951464001104160440d4060080d040040080d41121042c42030fa8101c5080a01400308101c0d8032200443c030040092080328004800a42003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 935183192 1250 935181942 935182021
    0x9030709110a021e12160602040f03021809030a230301030c0e01080607091401170c03060307080118021c0c0f050f0402130e340311030f 60
    0x8019451805800d80d1150801402410511180c0f0402d007030319507211082c0c80f01c20001a1004010111485d00c50311080d412141e0b1491a1a08802a0000d80041004500341202140e0074046910803100306002550380343c464440c4400c00c82c0e0b880303100d0f0270a1100c180f10f1402484105e201290220850141105100300a1200d41083c1c10075150900e1a00c418042c1125125910740035200c4080201018a4010001000d0300b00501079003002081190500815900600d100300078840448100400c0d450f0903001d2141e07a410407a40c2510034401c107840010800c07418460445614145040041d101040d602404003280d95882c6044004800303d0b91940814041109a4090140341407040144c07490b080030003100c00340240c80644281e00c1000303a0030300e80e80041e00aa04944c2070000c00d0a0507500c0a5035031401456070700960aa0040400c00798181a4100686412014503601c0400a0300e5052001d81d03824041120700e1036a1200c0d10010501d1039207541c950100820041d5903140c81404002043c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 935184442 1250 935183192 935183201
    0x170f04080105010e07020105100807051e040c03090b011d0402120c1201020d06150807030506010e03010e15010e1009090807120c0525090b0a090e030d1811040209030709 74
    0x601c11054085090250341079081c05906e40012600400d400c16608220300c403a09c44825200b204c0c0300718800103400c2d590903520001e40c1e060751402001005a00c1d98fc4101401600049400700c5a40c8248070002c90140d07041c84501103800b0300104090407680e41c50b420f01c031031182d0344030301110755106502c00c0d03011319aa00c1c401c000120001100150310741c080c0c40008030588980b82c004102d07000312110086240ba0344164103550148035031070081816101e010050b16006211140d542d095402e1840040380c104000441d10407001c1c082100f07d20340d0b81d94048811001909070740207000031072084010009403000d034010314400790040d900107181180341c0d9156000003110484140103e11502e0542050002c02d0010310110000d03440b0422030640341d03005410140021b405480481170b9909010708003524ad020244020388800c8208001d00c150b221036141e80c07900954681c041040c2004d40d0800c0d01c0341000001039102d42c0c0b2400303181c1c1840705a410003001e90841200f03180c162003808000074181145004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 935185692 1250 935184442 935184449
    0x14060c010e0316050d0305060f10031e1a0405010f03080a2706030b01020a0b01061d100203090a06111b010c0b0a020910030e0d1413062604170f0408010501 68
    0x10086800740d6850400c1c28450b49070683d05c24181b504081010588030001150b40c552411a0340d15111030510f030050f03000380b0464441c175414a00d2040c20044075082e5a11820b2a140d03003400018a500008041006680e402d02501d029030000780c200700002420207018003d850180e042040010b00c05001c1000d03006000490400d0b500080b030b008005841d01841600c050880038400b43c2400d900c01e0300c6440103400103104000803c0070600d0700c3c11b50740f0000e54000d15001401401c01c941500d80900080d9a90004140c1601c1000b240b0302c0001c0307182c0602282254602d140010706050340c10521200400c06120261506010010b0340c2200040d00c8851014803401e508a07005803500d10a000f4020000d0b002d0340540181850140313800240d001c002407025410825280c282c60b0500031040310741c131600070070320032421440d448000441d00c15000040030318000200e501100c088071130881c1e9207502007800da034054102c5450400060307400e00c202c4020655261b848807545d160960b20510142101c60036031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 935186942 1250 935185692 935185717
    0x15050709030201030b0303161b08010513050601050d0f0602031503010e0a060c050c0a0204020904020c0f01050601020d0c0b3103050d0e03070206030c030a060e0106020c1914060c010e03 81
    0x2014070031980c0510552100313101c158021800e01051240d8000d00c40c48214000d801008101d40500480247e80c1c002800360404200902843c10880d481d64180e00305004200c41030b001d58000483c05080150070002080d400800e841d1525a031519401e0080d8005048a0ba050104803180461034030309006d9032540890000c0100702d40d85040c1461422034030b11300d9000040040c10000e20b04189000181c52403100d404807001680d900c54400002d0003441a00e45809460042c038010b8010380c0e81c19032002c0c0c8070f0902a0241c42240304442c50480703000d41c580f407000302400114408a481100f220f081c00106c100c18501464204002111045400d06030800403000500005030b05500c08036540544500814810700840c01d01c80d00d64001100f80c08003c102804520011000032014881900000018100b000c092410355864050094551030f440f1409401000100088005680600415030071070b17100015210404840a00300722090b030084c80ca9010035900d60040052a040c240020080740700c858 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 935188192 1250 935186942 935186957
    0x215180705010212040308160204060b0316034d0903160302010906260403121a150a02011d071508040b060103050c0c1e190f0807150507 60
    0x420480c50056241c0020b41150800044284c1c000700030015602a80d500080564035a2068030031107403040c6400c04041c0d480342c104000003500c010858002c41c094410006c5030420649042070603420b84041d80703045020204203c03c50084842008000100da8030b100c004100b4a004c2040c004451241e00c1c0071080c8024030025096050f480c041155104a0080b040140780aa25540002e0b100058910891080c00680d64401c5001400c00c0200b1170b00b03a444210210440c01c060400a01d110202071400d5849444e044900c1e604a000340e540c0781403480021b010200003480c1019030a80c5801c1078040809641d2161340507030003440d15607020000b50382a1002003400910b00045400709c20220070500c4180240d01e010301021810031103c0a910103c01e00707010075551245400e40c100b41c4100e50342801140600b100068020741412143d800c040030f04411100e011076800c020305540744c03d441c4000d11442c280c0c000e6100003005000a0012140552810580c0210b5101194152001101c0800010700d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 935189442 1250 935188192 935188231
    0x1b0a03020f0628033e0f04030803070f05091012020903030c012705060705130510180506040e06090402030a0512090a0603060b090f03011e090210080f04060209010215 73
    0x1845403000340710314144c042d20040c0c4085e055540886528840d148040142c006810740800f111040b01c01d441c03480c4003150b96459590611050300c0d0400e44500000a00010b6906003c62050007602c1010000404607041070428007020b40d400c1e04000c00403030f0b4094003484404010760342480a4214641442d0006c64104c05c4014000040f000851b0442180d03a91848103401244e80020000d030301030614107109541e0340320003000800805c07181d40030542c05264510f812004a604c50181002a07892881c200c41c8142c566003089054010390090240006403240062043c2c40c240d0704654100f4006001e541c0c2c025150740705c6a0400341441454250910700044999580c05c044040000404451a01b00400b030b0903d4289441842a0185d40e0311030b541114000469580c00c0d407110945680c9500c03408001401000320320080c000d5008140d00c50110344410115040c041e12481e8030078266004101c00725075541d92124029005008882d046208040394000d034a00180d030014020381062080034440b002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 935190692 1250 935189442 935189447
    0xd1e0803010302211005060a0e01062d0c03031d010e0f0f07030327210516050904080f0408030a08091b0901270603060c021b0a03020f0628 61
    0x4c100e0040c007519981010220070181d020078101c400c0e10b85107002040d26240c042c0000c481010a0300f144544030000f0300001045a0442000039001d42c3e614000d094042541100144820341062645e003c0f0f0a45012400044e100e0350000c000c003010114032406001009009500315500c40511a0040d488540c0000c1c104004002d030310654540d82c0000e24606085590003440065082050712105506c0d02c0380740d003070801c0e02032000003030044460007840380c4200d58000141040030030f00c01e9409005110700401e0100742d042488050391005030080d01603454658846078160300007170500150744824080030821810030300040c15224502d030759034007540c14840e2441e1b080c14141152103c002c0c011040d01c0e80a5101c400340641154011000080800c03004081c0c040b40245d030940e81580c4c20b140400100400089520025100740e00342d00300c840e03141021804d0008800303040ea40d40d034890032045003080140340288590700140c00181c6090704007a0401c110309240000e007104c121811b540d1850045500740e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 935191942 1250 935190692 935190709
    0xb130305162907060c0e130519090c060531030b0a05060a090b03071208040e011d040816020907030501090f0207021e030a08040b030a060504020f090d1e0803010302 72
    0x500d05070b001c61100d104410a8002d8852208018541500c480052099074000c600410482c0409450000f0aa4403150074000405040307a140840001064002d40071070b000344141000d40f640031840310586401c3c620180e4503900007030181c540304410001d21810803a0400e01480f901110607201003280750440c03a007034840711001060400c0c0d080c6040100030307080e51390301400b8040b0341a8680005880300030f0000b081c20181c0641000b003060340032251241c03c01440100410031207400380440390361a43c0325450340c1c00312400607481002e01c4140c4c0c004100494040d5004162030030b1807505c0208650265800b1070030b45a012030306030000c243e841004000242860044017030404104904525186140d8001450703c4601c4000806450021400c080592420000c040b821508000c0786500d0720b035503280030300c195441114290704030303414220001102e040c02d000707503001d90070106103840c24541c0d02805c1c00301c105ca40c01011307103646e20310200250b418a05c20003010405401012026620b6045005218518 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 935193192 1250 935191942 935191979
    0x60109020705030715020d060e0411030a021813120e120d02031204050304090612060b0a03030f180519030302010b060a0905190305030a050c0c010207050303040b13030516 75
    0x1140104400070000d0008412280307a50f90080704010384520101500000303001c0d214000750403a25001c004900d44c280c0300040c038881d61040201c1c1c41025900024142c40d80082c007002034000c8034009003440c00c007103118200c41d4450311550300c400c56484162520200d000c0c03001071040c0480c08040c00086241405c15032524402c907814002e00480c1d1445000a680344151901054038691403400714003003140510444008100c054028072455072103000321024001900c1b0200c1b0308030b280c181e010701d090504c0000007044035095150001400c025202c2900ca803103562040e4041900600b0011440307a50344005120000c4141c00142800c81c158640a402c50348201e960710b00ca00e03000d004081e000f1744e116004400341c400540d0800c041f2410103080200e1683c40e904000d101d800042004544550300c035014091400c14039084582406040005a8891546001c2c3c240c068004110034401441048010660f1040849054600c1542c0b41c82d100c3c01e15003400110070f03c1044018007004848203e48805552 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 935194442 1250 935193192 935193209
    0x4150216050d1103090f0105070c090b1c0209070c0519080a03110906070201050a0512010e0f0f07020a030509180a3303060f0b1e040609141f030804080c030601 70
    0x44072000080d06a4174000d8440b083d21a89218814680a9204038241c0d9112603111031281c000e01d4803140004080c0c00c0c1140680c1c010404c8921046c5101388401100100b240c002e0b2039030800e9155440c04503800568080c09035898421002c0006101140402901c1c80c0d40c0a4280e1503125070a88000805640801c84614002c580502c500c10480d07075181d0858001540c24200310760f5540c2c00130000c1d10710303005d000510b81c1080003000001880c0c5a0180002d80f04003450f50f190b419542e142c1404407400c0c0ca094a0350001a80301400100c0003a004000900400a000340b9a00f01c48202e01c801d01504802201c04a2034552222800c1e4600c025401da8804d485401c4000744200e0004814004400301c41c0b440007820168882580441703814155001c0702118a01a142c400e007102e0803400801c0903250840c0d001d0103945890b2000604041512074142000160140c554003900c804080702000b40003150641c84900883e10f00000051815000307000615490f4040c0c414218900e04040c18802c050340148030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 935195692 1250 935194442 935194457
    0x1506010e1e120a1407030203120a021504020307050604140a0501020a03020a06050703110f1308010203010b07060e07090e0a0501050606090a0b0a1107081605041104050904150216050d 80
    0x3480707014001c0d01d2425a005075903003221100d541031400d03e448032101001d00541d201100701083d9110108690003602d0003078086403c0d030f42602c2d18a038002e21903110b55800681042d0b0f004141503482000e200e401a00040403940281c0d211000100d00c4e501c02d61003c480c0060f050082c0455041251501006007800d002514600e041914003948a0140a034001c102035a80c10010f1450b501903403184c1101c1603010711254881402c207a4802066010404860341c840000350002054481402101c2c10303901206e540d2403e2450380e80d10b081c0901140340391a4518000e0f0f5501207000032180c03140a105c40c1c3d02c1801000c41288504105017100c50162445002d16000c100c0011181c64065094007101c0f0b003140031f00c0d039600f11094101c8030326140f0324042d000e600070f1140015020000061486134203001c1100da92202c4c0d603c100f000101d900c485102455002c040c0004c004920f05035070f00c2c83d4803a026001c5544941c40080210080b80c0c40b078803044e2984440c9603801c0c0f0034000c1c02c0000b00030750202030400c0310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 935196942 1250 935195692 935195719
    0x52416050714070306140a0e0601210204020d0c0e10080103080f0c0109020d23060610030c0912150501060f021c09080102040b040602010b010f0f0f0e031506010e 71
    0x50181c4110700000d0182002c10340c107414200003c1211500039600000204030040c2100c801d043e5070300d01981e19a004504100d0f4649940201140c054100c400c82001015410303003410840408807444501a80c0c829030a01801c803903034440e8081ca0000d07200c5c0382d84041c0172a0b001c40801460000e003010040c200a00c8000510000d18400d089944541804941c140c079003090004290142c100c000e0f000b0b410034a042116020131440350310a008000742488920303030111014a1159440b8421614039a000c560400c807c140030780a58010032a98031145000040d403903c0e0b41186000840b2800700302c0d036640201004125051341842884d026180918103864503030169000250740b01c443c1c10b040f880b40001207128a1416000301402002048043d009541700c0749d030391300f040011b41c00500c0781e440554200244002c05d58424078040042c0411901c80c20315010f0b0b102022280204650030700800d00c0a4921000c0c0c00c0e0b0350411400c030b0000307a01005c900d1149031603000101350510108010340078107900100318 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 935198192 1250 935196942 935196947
    0x2512030806040f09050a0f02130c08010b0705150403110c04020403080702040f061205030c011d03040e07050f070807030f0806181e0f1006091508090a052416 69
    0x454004000701c42c04542000000101402040758120082184c425050001d042207099180501c007039000b00d5440810b61400465481941d600005010001d0158401848916a000080d101c440c0c0200304580f180b000a003407540d5008030980b01500031404165542c400f0000801c03027250038200c00d0b9803d5080c039166035244213407070207503540091050703840700028403a01d10540d00407001028220710303100030414541046500c0f0344c0300d4204c5031200d5082840b02c1d40411783c098000520b039081c000c0118600352a00050382001d040c050140c1042090401ca2100d500d60a6406004441d02070075445941c1d40e51885c000e0006200c00e000c40007032092400030007880741e41d81130400d0003940b8074208007010399440082c4910901760350144042001105000d102106400010043c4503091501c98403100948030381090f1200c001620079041900c1c64000224401446040300c0d641200c441021500f4030011a40c6160038070401c13020601d28503102d1048094928010f030f00d91500000400310f0000c5000d00c82500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 935199442 1250 935198192 935198207
    0x60907081f0b030c041509050a05130b041106131701050c1b150901060e13080414031f0209030d0c1e0c0906031a070810170a05251203 59
    0x200c01c05941d40b94a40c4490310240403900c0c80042c010300403c6064000c001c10b40c0c0d8500140500b250140c6001c0010b01d060025110f020301a000c03070031041e0080407031940d60590041004000720340050301010148056181c0b81d0140c140c0504040c0341d82d40081c1130103114002c0ea8201811140160705003401d1048460300d0708115a9071401012045015481200c051850160a4011070039251400d104002c02d030441940507a007039601d0807040c00025201c03022000c0c80c0c20442007025282c40c80821003040345402c098030030403940700e0140a45401d85903c1d54052241941c600070301c46201d80005103103446260a2141d90a0844e460800501007030564403004001007080221a4820a4500c1d1180500c04118910703c02004511800e03c4100e44038070b8a4900c0031165060098403107440c0b408101918056003000d8480c1c000c00c80c1c0c003100c080c5408100702c19140e1041404595028501400011810511528941140764000b11540d41100c600c400d0844056a010224203101c261842c000664001c42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 935200692 1250 935199442 935199493
    0x9050106020109110409031e02010b060408150c0703140a0c080a0c0203010c140f0a030213030c14060301030803070825110c030106060503150a230a0b18060f07050f06090708 76
    0x2401230101800f2800707030b00408188011540c85071011034001400c46000844205c00d801504178001c050704c0d420b41c0c40e0114014100010003080810307011140500c0410064040c0d0503040ca4012114081c03901c8150441d4404540030001540805c1140107505007401500514250361501007010b4240b1085041c0900800c3c440f5110f0890000c1c40400491094059410380458040e45101c0c0583d0b13450104032100d16445501d0708400e0341e400102d203d18120060300c2c1201d4000046070301c0d658139503a04030b420840040c010848d80344440f00442c2c0d91780c016280100304210307a80350f82c1102c0c07612009203860610101310040c42a0304050051103003030703848010750340c001c6044d9018070b01045000c400540071040c4c0741c2144e41903114101580514042e00078005c00740b81020b0380e200c0c060356210100101c2038442e42a040003085100c070500f00e050304000000300b0900050340d0040c0c0c1040c0d810b681d4541007100c1080001c840e54000824448800da050100a00804154004100402c1042c22600e1044a03090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 935201942 1250 935200692 935200727
    0x1050a060f030917030c03011d0c0a03020310182f07291501030e0a0c12060b060403030f0807020102131701090b01060518180c030606040905010602010911040903 71
    0x1484841080b480c2c0c4944d034914680046040d40746c0c90a003000c1d075000d4100744105107450700414078102ca42d04174412194018801869054a4000f254000b0b034007035072001d024801b62420940d0005a104c6007240c501c10104541c090202d104280c600d4040b40b82250703614011580c410b2038070303a42c484000450840d001f103a403000050754040c0307452010008503800c4a40c4114596542810044000000400e00320a07241c00d0b20104164601090800c0e644c201011008042046249090240c10043c4d8262032050380301c0e45002c00c034000d047c000318109400c903900490202e800b602598507081e41280980d40e005080b03100850a0035407090a03000382d07201600c12007040010560780d418400c00290000004182c010030840390650f9903180080560380302c80300b03611000300c2012101500745012001c40800c190390500586007a100e1991084556001901036a4003c00810000072100d1a5004042c001c0c90590000a0494100e06281021030402080a0b218615205402c40000e400028808030001e422 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 935203192 1250 935201942 935201951
    0xc1c03390207030b0a0615020a030206040318091404110612010510120c0e030d030c0918090c030b010906090506030a0335060a090615050c0c040612050601050a060f03 73
    0x90820390819942d504043c04e00165281045003d0388207412031000c45150b06060011501c407204100c0c0c5580c80130720700400680100010502081c800c011803100c1d01c000603090b1000540d20036401c412603079000342c04480729000a003040140900c8490810241d44d00356900e5181440f00d0030305c1900c58005009061280145003401d61010740314003421511118120000c000305803e068000e410031520490b524400d102d68018100c0c214428045d140d5650300503101e0705042030409035400701900e01ca406243e141070740c0e1813280700842e05180400e030045000f8415006254105403004040d00c1c01d94111740d501c42d0510f001d001d900e40340050162415905032402a00361000100041d003c03146280749000c20b400c4e12a50304814420000d00c0070302440301103ca02d9052035448520505440d52407092400c450700785d080a21305503010704000c00c158200c802c15556007207181d400040484002c0d406c44e100c81d40e46c011608040101c204601c0340507010490355142035504c1c00c100207005540c0d4440e810209030b190b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 935204442 1250 935203192 935203301
    0x1b030809030409020412110103020901051b03160b090105010f0501090e0a06030209070201020d0b031b06030a09120302030402040b0d0203070501180e070806180403230c1c03 76
    0x81c02928050500b03102e055544603542e101d40040116200e905451040300720f01150407540c001d1003120884001030b1625401c2036100c040140780e00304640700d941040d000811101c12040c03004202040b003503100301c4448542c4c0c1080d05201e421076005030000072910518100c140440c0e0b0b0011072400850340f401d4443da031030303685030f014400240c0305680c0002d410080441c01c0c030801640640107422040c0c102402001090f003071800701741d92082149054201000c02d516626900d00780100250313409402614080b40d042500c1e030b5010404d04015601500099002c824441149094001c00300b2195040360071070000304054000a480d0420b51085034144075010700640b80c1810041c0c071070b000504241c40d0500d414a805000a000000b023252003d01c611014000801031080e1603440501480d00366070f804101c01c0003130704241c0c0c08103c40c8a410a2003c3c0034031003400481300800c07013403800e003051012094400024180190941d241000400054a01c0c5a9039820103050a42e40428803480700c00503403001d400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 935205692 1250 935204442 935204461
    0x903031d070f1a090d030915090e04110d0f030306030b0f0f010b0d110705060a0e07080c0613030203010c0905030f15131b12022103033706151b0308 65
    0x1445031107600600f004002d002410740041003e0201c035513090742301404019190085400041f607004d4039403014458008507000c40c0308100c00b040d082c103002e04400d80c0101151109001c0084500044001a89940e4280200805114a15002080d4811110050402d5500049290300500466003021804140805d81160b02d03080b503200385107960f01c2c0d03039038404040c1400c64440381c08460141c181410440e42d40c00344070000482404580031400030b85848082501004060b5205495441120355048404005680d0030300c1000004401501c03032441040c1f8140a043c2402410048103846401c06000001328400f101c140d103500c8611310301c44402998961800084600354040306070102e01c0600ea000c2100d0021a52032000a80200e035001010301c902c4140c0418090741201c02e44580d0030500108010007818040000400b28100c1e43c95400f0989032240c0b40c0038102000f00040007510382c1c2040188001c0c01d0164803244030070f0b14100760507102c0001000113a01c00101c0050403c403082d00010820740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 935206942 1250 935205692 935205697
    0xb0603071205030919081002070602040e1e0c09010903020d1703160318020d03110f0f0d0e03281a04201801140f040903031d070f1a 58
    0xc90882400c201141c581000d580e40e80045180c0d60240149204014011003801d2524080703034036074801040c0c1c11010019190280d040700004541041e003e00002c43d109066502e000d20035641c0c01e5a462014030002c160070300c192000361004803c004104640c10060740c5c0004104140c0e80c06440c1c69460034810710300182d05c02c095035a032042c50007021040c4149510b19120704c0440c48400d540030311100017403400315902c000500b00000c0d40300c20a011040b002901415841031718104a1040c1c0c0c2c4882c0b00012611b0401c0041c03e4010b485030810180e83d809207030011016000380c0816801060300103151114000b40141c11402c4c801c40030200049442008813070340c84a003800160380c1c01c040050034649440c11107000101d1a100d03001100702089942d50030000b07500c18081ca180d20354018140d2900d40e010740e6418900d02c159802c014654501c0103070751514010411402e21940d000500c12943e81c2c200f03103558802c140c01c1c04983d00a01c000f00320710300301c511690b000d0700e50000340b092611081000741041403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 935208192 1250 935206942 935206949
    0xd090302062a0d0206011e06050901200109030306230f0f1c1b291e1215120312060a080a030816020d090b07050c0613060f050a08040b060307 62
    0xa01c40c803ca4240c140d0b502148050490707001303904404070215020302001052440f401001d00161003031040c1e4080390700c074030810044801540740140000d0003041c04a403d41d1407441e026004280c980a04000b009008100d00036210f9054014841c40010000001c01c105c94003030f5070364400e6000b41d42c140000c1e0341d452448903400b41d40c41c2420340c95410034603259000341030030310101d1083c900307020300040d8184811340802e400c0444000419207221040b0701030207c503001203a8031170050110040052603048808005c280e62005812881142c1c0781003183d90740303100403d81800c2c0c064040301c100260000d0340042691101c10002010380259544c10780803c00c00c41c0581c0c0880114856152070800389508030340d110f8010a210304001130454055402a071342c5031000c9202c000051030506c000c0004581d007802401c0c807103110350250703808242d074440026503a4010b6a1401004090007908110301500705811650051080c02c02504281c0c01d424003400c4021300406c0944004e80c000c00003082ea41d0305000c6180179 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 935209442 1250 935208192 935208277
    0x30b0a02131518031a04030203040b270d0b040602160804150306140f0d110604180f051b03040f1509050f06010503030a050f0712030507020d09030206 66
    0x440c0c2e503500384032101000582101c08645440381c01c528078010f41d031802c0181c1360024144900c14640118111100c2c0c0014015001c5000c1404003160014284004103081501011218080c2e00e03280d407035241d207c1520711031074820a900c2c2c0c080b10000f40200d84096000d50040e4005844e40081e0280c0c0c54151342c4000010002030000034041642641940540e01d0309040d41d070704114054035000700304a6214230141c0e01e039009600c582552140d10300302982c0c2d03962030700c185414030842c08541e011175643d030000c1e0003c480714440a03445001e0704005102d01799040402110612079810111006a80800348036080d10310843e0020005090000004c883c2070015807040e12403005003048001d490007483e00e4481100c2c2c0d409241c69202c80468001407090684034020003440c5044e04000098410760f00500c5141040c10b418007442d40420461200120201107949001c81e0929140b20001e060044150340d8400344000a4400e00243c1c68000590302d884207050940850180007483c0c50751544e410340c881111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 935210692 1250 935209442 935209477
    0x513050901030b1909080d090206070605010e1905010b09041832030408100c091203050706050a0203130803060f060301080109230307110619020c0a06020102070c030b0a02 75
    0x2c0050030326046100307006000303140d40b2540c48904484c040d02c3d100f201c00381c41c201c001c2c0130f6042107008607400080c82c540b004010526003952030b41d0702d81c00c0d28002d900602840740d880702000341c0442c0b20f68040b24034800400c1c0c200010340c10310041d403805000c0c0b424107900649d902c00d92581ea8030460b070716800f4402d400500040340740314030700c0ca07003841c83e80c41c0f04032201e00e07100c291348044a022001040c0e8050f0360354000507008010101245a0090000c90307200410072415000000e101180705100190300c500a0b80c1e0b2a944102e039041c103e00f951006091010b81c18070401c108148a04c08011060845502034911541e0b626207000007130180d2081929268010300020002414003815031002c040c061250001c80d00d2181c1c840001008542810b642c808250070800084000482c1c01e0701100f00f0701401070070a42001c9a14004110a489000c14200568040c240f40c0320b03185004640400100340d2440250f160840e5075880c21a940c0030303480010030010b611400704413101d1450301507030b681c444500160380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 935211942 1250 935210692 935210699
    0x20403080c0609070602150612190803160e030309040e10150801060614031305031608130f12081b0a0b0417031b031e27010c020601060513050901 64
    0xe40780e02003030301c0e002031903c0344000002e02c11b400415101d01625188401c48a20342d2000140f00e49600715a4018906020305150a0310112002c80b112001500560301d458036407620003044060340d803030141c0c200d060000349038001c5900d940008c11220040401d41c0c0c0852030100084c0781038a40f0002d0300b041d400642c01d102c9106416454400110b0413681090b0003840b070a42d0728982503e08805d0500e0faa8030400d400c000040c1c540000c4a181342c811440348017103900d003000c1682c0d100340d071004c180300880311814000341c031444404140c40000044d0101030f880312019031801c2d84401d5a0700010704000c11a140100d010107a85d0300600003009040c00d01c000741c0703d4002c014a440c1600040c100d41c103c58914007040305520340941da1090320310030080c45c99080003001c0b00250524427070b040105510340441036a185c01e0682e800320081e06000d03052000405c50385e21650061411b10720500110622681e15007415540c4195000400e5070448130541485660b861038030380c10103003841c5030b50002c0e50400070020000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 935213192 1250 935211942 935211967
    0x120d02160c081014060607031808030a0e041b020316050c100206070f021b0105071b261222080d1709010207030c0803102111190b030a02040308 63
    0xc0f00b41240f0094108456400308005000003181600c2964002c8403c1c09188000703802002c0315407180313400c4100103406654815080c0d00d181d0050360000c00043d081048842107003045d00803001031286640308000b034007440300c6000790f0780e000711100c01003d01c00000487c01800b00c10300c4a451143c9000e800010102980400030f0760702c0c90242c5600c400902041e010644403440414a11040c12411041d030b144000d150004658a40088030b05840100003180741071207030981c003800c24002f040c0000e00c41c04010303c400b1107000d010000220394481c68001c0341032000700c0440c8404403000c61109140c01a030001180d5215804107182c1e030484105032007514540084550040458a41d4211918a0001c80ea0310451254280c0c041e00c0001000300d54500041320000340840051070303124041c0070720704803456a41c407150200d01c20001508055a124018001c2c184569203441081c2d0340c00903500c6c1e031804d01d010540c00003d0ba409101c5c4074810f010100100d0111142c540407980155000309503c0c0c2c551201003400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 935214442 1250 935213192 935213203
    0x1d0a0209040839150108030f0f090301150501030f0603030e1e130b0a060e06071122021e03010f0306200a030c020f010e0706030b06090a03030903060e120d02160c08 72
    0xe002e24410f04c42d03141a10001620303841e040e10380c0b0001841c10450614101c5074103030042020081901d00a00c0341170415102440765030003000008400301c0c4031078a40700024044031000c02ca80c41072a804c0c81d0707081c404a0b80180d6021241602a250300c0c800d1100b070201051500451a00103500c032108403070420700c82a41d904078a155104c01c031520080e01f82d0b10340060b10950007060030103411980611059001c10464400c002030340c440a84007107160804221000c4000f0407400810024035408500b00443c1d0264a01c1c0d9210216055071042c0340d54140401400c0054080c480101515150b50070302102180144600a0b0700c0b0301e1121058941c440f404000d03000d080c0b02c003030510042c41910b4003445003440501503040800210006000d00a0038040102c0141c484103448580162080114208503150785a1510042d4001e42d42c9007000c03401d5107080c109039000741c09a0001d542c4030b00801007920225038200d0310784c00080c6034011382e81c40708160809e40704c800b1030318060714a40007081c00107620f035800b095 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 935215692 1250 935214442 935214547
    0x6110f0d122909060301150b131403151009020d020a0e0301052202030a02060d050907090b1549020c0703080a1701091d0a02090408 58
    0x10140220000014522203084110400000c00014100120400e0411071550742d0480030140010801800070b0860400085440c0d2088030a401c00040007588a00110900d01c05003081625200105040313a0010340c2c1c03214502c2c034cd91000c010300000302c0c800d083e0000512004207030000096440741c2c0850019402500320010f4040803c0714100402e1341441c06118240c4200170140171314681b841d0320703030400038081c1c80316000f00d8141c440d903105407016030f964401a110389a040744c4c0210752458000d242c01e0608040c0e41c400d400c0301c0e041480310002640c0317042c600b0101c2c2d0520320b2125207804c420000c1a48440c0c101d4240e112038510615401400d2002158149100e40082546004924003a845004034800c00044011341c2e0010401840058280f1000b049490328070700d000d42e581d01030461054a00f40c000ea20108103103540300c000f1150381c80381d0b6400201d920b4454010b0300041c081600407481c2d45c0001000200401c1d40000c428140c0744a016196100c10360001880607440309207059140c90356007245 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 935216942 1250 935215692 935215727
    0x604230901090c062607020a020904060e1c1e050d09030306030605240906060f030708041205031611010f020a2a030915030603200a0603050c0406110f0d 67
    0x2c0300401c0c898040c085c80c60801800c1e01c010003100020451142e031020014228100b10b0240640341400340e945c07903288500850142100046024503030b035565140c400b020284800c079840d41c01e0720070301325600401a0707185d4440c0c000a001c9407803511301d4101c41602c00c9041801c031191901441d0024181d00d03a000c801901e1043d02d0401850f10b0f09092080705062010341c00300c003090320791408003071410116076207500040041c011030704004a9011800c90b5030000c6038110000b440100400050080071048262210b04a09040c0e01c1e50501003440c0d50401a13440d94541440300f08003205843c00c809500c0840708410b45402152144c2d0742c070340b000b0319034460380b0b4192641e1804541048010940b0058604140740d164075000201d0b854009800b03203216681c030364070043c0b40c3c4c1c07101e0010106114015508003561784400182d2001351140c200500300a00f50404010180780274208048140b00e001180d050b2403203401c010b8080324200f20314919040001030403020b54042c5803c01e6080d60340003065140c05e40d0100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 935218192 1250 935216942 935216963
    0x160c030c080d0e0301060f09111317011404080a0f0e032d0c030c13090c0f05041a0913080f121614040320030a030f02100b0306060423090109 62
    0x30b0f040600360f9419001d4110499034040041005480c00e51000500005000f41d003030809000c032104c1251945103074003980700d003103064100c0b46100c013007807242001c004110a01440c1c2410b003611107081a0080603c04001d100011005800f0b041c011450810851002411030b100e01c07070034401140c08e03404084d1070030404c84400110503044443c00324035854071020280003464240b07a00c40c100720800c10000d5441060a13940c0b07c80e00086001192400c0251208071500f21a1038580000d0108a9242000b41c3c403400c044a4000b03a100d40c1c801c1050340c2c1251a000600340008098101050341d4800c0c220002d000b10000256500c101c5985c8120f90711400c421050310107144c0c56080b01362550401c4a0a440011004000c140002040405464020a40c6a00d1b80e10340ca014180401d142400f500000d0f4041034000f0340d0400b105504004038032141c030300780c2020310450030040c0110799165009000c8510680d01d6851104602410091444e40d25000c0f841d11940c41c10700400e21802408030b0320b01a41e0b9100d52 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 935219442 1250 935218192 935218217
    0x20334020c01110a060c090314150c03090d05030c0d0501030b060907090e160512270d090504020c030c0d05090a090e0a0f14070f0f1406160c030c080d 66
    0x380404105103050710040c140d451030651751803009011080b441e1042c03001d01107012000c66400b948407000c00240030005c0803a0b808019609241030401441580c4140c010020070005c8440400c24031852a01c60825503240e48900c404640c040c0546810a803556243c00000001e1080151040d4019401503074807044503240c02078103c4036001750b8080c1050210022000c203003045410140280110402c0c40c0c01810025848014804000c065800b52141800300e026003017060711024900c0340303c2e00d5000c02812451441d0b540a0000100c074896244150390101e041e100c0c1d907105108995003041f00c1402d4032030102000d0000f0b01a030308610410360003000c803a0000700d09005070b0b2050703490950602004000d4400e19982e084c80564038640220341038030415501850303801041203c080a45a03030401d22086604150079048000019807062050864000e88200f6907101d240403950b0301156101c8041c42000c03181043c1c01c40800940c40101119a4520009800d1101040d003403e140c1460b170742c3d40c0c0921003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 935220692 1250 935219442 935219447
    0x809220509030c0307031d0406090f0f0605010f081b0307020708100b010c0b04140304061d030606060f030c0c12190e033706090c09060612020334020c01 67
    0x520380d00000c50744c0c001c10a40021901552080c035003110100102201100312030702043c150342c0c2540c40302c08284d480d0000d035000c2da150340c000e203a076411040000f0806189040d0009010030300c6954108240074141c00404c400104050100c6a80c01c84452095620300300030324000d641d108180704500c010302070015080043c0146014001113900140d44135142d440141c0c44d500c19401001c0c0046420000c00c809501c03c82c00f0a102800c0144461b03106c441d1107030840640e40890351200641e071482500043c04201081d500d40d8103460a030041549084c0d100d03a105540c602092040d035040300c11074030688400841c0c03a0800300c01050320603201c004a9035103801070072065a52040a00c983e65058215088034001043c0b101e40e20200428418002010803108a911240307420940d03000f03036030007600c0d90b41000a1100072003030b5030700800c9011020031a05140100c010000c8519810f610140c41e000000704090641240c110000340001c410385003070588518442a0070512505011070241c0038520906200d9070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 935221942 1250 935220692 935220697
    0x906090d050c03190f02090901182a08121303080301093206040c020309040905030703080711060402010f03091e0b0705090913141204030b0105100c0b04080922050903 73
    0x340d200845c80d4180800e0303400c100011900600005a6642e280200030060085540c800c1d400343c00749580012144000c000c5007071440d40080c003100c2c02100c100040000d040d002440030240d242c3e03e4000390315107045541c541440ca81c140d01c040c2000700080004614171348141c2c402c000480d40e5005170015083c0903100d40c24000f010b100446a44003150002443c00e083c10b400c2100f44000d40c1c81a689000d00c100002000c0728000d143c01d940300c0d400071032000c08060b000b0788803e400c054541010020002000b103081d80c0d60400800c000c3c10000004a0703031041070f00075040f03101320b180d001401218420703540200e070020410800003501e50008090101d41258010000c44101d0403024081c10125540e240a800100c0b10310002110841e01e000b1101c180a1030910880582c071000c0c41136903954514500b00715002c0441038224510500702c0b06d0341000c6c0c40c2e400c41c070045d404987c040c9001d8030954a80c1082d01d00c0d4010a65020b402401000b1180c4844003e1503003103640341c80c2c0b11000c00013034450f101e601c0c1c1c1d6070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 935223192 1250 935221942 935221993
    0x714031603031706040209030a03050c0c0a030b013b0411091003060908090402030f070305070f050d0f1b1710050109050603100504110403061a0112020906090d050c03 73
    0x701c8003902104501c841c1c1c00b001c4c0c0d103c074019101510304800040402e192140300d000c20b07400142d000c0307030040c00f2850a0281106500d021640d5424072820340c3c4415602800621aa6503480104242045100d1106113504840e100760b984180007039216010825280e68101d808903806c00c4044062012440c0c100041e5005280b9401b00b105000d041d513071039500500647c1000da0703408800340540c900d10344d141e00065115101c130900d05403240c20a1400541a5100904150248119042c0174104103030f104003940d820307020300107001c41d0034807030300000f180241000d0041c2000c43d4100640c803441315400c00081c3c507411102100c1c0084541d1180e1220b05400001d004d203500042c48503c04128a20300100515000400c03034499550141d03507140000c0888410349490214501c01003400c00922034144150a01c0041199030101c401c0344040c0003c01d040b41e9440e4140510383e01250520051301c600c819103034145e0003c1c00d0105c40b030301c440c10034903503400092800610a200d44004805400d030305034080102c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 935224442 1250 935223192 935223197
    0x50f18060d1a010e010825091d160617010308070b070509151905041214031908060a05100f1805030a0c03050105060a140d020117100603060b13120f05071403160303 72
    0x300345c108080758010b414541d00c100b801c1e8138042c0802c1000f8009005031404170304819810522b4501d0440007604500c0c04100201da00030429004001150501d02142c2e8442d900c6504040705642c1c2000983d0140101130141da000030603170070b140300c14810000041112400f42c1081d0032405000c084111820300c250b001e0000c008000c150706000044240307030804103e01200050b2401d203503c1c50035170208045013141000014551106014081c144440800090301d8140c507009580c80207400081c200513402d490402c2003080380c010200d641c5c20703400d8400010348001429500c804066040100f41c4000c1400700361455440e00010403018640181801e00312080b0748412130821020301c0400181200d0880c003a410b00510b00f10b5440c2c0500000e800500c585010080c441a007800d002c8001d04585841d000071b001004100030781c40880120098071070450341e68608007841d4400624003030100791040c4000600e148141e80002c21401e8009441c00c01500041d0100c0380c1203107280141070a00340b182d01c4081d01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 935225692 1250 935224442 935224513
    0x23a0204031a0402062701091703092103040303181401080118180503071203051e040501090b1e0f0106080c0a030b0613050f18060d1a010e0108 63
    0x2480a465020341c1e2150000700114142880701103c03802401010645500c51ba000c2c07200c007061503030070600d548060074410580e0140c207441c1c01f41d515541d2040c80c1c0e01c18814031020004444081c0740600050107036200600b92a200c07641ca02e4068034072043c0c80c0e110364480518400220b4454800c025a00c00e1500c142c0d19000b05034a440001c50b402200c008a1542c07143d02c074084195160342a142100d2068424001995180142e0400d60410000e92070300404143c200024003104000c100101500c9000016603a60152103d1401c0c0d030040c41c5400c80201158009820480c9500b4103000150b0302250000b08082c25989a0402c0e01510409004501c0400c80c0b160100f6240b090000103084110258200069041c0510f4002411904041035403a0341c080242c006000d1070074400e400345025602a180f81e5101406890711607840180104420f00403014003c80c1014402c0c111806540481080c1c03c58000d561690070054444000f40a2102c0901c200d0150f410310183c445501119a0100c6000c4c0c0c0f0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 935226942 1250 935225692 935225723
    0x112020108040b070203071a04031107061d010e04060609030210020d17070c171903052202030a08120103021507030e15040305011112100f090f023a020403 68
    0x18100f00d009403050045200901800000480150712022402104140754602c0d240500e001080760000c1d030900312054202d94000c00c101030f00030b161000310030010a84020701c031450b080121002c9500d50200c1740d00c04c1c10081c0004815400c031080304266802600c00c6400750440350313001da98801c2100460000152001300c0300c680c0c2241106411303004051b602e010b0307429030801c0e140d8600c040ca9808100c5003484000505102000c0003c1c0c01d80140203031400e080c000c07403030880201030881c1c0410041c4411400100409405c66500b0b0200e044402d0340650020303216803803400015900002404201d000f080042c241c020350141003030950b940d8580c0b50b03803070303041c1510424188038468a50925407254100d0600012000600c01e015042942504000c11510307660744611086115801800f481c0301d00180000c180105103000120b80255801d07940b000c114a80104183e0009101e024141054a1024a4206c000c4d28144207404254000e410b50700e030219400e000c81c00d040f4401c0388070080503040750010b0348 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 935228192 1250 935226942 935226953
    0x9060303030b090115030b0d23061803030415140405010b0a05010e0906220c05190e0310020a0903120e04050a0e030403062415020d090f0605031801060b12011202010804 74
    0xa15074000d018103c00314078a840d60350181200715103009c0d1036081d001c140e504884141e080105a9006911a01c00d07201480303005082616884058006460a0034000d11207000503915000b500c41154440b000d40c0586c586400c2150090140400b9180301d41c082000004040d88240512a10b43d41c0051083c0c07170b5a01c4031000c0042080d0020541440c050b100410503113407201078414982e404c80310b80c80d182d0351100110358813207170310b0340a840d0071090195900540040b610006001c0a040302e101e0801a650740c0208803d40d502c2d84e4540c001800c1000065402d038005a019403c14000481138070248003a488940c4030b14142c41e010b045910141c0d0041c8010030110741c440c3c10541054030030707544290210035510503580418401b81c0000e0581c81059004038411541046803201c0841c142c640b4115550a11040c42e034552503030310520040020200c041000f00d08c10000c1a0460503441c80200079103a0346280562140c1c01241d805820340d0741c150000540d07083c56180707012002c0c5d816035a05043e42e9684d50b40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 935229442 1250 935228192 935228201
    0x260306040e1c03021e040605091903050d030c0206070c05031615050f07020d0c02010518060904090605070207171903050c0601060e152d07060609060303030b09011503 73
    0x10090780e104003100d4880c2042c4440305041c0310021554056650202e201400d040b24100903c203400e052000c000400c0a258407809488026404440791500c0c00094140060900d41035040900f460080307440c80c4000c9505a8498052584140c098401075038030b4040c2030394082941100a4a00e03081001103846000a00300f040640503c0350401258503420307201c00a044610880303040c0c000f007480d0b1b414001c00b59010021043c0707641300c074a041c07800704515a000030020300402c01000c0042850f813070b1103042071b134400c019180c00450240c01080003411604141c0d000e00000e640b500e0150003560f002048550b400011500405c15030740c01030a05207260b0140c211b280d1030340c14054081107414406170202140074881c95000740130554803500048060020000708000005100800600410088001e825400c3d5805103400e010f0a40712401d0b0a06d840008480c410284001e00c22440c0550100d0410459402541a2402076500b0403648901509000d034005080c01605520000030510003020b51282c6c12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 935230692 1250 935229442 935229461
    0xd030f14040e04140c06070f0f06230103021c02010c1203060519060f110d1d030a4209051513170406200304030f03020a26030604 57
    0x160a01d45603641640000b45041610201d030840b21415003014082410440030240301d500f100c03604e1615100340d8450f81d0b01100910001d010a003803c81d00320500060fa8400c81403102024150070003011070300240b10800c2001d02080b0b20601d107202100030080081d40f840c84041d54103840b45c1c103000c1e908e034603284822015420301508041c1c42e050081344544580e0600b4107084640d03c00740001c80d0801d035020b04081306071350100c800c20100d107405207803503003000030f181d00150f4240c148907201800010043c22040c0c440d52801d40c241c42840310078410400311000018021281083d00d035000403c0d03401c80d0040f968440080144000c0444401e140c0d502c490f44503414036841001140e49038808510084d450450840320520600c9100e1a650244401503031804000810580316501e070504200300a054501110141500b80c0341005510f1072040040048802468016110b40100201454000c1d41c40144030310032521000d0004070380402403c1c201100c0841400c01410504554600341400003c2c400b800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 935231942 1250 935230692 935230727
    0x2090a1e0b18012703120f030c09050609010c021518040e06010e070207030614071803020a1401050d0e0304150f090b0904091a090c01050712140c03030a02090109050d030f 75
    0x7078030001d00c64440c1c051402188031b08142949040c03183c502900750b40a00102405060409600c17084440d4044010300c1699804c0390403548441c0b41c0401251321141c0e0940080d0041c0c1d5140080e65220110307030140101420801a407240c4013070100500c0b05645140b8410215a8080001803148410540356030364042e40c14411158250350340d46402041d68100c01980c40a500e1840c00c3c8920b2660102c111400c0c2003035061100c66207803441c1c0c04548a440c60788580c0300003045042415400b0f138424011a412800121014481142d2072125651240c0c81440341d2825207c0d40802e52810501580e95201c1d5000c050b00c070384840b070345400550903081c4c0c043c0e10426803050383c40c62403500103000880c0c80c0002d0509104e10703502d940303000a1650720b86042c02c0705040c1400000d0141800090250b040400888194034020a0054451101070458081c2d031000860301e000c0807040149403156940986140c4600f40e82300c5082540d10400e00c40512201c400103000241d0090000402501032405806040141c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 935233192 1250 935231942 935231987
    0x608070e0a0203130b0709030b010611070e0601210e060f190506010c290c12060d0f0807030810050603040201021b121506030f010b010504060c0602090a1e0b1801 71
    0x85d5641801100304072200808210003050070b0050007807552178035014103000d046c1001200480c00306159111308a11420030711720102c100194580e44200f140c2203100d50400841081c1c0c00313007070402c800a40023020b9120b24030300c6a08000f941c0b91940c03050990240c20380860004030301d0141e002c84406032000400703150500170b0500402c2d0002d0310007004420052003c0c000d00b685000302c2260352406640c0600301200040003400340074943e440d11041c094120340129844503d4400a241c8100e40d115002e001030000e0720003089810030305400951652040b81ca00c00c03004100c2e91510f08008580c0015100a40141c4c08100f055002d044408091104000000d2040c084010741c070407120319200743c0d10924501c0815100909c22181010060001c000c0031050083c000c1d4002040001d0841c0a24071414040001e62401e40301400031560440e92000800351190070b40d03070b4442c0707440713400c04800084000f00c02203038403400644109070070180c40d00b48028051070442407a1601c011540c6607014401d080009511 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 935234442 1250 935233192 935233231
    0x120402040207150902030d050c0705120f0a0803181606051602030d0203120a0c17100f0f0303020c010908031b19052a0d151404150608070e0a0203 64
    0xf800e40c15051009084000c039201d000740c418181031034010300c03503030041c003c00307101c2107440c400041010810f4800994803030610101d0714100c945055100310010841d4020417054a091000345001036100c1c0c6940b01010054a100304000d59403040c0e011070ba1030b050b58040000b8810070340700308028800c464444494404050f13060b000130b03050107144031007a0096031002413030780446001c1e21481a230080e800c171000c0003100382d0400c010b010340d80f074000341c20505007510001031420035903048580003030b1410a038201c51032078a620348465000c40300d00094015200e070300f00c2c18080350310441148082d5543e03480518280200140d44034191014140c0000c010300070f409140d8008001640d50303c030308134015002058114045450107440d080040881594504284140340303068803a01e500b504040e50003281c030440c5e911a800400b0050105401145520421809000c03e10840c4141000303100740000082200c90703902c400903030340c4023001d02c01c022021a0701000a41600390903809542d0201510161644e0341c40d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 935235692 1250 935234442 935234453
    0x120a030b100203030a0b0402040503120a050f0301030c031e21050702120322060207050d02011214090f21090114130306060f210201021914060a020a05120402040207 72
    0x420889400690004c400c101404459008030102c814040c1ea08518141c00e08001c6511140424890303148400c00084130490342d4402d004464050f280403002c81c3e22542c40341b030300b11080b8505100a5410f03940c04108800840b03c0f542072204600d9109000321038140c54000390070321300b000c00d010140c01d20006001100142c0c803010418048a2a03400186035610141220460301c110503140b02e00d0610441c68050048a0300040c40c0c0050710b4007100c004c050717001d6a00c01200d04038000007030080c4890401d0350714a20125400080da01896000c02907a900345016803585a8070140341400b203990a10314005d603904039400c1801000861810301d0309061596034402c644682c1c0e03000d1510715507a222040300403c240482031080d0800340044600380f500203403a10344d004945840c0790402180c41e1005800e42030443e80200003400443c03003161100b116042450415a034002c00e40c65290300c0901404c0000752000e0b00303510072070311041015100c0c9410b03c0c105c84054a28000000c100f241c1099081008002080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 935236942 1250 935235692 935235709
    0x906091902040b04260a1b090903030b12060915040204110a0801030615050648010e0a02030a08030a0b220c0807080a020f04181d0609120a030b 63
    0xf40450000740d48620f419941c400207550b03c0308051100c0400307503845803203400108030002c9481c0c008030300010445e14181102c003908243d42c000301d0b041d481c00d440c003810540c041d0080c01d403030001100c540711101a40ca04030344d16038508851580c0160015844021483d02c0282081d40042c00540b0000c1c042d14035a00c41c80607540081c4081011441c40c00040042040340c1c045c0e142003240710102c2e8a0000d00c2c14020a02c103000c0d04040d2610142c01100c4001c42c8601d100100e42034229000305a43c61031002070040b1070a1205401002055003810810070918000203905070555078094001c100c81c2c030581d2518540368002a00c00c0b0040342d1150500b06e03899444038a003041d00700b440c000c807140c122800c8032200200d4911a030750006010f031900803c840e090300401c01c150302406014000d070b9905402e040d10780d032603c0f55401c890b520840c840e200c076100340364680c880c00000032031600000701c1011540340c0e85d654010844240311607500c003a0100d078040350b0354000b501500c3e8040c1804074442c2d240200107004e80 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 935238192 1250 935236942 935236949
    0xb0310060509010801200f160b060a05030a110402071e120f11070b0d0b06031f1a092b060504060606030606020309060309070f0b030105100e090609190204 68
    0x68440805008a00d000b9001d14010900711008100013204200f15403000d80c01d00385200c0716a4404191140c4a600c2002114805088240520003400c0e0303074070302610303041c03020303500c4034025140310038040f41506001507a540040d41282196920320012801c001c06940819411a08500e4283ea481501140008614901031059000c2410300321000402041c110f004504007040001000448500041c086183ca096803c4050003035583c1c270341e1a01807805040b0800000e900880000100b0040702c0100491901d4242d0010344944015070307800c1d40140d01c80844001002114041094042030314001040c114a003400e00c107100d0607826824143c1d038034000c036404180d030b00341d4940007044100006803003001d0140c1040e040c204113060421100030354a003c6c540d02903000e010700002107901c244080050f04002d00c1c603040b890311201d4a411070302c138150708280300e154002c084543c260950280110310702c04803180080c014a50b190344550800171039100140864843c80e1303103041040d46240243c0000c0014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 935239442 1250 935238192 935238223
    0xb120d020c040f02121303052a100b031b04270b22031103091c030801360b060a0207030c0b0c030703140f0a0f081e0c0c010b03 56
    0x61060340502060322440305204100c3c3c3d00c1003044800c1030b01d80c83e41c0b640e04225441d00160289441d845c050f2500c2c441c5000680e002d0003507184041344092201c90301642c10414106035005400000c0c0104103607a25100c1c015855000501c401101101d0800182c0010700010700108214542660041e0701c01d0050186000403240c0000345c10030b0005403c040c6401c0b0000e803c00c408038402c03200e00781401c0c0725010784c000d00f0400714400d81c40c611403080041d5816620b0090120103000b41c0400c030f03a0040d240540044003c42c00c0d0318000190080c0f41c10034032a030308040b00d044007809005000c1203c5600311040414212030b6840c1442c00440e00d840010f80314440098006012003403e5040141e00006564000d69034400708100d007140711000402690b0300c6540c14102000b00034000344007825640a4000c00c80813008001c104906150760054000220311000d44501002c0d03260130700302d800c140101001c280c03c0d0003001310200c1c1803403090800400b440601d01380005400310350b0100080c00d11045043c540741 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 935240692 1250 935239442 935239453
    0xf2607120803060f090907180605040e0a020909030901050a0e1807082a07030305060a0315021e0a0c08090604050d05010b010207061701060c0c0e0405010f0b01050a120b120d02 77
    0x3504d051042d06013010040450b83c02e1078619003101000d40d200b005018844c81d4090808003640c00c0340301504140e01921006005000502c000604595250500c0c01d0aa102d074034040013041d0f40c800c0c080101c4040c01c0d030694400340303000c8543c0400c1c1c0d42c1d0300d10441001e800603958604006244000e1a015004d40c1042c0c0c1c2d07400c002d040c80300745614900411038003190307526407650301c4080003001c00049504190349030801140e96913800700061103041c21075201408207000c031984680c0100095001704903244201c0912840800c440b855081d0b80c0c0208659000815207038107000001c280f820019100c0c41e5802440e051410381c641001c07e0021440400441e00303691a410b000b001580c040c0900b0b030140542d0714010740401d5240148250510061003950240080d0000500501ca101144080508004010440e003030806280c454020b09180402c040e41603e400c0029000d584148102c1d12a20155030341c1190082c544150b180003000e10320601c0b5842019a6840c1e01c80300d40a02058101d001241c01800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 935241942 1250 935240692 935240701
    0xe0103060503030a0512090c09040f0b1302060a031e020a050712030b01120e010f020307020c01270905180a0b150405010f09052e0503070f2607120803 66
    0x605840058100d00d100350010f2105031070b62603124003a80c1c895000c0840481c1d01d5240c4584260909803000052500000707480104018010703031032414403100d48a000603010321f0382c8450443c5400c401c0c03d01d0003544020700b0820111400d101c0c0d0030100c4a1100d00d02d01121103000086000d040b81e01c120860f0010800220340b00c42404150074401032101100d040900003030a41500090200e00e4190111101c959104189440307142d0950022054291141d403c40d92814004d4019540301c54150a5500241402d8014298400c074140708082c0740b850b40711400e8540f800c0c5040d0300060040140200d80b000b92204048000160800a82e1030341405490f02101500381002c019503910f40b4170f03940d9070059040c5801044103d5400e000e590444444290000740c60311400c41401c3c58081100009250a140942040100e42390519800448030105c0442d01000e6462445041d021080d1044220040d0074030b201138402100c1a540c00d03500ca034000103680b02c0ea52916454200040040c41c1a91310032004020031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 935243192 1250 935241942 935241947
    0x19020a0503150f03011b030e0309030613060b03061008100605151819030302060f01060c0201140d0e0303071704080421060c0f0f020a020f01032d0209040b06041d060604030605070e01 80
    0x1040d609408e400b0350314200749403000c00d42d075000162143e4054442850290140005944401000380c40102502c0060a04d40c03009100304105004082c6a40288555029001182e1280c00c0c00c40d0300241c03901080000000035807925400a125005004215066030708440d55040203042da1010301c0d07490028441e0450600900d022030040c2010012600b00005010641d0080400c1c9071080e82464100120f010750302c0b0310050703401000040d01095090503040c2d0381e60070010000d580308407504c0d0f45a101c00007100c84144021081601c015001810802050200000d0107800c0300680e40744050483e04861960350b00400c64000c0204007001a00d622000c10a40b40e00c07a41c1124511003520041c4140a03064001a1510351075159880c18140c1d1240a541c92414600c0b00d503016181e41c2c1c8544001543c1e8079400c201952040d9040c030311443c600b400d16440c529000302981e065910403040c481100d01101d51410003414054269544081c1c207100000c005002c1e8011548a03401650b980e240c05650107001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 935244442 1250 935243192 935243201
    0x142031a060a1422150504110405060403020f060f0a050a03060b07050d0f0207080a060618140103030804170703030b03070501110c0613080f0619020a0503150f03011b03 74
    0xa41c0c0c401e401c0c0380d0003085107a81070286025440c40845038215161500b14081c203860304080101001103040142c00e41d111040903064100300c56060b51b061150170742e60103c111186c0f089000310740c2d1180041c003082c0b0150031f06048010f01c005000d84581d1410412140e07941e8182c10110600c030010f000029901c11403541030042500510307034200c43c142031194540e6119110b0000b041d0010820041c2e0b4410040a4400c000500042074180c0559492200320700308600500303014001d5801c030800003040c0c1540e03074600d03104080051800f01c00d4403500e41d0840c3d80803031f101000600261094403c0304040003110b08032100424601d482a20002942c030701100915051600603440f59052050141c80c03080150310206451410110840c0c05580d160300510440c003031040140c00054081c40303859246100a02d000942a0003331603d48560002c600c44484040280d01c178060040c40010710600200c1c050080050b0f107025090001003880c0080188080801e08540301928103442404412200c9005a90940304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 935245692 1250 935244442 935244451
    0x60c040f08060610121418120c1e0307021905010e040b01120903050f040b0a1d0d020f2809230609040813090501060905030142031a 58
    0x41c2c605890500002061888a031031000e0520109000154121050f94000c02e41c50030803200d80340c01790400034000c546aa10360b802588081c840c200510038030306004400c0d915400d585000421072500610314211242c800070724203e5240c401800100c0040e9034800401070380c6c001d06101d045145107083d0005000c03503e00d8007201e008915082e0000c40f60303640300310001d204000401340070a50303601900c0c00315000e104000415480740000720f0082142409071005061f80b410725503981c4035620801460a00358504a0420b035070281e04d2615907030041c14020b003102c41c1d0801c02001d81440c10142c1107045488555507035000021800c0220a100310700d001e03c100240358180c0c0245010100c04e960380e0010031003001d824544500000000038040140d1401198488002180b10041c2e207035980c850140549828080d80011400f0042e01144500303052013010083c042c041c0000d500c00045038a05010000c980c9604121902542c0340030b035810400341031800065105074910b156144a515102c3c60000300500b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 935246942 1250 935245692 935245709
    0x804020319051c2a2a0b030411030105010e0c1c0b0618150705031204060e15010501080f0c0a030b01090b1303060b030a02101d0406080d020615130b060c060c040f 71
    0xa98440100d424451007010140c881c0301e500400c2c40425034111a8101795030300070082c11000004000400040e140c58200200c01a002408203903240e21992000c02801c95050580050074040f80c0c5a10750390808101000d419010002041912000071462a03800104500c40440354000750042c0ca04103120009542c00c4000e0811b4180880c079a540c81d140c0c80344840e1034245024520120b401e014050b803003261441c214108913107480481d112240c20490013445443c1c0880c42c84000902c499000351000f605c100c40080400307140c4004c91809900030f0044c5190300341040801100401c3c661210b0006007004801c200c142007040b45585000b006a84012060340d0103600035015050050312101001c040240450402d0400a55002c02044915002d00c80e02c641c4035040050000d003c41d004610440f111a0980c241c4e22140c0d910070b00389400c8a23500207003a07003040d070340304440002940c02d0344501c501e6000100800d18100484603a1403508500303491011003004009000c0195075130902042001300800ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 935248192 1250 935246942 935247017
    0xd05011d07120b04060b0a1502012003070c031e09090e1c050d0906090303060501030b0414061002070f060527010207030f05010e0a03050c07060804020319051c 70
    0x804051082d0300500c0007022041d204012808100e600d400c843d65000001d0700090100c0d513540c2e184441e03506691030000141d4640700c150f1050340c40b4042049c4203604180e642c80e10f181c0303440c101210548400d60082e42009501c803110a8692081d22003006590300650303801c03915506200081049807201800402c03123501407041000301040950410120f20f2031800c119440702d002c00c20700c0d030103050f003910000c04c1c040c80c04001c0300c01c15826600c4101038580c00e0380d0170004162011705003c100d4080101500540ca101000070f0010302c0c1c40209210b5454851042c0c5414a40d109442602100c031030308000040f4101089071120200c00b806054440d9501c0f2581c1c65100d2a4140043d4481280340009000c450b8010724450921500350441d80d2501d140100f00c0d042001d040c2002002c5400000c0070480e103001c0c0420008146225000e0341e40900c0d00180035015409545188038015428030004561034000c024808401c107000034821050300781c10351240402c00b401c001d0040001c24800c0941a540609e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 935249442 1250 935248192 935248199
    0x80f0303040b011401140a05030f07111002030702010b210c0108010b0f0306010e03061906120510090c030b070e04060e0106201906020d0b1f030513020d05011d07 71
    0x82e001d60464550314040d200c1c04140000484a0880c0f169015007141c90000e45442000e60020046200c3c0c1840e00d50701100d5210350300121460700e0343c809041040d0348030404004200140d0b80c02145c20400d54000003440940d101c3c00300303004952000b4540341d64010380d8400b0090340740500c05c500001ca000d20b03260400c0c3d81400c0701d26516004400032602c981c0000300c005096a4007600031901000300090488800d46451703660760ba1804d10b05600b12088500301080050340050300c10b65079804c160f11901411204000c155440001c0080784030a50f0030341110400003000c0303403440800e02c0c06488660744003c0c084180001303100c1550b21035441030180b07200003c01081034980c07000b110400c1c08900c1c808441d00400c00030080307140664425042c1d42168840650104100882e80141384d4085140c2040c0290b20750350f0708011251180711800d00103641180441d07640a4440d90246e54000102ea4208200711000d03000300700e00096004046440d61341d5480d0074007620340000c2c0c640c6a1802c0050092466608 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 935250692 1250 935249442 935249453
    0x60f090604060902031006092a140d060b07050312070c0201082a04090204031704050f010c080705150906060a0302010f03090302010605030307111203030105090c0c0a1209080f030304 80
    0x9000707201500ca41d580d03c2c141801c568080c00744001000d14001c003808040c4c1c680124100074220440800c014206a00406200c41c00004006140001c0740c1c60300359221700800c11541450b400f0803112440950f9170900401c040045c04042c11301c80b07000d80001c585404500030311008420000e04120244a912071000380180e074485001c0c4c0d40064107078880c5a0070844a000403504004010904915560109000c2400406075010b002100e014000206008100c50107154162085016564110350b1049110840c3d5019100c250600c0784140c0d2030914149503905c0d03640c1080b41c0801c0e414075112642d0240300707440f4000c021090b0403190448250500c0c0b85036074006040302e4401172140e0281600c445010301454000c0d40118024900039040d00d07503400161401c140a40d61104102c0d10800c9000c141c6012550b00200352410388034060141340c0a91a007010310000798102c0d01851040d4801c00381c40000040c1903140c80810302c3d000d07032500c51640d8100107400b400c2c0070304196201e049074405c0c03041002007070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 935251798 1106 935250692 935250703
    0x2010207050d021f1104090207020d05010e0a020103060518010303030c020a05061603110f04050f04061d100815040809040912080403020d0923010e180108060f09 71
    0x1d02e80521a000c40700c1c00084c5c5401e80000348418071910080d41e008000d0103000030282e07512120700e0340e03c0909480c03650084080d1174001c09903850855070103024900207880120781c8106813444114800d40903400511000c0c1c205034941424400c1c0038020710180c08103d4001c41030740d07594500344034144050449070f41d480300000c0ca0086409660450031040d41d03035001e00c0010f090315003450841003105410a80900c0c0358003c1d901c0300d00203400001944403044201240a03450803500e0701808038550400c0c2c65100514a0304804420120040721030662540f00c2d81c00a0680e4075004988080703401041d004d01d00612041e0007109282455130401200d5110b94070917421a00c603d00702244c12100303e20103125140c10b00d4003d14000c0002d510410f5070010b01c100614210040c011040c001400e4080200066204802e1500040c00307150014403c07503a1240d0022080481820701d08803096541 = true := by decide +kernel

theorem cover : BRFrame.Cov 935071942 935251798 := by
  have h0 := BRFrame.cov_init 935071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 935071942 ≤ n) (h2 : n < 935251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
