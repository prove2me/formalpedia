-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3581
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:04:42.97498+00:00
-- url     : https://prove2.me/submissions/322b6760-9246-4049-a422-687a1e209494

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 643884892 ≤ n < 644064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 643886142 1250 643884892 643884907
    0x90d02090a021e0301050301060e0702030912100f0203010503061005060706021e03010320040e0717011b0f09141005091504171e120c03121e13020a0506 67
    0x90140c510b01808440040f400c54038504058000b45048500c220024003e441c0c83d0000c552a0450550310500544d00601400a142c03a04001070b000c0d01c000b00f07007190b541090510b201c500383ca0404030800890f6030b000005125505042c011503501010f1946481941480c100100306207100d01c200c043d0403241e0104030f20f034038005849105942d5030000b004e565240e50b180e05055106210400c0d00030080c103440d0401040321f007002d0203606050611100905105031401507006840405254910041e550b2046502d440c030100030300400801a2640c1e41c030090441448000e0480c59144d0400d00c0c00d103140394a11103840d070350204a00030614041c03501e01c0d218911400412038001000807075800000c00820003040040c4074100d10510785240c60200ca04210440c680721881901c1042219950340200c0d038403d565008038001807a014403000112854510009080043c40205a0395440e0403410740c54135010b8081400d405039080f040d9280f00810680003640040c090010b5482624003a035008240071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 643887392 1250 643886142 643886161
    0x51008090309100f0210200a11010203011d072a1109040501050712090b2206061d070305070c020f04020909010306060312021903030504061b0f080903090d0209 70
    0x181c03242e0801400050003082c2034040039041c4000504880018031035448401d40c00140c0d0700034421545014881c034480c000460250300d49a601034111401482601c030241203a0000c240b000358020301c840303825540c081e81e041c0c51600301e141c5c001d040b00c41000359060b0750856984151691704003603800c401c0101000081e5103860001c4203600030646512244007410041409019005144100c040395140890b4003895103081049907d60000039156216440000c0c00002e40300300c1318031110034141c06c1840d64001030f55490301603e4050b006041c5030342d0801c0045912001d180c0501d6003001460030280114034000c0c800428440048802074401c00f680000752000380c80d80e5040381d0201c80040c3c01d40c10a0342e140c1c01c000e0050500f0344001c0ba40407200c1d109840c000b510100d0b25821428074020b908119074202d807011801b5280242c001d81d0001c3c0e48607240490310108580c0384c280c0505684403290010b9960b01c4c00f03000070303a00424060b500d40080100003c140d0310f184a15030700c664115621400f507282e240c0903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 643888642 1250 643887392 643887397
    0x10806010903080d06150c0507121a010b090f04020a170406020c07080a0c060305040c090f14090d020f011109010302070503040504021c05150a09090501090203011b08010f0510080903 80
    0x43e00100001984400164041e04a0740c155a020070130b400b010520840100d5041d010194060b00725041041d0511170b121008120703019036800b41d0201000d94201c0c0421605011003a0300c014141e020001e40418242081c0c0c03200ba0072854201c40071410305403507038405821460305030344922240781c0b00d00005080014076410b8680603d0f0f00411a592540c9401c946a071341e030300010301502c1040042c90001030740fa10a002e042c3c8603990220640d610baa203800c0d400c1c006045050020580c0b1519851681c1007404507107501071180b5541d000403e00c2004c0c4202c080d00384002580502c2c0f00b80d041941e803003100c28080040ba25070101c00c1c40d0050f070341e5065041150a40c0140d8000c143d206000140d203048050460308001c0310750780040300c108019221150010702421000d075406410464124040044c0042540200001801403001042c00a180d03400a402c44429240b0307451100742d03114007c0e0105034028511805440050394207000c0c03600348000200c40c481540c0d9110b0400144100003051f0070b409009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 643889892 1250 643888642 643888649
    0x21c0501020a03060f0e15090421050d0f0c0801150c050109030f0206100e010b0c030d060b1803070b070809010c0f0302061e06010c0303021809100305010b15090108060109 75
    0x71501c1d66400c002c010068442441403080000d44002c02103032250144401c10f005203941240c608134200068144003031408014000e0b03071499680c060b401c03080010907110040318401ca66032240e49000f500f4585040303a100a203148070f510700d03001d1200602600805aa41501d01c0240f1030101210440000c0380e0822800f980101507500305a000070805810031550903158032690280d84d203a640d0b000598034581007d03c101c12a022001004108282402c0018030100b0405419a841c242d808603051007941d01e180d0080c1e580d01c0c00042c07800aa400e000d241070028203404c070302401181c0d00d404295100c078020400041e01030b403000241c6c0c150a0f0300030f607a40c900896101281c4100b804050070044e4481071308440316104160b02c0010014241d0000c0042d40c800c0c50140c5450060f0321031034030110025040b2a0b50081e040c0440f00741c465140d075940321f0445c400d039210010003200505500d006400d6480307006a0501910007156081004001c213019120100001c0c6803c00c4659a0400101c81d584516403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 643891142 1250 643889892 643889903
    0x1030e0307110609060715060602061e0f191517030403050303011e030c06030209040b04380d05070302030c010201020f070f080f07030c050d09081e0c06040b19050313021c 75
    0x2905010583c47d5412060456150f6002c0d0780d4948d42e060948590311890b400d130900070b41001800a940e804490144c560032040c03039400d031404d0003e104408400c45121212101c0340c0b20746d03080708011005a9001040d4010104000795041a186981d1540e4900040c0107600ca0500e16403e02e640c10b8110080182c0110f8005540da00a60b46c1d80001074000c0d88031fa40040e0040341401c030702c6034250401c0e0203000c41103c543c00d0100034403841c60b0300141310081715026940f40c18808480310f441e00c2d40c0d50030310054817074002d8015090b0249544101450860110300d01e90640e401801200740314681c1609880446070088440400c038441441d09144510524a11011551011402e60249a444113850560910a40807105041c008070002da03506c0400c0d104401080e80b00c0787c08080c03aa010419900e1042c0702c41701c01c440180940c2d90002e00160060380014007440303c00300756440c034801d507601c042000e151142401031441c181210800180580039030040c1c0111a00080811202c5680307002c10441038000c4d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 643892392 1250 643891142 643891163
    0xe060c01020d05010e150d0201080105040209030109140f010510051c05071d041202070302280506041e0f15140702040e030a0f0302210c0c0a08040501030e03071106090607 75
    0xc2c0140048030b0302c16102000d810041007011b0b056070910031180849660141c64940f4681c0c6000c0030031010354020b039103854155481d8208600005d070402c00c049503203028000908818104188034034212040202608102c001c1080c0401540d100c00ca040850f90300c0e04450440328034254100a40341400e2544000c00700c0000e20303a01400c00c1000340c80700d03000c3d0384a00a049594940c40d0307070490b5a400c2900000e0341c800c0c0f202c8410034514110045042440f04200c1003600725981d140009402c9806c581d105038030041c00a0010100f18036000701100c0a0034107094619034090401e04e0071440c42000246800030311540080c80108041c0e042d055070080c560040c024010803103030484640e100d40040d000d070404588540d2140c22054041d00a45044a25a0701d40c00b42001e400400514a14001751051580c0300c030400603110b154200344a0404940e02a644107507030389207000001021100502c1c11003c8a0f0424010400001c0855951601100f0308840d4a500d400741030000680d18800c01a0092200414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 643893642 1250 643892392 643892399
    0xc03022404020f010e010206270307050607030b0a030c0e1510031e0612060c0c050a0c081203071211040f06030605030606190e0a09080c0c0a080106060e060c01020d0501 74
    0x180350419118610965580050010f8080151000c002001d90240907070007110014201c100a1096a620181904010b42194540145641c250391000c881070341ca0303420103070400004a402d401010121001035621028840c07964031a52540c511500419a0a42c01000400c660301035121610103500c40091400d0f295080e0014084e004004a0603089000150411051051845446060308445101d0861160300da1140c2c5d4140c010305554084501384411003000c0300100300c040007424503c5226800c0341e0045414604120302d00701681106110002c4204108450681d0200c0c400c001801c1c28100402e0780105004550818050754020081c0c401225400213100399054115404036081541a280543c032038109200412007581c42408008408190821804102d030114a40c041052100043d588009640c2c61b030b159845102c540110341e001c41541c41d02c6103800d8505e0340003402e401d030003080f10302d24220010380302c55a2006450b110b141d0108880d61503850a40490340c0c1842c2418041025684 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 643894892 1250 643893642 643893703
    0x61f0503060a2715060f050c01200304050606150904050a0b060a031d0f070b0d020d060b481603060c09170604060903110a060b130603120c0302 63
    0x220101000f0581451402154407030a081520151501a44e0f4143c505131160003d4401d40c0c84990b41600666070b0341e410b000070844482807c6040e18425203142e42d41d0a0506000707140800240000d03211302c080001882500c454801210349800301510041903580d21070706140e009215503502c180d0051400200381800170740c1580a030030010700c9008a0440006078035041a690302e1940041d208030b41c490242401032821100c05001e40413030361000989844440c0c5c40c6001502d8656200d400d04190110764000789032302c0d01c2d03001d1200b94020394107188034400300300218142516030006502e4140c8000000e1100007024400700d04c8442e0609110340b40d1603138916000d001000b500403490300040503e038000c15080303201c0101050b002d0381c0000914407500c1303e4a54000910740d4020071024854600066003c0c00c1c4103004180c103a9005110000c3c9149003c000d00900078100010320250910700682480042c3c94101141c0b910300329460b0442102485140a0703103440d1001d40411b5104090340e00818a518 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 643896142 1250 643894892 643894949
    0x307051c06050106081006030b060409090c0801320615030a0906110c0609070f151b05010c1211030f130b0f01060e0a0b09090406110f090405061f0503060a 68
    0x44508004007011f5600d40303044007114110300d0015800201080100104080c60304080341160050b40c1025003117664088a80c01c40788100070035481c010f905068112002e601c070501d803640c00c12241490320b8070b10348440003903e08228030040c0b0611400100104070760003131947c031081207a54800f204001c2c012490540041c150000301101c1e2046c0708039000282080780106142040360341015072000f04d17038100b102d00c403003161040b400c9208010b110050928895000f15106c1c0d1101d0107500009507001465078024401c05140c408500094100050044800e2070315080300d6018500072441c3c041c5403164451450036600108014164507940c2c001d1200d814450611981221856140d540d460101001400800c0102c1c1c4110610303c40706110560301800c1444200303a20034401c443c001650031510520020542041560301e0704c8107804140420780f410300344101c80d0040400c0b1100800802000f00600500740120004400c120000c8045031154881007854809041c0200440ea00700040c0c80c20b031501e00c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 643897392 1250 643896142 643896151
    0x41d01020a05040e01052704061401180e06010f09091a0f0a0e19030e01110d020c0f060c2116030c031d03060105010509150d0606110c0307051c0605010608 68
    0x90364a04000a1503207403030300036105100360304007e00c5100078503000d01c248854001070041d40c0d1a80c80b05001008080e00d8025180a03003103000010a07510340c800c502760200e80c541c0b500d000c59680054014801103070301c00b48441c102c0740801c2002c03c42c00752500e46500111498803035089101d5500003844240b140c65003902c0c0c441c42030200e0800001424101d030503619804408261a10b1444c0c03500c0e040840c0c0701e034044451200341030400e41d44180714100038914001d0a5520480103800c00394002e641132038a001d070b40b0924842240c40b03600701403040c801151992a05d045416030301102d0310034002600d680b402034400c1c17400c1c0c2200300005da1440e410046d0640c2c00407142140080d0a0100f4520183d00d1040920607400d409001031107a81c0c00c003401990f141d402448065840380c2c0d0780c501e410100c81000b00801c001062840302140c2203103400070250441030108101c0700a42c0186601d600135880000d402c00c02c807082258503011140d00d502d440d001d0400d010742d0107090740b8107280000c036256400c4014140107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 643898642 1250 643897392 643897409
    0x11e09060b0702120c0105182701090c0203090619300b090907091a03100c3506130507180b1c0905031b0a0309091a041d01020a0504 58
    0x24840d00c1005a0348070000745e1419800b1810a03c9081c01004080051014507000503006440c0031010490503a07400f14079a10000d007480f0003c0c0180882c82d150f018501d03280800d800110f00b00702c44040007520038010040d038090ba41d075801541101c100c0c420812294503031030264041c00c00c408805088640f000c01c9528510080f81450310340b4520b4100700511520540ca2407029204603420200744a029000d40c1c101e24002100102c0b203503002c1c2e681405401380301c2c90310200003d00c1118854001d41903c1820304903d408003044e1455a40c4420424014412130301e10020540c1c2036030300c000008081e04e001c6c441208100d0f15000402813859003002c480500445c4a1401d013491a5403454007424501c103803c0200700081403d5201c0340725915a800c000c4040744203c00380d031305050599203d291207107554036061960303500a82c0310350b0a06800005200140c1030741041031250b00100b1618800c51075408881500440c2d035a80c82d00151500708036580305d06080140295582c2d2507040000b0003907009406104c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 643899892 1250 643898642 643898659
    0xb0309010e06010f15081b040b1809040201020303072d05031017030a030f090f080a030f0b150a0306090609240509060d0804090207120e01080f011e09060b0702 70
    0x4e500000d4030390720044805418000104803120b050840e80c13114050920144001114500b200c40354019014002904095003a87c0c1c4560b031140003601d01d008804021400340302004140805070740c1c00310840f030b485001c03403c08001455130032808850262140c000440d0f289500e11165860561010003540104403000d840350840303403500007a80043c400e08029881962081101d680710900941042c076083c0f807409000030305904d0b02d85400b80c100070310000c120340074100080c0c01211142c051040303811100859004100d100104004039049190300d2440e8150280c0c0481d503180c085101e81c2001d0301034041da0409129441c4c0d00c1303461502411801c0e0b401110f080ca21158000c520000701541c0088820040181e8000c2d02d540e420301c801c3c41411941510f00007c100408112034400340020a02c5038480c881c04502901d4100c4004c14040240400e40d041011000c20700482c1011850070f641507440e02c0400d015039000401003402000c0e078580c0000700c0f607804c040380002d03102e072001c014215083c02510b0004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 643901142 1250 643899892 643899899
    0x304031b090e060c1b190303061a0903030d0911100807090509041a2e05011202400803070303050c0408030307030b0d05100902030d0203091c0c0b0309010e0601 70
    0x2d4480d103084403000c1c418030701800381d0980d02c403c0b03030500040d16035840280e13000d1034035007410090a050921b0303058001c00d0301c8036420080e5041c50711091001a0402101c1030800d9a8980000c0d1030780f04001c1070350101910b40c220703507090000c03114620000020050070301b034000c4801e40c1e0280680400321a0803003c648417840005241c249089100e2007680c0c40a20450107508151354504641005455004c0d04d81c0d6620785403000c1000201038941c034481c0511420310040c0381c500010007801c5140d10942c801801030060002d08031549110303034896040912201c3d19081e80d141c00f58410028a60f040c42d480025520004a003403000c00140034080c000d0744e0a0003140d9130072171910340c0352055124041156100f000002c0c820b903c2540152001d0600070680e081c0d000340d6450700c901c4d0601c0031400c4270707440f0341e02c0203504110328003040254508241c5001071400c0002010000e8051249130400f11501461007040804104454034024013401c15101080d89900300b030b242c0700c6d00070303c3c1d09640188103104040010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 643902392 1250 643901142 643901171
    0x2160609021c0c0e09070f0e0a1503051f0b150d0e070807150201110d020315010e0a0311040603050f0a06050106172403120d060b0a081303020304031b09 67
    0x1502c81e01d8005440031222880d0000c031000c500c80040600980d809010004201c070b0114801000c01020304402c1c5102c1e5041003044601259035080340d402109406d881c041002481c0400d480c0038a0201500f400e860025288420014000d0341c1070140e03000b02d44084800d1044a84000f4007024000d6900402c0604201603409503110094040c0f82a25800b9070800c10408030380c2c1080d180a00282d2001040031030380001c03d602c05401c0502004581c07034020042002001c01d51603000e101c041c00b464682001c441c55808a04509214040a8541c1c0c1e03400c10518920b4940c0d41010000b59406011100124801004c080e19103900d510116001810400005052427081503021140311003000443e010f41c4604064034400051030060442e031032442c0101b5003075550f06125070100b0b51101c40406a03106402c1c80030b14101c0341ca0313803c00d400402c011b0010784d40c100e0340000c402e076104000c104044400d14187c1016071443c052940300902c0b60704044400180701030070442100c1181c00d000c0c024065040795078550b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 643903642 1250 643902392 643902439
    0x1b05100608190b04150b060406090e09010c0e130905060405030304020a120213020306011106070207080114011212051624020717030604060803280c15020d0216060902 73
    0x20340f50400042c00300e0b011807403000c10044074003821000000c0f100944004201d00d034015030f105002040606100300703e001c807440034559008800800801135004082c1c1e0180280046071219400303039400400500d078000d42d81d8440b120380754000084903403070700d0a8a4029030303980c41250704a0045621100c001080441032240c40c080a900504108103043e50000b024001d402c02404a4108001403150b1000414180a00c42c000c12260380500800790030171010714250380c01c80c0c001d000c80c002c44000402005d0300c81c0512081c010303030040800402e550048002c40340d90243c1c104048132002d8601442e410464820303040040c2030340811401e44565560741c540c000700c0c001e018019012540a401c5410100280d41c011035001600a0000800d5030f02c45c0c00e01481e40d0051036900c0c0091541c0c04140f048a41c9040e8070b01e1240c807661400c0c0020b1005036a480d1345c03c036051014154170940104034244601816010f81d21104200b001d80b284035800c90402402038003425405030b001d11500700d80450000b810aa0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 643904892 1250 643903642 643903693
    0x1b0303041208070204021c06030506070f0806090432070605070f03120e0f0c03010e280302010b09070203090a081204030b060a08010c0512010605070b071b05100608 72
    0x903154031119261985070700c5900010f01240d01607800c1002c010402c0d0843c0c250001d400b2000c0340016a00d0951401c00d28002020b0440c4e07060001da01340034a4242d0f4800043e80d0f00c50350543c2c1031412a155443c2102141d11410b00508a220450b2403211403031041c2216060005109002c843c411640d412013502d0134816100050252001c0c03070145408a80140400da0a882001e079000031103d081566160034180c00b4084ac00d650342144000b001c05107000d0060348007171850007014004070b100d0103501c42030160742c081c180b43c6400040e10b28002414000c1d44500b007440c002614000703c519000200035140d07440780f02d42030710511032640041140540003c045111302010042146841c0c19a243ca0030803000080410781d00580110010688034002c0c01204851000d68542a449071581c194420780d02d40305070013500401c8001d00c207030700103c3d800c81d241903041911800c101c854512440d8608140700c04e40741029040d88100302000040601c0d550040c412260140141c1340100700481162401c5901504c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 643906142 1250 643904892 643904909
    0x403020607210911040510050a0f062a02091519050102030d090c0b04260102090303310b040617011d1e19050109180618060203091b030304 61
    0x202c810042d980c43e0380100c07901409110003081d1011510000b81c19035100b10b8044048840c601410815421320303000700d20160260080703000410f820302000505180381003d07400162100e103a9107555003400c000180d250303642c01a060751200c1c42c0240140784110b00540315103020341250380ba00001c0041700044001514416409145071500d5007000c50041c0a4900040d1303041d6407000790020307894001c080180000c208241404107800542d820110301100c412111165036401041500415500441117a0b03014003201c240f2005903011020740c14070403503405600c14074032854250102d0003075000000b030402c582d4181d032543d860303140d680d040e2281b0110038482c1d40e55003e40e04c112014805030f201000344c0e020b5101d018284c6101c421512042a485007030704d101910310155200050040480d016941c09000040402e000460f17190b0089000c07214550009040c4565600c125501d070203141030306501030307a080301040d07480e420440b00d0152250b0301100c284c2c038009030501c40300b02e4034200401a0703003c0303484a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 643907392 1250 643906142 643906187
    0x7080708130210090f0f1403030309030a050706271101030b0d0204050a1e090203160e0646050f0a090e0102070602071101030c0e06090f031e060403020607 68
    0x507800d118103103504405003801d110150402042c00c445c10003644000302407103200c468800345425030103941080300c4400603001c3d4004004100d4070b15400003c5034040016480c0566031030741e160810100811240d980b030702110030342c50486c00c400c2c0d0082d41d05141050041c0071000c00402c3d10401074046800801d401a0004803051180c805440e182c0c0c031141e40084800c50100b5a242e001d0303a1141040c1a01021030100c540da004d4180a500701001400e0485203840c00e5400224189602146050401030a00d03124607904411949034a140c4401c0c00b01030882c0100f0301078603501d058a4a0000e40c00e013008101502822100003800386050388094064420181600000d00e0502c071251001d802c4209180780103640800c034520014601d44000d0484a0250311101004d0b403202e0700041c140c1f120308003441c040000b14210780c0041e580ea0340441b406030004840314100080b15101181c06c0000342c0c3c4020361140b1400c4d20600000401041c81c44c801e9201e85d0981c0e5465031041c40a072030a1010781042c00f0180000b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 643908642 1250 643907392 643907431
    0x40f020306130e0d03021308010501031a01090507084014281b0605070b0a050103150f0f02040306140106020325020d06060303020d2309010c021f0807080708 69
    0xe40e005103012006061040d0b001511030300c901c3d02b9540c0a03803048841400404040d41a0701561201c54094040d0359800e01c0f40d0f05200c2002820400c1c0540300302c2c001c1d401c0c0c03002c2001c0e03000c28908842081844d101850310080c2528200e140301002040c098820b03a5202e07808245820300442c01c1814043c82810b04480e5007880c4801e400d80908240701103d2005c0011868400c020b101c1b41d08030001c1803c2e9a0f02d5a4825075441c01000011020705503034400760a0000520005003084a00582c80303207045000928012406507010140034407910710b180071031000902101b4000c07940c112101044000c10b50301c1060341e13500b0040b0790320301c10300d000103804814070900003804a642c400007216440c002803c400308418542c0301c5804490b481e40c0128003682c807800e11441000d4010103900000d01e2a94404107041c1414101e4050a20840c841103040283c0800c407101155a07500302410008130001e0649502c920640019004441c00e0741c800012030f50240010b402c01c0d2140d03401c184a0340d203448030003150150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 643909892 1250 643908642 643908647
    0x10e01121703090102070309050409050703020402030a140103050a110901060806041802100f021902130b0415031104060905060616051e070e06030a0b13050705040f020306130e0d 78
    0x141064211121815007102080000801010b140648140380005958643c1c074607018000c00d01682c0524002c40c20a03260a002c68004100c13002240e40590340540d59030b846090702e00050a50404c40c190844903c1d0000c01409000501c3c607003800d2045444c070145d0804401000000b0009100e45c10000c0d1130304000580600b03158200700050403010745008083c0d0915400507400d071190305550b500140701c807d140e055880d8100190450094070200038450998a5000304443d8403503c04244040b649903480c03000282c0715603111120000e00504581b07085a100e2a20b83e001c80307003000d5020310541c00d2050100300c5090702d00c103903805070360300406032803914000c0d00319100b0344a01e0010a0300c443c0500402c02c0780d11030114044216012814000d0305441d400c00790302010b191006482a4002e90003800d80c00c4c005a4603032600340c2c0140b4900c0b0411210401ca02c0d0582c07500c1e9045e04415041801c0050b2050b500403581c0242d4024101284c0b1400718104000340c1c0790881b20244c100b10600d501c00c0c891585801e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 643911142 1250 643909892 643909919
    0x120a0519090f060606110601090c050a05032e03060c0503070906081b210c0901020a0209100906260c0f04020d2003010323060403050319060803190206010e01 69
    0xb40718503003010040000c2d4540f14226400b65120b440801c1d03100c0f1058500d4038003405000d014105a00d0200309642c080c0c0070007040c90003194001d00c2400400004210710200000c18404510707100107504199015508038190a840d03140b1003102c8030740c20140070006180c0100306403880b032240c564a0604075850404203ca0500000c0d0030301c400d042130203096000c0b40051030300600941da52040d040c00c820381120105056040c006050504540060001c43c00b143e0340030904c0f105154045a480400e44c3b03a484c0c5130103c000719075016068091500070001510942c12414106060511820150394200c1401d0151544a4000c03001d602608104000d0701c9890268082c1240c5200901c001514244400085c4091000c1419101c82c1c0345000c0010020011604115a00c405403450042c03101c0c01128a000c2d80c40300050030007428010084001007504600384502090348040c6201884541e5480026903140d0b80f11a00c2c1e140d00c0e8070b41d50765014030103000180d41412214010000603140c1c3c070b010201c2071000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 643912392 1250 643911142 643911161
    0xf151205061303110609031c0b09060f0102030d0504060b011d01080f0c07020d1a130b011811190f0203070309090e011122120b0f090f0a08120a0519 65
    0x18081560505013400c0005910a00c0704070000c40d690301c0b02c40500000705101c000c050b9142c0d0304020089405458540481ea00400140e45040e544000040140d0842c040c0100144100c2e2600041009210b85508143c52044080e29554080720a05451000c044c60702090f031800700b4801e10209a203841c9030a41280e001240e900814245009a400200d40003020f003425125040c000000606180d181126a40c00c4110202c00c1c8410b129103941d03418010205105802d07081c45214083c1d102c0d0141070b0070040443d018030400b15920b2220517042c08403c1110242940040c916003805640d05000000705e400703003501511107144080c03400028802130241809049820b540703603940042a040c802016008444500040700250714003114200d058255540c40800c8030000b2175015400b140c20b80c0d9003907802104026840f40c1c2e503550f5036403051900d0504030984403079100f544080d0003400410000782541d014078105004154030781760326a40584509644c0d140e03190f42c0444c1c2c002c880082503400307500c60 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 643913642 1250 643912392 643912397
    0x5070201082a03100b030925091d0d030203070e1513060f0f05040f061d15070201030e06041106070c080601090c030b03060f0c07060b040f151205061303 67
    0x407190100100400c4080001c101c5100507000c0f00b480003010b0f107020000090803024880350300398500002c809030344e00c50501d90050310107400445901c0c942c5a000ca42000361007200310902c40c05040281101048081180766106400b0350382c0749844681c07080c000c5902400c803036900e07035030b024004d9003c1080c001c10044111004550810032803400c801d080900c04001c1041e9101c24081072804440905240380d06107150080000400c000d200c109102c401010544a0302c3c81c194940020180c008420502c4070300449900440c401c0b05c020080d05e40340020700b004ca200303a80c180300c1ea804103110f540da1550103580090010840383c08101990420038090300041d40503c100441c0d00703a441c00340c00d08004017030300701d4101e060300c4002c11440340746c1601401c840c0c0301e8280c004014901c0e10302d40c1d86801046c06010f02c010a130002031610140f1004c1e8000c100b407040004c01c02c0018020248030080141b0000e4030f003002c48032842500181b50110850703c018003a402002402031552a030701501030f403030131450b011010f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 643914892 1250 643913642 643913671
    0x708160507020904060b180103031d0d0212010609060605030411010e061204050703230c090a021c02030a050124052107080907081b130e03030f040b160507020108 71
    0x2d65541c01e03005001d503009000c00240340c208041804622a40a07000d4003444240400400000764049114118220118501160320303a0076070004100400140c1c000e5446140d041d51202c0075001940804100e418005080018950710310081d1058041150054203035a0040c10750444d55000d074500c0380828800615040c90100a01a403544540041d43c040c1c0d100da200d900300f441004448500b080d0711035042d40d03001c0300c011081500c00d6a0f40036000c03201c50094445101090b0020f0b41501615031030401c0c0e10300c416a0b0504800c48000941084a0900311349007090000580c0c4036201d2070303400f10480488980156540b9510058130580d104180c10b00381e0360501150007103010a4a945940592041c1c0c1d01c4030203d041c4118240c0c90050a80c106240c50340000c0017144452450b4120240d0520040d107100c020804108681c0004202039050b0011314000081006410f04890000ca4443d0344a03002c90307516034840f681c10801960741c0095110104a00300304480242d030181d440c442d401103031088901c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 643916142 1250 643914892 643914907
    0x9040b03011d0a0605060103090803040210120c2a170f0702041b0f02012d0e0d02072c0109150302060414032803082a090f010807081605 60
    0x1012907041e202c456074141c200d2106202003010300e00405802020903c4d007440000111b131200c001a1001600080c03091031401c000740842406410103d5030a01c80920030084524508009000a0b0012001c05c50700d200781c0c200420399900910350520940d410001c141400054981c0101c103507885815040540d403001e001500040c5d03030300e000b0924000140320410004904010010386100a600c141c2001d40e4140408001d0401c001544d84004007446402504000800c010b030300010050f103026180140502c8880390440c1c1c0d00050705104856071600e81e0844980300d030016800100d03000c1100002001d901004000c280910b410403061120714120300030328940d8a600042d0903074401d03070000c80902440d0654003154602480180b01c048200ca6140f800403200c11046140141d10180080c148444040452060f9503040e072091409500400202c00e4666502e40700c241c1600000e090324819240f11082c0da1182d4494141d01c1d010707070708a4844a18607200e1416030308602844d8203008040040c00d01190 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 643917392 1250 643916142 643916171
    0x16060c14030712030204180504151802060307090e074d010c09080303090319090801090302070314010b010806040218032409060112020103090609020d05011512050309040b0301 77
    0x110288007913100141d441d0f107008207000c0342c41d01454050041c54904400c02002c94540f601814000422100c0007442c0c82c451a40312039043d4200101a4200c00c001c400c000c12940c10048000035514418005d2850342c2e03e801c021035a4a0010445010008802030004401801d00d4503000c0200a0030240c1c00c0d65851600c0d0381c0d619000f0b040200b184981d183e1019244007600030800030046c00c0840c010710b05d1884c0c1003000903502c1c40742020200104ca0040c480400c451b101303001e542d02512441c8020711291140d41802541c61030b00380819070302c102902c0d00f0380d20701ca0b10502c540e01280806844044007079035610300704030007500718507104080707464960314040b0350390340912001892030510100c21000302802030003035121140c000d042108552000e001400b50040403034400f10b00a0b07091030049410103651070a80007504405100940024003450508100201134000c0c2d00410320320480c5854580c0c0e07131008807116030801c4401804641082280e840182001c3e04546070701d0f0009000410411018481c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 643918642 1250 643917392 643917413
    0x91a0f070302060604180302071a19020d021207110f0109180203040c050a030f08090a0e090a03021005010f030b091c0f0927020306030f1c0216060c140307 68
    0x710010380000003041581d140034420301880c0c6420343c14034428083c482e90041c0d558401800340c02e040e89661440d80c40a06401e20071141220301840078110004400c1c00301030f45e02c0750190b1b101005809240c816150601d200300071384580c1a003000e01c0f0080481d0030300501000141504080d070400c0843c18011554154038080f0f00c100d411180c000680d07070b14041c10f002e28120119000a4402d0000c002c003000811400034041c011103401c108103a42e21020000050100055580f040d86504105c1e4100f00c001a4041010829140a50260380384414400d0b41c00088030380900450309255200d0380c040c4003003075030f640d0456880000031080301c5059050b0408090307003214008800000030b00c1209580340c82940301401e0401007000d01414201c2e1144840030864200740030003145a042e0780400003d4a6983c1001040a240a0341007550408910039001a2181c0f18110021016100702d48040d03080c01d041c0a8024226296076566142e088800c7c0e46482a40e40ca00c3d0441c065844280002c03c040740c2410030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 643919892 1250 643918642 643918657
    0x30c0204141e010b03040308221704032603011203030e160501170f0a2d230105030a030c0221100e0109050c040507180315050c0307091a0f 61
    0x61070044107501d8850b80c402c44005070002c122002c024024080080e40200340341350402001084903002e002d554452101607180e003a4044c1030b4a01c4800c0b13103005015080014019640140000c01c1c890901480400640d418060080c10705901080100507c1003000084e8801038802d15000c0381c510042d084481c034000310300c040e124595000f0f9400b0003480d1b80205812000c5920340745a10850300d4031000070000000003c24001301592991010382883d00301300d289000b0403400800c1e5041002040c4200002800001000202008102059000111811003c9040b50740040040003801c0944d41c0855041c075043c0b001302d030400080d44404036070241c0d040950203901031140062054032403840414081d0b840004501c1d40da80d01d0203100c0f5000c1080821203d040311015200828a6142c0041c100d40a8902000385103c644060b070000c020054500e00500309100d281d0800d1000d0707110030306a00c0303081c072050b90305001044182c0800c10100d8442c00051202240b0402ca0380d0030664281d00e21003142d800580c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 643921142 1250 643919892 643919911
    0x1b0703060c0e2b0c17060103020310110301031401061d071d03030919170a05060901270821060301060b04080d0513030f03080f130b04030c020414 64
    0x40901e49055000c5011100c9010440b0304064807260210140e20030548901c0000604454039000400c2c03188001c44034008041d05060090307a0025122103503254071082c00202d12a000b20211030480f00a18000c074200303440841c45417403440e4030715903852811394a45402c2900c40c0d522003a0020302400c0c048041c3c8c130b100304004500080380c034004030010712801703910b0b4040c80c00007010b01070840903413000400d80d0340c03c580a444a80400c1c0804482940105882d402000d00035168611070034205000f0072004072483c4a003040701c100791038070b20358182030301c040d860403100d440200c1c1c1c44908051310401d4031003039050241101c1ca146c40d210740201d408611418010700c1101703400c4800d004690070248030b0f02c0002c0c0040b103511401c2c1800c1c4182907440d00c208001000030004089500d418038580c46409200859211034010700c840c2d054600981598011540c0040c1440b15400040b00300a81c201c030f81c0741080d03216010303040756074482d6001d44c1c0e0100102010303a0007584e03030000c11450880c1025442c4c0101c0251 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 643922392 1250 643921142 643921151
    0x10902091e0903070c03020d030e1c0615060c2004020d0614041e0b01020c03030a030e0d0804210210110c0118050304270f020301090b03031c021b070306 67
    0xd424101c0c0d4040c00d100840d078002c010004c013250420480c070095990480354020030604a0808445034036100748501d034407844600c03100c16a12a6800c469586a201e510240444070320b000310107030300b401c941c07041e8804034403000c0300040042d04100310088210951018411481c2040e0041b4040381c01c232507080710400350355042c140008100100340b41a4402c00b2a030501801d2800400501d40755007407840440c2c41c51f2034034114081a8001d003c0c0c910400806021242c43c0d5000c641300601528080c0c12000d540d0040807030382a1039600c11072005114a030019002d05003541c03805a5886c01a5104810f1001c500581400d641009418055840030282a0401a440700300440d2502e086a400403030540e009115a038014000620110031f6a08135107400c601c400311100c42101070b1300c5070129101c200da0818034104800b0b040d40c415a000d181658160352080100100700418540e50348516007040c0d05139840521080760008c0704e50020301d90f40e400c2c000810b00d01c010b0100070a00d00034050304110b80740c6494 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 643923642 1250 643922392 643922431
    0x60f042409080c0f0411090303030f06041803080718170708070602011512030306031406010e07090506070b06040b060705010b040507050f0703120b0d06091403030714030901090209 79
    0x8008048040c00c034940c06004640c00c3d2000081030b09604018507800340b61181508400c02d641e610a84840c0c900160a0329a0703032411a0718094561001c50749284218580600e01e44c1032548001c250103d69030507180c0740342e651170b90340b816100c40c540004d80050491001401081140c44104140d040c480d481c2c00800743e081c01c0050103410f10324142c01000c1103a1401420300e0b10301071014000d40c100c54489100007803001c0070381021000f601c030301c0d0406058010390b280c1001c0381c0c1100041c40c1d4125450f950511585445a0a049a424440f44121a48030740180300e03020200d0b071200c3e0101c1d00302c8001040040c0031645000403480700e400040007a1b441d651b5495091085080c00e02509500010a1910510380b84e640b91200ca01c50207191005010000001c400b1f4100a200d54000803100d8030040c5408403240140c605240a01080b220441d03800815a040700c4210384001b00b664003d0140c0d4488411a00b0410b82e011002e0308002e150b25925034881c64942c02580703c1704c03d0640144024000784001d44c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 643924892 1250 643923642 643923647
    0x4170a020108150604141203030f10090c050a0f09080d0c1509030c0f17030a020306011b0308011707030c08030a080c0a051206061c0c1d030c060f0424 66
    0x1489034128801a50143e0080d0743d95004640542e004045402200000310020403d920a2600c0c04105031000000780400c001c10605400e120342c00216080c40883e4540e4810350603034140c0070b40903002c17503024444102058001c07040702c107062100c0e03d04a004161745440c16442c0c2a00f1111120126510f080343c0c1091041d00c082660308059400001d000c98140c6c0d030b800900c0089100800f51220068440103010003c2010160900c2500c540555071a81811f0b4174072002940190780c101e001c1429001000e4950100c002042d07445030b010344884000d81c0c03074001561000080022040d0250103503001c040001800c54100c0c00152140000954443c04d80100c040e00407003000d4114108508203012000d0466803203811640d07680c15400104149440340000b10750720380600c005042c192071400d50803d0006140741d005486a031001d03030780c161186c0b4a1181c0d01c602c00a40d840019007542166030b0b0142642400001030102c0c482d0410003d14003991403080305201854a60825407601c1040c2c40004000c0d03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 643926142 1250 643924892 643924907
    0x40e100515010c0213150b03040c05010e0415031b0b0d0903030b12060c0d0216051b0406120209070509030d1707032901110a03050702041802060a0806030304170a0201 73
    0x600c282001d05040f041500000d16019264280d920401d8940f541e002e06100743c040c01c84000c20062143c55180d003040c5ca003100000407940a218000f50072008405100e141600030010f00703c0406800b1008641980c680041c820f4440c2009a0740c022055000a44080c448004214004681100044a20161a000b015a102501c2c81d81c82400b401c0d940741030f40b0302c010407100e0f00840940b445565981440300040007a00592a100d0305012614004805100d03020a210204503024001e62901070101d204110883c1c0d01360044544006541c2c40e2040181000b458603130b0015060b0800e1401c004040c00000d1070400c40b04140310005040115020105040300c41c00f40e0003171340d54201448070280701410782c400d203240d00781d0082c40c0d402400782102041c0d0246185c40d03100360300034090721002000747c20090440e82c08500100e01403072520b074684031328000b907000d05589aa070081000f8940717140b55a0480300882c0103480a0307410301007040300003103400c2682860740ca4002d80030b000c0c01ca240c020780000740140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 643927392 1250 643926142 643926181
    0x11180a080d0f0309050106031703101a090d0c1a07061802100f09031b0e06060f03010612141005100908122a0c030f01020c060411040e1005 61
    0x5600c800300316080641c012488030349006251900107418013980c2025800342c555680b01405e0701018940e101e80d6101d4920055101c0d040b540e0302078400b40c2e07642090507071641345241e031a010040c0034080140d00d490111150000720340601440e0104540710799604103240f503a4055110002000100b55081104600840002001906016402043e50b40204015081c0104440d0070044000094954a4022114403003e0740e00b000720003d1107508011140440e1400c1d0003420450012800080c8461901004590b10113649003a02c50071a460710600b5500456050030340007450341c40d03030241ca0101c50000c00340f9204c0ca03000c011400300030740b500d03041c052911802c4010f4400c02c00342035418800c02d00009a1496007040002070b031755880414140c404000a00c4000c400070a440024186003486400100c2000106044085d10106903810301490700b00e1080f4807003102650810300014010445d00304031a89084009440031842980c0c4003106030408510350759807075004d5a10000d02c401c0000603140c0c002d10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 643928642 1250 643927392 643927409
    0xc0f01020a1d0a030204020d0f0905100e030c0304090519090809090a090c05060a180e150a0f0b070303020705160e100509010506070f050613051212150411180a 70
    0x2c400440e0108005070711a02010303005a030005842803084d415a4031110072889095801c0010803270a290207510380034a003100161507800d090300c1032203410020003150741c4640d0380001036142a00e091690b201511005000d5002e0f00180b9941d80c000034101e000d034030020f900c0342043d603503a103140104000100d2400fa00c0c511001d03181ca104000000c420761403010540b841107403c3d5485541401085034041c914140000c1b4024003003800241c090320040c1c80e103003d2141c21460711410003602e800d201000c1014401c440f442c203002c820422031844140001c00219000b482c1c0507103800200e440d55072400d40108809402840700c00170401864001e44842500010030480200a2500d04070005003910018001d00340300d100c0008521041000309880300800c00c2e84001614828605100c91154000c3d1a00741a40c0c03030300a801190f119079201000f15012641480301a084079101c80da03c0b007070380b1540c030006190400d44d40c400e2440612102030141c101c1c3c540240300300518a0001003070200d96203659012491 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 643929892 1250 643928642 643928687
    0x30a18080c0f0d030e03180a0b0d060503010614010f0c0201050d020307050c06010503070b0d0515030a08190903020d08090d0818010306120201090e22080901110a1e080c0f01020a 78
    0x80717041c040704a54460040c00310000100030020002400220217901a01c840c200000d5580501d600c5a000783c412190120020000c40d0740e605d002e000310007030300c040c580d00140c107000d4120202805a4140c507292401032500b00c3c24a680c44200741c00b242e00035111603012074030208000000c070b0020001030740908025005002050b103800c6e007030001ea0103024145030700b1a031580009804038010010024096000801300c46e80e00c2e10070b007401c56583e882898100d42029100c1c0301654098018180101180d0740034000c240e2030303241610350006a80100400340d41c0100344021100114800102421a83c0181d26403915180412400902140c1040d4003001d5410a03801c9010702503130700419007404460000c03400404030340c0c441c19007400100006d00a43c400800e505455002d1140410143c22498001c6e00c03000c5000f0801081e4a41e520a902c0c00200b00004101003c00b403c1c6001103850361180c82002050b0820349901c10700b80c103014040c1c114a00c0c6a502141003480035038428034941c0310500002c00402c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 643931142 1250 643929892 643929911
    0xe0f1203030114010509030d1e030608030306042c06160305090c15040b0408070e0f061e0402041d09011d0a020f0a030b071220030a18080c0f0d03 64
    0x80d100c0c001407240f0940714010801001041e4014822503c00300c0d0003c0940b10070a1b09254080d002402e02c2004604450f0a40c00660300309000b80708a2040c0c400f010300642c29903940e501080003a140d10380904412080038526128500c14030340d40c038420009800040c0c2031510705481d80c81150054140504200b50419040c40703801c0b50040741480c40f2180541c1c848108c45e1561806038140d104031b900c400c0480c0300c00100040c2d8040041070320b209403221070360580103540701d00c0101c03080d400c400e6035000e07400219080780d0083e40c4401454543d486001500c0541425540c50300c44c81c00f41640300c00d0015601d40102049040c900030321400351601203061150f140c4400d01d94840c1e5503443c003264000c0c010810026205000c2c2d40c0c5404140c02540d04c694916540d141516008200c40c800e14031040b886801c180841e032498100d5601d415400401000040c00c591310080400050011514603c42054030b030810707140810384050091040d021001c00a00e68185421600c03031a007040c512401d8109844d01d0b1014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 643932392 1250 643931142 643931179
    0x2c06040b0c12010e100e0a020d0507140a0c06060f0902190c031d0d06020f19031107150f06080a050c041e0507120f0605090a0209010c020d030e030d0e0f 67
    0xf070540300070615101c1543c1c0c6803400d03544020100c0c0c103d02112404032080248949290300104544100f2120511590325082e0302a245014801d13510700803200e00f8001240300d140318800300e40c0c1c981c0c010440404c0082d5030343e4041070780d4100ca800c201078090b000544040c400d0200c8808518081540ca00400d4220f12618000c0c20384200400704510f4940b01020340c42c40340c1d50035000f240000e800000466036207130070410a52480d03001c00c1d0400800318420000d070050341d000344942412089010303d00f615050181d40d0395a000c15800324289040c50341d84160068400e00d520800d4094894800140034440700e5047c040d1230b00188405140c41642095404500045600314145203004200804566511580015030341014440d42e9060314502d00004010845803941010040307803030a4868034140d846140c07002d0141e20802240c0b6000c40c56030711b0705000500b401010082014001c1c94605101c554080c002801c100c4043c84c1840041d00c4c8024160b010b01e804400020b100e40e040703c0d54140d01048027040b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 643933642 1250 643932392 643932427
    0x30605010f1d1b0a090e06120601181104032d030c030804052104060909061a070201090b030403031a06070b04030e03010b090f15030a080d2c06040b0c 66
    0x8a0001514440400c0c28402030301190041080030f1007110b9111000e44400425034581e0f44075249810801001140340c904100c0c10300e00300700003444040c08a5a08121086410305101c0c09201d0800c0d80e1858112841d103466005800514030450079041d041c000c15903445540070000010958440840300c2080c00281c0014003444e040c0c0d458205410941e4403400c1c0b45060400103042c001030b86041c4210540c0013200d0030010400e4940071780307600710015100c0102c4800c076449400b650a084000e0030031030700055003120180a20034414546181f0f8503450750840325058101b42c804902003900e504200d82c0310079078602d00035003a070020340f085824001640c40300c1d003c0c42c1c80908060240300c001002d40103a62000c3d04580c0d0590009007400c856030410100222920354111014244008140c0a80200c0c0c500410710303a500c550003138010303402d12842d0445038008181f03400c04c0c1c010030401c0882400342d20088440056261100401a001d949080d0500e903181c032100074620321004d4802c0110301900300d0350408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 643934892 1250 643933642 643933679
    0x6060f0c02100c0f05010c020f0102130b030612030d0e0c060a050a120e190b060a030b0f07091a0a390203010b120a03020c01090501090905151207030605010f 69
    0x69007030455611034400d5440701c0c52581c3c05030484ca0f0b030030700c10014480e0542241007001e900d40c0c21500394200392458130707081b03002d00da0300701d002000c1025041210041d59009160055402003140c55440c00ea50701131851640004060070150740c85130011a030107403041c801d43d0324514043c0c07180c5240420002c0000c10300d1248000d0b0406016030340e080c00c2c50310303c0282e00164032000c0c004100d80d0203090304000088036a03051030049400c80e0900c400034076141044c20107003048940c8a002a103998440c0107180219410040401c0104180900f0000d920454420382444010182c01400c0c0c0d60703406461f0082901040820711041d40c80c0c8110f03444948188611030079500c1541c2d00d1303032504441c030703a00c0020b000d00303585002c440d0b200148000320a84a20081038182c2418800c1d02140c4618170b1800054440c02c2d080e204a5000c40c0051604200d805c2e00360b0072480c2c0c442038442590742d4202c240310000ba0440c01c00460800c60b40e100410910030003a040c030446015101d00e00c3e2950b182e9103044500d50b0407050703210703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 643936142 1250 643934892 643934899
    0x130803070f0c020406120b010906030309030b09030c2b440703150609030807060e01140702071508061c0302070b04090b090f13060e150a0f06060f0c02 66
    0x881e4a0542481080001402e9070300400900c12a555031380f0382600900c1010b0b0a90f030b9640c800c0000200030300c56120707010840703a1584032200080c2ca03645541c10217040041050426000810a01106800c00e004541d46140c3c5c0f490031840d10b4208035804041680d840c0044418000440121185818454550445004150318040c41d6205806032401c1d41d0403110041c803000d289060600a8580c0c02d500070b0042d02c4d00001030322103259601c0c0c41c2182da0722075910001d00b181004200c2800461030680005404200b16030010441940103071040e80b0458080700c00d04010313007200e0010300191388001800d0012903928601802c4508150000070001040c1107525103030b0318040002c8a04050080c0300b41e02c0100600540c0c952240da440782d0cc1d40c003a003500d41c4918407405030381c40001c200b0741007034030b030305000b00c2c41c0c000b0702c0c44008056a101c50080412010030f9406100ba00e2100b032200da00b09a41c00d1140034216008100d00517201c00000c2500c441c3c1e007148062041c541d5100301203580c061100308046404a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 643937392 1250 643936142 643936157
    0xa0506010527151c1410030f0f0209040f03030b01090803040b0c0717010603030305010504052502100207060207020a0510020a061e020406050304020307060806181803040e01080613080307 82
    0x80003d078096980b07242d8110500008240c0019030890711000191404004c4800e12000c0300d146840b501c291812904910594607140f030034004641d01d4801403542e184904800314803070038241c0000e08105000c0b1000c5a141450a101d4001c02d0b505000e030201112080c07d0860406007446903007500c90040d4055a03c01600c041382005018200300042c00c0240001a4101c140030641c0300e18501a01075030209801203030904c4000940341c20180316291240e40a032034441401d0740040341c0300c800e91380b020035000b0840c85007060300001e01d10540300805c00c0500c101001a1384000d11300c103009c807141250784903034482c0904010007078040350003281003403180343d104400180c1900849001250101c580e0026103816101241c0490310781d41000066000d180200c00b15040705a84038002c6480380f00c01c5a4160704010441b601d6a650600c01510a801c5049400055114280116103901d0341d04203602102c5203024070001004856001d2103015084403016410310301100e401c2e100e01300c1d5880090001c60810191 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 643938642 1250 643937392 643937467
    0xc060c0309090903030901060608150f0102070f06030f0e012007060e0d03020301170a02010207051207030215130605030708130201020a1407090c03060e1605210a05060105 75
    0xd004803101140020145407480c10815043e550340d1300102c4002495600c1c0c5a00851390500030509079104942c04504542c003c0020b4040c40814200824014190302c0740302c5001c155041d01c0031041c405002650f60014111a04012000940356440c0e0101026490a9400018141a601c40d548251700c18103a081e070710400d600c0e210008041400c0b40304007034003030720302c5001d0001d9050f0002e6040740d03100b0740c4080380d07070b02c0c68000140c4500b40404028050303840228100311b2420701c00c1300e0300d02c408404030546400b00c1c0e5039004908a200002a060218180001c090a601d43d21001840c09013181c1e02d003490541c5000c02002d8078203600a0038007111105403900301001c682c400c010550000c2c0d80325032807003950120720034865941c034142e0185100351400c00c22400b00301407003072161900301c4203e0340004042e61030340c902e13444081595903155801c00c80c041214a01e4120310254103400881e100300300c18001e10704104914100d80340505801e0405c601040314804000c20454890f0340704025803d403e881481 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 643939892 1250 643938642 643938667
    0xd11010b0627180103110109081906050a0b04060f05090903070308011a0d1b03051308070b0a021b030c070f03080a1110060e06092a030709030204050a09020f0901080c06 74
    0xc4040d0b0701881c00f04a58000b0040010504041e00500c0080e210380b50034586031200380e600c0e0320281084103007901c0c03c01c9140000c2052600842d800041a0000007203000700072000c01c058a000d134208004800c1c1c2d1001c00c0082e414003110045d400801c0001a604081e02682c0081103141c040c0700e5103c040701801f8400d10110700da40125440307645a038000300a4412580e1502c0c0c202d503200004500820f26000014140d50003181d0f03840c0d080e0b507002045501d008595605c0708112107010309400500b5500340142103030041400790000380c45200000550316001c140165a2820026400046412900307040404c0024080001e0325495041400c120081c92482c20110345858486007458041c1c900713005001420b0740e0f42c1e081c868011001918840d8099441542e100b600684580c075050b90322003080580e5a0603142100510303086020f03880c00c1d42030556603400044c291072069901c420203a83d2201c040c0c0851400031000000007506407121031803507140000190311229240201c6000343d1000982e68007002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 643941142 1250 643939892 643939909
    0x3011a0901050f1b0d0e010c0323070503030109051b090607110604120303050c0901020d0f050c030711040e12030105010f03022a100207320d11010b0627 67
    0x71100f201c000d80354007466a030142d091204140c00b00c1d850168014002190340f240b215542d058006031603da001c1d418030780d0215400044041d294112500b0206040815030a440082000c14080e500640e125414901e4031011940d0240010f4010000d40c00c41e0f410002c0c0000503104114811292292124180c0c10071484160808095a40c00603000030080381324648112003168150195800b084959607100d0101268400c410040703016030320031104182614402c0e00ba56001500343c2c80c2c5181000c00554440e4070715003003040100d409400d2940007525905161041d101d105580e040200035680801c4413004080c801809414100030354010f0001c2180c0c0031350120b4000c01c0307854880220f441a01c0c66641c0301402d4258200e40640500042c0e860a0141230082d500d28640000c0f124405440d1103954000d10780405c905103600c15003603000b0400d03d03142804040720703081664440c452055070b2881e00c142103821590803188100410700500701a0088808030460070f004414860055101303240028080c1c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 643942392 1250 643941142 643941157
    0x9010605030d1d190915030c0e1810050f090a0c17012a0f090b03061c0f06052502150705070c030302071a122403011a1503011a090105 59
    0x40004804d03a10030250005081200e07045c460801c0450300041c00700202085500c030180192941207801d0022510810900d0741140d48a00d00304900c5910500650a012042c44074044959a40e020406a49075110419a0018016000c1c1c0080c0819540b84110403650b401446d4007000010841042d810b000d5000700356490483c180310002d9820381d4401c11036881c0c2c030402c80c8002081200135001d03583c05810b0003000d0f20190b140060441d0f4800e002c3c0258040d100304050f5007058584c01c1800031400740d12036190000c5c0a11804102c6241c40040b10f142114029640e6507911a06511a00150350103c3d1a00386d94218000b00d80203901d982c0300032101c500601c28046d000c2c00d8001070010405030009060401c40704112074000c4000c1101c0305a0b68603000301842c46080800c0800002e801c1e8444104c01e200d0010140d80541002170304070042070031988c00080091030520900c1100c2d103d440c03c111110548911140480d2441d81051174045030450018100c1c0c2042c180480e840340141c0c050010744240c0e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 643943642 1250 643942392 643942399
    0x80c07140f19050d05160b060114070605042006040306090503090a08150912030a0b0a090606030605041b170a0207060c050d0b041a1912050307050609010605030d1d 72
    0x40b0b1059a02c0b0815045081c1d404a5140c403c040b8110007650286080d1000c118800c04250544005500ca85182d03039402040c690401c50710404c1644920f4000d009003003020b00032400020030740b400d40b4203208011041d00001080c10f030b10078540181540c41c4411a03054a03841900030860060500e80541341d406048015540701c04c0c0f014010075007210024901e198800c100c8007070300554a9038182c150712107007626511600e080c0b007040000c02c50b1103107411040d000310300941403803d090340d140c0303400c800c50390340c1d030003080000381c4a07031080055252501a240d068040302d146406101c4000344040c1c010748a03e4041000c101003400001c0b206846581612286a0005400c2c03244c03100030b44d001003440e805500b010740841c0c171b44820325401e41450310540e034a00c1032151880001c24214020802c490b5085820200000c2c0403000214210040c09810784040b4828401540c5503582442c10078240348000302401040c1c1e1503c4810072a50390006400c43c401042400c08140a0001030fa481141c0c01100c260140c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 643944892 1250 643943642 643943653
    0x1051c020d080d050f28021c06060504080705040e03250b090a0b010605070515090c190e0c0a02030a05090f09151e010c0809011e180501080c07140f 65
    0x810b45800d8001500c02c00c0080d001580303e03624450050300d5014180504250001b0852030b004007a4002d07401002c42c03803500c515031340c1c032030306a0254981a54040d400a1002036400304040181c18010032484015110032103080c00140e084d1165190fa9014486007800d10001c112801011307400190340c6420002d401505c0c0b6101c51401c134600542c2c507070358903d04440351003440000180a512900548c2c441c0b41e8480042c0030441d10403511400c80d0140a030403220a4001c4009681ca50794071a0910708044241003204001035190000d065105403005041c19283d540170048021441e60100c02c4894030138482c10155120074451000c282191040182185c000a80900f4041d0940b5003e000c401103030070071504d000d940100c259541d452491040303032540c08200c0780e856140004046602030b010342d8606141c00c00c50040c24140c0d0780c41d445215200030300031030400000c429111550200b0714000d00740030300700b071000750406101c0303841a88100c180180921401e4100340e000c40034140f100704228a5050121803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 643946142 1250 643944892 643944907
    0x1106070b0c0a09060806130506060405120f01060506040602030d02070f140f100b0a0e041703071d040504020105091c05030a030e0705100207060f141801020c040501051c020d08 77
    0x40b580034010a001007000c895001502510444070310f4418880a00b2890881800c2c084040c0603001c064112039005c68184000b00306910307aa040d081581582c0002010441201074449084960b103401180c040e1034104018003031560000700300c6107050b0301d0320707070050360341c01203052080c61540710705402400400e081c2c00202003000300041e10951090303a9425542d41c108a240c05004a1b101e0000b001d4101c01004410843c0021061815900c0381c0030384c0c041910400d01030180b43d03032030b44200d40e410003050090803102e00c40449960900d6420300c080d901007016041c5900080c10038011040010321444101440e00f100480e41a00b00103120f600c002100d0300c40500324005070141c031404002401a01c25108005003614010100c8040c410701900a0100c150030f00c401200d244100800030006c0c030080f9403540700b010708000014503002942c11070010b0548035803000207090140f8003c2d0749114a040200511490fa6200003a520506104004030818071143c40407608407080441301401d402000706030f90 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 643947392 1250 643946142 643946161
    0x7020a0b030403120b0f04111207020a1403030108100509031309020318070e060108041b0e0601030501080313230a031a07210f061e080c01090b071106070b 68
    0x3076000310300c00e48445001c04400c68111080ba421034411039440b2212010301c0c681414103a2100d400c0d14504000645070a001d203400d05103040741074400000590081ca20300040c0b00d41c420144400c42c0000d0050342c519450200003a130340c2c601103421202210741e00d4020030f032869010030440e0a0901c0d44051070140a6070b86903198000c0d00b00f03d40d600a10b102d581d080f1100c811001c17504200307641c40c0050040c8079440c1d8900440e00140020f00480c1d90b030700c0744515107064000320f210980c010700c104508000c5c42e02e0300200043c1038501c1a17204000c2c0341e1040c804924805000541c00003542e00c5081ca560360504407032003c5000c6a5140302c0b45c0d4200c40611004000d001c08540112004c03d000030514156484981040b10024504580c1c0c507142c0f2101040802d4000312a0002062240c41050104410307407103a240b04038070945040c0541c0a00101801000502028880d1205040f02403d104905d07a10741300c064a854840c87c42c0092540442c1c01002c0e440340e8841c030070b0702c1c43c040d001105090315203004505e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 643948642 1250 643947392 643947397
    0xd090c06020717060c090a05030303010f0306110306091504020f12040606120c090b0a03150e060604110f0c070b0c0304080c0f2d091e09030918090307020a0b 69
    0xc5600500031584046080d5102040072051034400100030f1001d0f070b80782c00091429400450420790710030642d607000622603034100042c601921600200c1544a4910b18024003180e682c1140c114a2080600402a140e40d030b40e2009a4041441c1c04d001540b4000b000c0060000e05c910400310311b80b10008a03095221800d00d010081c0300d548241420410b0b9500c9503410246021501d40003070040003800000d00c03c904654114004116018004a224039101e91318a4a141d8246200ca480c00c4e03940c10b020103e0309c40c100040383e00540e064508100c00d04080c422405c582c40b0f610810307111f8960028160101100400221008142c407114a546a8081d43c1d8807603201e80c400e220f80c0509110300b0515204a1400c208003000040c0020111000312003460440c410304001a228100e07917954201c1d048059450342088544076800c0400e2051182c1e0030081d510307005010162520115070f10520100d88291190b4001d111000034008007290700c2d6994450b07203442c6214114009400c03050402000a65a420901 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 643949892 1250 643948642 643948649
    0x50a0603020307050a0b030105011b0f08090108131707081201060e180603030304020d240b1309110f1203070f0308060102030a1e120204030f17070c15050d090c 70
    0x683d9403060340d078403c0180f00080d5010301030320b40301c04000410481d80509820048c0311703100350050b0340200c641d80721000110310b142c00c15191960001850030494bc0d0000d04035a100314000e1002d020b190a94a510a604050710303c04880084006114000d01c0310001c02d951040c03908261074401e41d0784400e4000c00744a072030346500740102d41c0b0403a41481a028003035414850b4101a0081d400c2d6607854003001080d503030045096542c6041486d84003103480c0b0101c0e0100c002e0710384c41000300b8496816420b120742400c0145101e00c2c40b5161100b00000101038070508c640482e4101c0c1c000315202c020b80f0014140009800030744e05244000605101040300c0308a00403080380c001e44507070480340d98070801a6142d1280c0401d200008841407425954403821151000e03880056251500c07000c10808403101c200d80c09a001a600e030305403030110004210106080581c402c1c5a481d45a0070281c20b43e0b03a202c051000c80c01949000c0c1e00381401f0201c0d0a118800395250350b02c580d5010700c14016a4200441c84401501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 643951142 1250 643949892 643949899
    0xc16060806120604080f0d0f06050310061412010b090103030c060c1b15020f070f0c080a08040b0307020c0d030e010f020f0d110c04090803090c15070809040f050a060302 74
    0x40000d0390030314154010b094a414907070701a01d03190380c540e81c9109055000c0603100401d0f4805004900b441c07942c0e031045501c55031801c240000c15505000816250492048103c45200e061080510107503024680150711702c1c0042c2d540b1543c9001c0b4008281c0500b46107024140c1008001e03000100340f550103030201c01180e0044408200a5055003821507007030780d10384090003c0001507812400001c2800b07a2268a0490420006060524a4180100e00c1d48100700540b085011301d1003107028002c03461440802400c840c0b0041580044075610850207002d0380c410b03684003560120010311074074000c0c080b6407075003040281201031000461a002d00094080701031140026185d00c41505000d00020343d54040c03001603c0108601403042c2d0045400c0318503015440b9048c064a007032203505880d907011310003040384101c2070703941c803488c0c0328000e503103880c1081000754410549d1031013400c070718005e01089034802078228200d107a0f10180b1401040c05001051446202c5918203800c0154400380c65008800340e034402c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 643952392 1250 643951142 643951157
    0x40c080106030b0c07050c0a0b370c0305120a09060506010815060901270e0a05010501051e090909030a110a120806120d020309130c0c0b0c0c1606 64
    0xa6001500300c0d8118040240511601c4010400c0c29810601034000030b84103400300c5080318a2903020400041d5241e1000b4178030440450f008000070070346064421410741d41f0314111003c2d003104141c51810018441c149040c042400b40d45801d151199044447c8a21080e10303000c020f00301519881e000740b040c00001d0780c03040d182c023012948a40c4601c00711401402214110b1603409103d1003004040c1d4800101141802850380c440006009942c42c24103107544e801c0090340c1000e01e0480440301c801d40007851030700807500d010b0041c06182c0e0000107a0300040d0000d085000c3c000b5120025a80501c038210800303a00030759900410450210010080106d840c0b665250001c011900b00d003165164040c88009015079040d0000f408400d00c1450000c2c1d120368001d16840e198040c00003218107014100c01200c00580000071491180d00701200341c40103800610740204000204c40d10000c15078650008000c100345400c0011807094000d00f415110040013201c251100c6001c0c1c800a806401d00b00d12810b00804c618 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 643953642 1250 643952392 643952399
    0x1501060e01030b0d08090604090e03030403030c0c080301031203110c2506120c030b0d03090801060609050303030a05180d03051b16080913050a0b031005072307050d08040c 75
    0xe004256a558001e481c12510413802d0b0340d0034650707400035003095401102c144400514115140114202200e8140186d6528105401e0003010f884c0410503034400d02039240c0641001811480899045a800290f955201048030008402400000040e0140c83c0404070700c0d07201e1018041880480c0c0d00c8200031000404541004284070a000380c8104c1c1c020421780e510300d07050721419401c0440c1e08072003450009000c2004030002900c0030f211304015000201c1c904002e0007084004d11a0801070001e9003002c414052401c0e00181c2d491000078106d041094031480231400f1039403650ba4030703c1d4055900b029128171784180c440c000c00a02d0222102c5d03144031442040c1c0ca00c05161032040340c42c1802e0100e00c2c21440401034407203040c3d40e07102e03050142e005450381d4a85000078525200b0b8500a8407120300200310000d03020105407a0040b03800007401018a0034003444540394011081a065415241c0f1101020445006400b0a40101080501a400b40d00c046001c410b6010440750700c074610504a81d01040e84 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 643954892 1250 643953642 643953647
    0xb091522060209030c0604031506080102190e0a08190b010b0703090509070210060e070e032a06070501060305160f0501050702011209061401060e011115181501060e01 73
    0x1603000520300e01021030304800c004a44942c0007801400f8000d01243c200040000105071650f110b54015100e0800008100c6403005050017150000d10108000b90305003109500c0c40301c42d00380c40c41c03402c2c03082c800c1072403092005440e003500c0003006081c003005a42d0030304c00c0880721259025a1800c1140c010750305500206031940ca01c02a6030000d501a91f031030b03002904010601c4500032000d0050380641c419102e4880500c11170303008810103051419480805400c00c52000703400d808110f00154403a4005140b44214040c107074500001818001c03406019042680010450f184100700011749a5401d0270404400d06c4800207840c00c0e100300300c0c00400307480340c2d036690442d1080c0c00c580181342c0050001c010b90710144d84030b400c84081d80682c806000030035031031a40c0c1d40400c0714000000418400002801000089d40043e020b5160307040030f091511514140c46070260b1030f401c000710302035a160408004a054030802082c0d22401d001c5400c1141c19009001c01101241e001c24400d03080000c0a10310400f19a51 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 643956142 1250 643954892 643954921
    0x5010c0f0f06320a050414010c03090c060302030f36030c0607050309101a040e0705010305070306050d1e0206040609151409040e0111070318090b030303010b0906070b0915 75
    0x814480600c101c6407113001c0144094140648140ea0000103108400c031001004c1c41000c0c9107060a880c0003990301c442e490002d04880d00c6a10603000e0510500410021010180d40190b0094240c100e032051920f1125020000c2d044c4940806051000c051503507520b104000014078540ca1040110f4090742d0328404120b807680300446030031703c8079080703004014541026904625403940310a9013a95202d0342d4a00890100c075051076400d42c0031f43c0008010441540c240c4107482e004540c07031030140030290500700852900600c0c0080141004070108032075500074407030605250120390080089540703540d1400d00528440d0301b401102c0d80c1942c00d184501480f402600c20560070181a400c10703040221078001c20006100703101890320155200c22030b80c3d18455401c001050f40f06e1007911a02d901240028409401c00001d803c204c1151b8584004c9121a40d00007054034111843d901c1204d03030791681c034808110075004483c00200058201d206000d00c3e110086120007a07040b102105003526a940a040301814 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 643957392 1250 643956142 643956221
    0x1c0305030411100c1209030f03022a010f1b080f0304030305150901030624090c0e0d030804170c010507030e0d180506130806011403070e010b030105010c0f0f06 70
    0x2450b20000240002c151110206075a13800c0d040c1b000b003280d940e0f22550b04c640103103407040380141c104149400e114044008030752100060721040000c84042400040c2211481d03150f80f00030700810300e001c00302014445840c00700c5030b070b80400c00c19282d1025910054250300140e03022000b1a082a00240880b2000b0b2192420940003c01000260f442c54a42c1070003009580c0003404e0001080a011f0f40a07511281c4070b5000300f00350b100002d4200450900240502c1c0846d10740c511400b43c080981010030b41c000c030b109403c1a003090024018003841d885408091264a801c0405942844c0c100484541c06901601d446c803007a8054820044003284200c441904416010a4003003800d8030501603410000701030b0800c5620b03458048030b081c1e2103103100c0d031031709a09038080500d6405400102c2d10a050074031490300140303022402c5c12a9941000840700b8180814010b4074100402c0d80d0180040c00450302e04170305401d0704540e081c64606000d0801e00c0c00b030503601450540d0502c0d4060500800180000000c03040d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 643958642 1250 643957392 643957397
    0x507230909012d0912090f080c06040e06060720040c1b0602031f0f03030f08090d0e151326070b09030c12210301060807030b1c030503041110 62
    0xb0f480201c4881c8440008290fa088071142c0d41d00903801c0007522503680c2c90000e1030b07591100010b1901d0060030080d0034007560010011034100781c1100c401905c600065806840803018030000700e075203a102060041c041c9400103000c03011590402008101000415901c011b0705590502841c11829001d45145454015485045800000b40401700b00a60301442d0070501e2480442000900303010540501840d40e00541110441e4210820800d40c02c81c000c110140202d04001019140601c2c4541d00c07580851010000d01148010300240c41c0d80381c1010500c904800d0102c1a1508008070300e5041200e1301d8006c00c1440e00c41004419800c1003000909074a84444d00000c28a807030405c2841d48294028215480c1c01d031262034181201a0340b8100b80c100c0000c0d0040042c0743d1a240f0341d080b000540c92002c2903100d14801000184010b0313a0140985621403681e08020aa02c240701000c07503104842e52400301803019070f2110a40c101a440401107024600441e04401240800e00c1008020300002e00013801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 643959892 1250 643958642 643958681
    0x6021210060c0308042f03060f0606030a05060a0504020f0a0f02031912140115080708010302010e280807091103090304051903080d0906050f040816050723090901 71
    0x42c1c030911040d17a20a118920004841c20940c0612040000b071841805150007107449101841c2800c01000e580404c007443e5116035810a00c01080d0144001341a8007840e984602c00911079840d0203402400400014104550f264007000c0c0094448d00280960000215a80d11482c9140c0c0300009170345900e062418018280e01c200d1406640c0c24209036401061162034000c45d4001c072982b10503803802420501c0000d05881300d4080c00404181004208200340b000c42001400543d88c000ca8105070114295003c524807a840510032042c070005d1214144410023002c0c0204400c0008124030303084690b104810b2285401641001055010071950030b110790b030092000300030341c2c0b500304210a10b00c242080035800040d225203035981c183e8050b020780c40045440d03030f10341030400915118040d80042900c3d0481c81c60f0900356501803d520541e410886604442d044034410b021017070241100524541801c00f616113010303040021800a0901d8991050700345100103089044180114100300e0b102c01413285 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 643961142 1250 643959892 643959917
    0x12c0607300801180e010603030c0b1f0303030209031e0714041b0c151401050109050f0a030b0a150e1f0f03030f051c09060b0a1802250602121006 64
    0xc25000c80c1003500c03816807a445e000e11440390038400e2901840c040d5850000e48140c5003000590300d040507211240724035145010b407800e41440d41d052000d583e030500e000341e540d9950000181c501300d0419004520844403c44003102c0751400200203046580300468540004121805c2000b21004192004120244000c1074000329100d1f02c2141c4059200c4c41c13045140e8101c02c00d1072401c0700c0390070000c03240034036016005100940e08021040010503007100e0814001040d040403400300d100c03520004000716a050040303242c240f070a410400701c084100120b454407940e200310703d400d041400d07901d0554051002c0c0c814140408000c01100984d1071048041e0000761450b901248e014500e003a0280400500388400014601421036065000b0202000410301c2d6520307060900803960801d1070107108200c1440100612180c0102c1d011215030300000060b11810030000c0942081d2102801c0c6600e0010404110100004c0d50701621b00d158441481034203640d00c1c800d0b00c4600d41c44a000d55004640b0106918 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 643962392 1250 643961142 643961159
    0x4061d0c090601021911090a090809040902060417420601090b04060c02120f07050103050a23040605010e06220e060702030702011706012c0607300801 66
    0x301d40145044c8101d4a650501026000a0b420114400ca55101714001001210310b4854401a0841c0c24060100603141b407694440301c03184200000d507401540c54044400542d40e440c01501c00408400980c00700c0e02609008c00c03071322041300c45180660a0b03e130b1003030120250310200144100480fa1400e20701009036924100b0348840d802006d03141001903030100420459441400b81c03004140c00d80310308581300f9082c41006000540843c030844281d1180c13503e400e000c5000101c0301c04580f002c2c01e000880f070b2500c0c0340d542c010f0a1542c840d03086900800804034144103800d0255489180aa1400c210a0b602c402c1d0802d50b0f42015035170300303038031664118010080c14150f002e0340c2c1010030810302c0012480214801d050800394200e0391503015030000b080304800d40d40c000c0b50003007003100c1b040d0640546203450400a44899698800c1001c80e009110400d805140103014030f07450510b0041200e5107500035881c002080140500c14454900d4158410407090015003c0109840c0081c4d1100000b580c2481d406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 643963642 1250 643962392 643962409
    0xc11032209060510111015051206040302060105011101150303020c010915090b0d150b040f331728051608100f030609030e01020d020304060e06040302061204061d0c 72
    0x17094035034020040c200342800f10034807d0850000c91200307200703400c0f498070381007101c0758159034442e42d2603400c50801c1100080e404a401c0d41516400d00b080d40940c8414070202d401441c2d213108040d00e09142000c0841819000600908000800d90300d140d0840d840d02586605210055a07250100b074164209010341c00c54040604400c2e44040c000040c0c403050010215000100340c0c3c8240c101c1100080c0501c1001e0032105400c0280807010b108101500380600310440c1102a48c40b5101b02100c0c24a003648418440d118002d0940c04c1c035140a08a03081503000c2d00300d03548e91401c0d11b103041d103105100e40e02d42c941d05004403442a50200f903010344400005170166004600140392481d908000200031580c0b032131034000c0c200503600030900000c00484074503000c4c22110508528a040d03502401c0d0000c0a164000126401c5e1600b614001180c1c0e00c1202c08508507000380e8000070351080380494803078114020070302400d2043c1d000706001e00c000e00c0b00702000b80001ca100c0c24600c1d00f40e0007814a02c061030070700040c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 643964892 1250 643963642 643963667
    0x80a020703050702030d03140604090c1a0c1f0606030504111e0d0303020702090a0501050307121e080a091514031e130b0f0610030c11032209060510 65
    0x42c814070700007640c1c0c0040d003883c001440c0680441c0da21124038090790f90301404190f002005480c00c10903c640c0b62110040030140b03101c2c50000c801d43c003140c003640c01034550a4070803440b000000c54014807001d51740404030240c0d1032102040280b4007100041c40310311070301a0758042c1c0c0d00006060b0603142c548045c0118001c0c4011344c8500000821000d46c0c10b03890b1101c0c2d10ba611402030342d0068541a96204028210740064800350106042c0700050040e80c0d00810b1140c101e8803000380c0313089100e180e1b00e8468100141c51581082c0204588445014000c10000a048103000360303449494154891401500d0940040800c8c0c0c0052207d01030544c40c0487c1200554110240c041c09010b80700c128545c0c0d41c0030302c2c4102c58091600c540c121034482042151720395650400c84540001446142850114558074180710842c0101134031004200c003814050b290081c0e118046005072582c614155100003100401e0810550705210305250000d031484403031094205440004014200440140710100d610703410011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 643966142 1250 643964892 643964897
    0x26070509030f03040b04060e030606031507090503190302160e0105040f090609260408060406021b0a120e010302070c0b03040c181a060c0d26040b090d050a080a020703 73
    0x194602d00c80d601040a44010850001555591070070201d0040104d9440c0960500139485078046c00078980e808a001010900c41d01209000c55881c1c410071142200703160b2155405000e0244d100c1c114840101c1e100c90820b0003a000c0341c03501d0040091341c000c1c2908a00c01c5c003800c0c10b5080300503c07184c0b074942c02103c0e25006c058404a000d2809459a000f280e0181508031051442c03125601015840340680d44485d0034200125401d0902d40800542c071084000c0000380b14980c00102c1480440400d5203181c0c0c020b14003411242051036a25041442c8801c1109410105010303000908541d8800d008550200340c1c014a111a02441c0c030280e05181c0d000584125503241c1401c10101c0c01d2034001441142d01d4040c83d001085042c0c03ca11078009a1030500c0d0014003c110400c41c42d80c010400103044200b5400b546003440c90100300c048014401000032290034503509960040c44103201c104040c07e40143c078404155a00b41d0f416210941c1c0a21410001c0d20204d5110b90003d0f0306e0350010360180c800d4038000e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 643967392 1250 643966142 643966153
    0x402090105150d020c03040302040b01050c07180e060412020714060f07030306170102121302011b06180f0c0b0a02060f091c080406050a0618021b0a0b072607050903 72
    0x83c1840c01682c0114032441e2079a400441c0402c00d5150a014031044503030203091061401c41860049a111103a5000d0000c030580380800c0081c02040e558004216803200006a44040c1018501f8819440c81c1100210040c4104000801d4200004507104071640000308407505e0140024a81e080541000c0130940c20315070785c4c0500240402c940740030381120b024510001684c070b01562004440e02031002e049a010f03808002405801070b40c1102030245c0c0000075164609500300d4928040000d0310500900e440380c1d60014030300d038013000071041d01080f100f403240c408000c02d5074072006030000a009031700c2818016408040800e0544041d00240c0703810440c05001d5072030b91203800c0451107003540200060340004d0340603000c11047c405584181da4001c2c824983c184a81c910b000c58070089645c5862003040b0096000813203801d89403060212510794050041510403510007410039600e10b600449184012500090a500703006120521040700c44842c1f10761500d507512050300448403500196290b0740c051058 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 643968642 1250 643967392 643967407
    0x307090b040605040c05030708010806070c1e02031207050f030a170a0908070807030e010306150f050909041410020901091a070611131706060f0a03140106061106040209010515 77
    0x95005c0c2c0013000c2010b0b01c0381c50f0f0700d0901040040040e80c0503400300c21907400100c00d00403015489034021251036005401008140c04802402420800404009505204150041c0e112405080c00f0f0820a0f000302c0a0394112040d800c007580d22485181a1708000a000b50501003000940c5c40384650820300ca11800038843d200ca540c3d5120355800008269400c400229200003019030100688100c0c01c42840d09200040c50031403420785518a0707220890034402c00d041c04d210032034415001e4942a0100412840c070718102420560300b550300a01c0c400c130150180400703605070400c035802100c1c907800701a0b40702c0004d00c0c9003610210082600c00280c51a40750700f0040c4030041060390281104200b1114200d55503111a4202c048002009a210440610b041411525000030100d043d59000d003003540d07601c000faa2807500182d41680580c00007014480c4011400c03003240b405500c140156040c03502c0e602481001c40d40c409582d0403040302d00a40c041002e600610060402c0101900c1c140301d403001d000d0903d01e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 643969892 1250 643968642 643968649
    0x207080417010510051e060c10052406040b070f020a0905070e120f0a11010c14030a02070b090913140712170304030801060e06160b0f01080c0307090b040605 69
    0x580c90300d40c1d41ea91190f050181403a00034810308010901180c20381c0500c3e02e031220b03207034110080c000264031400380442c1c1401050f10074426440d80c1c5c00c042001f00210324020341400b0140036064104403c240010303010090b903051040c1150181caa45802013070a04250340c4d9100c07000f03101c5034000c83e009080c1110004252849003d414042e02d00380d210b10700060280d81c1806071150940d80341d102c079a0701c466004e01d00e05201040c8074690f0350704105030700c011040160060700c9445c55003000405112404110308405400031014155407d03003a401e990403a6038802e820364003401401001e076442145100800c10a4509060920085118209100400c052100c0d12801c081c080ea1000d0624807000c0001c000308064407440c00040050292a18110b05203034900600c840014050402800400c604441030769482c5021b032050b1442040300461000681d14101c001e0f0401511146ca61000010020845035404540000b090070003030300030010b031882d142d030b8200074160510742715030000d50340c42000c0341503103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 643971142 1250 643969892 643969919
    0x6051914070602190206061e030c06040605031005040c050901050a21020c0f010c080103140a060507030b1e060d0213030204181709010906050d240f08030408030d02070804 75
    0x180180780041e203c000c6000a074050502c208813160440d08200208145c07541c0d1f2811224140d0502c2c0c00c0f11000c0c08041001c20f10700b5609440caa684064003203800110380d0f40c810011072141101c207000a020503138420600c070950350714a0314500403420503c080c1d00c1e03951080e00904031081062500e0814480e00e002c107074507a00390f03403e202c00e4016000074030303515028010884081e445040100801c00080c20050003401d510040c08000c0840e07401c0501003000513810403110340300743d1700300000b0003050404203800340080071040945400b41d068451400030800f9050755210540380050002c074689101901c52400942c404084104000285400440541c0b2107100e2407141110a050f4104222a64100258607034628514610040030030010b0324100d0740e10000200444060342403094031400700d0200c10b4003801d101940c01c413450010b0803040c0040114482d5940403203541e420002103458440288589070f01c218041e442282c0d00c200500d0608030b00980c02400c40714020381107070b8240317a191720742015040c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 643972392 1250 643971142 643971157
    0x71e09050c120c041e0b16020109210b0105030d1e021603050c010207050d12050702060c0313060908010917071e03031a0a0312111e071e06051914 64
    0x200c3c008034040c081c651400441a14440300ca0030190301880c940400200c05101302481050074008282851b002c590040d298440074001c40504600c00788a00521106140c00c280010345001d442c450002420f401e010400e5029040f166039030000058801d000070043c1a10103691000314462003040c003801e12451001c1001851044010340070444000000920b800ca1f0381d04071610580951000c080090562a140c1c40304040c282000e0b40c54408a0000038581c0c0140315000309907000000d41c0001a00701c2014405c140c1e10980c07a01a103040d20b0f55025400c944510700010710820990134031401c90120400900919031050640e801c01d03036100d0b204d07140f0510042808a001ca07454034250b1642080c8a142030100c3d15007602e07031088a62031511109504080000c5044c103005201000031141e10091103040300081064140f021800f007000302c0d0035a1081c0600c140e00704c11401050309050030110380e410700c003210800ea5a4504008114602243c6241c00032040350031b20442d42142900c4440400107040788 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 643973642 1250 643972392 643972411
    0x32706060111071203021c090b1204050a0c030807060c08060a05041109030d05030f07030b0a0504090f0210050a0212070b0f090a0b07051c0509190813080609071e09050c12 75
    0x2c0d6840a9241c0310745003640c441e0048c49070000062058106250580343c80103031501108a4940345c5040450074100c44002c080c00d078410a0b0703004002c2c008000300521489100d50000c120154200800322102102619400e41c080e8650341c00300581d2502e0741000c10520341d40400c0e946000d40c8030300060b03d02041038065034003040d0040100034408640d03d4005900643c2c9080600c002d0310701c40c00140303c1d662203024581c41260349045d41c4050010310740c10115065800b034400d201e018400320000d022608075214920043c818806009109200071040e549207a81c00701d07158166403154405078103010002024400c0d02c1c4501c00402c804640c140c0c5d2028000d03845920740c1c5650740c0076051080089020403100039445801c28040c40b2420780006048041c4000d00d40c480c8602d9051803030400f0b0320307121321080702941a01c015004540c0741c0021a4090003001e0714401c030354000c0c3e6100c0e8100b1440c1d80f2a5040c482d160032003003080103000110b4000c254091025103490b407400c007000f07031110017400054a80002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 643974892 1250 643973642 643973653
    0x9010f031e1e05070c0507080d050703030f1e0501182c0f0106030c0513050907050f0607050a0c050918070b0307120504030804060e0f07030f140d0503270606011107120302 75
    0x5100342070103040d02510100c00503099031000449e0181c42e51080881c0103040660b94101d04c00da900c0c190707000320134101108511050000d5604c40c0030001d000c0a000c0c003000c10340440e00a1852004030300c1070707906c0344040040c030f000384420025049000400301c8100741882e000c1d0010800201d0000e00c40e1401540c4250025060a421701051050b0014103000700f803889031400c010302c042503000054000803203100315040035020440c0350110b5501d006002c802070080c41852184010450024080d400f40d40040d0b80c260a02e07a0340c1440708000180000102c021038000e00300900454021000555003e00e0a040c0031023041d00c0c1502030402c807001282c0079400205403400384000c05c000d0303020351811489003400800a5480c0824200c4c0c07034080901c801407184481e000f0507000c00101100351f01940c118a41034560102029501410551088403240b00c0e00a07040210808007030500d152500c1c03c002c1c00001c2c0003507030312040155452083c2550310040d074498508002150085035480500b040e1003a805400e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 643976142 1250 643974892 643974917
    0x2150412030305062e11010f0f0f11070803040c0b0304030e030c06030907061101090816170f030708061504080a02090a060b090607210509010f031e1e0507 68
    0x1c0840c3c030041c01c0c8a2080c0101400c1d9040320140e50b00c8042c3c3c580d804401c010191049600a8030420381c3c2551199555081c010f0340c5074500780c50341c481c64040c1280f45040c800460600d8000c0e0465848440c00487e071841400301c080801c40400140d40e009100b90071104031aa100e1030300003420b810494080300010030000d181c48050400780402c445c03801082e10490b0a60500186050326421240102b0040141020b10700b2130080c425007210144640020314a80d4485480491038012503a4083c140c071010744108200b03040600ba0030450380300c104203040e61421a21085000c445410001d0141c50b0710450403440199800d41c200c0003440205032200c010250031601344148541103600424000040340b03003010400c0303002d070b1280807034100d4403003203820f00d643c3d90b0a460001d030050014507204101c94088051600c0c0310341c1006c0204a0502d098881d03030056401d1000c1182030741d50511664810450300b100a038141c2c0342c10340100c00103541d8150089901b01c5030303a84950468000b15403507000910300160700d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 643977392 1250 643976142 643976147
    0x80109120f140f07030309060204030c0e010b03040b16030b090a05060a090e06180a0c183b1f0204140d050a080d0e0d0207030302070b130308070215041203 68
    0x1a03900c1600360034410030340a009a0b040c007280c001c2c0c5040307014103240082e02c201090310941c840d106096020ba4115203a646900707008100704550300411001045020000c1a640c00990503a4031076a8000400d00059581c00414500c100240c0385450506480d0b20100502d9030324284170920030991024000340c503241480410200500551000c801c0c1c5250594807141e014001c0745443e4400c40090300d44e440d1940700e507103040c40c025042e1405002d400034070070041805107881c5107445041503812024000ca00c0c607803601d50012450040c0c02056504503180940030318080044182c05211888152100c012100c0c180c05900f884090f5030b8035105500207000d00401c81c0841e421440e9a0703041e80c054400b0030196650640d03030021103c3c081c0104002103400d505a08454105c0c1900e20821001d86000301c4030040041d5880b041400124094050701401103110b035028829100c0c20a1115540d4201c00d207181ca0790075040e40184001e80e0003000510300c40004410180080000b0312014660302905c0c0b070b207401c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 643978642 1250 643977392 643977407
    0x1a0306220e1507050c03122802030402031006050d02150d060f230307060309110a08031819050111030f0301080f0714011e110d0201200a0c080307050408010912 70
    0x58060000c14480c00c4007240b00041a502e403407101d101000519224800c0700b17800d948d040f012000c0380b00f008122280c2900c45c43d4002d180551320940c202c0701410040d203e010280c4a140c002c07a80c00c92150b25108005d0300d040c0040202548500d0403092a0000114140050f201d1039003203084440a030b40010841c0030081070b20a0103c20801c0e00700c0c1032201d01d000004e6291800751050f101090384410076130050180c40385180c8504403006000d030003a41d544a10039034890700711203a031248109000c2290403280c109038415401541c10310000f540c0c1c407401c04006491b14084d200f9041007078803041c008150070403084001903010b4040000180464a01c050400c2e240440d9074020f940401c40c130307103180701403641c02c140100b0101c0004078084800c402400001c83e285d411038648400d4034402e8403c06080c0d25010341c010b0240c030344070101e050141c2c1404011990741d441f45070501c00000300c900461001050030200136580066442c54503520f815501c00505080d07517010841a034000a803800f4040410b504143c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 643979892 1250 643978642 643978651
    0x203070503070e0c18060304060603030e10080a18020d0c0e010b04140f010509031203060406080c100c050a0c081b0319021005040306060b040603061a0306220e15 71
    0x240381c0746040003610300d010f90b800303000440302c20703804295141144c008249000c01144041e1065803a0b2402d42480300140406110560100b640740e0f10405850512031440305051256440350899a114020010014409401c180840c00041d050180040c2d9840d141503103c10b000d003c690500d203003449135000c0d901c0b2041e03204000c2c1d81410030081142040750782601c7c00c00c201c110b4052460180e03000050303425115504140750726000c0c031010714000e4002400518003c04090342c041102c20b4507a000a561400d5040007141d01038602c0c00e00310b076030503c28000d01d182c240c03141b4142d54040c40c441e510186032648039000110540c11102c10409400b000d0010401d0000c8110300404036071b002c000001d0b11180050700c0281c05030048003030103920700d801a0b00703c1d4001e603440481040140d545240d07400c5140c219000b94800281041c000217604032650485800c82c0c4804100149140c8a8408010a00039170f200307400d003414401103221100340350740d100308203041504001501d1004c086c15a0750504400081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 643981142 1250 643979892 643979899
    0x10031e1a190e060a03081c110703080a02030c04031a0703150302061b030405062106040b130b040f0e0607110321100302030f0d0e060414061b0105011202030705 70
    0x4501603407400d21203240044841c0c41c540d00260743c5a500100c0c0a5000c84c0d00080d01a01c400a1416144914214132100046090342d0070440100b44558011191048020107400079070040045000701e61281c0c021a081690f4850051600c0d5403070380e0b8410a205201640c0c04074450890800c001c007a0140140300c001e030002010100c0c5030b820344c0c1c0081c1240c0a10180c0100e0312000244051441808108031009400c1c01008691a90001d41c0d0320200030352000e14494080030403401007456403e241c001c4004444000300314200d04001a06103900412955622503402034039840117600d10101d91056903800744a0101510300c524005101400c001c0121500b01c049600800c90301007a10603026032076143c8100d0928200b11038442d08140340c1d62484540000e5850300510340c003403049840006440d00d40c1540b030703261000ba00140307c08001e04d0b0b0145115981205c100081c0c41b445c1840c02c81e0060405004a01e03500c200f00c04000138241c00c551091b0000c00d03545000c540e0420030f41c5800c0040c03070000c00045 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 643982392 1250 643981142 643981159
    0x90f020f0d020a0c140a020117070207030f050304050901060512090705010206191d01060f060e030c0f0d0b0f06031506100c020114070507151d10031e1a 67
    0x15104485a200c0d051080e00704650100e40440da0b00d1113210030b1a90f0039000003400b4030007207000d08419155080139008a001c24200d120108955888120380e9201e8035050300585800e510b0341e1603102d40710b00302603001c0302d850004000103e42aa03665040c10b010388120f80e280c0c0c1e10340d20b10303c2c08013007485000b42c04503403a903004850811080c0c1c0d00084842d44200e0b0382508188103110031040c0005040361040801102c2c50191182510348015446102110400e002c041c0c03000e0782e41c010039a10008080c401c103030140c01113101c1200500f4048112001154040c00034680d69006458803000003a0949100000310b041e01d0a2058034035042084615135102001d1030446400d200d07000586034201051450144032100c1c18000a581c002d803580c1c0b00340c010307000c4219a11000c038500b8035100d40950040c083d61b452070004d490740c0107100c0c1c00d22a0310b041c802e4204664429204042110603000c459010341056201d050021800844582851a03594098004600c07891049039035042a20760368101c074012000d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 643983642 1250 643982392 643982407
    0x3030f03072a0f03030e011509020c06060901120609031116060e0114030619081014010636080706090302030c120a0609061d0c01020c04021806090d02120304090f02 72
    0x1e404001c1095031301d410006924041c2031021800340401d00803040712500c109000140f244c1040d0010241762009209a45065403403608115440710207000f034031f400140c214160f10019a055000c02e00f05070203400c0543c0102000e000e01450300701800344141040003000c80170070110f6000300f01042e0442003400c0105040d03003002c072058242d000c020b140920402d5070191440720500401c5c00e030310103480600b00b035401c4141c002e441c510161420f0000f440c003501442000003400c5121b00e01c035001402d2413440000a405a5180c450b516608040000a00c3c801a090000d08440104600c40c020801c0b81c8032039030b0162030350042500742030000c1003031b41c0600c1100c20302d540303040d0001c03c1c0c409840b68032860000e544034290500e58000c1c000d491920300c0380c4444410040c3c82107000100d4400032070f401d03405c80d080c414041c0c050005074052280800304000d0034100d1b4601600e0034802078141d080002c0d1070604618416000654418000c66031180030b504001020b216242e0f440c0644009002c1c5e294040d89003464 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 643984892 1250 643983642 643983653
    0x42d06060c0305130504111806070f15060f090606021009080a0503070903020402071a1303120c05090d06020319110d180b0115031401050f0f03030f03072a 68
    0xc08401c001e04108001542e00c0020701c1c020b05290140c54054810400ca5220300e1583c1c0380d40e4440390f042d03403114111107012449403034485c040318000c03540300c41104014a123540c5c801081c0e5200411900e14140c0301e1902140680d501c11169005241944000c41c0d1945410006410400c00341a0240401d0600711500c000c540088200c2e101c09045290481e42c07907583c2d07401103491000300c0e0802075209000083c1c00d010310140ae0a00300088100f2541c078003c91300c4090003900340207501000100499040d5030b669a020525a0140007441c007181001450078080f00002440c074141e40b00c3c100e50065000c4180409880380300034207a202c140b0183d00b003010340440d010004080c000e221001d1059511250280342282d00040e0702e451450380005201002e50311842040c000c0c0c2111300c00440024548800e280000810420300d6041b039102401a841d60301c039038001d001420a1800c00b03035805102c20441c20700070340c4207800218480c220550340c44203200c2c18946030700c004d03001241c08601200100c41e03014020a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 643986142 1250 643984892 643984907
    0xa0320010b0a0312050f04030602040e06100806060f0c10020424054305061f0b0a050f0304030f09051e040c02070510050913060e0106030c020c042d0606 67
    0x94012118880460700b0740c0017159a40320b11107941c5960f40c4040317000000c008098024000341d030043e8100c0c40d000e644110030b1042c1e03090449030010001d000c10000c111641804d000801000c00d0000b0b0040c90540182c1449103003140c031b0b011202d1481d074000323010401140805a043d035a03102078003000d101c0221a250041c6180a5607c4c0e149038040020078040c4020344102080f0b80b11341042c24544c100303424594a03046052410402941d00d030142c4000640c2d040600c0865090001d840c0c1d081c400b8403410040000d030390fa0030203a2a1014080d042112010408015018500c03031131099440f08000031020100800c6071500b94042400381159284514981c05104031405880c1401c0c0c03800620000741c0081245086c0161344225002310500b90a0401d082d0b100e801000100c01c10b07540f401c5940001181041229407510414400c1c010b003000500900e13201c2e4002c10403498075841120300c40021310000070100c0e0b00e5203201101e4020800b42c40e5010705046010380d4800881c0000402c03129161990181c1002d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 643987392 1250 643986142 643986149
    0x60b030f0a181406070e03060606040308180d2301140406090219090b01081506071205040510110f2d1005010b1e0301060909020d0e0a0320010b0a 64
    0x19260360b0340403210040c4400d86001590440080842484841500c0c0d482c0d140c00d4031030310001140f1403090f0300ca0b8100000e425006071400380000b49080d142d45c0782e4000b15005054840c2840b4482c8120741880d40e180328404014901560202240240341100c0e0720341030f51101010000359060901540c15032031001405940a508000082101c1001c2d10008100e00750348910904402625880400c101c0000c0d48106010303c4c0030b803134480d9952909159401110b1040c0901d07130340300b00200030341c1c00050680c1c031200c15000003508001c1d040903111000110a01d2a004503440012040300c5000e00d0142c0400810001104520241c00c1c017a0b40c61541101d02508056126a101041241500701580030030000460600000040242c2c2d6112a0302440d694415140c42c00990703072003144890800d50020490381242d5968032a4080145040c0303c0c440650010305c06442d4013961546200340e460001d0203015401c5129a90b003104d10058805a05851007107032181d06c3d600c1e031401c0f140da1b010743c4070512128240c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 643988642 1250 643987392 643987411
    0xb0a0e0411060a02010f0c08060a060206040b1f0305030a050d0617100b0d1a100b0a050a03090606091803030609020a05090409050309180402130c0c02010e060910050d060b030f 77
    0x2210f102c0c40042e4013604403242c10034602d6242c1b0030446605079011800d02e0183c0021590921195603e800880c0d0300d903800d44015150140c00390104d400301548030000b8035482030700f5449a0809603651101e50854020105032004158002014440650a0f02c2041d01030411342c10418074071560301c8001a51505c1005402140710750b2103000c440207948181e0b4581c0f411354400001c600c8800c0720a061b0b49142c000b0783e007107003103078a92510204400c0030420643e40d0401e17555030745a0130450055001c0b4050140c2d0203041d903640d942d0700004a14126513001d0210002e5030041303101030300d64061030000c003291210390220760318030b2042c4030291550343d01504a8201160844000c01c00340c0050502e00d00350b00c5500501940030302c00f91a1030390b0b01625081c40c2d0703101d68001c48240e140d05581000c0c0409407002001240005a0304150110042d17000754040c40004502030040c5080c011120040b81e080b800720304054001c5074011625848180f0503019000240c4050008642142081c040c00941c0c1c0d0405041c6404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 643989892 1250 643988642 643988647
    0xc150405100603110f030c010c030e010c0f0305030609100b0d02250309170d09030b13060f0e3c0f01050a0207140601050102060a2a030b0a0e041106 65
    0x51000c10400c1c20240c054401c410009580c3e607240840c0e40c401c10116803400380020260400c420b01c0d0104820300c0102060b1030740030807118283d03000c842c46082a01c805040c0311410301101c01144005500500c43e5209403034182daa8200801007041032040144001001c100221090061850f407100f0740b411620741c032fa800f580307500c4c520680300615180c0b0720400b02081c600c2c0d9100f01c141940b0800c90022280c20300d0b00340442c04000401e454031141e21b0080580442c101042c20000210f075410700582c041d61542082084520710f681c3c4001382c0d039030300759001d81c001d071510aa00c003442d000780502311004000307516047c000104404504c950303504400a8841264010b50700010100c002e101c060781d01d5240c1c0340200941c1c602000d42c000250041741c426115020205001d000803200084c1c45416101c0507001007200365150b549038009002e401e18840c45c0d03c200680041801c4d40d1160b41914141580d44012610034280c1c001d115115541e0b5228000c011000002c0c0408140301844a610148041d1403056 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 643991142 1250 643989892 643989901
    0x70909021305030f0a0b07030603020901060e030a0203010c02010e07050a03050c04150b04030807032a080307110604050a0b091605010e120a03090302030c040207110d0303110705010c02060c0c15 85
    0x3004050680e02658050107480e2000d4210b960200d41c1401d260f20590006c0384c1500c496004a00325606400000e41110518005201d0309001d1800321030030384030040c22600c3c1910b0550100303081d545207081400c0507039110b03082000c203041c00b8859900035140c1582e50001252540c2c4803d56103004803040c160045650f400d200e02503001901001010f40340c03c10701140e5070341c0c0c3c030301d002c3d103081d400801c0075000114071404425000d40030100f0708500003040c401a100300c1941e610754030046d61000d0000014040c20b62001010701009000840c8500e0082020f0205240c91341000070381040e0080c00003504d030304012224801c140d01c0c100310800356032007841c00400b00310301100030031041011040d015426100d003804d04010503900520032b6007528030940660700280c00e10002d10040e40503060700100800e440b006a40068100f40da0b14034500b60081c0307004510320000d42541c003c90ba020f14010740c1e840e515481410600b0b50100b2200b0382202e010051541341c48100824943c440d21488a0b64a09102440118 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 643992392 1250 643991142 643991167
    0x20d03051204080301050907031a01030f1d010204150e100806032127010921020d140706090e070c050f030a05120108030a0e0d0303110d06050f030607090902 69
    0xc818078410750714080c095080074100381150350803d01c581c80c4540049000220114424041e0501031030104020503002c2e6200c900560240401c82400350b1070564410801d07102c100c00700e28004891680c4400180d035a4241201640250344140300729007482240100303444603888081c1030030b007007541a146c0250f55444600000c0e00700741100108521800d8100c0b101d0fa910603924005010110f40c1150407003d403030b007610120307244c6203ca00030f080c08281660002c021503902981218140c040490b900c1150f40da40d035000a401039071324041614000310030b01c91160b1111040161002030710207810400103191030318400c011845401082c3d8020804101902000c000080043c1c1c3e45800c146009d4980b12000c4180c010041d8000f0284c4903607048a920000070380c404003008503440c450071036480c0c01c0704003401d00c140042d5075800c0728102c04255640074104510381e511005003801d101d0100e000310300c1610b810104407203004040c0c14144285c00210502c0006a040801c0400b16004414050b03201e00004120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 643993642 1250 643992392 643992397
    0x509030a080a0b0d03090509060a0312111c020d080a0b090412020313180609020c100e1f0203040b0c03070f08100f0308120907030f2d0605010501020d1b020d0305 71
    0x6680c21000d136007445402c0503003001c1d4850a842c020348030000c160f9a80c0c0104032821600c1e03c0041c00e0702000b101e040401e58800e0301c00c0182450054100c070303000c045043da0300000c8521400300c1c03c0160020080900295440a00030342c0111390444180030105410001640c0404042c0004008450300e8050b070503028001c0c03042e10b510b09609070100207180d41d5401001c40740d6400031007000c02070785030030000719003a14207100782d41c0588101c00080c124a14240420f0004001c4610310407054885c4006101c00a2030f50455450070304450800544c4a041500d400d10040030080d00070040840180100880140e2003981080508120320708040d0341e84400040039561946600040e86c1c00d08480e90100c1441821001854008e0151103525010f58a0491240d200e5007180002002400388400a01c089400c18003003c07804a82c0e81c409195007404a580c0e00e03800000c080003162003589401c0108115030b0180a43d4040c46010b0401076940a002c000302807442c0f83c05c1100920409040094509041c030900a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 643994892 1250 643993642 643993661
    0x812010512281a1003020f0d030813020a0e0c0703020106050414070c1410020310121205030a0b0d110306060301020f0f0c010e06090f1b0901030b0a0912210509030a080a 74
    0x200507445090144c8101007040c602d01050340240c2d9025425205400c020b9600351841e50980c7d03417100c460f00d030320f602a0054450400c0603070340040752070804141095070110444c01141c00002141e650f40c820700d4080d017524401c1d03004130701c65454400c41d0401c2e020244811503001d400c40c0f4000d1000da4042c986684403005418150609225500a0318445080355004502460000e00080ca007650307030ba40c0c0b250328142c60210040c0b145240c40020b041c3c0e00c0c010005150041191100032440790845000306200062581d0160f40c804003100f503941e940d040c1803013156080f28054000350700c1c001056000800f90300c140229540f5580d400654900c411600390b00003542d038119002a9031003400c0c40c0c2252075541342c017071841d40c5d614040c003a030300e0303ca081ea2020034110016000e461084240c1ca075455002e040c00005040410083d00c0d69400c80000b9a039015030f4190000f00d80303070006106021100300306e07290602c0841030701c3c5910b404144984044000f0641e07070000010328111030316555a030040005085000d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 643996142 1250 643994892 643994933
    0x9060901090b0c3412050309030615040f0c0801050f1c080c06010b0403031422320a03020409021305040f121701150c081201051228 58
    0x660310f0195800410402e00b815980413071600105924090f110040394551500452510002d0f000c10004070009441905180518296410305a103400400c0c10300404807170560110390b020103a00e0440c41d0501c2030043c204c4015000b003044030301c1c520f00601400e0042c040d50744140c21060154146a0f81d10b100500d903a4201a030030100c3c0141464050201d400071070204041d801140004550001690140c030300301ca406944180250f20400c0c50390109034841102e100c00552030340440840c12020398250340040c000340d51010b15030a841602c4841114035000d804c910021011901803156840c821084290798040700d00080c40211440000c050240410010800c10704010402c0705200004041c4865140a000218001540b00e00202d412580c080410741103290400014050070044440c0c00c0c000881c41d041042c80181c203501e85440301c3d08800e604081c07500c40c84006000d6800c012000311038984143c402005100e032959608a022610083e0b6200228071030019002800000b40020812900c42c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 643997392 1250 643996142 643996147
    0xf060522081b1203060109060f09050405102607052403071b0f030801090204180e0c19080106050d03050307050c032502010806120718090602033909060901090b 70
    0x503d0f02050700100c0e4100d000c2940044002110742c0a4441001c20031600d68405007100e00303110402c80281800f4100346824a07a1000215804d000003212290b840c0140b80380e928045004490140b03004065040103000381c03040340743c110301e80544010144154040741181c90712555403000880b8820340d00e90300d02e00f180d11302500c4142400100885020a24042d41d5114066030300d0321544400d0384518850015100000c0c40200281c2c4020741c03014001141180582e88400c0804000a2400d020704070029050306c1c40c48020040c51b03a003403081500424041c2c8a0650080ea50784015003603000080ca003800340000001c00c0c40310b616061044808400c0644d0303100c42070304201e89400c14103103501c00d022400710320110702041861604a4070a41d80951050041c10118100b07a41420080a000070000c0c070151a40d071002c1c00110a400074600c150700c110398000c40b40009000d00c074281c600c41400c4400c01101a80c00c0100356201000b02c070b00380e401c00c1c0d450340ea07500b180b40d0040312414025030160840200c007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 643998642 1250 643997392 643997413
    0x10212070804120201110f090d02031b12070b0f210f0403030b0307080d030e03091224040b06091905100f050406050a060c0317040f060522081b 63
    0x32156450080f4040d88006030940348958099080b00c002440b00314000005029003012800c1d143c0040038401c002a04c070b54a410390741d5020a02c0c00ca0900c000c0c407888020170315618183d0600032280748a55030100d006001042c6098000c0c615481150b800e002c0c6c44400099940504110403840620b5a42d04446201c1c54507000403101d1203075001b07442c11000030b420000280d459140003c0d0040a681640014148005400307606a000307000b490742d15882c500050161100f19a1818280307145d002010002c0c100d4001044030764405003656030442a0030039072820501000c00c01e18030050350f01c40c0017500d03c503003552074455502907403000003015075001905000801a01c3c0c2503035000d800c119502540b440b0081c0341c440b001c101c25604c1d103025481d0440c07020013042042d00d104901c0004a24007a0a000703030300d81c3ca40c0c0401000b103001224251051508030f110402000010720a0540c0500e135105044801500f0035401c1510542407000a016920081041d440049039580b40c80081aa0202114980d106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 643999892 1250 643998642 643998647
    0xd05280201030b01020a0b072304031211070308070602031003080706060f050a030312050c071203271113110c0109050d0302040803030a02160c0605070c14130e01021207 74
    0x411404070700103401c1c960580324079400002c02002c02c07640b0000c0ca00096440c0c04003100e1040e07660711003100320444402000b0260f26050002c202543c059080110b90300c0703420754050100400b0301c08100740c0d503200c3c8000f00080749a5030155100da0750b00c00d17805640c07034449100c69001c2c0780068101400002001540d1000c016030359000108490700c1c4441c40320041d549904005803500075200141c0805c4680750340080e80050355001c84c5d0302c400e80a03105401c0c4252a124021800100d4141e640820f95400c0220046074000603280780d07641c101d10f99410340034000d6031031003c41010180c2d154000c0c985d00305013526613400b607084404084001d03081c441d1201c0044407503030f01031318944400750b4050040300040908140300c1d0003158159642c0748003c5181da140e00c032081000b503110500450b50b130404119440005400754071207500415495554a171034540500b0702500c50550303503000705000840560660f00039181c085008c00b41560000001a2046020010030701901c50300c051001c840b0003c10401c018a40c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 644001142 1250 643999892 643999963
    0x40b1e0a110114061309022e030f060b0a030903020c040f02090a05060a2f070914132001030216030305011509140d080705060a050105040e1501050d05 66
    0x141e464000780080e20440041820140d402c2d220700740c1050704041001e4680c00070b03820103244584040d01401e4038010301c43c41843e0600040d15846a07408400403003961503503050040b960b17410041542000a80d00d001500b0380148600850723032061586501807501810b0082c03240111304907010744148a500703c0008444000c3d0300c40b0114078490000c0e00404955400d0541c01d5030210440c90310b40342171040101110504802010020840201070350910007a074010174080100204030300301000c115516210035142d2801c030010110070b45003031006845400b05003941c45000d11403d40c500228482d6051100407000b234850324400071104030481680504164cc1540110f040307404400103c401b0f2006050212080d1031507106c0c80d03101c00f0264102c641c5510f0042031400c0440d10604d04185087c40316501e1500300f101c1103480d00d102580c4d410040040742028020044e4083c500340c082d001c0300c00740b12506440300302c060040074041c0001d03400368420804100600d41b4100101c84500700707028104c1c02c8003907140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 644002392 1250 644001142 644001167
    0xd0603140d0206010b4603110a0206040305030a060503030c030a090e010b0405040c050712022d0715020111070b1f0509060907021606090306150605040b1e0a 69
    0x41c8910303a4128022480416654140d40100740b41529001c0d0505210085419100903208a0706008000a45481e1007101c5009004070340c0c2d201c001c50300c49900018040300c0303c1c2400c403000c0c1d4104004040c6410f0b40460300d0356101d030b0725081c480d4072610b400031051300614a6401940d014440010f006250301d8001024069201c455501e11482c152120001d9000d041c1c2803150321105002448180074901d40303034109540d00c42c51460054242100c2d81c480710040d0040c01c06120142e04030f0010103004200168004a140503039001021042c261454269502d006074420340038a20012414071000038801c3d0803100c3c0c0611f40154140e01c17071a9900b8013998848050b243c401000e14820006501000c0c60740d40d100413187c008003500c80c0c0d40c2c0c803070040c0000100018050402c41c001c2641c40300032210740400b840041e0549955120050b070861800310111804040341c800c074140b00342401c010556200003202d0039211340c1071a40d0346070380450f410344d0b5a1032b00c0c0d00e07208115101c010841c400150703030050510294 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 644003642 1250 644002392 644002433
    0x10050d24030f140c030d0c02030c0901140a0b1903050603120316080a09020f0409110613030b0a050610050a032901021005040302030306060c0c06030403030e0616020c0d080d0603 78
    0x541d44100e4280f5070320213002450b10380503004034054031121070180f1540905a4000f41c16074a0843c0c100c0005030036020300740c101281440b022070300d030030307031170500105072000360018030001c0e4035007143c1581c1d139107502c0307020b600d140101038450300042c00c1602e0600c1070080444c2d01c0d140094a0f0f060103201c0d1821003c6080035000040d0224001420701c0c0c103a80518002144c014080e80c41c031034403181c14000604000e4200307803000149600c1d20206600c0d0000100a01c0f032030f900d5050300035400c52518900d10b441c09131281d0046c40c10141480f01c0c658680368000008001c0b41000780c0e9541c042c0806402400c0700f031504004520319003030106400c00500003050301c031210980c240d40c14411404443e9080314000d80d00600141c2c0309000090160505000401414580c80c040b00c00ca50b2010300090642e0384122412000a61108101d40c600c560800443d50803048030b50441c54215007080009580320000610a445200307131215013402e01062400700c4480414440043c00282d03201c0c00c22000307150b1002450300300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 644004892 1250 644003642 644003663
    0x8030d0e0d02300729072c030a140c0103060e0c04050103021c020403030309031403040c0603050703060504020408071d070f0302030604091e0b090102090f120f070603050603070510050d24030f 84
    0xfa02e4864505803030582d0b107c0a80c5140070301402c0041902c11a000c5c11103425120349404400403070101c3c4030004c0303800200f400030070340d010122000600740c0b8556030040030b10450280c107100d00742d14210281c078140e42c002c0c40c00588400180c000b480040c03005d03070450700c15140300150210a05034950030181c500c0d8040d4986807412104c1c04004103552104460160140350100001d000701342c400d4100d03540080c414a00895896110700000c0c080360302562045140b03500c451010030882010080c221010540d4080c524050b241110002c0d00f15003400f00300c03400301036000001550030342e0f4503032000310000d8000c1c00b00c0400e1000d59040300614031460400f0780709800301100140707400380d050080307603134100c400703494605414000010f225103500c03403d148054a0003500b0f24949800d0003004810000c0c40e0640e004200790401009040c1400c8250700a0303800341024a00000095400c24215684034600c2080010501030512042c00406480d00004900300702d0300c030b030000034440710b0380c0e181000ca030040e1503148 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 644006142 1250 644004892 644004901
    0x1060302091603110304020303030a0c09050303220f080d1214010b09030c03030c0a03050706060816030c05060f0901050c0a0b0108150112032708030d0e0d02300729 72
    0x1c0d103804101e40c02503141c9c1c0304000042d8824000c0c0c000039940e880a080808000ba1a10006030850f00f00114540500b200591401d030b609000e1301d00040149526440b103c01941070003440c1e9200d40c030740c444403400d00141c00322441301c0c00301643c08021152002039140445507110100007038203a03c584c2c41d0a119120701c8489030b0280c50b01008444580c290a40240710441840d5003d0361550400380054800a0b5604c02c0026051014008980c1548141404850f02c034110315200300911907641190b4043c420901c400940c2441003402c98014030401d0130700f0b80c0c443c442035050350b14280e0100d00c01008056083e00015003000300080341580e6160b5400607a20b5680c94042803401001e07030700000350025144842e036010f01041c540021003403103d050500e200094aa8401c0f602e1640801101500c895a40c034403038007401010320442c41170240c64800303440c01403000036004270f00d400c0d41d50000002e0004007107011b445200941c12500b109038010103680c80300100303000d00c44140340e54502c41500b44000c41d0014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 644007392 1250 644006142 644006171
    0xb0604050118240f0e0708010b03070528030621050705040203060109080d0206010302010906020606100e061620181303030e0f101a010c110301060302091603 69
    0x6058441d02c0d0722020384280341c1c12000010f09042d80c0a40d901c1c0004483c03080100308240d144038090840041032003107240c60044100e0801e10014564010445000014001b6050b00310440390005080d03e801e0340c442030f445008550740c1c48020305804c070000604a8440c150b982640203d07003140c9018001c0d1001074261000c5240c21100300a0003001900124000c0c8218900b0364080c0d5000501071429000b6103890702c2e0704919058881c2010805a40300f540100110360f0310000c03100103400a4809040c0701c6c1801400304650f950310001c1d0700184100040e410709640c0380d240682e2101c04640b00b04e084446031900b0002e514041f044800e201426190015030642c4c20820002c030070078010050421825503500c074030405d00300b9003d1030032001c044c5c80c0e600e05103040f0320810041280700c007803c02408243d00e9040240088804854070751100c4040c0c0c42c021600d50380c01814110105811001503145040301000217070050986400007075000a445040c82881040d8031424804888551420049419002c00300c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 644008642 1250 644007392 644007401
    0x20c01030f1a13060807060c0b0a18030e2206091404080d09110406090c02010f0b03120309030c0a0f060501140904120c05060c07030905150406110a05010f06030b0604 73
    0x101484114402c0c0180103802d0140c002c000c00858810000345850701ca81030941490b200d03500040005020240c10024800742d42c281c1c0b50425001c138803c01444c52402a000c6159118882c0541844030142c40d00209488220240f041d4005001d081800310030b1024035030300140362902409200c039107454403d0103280c030709101c210b0056030440706890419010500e6800942040d18040b20281d0031f4081080c4582c649001d100c000d0122142c0125414001c0345000b03003160001c4004410040c2001c01550b150340b40464880203141e00c903900d90307540b5500c002400d8990700c545550010f0070b10072070201a007400050200d14a4007842541c0502540e40e80e044110000d440f103078682984980d011001c5400207844480c0000050064100100c0342403a6446e11418540c086035410100c1e88d000494804050b4002c201e040a0301c0c080340c01010b190b0a855809000e07000d540261000d2002020070700754148001c0010307001c0182e001000344a1000c50031903d00c09048aca210480e40494000042500e5250a000303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 644009892 1250 644008642 644008661
    0xf0708010e12030c0f07050a06020304030509010e180c091c0b04171206040c1e0e0f011416051908041403030307121e060b0304030f1e0c0212030a020c01030f 69
    0x13051400d248400982d000682c1c8440d41c1160703188a40790306100018264009103200e079002e511225155101140051302c2195000038107442a00c0808030701d41d900c51a031145680041d1070301c8846840380d200d00b0100d440c07540040250005400c40d81c549104005807400c0451146100713180d01c04030074525018803e00c0d40900420780e04815480000103000b0b042903441036802241078039010064440c2001c11100300460101030200041c6801420f0350315040c4002809800740c1300b03180c60910174094112a94150103140b5150320014610806101481420040c0040c2121504150a10703419a0710b4201011f601504c283c1e44040f01411424400b803038003101b030724812112030b04c0c1c03c0361056150700d04100500031313600960228038841d01d410242244510078040600107444c2215540c2c01c1908001e041001140c0360350040103d859040091020003182d00d154220391400c21880480191001680503244041d03840081d10022542040c40341c2d00051000c2e1004c030a807010000c402c03258141406541c0c0150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 644011142 1250 644009892 644009911
    0x304031a10061431170c0d0203150705090102060a05010e1801180f05010f060f03111309060b0a0501020613080d090f210e1c050f0708010e1203 63
    0x24070401c20180240061070b04005030001c4a4070740218202c9114030510142100010001c800f015090001c0203120030301e02408070b6070140500c210708980b40d40c0e56041e0700c00440340a44031003110781003191400c008a2444031420488a0040d20b41018001e0203600180c222600610503e00469490201882018141c660780c609115403642c40300b00b03c036501c01d1514011003031507588130b03820700c030303600d403a942071049613104e260b480e840d003045403e005080d54620035205801525003c41044116006d04600b01113035804155584210b0003800080c0c401081c03d102519141d0030f1645c1c0700100030095000c40c0ca01c0780226005006d90382c541c0300480e548ca038216001c485000c00f414036600415800c0700a40007201045202264003149039989250003180800c08a410002102d010f580006c28003a240d180d00210785481c88000651000040241f0b0240021080154103040c4c0c0005010301440070300e0700011100b080b501c01aa40b24421030080c114101608254040d00e001c4001802c114004c5074003030f0380c111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 644012392 1250 644011142 644011171
    0x10262a09040c0e181606090b0414010c0c1e150e0102191e030f02120f0a0c0614010b0a0f05030402030a060e21280827010501080304031a 60
    0x81d0001604200290030132a200401d0046030422000811184204184982119103841d02d000d0010703054004030303040701e00e038003a081c4401c4c0001019401c80c2005071201b4a81403170041d002c3d090800c1d84107400d405c036640380d0b4a8086495403424400b020301c801c030740c00002e46c0744c40d11344000b40444032083c042621b01d006070000100118105080a403480e101e5021795000301a024403e90600e080d40002a012004502c41c0e071982c4001e0b81d01806040041041d90b4031051901100f480b10701085c1c483c0481d0b400034008980a10418070500e9800401130500d86444e1644ca075031a100c01000540001c0000c8000501404007a00000d03c10300a580c01140c0c06001025602a160f480030003405100700c4081e02c2d4842c5145800890b0825401810320340501c0182a94070030f0400c400c041101141903210b040000d80b4000090b00c039500c00c0c2000d900000b07044444100b12500c4420b0708409103004004400d5600b07003000410284070100042040b2442180c5001c01031540901038581010202d800c80501c00c4071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 644013642 1250 644012392 644012399
    0xa0501110c031f050f0106091203090b160210020c010c150227041a03100507020118030504150c020303030c0708091e12030310262a09040c 61
    0x34050300d0304406844064842402000000c0307403074803010a40480b60100d50900780c2204814134403c1d01c1d080214144941801c1d814400702070034000c07480c0f28540301b0010640b41402070511171034016026002143c0c1c1150f803415031000003000056900c00030b911444640f42c0882c481c40c00000c51105010040e100c003240d0722101c0e00d034182c1d20b441c51000b100c4500d8007080405043ca420089943c48121204030640f42011440140030440710b007507007569640b5102500d0b8420130756000844041c11024800701066a40d180f007000c07805442100720103190302c02d02101c0d4000309a001400303070003503030586c010340280705424240c226100c000c002ca02075010381040020442c0007c00c0c0d8000c0144c00cac06113800c00c0c034107400b0030041390320010342d4401d0110580c8402d2038038106240c01c108240031044044002c42c210f090480440c0e855001a00c10210704403040302e2140c59002d8204540504c1c00d0000301662500d2503c5400d070040c0c14110703103d440c4018042005d11581c5c1c94100c1419010350380003191600e80380c2c02c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 644014892 1250 644013642 644013647
    0xf03031513090b010b0d0e120930010207050c060f0403030c030912080306040c08060627040501170d020f060f190c0207140d020d0f2306040215090a0501 67
    0x19080d001c0300c6449101d0040071640725030502c0d0003443c1c0d003c1402c0d590b1a105d024681290340350b0441181c0c0c0d030032030701101c0f9040300d140040c4d07034000e40229045103255403048801d84940f076030900104140012600407201598040d4041c0c100d943c0954140c03003011100303204000003485421b100382c246140034802800030074403a801c80d096240c4a4200000c0c5070780c5903071541d4400b41d0380c0041260524000010041581800e01036204600401c0c20f202131981006000520540143c586005844007400400743c003401800e04084c0d4154005041007209503105c48003000c90700e0400d4a00c0546100d913500004249100080a00c0358a07220006170815494400c5190480400942a002d0920111148441d40d006c81e00c982d500e02a443d40040021602d44030b2070b80c02512050815600c180d860b5010040540c0310b044841d140c10344c4c0460345045489481c5091000e02d0200c181c1a4000040c0c9062a00b00440008186000300e001701c0b814050194032505a1689108a01000d500b2440b8039104010550 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 644016142 1250 644014892 644014909
    0x150d0629070516091a01031e0509010f0e010b0a0602060c0708090604150306080714090408030406021207211b0e062101030b0f07091e0e0403050c0f030315 68
    0x10711070415290700c90318000076403444040c0c1d034000c824019915001450b80140040385d10280c40c00a003800c0c040034201084001c4c080012114040300903444100103200e000082d0f0020b4403142d200f0074200040e000d540034090003048004e050601401c0500d0021500600004142c0c5c45001c000318880d181c151996211101d0f90401d028241d0420000d20000c100c48802d20350002010303041d035800189286c03419013000c0c60103001b41d00644504803000c4050003680c4407000300750380c040e0300001c04035542d407079a281c2880244101c2c605489611221428054001d503c0354562040b45001d01c045035940303107420b28003000c41e076103032600a800050820074020054010311104095000c02400f5a0806861700755160400d0494003002c551020b41c54018020411094402500000c54150a0318540b0344a4030107065040e01d80208550300c42400b00402405513003241850151015001094207414945805451034201c0c000641d80750042e101408804e040000c1500c1c8102c4084140420341000c64003400940e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 644017392 1250 644016142 644016157
    0xa0e221a040b13090c030b010b12010f06090b030c09061902151003110a0315021c0e0604170c1203090c090919060e030301060c0507060201051509060d02150d0629 71
    0x802c60b1171000011500c0c1d0080705008001c1c909000b0798819840b02e484030480c034140c200000c075a02c0f002c4140403041d400010a001e45060b002c10a40d03a880e14203000c1c0c5a40144c18400303a1103400006c0071042000480454145e081743c07602261540340c2a400070f0007180008030348011201c034130b0040400125601c8200300c24a0000a4941603a8640303e07201c1c50b40000024414520142d00000c80c40480740e03031a0f0115080c1d0804141c2006004c6121024548581c00680090074001568a1805820300d901d000c07203614810850031a5006441c405080c00a07400403200c00d200c0340110350141c00d1600f0840011807040c1491006483e007a0442e03c01e10b40c8007000c4440942d41507980d207010024182d4200000e40c040d1800b038851701e4a1001901d80245000b07040e4120404690411080c00640c41c600c40310090250011074613088241d80b95804030340c0d00308000704065842071f840817440304400000001440c2c2540e16400a00445d602c44001c1403400c1e03110800b403121306103003040c5800721600400150424 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 644018642 1250 644017392 644017403
    0x80c130519090302032203350d0504020a091a04020a021e1e0a05030a0509131407271e15210b03030a0e221a040b1309 52
    0x1c0d40030091041c002c0315032442040f005a80002458903005094a52100c4d42c0d07a001507070074042505664603410b00b0958640704040d0b00700011024a01c00c12a026101e68030200e000c0310b5a110385481221801912081d01c050b40600014040440e14080c28021000c4072401c10144011403000310b818807000350700424505045006a80d06c81c1001603095140c0944400040010244d1400748400007803c16401e4030200d003c0c0e0302c104802d100182d80030007903505440c594140503031039855500101e52440b40d802c8003e104d20f49401054000da090f4200fa1502400341917403021341030702c0c06070811682170084090307084151240c994104800780e241040d8003c5400b40e490341440c801c1c0d540407070b100c00d06c101d00d101c2400f10b0030010f40c1071020094000808072041890314240b000e83d1070b24002c20340b40d10980140070208030f80c400300d03001c103600e0b21805420a514070011031450700d0b42c1d108040000f41454140260b0403002060801400d191a00460f040d0f0341c0d0080a100c04075010700c03230800041003200c0c8200c52 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 644019892 1250 644018642 644018671
    0x6090b09061c0f09050a110607031e0509041410060201110702090402040e1e010f1811040e3c0607080405010b0d0605040209061e040207060605060301090e07080c1305 73
    0x101c0e400140209a00700b403103507001b020244000d04d002003412082424460144400344410b00200c0e0703000c0c8500d01102002010b1001208804404235480d2280121442e003140c1000d105412814460000500c00c071850014810030a4407554102d007170382d00021a0a0124000340403400c013520b40115201e400c14401400020021000004d160902c8040c01445699181a60381003245203828001c80c2c2500203000c80412034031800c140c82d0030803000b82500180140d04001d41c1c4a00035202ca604c21a42c213038011003200c0d07400729041c800b0240084012050f00c5400d150a031510010f04026222a10598910024101c01d03030b60384404403104c140040041d01c50303640f5507881c0700564840c0c0e00c0074500c070342c001c00c0c1c04902c80c40c06005000b9032000140855003c3c1d40003411f101c1d42c1ca0343c030b1111884070400496000d44e80e10490308191002d050640c0003241d001d0300c0040001a03800d4941e10948907100c6040c140e8420743c1e4ec1d0011292035094010907181c200740d162114a01d001c8507644800e13800911481602c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 644021142 1250 644019892 644019911
    0xe0f03030a021b1204081b030a0609020612040605060f04060f090507050d02040305070e1608041b081f06061404050402070825050f010204030503120a0e0f030406090b09061c 76
    0x3d15000b10130f1410061800c0c0010b00f0302080e881032090320468a525450f8040319480300d00440d035a60300d8004044d101c50340d1994200115501c3c041201d160f1519031303000440504160418500500c0d05030340c1c40b8440e68008a403207502c3d040c1401a036040300e1901c1c030030710440c61074149000c000e01001007410007004020406420075035010720141c000355001c0c000a11006003080704c419001c01e8050010054616149129081541e02ca01002e51055210070000b400c0c0e03070b17215040f403505110360b00300c050711380540d220079422004032100da900069180082842030030740e03410041c0c85c0b40500c070885001248041005101c9070620360018841d49200342012071400c0210003c03141404895101d40c078507880a0050082480400c0000000a01d5500000c40c40d140c69640c640d503591003a420400b0400000a000a41d501c296a00c000c171080e10b44410b85100c40f030414034240e03c1e0350190280d440451702154001c13a0b5540e084003903403840c07138010301014a0701c0c0302c0c1108146013206d9040001080c0392245851b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 644022392 1250 644021142 644021197
    0x140703020307060503060a0909050a170405040212061f0828020d05090c0603070504051302040302040c02061905010e040201181a0d0b06120c07062d0e0f03030a02 71
    0x200000e24113552101d0f240e061880c10094490800d5001c800654204900ba0000c2040408c020309542d40c42615034a15071302060580d13446000300e51000b64498030204e00e14203106804095984640021a495801c1302c07035020810a4513240403900e0700005403400000341030701e10f0780c0d51a11445540c00280a040304007100c840c00981e4009901c00301800d4a650a011010f070782044038840002007180c8150451801081c02811405640708480c442c03480c6110040c41d0441550403100075580142c4107011114050601135a03410b0180c6440310800e01d0041003005851003441054107031380c152001d00c01542c0700c0e0b400440f100304400741c0d4401d0701c0480030000035002c0e03405071005200106060010391156041458941180c04580f11940070348401c1140552600b080395809a0111855021a4480b44141020801003180c481c1e0219000c0344e1400c0d040300145640401c040302c00302042c0c2800101e1603d02c045459015150441d00c1755072003030000c1040340304150041c2c080f05020b003a40000341410800311 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 644023642 1250 644022392 644022403
    0x203070c0627060e0d020f0306040f03170702030a0c111801183b030a090f170d030b010c02030709020d0e060106120506220e06221407030203 62
    0x84030125106003400403050548440e00e04041502c500c00c046468900701c0d002e4420004900e00318400c1426001103400c640d600707030900d121464060101c90702c3c0d00e480e1078030b1180142c0101c010342c08070f045105070700c1810076090042c5219002603805141000300f450015a01c000220344109ca003c90007031140c0c461a12000c401510480c0a44190901549819403241043c101c0c9450380d000c02e030900c1e1441003800b01c0381150840345a082500c43e8000390006000d4207468168085401503808001146180f5582c001000c0c8165009034034003110965481c205662042018100034507207811241040346440e000340d000400017401070425504010140e40081d08042258014002c082d5000c64014041c5189125060300a1382d400000c0c01603504081000e071a4003001c1c540101e02c0354a4030000b9013251281d810b501e41202c002c905003a00c003106201048003074528204100c034584122000a02407060b140d20b034000c07503070801ea8581503207065901c4030a62940c140100034042d01c152840080141c908004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 644024892 1250 644023642 644023649
    0x70618050607200409020901140a0f0801051e010305100f020d14090d0c020603040803070302040905180d080615030a0603021f140702150a110f100f14070c030203070c 73
    0x5220600c0010403007070322034100c1203103c89004610780000c4000684800071190305403a08001c082ca0101d50100018940c507516400245072008244400290348105400450250b041c10f0030746100203071801e0f441d2045080901c800340155205407000d11a100f11070f031040c00200510310001d460207401c00000c00030b440e02503101890016004081251448080c82402c051071380038541604400c9003600000d0060001810141c14030714000041003966000c1c0d0304136401854400c20070321042c944203180d00307600380d00b6134490b0006003d0150300c0f450762881010881d100d400004c04400d043c4240440c04400e6402c01080c0c501560f030f540e4004000740c0e031280408070801500c4650062804001e02d0000c004691421035100130380000e00c00c00c1c00683e18001c0700c1c2019a0b90301103058881c0e003a071004031442e0680c0000300710903025018841c0c052100110f000781d696480300c0030901410b00b030742d4040c1c2d0494401034915401400c0f850301040d00c440c400e903500e60f801d40c000c0c41203d0500f020350300c4542d0040619407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 644026142 1250 644024892 644024903
    0x71d010903022d1203040501051305100807030e0c010203040b0703090e04080417030301120230030309120913050601180f060905010807080103060b03100e0c0f03030408070618050607 80
    0x10340021200350050356458140001d4503015828200c03040031561741c1c012070080c541800390200301c1700e21118020030000c00501e0000d21294681801000181c036a06090b00c1d1039000038141b4101d5810444001480240d014040e0f00030b5241602e01905003a0707507000300d00220200140d40400103500281e03052403600441c051004181d03142d241130109900f850005c200001513800a2004024540e03044140355041d80d01038501841880421002e003070300403210210070305609241103103240141000805984540c1502e41140c20048449a0040440c011303000165481440c9603e0620400381c1900072a0b0000d0042c101030b08070440c046840010034919030020325415403807540411005501c03c00c407000905003802c0025150410b60350090801f0710502020f81b00d652107a85440302c54030304201d91031982d458070700c080081c200400c100c0c2d5100d45914184601c11204040c01140d00c0c5000300c11102203a412800600300986048001e5680b14070340d10138240c0c3d880002030000b415880710301c000c040061045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 644027392 1250 644026142 644026189
    0x604060314011a0109030b0f0a02090d0f02010806010c08031305120705100f090206090f03120a0203040f0e07120506011b08090316141212280503071d01090302 70
    0x186410f890341c1c02d5049024100104100c0410100769640d5030a81c0160781e0316109140c6640b02a011806441076424042d004050f2a2042080c0312040c0c1e20428007620036603c08295466400044640d1649650f003d0070481081000c550003080c620685640030f442032058801d04203240c48141c2d51904012000e580e150881445550440304a110700c403910304070f0f26010452040c3c0c42c1c01245903402808400c50090800b684940140d9408000074141e2020070b9885982c2c8420039403000b900c0380c103d8420001c2101981d0004221451000c9034244502c1c02c3e41d84414815190188402c06000080e16440c1409070b40140d1803581007440c9184401725000743c2a6954030b4800605151801c2d43c000120004140104410f001910740b85800001d142400c6a401040b030f410301451606060740f10840c200900c0001030841c0b2200703501c004111b20010a4011180200e010f0002503856120440341800000c11900740041e0000d100302244008010600d40000081e8403580413511950302c019680e00c903000750 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 644028642 1250 644027392 644027411
    0x7020f1801090f1107080c0106050901060c061811091e010e1905040314071106041706011e050d0336080307020a050f010c0c141323060406031401 64
    0x650159408207104103c0030031a25068030701404c02d60040c40e00082480f1030000b4030342180d0409400a00c0904030040c003009595070340d01c0300644035041c0030904840b0203007800a0185000000c060f0a042c03141c000c482c80c100303800408100051001e00824000054154024405e507141e90196658040c01041c2400b0900b400c01c1400c205912800c00480301405013408104000a540701c02c10f81c0d1074914040300c16480b49950300d0154078112900ca10190042d50109e40080c550714510354030300d0f4680c0d007070089d2011030744c80d41c450034072195241500700780c4e04000700420012800d0103815055014028030303264154401440c20290705096140c0700160700d80841584c1080507000c3d10440340200b00c0040210715111a5a000c503840c404940314030391048406c0300030340c02283d00407202040855070140900801c1515000211b807100c4100c4030050007002c4445102071001a41d210744209441c00e003400000800f8408202e0001e0500240b519405c26280c20000001841003805400800c49030000890551013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 644029892 1250 644028642 644028659
    0xa0e0d0e101416030f091e0303030c02070b0c0d0e1005031f05061611240f0c24060f030613020102240613061503090204150e0406110a050d0207020f1801 67
    0x701c0c0d000455111644800c2007107e0b03200c8034505089a03072508011a01c03002082041e4204082c50f4440c00321410006007c281410020036070002c0f0440b540c48031202040c07038806111051a422451801068007000401c0c0c07594030781050204581b18031001c9072002a29540400c2043d003022250608070162458102c0c104002c080e48007855007402c2c1d4280041040c1031140c0c200005510f84a100004800a8520070750034450044410030784515003101d5580c0b40d0700c04489070420410700b40c07401a0b034001c1c002c24034900e4000000440200001c8c010451625224002c915501800c4800c0b815441012440c124142c2d0242d01501800303c101910a245d18296003440100341508040390f8020b480d02e881070021035201d0030311500010325407034000b50304400c1c2d10128004101d242d02c0704500e89031810001481c00c110200d61440f80e442454140700251060b200e480b42c5014441d24000840d03028000e03070014940c568050220795000501c984d15042c9850701180342e03980ca5140c92081b130620800140100344c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 644031142 1250 644029892 644029907
    0x21060f0912111002070c050315040606120c09050709030b090f0f0f03160f0605040828140706110c01060e07020a020a1404140a0e0d0e101416030f 64
    0xa205007014803480d00a00780c0b4a49030f0354109602d41c0b80030b41c0400d100c01400201c60880d006000e019045a22140314000b001402400485040342d80341e081000100b44c403640081100161a03000305550600e07420016000007801e0000e210a040099601001020036044400c035400f81d4031840241c407403021041a10f608102c5109800112a4011044101c24440000441c4c4240304210224648506070707242c04546054100c0c40a8040c50411085c0018405400020300d4000e42459044480c4503000d1403000c6071038501030701100441d8424030000300150070b150042100a00c111400183c082415101ca091034011054120580c1e42d00c0b0300070b02c21304070700309000d40c0c0000c001d000500c010b8900e43e0001b82c5440c51800f400031611381c2e20390880d510341c0b5550070070400b0668108042c0590314203c50b203603008252031200c001442c400c040c040e2170141d024134456141004080c24420031405695000d4410310245a4450154102003001003405000703030141c086442d100b560380c2d00041403840310080c00321 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 644032392 1250 644031142 644031173
    0xf02090103140c040504050c0403050d0905010f080403020d03051b1204020f0a2304091a040209070c0b010524030c04030209010b09010c0b22030905030d0509030721060f09 75
    0x4010034240303c0d12105000c25941124000c0b01c0c08500c5d9a640420340c041402240c0c0001d24511500c007080d090941c003d06440e0a454080e680d080d90091544400c0740d031148140c4000c0c0150300401d6080c0001440f07a0011035010303030b00840342c0c2c1c1c0c81c160482070b4851a07400440c00184014100342800b04602d0a01c620075620304041350300011203810001c80c0c0020344001040308001c0031580304c55001076240c40e08114403264200304a8080892000f5180f01d008000700e031b00301d104080c408006000503006500b030b46950380d00301c6400342c0c01d0382c01c1005120080300405035503a505003500078045442c4050704020f5104100c62400039440351b196205209007941c040c1c1191413083c00038002d1400b281d90000b001c040660300300199a500d600c4032500c01d101b448108c40c24185003001e4a112406064002c1c241c0d00c2141e80580c1102c41045081d54115000d00484030f519501d03030040700c0e0410080083d00f40803210007200c400f610214440660380c1d041116040901d9941e043d071520000d0003440b0412510382041d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 644033642 1250 644032392 644032421
    0x50c0c09010f150c061107060b011b1e05071e06020307020f06160c0f1a090319080c0114150a05010f03320415060e0a090311010f02090103 61
    0x49504104031064040c5950107441d03004a06650f810f4102c520400d00822040e420032410411000f02c40b52414055003c443c05541580c109245200694400c00700c0a0042106410720094880c2d580c0c1c0d460207651700c0915003421000c0c1100d98201040c0144214002002e0b88600c01c0e0000403019100980c0d80c2990340900c09541040c4400c0002d0f0322101040e50103401c00b100c00d03a035280e101c4840c001d501c800e008009410a02004408a904440c01c1c20080c10b50700d1031149146e018451190a8840784903810800340c05800c641c540040e10030204408141c2180f0881c42941454514510682140d1050000301e08019581042c00324a0141815004100e039040e9007078031020341800e001030246150706165504140c0d4592040995a40c08132040f4907a402140700e400301003034807400c0500d0040741500d0030745110001041c3c1e6204c003d00c41c81400c1c02c41d13102941044040e91105026001401d56030700550501501b0541103072580c03070078480c900c100c0c042c110006894001500005088884100c0b28214 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 644034892 1250 644033642 644033659
    0x12070e010f08010f0e06041e020306213a020a020f0402070506010e090c04050c0409050105031c080c0405030109050d1e0203030406020c071e080606010e010813031b03050c0c 76
    0xa81e00c83e41d100002562020178041542c0c0c0c0b1100003090041c03241072050129440381154031816038407240c00031030050a04446160040c03c071060414040da10400b1900b04070740c00118440501e40d0000018003e1660300007102d02010810a06404060300d4031401d10016040043c3c5d0208618051070424210401510110f0400f0500c0ea2603960340c1d4018010000c0110244000410018040148003407444010b0001c0c0241c1c1031155420181d0341042c0620074210b07040c40c0021495080c0020051107806502e0750308103840800203c281c5400c10090614008000204004542d43d04c0134052004000d124100401c910310711008024179030040020600c111440c92144403c4d201c1d8000309070b0390000e400c528016a20301c521400d01d03140c04403562011b10845d0514028a2010342c0b0f111a4004a80100d02034035030b6a039401004440340c0c400040e40501044213400400c80d4065101401f1007668070904010b1441540300390410820380c510b28044000a00015401c0150202402403000c441800d903a030a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 644036142 1250 644034892 644034899
    0x804080604032a140f0102070605010801050105010215010608060a03061806050604060f051306090e0303090c04020a050d05060315010b0a021506010203090d080d05070c020405060f06091512070e010f0801 89
    0x1020000101006030148441c819048284d10742881221501c050b13100c000c650300c140314500300700501000d105400c001d5203410000a4a0750010800300c54511002c4410110f9a0074100141c07100c0c48041d00381c540000c1c0701140032001031041e2090150f624500c0401c1410002d1030b25140081d1100104014000d5090000c00c006c4103420f101c0110a9540403a100c00b072082c01600840000d246a500c043d00c103d0422040240c00d0702c01200540c06080c0b92020780d07041516080c00c2c48264401d4001040014108101c454020206548201e0700724130014280d0f03201c916100d5107111600001c2e00f00840d0b5100025001200c55010043d2203204444404801c46915050002035140e0203151301042c040c065101d0050300300011201101e40c24402d940c0104400d05068100070618010030f80c00700c0c001ca03d0000401c0680c40e0402c00480e00030f20007080039140514074814491403500303a0440c5020340e5424401d0203030700d02812030b02c540b10312040c2d900d904005c4640d5000420b40d082022140c01070001e590b0052 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 644037392 1250 644036142 644036207
    0x30209180f010510030308010b0414040b060702030a0303020901030f06180903172503020c0703080c0709111305100e190806190606021b090c07080408060403 69
    0xd9000c12031082890380410340d4400281810120303911080303154640303010880c0d98410003003000f0569029a50350241c6a03240c030300350802403285000d101c8a6401c441d21482d40703840c040e0000801c03550701901c80340c201181c03071b0b01103481c01506e90800c4011035004034a0011a50b81880788011541c0c40c20000e03c0103515041c00440348028548183c85029104c1001900341405400d16400c8805040c011401501e4a0180000360942d14401140400040898850a580300780250381d030704403606014240091441d40c0f40c0d07031180d00c40f1003603250078014002c00150170041441a4015040c1d8010060358544010284444140c196004603120301d400410fa00b120a520074516038004100740c1c0c010244030351703040c4110780d80481f070380c031022192241c80c041210715001c00328618200c058a100c14020b00d61101416600e8820840310342e040c0041c00b141680d0310b03140841c2141d4202c0d10700c40241e481c112843d214132509610941041f98039034496401c4c0010554424014112070010f1002e4640223034510500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 644038642 1250 644037392 644037409
    0x909060105190e240d05010501090c080f060f01090b0a020f01110403030c081e030a0c2d0c110303040b120105030307170702010e0910030309050a0b042303030a0915090302 75
    0x490350044074841c207a60344c4403080c01c0c41c0139003490010002c0105034480d15000707001e003c00740500f8034210708101c406406035000d800d103180648210302c0180d0007680d410081c44008084030060504020000100081c815190001001500c1407276014140038446140d0f00d80c256821101ca80302a10420402000031a42c0f00114101560344200015030f1b40d40d030781e81151003e240c80040120031101c00024070200714400e84c001141742840b61900401e0b89006001812260040072030a880142051001d640315442450340c844010310034503c84000b29140c80100b4038541150700b150105400010b180f603030301505080310500514084004628004c5a40c0c4c9040049000e80342983c00342c80302256440440e8024241440c20000160038013481e407810302ca03c0b201c20f0010340300503008100503032804540c0b403c0020350070007034035030004a06150915000d00d004844030079036000d84104d00000c1d25640c139030741c0038001000d0129a070741e2015281418035241c02440c03002d4649442c00d014544a0820040c1c4401c1c21 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 644039892 1250 644038642 644038651
    0x4092a1b060906050f0f061014090123030702160803040b2b06090f02162a0608070f020318040c0309150905060f040b0103020d08090909060105190e 65
    0xa03032114149251600304040c18070b02000805141c00d00c0c04200d542c04209480703600c070340e40d00e440d070709100c0d22804c0501403001c5660011900092281e00390300d4203150070f50010300450304189403040c0e111140050f00403042ea001c3e03294518000002080c030181580c10020001802034400600110741e03e04815190b491007684240c085855000c40d02e80901008034030038144426102d003482c2d0303001041d602003400400b114014881010b10f80500c0c0030900301c1c0c0b4800d417406100300000c040056100d940715844070484814070203910038448000c01401442a0140400030125a1070384041801c07d000302816100d0000f4440003103610038071556104041c07244501c0d00e0203c1c00d031400600aa004142103014010314540a00038542150306281072a4069000c441003900400a86904c1c1c0c8580801c40b040001c10398000e05015000d10040c0050300d031450f4540314040c8642142403034512207001080701408100c03900e24468103e030004010a04210401015020401e2602a1403900305035079041d80d6500a403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 644041142 1250 644039892 644039927
    0x6150d06090f0b0c0313020d06020c0d03060918020a050f030f0d0f1b0f12020c03160509060406230612091c0f090e0c13030c0f12020f040b1504092a 65
    0x190103000c0c44275541c101d0300016816010ba42042d105114060701504292084807502494002d11450070000e034209506081d034000c200e00e03001c903e864104210500c045815079454051a0010b0a010341d04002400401c680341d00c0d42d00e100c12400001802c20a521510201880384018a0078001034050000d03405031507001c04003003082855081300b00e00c0d0540303148407580c0601c119140890300036903850510040320003c0781d0117141e907030700c000c103110540303403503129007212a414013103034a015804070b50352020384403c00707400d460803c030000710903841c1204180c8805400d40c1041030300e00004644642c4450207480e190811000541010100034616001d5208a010703604424010410810450045413180e40c1c10b540b0710061036441c1d040c00d2030303550210b21804901c0360b44140c0006503090300001d4444540c7d00201034110b216a80000d010140079035400c42684640d140d4104c0d1914096240640041c0c0b00b031440c001243d03401060148000000c51101d0320014141c407243e01510781e4000d107182112000308 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 644042392 1250 644041142 644041159
    0x414010302190f080c041512080c0a02090a0e06180d0c0c080304061106010614160201051e0306241603021221010909030206150d06090f0b0c031302 65
    0x75941c502d95a11140c02501c90003031502400600c0c600001101c00c50442c048038200b04410003005484d81014403445a03600045500c0c4070200810b0741d11001d0682800e01005481d8601626030002d00344d940100d07080c4142d0303607407189000809142000420b41c0200c030f0023184c1000e420921145980c46c10384480c080c081003124454a0104480702141000810182c2c045a0701c0f107841c0c1c07101400441003540c614400c2d1050301e00019106101d0040d190f0301c00010303800945800181c40520503c000001401e0f03040c85402c00c10403e000325034103035024000300d44000c0a40c4034204881040550701c481c0c4040361140440820b548021031f2424200d07400820740d040a4800c01c1c00d40d103810703420b2041e120500700ca443e4010a5282c0ca13542c0500032246040d40e180c4a4500503a22000205d0403107088190280c010791054001840c43c24510b401840a10001407809000e2840b40d507410050b54030310681204d080880d0040102040300268000d50020149003445085241c142c1a1a61006420714064402d8264 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 644043642 1250 644042392 644042419
    0x150e0709090f0b060301260a1509110306281401090b15070f020406050607080d05250207090507080412080606072a050a14120304120506040c050414010302 68
    0x669000d1040c3d03c40160006440b580e56030710380850608152440b450400c890710611038040b80104580f6a540c0c6d0080589141c04850b0510300c4c01040701c80000c40d101e05031081c444c2c0842d0740400046101d0038184854600300c0507001001d41104e100b200084070031604040d1040a210442d01c0c540d41907440110b000035418402100080088406414100f0200b0b400501c48042c002d0100070f44a035240242d6051007110360342c00c14086a8403540a018040707074400d00603e90700440b10740209070400164442d8600060310807c0382440c5944c4c224004015034131280042054441600031700e41e20604038245550249001e0312002c40300d0309141c040e8020001c44800158003030b0303102019a030780e00f50000160010040101c0d881698107480b6120025120a41040040d461500450740d00c103664940d80340f05a00c04ca40340034000c00c511400c6925040380014040400d5a2007040c071a80c4d006400b41d0010318050916003004d1045540b2600800d002c0e5080600c0c80e56030600e55503245046a074117071a9000030244 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 644044892 1250 644043642 644043671
    0x1b031306090f0b0f0f0106020c0904030f090e070314010b0c0c0d0309210201030509010e0d1d09042117070e06070c0906051002030c060105060328150e070909 69
    0x1d00c1c2d42c0050580e081401801034400c06468164401d008000400607566200e13102a40e850820744403450340300321070000240010b442681024401c0b0b503d070400248076a00d0303510004803a582224540006039a40c0c0c55880309513102c4541c2401400c0c00451240b81c05581d222494136074001d406014003403103400404c0c1080501c1064824001c00004150100e40d210380c0484880d50205034406074002814500070482802040c0f18031510000400c000300008003c051060314008100c5400c255954254600c1d07400a845801c00d0500c03c510802006d00a403244500c480e41210204040d502040007000c081007440740181c0c02141c008900c6c1c10035005414005000890902c10000010310034202c81c00002060f15403a0081c105445040300d080c3d240458400080380d03603000b600910510b0350300000041109040400c01542c10441d40700301060345840070741e000160541d40c494900710f42c070380c0c8035041031050620000340d002800203521058401e08003200c0041103000310b401201091071f034801110781d0060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 644046142 1250 644044892 644044913
    0x13051909150b0301060224061815030a0b100f03050d05031302061c0c050f03010e13020d1a06010507051b01050c011401090608030c06010909050a0c030b1b03130609 72
    0x41c406032450ba2982c40c5c010094036214800400c40e401d0101e00f020700303001298481c08610540e400b820006480d0905019640c020002403c2c0206142000c80c4c940825103040c01803d0744140100783c0d01d60035007010100c1c808104403650100d400c03060768040a00c00140041070300c03102001c00d8079004da2203484600c1d03980d422244a010080d400080002d40c11264042c5081c41e203a001612282044140301008090b203941c41103080c9200c1c42c60742080140460008000442d03040640c403140d10f440c1d11901d60200e41d00c0b149201c010341c0d400400300309036201b2150050402da4846820b1808a040042e81e43d590390740c444d200071191402c20000c1000b10120b920413000d4400c0c200d082c0c8000d1040002901d00032592040a02501c0003d6090050100301a0000030442d0042002e00c0c000f030441c0ea2038002084010000042c0440b00c0d8000c2000203404188420048c0d0f003d9401500c4020326814035042c1d8009096a0300c07843d00d1951020b20810070b2049601c00c0d01c0b035105130010800306004a45151101110307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 644047392 1250 644046142 644046149
    0x60e070b040312170601091710060e0f0c090f012610050f0406030809060a05040503070e01050103050a06081e03070b0106030903021524041d031305190915 68
    0x15580494000144441000c43e040c0401440e00ca600509403003491019590030100c0c0c00074003099100400b00b02d024044145401c0100c480d00c20b4503180000c8041c4030b4152400c6601070304030000301c00248201d246180c0012038118241d01c2e03505181000540c0803600803540780c0140c1e418041075195158294442c5420a070060789200f40c0c401e150f161101908010424070701646000340b0612040c40d50a050074410300003900d800014007810003a546041014a03880303005210304005083c000020a03880c02c02012014200310020304100d90304007400141240c0005100c0114141804001c01144030007140403540c628905200c1800c03910007510701c070710718890302c00000c1c0400c40d041c1c00007034142e0345903000c8156240311b0b42c296041040c50595801080009960310340320350040d00300d224900340c1441450781160700058004a01000a41429144d0b17004c6110b00702e40a400000b41d80201009920b90b01026040c1160040419040c0300316040410030a8040e100305a43e5030141039040d6034101c060310380203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 644048642 1250 644047392 644047409
    0x50618070e0414011418151302040f061b020919090b090114130b13170c060a050a0e1009060b0a06020f1501060f0c0318170601050102010507050304060e07 68
    0x20300108641d00f042c401c50901ca41059035400c107625500b145889500a11210b02091010065490b00d5150105e03010408101503405070364200c880d10351208600140008104129114101e9440c0400181000d01141034032a2185c43d4202c90f0401695109403c0d600300c10385101c0600b040268503074000042c842c0039406010031465904000b006201500102d840664440d8031020541300d02030814205014100020100366622001901403200140a80744660049264a1b0400318061480b19a548840e03010a2250001d804010580d08240525504070040000030400e921200d001c01d0340707900ca0081c1d41502c035034403081100240035250300000200e940050180300c000d5a02c02020755145100604280d0500611801340c0840001c091102c0c100d9111303464100303007250b4408046452510000c0101e003444017200800100995807505c0001030a035801c1e07000c8168101c590400e241042c140d1215045a0602081262040d031080a40750031950004010440307289860302a420502690842c214 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 644049892 1250 644048642 644048651
    0x6050c040b0f040f0602030c061501120903031b091206181a150a0312080406091709150301030215070606050d21080f0615040b0d020703090801050618070e04 69
    0x44410b20001401243e03040c0c145a420786503a0f02059031a409207542602540d084100060341c0e0440208542d4400c480524005400c0a14071403074004135403074600306500180d80e031068a40300d113180c40c1201044a4440c2080e0042905e8083c8248103c100718000501940d2540c6100780c00c0c4452103080040341c0d50240102a403070b40052003c1d030121904032480c1208404089080f602d90500c10300140c2074075003000212581d0100315800390307034400300030300115426903480c540d0201040111150440241c0070440e0140e44081c60700070012803c00e03100380740c0a8040100010401641da81c20602d18440c10440e146484509904114000304400c1c0c1c461a000903003050000100000010081252961030203510f00540303000604490074401254a150185160004a1080c1c84c2440c1030300e0341c01c24a550040c2c54651115403400301c40d002900300301a0183c01290000406400c20001c1d005400d040008100700c2c9054000640d8460030400105106040100071880a51007001502610700b4041d10902 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 644051142 1250 644049892 644049907
    0x2010b060c210f04050d08120a0516021b0d0510140f13050a171e03010305280210120c0c05010b030304080a021e0907020a05010f050702030706050c040b 67
    0x585616039880100d403104081071002160000d40c0e4159443d49200c050043c1c1030a0030b050a01008401809054410328014011103c41502042e81a407103070300003901c003051300e0a0400307090201550341072041c01550440410802c568240c01802400520221241d10b00d1b600f13035040180c2455600c000708078046041507401c1c044050140c24013070183c19000b02002c010b581310101c05040c1030110130002c110390000c0050b48085010b0007100454150200c0100e0701c1d010658502d940908402000020040301c080010824000c00384171403014100050098060402e903003005032040040c0c003100a05c00c0304010546c00c0e1940c400c004c042c80f24007003040f0801c4103489080010782a4a0310120403038081d8288820080e07a810048140d40c12594048000c00000c0815820070240000d84040030162a03014240e0050580d1505010350140805401803c0fa031000c9090607800e540300c05803046011130400b03060000550b030020803618240c1d044400060303e602e0711150340c81244610f902c910350741403011a440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 644052392 1250 644051142 644051167
    0x9100e0d0606150314070c0305040b0a020f0f03030717070513142806030f150b12070206130b1005090c09010801090504110904081e0409050f0906011502010b06 70
    0xa00c19259002d150b1222041030700400c401742e40300301030f030b40c81004204d4001c1a0f10901400142620502c64200141000d803180031040080d0045400d540041e880704404040143c01441540e802c1036821019614601d03100310301410002c4440344401e014203c003000140054400c1e420f40d0144040c0c04019600c0c15582c240d0583d0184034040c100c0d1107480100c04612440d40280d15590076a0031000c06440901e25085d400e03070007040761030000e44d4215120021940d0340a800c254500141405080898885041c00d03100007450b40002d0442d015513002034240709614003854200b0707207420342c02a003500165450b0032020f01120301070352002e034200600205000c00d41c2001406011904400c0c5c2e5135109a82ea0b4001c80c00c155481a90050147d40841a294030a81408059141e115020b1078281b40b500101603000e85800305114089140d2a901040901541c0100c0c041c10790011000381e0300d00100d0070300b520182d03101e0300b0620401d80010030326160209014000c0d04641c000c0e000003804684c0b202c02d01181c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 644053642 1250 644052392 644052401
    0x10501060e010e010206013f0302031309020a020703080d0e070b040510210b1906030f050f09100b0319080417060106020a11150304060b09090c0609100e0d06 69
    0x7804140c181e54070f04155480041c00034100c9400142c010786003621042501b0410b20030408a030211110702d40010400e405040c1c100b0800d611075030080d651a641c44d600000d002b201c94100503216801004070013a0385500003800015290405051640c03843d407488104001c20001d00c0408050241d180d001601c064180080d004a071020b41e8034041a19141c041143c0e03c00184501c0568945e290702611075104903903108062000000e80041c20300e80161545c10b10082e155401480080d480e1a100407882d85203004541e000070131844502d9460600710a0183c985a54144200c5402c0da0b03000703440e00d15a002c110041844282c50484c030200529428024416441070242402640c015041d1016000f4000f81c40390407580035070f0140c80c41c401242d4400488017107110304558003c44241e494600c0c004982c0065009a100d0b510004034000610700f0702600c030720000c1269525420909034a80c903616580c04541350b00c0401ca5045403540f240310001c2d20003100d000300307031078006030700c22840c03c10030030543e10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 644054892 1250 644053642 644053667
    0x100e07091502010204121707081201090b0d0201020309090429060406060801030807080f13061116140f0d1a091207020109031101140f13050904110d031101050106 71
    0x2001925510001c0180d080c0d03c2180300341e61005003180c078a000881c10449080152080412000c0e103405419100c0c0794098201c1000d010708104810700411040e0614821007000084c10307141c40c00c840d001500042e440f80500b50080c0d00507010a03000501b0000ea59030520000e1381081405d9002d0524540682c10140d0111001d50040346015008030300d0600502d101c034100d903880714503030346070446035981d003c166005001902000e440c184010204d001c424505400a00159918104254a40156903181c1314000080034007410b074840b000d000d50781441d42c1680008400b9a402c298401c41d10001c10f20b808800b420151a00b40d00f107150181c000002c19205000d01c00b11012a200d4498038022070055106001000b80810000c074001c000240111020000400c414182800c00d4403008a48414590184c00445120040041c07445c0d00029181d62480c041c2c0000e0300d40500c5441c0a03900d0441040c000b5051070f200740a044850410984070714203c00055800200034890380d40e6580f0050301c0b1215201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 644056142 1250 644054892 644054909
    0x17040602031c06030f170d11091011031b0a0c0314070e060906040e01150305010501180e03090103020f0f131403030c0703110d021917070806040b100e0709 68
    0x12040807101c2c0850140f50143c0b600128207051000d803903581d04400e04044c0c032559103802024407610f00b24501c00d104400d07000c000c8103002a6202001c800700320340481c100340e02c030782804101034607030000000000940d0300e0a055415445910118501010700d010650000181004412100401088846a1000821070043c3d049451054640c00104440c18049800a810005082c001400c03840c0035000214030250351400015038204420702d00b40118a960000d840303503915000100080c1d601c4140a1091240320401040307060307400d0303140b43c0c0c584c420341e00c03498100b40d004039800c554407000070122145200c2c0984182e03581d0000084030208600107115900720710303000000e41d80e25810048111918a074080380030744581401e42c0d9520410081c914002600700304080f400c000181c8852005c0264440e406070001000c0b45002c0200e0030540c00c00c82d080b10300341c00c8007030304010b0060b00140080d04183e02200184550741e0b00303880b24801e016590700c00504601582e003440700c1990040c803041c1c15200c404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 644057392 1250 644056142 644056177
    0x6130f0207120f0e010c0206070b07080702100902060d050a1e0b090c0403020d15020d0f05060307050a03170309120d0b041508031b0f0304061808060403080708041704060203 76
    0x50b4040d40da20016941c07000124200800000c2e1941c031540c11841c040c1c0c8010510390800d41140c0321400c0107001201c56201060720305e400c0c441029010021007004000300d1704240f0010903c2d030f011545c01c0c0220708142c0d001c640c580000c140c0307081ca20b4000c519a0400b94003c01c11303801c0ea0280400140c940301c42100c0c002e0303070550041685d220244040301d060b2a0040d2208040f2071031130756281c00c2d202c0d09030171249189a00380001c407030100391381c02030148403003070804081804c1c1016800c040c2800456485103120b0b1824000401c00181090b58000303460300c3c482001030703ea0795001401c604042c040d0a21075015007000440b040c0c505119031005425290035517040000c038064592074101d032855800b40c95071a07030041c0002400c031103090407103214120800b0103541e50404150030700c40c619082600840082850580c030325070351080c0c1c807640100400b0384600902c01e42c18244c502805841e0042d10030020031500c13100203014024964a884a00c076640050705941c2d5035036810081d1290030026003011b851014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 644058642 1250 644057392 644057423
    0x50108060114010e030703061802090603030a08072a0b01090506040b2116321309021908010f0b12070e0613060801050103060b060a140306130f0207 65
    0x2403020305032255081a01450b4092900640d4000007103880c165040c030030071401200050540c05103100d140d0303111540502c0c0507168410030810010041905010758020301001683d40e51103404240c01400d05e09007028400038070450a00000c8030b0040022224070301c490b07458200422462417038100c0f00d01c40b80811294842e00304007c10b82d500d80455035400f55507184203001c07201401e6a64200184820100c5646c0380303803d1054144030340c80758044000f031b00070824101488120700e0411b21500cae0124000d00c44548241c0000f43c040d031045650034031155500d4980d07034119164210a000132880742844107141c2d90b56542090f018041d5003001030949403d040404043e411b0000f5007804021003100030700300e203504144030194180c4009002c03a138413a0300c1042c00a4060341a100d5400034105180c0040765a40c1141000e4041d200881c0200380640f80030000510074942c800c404040041c0c0d429801a40c984074400061041c4000707650245005140030300c48106c0010650081070340328403e88007510111300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 644059892 1250 644058642 644058659
    0x604030624090c08010b210c12010e0709090f02070501050423160911160305070302010b010e061c0f0f0b090901060305030412050703080301090c0908070803090f0d0615090501 77
    0xf42c0d125001207000310006104252408002c1c084803c7e00b0144030b003038014004030520001c0c03801e0f01ca910350b28200045091840d03100031001405030995110318655802c5c5141c0040807080c841c8035041440d0381e0f030001900d041d00160111100345400c24000d0041d801c060520111802c81311818903900c1c90420001e0300d21b600d02043d14176a19580382c07000c25800780f41a036160050b240c04404849060b05c20080c2c1e02074410003491046000b802a9941c603298061440e019084444a2180d5818850500d050280c0b580e103d100f00e4044480440c00e400c4440d00040261010700200485090ba45041007501d03510392480d540321460714802103404401c20f855201c909403c840f007500000e0300300d4004200900590900c0301031444242d108404803007005a0765220b8440c150401c0e00401c01068448241c501c020758883c41c218040c05064000c0d01000b840c0104042d074a10640c06294024603c0300151340450351a0f924000b4055040744003480038541c10300c903c80750340600d0701440015500d03020002c194002e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 644061142 1250 644059892 644059901
    0x20319110310061d09010608032a030421020a0f121a0408041205030403060c0e091e06010f0306120609030815010903020607141f1a1003050402060403062409 69
    0x415548200071000c4a9804c0a0724000c00140300003007540d20b80000144614081008259002c104035600301800c060540c84c039140641d103820241964024403042c4400340410482c190894003031003c4812070180380c4042410440c141e0321030f22069450304000204005115100301d1501d1050404032444d2100c0204080c045070195405002440c00703000901418500d5164014400d00507001c80303003025039903a00c40c000d032810403000c00d00045140303480d800e41e400c0c884889030304032a00500c8034400486001e1040c0600c43d0091049041000c010312081c0114040d0b03101030054000a40ca10f0001122400c10b08080c02c0800800c0b400140310000142d460720124140502e050816981e01105d94919000c0219640021106540d4203407880c160301e0004400300f2504a54806800190f80d50400e444200b00840f0f00c03034100c0f8040380b0b03105040c000746503952801d070400c0582a8100001c8503100d43c008200180240c0d00000c01d85441c08410780b40d481200303102d401c4640c0011841d56101c545a0013000c0589 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 644062392 1250 644061142 644061149
    0x80d0c0b01030b0415020a0c170c0a11040b040f0e061b0f480a03080f091908280c02040902121203040501050f0603120702031911031006 60
    0x140c81800040c40015007140880d0f8019000d80c3c18042d640c07881040d003101b00d9000c05190400b04101442030010010783c940b65861488242d410f050410050340701c05604c40491300c600400d048000440c0c00510364031a0302440340d05001074010080780b00041403040007030803d5491000c06100d007000141150f007101c1c1d406100262602009814070200350105440c0da003202c020044541e020800059110300d2182a0701c4082a0310307175100c040c0348000e10b420300c04401042c50b0107500d07420107519000442d4120f2401500541101035150565031000e56203030030001e10301c0c0511180c403803d102c40300500880801515403000302504844056000e8041e0b682640219082600407502c132140003030151409620040900b0f0000e400215040c2c00e0703009042c1420500000170780e2041c2d011080c401840424400c4690244001e00707020801d0419500203592444102501907a44000294204c11520148038070200301c6807080682c2d00340011403601004260b00000c0b80d5000340b007481c0704000181002c0c00b65408030b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 644063642 1250 644062392 644062403
    0x181a0c12031311061c02130e0603150411040903021e0d0e040b0d0c12152307050f040b04090e0111030c0705010e07080604140c0907030207031205010f080d0c 69
    0xc0b440b07070365400e1504804280b1650f01c40b90174806207100d110105564086420000c80050781c0d9106030301d44041451030303500001100449642003041c1c0e900c00140e11580c15200200034100c1d47c0da2071a10b07004503010116050380190a00d250101019000524000013500d001c058501d52214811890ba8a101e0060101d00040c204586400346081a5101d8868040c003c2d1440141502c26203c03079061002e542d11010080d6184500e800500a89100342280410a04401e021135903190020284903800c4501015182400c6808a0041c500031811101700240039089291603665440b40d540c0150098840c07804035038106121190740d640188109041ea1030016003140c00c64542400c1d20056410050301100e040d9a250103655903038004111100040c2008001041285082e28010400c00d0b0740480320561039110302c810103590b0b03a50f0001d80e075004240e0700d8010b032100a00e060440b002107105241e1340e1424945000410300c03221007400c0340255201c44007103130f4a8682c040001c450509042201400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 644064748 1106 644063642 644063671
    0x160b090111030408250c08010c0905030d080a020a0e0a180b06070507060806040605102f0303010302060f1c14010911030601181a0c1203 60
    0x91406201105003141400d0344c030086a40144041c00c41c0034502004c07007000c07203110200c82c1607480c1e8220a007a004195103002d418000c108080601d000211030b20f40c080b1f03031070500040002074050076907540c1f645551020a2140250010700d084030400c142c80c81e0350070865540300c141c50040e1441c101c20a03034905000c00c80720201e9030503000e1140550814046c50020a0f0b02180070b100b1103866041c00b03119075540c070b40003400034950740e0807031540711600c5d02460420a074070105001c0d8450804680100903e451132003a210104006001da09035071080005200504164014045010a1035011410002d03803210880c0400300001044140c00e0340c51b011a8260502150001d0041400041c2040200c045800030011b0380300c0241018103029024480100e0540031400035002480f0207801001e40010725035010425074082001c0282ca031003140d40c0141c6989250040300c1c01039603401e00302075 = true := by decide +kernel

theorem cover : BRFrame.Cov 643884892 644064748 := by
  have h0 := BRFrame.cov_init 643884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 643884892 ≤ n) (h2 : n < 644064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
