-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4816
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:49:39.890551+00:00
-- url     : https://prove2.me/submissions/d4becb9a-2f78-4197-b3aa-890d856fefaa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 866007194 ≤ n < 866187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 866008444 1250 866007194 866007199
    0xb07050c0d230c010b0312160303020c0c10020607080a0911060313060e0a03031b0906050a0e041404020102011d0606060715060e10080705011d01110f062202 69
    0x94a0a58103011916100c048100c041c01c014001203540c2c41c80701503801400e160041000110360b01070010201402d0a401c1d040207c00010100400c6040300c2d0310b980d580c070060f94075080041e280d180c0034456603c1d0030500b9444ca40c0005d90300035161449500050828070921f4640d545039140c3d56800d0015054a0848000401035801040028603d1804c04040d5038840f03000940e07c07a14804a45036007050b60701c1882110301c19000f4081c0324060541c5400340b4603401001d80101528024540001000c0c1182071203000c04008001c02d40700c64040c429000303000510401042441070594224070010b0301c04040d00d080707001d036192948000180200f801c00007103d10520f0003500c1c44c4c0c1d17201d43c01c1c0310069006090803a1803070748500d03d0885120551140c4005800fa8590b808024609201450189219900015200e038411541048030340c1c6d0101c11219014011a41d88070218070b1200182c8400b140710034090b6645c01080503400401e0740c0090403500c00c003200030038854110001200c264a40b01046400394 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 866009694 1250 866008444 866008453
    0x4111f080604050402120a060203010f051c021c06020307030204140102010b0f01120e01020309010905010b010908032a030703120b0a0b120c1c0b0312090f040507020705030a030c0b07050c 82
    0x960520b0140e1055600c00e00140c0411a010060f400103030a021184600b00c44060b808001440400011100307040607100a0b14501c40618011440812510320004001c0c8370b034808414001d110881c1803d01480766074815815501c9080c5884058003039000390180c18500b810201507115950700c1401804003002c8040d04a01425900380011524001518020044c040d12030422440540d402d1004610540000c400010039800a140082c2550140400d040c104048002d052201441c0403044954440b080c0002a0604800b810843d002184542000b805400003289883c24035801c291100d5103003500d11400c2100780410b00800c10844458001d540c2c02400500150340d80340c105412003500944403421160809228880c00410f220154520741c0d0700c181c44443d4090310781010002d0b0100c540009489a040a131000080341d204481c00502601c02d0b5200d0307000c034003014000e00004019100240030750320602c038a0b04000c0c100d54901345c021100104000005240c80d440740c0305681c16840c00c88081e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 866010944 1250 866009694 866009701
    0x1a0a0311041d07050c1914070e01061b0206040e040b1803040603023a1b0816121a03070b040605070b0a1103010e01031505090d050a09030b04111f08 65
    0x200440b2000416680600c2410006007020120401c0400c030819a44201a018480c1614140c0009440081e03e0031450f4495078042c0500030485a80b81d054a6581c64200c8000e19401c55003292100d401c44081c0d0030910014010460b14407504540384100d010340982401030301c405540e0130b00c82017001c080d101282c00c103020520034907110b50002c00d0031000d200e0380d1000c060900a01010031110081107202d29201c40480c801c12028940100303400c5100583d80d0301400c0d00d40f81005400b02000600c20705100482840c0d00f441140201510759541c9800c95003003088235010a0148200d850304a00c4a00c00c0c402c5540025030104402c04407000e0300c00c0c82c0d8070f03a400c10640340c1d500740103031001600300c035001341d2261806403030308581401950090a183d5070050255144d4104507600340c0303c608111b034030381b07081c01e0030032800340c0c03000032620181c20780d510300035a84080186080702d03603d5007500002c0c10310300003005010910070601e00c0002da5640c102c840071304a01040c650802ca50782c4807446400444d0015000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 866012194 1250 866010944 866010989
    0x270309090f0b300d0c121e0302040927020906130504081b0c10120e0109080a0201060e310605180c0a050105030f0a061a0a031104 57
    0x5419800c280008a8200640300c002104034502c0c05003180c4080c80e80d016107414031044a20034810388107a83c003030846081510001000764400c40fa0180004801e144000c030418414015040942c030040302400c03881085442c020041e60091145100c41400c100d0f0545104c44080007070210f01d510f0000751080d1804135824030228060003440c05074405100421240d0020a50080621562051485544d500c03840c0c1c6221130503c00790700242c4980d82c443d04000c005a16045140c1c10310104034145190008800c000c550702030507503a40344009950805588108102e062000b40c00410391380e40080c003065455400310a540007045170301c0c4100c1044c4900400e12400150141340b024100c42214081c405600d8480d1420385405550a13080c1481e004801800b0b00028415806910012605030034498a0000020158003000d0401e0303e03143d4820011072044040d56001400400703004120000700c010903102c54015400502985000c04d0821003043c1c1840b03a0b54048509480c42101c8401002121006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 866013444 1250 866012194 866012201
    0xc150d0c0e0d03020c010909020a0c02190915090f050f07050d020d02120a050c030727051002030a0905040902280e010906090b0603071b0515070327030909 68
    0x10036028020301007151a01601c9400d407400459009400800080200c40001025071a031644404032041c81440044403040e4044840d80f54140c048030380c03626440d42d010260410340300c140d020180081c41d0030200f0006001100580e01111002c0c6030130440c1200c1c000d42202a030354202ea110303410301001d8000070050b40c0904040d0011106142c030060611502c001090100c3e0b2021402d81d80c000c460310304004200c102070003855884410b039101c06007181804000a1b10003800c2110100709001e5000000c02074030411008440104030040c4015002e030800d00000c1d40300d41c0448640301c0010410300e004030700ca003000d02402100c00e5018061b41e0400c0809500340120448028191800c03c01080c80000d0ba100c003880c0c0c0074040c19000301c00003a45403404090703900b00d885c00546240074a01c1401000801034002c00d00001483c098980303e605025a45009400d03c0c010011102800310341e0000d014001c0c0c1d160b4844520b01c2e44d00080c0c802401141141c0c0441d11078841d000400060768200c00f807003910050741 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 866014694 1250 866013444 866013461
    0x50609012709081b0c01172d070e120a030206040f060b04050705040f0f210213150e090f0a1b18050901180503070809062206020c150d 59
    0x4800080c090040da4440c00d6560180ca4403039590003c000c40049410300911446558142c2401c1c82d40b01aa10071010000300c7e04020310244030f40c503015a440c1855001440904140340c0140c1e001507103890918000f829005010f05414061400c541100d06500310002d1003149803a095001040c2541d03655664140171a2161401c07100c040d1500101005a221400b07124041c40715030b1500303515607040c07400d00414010294009547c040802c02c003000b04100d20742840304a00c1c0c021541d517400d083d41f40041140055243c0f159842030303107414061005020142480c00030f681c3c4e04042c01400391543c8503040d0703543c0400608031502c2d070040042d4000141400c9040b0101440003145e040e6000d0390b414900c40701031801729201890644500800030003500a100340300d80800743d12008500440c031620f50b19500d0043d42401400e002c0001101d840715078451046d503401401220f905d54000d40c030140d00300e940d002c0d03501c1800c0141c450780303158101ca40380540162054030200a101420641142110800380c000345 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 866015944 1250 866014694 866014769
    0xf03070512151003200708070b040609061d0c0108070e1008151912030e0405160206010806150108150312120907060503130212010c020a030305060901 66
    0x1c010141c500007444101510941c1e01e100040480c950030300602c07031481d1000044030105031a100c0ca10340302a40c49020900707804220b200c45503c030740c2d4030b250050713076032195440c060034001d4658104020014a6001454070303a2244100740174a10b04c0c8220a0700c401c2160b100241e0a4000245240d0503510550400d940030711549081d4403060b0700e04010501914030001c081001440b503201304140d03001d442c0c607000104042a41d09031008030940b580c04240d403100c1c1c060041c65414200c00741041c548a01015071900348000c004000e40c2c2001c07218404907041018950340940a13040c00082c80798000b16909118080e002c0901c490b10840100455440710b0080940004150f52608820203440800c600040041c400c2c44807a900c4411040442e450000208104102c3d40302e8001441459400303810791340c000c101d101001d02010540c1c400030700c0415540880c1c10903586001d5402d0202c550000b80c03499154040d172020020360300c070b010500c18225424050803810700000e001403c20010007403000c0100716080c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 866017194 1250 866015944 866015947
    0xc0f040504111c05071409070f050c03041203030b0a051c030201060335090a03061e1e06060c051b060712030b0a0b12060f010504120f0b1b0f030705 65
    0x5000000f6200c00e10300e01c40003000c0403100700150810404210420207080f2080c10070950212000020701001c6c0010004810480c1d00c40c002e4240b10f004800381c40820342d010054a488545824499090040300c10056000074200701c00d156940c24030f4840c450039604040d054600e0070246d0080b0f0840d0101010003201190340e41c2200101040e10201002c10700d0816000c4d01002050300710301d0808004052114400700c0004100c41140c42e5035004817102203e5021b040481c04a060501d0f183d1480328490741c1101050401000240c201d1007445080801c41d0307491810400709440703010880b50725088090041059100401c2514500c0d548040b8040c8000018481c600d07010480e0b030752200b02c084448150003c6900c54101d1440c034034004c92548058860711442c1814485014024500c8540117001940200310740c405400700e03079110b802101c025005038410784c068040c6614152000100c041e000b9210346081c5400f0400c0c13200190400d100701c04115180e242091181b10010249a001034800c2041c82030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 866018444 1250 866017194 866017223
    0x10e01020f070e092e0b040605060c06070305090d0c15110403060b100c020d0201080c0d061d061002061906050904032601051c060e0105010b1b0c0f040504 68
    0x704005201c05454018030310b0019081006400d0301d08000703032146001d81626450440210980b40b0003c0074805001d80021505607000804a40104010b0304226045140003400265400c000502c460080805a801b00903594820005a03142d03100c2c02111800144104810400720b40c4038200d001c03100c2da0b03054000039040e03002140c0040079441a80300301c03400358544902e40c1d000e00d40084e40f001420030a003001141540da503030003e44440b0035040024144040310021455120243c810780340842e4090313108100035070300c480b1140c0130b815282608104201c0600c001600781d0030000408075945d407054004100b40d4580d4030080b841458040c0f4043c4610b40e1384c1100103001d50740d0744100b90185010f03449109880400d0490800c05200c0d450360f02032840c84800041145440340b48141c51081d00d080c268030b02c800da283c40c141010304200d0780001425800c05001050011901c002440001e03459841c0c070301740c9000e06900035114211000444d9000c215982c0d06801800d054111951191080221021100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 866019694 1250 866018444 866018473
    0xa1712090a0525230330070b01030b0c0c0a0b060907080c0a0e03010b04090c06092c060d050f0106050114090f010c0c080d020604120503090606010e0102 67
    0x1011266400300e94801c803640d40a101c000c0c00035074000c0c400f08601c101a6041d4900342191021644181d04c40c80e408140500054010b050001c2da00c6207005003603030100c404040c181e119101c21814284030301e610000c2101c2d003080d802800c44200c140d03c840014401d81c60350700c80004d4074a00070f000c02046181001b007000403000500c00010054031070354041015003054424003040080c020280014040898203000d080306142050307446460139480c110002502c0280424007401c616403080b5005400c0407921400c018551004e03905031141c0c1d03601c103200306607104881b200440440d19100001030b0032012102883c1d041c495031507484140542200c00c03456940c0d0350b03549040f600c810004466591404180b00341d41c0e00a031035005c10704090301c5103400c11244100040302d101c3c1c0880c41506011840840f00100b24603a0344000040070608242d4414900c2d036100652a10740445084481600c1d0307420300b84015002e002503a000c0c000003c0104180d65984005540e0401211140c07819845000e24041051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 866020944 1250 866019694 866019727
    0x110f0a0515070e0a090f02041a09030c0117220f03120b0604210f0c0b04140d050a1b0f082a0306151f0c03120506030a17 53
    0x114810001400040242040031910000c082c0141d01048040788149400b6035440d40380e0001e655001100207070800504610f00c1c0244656400810304088003a01215090741c5900544500c100940a580060300110011100d001289656400301203e4002048981441042141420407070407264901100141c607205c114064000c0304a000038180c4410194001d02070207042c1941106448950030a424014a0183d281131091421540034815a0600030301c52500381d41d00405400049a0208580b10b01010000740c0c442d00580706441d8044000032107070b0a14482d5100d2082d08000508845600c0d60341e0007100c441c00c841c0c40092080c5450020816601ca0481c803001800d00c1d0000b00986030504480390480c210241d42c0280e0780d90a507000d03107190b480200c1c00c3d942c020300040d84020f40810300310008021004032105140480075011401c0480da402610182000c2d001c2e4441e0750000c240e07502c012041d181d0880c1e0301501600015040c03000103c051110310780241c05100c6507400d0000030f19004090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 866022194 1250 866020944 866020963
    0x3060906020c07061128120503010918020a0b031e01060f080c1305010810030b0708041b0501050a030c0504080d0503011e0f030f0f051501180501030210110f 69
    0xa6030015900c0001c14003049804014030041c1001609403490300800758490a04060b8400c0340708000b01411150350365048491040b5501811056a070380841c1401480c6270030902450702c1481c5049050000e051468005088147e4000c00b07805400e4100010620503400280900c4491401c10100401d02603440314058003030061031340d900c00d4130300e280707100241030303141c0030b4401d01c00190200300801c0050300180d4518140c3d8800e081c540e1003510760945c20800380100c0c2d0304c0500400d0f94081807000541d0b00c0460140560300540102014107000e803840d400d0005548240d81c0072907020010701900700d000b40c10088800c0104d0a08a0405030b4508030f05043c81d102e460700344c0006e90004014448030318070f440801c00400011414002d42800e21405460701c0c0c0050002803e540d2550003594100280502c054894540c41400c0c2c2e86101d441d80c0d0035440c1200c4c01c0c041d41c0b1400b42d040b82851040c9005100f4a4100e07078006010b0480d0744404041030f00e101c0c5100341069818002e070107c0000071304041108084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 866023444 1250 866022194 866022203
    0x6090809011205041505090f0102030403030b010905060a0206190b061c1b0801050f550b030a0b030d0203030402010f17070f2114060409032106030609 66
    0x16100024400184407603000c0740b002e0b2606151600f0301c404141c451001d1081c0014140000a40b612400449464400b06072412450740d03000004000402d40d05070004281101d080c0c940520842d15401007040b81d0240e081200010392110001031003010f15900c80030078036006000009100610180802c0283d401640002d130109182140d00824041601c54051504800061201c1ca0340d070004006003a10740610500c2d04c11601a03840b2903465075200002c10141a2543c895860702d0303003107020b265210811000c10020b00c03120341e44190b4044446480724a450365448094409142459226121608043d0150030700310f540350409061078500f001080c20021741e40e0011342d1a0b203014400141242180c01c5c1c004108529055544003880707264146070f0f0012000d003842100c3c1c1c0d460358030440303902c880300844202c5021500382d84070002c15240d00c0343e40341c2c8421009540d12030799240706000c241c03041d020005001507040c200c05400004200c044105414045101096442da00d49850041d03855580c01a40d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 866024694 1250 866023444 866023447
    0x1110115050306010f121101021002030a090c050111121b030f030a0f02130501052d0901080f36010504060501180e03160204090203030301090903080c07020307170109060908 76
    0x8102d180070051140103040c01c800b60380c2c0d000c2c10110312040740400080e000702001460001010160b0007032101c0048011000c0f02152a45881c0c00160050141180107854992a498011459521400c000131402e141c1d00c5c004d00400b850b0b0320740802c10344e100c141d030070816016181144400036001d0008080c0c50350547d90071512030800d0070400c0e007211486e6041901c1c0500c1002002d4841041c10001c40480300f00f42006a1103c080204030f184420030030708030100c0c040140150598000e0400d0141440f903100780d031400f8196507084d4581c2035500054401000c40d481d50a440444004268080c000180714000b048102c100480c084a00f5910300b43c1e03084541ca61075000520180700700c0c2c1c500c00616140d0940510281d0b000c80c400c0c0780c81e8030039a1240070082031120084000c0d920341e9048098a00c0c1d0140441380d40f580d40c1c901d0000181040c02040f4001021032020500b2906040c0a86032915002000303012641c1c9400d220551030340c60003002000f15500c411800010848500c282000580550340ca80e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 866025944 1250 866024694 866024699
    0x20c21250f0311011d1908010c0801140d080c0118030f08070f18050a090f0c020f0d030518030d0614010c030c02060a02010e0a11360601110115 63
    0x30320686a40e40c014144035001c804003000403400d07619001101240a003402900528150852407420445100c2c45401ca1a20212034412011451102c0103d070781000c001c100d889803101046640306401c0c41010103403a0305d004410070600e000800401040d03c68810a4a090010282c0d107080d50610144031184840c4511000245034201c40ea003102d180f843c3c40c00c140305182200024042110702c00c1807004004c2910a100000007580c01c2c0d40d406048000c24490305660f41d280c00310060400304c1c42c0c08449900300b2860f11402ca00008201c05021411005464400003143e0128028413004150405141004040c00c608410500c000d05011052090100f11036007414031140817420a21903560400040c0441c0d4808241e12001411406a040b83d0255464070802c02c103d01401c440910103d903400748154860800ca11041150100300c0182d8004022440a01803d0000c070b4030121000030001e0301c880407810041c1c20300c87d1258440c8050400c5208000c0c0304241b9400c640801c8100c00030180040383c02d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 866027194 1250 866025944 866026003
    0xb0304110303190c03090518070c021203070f1416060f0c17070c0e060604031e02060a200615010809070305030307050c0c040e030f1806070c06030c020d020c21 70
    0x3c3e8019020982d45c900c20642422404908d9060040240e003c00040414a00842d6074020741032000d00c6030202100e843d0000e509110740b10001607401114000d802454256031041302154803400c1001e8202852041450310006640c550f003442d0504040164660640000070303801101003028508240000e034403075080f890a80d441c1015134002c040c2c4e01d40c0c0c420400c0055951402103605880d8000c031400520b00c6401c510504001923590b000794011004203c034040720b5444200c0c03030080701d40843d000034080910540740b40c40d03010036107503215581b441406018203940030742452a041217059007200d036980e583e5100c0d242540c10a0354010b00042002410a0b4500001c01c62140750031b404881c2040500c0785404030603070743d00c10050224280e03200402d40c40400b4400c5c5000f1f480130940941010390340c034502c0c07800341e41c0071050380500001b00b481e00ca51480c2c074a10009240b0a074070308540007401c0118038241005814105407002c40348068124a6000030301105000302c0d10b00304441c1d05410340303a01114a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 866028444 1250 866027194 866027207
    0x20711100c0507060c21020c130c0206040f05151501090e2a0409020d09060e010c0909051003080c0a02040b10050d0b06070609050a02090604060b0304110303190c03 72
    0x118003003003007030004281002c1040440c00e88100c42580c141810990090b25003540c40030348001001030354a1441e071a600d44150007041c1ea1a04800803100c0d0052032a0389840901103a03040b0103808010703440328002a0000d4621042c0303410041c000c60454040111815188585c81ca08450515a415400c82001c0c4196008100d12024100205000089180260800d00c0e03051956051440c8031150300313207041d1000c54030421140502400301c000d540c0d41540c04807000c00340c041020110f0360340f85007040f40e050004040c440d0000e003020507904c5146640c40c1219603030207800f0182040003001640d00c00000080d14040c02842c0c001130300c5014081001c8107004001c00c580341c550750302d80122700900407200740715400821242d040080071000600c030203401000c5021802103c42c000c00091601910000380140000c068284600c21240480150b40d11424031064555030320444a20190500100700011480c5000c607a031448042c0480e07051408412120080840041175000031618540d0b03540d00b031540c01f86 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 866029694 1250 866028444 866028469
    0x6080a060f0e28061401080d140423040b061803010c0302120a02070f14011e0209011709150c040305010b220e0708100e25030312020c01020711 63
    0x1400e1254182254260b4a55080c0c040c0491810f01041c00420400c040d8020030244040c5202c0e0358482da141c01103103a0751a03030347c010500401e01250942c2c100e0b4400320212020b8038031b04000e07100c03a400b4080705180f1160000d40d156074055202c0c01744072410740b00c90340685107a052040381c4092084601c03003071508407142e40b01000101401002401265019040480d410a0495500580e250341d0f606203844686100741d001001103500600089040f4015000040b044100070200c00c603044078800c0f10412031050809150104401c0c0b8880c062020304160783c25400081281a07920040894000c012940350840c2c1c0a0700f49040820184140030092040503c0013a042d00c0c000603070000540403042e990b00c03030f4180141d0305449854240050384140f2000e4010500d09049802800880301060054030048084044030300c101404c1032070401111800c001414040340c40c100c20340d0700310b80b0119401c6681d891448072054007002031010b91603091005018950081c4411703004c0a41c440c08010036035241c031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 866030944 1250 866029694 866029721
    0x9340810060512070f030f060f050c19080402030c1e06280503040f060c023a0915110a0c03120906050c060601050a0e0406030b220812060406080a060f 66
    0xf0401d01080c43c41d45e071007500f500c1d0020b00362a2806200d01e0840c000e011021000351201d406c010501c070000d045640039200030401400c5081c0040d004981c00c40d61404110f801030f5050380315a081c941d0032305100ca01640300d0040c1030f5490300c4442100700892882e500a400f00d0b00118076000c0d40c603001c0703402d85042421000c9646001071541c1440d484d00c81e68080c4910004c3e040981e11025803007107a00802006000810f62120b0b4602411800304403041c004008159038448800590300841c4280b040c9184019544c040f164900e0740c0b552917000b11905c246540700c110341403160101d61404104590032000003584a401d82071010904032070000c203000100e6005405100050003040030071800400c40d264046800e18200d900c903000c1e110119001c8020790302c05504540703003080103c14045600d004c82d10480745900d483c1c015004031103a558110402503000381c4400c1042c00900c01c0f584c51000559005100140082115910340c031400c0d0919041c00000c0f80c103603945081860b61480540286400c01000c0d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 866032194 1250 866030944 866030953
    0x111603052b0c0201051b010f1401090c12150e0103060606030c030b01050a0e0f0621070c0c0e070c060617010c05090a05060304080f030106080f09340810060512 70
    0x3801c03024120265004009042c00000b00d200780a48001c200c0340100b0b00d81c07582c001c0c01215840545c20300149000c081010075140000000718a40f8098098110300e0780c8a661000103540030405020f0052814007203001000c1d502203000600810302c0940306010318000c410005c0c8203403401724013408071041c40890070300349801c01244580030b80e040420b03070300c80ca0b22505001031113410100000300e001840d000a268403040c0441c0702c034454100c0c540c01ca10050400c900e14000790300c1d00030040d503021380b91342d13802800701b004a0350504c55480125950390300901541000c09403040599644400d407400d54210b140c6000c0012012003c04600340150340600e104c8d4200306190203560008900c030014580201400b80b10004081800c0010b07000c112000d01d0303092100c058903542c541400801441098a40032021452000800c04485003c0b0755140c0c4201d240003a9010000510301c2c0c8403184144080b000840410802e0000309280180328010409030303040b0303002402500340410800604039985644149901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 866033444 1250 866032194 866032273
    0xf010503060d080708130e090c190b030406110408011a03070f180b04050403051809072f010204030308010e07170610020a05010c1110090506182506092411160305 71
    0x80644a5050303d2410000c00d9980d07070303030f030400c0e6003e040c1d2200b51030fd0213803001400142d0818194403003500d800d46071591a020007510810183c0c1c80702c5502540d5204000301c0c008124144510030364040200b480003010440c4c000140020782156011241079005c5000010034110540c80306d00a0344041d0002c0b11104811300308040c00500101403103503c0641030a96036501c1c1c84504030b17004180442120f00c4025940c81d503c91030014034042c428819940740d82030041c041541e03076005103076002001025260120303070b503540d090401020310b035164071503000d6000c0d10700d01402160003801900100340035510f03a04040d91407a8681403078941d05800c0b11101514061000000440100b48150000024807008038111b1000d840d050405595801040340c854000b0400d03c0040c4002035104100c41164030f841080c56130355181c1e1521a107410b5400b4400706041c040174400580113820540c80311816004172401d000c00b03200c1c1c9010700b2903203801c156900c4c1d206044001d6160714417540090080c0c0310501c000034951 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 866034694 1250 866033444 866033479
    0x10f12090f11042a0c0b16110307050d0309020f190e0a090305030a0506010e100908060106030603110904081303050f0606120d0f140a08060f010503060d080708130e090c 74
    0x180c402041480c0e4208001c0d500c5522440742d00c403c44899040f04611406041290421a00300111f1140e4008509000010b0a5151021041e140d003560880d01900c9000014035046000704050390040745d0040e140207104600361188541c00708428070480301d19424500b8005100100f000041c00103c3c01030801340301c03400181d440420341e60000c048242c0410152140401a1a4120110b81e5260007010559111000603803040e02d100480e41e1100580d0b849989900d0120f0541d5040c0c0800703800c074000ba03860140c2d141040c500e45c6902c85d0003540030341d080c12400d1a200702182070640c01550b01d50301601801e03004420506c08190810411a001ca0072406070b0002c95441d422400200014403c40a50407112a03028008503802403031000b584654840310200c01400d4030900b55003581c06a0b405055110349035000310202c0340910300043c249050f160741503846407100c0e400410220b50300101840203949000c0079420301e402900b103182d030f404000d11b000c030111031078140715401480c803812071440c0402151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 866035944 1250 866034694 866034731
    0xd2c010c0c0605060406170d110a020a0b090102070305030c032512050f0d0f0c1e082430010203040b040b150d080a1103030c0306010f12090f1104 64
    0x119032040c8080f40c01e5480c403000800516103a40305000c0e46010400581c0007100119110f81d407602d00740c880300e03840c00c100d4500650341c031840c410081d00010705440038032500c004100501302c006014070465100580340d0b07540300c1c1590800284034a507a480402c40f8560240c0201c0104031042c8000d440540d04112500ea03805200320442c0c0d81c03020312100165645030407100b5001c0b295881610041807142000c41d560301c0c0014103200714813400148001100c06805c280c641c030031440c440c1651b1342d044801e46502c0000132480300c01c3c02c070141850044d1900c0c008035171036102c0000c403401c0d080b09404000b40040e01613004900d10410302c003803160344104200300c000380868550326045a00607052660f15076618112400001c4800c00080d071056568410000b00205000100419081640c41d500030142007642e40f070390782c0002d45195000510510000e03100b5481807840b03d202c0307071040c40c0c00e000744624910084101d4210820545001000002007803c4c40714414108159050a54007045a1503424881c081e55 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 866037194 1250 866035944 866035967
    0xc04020306060919120c0501080f1504050718030c0603050108030408060f040321054002010302070c060f0e090f0403030506030c100314060d05030409020c030d2c010c 73
    0x2141c001c10300e8944c21088061403406072070b1602074084015510308001341d042e00780d031142a0001d0004800120100101010355004800c90304001d054050154200805044c00074940020842140c109980701d94401c502c010046000300c1048420f1b5050000c0141036030416003100c1941c0c1d100300000c000310000000c1c10b0740d1000c1d0017014075016484a2500311100f040706000655440ca250454181012241d4042030081c07000d0f1261901084428041d12046213041c090304a08c000ca1510741c801c00c60002140c3d280c00b07403051500510300102130781c81c44d0001d040b0340c100b1400505810b039400e41c582c1d000244201404821140c1d0481031508101e0400c110000610007800c141d150404035980f0740b001c1150540d2020001c0900c15540d0072850300900500382d403030707010295824410210342c040c00c003c400034402d42c0d0014051842c143c14140408041d60002d01012a188000c010082d070290b401c2c881d802440b9110542d101e0101c0d1140c4042883d194405c141100c0c3e640b40200e100901ca80100d4410701 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 866038444 1250 866037194 866037199
    0x50604060f03060b0408030d050a0516080c070803090703030e031203070c0218010801020d0f0204031a130204090b0105010215010b090d020a08251a0d05061c0309080c040203060609 79
    0xd80c5118040c08801900884c0d0001405034800b00340400c4101002c00038009001640c5420802940e1f07100807801903d070305840380124801d040d540c5050f9244034400f01644244030071206032800035030b9554038100b0307401210381c1c41c01900400401d008269000c110281e00d1041180188006a07a04c80c0780138480c400a402031003403040c6144000d003191105480382c1403150403420b8044143da52800c40d00e0103507004180b0700e403241b0b1504807407007030943c003910940e401d8a0300b086103440603008a0402c103040c0400640803d800000c20184680141c0d88d90141d9000a0700c00c0fa405003040d40741000281c90103540c40000c040452016006000d81c100b041c081e5a50482c0c00c071680ea00e001050700100d44060907603040380b980ea0142c50124481c084505807a24460101000785048642c0e071500911001451180d066841d00000c00c5010700c840a50707000180c001c0f900070043c05000c0c7d58442903030401225200110003042880f9002c0110400034021114000c0381900d0035880e506d007190002b00f10f482040c02051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 866039694 1250 866038444 866038457
    0x20c1e19110909030903070801200310030b010b18010c0209190906020c0601080c06070c050103090206090907030f0c1103090d1703040f1e02010c02090703110a0c020301110405060406 80
    0x1018424410715403030420801504507120340c20700007811500c940c026540d5500902c20320b100000d00007130501c21400c42052074050b039507417000b416400c940e017944040e00e0360784000740e014004004904001e4049000b030810420240d5aa01ea986000c086ca502d02c4900c1da0601c0720442c0240f000d0313207803600040c1e4000002440c013900080305d030451400501070680068000e40c80400e4203151000c001a1140c1614003d07411221001c0408007040128070420400900e05402d807a4200080d500a400000030180b0050840c0d040038401c0002c904044011502240069181d100c007400c0540da5229822200443e80f41040700d8001c030460266403032040307060179809075030b103c0f1000003403101e22949404030110120140c1d82d20b003020300b420b203641d2010002c241c030007000c5410030302c1c0c0c18500c0d8070980c4410360b4181c45130284d48031a6020482c5041005004070241a1641046014008540e005000750b9805403035141ea80c90070b034014103084600318500140030b9042000284150765400003a034040782d0b22850881c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 866040944 1250 866039694 866039743
    0x150803070308250c021203070309170a02060a03021206030c10050903030d180308280b030c060307030213230d140304060924120c05070213020c1e 64
    0x1c0c01c2001c50392900c2c40654041e0300325a603019440080541000d000303c4105000c0c0c400d04e040280c1f82e119203440203001c9940e661003084000c04005042c0b50101d441c50984a000d501c90300030603c1d075403000b0b9903000002d074002080c1e50032005031885076401100a07801059115503980c04941d0308498101c1513400d0010119801c40e05503001c008940d0b607840154020303c100450b00c5109442e45a64050880203c0c21f10030000381030125000c000341c0004c0780851016054144044044010050201d40c00e4242c020990115003980b141001913000303111658005030741d11103100c0312045600740c075000345105004400d201c42100c00a5200304800a00484840c40c0000745403905d680f00c038030270300e100345450300000ca000100190050031060484501c40700103194620312540510b01c6034003010b0008085080d50003071410b41c4e031056202e9030766141c20741000c07480c02c0a50340005201c015843c00c081005900041d40c81d1590000303100030b001444044008101d02c85404502549501040102c1000300d107403a03101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 866042194 1250 866040944 866040961
    0x60c070213090c03021c050c01120f1e0b090105101407050106180506010215010b0a052b060b030c04030b130f0f020307050109230a151101150803070308 67
    0x1070803580c0c042041c2000903401c140342500c59802c2a10017644201500c1e21010085220896400e44842e0300401a0105c03000070401035030701c044440b0041e0b031107039602c85640d80c0c103913214402c6041203c01070f0f06000c41d000808042e40140c0b00207502044c02404504010486030300ca0502d4281c0404c450300301400d01c0d0741c522aa91503140148000a0015800c11070005000b8803202100c1c840140310100074071544e612140160380c0c1d1001700000c1024040303440010050f40e8611805803000d840d40c3e00c0c200307140c521030703841d020400f2880c121100e000d2000e2aa030550720b0b1a50f4405c440051001c11901400d5150460303050065000d280b0001d0701080e80740e00029000046e11a400c0d51481d88000c03101082da80b2801c01103508951903030100e00030b20444002040b2907006442d403104070342c0080b500c210254000c013a401c0198103100407280d081141800d0102e8103402c0c1844c4060b40c0e02117070f0f562880c07031881324607205e01b511010001824201c10245007800800c5001c01103c1d180380e00b5003000030003510764822 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 866043444 1250 866042194 866042209
    0xb090409111507030311040506220504150f06020d050409020c122a06092a0a030503030a05010603050705040630021b0f0c0d0f20040e0109020102060c0702 68
    0x10080d50090302c4989031000071940b0000b07032440034000c0ea4100410034510318070203183c0c807540c01110b621403c1444100d400010103403550008101541601c86201e0b92400420140e41d582d03c0d05100540c1c041c6801d00280d00c0f1210b44d4401000340e440100411111401c000d046846103004400c10701e42c0000d03400040850801000c001114207543c1180d0344c600300e50304400710381c44481008520b401e5851016071029030006095003c1c8645001800c045000860010f204442294180300c0f0940801c22140c032950300d91610000440c00b5602843ea240b802648010407114140c00c070383c084c18030b02400e000700c0c80d90100603a02514894106418144840300040402240a00d4000442c40101c02e001201d2281034000d0841c8074520715640c40150701c403043c3c454403801005554070740c991041404201520b04680c002d4280c030b0240c07221400c205141d88501c800311070890006451149050141e007000e0801d840380a2440340d00030020014105c007540001c0d12408003800b092404c807400f1030050300b5551076a2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 866044694 1250 866043444 866043473
    0x50c07201c08041e14101b02190e10090c02030d1a090709180204050607020d020109081204060e031606030b040b061827160c15091b0b090409 62
    0x2a0000b03034040e134580c007660600940c050300c885886444151500743c24505250341760a11a520340214400300101a540f240f44051002e91380101c1e038240b0028844849860000a0a02c01c42115041e14150b041052020310031307841400950f1408407204140c60703003c029500d01c041002c40200765140a08020000201c1848006600101c40f106002d00690001045000c44440c0b140c078036141030516003d40100d000b20b03c1030580240c42001001c00516115000329100c61050602c1d0a125880d5503d075481c0040c2102c010b060102e00240a00102c1d0300011041c2d0f00b0f8030201d0040c40c00041854101010b88291321509081c5501c2e0b0742c21070415540c68110030041140500056214160341d500d030f00300d1400740e040c854005c08400301803404a0015a44040c44805100001d5156490b16070002c0144400e030302244042041101c0c4110000783c2503044030a031603024200c007264903001030620f040c0c2001803003001513000c05171403002c002591003041600d6001504850014541c003544c100b10740d4154008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 866045944 1250 866044694 866044709
    0x10506090406053001060503030715020708120a0b0f06160309080a1a06030a240b0607080d0b1912050a05030307020d091a040302040c12050c07201c0804 67
    0x21302c0030001414501071000b01072005181d200048141d1101c1c201d01300c5d00e4502405030190800c2000c5404581203c040c15a412440031006203001002d031246000ca410075051800815461010b00c88065124000d0a00f2444100c07458188842c8400015406d845060ba03600b03600d8400784c1c516070034180601c10400c01800000152030710706050789000c038804400350312800110440c207070104109040001e600701101e98400404076210741c440d02c20280184182d40c80031201d5444490804643c0ca6a80103030800318419004c0c01c1c0c071441510855002d44000291442c0100136480a984481c1d102e0345012003120f110049610500c00030f030502c10700740001c1200241081c0b01c00030502000c1c9600103522140c0b2403040d40c072002056114034212900103564072254071102c80900c410b101502d40303a07000c5c4491800e58100205189203640402d002d03075008640c03d20003803002203821400c0c01a003d03480000c0400703140c14010100001e1000424101c8044d00001441d4500d480b1201000781c20400c030341c05070420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 866047194 1250 866045944 866045959
    0x120f0c12061406100809070b0f130f03080412140709060303030506040b0f040911041a011806020a03050c0f0a0c0f0509010f030b04080c032704090b0f1003170a080c040e01050609040605 81
    0x1401811951192b52401d81d400000300000038846142290b490aa80c4d000440900c0e09240104280151074408815070758400c0ca20840641d0407030400140340100041c18010070194a9400c016088400003000300e4010b5041c82141e0311140c0c3c1d110048030f0741d220100d0b03000075890500d0030413207524400c0240503500580f0300807004041c51010b02c24544504400d98664a030781d07180f032980403070b80e0710544195400751b0310034004400081d0144019280320000740c4210f600080459650b903150603402401a207654040a84c10320490101200b1030000d4801a142607120703525002c0d000b85107103d1440040c018917150310204040281c60012100000300300b40499807101000d00e040c400010707030300901f05130390181d2814240c000c0c28180201d00ca8540c00c88860507043d658402028010f01000385800704040303a0742d81c0400040c00281d1204180d0031803e07038541c4c07038440414000d4503029000d003498507803410500c004c101c03040100305600e054034801d0310300d00d454422800205000e811142c00c44c03a403202d03c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 866048444 1250 866047194 866047207
    0x207021306050a050d050d05070201360b161b0e012c251e030f06060207030807150f02120403030c05040807120f0c12061406100809070b 60
    0x11550000000e07110200c034140c042135914002c105c513880d01c43c1d8006000750050004034181074050320190109074010f06094123034030003503030b1000c4071981800c0f180c260011440720010b1025201d40300c0300300904480c500c0b0310319119200803180142d68914100038540c4000d0380d408961682040054801080c03441c0b07a5a400756180e200c4c9034135010500882d210104401185440c2a030131910000340038800d140c002140e10908900c5009540c0040c144060074820050b0f95100c107503200c40c0360403014000950b40091416001005070b002d0303806a0340200219804441c1c03e0010400110490f2038666010304025400c40314410030340c02401d4400b4a080845101091440386c0241241c01184180c1c800c0c0e03010001a039034004143c0d21030189014000866121060610894981c15003401040307004070b03070031030092100d969401140e406a41015a80c400e08001c17403c108043c5000310b4000c2045241c54080919004000c40ca0b0202032194940402042c1404a509100140602c0000d81440c3c071100b5035817034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 866049694 1250 866048444 866048479
    0x30b130b0403020129010c0b45060403050f09012d03050c0304030519090302040c1d04050f130501180c03170301060e0d1a010b040f0e010e0a0207031e0f030e0f0a1203020702 76
    0x82055402110b806400038002103127000072554500c070b990706468250400c05190407034000f54001c0c0340d1403410f1090416440c00d26505603124540c050038210360f000011a0a00001010790f400034001c0b043d010414024840001e8000b0300303440d0204800d170881342425900c0241150f1001441e4406900301d450012a00145a48a001c0d000c8041e04c0e42400c0d00000d003407a080c0411a03800304c40c0c1e03c2440c1d007a40046003102c21801c0801c22107500410000c5504074400c080d510511254450071205120380120400400c00e9815020941ca1030303125109040d985030900140500d400d580c0a0f0f48102e9007401201e040041c1c107034079005d400c0b2508144203c903684030302e48407002d94018011007001400e48500001d152907aa40c199068030305a400c1c1c404903844045064000c0d4010420032402d111600c0c01c0e220000e0b11380301c1c4204150646a42e8412a60003c800143c121120709800010b990000c124456404c000080e8104506a00050000d60b101240f03400b02d00a015154000f540086003100525005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 866050944 1250 866049694 866049781
    0x10522080304090b1c1113060b04090c0c05070e0c120f07030e0a1709060f0c0c100e030a1205040f09020301170f07030b130b0403020129010c0b 63
    0x25a43c200080185021200400c150094140c14080030782e081c01590100141d807290034144030702c90241c0895000b4648440e80401d903605034024000e40d07400454100102809400b03120340d10030103410030600300e01341e6485440e01e82081b40503464803140141c003c1000305000c01d0480c0c580d09990300b0f10280c1420300780070100c5011410b8400307000081c1080100103c4020204400030300340d03440903014550310420703d000382d940e42121900341d61204042c8020a60751003e00014100c102050f80501000303c036040c10040b004080081c1c1804000c000160344d05103480024150300169044100c8085510421004841d140700d19007003c0b06842c4503010008200303a00341c0103507042c1c80c940c850000450400800640da0303001110f44800c801d40c0728000401c00b1a040c1c0d00070031380003d151003a00c00c0000581c0c0f40c04c10710071741c181d0f000c0b00148c0d0b440c1540350100c1c3c602e400b022103030999078540e03058048400000a004d952240030260241c2102000b1270100c1c0b280308256054403400341007803480202c8512080040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 866052194 1250 866050944 866050949
    0xb03090609011a01020a110f0301090f06050a021e16080c1f0c090b0705030906040f171c030b0409050604080702010f081012050c040504060509070e090606010522080304 74
    0x100e41c01e03c1daa503500c25501d01c41e41400c151042e03008000600031900d80b03950520190030959001841c0d501c01440d00d40b401c0c05054081c0d402401c44000300c081d2403806004441008045142c16881406492031460074251282444c81080307020079210100c0e281e0240c01c020602c000107240700c000007060303240a040803c142c64503d140d40ca4180760441c40c80444001e031400780d14070000242c00040c0900c4850160806400d82c58007c2040fa4104000040490390310f17803098000c1802e2040c141004c010004a2185011f8800c08440c06800c6c03160741001400440c8029030300d5030b002c4c580c9565140d0400d441b280e000c40d0149402c681141d01034245403c0481441d8041030040c0e00080b1144080b030140741c05a00300b580134240c6400744041d650300e411078a204000c98441e027100c050040d1344000144ea0781d18000c40b030066000f0140083d41c1d0038106c008a140907910343c00140501d218001300115040049000c81d07010200b824003503070303602d641a04c02210543d42e4441c0141d00c0c04030a00441d0420001002c0d009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 866053444 1250 866052194 866052211
    0x60e010906051e0111030712021006091b050315040504080d0b0108011a09060c1b0112090314070503190e030d080f062119060f09030c1103070b030906 66
    0x21094680080c480060f680001d01c1500101010a42245500c1100d1132a007014100d003d407410001702d5982c070640c04d41e500c80e00000581c0188010f0110a0541c41410014084084c080000f011a051021b05285105594006002d00440001c444615090079200da40d04020420800f9141c1840c20346219080700306030340162441e1183c4160325500544029040c1c07449030100320300440030406000c980d03501281d42603800090911028a403010304008d13543c2d610b4681900f0a18a141510004021580720060080740500b058100404642c014032091004070464040702c1d0b84040c14100b20340f40d0b115100000321660041c1c2610700040f503100d610040011400c030300351440d00402a6044481c003000359115801017281c1b10200d18149082922040681941070740011140e0b6541c03c094105410200918075034000c0d00b000300c0800c0303010b11030303904020b100c441d040002c5200c0d034500a0008520000040001001c0390b81b0b408940d0741009028014100000080e81e83e107004d00c1d01d00d0304e40c4c10a03100c042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 866054694 1250 866053444 866053451
    0x5010306150e040816081911120909060d0c080a0c0806011a1c23100f0b0c0705100e040b03121903060b030a050412021209010c15060e0109 61
    0x384411140700c1a80489620200200c410346484d1515140d5500c0700340001c10070407403141c090700000c0107203000d000643c0100d0745120000c0131034200070301a00541102d01c507a540140701940d407642c450906840d801c64068424041a589104c0403804000440c98007030b128030781031030000507800ca00050503c40c884c13041c10060120b0b40da804602d80d40300d50a00500c150001d0340e052410405001c1c00c090010746502c40c0c032080c40d107a003590362402240c006e1001713030754480e248840320501510b6800c24075030002c0b004071201400c2481e001128480900ba80151a0121400036104c150500c0421600c00034100080840e80320b0300101da00980040c0303091640718040c1d03041c850b91015919002c18410350301406440c0f110304e8400d0400e55661007505190303034481403642e50b0f100450a42050f80c0074600c01c8170080c400045900f85414068100c030a2410f2010456200d14130224090340d45800ba04c1a421080c00d144407070361021301e001c0c03020b41c550300616243c4524242d030004018440704070560403140c0c44038042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 866055944 1250 866054694 866054711
    0x4060f06110a0b0c070602120a1b09030f03081b0c06010918020906150c0a0f03080f28110d060e010501050708040311040204030803070c0605010b04083c0105010306 72
    0xb600d6414110018001c81440c2000403403c0a04000030143e0920481c4018501001207140c0360013128265140500d003030307070b80862801000801060310b80380051410034000c0b003441c603511480d40200c2e440008080000c80070100e4102c0851901c007104234854a002c4644030310703022103155510300092042040f128141710400024164034501035541a80240821708260b4445050101e8080c0089000b28248010408000070a07400e1010041491060f010b0305400321700743c1230081c0040006064040d90740c80744014081d0359040301e26452011101c00c10001c2d285a420070700c0c00000c1030b04400d04c1e500310400280c46420b0b80400e911142c240e8001c50049091641c840300111024040c803174008013614010001440402c440ca10001043c94006002510b010307141d5031201c007540c0058401e0340100d0751718410801004401e01401d809007215108603401c09107002c080c2940c0b5035400c8000c0c3c2c0c044001480d1005800134080c4849184031044034001940303068040380c0c0c4d00a013000d00c4207a42c06071420021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 866057194 1250 866055944 866055977
    0xf0c0a03021c140a0e0111010c21151206021201030b19050106090b09131103090105070c0201080402090a0b0a0b13330c0b15030f0c2d04060f06 63
    0x35000d5100f03160351241011180e090a851024643c5400c50500c00e2030650140e07407820074014010f0703190380c641c1d440499070350110200c814125000d5002d07406904001d04550300c0c0106403154000c4138600031ba0402c401919041400003442114100900000c82c0c1001205100030510b07401c1c000d199100c01d840744802901c0000e01110b00c01e01881000480c01a810404078035541d02406c0694401040040172000c42a080c000b103130704403088400400004000c10407840400e21990780e000381c07507003020302450b92140e00003801c440b00100024810803005011640f00c2c01d103507204182c5030700c0c0034100342401602e5006112858102c41480403005104402c0412145203148130010030a98140c425039540c031026401001a09801038194204107981040c400860102d28030139018101802492155180c40001d0508082c4600d40003801680540b0302d00b001d83d2112690000c20300c034103034003220030020820032101c02d00b03d0b0211441da11609007a030101c0c070b03807000b05130f100d040701d020380c0b50481c419040060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 866058444 1250 866057194 866057207
    0xf01030504050c061c020a0e0109141c0503090904140f070b16050f010221060108040f0b070c0506160e01020d02030307082d1b090310020f0c0a03021c 66
    0x4004040390808181d1a003a814000054035a4590400c03042050125201701401240c001359021800a614010200b000b035030415040c101a00d1a04020504001e14030007080c2c421158038414121180b0f25078404081c0202441941c08643c4000c100c0e4510b801d09082100b5680d040030b511040c24050b90441860400380000d00c04100e070040f640c0103081441a004901052072a54020f0f1b43c0d5001d40380c0f031005ca0020a100404080700041c115550341d14603006079075000e0100400c05030500002106200c0810501507508551560010303480c480f59840e00e1084901448940b0001d0580c403ca000384040a80c128142c21845c1c0842d6483c0400d5855940049a48504954003400585c02c208042450b081c400d8002c5a800041d8040d00c500110660f2285003074801c0e40f0082c0e0b0074102c001028800302e42e000d145029050303481e082d0902d0400c0c141c600003e886038121406c9041095001030342000021003807041d0340b60302a83c0010340d104440e00d07040113502ca05a03408a14039000c3c0827007200d40038038040e58 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 866059694 1250 866058444 866058451
    0x2060a0e0f060406020a0504120b010f09022a010615120f020712080403030603020d03180801051e04020f21060c0a0804120c2f03010e0c010815030a08030103020f010305 74
    0x2070062050b82c0340c41d282c0c1d00081d44400c60b09030812101f00301c0402d01c245800c000302406841680d10505941c134200b000140e141107134100ca04000c2c010440101a451003200008281051907001c04030b924039a0192401004254440c01845c9014040c1041d200e405c150715203140ea240b00004c0c020102e0004002040388210503000b404110f4101518040c6c07440b40d02280c0d801752082c2400030703084c0c2d180e8001403048081102e0403000035445461003842e282d402c5450400814100009000034144261400019a1610303040d00c0c80e5440320700000d00799542c0d180412103210002d0310020208108203120b40c442070031407429075000d00c188004110004068800c42d0362200841e940c140070398642d684c802c89020001d4a440080003400c40803400460145803000d0380c001c00c03030b4611786001d640780340309848480540d109a51184c1d2408201540d10719011070300302502c6409180c0901d0341c0d0b540326040c552480a00e0142909481441803031402c0040004c000c5050b640210b50a140b02c50815004500313a44048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 866060944 1250 866059694 866059723
    0x1303061107060b54060f030c0108010515130305010b030601121104050702030702040f020c0f06010e042a0605030a0b091003061a0607050105152e050c01090302060a0e 73
    0x40c103080490310401e840d92a10032440c2904e881c0000e418a59000c1d10802082c00c10103500300d4001e100b0789190040c5111011035055001e080d4034000c0e0400070b00b0030320052242ca4024001c0f296010301085940e0205c90b0451040321804c6a0301e034503403e180d03000f0308a02c03e80600900c40d0000101b900d1b0b0400c032261280a40c00011880c03000407403c1030001528000d4001002d521041c484800143e0f00d50003040c1602c543c2650058641c1c180300b05070b500e8045c0c251030000c0d1036080071005108640c3d04c07106160b441500080010442030442c0d110328000740e2a070784c40c0c50681806201c0410120362200055000700d0001e0300901804400e0020400c0f680380546510304001c640b148108002829504842005454000300082182031003021a910350302c2000c040312075035904d404104030840100b0411300e08110036a5a9225034040d02403101e92140070115000c00a89c0085040c01414441d0048602a0403c4002442a0800340c030b00030b940c030801907480441140c00e0041c9251442000601d4420070002d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 866062194 1250 866060944 866060989
    0x3050708130f0c030b0f040506010501050414060327030304060c0807020a0605090c0a0806010315090201090e040c150206100b0c07052b0803011a19051303061107060b 73
    0x40d6612140e075000b981c401190011a00e90000001c1607400119500c155801e8031410340fa403605192840c108034058002c54107016043c402032103944401d1003950381c41801a580d86960341c81c0c0c00e1441d1400701c80030b85030920341c4d9200c400300004400003201960103580b00b00820702c15020a1203082c1e81a04048641500580c0300c4218400424141d402c01034001d110003081c2c0d5051800000807a0010680f03421085031030b4040001081041104409001d540c10307a010304000d20a00d50f030000740503068500c81c00c0c11030740c20403010a00b4065008415001407020700c24003034140f1071003030010307440b480c1c101c0e107100e000b285640000984c5c0d014201120205a85507000d01486400d0070b04002c143c0d80c0110101d1000c0700810301d422442800c00e0603988440703005110306a1250700d8032800c2404507411409d4850b40980038070140611002c1001c4480356142181090f03511600304010131a21506d0a60015010030b0030045540c1140c0b10a0004200d0f9034015001444404441401d21031201c2e40d04002d100050342 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 866063444 1250 866062194 866062231
    0x61f050d1509060b0301050903120109020304170c03160f0308070801062703020411130b07110906030a0210090f0608090606060c16030804091a03100b03011401080d03050708 76
    0x8203a07000d1041d442c0f007410009420103c2d60b022900b100c904480050956000103400591103100c80140350040640c8a825840d51030107540702e0b101d400000000c892039441c0032aa13204007105c14002d0303e110035251100072411000300e04102220444605054010560390380100e80d485d40301304540c03416100a504e0701c0b0138034515400100c0e8501d03000e81003c0d0f6001986100440141e40e00c4c000d0789058040c51400369154400900d030060759408a44c0240100201086030100003407a04090080b40c1c841141c1240d00341c4e0710003000c40d00700b007101c1100952210282404e0510250409040d400303842004e14072400c1d01d600c4070310503103104005803502802d40e44a6400510705150200003450182403900660b070710614203454441c02e0a4968004a4401d000410306101d1410315110303410610061101040e90042420301180d280c0c4c0d920000f10b01c15030788900002c2e0190720250001804007840b0b2003e81135941e51608116240d4001080820001703040101040b0100c0c03180b860b1500880c102c0308000007000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 866064694 1250 866063444 866063483
    0x702010206060603130812100519030602390c040c090311010c02090a0b03280201030f1506030b03061e01060e0a030b2d070912020402070203061f050d 66
    0x800042c201c840c0100ca00210394000781b18600500410405110119a5400c1809150b2642c41c4141c203e039001e0400503441000c0281461050011030342c1044006075500903d185c00c840e03c45488240711214070300b60394071000701d5031038598400c6190b00c180291902e90010000700019500b42240750800a180c2840a00202e00308000714402c038003050510810801055020030b00c5e4080454800c510036a0b15080515282003d1200a9180d807003040d04200c94400e08000803480c1d95151000707410507594642c1007456106641c41000081c041d04410190035565507401000780418a054500a0003004080b40d039524541c403c810300c01500107980640c51303007080c808176030200a4880301340c1d0041580c1800800324003000b0103103001303144d0340109290f0038012008401c40e00e0103007040c1e0324402e2204010490601c1e4019400400c1c2e80302d00c1c81503d4206001c0c00014041c1c059900c01030b6060042c90244410400d00361585402e10402282481d045951030080148101c0702c61800341104004240404158 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 866065944 1250 866064694 866064697
    0x7020709092015042c100f0803070818040b0616031803020a0e0411040203040308010314161a0705030d0b0a0b090105040b03090f010c1110020412111f2307020102060606 74
    0xf0501c0c503080c61105c050f451040701000303801795030805810031004424480d010f540380c20200600348580040d460006980d65000082c85003065440d071580800c0b050f9206507903260001600c1c00c2c0010000e58503030500400d00620007000003000c501107150300e200c21500d484080241d0040342c5e0020069101580307000000ca0392058002d1044500300d20003604045180c0e1503102442c0a203000c0c0d5542d24542d8194034064810070b4940f13141304080d91182a06040400d0741c0741c1114144d0b517003088800c0c4c0800b070480710111180592100101a0b00011445007001046903000e181c4130300c02120500f2110f81d82c4d004290a0b03120312810a80061800c00c030a000203a0b032880259040b000341002c50b0300318041c800d441804c49020900d10000142000e5141d4a001e13030030801000c01c142220000c46c501f91604207441050001c0c441c00400728013018200420340da03207402d9000c08075050f000c4120146224104c0041c8454031080044820800f50750742c40d10021054425584403030f5061b0010078403510340c1002c01046 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 866067194 1250 866065944 866065979
    0x140d0507090e090105040c050d0506061908071403070501110a0f1112250e061207080f010e190510050a020c0d020609150c030a050702070909201504 65
    0x41c01106140050000c108140e03961084008000010391401c06141039090b00c0c0c0c840e44038a03c1902040780c031102144010622a030881c00c12030b81d1f041c0c06806480c01e0203245c0030b07950203213049000c1d00100060032550030300d10f404c0c0c254048060b43c180c5a1544010b40c0c5583e80c03015a1042a4051009c0c00000340140c400c0000940c0600014441c1d1054280084d41c0304042094810300d603001821015481c0340d448402c40340721000400041805030800400883e0131400901030f503c26500762091051041007030025101800070007080d03c048000c0100e10901901485081e11801d2041007010382c031004400d0f04d044400c640c864054440580340307510b41c0c4040c04028000d00107440d420007015207130342001c100003c0202084d4002e801d6605d0b0404203a414070307c4101c0741c0350003403400344200001d0090300030440b680701e0364101000440303884400d400c034500301d415000f54100c0c80c6006810810700c81c08000910528101c20402c0d5001d107000340510054401000301c0140d1148181b009028a440c004d210920 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 866068444 1250 866067194 866067197
    0x6030f07080601020c1c0201080f09100506060d150e130309060e0a08010f06030201110f060c070804150c0b1f120302010b0d0c1707080d050702030c030a080a030c140d0507 75
    0x740345d131120006452030300200c2c01801c0081c042c1c2c840d40855810025059000281c0107590019140880709036032034440c031558001110342c4d168000b17282030f600c0e90b0a403100205851410800061224a0388070800312a005032000194250002000c030381c00740321400caa030356150b0b4030030070010301c0c00000303840160300c2d81d2140d03a12526608011640c20001d00c10751386c1c0aa5140c0c00030820a2840c00050103501c100082c000007600a546418041800043c00380c4d0060741c0030782030b0395031201d10f410000c281d40269080018000e596030311040302c1542c030070314121216005010342c0792203458040c400b42401ca40e4a4440c10340001070a01040003045020340216110b00900001c034848143d06d002070315040074220125803002802000f4001182c004c1c1c1d01140e40000d41001344100750801c20400d40d00c1200400c03860030402d00041a0007151401d0007402e0384c0103005012503041300c41500e0601e51941200e21008002407800e4058490750b4031851504a080250305c1101345401c004c0300d40390740500ba00030900300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 866069694 1250 866068444 866068453
    0x506060d0c0929221229060102060118060305060a05010303090b04081b121b03190f06020a020f03030420040203070e040e0c06070b0a060506030f0708060102 69
    0x40c00d1110300860211140a42c0c81d500a18140312140028503003032103020b21000070980c000e40581003903070116440840021104884190701d11500c40440b1400d403c04000620a408110304010443c031030b074080319003540d001c1d400e101400051000f01039400c0b11100d0059000400400c203020380c0e02042c080e0000c0485021620941307a480c1c40e0b01d009011340d8440c2d280395139003004100f4540c0c4144180701401c1e03c00e0005141a00c0c0010080d601c803d8110100d1002c412100e1101555a6103441071405003091020750b0385410901c1030031200204290301a40c082e02444440c0794940443e5103d90069070b6011240d0170064400307484200c000d400121001c0d0940c40341c0c0d003040b000c114040001d180f00301d11503402c4240c1ca03c0000d03a881c01021948919500aa0050040c0700007660006900d181d0402d041d1000140444649921490050900f079520740141c00000c80c1010301084007401446400015014843d40c0e65800c2409000c0c031084544290200c2038a003c0789600303106070801504500c0510465 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 866070944 1250 866069694 866069707
    0x110d08061302040311030d080c040e06190e1905010b0412140a0c091401051e18151f02190507051f020607110c01140720091f030303050606 61
    0x724100c0c0d0140c1c0007641c10354095482201c8070314040060488154482c034201c0c2060400740821005400740d405401c0c920b080c0c800010390079440300b0400c1800009080f103c07540300c0c4c2c0e59101d800304201d4250794800034001d5140403000041424010030b4120b031402c10070300385050714200010030240c0c0c00f010101c03064981080221405901004031011440c0a001c1c01d200040c9451112411200b070198200540c42032440101710071b507500740159001ca485005051501e4001c00001554000d601107040c601d00203040c2071016890104241d40d4a2110540c0d85003c030105401c00c19036902e1040803000016404049a000414968000300c45a14814000c0300c1302c0c9a200c2000030850301c1d00791941994400789105841d01070f40e04201c087c1c2c11220b14104a401c0c0d00c0d40e00c42d16030302c40355580d022605000680c0072201c405504c02013101c0c4240d81000d28018055008400a24220302c200c280c81d105090718404141d07401c0c490030303072301c0072180f000680022014076580d805d60103484018040b5a2003403050215 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 866072194 1250 866070944 866070979
    0x3080c0c0414010b220303020618010903300507022409070605160b190c260c0d0f0615140d051302030f10060b040b1b0c060403050607020d110d0806 65
    0x3205c026522a0b006000306e4900b100d43e4002c100303406071220030075a0601085001094100c0e51302c94150021581b202541071864460f0800144511a5900d0603840c0408110040b6070100301080d1a01d101c00c240040441e105659444401040d1180302064100200401c0b209001d03070010703c08036004ea490b1920210305074465600c1c0341c0e022216212880032104050040c0c0c0e00078404c996401c003480c14007a0100010700b07017814160b2990110744501e040e110020a070501d00160984031a107505080c1804240b124000b040060300340380c0b00f4074054071184126050054083d903001d01405d611103124900301490350798032101400c0d015229550100a0400e038102584081c0020b420308031000c0d00904d041c1c540329441104882c00da40c0f1000c200402404184080700c503181c00c4400000e16640141854803018800702d082c07402a1000c540d025200141c00800c2100100d14144505015004c1e02e400d00c103005000c1d030300186014040d207010303004821a0b4441e10b0084803625000140070f0a040c1d0b02c11840f0b006d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 866073444 1250 866072194 866072257
    0x100201091203150b07120c060e0a03020a0c0603060605161109070804020a050405090a060f14011518270f2405060a17040305120103080c0c0414010b 65
    0x801c00c00090b1104607951a034500f41c034500000f4034202540524107000c940311444c0d180c01860110301003001080c140030501078941c0140310780003181c4080c0d0710215103d107400b03135031500c0c041c030202d48043c041d4600142c003e010344562401c40c2c9480e1180c03072402e10b80320401c1c60548080d03c0c2c00c90300709009249522650b21282800e511600316a02d440d0f049041c036004004030080b4540c0f2252140c0d0809080265041c004950005042e03031181001c00c00c401140c884d60081c10840c1610f6200305050400010f0907465154003202c0095140c0342c8407c0d0f201c400b0070043c04541d80c0d0180000140300180580d46410843e41044001d14140c00d000030300ca4280c144450a0390707200d80030509a000c030513800700a49800d400c662802010111489460007124400103803215a0407011980c596900390001028035008000300e4000e00e071303411845002d0f0b68591404038000d402200c4a60042d02c99071540b11900c1c189403040014281d8420b609442d00d070b207800c0f440240d582c4401d4641d14590306030594054884e15420303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 866074694 1250 866073444 866073473
    0x2060601121e06051c05031c0b030307030503060909150610120501080d1101140c21040c2103080c0a0504080708030405150f090418080c01050405060601030204030c0510020109 77
    0xd4000c83d900d8a410208004400410b480c0c5800711424940f0a0018030004126502d80e04422100200b64035500003103001044035003c410b400d4000050401d08060b401801180308203400c07a0f20041e41e4891410a03a6102c15401c41d007041c2804a1004c1503a130314240700c04002d501400c5c50704504a4140d81c40c00d030140c45081c2c0c0400b0060340002c00500005410104010b0103880d500c008004010030300148400703080d006481c3c41b1640c200040c0441111141d49140c10741248120100002401c00345403007034924401c0d2049091401c070f0b8004031801600e1501070b03002ca8a8040e031300d80361161aa044d40042c9a0b00c11001d60041c01010840041e0070f0506001c40b0000700441009551500d10b040107100e90b4504240d0000c5101030104006070b09402c041c025141302c4281030750001540b200266030700300110490117028290f00c00200c1c2d1003400c48015000248110f203d031042d00c0c03040c1c44440054080e40580d02000303084451003241030107541040c034811515000244004036191035580c80b030b21484500341 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 866075944 1250 866074694 866074751
    0x10f030b0f090c3010230a0f020c03070c090609060b2208070f141909090615030b090129041e0504200d02010504030602031003080307030915050105010206060112 71
    0x600910305d00403801e2007613034221091300e20489000120600013140742c800042502021030303507503044001101c0459050307801001d82c2108499551115040006103c52948140d284503402c01c0800725080045000343c01c115042e00c4000f604084441030601c0c04501c4c003821554100900d22030010301c10700c007040040c00501c8814100148036081c0110501c44002c0400c680b40210400442041c1c0b0307840d01c5c1c0c10102280d07105030000034007206a142004c00343c24a440011000c600d014804010b0100d60304005007e1010040204030000400b10384a0b004998807500303d40304840c00710b000b4030798106a0400e800507000d595a0000503c80c08071004101d541c2581d0556800000000035040307a0b0320210b44403207111040301c0d100135400301a40020218455030000820998010000c10f21240c01c00c034442010b140d100602c00e407280f03010800240100442481034840305410744c814140303005c1342c0c40b8003410b0b1030060303000c0e00088e40c607080159401e000000d0894049560b4074154040088105401581e04c42d19 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 866077194 1250 866075944 866075953
    0x507110901090f0b0f01051b100203070e040f0501030b0114060d02181203031003060c0c150506131505010305040f06090308070e0103051014010504080303010f030b0f090c30 76
    0x50043d1048034000c02e80c0c54010401e0184107062a0307008030a8445620204045644a0740420f900e207007400281d00d101d402190020040c0140359402018803241d00d2000e4404014007003420343c44006842c03003840007805030708101006001c8110201c1100840031000750a03240307450031501140040780e00030310000c0d4421003622500022440c00110311120617125800440c2942011140f1490b04c06185c84000c0c1155940c0c0300e0b041e0424006e02d0116201ca03040242011085070044000d80a840c045070f885102e003101c08a174800c1600345104041030a818403041d40c810301d003484015001481d001c2c0c030a4510304980c0304c102c80040d180303026034907126200b40d89040c900d0800c0c100190604041200c0a814903040008000c0f016109000c1d64048070080c1c3c03200c500d510700321801a2140c1c8203035000b80d0303543e010000010581030700d4003503c1400c4a00c66000c899050341c80c000c1254040400740d40c080c200e45c000300a00c3c00d0764a05007212003d210072181c81c0049543c181e00b40e281c40060f0114205c4402d401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 866078444 1250 866077194 866077211
    0xa0c0c0b0304061523010e120f16080a020d0c051203070203010b100c110a12060605030d03020a020304230a080d080a02041d0405030c070f030c0503030a0807050711090109 75
    0x103400b410740f440390039000784c5400c54144680c4600780070005501c02d0189482ca403c4000340d030311a000c060741001c2c2c05003020b00a060180c0140e5118415880046c03164070a07161406c494800c04032158040712a004060100c00c030095080016095110006440c44440d107203000c5211741e502c2c01050300d0184d03d00000e580d070342d4151040c5401d580e804650a413090903911412480981c00131002c00742a903020318800803400050000030780180080d00410082040c0c0041401004000c1d80050140ea40840480e0605001148100d06034495400003000503081400104900300781030583c3c00d1a0307980035a40d01c0b41e0080d1800400e80d004199480042640d2250414035180394201c1441071700084030403005d41c6007070706144080130b00340a122000712050000d000000c081c40700501c00d5901c400c90a40a507600a5036500c29058242c16900043d1220360b14040e00003150300e8000111103900f943c80c0c03150112940c4440041d03034650480401035071003040d414040402c6070380360810f4501a0195070000100c2e4507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 866079694 1250 866078444 866078453
    0x1908130f06030528090203150a0903021b06040e330f010816110a060c030603030807030608071802070204050901021804020403020609092a070311061005060a0c0c0b0304 74
    0x100f01401d01c07040b840c0300d601382003a4401403201c901a0400780850100380e000291010031725124020074294544202042407000a4081c0d400c00c1c1d0720180a5402c03600e8059010241d0b40807031a52419003580500100420021000c110240742d5000d203003242d4100e0303041220a003e0f440400d43c4801e884030108828ac520102d4504032403013501001d02880c00706642d03c1c0003074000c102c44603440f20590900c0543e03a02c00c48101010021050950f500803401e000340250348002802501030313400118042413501d0001001684244a1301089401c1c00000304070b940d16001404d0345a64420810f01004c135000c012950150300c1d02d010300da002e2110b0400040ea1030304e007040c02c1100140c5641403070b84600e00410003040980d90714030030703a40386030012980e4103455282c81c000030340080b094880103d81c078080c8822103110050020050403c41d80282c983c0568400c0a40815440d00c0c400c03545240c1c04e140c1d9181c144281c5c00c0c201c000e40444000b40c142822402c8080c0c07140704c00b82a0341d81c0003000e28a00003041000f0070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 866080944 1250 866079694 866079701
    0xa05060f0708070e0f0112150f0e07021b040b011101140105120a0c0e06060405030604080a02060708160f050f0c0a0c09020c06041103011104060e010806121908130f0603 74
    0x60b150389040d1a5142444c0300182c00784000d920f160381001038189410307003a12141d81c005026803124030080d00c8115070307c0c0c20780340c0c4001042c411413003288400000100202c0c004226582c42c42c6000760100c1240340a0720800005001094851b41007000d01c512a042c0e280003481580e00420b4810b080b07458a614180070010078003a4071946805d95008054224001010300382203400360b03140551284407030355540c40403600c2401103900c0150305200b560140014008040c0040010340e03115425070b00c4170781e40d010301030301c200e0f2050350503e013000542c000c420240382c0f02c1c0050081c05483c40c039240b842c0206c2d00080381016088a03648121070380000300c0300300070412041c0740c4000604e0790b60800c0d4281030f81150b50700e4807803400500c05044004031030050501641d007035101f44181c1c42100c2c1055111901c45100034100b280308001680400d05100c0030440624291200e0900c1402c1d6100514030360103c8181c400710703a800c8650403070742860280b000a40010140c0304040281c040111040100751401c3c0006041c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 866082194 1250 866080944 866080951
    0x61b1e0a26070305090301021603050715050c0403020603060f06041e090501080705010f1101092d170706020c0609030a0207061805041802040507230c030d0507020a05060f0708 77
    0x803207920951070a5001c5100582c0c04054250900b2034840d01042c0c08280a8402d00464100c0e0345000d0948030100354100700502030b4140030f02d24007205800e01e900b0300c0c0300700c0e202503c50341c5034924140000c10040c80d00400440d031044000c0e1410703140d40c8200000c00c6076900701d904080d0b01d06d06040d00746070f000c18402407014000d0041e2001440507500d0098841c2d00d8072610f0041c123042004600f92140014000c0c4440292034507400000c000500680c1004c5060740881c4650020b0303003214480500322401c01001d51a00e00d03410601d04002c2d000000004000d40d80090b50468609400340042d8400d08414882103100744c910701c010750ba1342c07408884000c0c240b00090b005401030100d42c84080d02840c03007244c2c1310030680d01c01f5640050803610142010080c2c0804800c000d52040c1043d040010032070303007c4040d940811000b04070704014204913061001d140508842d901d0240e2040c4020502c201e2141c000f1600002d90303005440c01440326484560a1240c21103c20681055400a001d1400c1d03000900651 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 866083444 1250 866082194 866082233
    0x1503021317010f110d090201050c070e060103050c0909070e010c0b040f031106130f0215130503120a02060402090c120406050f0f060105030402040905031620030309061b1e0a 76
    0x84d09648581c80180d010704408014020b0b9100856030031a4081e20448400c85000012281a59903808580c0d02d1040c1c11502c46000074208808164030210308802d8440032900140b9202d0079030340b001400c44030350b90181049410001d08490400114518913102400355025419005131115a414054164941c0341800340907a880302040201c0e20140511503004207038440c0d21f0040034020f50000402039030051088054908002a00d034812242c458109801c58600b40c0a4800981c0064050101d40c050744a0000c0940c010900240041c0703019020746a1000d01211014202642c24180c4000040704aa0450b071550b81d40043c01114503c00f00d245601c02e203046220107040c0362001c0020164080600024020f58a80080004005042c42a40d03020200e9011030b0b8407801203418031481400c18081d603418071b5203940308020054180482100d43c0340001402039480c0440d80c9001c4940c40c0109d030784494680c020081c5110407600c04003100c52074482c1c05070007040300390102d00348540c2a44241a0005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 866084694 1250 866083444 866083451
    0x1b11030c06040e0c0a20010b19060f050c03040801230a06030c0608090c0415061101050c0f1308070f0e06040c0f1209081603020f0109020a1503021317010f 68
    0x2101c020380e121080d500208a111355500c0707000c826820b46042c50051140c11602c0040403400c010b003941548000c8294100711084803000503004009403460f002030090900140d4600c00068400e030090700102004011042124941691035410074215180c180703000109003103081c906031101c1d039480780b401d0b00710b0980e44040140e10315603a01c2100b034179800c2c0300c3e0105200d6407a001031300d064800e0140361156103018000307000c80f030898190701c6403040e010b00811010809042e8003580d45081442035900c40e00380301c40381d20b1602d000e0010240c0240c1004059420250703103180d0114607004207110f0700c030003006000402c4410906001520b240e454009002600403858039181001a070361004440403c2400f9003040039000d502c001050001e80302d1844054074000e800542c044207490761081141029020b542900c0e1050b076500031081c00d0b02c0c04590040d60200ea4a44288429030481d8105040d001c2a41401440d1002c4012000e141003080d500850303002c000c5040300f02401c0f00a005449460300101400c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 866085944 1250 866084694 866084699
    0x5010516090f15050d0e030405030d0e0f01080907030503041421061801020717030906130f034a030c0a0e0402010c080d06030215281b11030c0604 64
    0x21401d6218401c2e0500110f1140e94031020314012811620030300c0d0141014003c1110706181c0c0d9640740d00c1072041034080d21a107000030402c03620490408940c000f000346800c48400001c0f00441d100c1d040a041c02c01240100c20f070000020f141000100700501398800c0c140303584441c0c907040181c00b0811003080105150307400b4154040c3c050114800340d00082c1300c01c822071101ca00501c42030081c00390070b000600d082c050b25050a025160300001e50700c11040d4200f2600c0555500724802c0354011211401008403002001080009000f10324050444060a112828501c140000014402c012f82141e0345280c10100e58044c24907400522040100c40640041c9520400c0340f010540740311441c0324600d030b40c00f01c40c00402d086a10031020280c3d01a048020140c4a0801000080003050310b80710891042d440c3c004a03420040210060300c85000411260103400c1a44140003030580220480d01d0f0208142e0f0111015607007030044a8100c03003806000b002643e1052981030615194802d210f03144507000c00c0c4000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 866087194 1250 866085944 866085959
    0xa15080d09061d0409050705030d0801171f1a100c0b0c0301121e0b1f0509070503041506080f030414040204032604030c1202130504110d0503040b070501051609 70
    0x20204080f074280c0300003c82d68003600302281064400d401c1942d16020340040c14401d280c0c0990b5140c144e5079802d41c9200307030280c5e0388032040d41c83e100b0540414800c501d5441e400545c0071198852556011035000307000c804903409002510b00440c408060340031803100e00c0000280300d514480c4991002003019260700e194100034110900c2c80c0310110060201d00ba00c003555080c15a0130400060301d42d40002e0540041c104400089101403502450a00c0540b0a000008041c0f40c0303044014020003d61b120640b9540340e80c1c80b46a50015141080075025489040020380c940c010821420074545d1500903503243ca0400240095440400c80e14074071490050005002040c0416141e5102a072582d90300c18001c041b4000c01e08440c00390f5400541441c4408100198500d060804a20746900c00c850803c800c506555040e400c41e10160f5003e8825a441e80c5101100c0c00c0140c80444042d000d00b08480c00e01d50740f15101d80d9070b90b0040c1d901712903e9442c3e00601c000440c00d47d12800c1023200900300080d145060850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 866088444 1250 866087194 866087237
    0x30106110105040c0b0c0a0503040b04051002070506071e0f08030a060806040206091908030c070f0504020a120b0111030c01150b070b07121e140705210a15080d0906 72
    0x1e905c0d17032040008407603052840c00c120b0407003400d6004040e6074880b5921004080143c0180c410740d8003c8054500504406e407002c40d50704152200186607030305181c3c0503140c5140421a444a07001c00e81d9041c4550008180110309000c42607100c0d03840c00d80d69282402c41c00f0f05441c1c0d80d6010410580c404400c1c40010b036900800d0311801c007415100b4404a550b4843c0002c15440b0341c5e400601d0310300000500c0514040c002c14000e0644803003021440d08107681d1000d003c00c07449140540e00001d444031760450321401403500402203040c01494940c044800c4102d000c0d0031644010320700440c40c0c0d074828100b4465030900000f1801482e01c1e0401c1418110140c82d1a221348400800003800c115450040da4050b110b02c1e03200070500c0d40702242c1c4030407410f44105800c004000c03d50050752074054080000b42180d00c21411219a80b0b14110958190707030801c42080d20611010f003400c02c226813200420414002c4d01322200004100041c000c0002c1d1266001c05000a0025044441040030040501564030102403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 866089694 1250 866088444 866088449
    0x17100915170f0304180209090103050d020d0509060a030c110304060309120207060f0e0d0b09030c0114060112051308071203050f0606030114131e050a0b1f0c020a0b030106110105040c 80
    0x40c1998500205e1a0810028400c0f0344200b035000b04042d0022040c408002410907101c511602100e0b050540c10500740e03028020704c0d14540c0e1040040120504451280e04004686c0c02c00c0c1c100f0140000d011094103003190850b0300520700180c4d4805012007071050038603124074021624005005d0b0141003401c0204a001e403183d004052001583c110f00494a6031301c1d030781c1c003101c1d04283c02071850b0400550960b00c9500c0521012165801d11204441c0c503002e02c00c0040c01054161103121400094140301c0d03000d080004e1050740340b01d0310751340703a240454881001451000e00c80d42182e4000400b0840c041d08403800504030384040c1130540b00b01b2405072906422a810342e00c0d002165030b262106503000074621103000003c1c100c83d03403c2ca50411010b00c01c1c0c090480c00264032100034000d40d41d6020301d8104459003d50442d5205488880442010070400101064101d951030041c4044405801040608401e6808640780200003c01013007260340c84a00c141a052050009021604050300c0340082d00c2c4850 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 866090944 1250 866089694 866089709
    0x906050304050a0b01062d0504060f030b040501030c030c0b0901120f0e0f1b0609030a0803091c080a0f0506090406024f030317100915170f0304 63
    0xc0403406001007084001c40041c2e1080c4180c0d0250384401c030042c1660190a42c9007a492042c40702c0c501010300302040003000912540e00c180c102882d000b02211488011040f00050550705d0880300741d02d03100c500426000e0340c02917040c285003500e0b500d007440f0800d50340d074426a601c66040c80780328140c2ea40031440c0d11015011034808139400d014003100400408000e0b11025451140ca00488a000750104110244103070123041440e0108001023441142d203c2e2030b0f20186e26030000c0d201c0d10300045000019540140030101100e50034400c41d0b002d002400052040c80010a10b40740401403405c01034014600040345406d000d000c41d00302000403926040c0c0c042e100400c066000f0422900b03d15020006020f1200a4100102da8100b0007150300e003554000d04c22070310002c00b480c0c03107440c84040340344c00b50040725850364640405014804401f01000c901504100c122404400001150902c07400381074100d00c000d00007170050358034140f802001000c400c0307040c407010b402c1070380800b0251402206590444064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 866092194 1250 866090944 866090947
    0x60108030717040e070e130e0616020c0d0b0108100b030d121104030f0c080a023f150a1b12061502060f060301020304112202030106030b0a0f06090605 66
    0x50b818000340c070302550b04540d80e010300102c200130301c0c154054001e050340c5d1310a45071075401c2e2943c01808000d403840c084a020843d4041000309041500d83c1c014908017020341d20540320700c00c40c4180044c0e240440c000c01074071150707001c07401404018403e00841ca44c40900c036508101c400800b4000c261a054007202140904c9222500710091988030b4024689160124038500d079070755100c1c80e01d15903600c1e52250079202281758a0b03000c41c2c142d80002c0d41c015485c1d00108055821400030740304031800191345508000241c404410448200201c2c4401444109800007424200d4041021113a200384010840300f401c1c1d0078103580070205014600c0116004546140414002581c0b2554101801c002d5015200200c1d541f00740c00303c0320354040341090141c03101340840300880d1601c0b0109401c0c0d000a40b405002014084801d004510701000040f003407051907882d45000c805c0b006d103950100d800980c444008291224019089442d0564810010381500c100a400079030a00070004d145042500808091000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 866093444 1250 866092194 866092223
    0x60a0311010503190e3f0309030d050c0304062d0b03010e10060303170108030a080a14071110020f09040506030709110a09120f021908070b1b0601080307 67
    0xa060308503005801c1110000c0c0041e10b9014000d599584210000c1c40c846d000140c00c02032003c3c030102e02401c1c01d0080125001846400080c0c1042c0f5510160240c20544410041c0118180140c09060f11460110007540e8031303880c0138240718041d542c0c0c1c0c3e61102d5007940540ea02100c842425000c6d00000600710304001190a000000300e0700600e5403080341c0003180310380c068896100d00d079900003405680c0319940c1c16107071411210003080355070030a025041c031036041888000c042511920032950f102e00310080101d1510780d404501540301d00b0998035a00081e1508044410f01c1404200101ca03c4015030003c514085044036102654042c00d02070520032030326000882c0d81c6580401c2400084d2562081c10007079070f02e40144103100740e4000010400804d140f1640080e050900c00c03c2c0500450304440e0b0580340040c01c0e8208144090001300440d032082c02c1c15400700b00d250081014401031b002d8241940e541e900c00014459201006240652580c2c3c0302600512040c0b40200555140c2a40140085240703030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 866094694 1250 866093444 866093461
    0x3060406051816090c020304150c06111c050105010c150b03120a0f030c0f0e04090206160606030212030a230714100f1803110a1217060a0311010503 65
    0x10042c095280d554071510040401c0e20a95100c1202103c6003281d08106070080680141d80741d02441c440d803d104404681d5000341640210030002655120710400a02030021b41101d142d160400805120018031003d8690150000d030301c91103015000900703005c4180c213940e9940b0401c550900259112185d01d03a500100c068804009250210111610740f0b5200c0802d100d0051404a0041482e00080d0414000c281001e005c0c0040901c1c100356903603965400c18000061002516603044205d805c03050030003425110f1150500001c1c070380f600c00d48012800524500420180080c01c11000030190003c00c40300702d25076002400f0100210000041600e9580800410907881c010000003030701d031010f041c4007a10181c00120344211000102001000502400c2e9030a00469815044040b00300c23420801c0107000c2401514140c0450400c20111040344615544254000d54504186000308040d400c4055001142135401079001800b550410112441c43d103035451405015103105040c0440003000c601080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 866095944 1250 866094694 866094721
    0x218040f1503020d020f1c0c1a0f1303060c053013050f07030f0b100308090f060c0a060510090506010f03020a0521090d18031106071709040501080303060306040605 72
    0x6c1d8401030040040c1084601d11026889000900701c07441d281103000031800e441c1c103c0d8082004001c0c405071a040c0740c0614460103140d409211a5103085156801c0000040e13028010440d50a0a5546450f1222000d2103070981c040440250503010b8440159924901524115040e610000d510020398035010b4609009061013600880c101050040b04008030030310035500c94415076a88104812042c0d5600c48081c2900260540401800c82c0381c00c210400c00d51508004a42d40400c00402092a19580014803840c0c85d1a0324000c850300742e2550304112912503401450b1006000a20b014403240c640301c00020b0981b10790981a105150703010910100c500e10400a9800108484c018401c0303181d1081b100710710b4980f0455110364944507441c5000501c40c46031928840788038202c0c07042e595a41c2180d540c40401c00a40541c030b40c0089041c00307000082402c0500803504081c1100c0301c641d1703400c0e22009020a0780e10582004009910400034881c16031400503c0d1075000ea00800001020307140c8a90b00ea501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 866097194 1250 866095944 866095969
    0xf03020f010f2c01110312070806120a05010e0c12030d1e020309070302030c06070201020a0b180d0503060315070f0e06091e031c081807090218040f1503020d02 70
    0x1500d100c1004030703c8224080100302050200f602ca61020003400d51109941c1d03c00d13001d0120046503c0400f049441d80a014280e401500080c10058840d102c01c926500d00700b10054183d030660b4440070303c001649414015075034030709001da480c5200c05a0078101e4541d07074800d801c00318910fa552480007802800c0c0e418403022103142c02070b80a554034200b0f0008a075a903c500d00041e071081c001c2961502c01407915130111050268184c0151803c030100d03440304c0a0003400244001040d94104000c140300790428003107608004015250291a41031200615240001c040000c0007980300b01818803945640000f0500d10b9803040d49008284070083c0780108909000700e512040d085007040381c0440758107042d41c0110241c2b0780290111021141904403c0d5081ea442e040c05030046000c0301e006c60181105121000302804401044440329a85c54400408a80c00448200420ba20302c0112244514081c0a98010b0008503034080c01003101c0000804507000e028403000388200c0651100504644420504604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 866098444 1250 866097194 866097227
    0x40b01020c040e3307231603120e190203033001060201050717070903080a021e0615060c0f0a0b09010c210209010201110304030e100c03020a02090a140a02130f03020f010f 75
    0xc48a00303c070407d5100a0fa421002ca02241c414204031440310000d100350380c03000c0e0340e4200030609030b04c1c406a0040b9003404004103903018081080349240e2740c0e200b07074001c00300b444a5a560720390640d94040709219204043e04901c0031641000b050024083c0d200d056000026056203180000303403542102139545407020382c00108040c001040c00c040c55034002c01c0c0711490704480580f4a000b580c1111006032a00d208a40324001801410800e0003e0b00780354014080e050303800c900310b8481d8001e480c1c0d11464100481c004480601c0c6040030889810704c207000c0c9001905150030030740240075000b1420030003554503102a24003036602143c1004107038802d40007100800099052540c3c0e0342000c0c20000d0081103407281041c000ca50418606e0082032084e06403251203509903000e480ca0400503420070038841809002054100d0300c1d80182201030b12241c6016014003070800c80146d4500c2464201056405542c1c041c50f07059911420810250700c03503040402006109203040c044c001e103c0b0005031290a00881400da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 866099694 1250 866098444 866098447
    0x3030103120c0506040605091213031209030c0b07170901081603060f150e0108040c090218120c012303040b0c040b0f070312020a0e040b01020c040e330723 68
    0x100303100c1b166002c90b00480b04601034035084000e01103000080c0c4103862106144020300407042002c42c01c2804074800e000140d20b4040c044964a17180c4901049054004422350000000c0e00010001c003031558510320840b01409908015140c4000303004600000d14013080e0f00c030661071401c0a103102c1d03440708000d04404028443c0e055118161130041c40c440705001c5010880400c01445070b503010300452440703160b00c6241c80c1341040c10303d550365001e50070400203103802180c0f904140030595505240724402e039a1003c01003030803041a0b000100789540c000c18560000c11088034042d644401c080c01c0f2a842a00008060015156100c54060520541e4402100c440000c126030030300c040c0032401000b9940c002c0d610800e04540781e4141c40103e2040048810210780c05030b04070803950510740c200c0003031641c0c140107407022203401c2d201007016210b0032440030413160006041685440780f034180c00c19034960b0711700d5018041030030183c13103445241c1d001e4840b006000c5070043c200b0301e0401400c0300e1520540f1456515 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 866100944 1250 866099694 866099701
    0xb040e03071b0902040f1206021306080421020322050d0305120f160c061e061a040302060304081b030409020c06090d020d030e01181103070b090303030103120c0506 72
    0x890025505030003040361030b41a498000741c2c03d0804c0c001e90b03094032255003200b106c20349490705c801e502c0c0c050640221220740c0c0074400308803074682422056004104a40350304040d4902494402c01e805140c20b6020090742100712801c00583d030000c02e0b102d18070200086012000c0b0451a03441c1c508445a01403070303201c034002e60f80c0d0702015489009031081e03103088900c1104c5602c503c81805e105050444610744040c019094541a5034400d030b05c5924214010b100003c0c41c0c3c070b4603100f0b502c00000c0110390002e4158540601b0442030124060901d0460303501c4864134103050850740014980d00c0045c001804030600482e641e080c80c006c03495161140d55100c0100c039034482d6031700c03441c0c80a074100c1c40e4140e02c00d026000006010b00e4003c24510901500390340909080c20925006138018449110851503940d039400010302039059141400001a025030112a00c0d88013481c205860700e48640c0012449000c01c2c03101420390344001090340e0545c0d40c00140715101500306076080b0350007810300c180035049204000c10b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 866102194 1250 866100944 866100953
    0x60f010c0209340206040209070c1a060f0301060e01060503090f060a0f241a04270c0c0f020607030c12080a05070e180903090a0f1d01080c040b040e0307 67
    0x1c0c1075840c00c0038071070000300d0100000080c0480008042c03c001da005000082c00602e81520129848525801d003015511441d847d100d1742c02c8400c407000d155510218051001c14030785822060140c180c100d00a000590038940005004079041c4580300903c01d010000c2a0b010000344980076184180030110b68592404110b007801404c0041020700856203054490341424070f80303110364101c0c55003a9058000c00d92401040442c4041d548001c0d44002038103000c086088010104c014218107050140c900c00060520103600444070901001c0d1f082c0012040b403000098034130041b08140540464102d41c80e5212401c0a03034010005a2008100e00d0b02d00c02c42d112004d400130134090061002e901c00b04000d03550604160303807000620381220390100051004406450304030548580c0810300c1c1056a0070207070042c000c45c012800507003005021500440d81030005480d03a4400c00c14243c1100781420b034651420621030b8840e05043d2106003d16160464a065074030740340c03c910035550354107003141e60314000c5081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 866103444 1250 866102194 866102221
    0x60308040b0c0718060918120c020316081c171503070f031407050901080c091503030415021516030c0c0c0b040501090e0c090d0f051b011b0803060f010c0209 69
    0x15000c0311900c3e11440303203110000b00000c180e00b48d0340051b90000d9644148030955081e031840600300d915102708418502500d0342c0000302801440604010000307407070688c40f005c1c2c0482e0007081c014100a84420048606460f520290390089101c500404161654002086c00c000352030704201d1440e2140d49001040000c05010b04a05840c140151010140c6510230403078040d5081c41107804950004401c0c0300c0c145407007412507821070440d512181e0b20100c031601003820f580156101c01103001000e0050300c41c058040c000d0003408400300c00c0086403450142403602c10043e240040c84101940d40d034a46c0324803805802058a9250445401c83c0401d943e40401d001581c0503000d45400a180c2c0d0500150750195000c29a01440c54101c6084c241640a000d01840380700004007580c20015000d000404503509002c4402034600c80d0061070309641d0010005460106007508110604584005103000300380c034202aa40c10140844a5400201011004071004143c1280296110620506100e1340c841541e0303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 866104694 1250 866103444 866103449
    0x106050903190c0b0c0a02030f0c12071512020c160518011d09030d0e010b0111030c0a110301060b120603072c0613020703180801060308040b0c071806 66
    0x4040b1050310660405002030200000801000100e0401040c400300600401518001c1400c404442420326690006450003560408660319a0020003051000c0c3c10020900343c80c2c81e43d01d1000b044064600300b12030160004044018040190000441075050b429404555031140301030f046650000d910b1002c03c410103070070300c580c600c92505050b800300c500e0720b00759881c1d0489408265255100b014a0114400024001c080d003820f0b0004008049420341c1e80d00c2a00000700500300000b81c10001309001404104441d40c0d4020a5441842003500e80000006c00c424a41d034000c0790841d9854011000ca4050a00d641041c0f40d5080041040692a9015982d030340c4a00030480032107220990b41e007208800603000c103a610a2541c2880c0c504542c1101721034460f80c1101028000000210180d015901240c11181d4101c00103018060798243d44400c00d4400340c00350503410000c0100c2480d545d100c10032441544200003080d00b021030018400c0e08148080002060005804c1c2d07a10b100300120640103148030b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 866105944 1250 866104694 866104699
    0xf1b0f030d09030903060e1c1103030415020f1201090b1e040b0a08240a110a0c050a0b0a09050f060c181503010608100621090c08030a0e031b0a0e09011401060509 71
    0xc030000c548047c410040100c0740889c4201440c5103803103940314840c1000d81c1020b005070312034080041c1000c0c0c0e0038082c0101103180e014900e085031541481c4140c010b507003008a00b10300c55451160b02c100c012440d2000d44660080444001540c840700c0d0001c1050300450ba4070070710342ca0096402140c1100710000f012200c2000501c440005541c884000c0c80031140b005451504c800020321240319494000e00700d402d00140030720104c0d0340420456840c40c10240080328210000d50322a1211010000100301c40c9030401c10039805000b035440c01c1046804140240c40341402c903002040450341c03464503101121000740440c800f44581d41d41c1c56000c0074240000582e40100c0e0088000000907aa5100b00b002c081c60b0300720f020391101d070f2a0b0f42511080140450340320071344241d100c40000040c038820800080250200e1522088003400c4441308042c14117082800146c6002c2001c1c2c502d80c00b5542c0c0520250960740c1c400002e03801502d4958040340180032080d03c1d0002e40030b24100200d5503641100c040c1c42d89071007c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 866107194 1250 866105944 866105983
    0x7030206011508010e1f090605030616140f090409030207170708030a08070e03010c0f030612080d110c070e06121605060f0903030f1b0f030d09030903060e 68
    0x3204003242c80a551a14210005040c000051010000c135110305504013110006040c0000901120f4503080e498642c004000b87d03645040800640c1003d000056001d5504541c501c01c0440901d0701400b04a55040b980046603000604100f400c00039606481001601a10410504405160103540c50301c441c0541d903c1100144418541030800040d11802e41784800701460800324146c0303040c2d6800c036000d0404000d1100f841c08034200342e1000d00c19111030100d1950356110091490320302904480403900043c0201601c000c2e1500443c2030314040700c140f0f081241f80025010307500c41201c50680a14854075a282c0942007000072070300c0317100c02100e0103500c0403034040b00c6c2c03042c4813035280d41d4500c8101000c000c41075111038108a54501807014280042403d0902c074034100709080004e040d1351009140c298000c02c003103840c46065121100345440300041c0402410351080c410200e40c1d80380119021244019107401c60401010700c2064103100455100c401409540d41c9040e01036262041d40460080c1c1441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 866108444 1250 866107194 866107199
    0xa050c121e04060f0818060a090309050307030c12051e0a020f06030f04030f090b070501330e19090f060e0705010c02060309120c030c0f0319030b03070801110703020601 74
    0xa101c01103900726403040c0c03106540d00441007030585108000400300c255646180501c000c0074081400b9103441920340e00030003d0181c0301881e01a008440c9a0030441c0241c2c8024000d000283e904007100e0191b44181154440d19400e61904500e8450408911540300140071a10000c04c100004c030401d000d842142c46000c092003c000303000a500086032088039001205000c40c01090140103d4200c034403e910b8180401a2a101201801e520001003124182c0d59862403240c0500140300303048000c05e0144040e10303501c000c8600b0b8544102a4000d11103404560401b0540841b6108802c0801036082c079001c0c03100a00030708103446c1070403612009a03841424408910513601c0d000ca07030038040c1d8030140c45a1111203915000d1240a800040c0744503081d104641581c104140401c0150625843c20030040d603403200c15030ba0aa003060b500d0f0400003159071007401808003042c010307010412420450b190004420404030002442d101044c0e000c0c50042d440c00700000a0504054000c2c28414020303000c0364416603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 866109694 1250 866108444 866108497
    0xf0403051b0907210e0318040e2e2004030b060108040803160e03190213150b030a0b041109180c041502030403050f06071202090112020a050c12 63
    0x10300c102d030518001614682d0104d019040744d204900348004140b000100d4000400c200b610399801220400d074004282d403d07003041c0e480c181c001c6074000c414800203480c040a001820a004c00d40d00f01c1c0705e01e003079010710b46018240b01c00d540c0584c089980c1d40c02010481405c11042c00b695901901043d10713015011000103100354000c0c1c03c59802180e001c1e0315a03246940d0b048010141d8410f840b1090b0802c1089016420140e50410490030710454190f800902c11085204002c20344a2848464451605000d44440e51152103003c480440d00018503040d80e903569540034200800ca07903803901e80c0c02840c203204181c0c00d11515000c3d140035a02a28450694080b01e1103028480c0400c840c10050004104414007402040c038030300ca00c3d9401c5500450341801e13102c0c3d40301400d00c002c0304160611030348801d040105859000c2400f01852080346811850440f603030780000c2003001c01903480c5004540002d0000301251140045548001c0c2882c2560310100040011000590186551350003001c1780c4d940c04c0500d903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 866110944 1250 866109694 866109709
    0x92d0b0106050c070611010f0e1b090c07020906010509030a0506010504061e032907050a030c0305160f11030c030d0c030b030a060b0d021003330509040501020f0403051b 74
    0x6080500c0180044e514000040f81c07a560050301c1030409540b03492030302c3d500032024064100440841400303401a508a8088d080c0c0340c0040c01104c80c4620440d00500c0036000c0e030b490032101c01c0c40d0140e580001682e84c040050361240300c1c0203a0785805202c0d052800301440f0f004212a4140c410858040c010566140301d810000d40807000d0179501030460782400c200040b25142a0700c80b512542c1c051210783c81e040c1c0d40050304d1500444202001c100c0010f440e800040d854421407500d4010340c1002c10107814500b40c1a000303031414100a078180101c8903280380c11140240c2c20490404880002c40e543d1381038191a10340c403070300041302000069052105c0308071464001c2c01800104800a070080c1011106500e816000c0d04007084071a40081c4414650310142c3c695080800403500b19480110360441100c0d942d0380c80f0684210355910801e024040c040100e038030010300c0001c0360310888208007251100e0a00f0350092080c031515840c4001c0c0001e0000070004e000c030700e203110302c2600c08900420242040900182 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 866112194 1250 866110944 866110957
    0x2d01081515090d0606030f0309270c1e0f1103030417030711030a21050f01060c0201050c07030b040b011508011a070b0c19050f0d092d0b010605 63
    0xc07407448207541c034100103960007410160304014031901003020741d0380f0307000100c4a1642054a0110100c41030b102416082042e4000503c4000c904005102c42d8440c0c1c640d810a500801c03109254541c032000d04024421482c066820b805040391080740c1540000182071260001251030124084952910020300040242c80c45640c001c503c4081c03540c0c000011251030340c40281101c05001511041c200401420006450110055115a14282031005030710b54140d00624070011100d040508101c94201e1782c041280c115841d90502040c035822602c01079603a40521010141e252292803030000500c00c1e540e807140d0245018280c024010f0362601805001d4502080d144400700340e807140104210341814041400c10000040082e007080107035940d0b150b02d464191510b4411003004079240300038140003c0400b00b401c81030300b00b00e4504028104200342c140a02110320707071080d50702c03036801080c000300c1d03500a0420b000d040510001a00d18034244032a00390401410b43e0741080403800413800c0fa0080040b10702c3d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 866113444 1250 866112194 866112199
    0xc1c1406011a0c28080a0513081f020a11060c030a0c02071a0a11010507020109060c0c020a05040504050717100b09040206070b18030d02040e06091b07022d010815 71
    0x48105014a0b4a0341e20003603641121804250f42a04c0011441c0a07004d8a10301c800c580c0c41c10b17640d604040b1090700b0400d10b504800415005211501000030a180001404404c0054056101c0401c81e9046e83d520302c100744d445113a402100104101844500f0043d031040b1b0120f03000300321400b42000300b203135602c5440c01030b030710380360080013205c0390300419100a40142c40c460301d403440c92810001d0405003519400d44000c0e000d40c3d19201b80c00100710903405454a0a0790b90b152620030540150001040c4d4007451040c14019a40d5002180503c04140002d101410417041004d1810520348030541d5601d500c001d400002c6498a0030030400f900d810b4044c10302a980040045043c042c00b51203035030504401500303040f01303c400038500007001c40c8103201414000e10078110050700c0c0c515000301681107443c0100054401c170311070010001d00a0111710350741c03207944082064a0f103900051000c207240c26080307070507070ba01c00190111502c010840e6140404816400380e8a0394419201c04203801840ca0682d1806035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 866114694 1250 866113444 866113453
    0xa0b06031311060a020a021311040506030c071a0f090105011212030f0614090a05010503031603030204030f08040503010c170705070218040b180c030c1c1406011a0c 72
    0x1140140018036100d0024000c030700760b040054149002031541d50109000102580143c0b000d0825403030508003401c100b241d07410040c4040b802e1840d001c0d40c54403403400354621501e00440840e030f09000c20707000d403600c0690100d60011500324016a40c038a004040f00c00410407591000000c1c482401030155074121160300c40350f0a80c1c1c0b43c56580d4602c0c2a00b200c18003408061307403100781c5400f00e4a00d0059100410b00850400d04010020f03003804120440200203104a5081400400c180e440000444110002802144c9041d207610714040b4081c2c8038542c00a0110300516411405115100000b070080b80c0049008000c11140080e00f56400c1a10a19100e42c95a0503000104000d0090008041041c4000d03e61b20043c0844a00a002c082007a5070a031400301c848000c00415000c604480058145940001c1454800080010f0340d204801146c950182d04008515664800d0040014440030b41c01026035100c4050000c41540e5020244501e260008014250440100c1c059080700c40c00c070700300000350 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 866115944 1250 866114694 866114701
    0xb0417160803030c070206091e03010b060c07050d0c030b10060f0c12050f09090108030705061008101d1e061501050d0c0e0d0b0402150f030703050903040f030c08060a0b0603 76
    0x915682100d141070342c01076400c00003100b40d9643c0c0b01180c0c11062510301080640c9270080c0901d400c41e141035107110f0040908001043c048400007403041e048490443e08242c84195a1078800c8038800c9550006009080c0c190034066407011820340d072070940d116981d60340e010786444001200c4200c4201d2010f00030041c510b0000d055144107400414480c11071000c0b00c2c0c1341072032040c0442c0403000260b1064040360004a110703410018240000ba0304501c0c0380320440b070410f04041c00c0c1d540300d200c1d94130282d80c0e4958907200842421403e0301102c040c0c40a0300250350340940030f00072040d80c3d401009400e80040c0610400201c00c007032a085503080d029411307500c01e410125081c0700742c401003014a00c2d110600c00008260300355030382c602614103a6184074540d04040d0b803e09205000701d8071200205169402018010300302411041c100380d03680030549160114154131460380e00c1d0300f58407894110400b1912014008401d1084024403d02121303200d030b040b00d080d81c3d244c0845800304c2c1e4000d18040d91000042021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 866117194 1250 866115944 866115961
    0x4050f0126221a0c1308070f0b040b0a120609050c03040b07050414130905011814150c0901031b02071a071e030302040b120103021e06030a150b041716080303 69
    0x6140d0141c0c6602d1310390b280c20054800140160b0030399100b4001c40e400030304188940c0700e503040244010103130404120b017800d06140503102d035401051148406c000394004e0a07041c1048941290b002000c40c45410031440c1405100061180c2c0211001d0301d080010030701080041e849001220201c5a003900710341a4807011004201c050303a401351000f4810341c0c40311030303480c0864030030310490507041003ca007401160b1506150510128440c0001502d154001e1901d00b100d0440881401d644411041019691411a400103800410030b544030301078841c152907800d090071900055004107582400140b2a5a07044586004c042072040c007400514441860b0920425a01d00300346500366a44a03040160406895054103052504911000080e100020004200f942048010900007503400960038142103200c402088c07503440054000b4030990b954420203107040c1d0040701c046010b8072000581c0d40d642c42d170ba82d18a0f408545000a004901d00074002c050f5050305941144008440310900a103045031b98110f070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 866118444 1250 866117194 866117243
    0x2901170a0c0b1315020601030512030411010c05010906050a02090a050f060a05280903021206040b1605360108040c03151b030606020607030902030304050f012622 71
    0x140348116040c8180301082c003813820040c91195890a600900c015851130428900e010b041e07800e50034000074100706210208014400d003504004080c01c0801040d036042c03404034014000640e003d03104c0381ca054107004001005400914200704101ca107204115202e600f08443c8000100d00740358059010050344607164055070150110388007a80e00410170764002c0c0f8111446010074588000002d017800c1050046241141440240300c1c082c1004204610381503990400400d405400c40015011045009412510030b1040310040d07200382080c45811041000c041c58009c1c900040c81e01d00b0141c00780780030159442004031070304c030315001000d02d4205440c0d03840300c540020b0741950300c00c0803940700d000f010b102c0701c6090705041d141801c07988e0004178a0320f4500000d00342400034046204146c1000c086a016a0f80081960700f0345504440c0c21400300a044010794054607000500c944100315500100328240c5107110907403150000541007500e8451000c400c0c0345030544400018242c01d541f094100100e0080308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 866119694 1250 866118444 866118457
    0x218070f0329190e0c1218191e0b060310020f0313030315031a010905100306051e401112061006120b0a0e042901170a0c0b 54
    0x4010400c1c43d6204c020902c0414411203000e1404035001a0403a052007580300e640b9803064a000d400000b01c1010520745841b00c003007050030005412108240b000344140000340c000d1107004808012014481840c0136200140700703c0f04140f10340107084414040300034a000f100c545032700000c901072450752400100842001541000e5040694030751214080d44940310420010b540161034441e07502c4403051a0601254058000e01385290500047c040030729420038035041920350055010032190380c1c40001801208c08080c0503481d11000c50144861000703000c0e510089894161010450044038140c0e008008021102d0605110354001c000001704030702e4940c000f0664001031100b908079030214105460007030f0542c0d0b044441035440724200b000c9074018615007808540c406007030091440e0580020083d041600c0360305d04401180c0002010002000801181100c00050055075118181039098048100340620780441c40c02c20314000c0e8048001640b01c0d00715a010142c40109400c09401c0502504940c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 866120944 1250 866119694 866119729
    0x2132c0f060123130b040f0e030409112217060705030109020f090d0309090b0108041a0712021c0c030b210a0b090105040c12050d0c0218070f0329 64
    0xd00c00c0b1a0107035501c2192842c135001e0024003040c011030721010042110344401c449070000d841c203010241c00000100c2614101e410103000060030403410b59090120703118000c0280d0840c0340c010101001110844400340548410084003185403520080c401d0b5510001d5640101250051004100070011070300186a849041042c2c00d003440c00b0319004c64841d140809044001c1440d8000501600403d0320901600070424a040002c2c3d003805e45942c854500c290040450320000c000008120500641d0340880d02540440115a916005654100940003245c0c4041030700342880c1400b010584203020b0005450310052074003054119050f130782c110051010284021600441a03106d021549007014548144411000815986441d10b400407164000382c00250f8100980b00c102030204078002001075030061380f030600300d1102c0c240d4000101070303441490b42c10300310303c000710200241035501c170344880c4d1585030380d45092002050007240030150703d01c02c4130584140300c208111301c08680341503400381c1d4910035507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 866122194 1250 866120944 866120999
    0xd08090601180c0c08120103020415060c06020702030a020909010f05060402030c270a080105090706030c1d01020307060603120f03110702040506060c0a05061e0709030b0402132c0f0601 81
    0x85584081e0181c0002114800c6c81c0e0400300100b0542c00c040c0200a864400081700c9980a8280f4070080c01306081018050314050b03002c03c9480440d20100400c9000d150000d028004510f45900294080c2003010b4804a00d58142400714080341000c0c000e5a0054000c1a1050308200600a41d464030301c0c00c114000c070001c01c1210103404c1c2620750100c90800303003030500c001103003900d000c0c0c8807286444066404042054904100051940d5101c2c1c00144441c0c0170001202c0d002200ca00100e1940c0580e0f40d02070425032410500208000d24500722409075441d071385405401603c5890203174202d82c042050100c140e01c2c1040701c1c00040c0303415070299900c00401440d0720700300305181d0303103051401c10842000c0311507a0051702480b03c42d15840a0301000c1d0a0f441c41c0b801c0103441e07c2d042c001d1210300c403032200415078650b43e404901150780e0100030428103140d10b40100902c84a094207619210490381206083c6060f040b01d442e5031820100381500741d403c02000900082e4641203404200512041c94240e25050303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 866123444 1250 866122194 866122217
    0x60801180c150807180e09010e06010f0e06060c030c012909070f0e1f020c0112021603050913050a24080d0c032c040b090f040204050a0902120d08090601180c 69
    0x404100c9075010301f402000010744d8100b00440180b03010b4040e046400815100c800c20040300c0900b01c4840e500040980f911522140d42922071032550059482c81c0c100f5501300841d450100d8040030100510103004010124000f5001007071011112080e5040000164074109224442d0f01684003a00002405050004074452070160b40101600700e050802c0143c1000001c9900ca40e4400440d40520100344c004516080290414040b080750b1041c1c001c0c240000803c40c02140c0e95010b03400d103c5c042481000b4003003454246089002004100d005201050300e480c1e80a441142503c403c000740c3d00703480c009008205080c40140d031141c40d03205c400c50411020b43d81520181e200e4004040c409040d1500f040702d240520010441541c62508171203000f01909400c210b8400360052985801c950140e80010306503c07820b14000c0602031182010350406062018138007030010029004441c91100e60b540c00842d191012a1921140c0c28030030003440e4a8400c10340d890441d440d9101c01100134540c1052034800d00e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 866124694 1250 866123444 866123459
    0x15080303161e021b040603020d1214340c0b0315040b1c030905030f101416122721021906060801180c15080718 49
    0x1841101c510751448a00c5800c08000e50b0050844401ca1000480c80c142001c0d550700001e60707440c14055018610000320b8280c0300d00d501d541c0e000c60701850b0041c01400200c6000e091180d1090a42e40c08a80020425401807250032490001d0703610007821105036605110440380d106500800001d0000e08550030900f004001541030500c039001440c0d00900c864592030400640d8075202d00036609103002d903041c90503d03900c6540e44482003500e00355889400d081c004407420700b212440b030580c0081d40c161140403111000084001495805161405428001542e4a410000c14114266004051209014200598240104195021000c000c6c10004001da406105100d0041d145c20000c90107041ea04480c2091010701c1d0f000b0340c1b0b141c0400d0008c407018240034000a40da031b00c094209808005007a26103404200700c5402800c018140e410003401207402000e1482c48290481c081201c00000045000940c0c0e0708040d42c40412900c41e45510580e661000c0d402e071390941090b5100781c4074440e581c10104622 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 866125944 1250 866124694 866124697
    0x6151e101701050d0b0c0c0111040902070209010b130501050a05071e1103060405070b07060207082a12030109020a1b051c0219021908010513020f04090213150803 71
    0x300507644810888450101121840c07006812840c01250041e0b03071100440c1103022844c0c2c1280c440c0d03540942da209824456401030419401e0500380800000d40001d4190890b0040c0c00c196000f219910792503642d80001c0c00991207001e1484e030342d86403601001c006075806036014000e45134a5044c05c130710f407510a030368416001c0074094007040c65811b0816624280109900c801200480580080a00781029121191ba803d114800c0c0d40192500150303000c204142c90f015034440c05e0780085d03c50748810400194101403080310100c00c680c262034001e071400f2260b0001d034812803442c03020ba005246908080c03048001c2c0d80071010210900a000c0490718041304d2002e1070301c94481c003803c05000c60b510480d4055540941c407410070b00840d4000d07288403011940c08132203078100560449210352140c9201d0a0150720003402d0348042e807a5440d090070403d00f10021080a000300d403003120140341800f003130707030801048070040d1001079080107a0401c50030011300c043e03200e03280782d0602c01ca16855440d51440d216145 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 866127194 1250 866125944 866125969
    0xa060302130905091608011e050c04050d080901020f070f060e0a050303030901061701060e0f040318090c0e0103050f130503041a0d0f09020d0b190f020a020f06151e 72
    0x305e40c41072030603c00b00d20203002c3d02c20160900200034403000b60506d13218030002c900520458815036a034008550200440c03c1214014840501144960196410501070319048421014094010401e01d00c0d0f8002010800c002983c5845c0401003041d8180b40c011a811082449a03e4001c07030400300c041043e60302000a5071050800f0000803078803d0a00e40d003110418640c020504050b0b04060041c00030418610301950300039503044204400e90750300d0070300b101c6030791003840b401c0c1510301d1948003c5400300750303a0012201c411039500c680a0040e6030b0001103044035000c888000c181c1d480c6c0741c0031910b112020110150540c2c01801180c2c2000d0312180c0781d101d030103000b0742c08801240c0d00141d0101001c0440c041c4122004400404101510341500460500100500000c0c08203640f5400102c3c03004400456120a4580480403c8007460b920407003802548400100030162107182184030701e6040001e2118410304945c0003924a03c07613070805010b440c0300c00b003c513000c0d00c50301c2054035403ca48900c10005d03038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 866128444 1250 866127194 866127211
    0x9021e0705100606030612080c191b06170c0a020c0603130606050418021504360b03030409020a03020d0903091508010e04030c060e0f0601150e0a060302130905 70
    0x84840468039a08101c030f50a038000d00515040240400810400c51900600e05070050071059403400e06490301c80c244000141d4003481d01d0250f680810600070b600c071352000038403468290303140381e951580750580300100c4910325030f69401c64242c00501c0441d0583c014050001860044800821484000655903001103413114110340b2000655401d002c990300031500245801c0d207081042000708110a200009107100186c06680d000d507201001c400448115401026241c90015a0031140050404982185401944070300c000c64a140140903441c400d40720b0701040140207526152420b55500b0183d0850207528043c141d09108101c50720f00701e07005101500d4882d0b0360703127020542840c612100659040fa07003002000103100060105c01130060800d6041a010700b4200c90401a03441d0060140c40640e130b441c0c00720700441140c0090118001759480c160740c50407440144c80c002c07a0104840581d21443c40c69401002d0460801580780268001c050362200140407850341c3d51611910700a89a00359181c12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 866129694 1250 866128444 866128453
    0xc04050103031128060c05071509020f032d1f020a091703071704090e0f0c0f13092d03020d0e0d020906031e031306020705030709021e0705 61
    0x500d414003a013050720304501e030221194032107280c1910300c42007011002400c90b995000c404824030b0041090702c209542c0b20034010103290003611804058545804200d024001c3e40151600901c0c005c500c2070900d00b2099080d50401c11103410401100040701e08038100c3c0d024000144000403002d142004d0100303007000d03000d40d03500ca03c5c00008000c164035500c0711002e0b0002d01a11030301034101004807503c90350000c040e00c1c0321845040d090060340c826030303000c1d04186142c01004114980301103150009100c08005458414940d4810311041d100c1c2d4080480e401085180031100800c3c1c150300182229008229401601040e00d40a48a542c0f16906a1103403a03541100e250800d03130704100c0f0030008020f51801110300c83c030301404103000840780c0344020311030100400080d216440801c1619541d2015403003110b12140040c2c0d034582ca90380140d0011040352060700c404544640001041030440d10090300a00e20b4519200c0070000a400c5400b001400c280e07450f1011600c07100300400741543d140290090b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 866130944 1250 866129694 866129717
    0x61903050a0e2a030f030412021504090c270e150d0812010605120c1806030a090605090105091f0e1c0806041a15070b0c071502130303110c0405010303 66
    0xc0580305450f400740352203075214a1644001e80c3c4007005950860341c6004a000c0c2c040c01e24800101d408514400c0c10804034408a000980703c030154002030041500303500d40038202e40002c2c400280100c40c580d052014044014030405c403103e0380b074100a92110900790140d449071000d80000d607803580f10040c217580070080402d402002280e0000f100d801080c0c0c034188a407402d004045100121100140144540c18000c02c500100b0050030000050340000184034513a81d150140d42d0300300500070300c0001c3d0303110b924201c0000c55071300e0144a4240a0200030b00184042c000704420a1851035210440220058941d0000b0320441c03810042584401e054031020746422890400080c001c82c0000d01491086041040c200c0c070780d0b248511540080303402590001f0515880e036202146a20a40e10000c0c00c2102039410410044c400fa4040c0c144030380b140d26050004c0710880080d0341a401502c00e41e108000800c00f080000078040c40800600340b40b00b5054442ca081d4103c0080c0c22074070241d100360003085121055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 866132194 1250 866130944 866131003
    0x27060408120a050403020a171209010e0c04140109020c03130902030a0e0c010c080322080a0801060c080d180605090d20030f0c07050d051b061903050a0e 67
    0x3216480000b01104000c0c2e403505880c025626100c0c0c0300017a0112494980700c2111400e01011a40c004165410f8480b09080c400d180314028480740101c4840e078000d01c4480c0c0300c1031810703009540202c1039440c220700540c5d0078030102c00001d40c03207015299110303c01041158106004102c1100007070040c598010784030f00d0104c501030140c54100c01300b071007140c04c454000d4103581c0e0450101c107007a5400c089000e031179655800c81040b6485210382401140c1c52640701c404c007000110f8000707000c400d249545464440c0d07170700d0400f56043c17040014010411030040c010000d030402264404804054840d000c548200b4540d15030004641080c1d030704141176080030761220360b450b81060b0700d4500d02e41100510300c0340c0d0004032103090300c0b0301804540c000b5951b00040c110010140030860707103014004c0180080034516451a01e140d40d0325550143c9041403400110240d40c1c0e1500d03130180d40761380c10011990044041007420440042c400109840006a036070485c4820740c0c6410000314810541c45140b23184101609200e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 866133444 1250 866132194 866132227
    0xb04020910120b060306030a0f080904060e09010e070e0103060902060909010b13050306160302030405120c06100605030c04030f0507091803020c0904050a0219090906020301060305180627060408 85
    0x1007950040b041002885495180016410a0107402120b607000702714041c5841c540c288503010342d00e680581040030100740124181d2549016114290080210b1080c01b00c03034a407141014400c0409000c040d40041000c86c7d0983c05c03c2c815180b0092030780b498884280c00040c3c0f00c007000e80260058100104004078810ba801d4404001360030110010083c5103006096442c1310340c060b100303542c101500440414104a403c01140406807200340d441511200486001c960fa000120344603286034500040c000740050142003101e00a5504101040c40c150964a070030005110000382110248200380c000039000354a032199002d00c2d103007040803440d14686424020b19010364000141d2107160300c5420312000070720006030001c034168140e8480c092092a00007807200b210785540700b10105820004030800300b260700d60056050342d0058904000304e4541c2c5000d904503000c000c03400035859011901081218001c0c109440124540302000000a040d41c80404c1c100702054404955062010030301c035004400c2e115 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 866134694 1250 866133444 866133461
    0x6060c140a081605100608010213120201080105060a110f01060f05030c0a090c120c03090618051e0a02040f0b211203070c0221071707090b0402091012 66
    0x90081c0711140303840c1c940d21601d210303540042e0b40032030300c0e16200800c000041c03049041d066101c580400c00c0d91790340e0302042c0c080d5100c9001c000f80c0c001e4206020a45208058070000341507010b81d201c401c1d60b820319050040c9548141018400e115125a100901520070444000c440c10214000302e2001c1ca03000e9038460702c00c902c0d0003207403203500241ca00200c01d0311a0308160007290741d002d030003050b64104140103032a102d00d01200d0311201c074100404060307441e8140e08081400c030711600081160580d0690800c0148a4280b8002c0c00742d0058a01c1890110132520082c0068482c127003547c80d148038030307400182102c05403440f400403aa11041001001e10b460a00e01000110041c54844201000c3d082e040e100c02240e01591015980400401c1800d40700b02e180291160340509003060544c602e004007140c880107545030f801e07144100d810105519020764050020103401500a040319030800c0c1c0c400340901700255040b604a5406d101000465941c029903508103041da4a0b41070040304800c081070706598601c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 866135944 1250 866134694 866134733
    0x919030c090c1d060c0601030602180f01050a03050a061503050108011803020a0618020d05060603010608010b10080402122b020c0a0905040228180603030e06030a020c0106060c 77
    0xa1004842650814403840e16210502d822400e01d42050001030460f000b40040500c0c51b105010010080004a07802440140b84d03000a803403410a40d034040011002d80d101c0c4050020718140462803456009410035a08400071b401c0208069850322070403803040b1124a04100000d48a50042095450a21501030f030101c41c5440703409492580e88029595000c90100203148583e10a91507401204080b103445505038010410881004241030181d83c070101690028800d51a040340029080014403e12810700d201400103202e44080280944807024010000da07000013124a03811121001803100d02c9200421140c0345445042e0302c0d04040c404d900e0f40c00e8000966000320440c0016a95042d40c08c8122000d8400c04500e40e5214400b00707500f08940310400368180700702900c021001307446050203c1a602c1a041c100c0302181401e101400707844480c48040c0104694100302c102604261000b5507100303440070005803404000810040c02c6420540c01000028003035400c0c07804215003000040704500742c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 866137194 1250 866135944 866135951
    0x2b1109070c02010807020c030607090501120b1309020a0819030f09050a090b03240a150e061c0507030c050a0905043305040b04021906140702060919030c09 68
    0xc0c50050454544080042d0501c0701034400102a18400c10203010040c501509403003540c00c042001400150f898000d0a012500700b80800314002c009119103550080b0040854040e070400744244001440d1402061342c00554400c404107140b8001c1150381c5440c042c85c0d06242d59855982001056404400c110108010440718204010f95410000f002501c5900000244580c245000a490300c80383c44a5042c1580068090145048088203050b1284e40086024045c0818600041064440c1ca00411284401010206070a410010300c01a800c0c421b100e5007801c009455268145060b046520480e14044503203814000c0d4241000d07568000c1400c004240040d003015540d00c0c2100001820040210b40400c401e0b03800c1d40240d42c000c0500c00c10000f020001400c0c24144440d020f00f0469043c2d000b400742c107810680701ea944800d030108036a01a900d481000c0e5020350800d026a101d544140e9200c0018001e5518a50324034850700031002401410003d141d03c0c61130b00902506191b800340440926 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 866138444 1250 866137194 866137201
    0x30105190b12070903051504030e032b0216090f0c0e011209030509060a0305011410050703080c09090705031e1b0318010e071805070c030c022b1109 65
    0x450724142c030342d010b250805680003a6944a000c0b600c50b040e591014069108040085c40498860400180075038001e680e0591824554414107035101d030361101110180c281410346822014415070046000d03c050300c166110085003001041d0840d60581107001f847d56554030090504100c0d04c204050300c010703405c1c550520540000060404c035418a810300c21244c9a0b142c3d031080510034012a550500028a03898440000800050003010240146080d00451408660341ca01d095540741c05400b10940d921b40c1b52543e959000c43d00008064684020850144001400c03070340ca0903607007031089680e0307554580c072441e2221450f0765204074680801322440118050010220340316640c1040004e4080b101d0b0b82d04d4403001044016240f44540c24002c0c2c2d440c1c07054000b540300d40454031b0411507425925a141a00c030310465002100d03000d58000700820452204040068041e0f0560411240000e295000803641c0d00134903814508440c458400400e030b1180030004001801e482002000e0095514101c07514 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 866139694 1250 866138444 866138459
    0xf0d0501060f0f030c0e0d020a1503060806090307020307062a060504030e12030301090b0f130506190f050409020f090a150e0f060607151e0c02031216180b03010519 72
    0x70006c10040c0c028440c161f42007081d500d404070000c00404160030544400e42200d28020020969802111030324002c44000c01c0b86058000284c8040301c0e002400f80102a2810005840c0034004900c4c0410440c0103625500344410358203600c811141c000d41003c500391916180081c0342076511150141f0404003000050308021000060302c1c113480e8001030024072021403038001001c4481d49070420b54000f03004240000440819089035010702819100d100641e20491400e01042d0300b14010600070840c114420803c13413034580c10450040740040c001d404103244c0036000c80e40c214411542c0f84002c5488620807400920000031640041c6941440710040341084038500d0305000c005811148100c0b40030134038800303001c0e101c1d00307006d0b824100c04030400002219140d102c1d0351a0707643d0b040c12025440d1407030380900d55001108443c0740d8240503040201d65aa001d66400100c1d24031001c1108011040f01016403041103c609032001d0f00320060031585940c5841300300720140d1058110f03814002c4000c602040402d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 866140944 1250 866139694 866139707
    0x1709100c050a020a080c15041202120307080619080a0309140103060b120619030c050f0a0303020606090712060b0309010e07030f0f08070812040203010501050405010810020f0d0501060f0f030c 84
    0x1760f01955095607103456490141c900f400c4c0c0c0050001d401e0506090108000b1a4003466000015640940704000c00b000c43c5101c05000c00c980c0c00300800eaa080000b80e175460542250b0301c001019130071a50045840e01c03903661a02c08071000490204101c81c02c00d010344919100d00042000342441c003071241038181001e882141c006c0510401002c80050080742440c1d5648103005c0c4000e5800800c600100e6a90401c82c5803011984102800744503840c100d00000e0070619280307400c1d00d404da00105901e441d01002d1055487c001444102000052040030f041c0707080e5405008010007109499540364108110041d0071286107440707610725a44522402c000064220094411568208007403e80301045400c0c0480203104401c8020306c0741000041c22540c850007000d0340ca0045009070001c0065a0303c1e51b0030700045903030a019a20041d8484010a012107181d0707002058550b2a00300160704142c8c0311a94042a22003c1c5c1280300410107460300c0d482c070140e10007500c0d0306442c0146800d2108110f0403801802c1e5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 866142194 1250 866140944 866140963
    0x1504050d0809040603060c0903120c02150a030f150f0801020304030e10020c03010603081210061409181305060a02030f0a0c021903180e040b13031709100c050a02 71
    0x8090301040200203030b999607121300e000710f40181c41440500440782d4010b201040901007120101204600c2c9200309118080010246502030011058040545005600c1c1c0d0001800d00e0b040540311852074550517218042e002c1240b140c02104050142000c09a590200154005c480a40c1c410310030080801c1c0e0010386030302e03942d8090720115400f90601000720300f050a040405501582060740c000200904000100012820284000000c0d19907465070014218144942e2002400c9041080b0300c40048400416000d00c000740102e06010310300e803d003445c0380002c440c034860040e406800481070210510400354800010740c1c0440c50b6203400c9110071203014010b80311078030312956000b00ba00d000e4002c10030b0941300361000165810480c2c0034a00185002e00d00181e81c44108881c01d00000c000280e441719901981d80a1a80d011540d2242c0910004100300c02c016010007174900c2d109a114896500c059020320bc00c10003070700c0c0904107160030074183d80e040000c0c041003103410003007508074582c0880c00d1240c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 866143444 1250 866142194 866142203
    0x203090309010309030c06050f0106141c0b06130905070806030a030f0e0a0b03091b010903081606090209150a0f0312140f040602013e0c1203090109021504050d 70
    0x503d803c4d02c0c1001c40b403080744a03000400042c54081803005c036004c4010300c1812103400e40e64030030f00328100c140b582c81c00e4018244521071904042c40c1d690710712000d903003004861400141015041c0b01a00d405c0006007019a40641070042c2c1e01c074140884c442e4404c0c4017550000041d0000d101880840e64010034031409080390104009101013260105d44e40ca80c402c2d0000c01c2d201d40120307203038104448810b03141c220704410a06c100c08026010609540651f1500301101d1b08510b41509210800101091019904104460300e03a621740c620780040e914015000c1c0211024109030821403560028407407509056007001e0b40f941e0310390200f0000a0300f001174503015012185810020001c0700740c038220042c050303240c001c105401c0104001c05c610b80e055100c440403102405201030264120000400301028101c080f03a181c01507c4c145200c9001243c006001e04040c4a040301c001d141203000440d01a041540c001160f80d4641c03201005601c0e00c00d6941c08400f9260081d286020b01d42000981c225982ca5030040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 866144694 1250 866143444 866143451
    0x170708030f190903110706180e09010b060a1206140f040207020102010e01180303051b04061112030109020705060630150709030c090209060409020304240203060109060302030903090103 81
    0x1150150814201c050695401a00b0303c030304a41440d01610303c09901e49808200d11071300d0030024501c4e2186400a0740a018a1890f200d0315040607100140d0038001042c140241d907d80c190075090744c442e64001d003041c60b2903a480116810041d00100b00b6a00e1a81c070032440398a5481c8a43c595a81d18004004809011500166150b0040c4010b034058072090181207040c6d403802d1984540d5081614038216194802e903000c00c2542c0e142154013512560000741480c54401c00e0100340019030250007010211031001040351013a45143d10a00003940c400d0300032003d8182c0111b8442d041080402c40307290410b4040360005418408481100401da12070700c1c10340e40e00d0b0b0b83c220322803903079000600041a2003495940304280908d44100080d1809855100440e11201e01300342c00103d8102620035180503000060a1924152501018a001e904064020340d241c901c500072012035078011105109205410307640c05a140d1074a000050410120b540c00442414010002c22500700e80100440d40e00c1c00d02400c002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 866145944 1250 866144694 866144701
    0x30708010606350a1506050a0e0402030f04231009061a130f09020a030f1103060f0403050a171603060609050901180b1201020304060c0504050915030c030d0c170708030f 74
    0x140c02034440105c00c6260705050100104004d0f601100400d0001240e80f01c9080380450042030004920080351800e154054000c04913002400c0801c0b004a02c80c41170100f900315030001000e080c10304c00f8000e001d003055543d49e80e9080421610f0f000781120f5003466152101c40c0c20410010911510100c560500300ca0b0355a400d070341545a40ba88071100b2180c015001031385144e00d07460144100904001d0a407181c1404540c0c00d2070314600002e0080c49a81290b0340e81c8040d498070340d025146500001030900601510100b0030940580c40c002d0341b80302c0c001d49852500c100207095409003c550301c60f0003810800c400000305000988858580e00c0c1140ca000d02c101076118004584400102035510303403107074807006240718204030480c1500514000e40c02203004200c0d03540307070f0601600c01e4411032103807503007080851000424480504611007102e01000d02500c1d0660f1000f8000b0317060004520b12030003c21104400c840c04e001c0c642c404a090030703541a040328078040305038a80440500004000c0c407010000304000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 866147194 1250 866145944 866145961
    0x17040620010213090f0510030309271b080903030705070212010204050a030c080607020a020d12020f0d09241e02120708181801050111030903070801060635 68
    0x1128105039102c3c0307680da80592160f501402074421202e11003607040c101404603150380c1c1010a54030450354581c46004e0140c0c507000511500203c91151030407880c4c1581403200021b0303064040d14150441d0a0520300e5800030031740d000b61440c0c6001c0d02d5100d681d4828020000d4490b000b1003154501c603012a210380452680b800000e0188c8500d07080b254218000316000801c00010300f0446040c1c400c10000d40c0c881d541d503c0c0080380d50343c40100c406507009412214010200e203125250003002c80c22441603500900021100501c1d100d048105540080c1005100b0002d03500610303a0212140b544581d82159024189030040417482400023128850030748030107600f07886000304884984002c04528207500c4515030700b001911508588501d144214075a40920103901d04104907008440354034058081c0c590a02c0c004444034010518020031b584020800c82d00e407680d0801000c8010a581d100114280b0305083d0010b1031400000e510360404841d01c00700741c00d8100d01000c03e001803032184105500d281c0d0340031203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 866148444 1250 866147194 866147197
    0xd0c1106150a03120807090603090c0e0406090501060612140613021b07080703060501080a0b010306020d020f030a0204050a080d0c15180b01030b07090810240e04170406200102 77
    0x50020541c19401c0004c990444100c510404503620744200141d41e90406405450824200404c40080c0200c14451002c0003123050b82c02c24021900000c500d030f1255aa0303821110a60051000f14141c1c000d1a18810214010700c5664802c03c0c0180070581070040c042404204501a00c1781c48507004961021214985d00b030702103c2d100142d0443e000310795500362442e211001800f00380c84540c185000841d84130070002e604032480d6405501019035030302c1c1d6200c9100135080554403030003a6400704a075840f41403d1f031000d5400f8401030f020050f40d440c40d1104004440d00250301c6901190003001ca00016590081007183c01c00d5000700c3c81040d80b0240069000080c01c0d910702c0480346129801400c4184620032001e030341039074810a005103a0b40c030f4880c8159900c0c1210310038100b55a00c40c0900c0825815150440c0171400540c0c0303840e6031021107885282544801075001510908030380c0d401c0209200c025080000240a0746444a103018100038000308480c400701c50a41c40ba100460010241d45800d50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 866149694 1250 866148444 866148449
    0x1050a0b04180e070308031b0309030a180906140306061c0b1509011203020705030f030d0234060c051603110a1403130506311a0d0c1106150a 62
    0x3968261900c030b103405000c580098036060b19245208e032075808880c0519040f81c3c0241807101c010340c107215410204455403203310074080c41c05032203082d0005400740c0c1408bc00d4050301c584819008203441032410305240c000000c0065210b00201c88a0883c1707054204007070170000d42c02c69060281651201d0811001c50340c4007220702e8010402000002d07041902c7c01c0b44400c0f81d8483da003901c0307129640c1c0c41050b941d0001100c805e101c941041008600030f00c41036008005050101c07801010f01e410010803442c40880b20444408048081055070080082602c54616084018284107040245003007124060107080c883c018148880d46405070310340141081661880c0c1c2e880001c81c0004034921507855129004032041c1c00004001520216040c0341140c141c40407120850031801108115000c8440c0c06000b600494030030b203200d090b0101c3c66481056401c521003000c000c01c0f59580b050a103544084130100c000d48010001010b5101e403141342d001c41c03002e80080000c07416062018108000451590075603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 866150944 1250 866149694 866149721
    0x1c08010e0417070f03020c030a12230a031b02062715151503090a1713080105041502070b0604021b030d1b0816210207060b0901050a0b0418 61
    0xc16075500f082005100c1c0c81485110340e00380d44146255502341a41d07403400d110000c1280300f6007000004043e1052480899103048401000f800080310540001c955102e000369000090300e41914108406060603911280c22a620040402c0e2401c02104107150004c01030340c048a04000e850340182c240100199061003040d03800100013418080021441c0003a26891a800b6080030a240345451a440c01030b6803041c043c603405080c040307055994124000951142d41c55060a0a10544c07070400442000070000d8000c210001400d820103041040c2d80040350120210513a0041041e80002402c8984c2e4540280303055401507100e1803c2c4480046010020025004d20700c8082a03400c825030a9411190f09140081a401a92403443c0e400325200e10742140d404985260810246021904c1544041240b03415803c508500403100c12554090381e00c852029910143c442c00c0310010382c940445030030700505045500307241661401c005e5040c1401540704240b07d58040c5101015250a503402405004450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 866152194 1250 866150944 866150947
    0x60d060e0d090312020309030312090f061305011409030901031a1c06050a021908130b01090e1002090109140f0301020f03070f0c03091e080607030e1c08010e0417 71
    0x103000040c50742007980f1003650740071100c0d01081d01071030003c41142c0108030007401640c81c00480c080d0b456031402c000b13802c4c0790903031261040074048000b043c440c07d4002e1400080d403184812141c1411030075100c1c0616100d071000048030600c0900e64001048444003542801d0204402400e040c58050b5002c14a80c102e800603450780941103080c0784850308241e220302c41d038400c0102da2189030015007240545001140c0d524907450b01000000e0042c0704056000302d011041d400d5174030303280d610b80d0301c440000c0e4070400c4100d441d502071600c2e2420034045c040b13024140c01c2045040030701070000203042e1071a920038026109201c1c07140d02c8040d280e03130120030303907402009d002956960140285510f00781c0c011104180000c1440e40302d002034500c6186079042460705603944042c140e003451400080403215000141c105520180c0c005101c0c10140820307071284003203841c005800404061910300701000f240c0000b51140092000e011401e4100000c030f41507500d8240c1101c069a49d80c41c01070400d1680f0703a51100450320 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 866153444 1250 866152194 866152213
    0x509070b0d0b1e010504030206070c0503011b021c0f0509011103040303081006030e101e0e070f120b0c1b070e01031406042307090624020312060d060e 66
    0x20a42201c00b41d001e00303840c4a2128848100d03c1000902d401400030b001800c1080100058500031001d002ca40e0b0048081150351035580000078211050b4401c0510b580d035a0929800c042034041c400c44050b21240e1250b807828840304c0d007005180c43c801c0716105007070040206065809074072440580714002c3e2000103d88d5602d49034100500003c004a98011030b400744940045a814468000e01000000e0b040c000c02a2a01401058014100310500c4503140080c0010814072540180a03000d0032958480240201a0606034003c1030300d180c6410402202000451400000b401e11806590109051440c0380d219545540400505030400c100c1015902c034002001c80c0c50240140a00d040f2885088020100680003094985401c012138000d040d80070340c078500e02100158a4403400c0c03842441e2040c1d44c001074407001c8007400c9442d281c0241c0080f40301001c021300c860046c2c402c0b240500072140020740c106042248104044540280369501400c002c4d4401820801d0a8200103038100b080c000f0f54813002d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 866154694 1250 866153444 866153467
    0x120c010207060605010c031d0d0602070f0b0c070b04062406110d090b0702100e030f07090b04200c03070c080105060a050a0b070212031b0604050607030510090509070b 73
    0x1004074006541c42c0d458110009640e6000e0617055113100e6168803811050390144100483e00c91080a105800c86274a8008400281c3c01c0d200404800740309a031009258541e03070800b41d44c40344005009000c404020005d042c04603107404c51f40c0b81d0207540310b200400e060b900c01c5c0b20103140881180082001c0110008007103001c507000380c441d1151501500844200100e00f400c2102d810704148547d0828200c10407010b00982000d01d00c0b00b1005440b42041c0f80342c004000003003071802c052180e4105c4070341c10100c3c0c14090381030503000e10705002604960520206003864050580050040011400c0e0000003601e070050100510a07244101c0d00401444155a682c18425000c0c00703003103da15100e500301c0a4003082c03601e0505208401d990701c0040042c24025581c0c24031040d1a0307a0490000036201c2405042844101e0a400421003080e85001d0b000b1414989040ca18102c4050581c0042c1420201000f8113032469103a000c2c00c842003084045000e40707441c4416400c2c03814940204044590009413840d003070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 866155944 1250 866154694 866154697
    0xb04080906030c03011d040c0312030e0f0f1e0c01120f0203040f030215090c0402090a09020c070303081005150304021206090634140408061e0c0702030d11120c0102 72
    0x700c07241107001c01d0b1040c4954041007107280887d0000e010041e00002840030404c00880e2645240c1c0314100081c0003a80b140c11203150801101262035683d001926280718440c003071161604e0f98240074203aa2403005080b01d07a980782c0c80d0f04c1840c4c504014000d43e55581410a9070400c01c0c042c808100210368a04003411301500b00d2200410540140c8503001c4d81095040c5141c0c2500d02c12410b92002d4021031620780200000b80d48107c8000b5031081024a0108200f802d9100506420a85130001e1606900d14039029220780070040840707120003000c6404001c03035200c0505c2e07284000c9507188441e0ba29920782c070001301441090440d00103588522010000407107800281d0074016200d28010064036119800c40000014029200c48003d200580a5803121070090303156100c2d20a118074607500b49134840f41c1c0140340101c2107071401100d02050b41085c280d81250000241c10a03042040c103840c021036600400c1c0c7c0c9448281030181004040810580380380c000380500c0034158402645117540d501c211030514040e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 866157194 1250 866155944 866155949
    0x315090105011706060f12070b04180605151914030703060503100e150921180609091902160b0a0c0c0b0a02030912041502060714070b04080906030c0301 67
    0x1041500c1c3d5a080c21124002a01441010003c0110300b105401005100415210703540441452040003c0400c41c2e00c202c2e8060070103400c2040c0700784820010020f007a02620255801a405064120100b804082d045411203000e41e41504140c0c503400c0216500321414101d40c02c024011540100c280b1142d290715400020844070114112403c1c00342c005031402c122038201c220b000307003544142005c00021190f141059070002110050b01d42c2481e141c1c202c4003804101c401e00b0031004400203964000429011308110418005640d25030410748400086030203920094040350390509210715450459802d0b070104c8100c1c081c40050000101d10341c0c54411200982035803500d00a0b41004402414184659100c54180da00183e1060541c0caa03210303000001d62024242801d50701641c803015482010302d00c0200000c040c41c0569902202c0444002420003d018299004100c40f156401200c00010000d40301c003107420040181454942c1e1031724a80c1407080f15081030300300d900401009803640600014604 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 866158444 1250 866157194 866157209
    0xf041113050111030a03050411030304080d14030115050306040b27010e0c0304120c0606030c082103061023030f0f011203031a12071503021c0506031509010501 70
    0x3925155801543c040f4900c5180c50420341c800e00140302c907140301c2d810898219016140505801038003602003419075015400040003540016031440d002d07503201240ca400641c2c209031103800c55060101403200d0703028404e42c1c6010043c0200200e9417030380d01c0341d03c10002c061006000b8030084940200c2240501c032020b620f0700c0495140400000c401c035020484610a607111480c20f27285540380d035511700c403813001204003808000001c401100010038030f219040c05140106120403446140c002420f02d4168140c6e00c3ca8850b00030081080b00c1e500c00001501c1d0000d03c111403003041d20505d460110380c8114101d0b42c6014220b00c0901e00000c400000005500841007046000300300c1c0d552148000c0050380a100c1d10409040c2d00300803030f010a20990055481c0c6011b0384103015110b40358030004620890340a50000f41c0d400001e070400c011910410340e9070403859281025401c104070165540000525200310100341512007002070240d079000c0c045a0101802c041038810303582000c1c503020f17000b072009005108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 866159694 1250 866158444 866158477
    0x91103012c1c08130b1312020319050c1f05070906020a03050405210f06070e0420070302010b0a0f0303020c0901260726190812060f0411 60
    0x107a20600440c01811011540c051500140c1000c2d008407500b520082064284c18241803410000900d00007440340642c40b000000015080d0b28242a55402203065003c41558000c02502481800e05c4040c0d950180c21400c0294488640ca03880c00e04220b00000e00a4058a00c5a8003101d07143d0590b0065011b100c0c2c40d03982540e1503131240e03c16680c40702404000b42c040b90062200300300d40d1400c1610080304003440c100d04900510192006490245a038038100d80b140c00000421202c9540112041d83d415801c4500b403000804000f042222070008034050601094001400800d15000350071100303040c130024140601c0d20760343e200e160158030300c1e900040b0300501910b51405101e150016611741601d4107494840032904031881c0b00241c141c1e120401c00c0c107901030030740c000070709511900d003c2c0480b41d460180420410346200640d82402421211820b4510031440c0210101c0d42080039264190038034500128540c030b8140000c3d2010403d0709410b1750082c10040320110080d24403000c0c01040d6003849205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 866160944 1250 866159694 866159771
    0x301021606091506081203071e210513080904021209030d050109020a09090b01090302190e01150c02130603022d040504051b0105070807060b0a0e1909110301 69
    0x3d4003510707070600c81c00030184c0c07020035a076401040250044d9082440c5041c180d0041d510010700303085840d40d164520010417103d00702c84c1c0e010b1354101500701c04403101100401061400d0002d826a401d1921310280120402260981840e00ca40e41104c003c40010454040c2900e080d400166685c0d112240030705203e03003000e00005901c2e6141c000d0700c1d010400e80c0c4940c8000342c205045d40004080306001d240c104002080300201507269150944038004a00d0201803c840c01c00c00c001c0c80100301a409a00304641c00b00069401d203600c01c11341d2818503812200c01e03031800d0f1051924006448145c00296010040710042100d01803d043c141009840f9800020318214511081104035002140c0c09031482d002500c00301040d204140c0300c20f2003210141080303420b00211b44c0707405c002a00280b00403294640d880502842600e42000c0250007004011800007a03490440030a100c201c2c0c5202009030510b03165401e1004200d4248215032003901c02500802c40744c01640e80403600402c8071000300303541452042d5030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 866162194 1250 866160944 866160983
    0x3050604050f03161202211b0619021c0203092b20010e0102040b1206060406210b1f08090d080f0c1606140c0313020906030102160609 59
    0xd54240700c401c1c81400213a0461a00c1d20510362070412200340440c0036110300300307869002c859070400c0701c0c1d00c05041070b5440d801c2c82545400e04c0b00c207030f181c071448540c0031a040214004074a5000009056001d0003da06c42860301d0344803004142007070314240c11a001000b00100c9000000c1d0f40344010b03414060315007412200240d1103420100542500b000250800030304441e03000c01c440c1680010256000000310b00c0d5070f100043e4220303009600314070f0000b1000601041c50500d0781400d00d400c18421500c40380350a00d084c4000c1c0c0701600300741c40906060107000705260307015010740c403080b0540406807501404000e03141701c0e082500d0f0581c1c01300e808140e290000c92440040014642107084042d121a01c651301c0b400e000c01c02c640302c0102081cdd036001c01001034081e140a56448074440c64407409000c125080c60f10110180c00c00c0007052011548024420841103014030b6540c00042c42d0180d03420300d00d42d1100c3d130200740a8410000304000070513640c460841044003982c08800f06034064000702c41401e420402c07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 866163444 1250 866162194 866162197
    0x103060507180602150c0d110903161512090249151b05040f0602010b0f040e120c030706061e03021c05060a02090f0111030a1202040f03050604050f03 66
    0x250380e006030b211716014180895055540c1e40c00c90303440440f56042c10807001d0810195542c04013a40c402d1440800c1102843c03d081203180640d48800c80b8034080b141c00d012a12039500210301d1000f08004440000b60100c2d40e00c0c4d400b00a28035000b60201e1003d0790301d00c0c90001004a5074900c4a00f165403040c201d0624045280c030100001910b0307405282188141d02e514084840600c40f0b00c13403441d65816a030b802c09002240020040109480d845d032940d10304542c1403040c44107640290256410b2003950f03400c6548200d110032941a04840000320013107a240c4407403400300300b0049030361450f20000f007c40c00314100002800d10244104c00c1489695107992007040b4105845031810302c0504100302c14001460724140212010901450380d0505a45c151910780c0f07021800d07200c030301e41039a00040164460502101481c0b01c10001c1c01c007841d4880c0180c03d40c43d40d0744140c0903038008201808a9916280c4800c1d0112002003680b402004045034507400c2c82c6c0d0f101c0500b40e0782126544200307821948010300200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 866164694 1250 866163444 866163449
    0x1a0610110c0402090a09020a021e07030b01090e01020c070605190306030c090c050f0d14060f09010b0f0706060801060602011503051f0e03030405060601090512070b0901110303010306050718 83
    0x2074803000780e1000c1031201942110b140e240d44843c1d030240208200f600713840688042c145a900418101a4824645107103014181140045400043d0240045030b48440304038111064020001428407441a40324024021003030000050300880c0400035003180c0c4600138142c2c1d803411501c0e01e4030490640038250107e608510000304071845a840801140c00e840d440310180102504146e4a0b2460a801510142d407140c0c000b98242a5070f0f02001c044a40c3c50608998400300640302c150a00c4103850014250b6141403154034401180000c42003103001010054a840c3e03a4480014003001c0d45a25130135020f020b107070103280300541c0b9002c0c1c500700417650074102d1800c4039000400b500381c0c503019803102d00091520080d1750207540e031180c5a2070342f800803c2000750704c9140940017034085401c0a00005010318480d0340454803031800e9118844091074041800002c80c1c00e405143c40d40e5800c10401a6425500b642c0d030084203020110002041c855513400c120f10a40503681c0310716420440c20b2884050640380d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 866165944 1250 866164694 866164727
    0xe061008010e150c07080702102a0803060d020411161406062101110325111b0f04060e0109061212030218120309010e030d0c021c1a0610 60
    0x19404520716164281c01030a1700c0c2d00850506150000c0b039000305100241003d5554000741e202c2c0d5100d541000c658010041c1c10408010001e104000707501e0b10309150001a0003144101104d01c4034008566555102d030503984083c0118a1f103075080301070810024002040c06845000d0025407104a40c03001142d11441000014409a2034550110078105c10301d20146d82c90b0040e642c0d0344014980002040003231803245501c4440302e41221001e101040c203070007200b5100024010820b01d00185038401240d0a022203002c1900d5801103a02200010000084101c4240c1c1007460914045078000c2152209410b072109201d00344103940c4d51301c0040702d40b21381802e00986040d95041d01d00701c95500ca5001404c1c0515080141684500244001190045030043c4540c140c3d1000590075440d5030007000b00c07013504030124040c28500c0082e82014008006003c00244260110f40c012882082d5014038084060381020303249000b540000309904149105036050342c420000d51440c00130040c0300e10300c82c03134244004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 866167194 1250 866165944 866165983
    0x60309070e1326120c0c06011202041802090c0a0302091002070815160e0301150f15031415060c010c170610120c03060305060f1005090103050c060901030e061008010e 73
    0x49001c2e02016000a807178200c07002802c10002e0b00c02101002030780d020740700e86100f5400e0420144100000c45542500440c517501103500d010000da0b940700039050380480c903800843c0d6901c649040c01c800178480c0d031289941c0004001042c3d0355050b400515501610741101c1255a290b0141d555040c0d0000c7c12141072100301070f10100b842d0800c0c410541c3c2020342202900104010b1034500301c41c01a4003164105c105200e0720781c1c0c020032026480541c00d4903e075030503040801000f2481c203061480701e04010b103650700018569091605541310036040340e101b900d40e41c000308401c8072a800010150310105103605942002c40f80031443d54509841c2000c010034040d190071842c6201a40c0781000303800804000703c1415034582c000404a00706004c1d152140300c0100480e025460100000c05503482560000c500800300400140005900020307601c0b0f45100c1212480d40342c000c1140100d01424041201136124000c1100f4820525030741400e20003507404000090000e503111440e0103948812000398421320808 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 866168444 1250 866167194 866167207
    0x6020f03090d21030e0c01090f0506090a030804030813090b010203070b1f0303080612190f020a0f0305100c030209011d12060108030c070905100302060309070e1326 72
    0x1408866880214440c55a0f040b5144040d404000450203005508000c00d44500c0c842d440c120080c0007001030b400003400c02c110510b00346840c644608800e80a82402180e000807454441d598100a00004690142a5660720b03030700c84c540307002107030407056500b501c80d4060000845c44002030300420030844c01c180d0085003040815195100080b6016201c03000c560199025400394850002c10040034501a842c1c901003802e114051008418403c1031511303540e04012104484242200c01c0800119017000b02c018030041c5d03a000003080da0702d440e8041911000384000000801c5404039445101d860850303020800605c03008015070a03413040c40070b0346000440025030340c1c2580d0300e20b83d11401402d00c00b034840c1d0b40ca8402b05003020710b080c4080c0c03c0505203520205400e09045030820808000d429240028041400c1c060982003160300305001c000e115600210000760031362001c000d40780080120400c60304076070074007040c2101804241841907480a00c507980380218130b03510403241d540c00f200ea00925032034103070b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 866169694 1250 866168444 866168449
    0xc0c0b040b071101030608010c091a0c030a120e150601020c01030e0c04021e04030c0e0907060203090d02040b0429120a03111911131b05090d08070f0c06020f0309 71
    0x10303c40c141c00d41811b42d28080032614000910410504400c152030300494141801400c00205c4201c0c1c01c0155850b40400400b104683c001c4180ca1103040142050950f094110140c100941190340d8044404d110f120341c43c15140c0725040d038850149000303030240d0307901d040c010004601341d80001004540350b07072142c1030440c05401c01d0381c014415404940254a03080682100c42c200603400356000b0b44105890b4541400000041700c401d030313040420403004286291400c040a03480e406880f001c0d170f22072050541c800080d03441316040351100d6070700100f04001d0084405800c40402e031040710412110210498281740b103041808503502500134100040010000d181d50407200060322004994450203141c0028400c01400d40c611281c1a1048031002c20b010000340c10720a0413045c01d041d0494190819040d2829080b40b130078a90403000e051b241c0780c0c0d41c40c1407e00100300c880c1c40880d00100706060020f07204042c00b000841045449120303888241c41e165444808903a10700262640c10b415810402003142540f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 866170944 1250 866169694 866169713
    0x6120d18090221100b0708070b01060516020405043315031a040807170d0c0804031b050f1006090b0f1302070c0905130303140106170c0d0207030c0c0b040b07 69
    0x711803200401ca003103441c1d1801c1d045640000000325119400403421034200900c4e49d1810b07000d02030914100342800c0b803160140110403c81e200180c000c0d075a0303a010500740006040c02c00039101034080a1172500e902100517a4202c20100c04085005142110490039192a4404402200d81001e480c8054400d500c00003c05008007030000c0710740070004c1210744001940c20760640b1010640366034454031030360550700c0901662590315040301000120f40070800020780101040c4507007640b481005461550318038005152002202008500303204408032a20540b4003508140262911100140b2101c080c2100384082c0108140c24a80d001c0480d05000340d1606080e401340c21018050349528410a0707448131000100d030010b031466071048c542180800241609800303071803195010391382d0b950f506601d041001042d410312200341d202c0100c60340010420741c00300102520ba003030007089001c56640c0300b140b40c042c010002c1008221050325800e000095201c0507181650100e0b2081c1900603d000c910b580c0d0046a07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 866172194 1250 866170944 866170951
    0xe03031c0e1603030c03030c0504152f0a0512030103110d1113020a111c0e0105071709090106090e0a0f0f0908030901060506040311040506120d18090221 67
    0x11441028600d840c007807000300444000f03500988490030440b46504004068452800d280410700a0400c8100015030024400c482d01e040c0c2450b09a500048013860500604c101d951040e02102e5010240011842c02003180c0d42014850300413940100c4070980d0343c4026010920000d8050310f085401414141480a15122110f1155509000d516980000103d018440c0070a440e111640400e910080c10742103e1000044460f08006000014080244881003032403045424100156210440d80603402001512080f5600000d0451110581c0c2080000c642102e0303c01da21811440000240d01c0f0302450605081d10110000c5440b80d99401da0440c01401c2c152240c07800c400d40e641241d0f01c0700309061040848091113200126901e050040c00780b0b094a440d0742000b071061408220400000f00440c2d021783c03000743c0545010030725035622400242070342c0c0412900c81450041001da00041a80b20500c0d02407000e8188101e0506901c41d00050100d01503600520181d01f05d4800c44032400111401d015030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 866173444 1250 866172194 866172221
    0x230c0901080705040e0411131802040f0e19030e0a151b05100c020120071509051f06060f122f1e07030c0f020103020d0e030a0e03031c 59
    0xd840c0d505c1000e06441c0b0030868054815100440102906141c041c2041221280006003403182051441016a51107070b0000028030451b0390303c065010b400a144c2016204a01503820b4980c0002d1124115042d4030391640c04a0010f2441c0343c410246d4584080c4c0c0030155000d2800c0d140c0043d4080400f52000d040e02c0c14031050f4880740e44004c2001039010441c0a60110501324040350381d4104250180c01d50308181450800c03204400c04c800300e11000d4009855405070040900c0e8100c524048005004001801d0003800034003400315000e002404c0c0084206450381031000c1040300e02d640b800101c407034481c100039a0340024070001307a41c60841d1480e08007142c100ca60940c40705000240000900055000c0244058440004955064040d20203811f144140700c210070041e1619116980080030711034550001446a40001d2a48080da442a8180d441483c03138104100101800e0351483c0740d4a40203180d4240014203507020703009443c100802134030302181c588071010300144442050b41c005444004003002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 866174694 1250 866173444 866173447
    0x70b010e0a14010e19021810030c050a12140705071e020603040b04030e1009180203060f120f030a050408010b030d050316020c0a030c031502030705090d081b01230c0901080705 77
    0x207450207494070003403400d414074944044400350407c083c44042c191f650500002d152404120346c00303d81d0400100c030040507880ca024010b1500d0801803100528200000c240d806c50308004010200e80c02c0001030a0680c043c0d8020400e4031000d01c07200040280f02d0700000c2d0442c41c10710124001803042101981c1080c440d0070925141c850302c00200e54403c01a40a000000d004400c041000034902e0f030090041c0f52a26006620f1407928401089181180042003800f8401c1c91a509610319030038407502c2c00000d038180aa81d40e8003044580200760b03410a01450945501e00240c4c08283d2400180c4244c0b0780b90341c2c2d11440c1c1565591918071071000c84030b8805c1000d40c010403252003099901c0d00d042d20065881810200c628500350f04040300850080310844903181d02c1002030002654001080d2046040e00301c13000c040a070a240b812603064040d5000ba0300c500f40e4402c200d1120903006401a01404030f414080308800a41030b441d0320308600043e141c0b04448101003002528551040905a60080c00c0d07041c8075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 866175944 1250 866174694 866174731
    0x9130c0516060c14032205030409240e1e0c0702040509010203040515130f080d1b1d09060f032a1008061807090b070b010e0a14010e 58
    0x168070070031020078212070890b510503005041c1604031400c3c0b881c161203940320a0442c500380700745240218085900180c1d5100102d400030800c9010801c031005000248400c1c01410b40d11f01608a0310140c0a44582000d61040d80208040d01024020f03407107640700c001c0586000c8c00c85c503404440d141001c1c003207420001e0704108150150302d50740501401024054001a42d901d001d090540c1000242025907000c800c00300148503440d803200842e1940c0707542100d03801c3c85003440340c41c0144031407040c0d0100c003c0c040d0070074610202d02c0280c201003844000040c3c5404500040b00d5945000c080c080c05c6002d036101c120a0003141003404d050085000c07440d07002c0d0403100003880c018060300070560400c01c400c0810310f103046025441d091183d541c00400101d0708001929041c481c0c009220340000107000d540c1140090001a01e0718400c024410051160801240c0e580080f41031440201c20240203440700d618200021500b085131070700c01c5072040f800039100f40e1016400c2c407840a03000800a04004003500000028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 866177194 1250 866175944 866175967
    0x70801020a1d0306010503060703230403080a0e0c0607200d14070f06120c0315060f0201050906060a0509071215060e031f0e160b0a080c09130c05 64
    0x100015425a142c1c01c0d12010307075408030340301030728020200e60290304160300400070303074800040a64101101c0d04000c2004200000382042d00b08094255100c81700c48501400203040c0c2154416010320039142c014021951900c071141d946030041001c2c550089402c10080002c5070a0041102c4c95038214201e00309101044800210b1206d4104000d907040c21050404482c004400c001403802040c40441c400b00740c515000d005480c2c4800c6007101f0500507240c000d4858480d03c41e512032044950001c400e00e80d0719888003002050f100c0780c1010b030303c095803801020a81000b400070307060380703d4040105038844060810092180140c0094000300c14414400904000b1050500030171041914240100c1035141c07a00900030129244920048d020303800c90204410b44016207143e01c0d000c0c64580d070000c20040303010707100c4c0c0d032030801d26a00403007041105c00b20101300012010000c0400d9a050390322a4a0341e102d6080007282440b40368442c5601502203031104810300443d421851401509090050400c09800c51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 866178444 1250 866177194 866177197
    0x4060e19080c1221131a0307260c251205211603060905060915010c020409050109050c061207080a020408010e06090d110312060f0a0311100c150b010207080102 70
    0x22a02c0c030300700f030114980c042c100d8583c80c85170040034900e80604003c0358901456015110117030500302000129032080101c440049840010b02d10030481040051503e245180c40c0d641003030025000c40030644144a0302d0064440d004401c1a411124070b8501015081c0c06940700e600c0000100304e5214020183c400c0c03445100c3d6818401d050040e009043d07141030b179000078102c4107541c11401c1c2c0c29150005000b0300d41c4a45018940c003400c040c000307252000010700184d034845000b260080d80242800c10702070030443c0c1900480003007480703070302100c101c1600340742006000c3c00340482000580c0010800078000510840c1995007015032520b00625003622114994291200340d01c81e041141d0203c8103001556004114000b40051a4036240846403252042e41c0c0e140c3c410f1207240c0b1306506041c40401c0c40d035512650360040020780141039030300e015620300c1c0159006c04080e4a00c0d10507284d1b40c007852001402500800c10072079110b108200c1861010301840024802074400c00e0461040b40b80102e800c400920 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 866179694 1250 866178444 866178493
    0x4050402090316060c0b181902060f070c050a1409040305030a0914030a0e01050c0d030e03120f150d1e11060a02150a0603050d121104060e19080c12 65
    0x291082241c5c12103081148142102030030721100442e100351011160117010455036030700e950310408c410a80ca80b90001951a0242c0007407024100c000080440c00c10148401030700c21950283d0703d05c0100c1d41d0303400b190200485076442c215040442c190001c4d001030300c140015a03214684400005030b2590075100c800d003104204451000aa01c000b51413411103403c101c03200c20a4209207441803030888507070303000c503120107521400d0018161030f02000c0910700d00c00e006942c000f00c0c07021040141448e24040001c650792042e44c02d140710b2942c20a0742d05542c1811880c1d208026005183c040706202405843c888110f1001003d841c4080c40d160345c0160ba039140c1d03004107212805a03000344514a040c0d003900c51080c1c07000c0d100c1407001d4601707202040020400719030306090790000e003014048603072254414809415038503c16a8124000100401e0940d0000c6003d5078800065a0b1f086c0c0201605a40e40c41c019018010030000b40d00c0003505c0c1005240100d10029002d07031400640b01804500140c041e01c404014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 866180944 1250 866179694 866179697
    0x7060e0105040b0a14010f05190e0901140703022b0905150601030c090302030a0809130c03022a100216080706061401051e07020607050303040f06050a02040305030405040209031606 79
    0x9406100000100b0702072110302e605e4480c820b0741154507041a0281e03000943c46514040c1010b40304810b41050008500070041010700560040e81c50492000380c000e02c586401d9000050208020941c090700c40c0c800c0c1d902c0c0251613410041030358a00c1c095030308011a1000248801600e41ca45840026410700941190048110000070076081180002d8244e4100014110400c801e05004201590300000c0580d065900010101c0c2c1d2154000085840300750030700040110b4504004402a40960690041000340d10309040c0c0c1c2d902c0e560240704414204d0120000b0040c50b0700034003070000c100100d030f0b00610305074000c0984400d402c03621313950f00041d40e004980103541c00c681d0b071f490400a460000c203402d09640b40919200b80f80c005441048401c090008040c034011403c0030821804544520046807680c1f40c12104403920ba103081e18101300003042042c411a2414148070119041440702c2c0240c0d002c0da640540651300341410041880000c0d0400d10714154544121404980803170701d43c40303581010f0140b5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 866182194 1250 866180944 866180963
    0x100501030203060a0e03030f060f10020a1a0405510c03040308040b07020a0b090c1f1d04090602070b090c0613050118030b1f08030c06060607060e010504 67
    0x541c0109414408000c0c680e032030040c244140da820701480881103036071082d5a9a08103066864440100b00070b141c0c8a0700d11034126004401d400e070800d0300003a00f40d4420b440b03a56807000d0241215a9602c81c03040607503004141d60720074044c8190000142c3c15003002c941c010340208000c410540b01a00c101c2e02803c20440398402101e02248400038050341081e4003002e01c01140c9e1543c100303a50018151080104068102d034002c0c2d000c20461381c428881c030a0050342120306011582410618292030f8142d80000d2132240c007140c0c02d0002c8030b4121000342800b030700551f124012a5042040d040c2142418040c04a9100c3d542d03400c12030004145101500a043c01060598250314010740060300c0c1c406074889040c400ea6040c00a410f11000d12030801042d60000e191802c5080c80703c45843c1e2111215030002882c0d03c007110704200c0580034032441404541401042c0007405030340d0b0035510781c80b80304d0015160320725044040091903d00b8100024000103209220000700c01907401d5105007150000e036001c40d0b801c0c07030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 866183444 1250 866182194 866182199
    0x40b1f120303110703050714010221010503010507020d1e1e0302130f0b18030c211e070509060d0b10050f55050108070f020c04020d0608100501 63
    0x906115420014103c10b000502d031100648010b00f00c1c0c0119100107101d04045030b9840549542901500ca84200500a00305034450107c44201c2c0f411090160b603001c0d41c6000005103400c2d1000507410140242c40d2960198150040b1514815001c0e800625060180312056418541ca001c24060340506151341c0051721900007801040e0302c040c0d00d0b400145a0580b442c0c0501600e240d80044881914a0b41c86d03000780d000880000c0f9050481d0341013020b0340718100f180c03400c210144502815014510800030744070041c6c40840c2481d50f4010004042e00c26901140052004d0300701411180d4011900a140030000c20f09035075042d011800031508034181054040c0c04020b01d05110b11030401100c001c0710051201d00c6d446030102c00701c80720402116800034103c1d41e0b105011024168402241d034400040000014448004581e220020702c2507038000b03401800000c84c0305210700c4940507070030f55070760203404030300d070b003401000302070340003040107800003503036082c000500d4101001079486d00050710001060640c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 866184694 1250 866183444 866183447
    0x161101061208030a0b090c0a080709210b0c070b01140a05060a020114010f270605061611010504081504081b0f16050d06110f04260a0308040b1f1203 65
    0x4601171101070141000d402130140705040c1505940a0f0101464001041e94078102c04441e403005a0344804140c500d4146d541c4a03542100341d14500d1140141a14100703500d0b00c0002c42d4841c402c3c1d0101404050712900148182e18088850f01c01c1c6a070014080482151110000b94090707020140e01d501603903442c1c20340101940f880c00714500401c80e140c00c91203c54034090030b110000425480c2805580c15115404254a28540c8108003511024200d15210944000e0503034a051002c0701c15241a82540c01500c481c1d03200c0c84c21a4165116480982039110b03054812a0780114040c0c4201c46c121030500c9020185a02591448200f4400400411801241e8040241460012070260658241911061105031a180b072000c0c12268428000502e001d50780403030310b0440c06003901c0042e0703200b00040c0000d41c05404010380c5006e60380c4061048209001c100400f0350b0350a90000060204980e080050f010410400c2140e500c80301c0b144904c10458044240c28164100a0300050002901182c209041c103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 866185944 1250 866184694 866184701
    0x90d06090b070210200a1107031b0f0f031112010209030a1a0a0606022104030c03050d080a06061409120d080901060b030c09060703050c100207120305161101061208030a 74
    0x40c00d07203001c03290710010300740170040c0510540b0804014882ca44403040301820041206a00a5821521056603007408103000c494800701441410380740031641c90040780980e9070a0301c0c00308481c0e01c030030541c50850b040c0091007085002d900031015255402d000102541e2020b00640790041c1c8034000c400180074480c064020440405481354020758644030040c00b07440c0d00001c529841014080d800f0400a05200c0007101c1c61145400082c003130200f203c800800c005001803116811080c80d241d4200698a0f024084201d0307449200f42c4000070f070340a84039a00340c0d1161004010414003d000c0e0034070034070f41c03031700703ca00c3c006070966041c0c0000c0c01d9204008030503000703105030405040c0d0b403644036140d0f0604100c0c41c08280141c0f071016114080005900c01094010740071240c0b03440d582c5054803003010a010340d090094001c7c89050f94100c036000d0400241d00d2207071107110701c0f400c1e03c015500100d41ca80041104e8440d000340c0a0b0a142d0b40c0ea203004502103000d2804d802c6064803c140c003c2d62850260000001d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 866187050 1106 866185944 866185961
    0x1011031c021216050702010e04060b030f041704030512160c060e010e0405040f06050414011e0e01050907090905070f060f020d0e06090d06090b070210 66
    0x1408454002d0040b42c890b000045446a4601d95a90307240486842104000742c3c04118420056000e100a00b20b01d8002501c00100151190340b0250a03500a031070340c0210b01900c4081104000b14441c102090400d01c0741141e00b49031950380c07003641c2d480c21a00884004400864004406401075040c2c048081d004440c40c00704582e2000302610340c04840d40c0c0d035070008803004c50f0f01d0a5030400f402040e0061707a0100f001d08000d0426240da00040002400807101002006d003070303040702d10090041100c100140c901c68080000000705030070032a00841c107806016410042001100741c008203485084500d0403e010451001d071740790260410225400000604403403c1000c00c0d5194000940b4803850302039021502c1c1102211400d40340911b291051030360161042201542e641009440680381c07902c1034201048842c1c45a1b641c00103807404440000050340040c002040d2081c4178004c0181e13 = true := by decide +kernel

theorem cover : BRFrame.Cov 866007194 866187050 := by
  have h0 := BRFrame.cov_init 866007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 866007194 ≤ n) (h2 : n < 866187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
