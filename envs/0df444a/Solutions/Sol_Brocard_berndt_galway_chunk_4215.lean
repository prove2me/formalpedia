-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4215
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:17.132702+00:00
-- url     : https://prove2.me/submissions/bebb5ead-6c2f-4cff-ae1d-9f42a9d1bf98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 757913669 ≤ n < 758093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 757914919 1250 757913669 757913677
    0x12060d05120d062102130c020601090b0315090a0605060d02030606010804031e1e2a24051b040f1a07022d0a0f0e04061407020706170903 60
    0x2081d2008002030582c501d19840e031154010f41184080c3d400c1c2030000c0d0407441e142d4400b402d0140c0c801d09240c91001c410310700d82c0c0581c941081c91036014080603440d00d030150000e00365120403a1380c10300405006400c100501c0c6007052140c15a18024480484503003000c8040390f41c054000d41c0200c0400280101503100000c0990b000482071800132251740d00c1e03040458803454410041da1107a015090080011680551500620303810341c00300d18840c218125040d21101090281004040041000c4061510001151640c1d160040503285440c0f0303032141e155203000718907907140c0705140d646a041c04400000c5100b0800310303044c50000c06180508160080340602103910502a41410071008c0c810f114074400b05070341e00964094902c080d822000c3c07c0d05840101c032541d0003004044058490f101c1c0d03261181003081150300803449510704030300f80781c1d480c050580020b20070b541c031036100e0022890200b09185d003248a40c0440d8094107246090070320050008855040c2072180344503e4003441034040020041b2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 757916169 1250 757914919 757914943
    0x30c01050313050703051c02010609020a0e0d0804080303010608150a060806041d07030501020406020f03041a0304020102031c0b040605041b030b011214223305040812060d05 76
    0x124021210710f02d07055140402c160001882c0313000c0e070844c10a4404451110103003c070500d40080c445a515a00c0b510100d0207840388040009a50b101ca800703d508003d10400342050003441d49138549500c1e22070780b500c1c1d54401c0e440800010000420000080c0c0c1caa00d005850905c02c5402405107440c181006006a001a1480c0e1145a0b0b80180002c55600b8101c3c0c500c0040842c81030340c4011b603507410028002d401174400c1070003501420001074503480300407044905a8201245001c103203154a185840c20344c200030007c070705511041244040291426400080310b8003020001300b455580703c0281700644040d0b0303210300e000b5803d080c1000b02c1d2114410001010405600e00010060400c42c0101c0d00c0503408400030f00424036110180006940c103101441c422482440040049038111510301d04080d910680a4822000161030880f1402214203286561140300c0508240c00d01141416003262410b540449034400005810040428807800050340a01d00701e443c141c40134050780f5076580f50030302010703c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 757917419 1250 757916169 757916191
    0xb03040825060e0a0c0b160519020906031c0c080412050a062016020114030709260a031409180108010506120a0f05030d0204560909071d030c010503 65
    0x16040914100306401c0001d88d801c1000c40350b05c03103040c80c204e025182044034107030300600c8480c000401c58100000c40404201d0020296071441c40b010004681900740d51804603910542000001000c01070450040052800741c4003502d4501e0f0203103481800c555046030b0001208081c0d6440e00e1041c85144103440d0340e203000940512828442d80300488005440c42003140d600003001c000e0154480e03200c0700078401d0b43e8a0b1480d03000409284400d1031f0400c0c1c0203030900045a840b03666040c0c00a4820042030029000314034400c0e0415800c000003441201907100750b08800e02840e001000740350710034060650401d030b0640341201c0ba590208003094540c1c0c2c0c02c4402504250b2034103904420400c0030000c036a6000803225007107407503a40b6aa0384026440c4040020110040d524030620382490b04421030f0000b0501c8100131000d480300e620040003d081038514660b4003001d013407141d004584c56008006100e0750140e510710a01c450302e080349810011008006600a82c0310200079a0703183d8201040340c1c0c200ca200c01c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 757918669 1250 757917419 757917427
    0xe180712080906070b040c0806060f091f03051903170112080309030f0f091003050709090e07030212070501020609030403050d0c110a090b0f0108060a0b03040825060e0a0c0b 76
    0x400f180041c41071400c0105500c034441c080105016900c145038054449400548440762501e60410016181464515501c840164041104291094800c0d15010358907004540401d50f0307512228240403c4101c005a04500c0301040d604155010480c002841c84a141301840c41d41880c42c10b40390703000400c1004148500000109510803404c10917070704014400c1c000a590380f040030558482540041ca0594090080045000451070090081310f210b0030482d83c40896462524501502070b0843c0380c0c104803603008212002c1301580b0380740045003642c1d0402c00185141c1346048002854100d0040022115030000d02050000030700204807101140e4040c642115845007604203000e20044140c003a50740000610000a41907440d50411059103001f183d14440903500340005492401044800300e81c0807869072028030402d05501e02071174105024000250038582229040020101002c404090105d4881c40f00010480035018034904100ba44024009514141c1c0d1414055031150003041c0002030041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 757919919 1250 757918669 757918687
    0x90e0108070e0717070e2706060306040204320a03030f030f0615030f0b0111071a0f1210050628030b060706060302041b020712020a0509010e18071208 66
    0x20511140302c11381202d001406040c82c2001030b01c81c00380242c400d030144100303c1e41c854071203034412618001100c01c2801820b46503100c80811042e9440205900e5000382e09010125481d112488821207084001c0d641d44100102c41c034440701c0000303000206500c03401d560702c02440003d81c003240e10394001056040c0810f440304c1c2c0c20709603030250440d500003040814140e10200d640b40d41c503400040621100210401c858550000112a992208500200c050784065810007a4281d03a550807002840410340450404112039107608141e404040351604141c02d200601030a0b01c2c3c40c828400c010407084518a140c40048001d101c061350306a60147e00ea400c4a0071841c840134081d401603030140400a00c60f6607503d00e40e1500c400180f22500080e8015441c0002c200c0701c180702e1100050300c0c42c800341c00420100b45080c800503140282c90008980066151000040503103030344001901915242410b110580b40c280b0341001d07440041c0e840314104da801081d0811a06240442d9042d04640001c20b0590b145042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 757921169 1250 757919919 757919927
    0x615150a0c14032116050d1413050601051c0b100302060d0c03200403080d0f02040b0403140c010f0f0504150e0310020306060d1d120a090e0108070e07 66
    0x20101c007818546030707038856a12058001c0010070004902600c0c0781541a0f000e80364480c102e40c1154058180a40c5680a00101e070094000d03007000c400421002c20354480311030400c030f07a8400c140e8800d08000003076100764003040018088240901402d40c1c0084111914109840e620b411500d0007424400c002004503101d5034031981050301558020344010758914072250078000900b1441ca5502c00240703007001204000031702800d0312491090004070380d030501741541c5403c0070a0b844000745801d043c0e030701d040c40300d00800d16001520080c14011003240c1ca03140385051a0040c04031034602c0e802290000c8051528907a0000030302c841a00c0305280c07070800c1c2098068252201e00c2250402014808040e041c01c054a03031000c10301010340c500750181c40c43e01d16020490000c2e130000740d686a5004034140004041c001c842c0e40054080b021400380200000c4c1001c00302420b0062048041c0c440c07100006413020400e801c01010002040c0d1501e00c0000d40d8908000d081c1c0302c48090158201d1510f221010881c16071103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 757922419 1250 757921169 757921187
    0x1090b031e06061e130509030712020703120302120a270501091a0f0a0f0902040906091707030e040e070e09030c06010905010e1503210306030615150a 66
    0x403201210702440c021070500e40c1d5581c003119042d2065a02c80358100d012042641001d103841009049004881c1c1c0c025140d40c01350a004004d04a944401e201080100726000004029040b40ea00500060350540c01c0440001403031756192018140104035103602c80b6008031105900a00c900000a2448800030211407006401c462030220800702080d48800d226040d031120400d24801d8019401c0303030b100e90010001e5510101d590080e0a44600c002501c5280c00d03401c0f01d580700240c56000030f40e4443e541e001400311200d0713070408d0f00e45558911440081068030200c41009880c81d400450070702d49503036401400207013840c1c1030600035511074450a81c2c0d40d03420021880a40f040e595441c48510740403200c1039484e08402c09802040c8202c10001800c101544a640d042c0d40040000080317640c1c03204601c0f100032810303000b402d805110f82010709880040c03030070741d01c5a4411400c000903920b082c00380401d0324146005d07010580b90701c2d5981003240265129103400d184011954111611150108415960490 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 757923669 1250 757922419 757922443
    0x2503060f1d070e0904031416030e0a1707091a04060303080a050609060d11030f010c020a061109030c280b3112060b0a08070f08011401090b03 62
    0x10003003002249050080186540556012012145035620360000715420318020003c0d5070490504e0010502091007039034600001407080301d126107032640d600041030203018840300950005502d900d4a000d0381c50403000000084c043d185610503035081801d01c2c180c48801034424107000680d60078030805e030420890407a0b940e6100c0280100035059072030801134804402241d0b13000d00946080300155191a144045034081d5501804400b200080c13541c0b01040111100c2440d6414800ca040b0409042000d000b01d581d0000305038040d003890781042c58098191824092002c010072801e01a07200ba54a0000c0c0e60210700004903805103000c030303100f070640301c005a418950380c0341d801c000300010a402c4641401050094460848043d00e0300201c1d003000342c1e40310840d55541d40c09000c144100b19118011950002d0180683c80c002500a441c070006100094554800b42c8c254214010810142c045490100018260407009019008903030b80c050402010500802030400c1c2e80320860b00e10b60b1806c011882c4640d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 757924919 1250 757923669 757923689
    0xb0f0a0c060f0203091603050309090601050c100b01020c01030608030a030c0c050115060806090405060408090301180b0402041b0c031b080a031b030905031602030a0b041406010905250306 82
    0x204104100196104950f204606d10884840c040c03040c032050b400c1070890f0f41000c051410180401c0c1001130003400603003814100301c0d0910101090260074010901d03090308114001884926070400a424103170f81c1c06185040c036140400030002280b022007145d5409007d4a0000381c43c1400300710030703107081741d00b0400644290f10b0120510b40c0411240d82d054241d134015120140103585420400005c01340844004000d9005180400c0000e82c101c2d0180018a400400100740312101c100300c0c1c8130300d07403202c10261f6031404804280404c0d8140340c85410061218000810300f040c100e8035029145200100b0b0040c20000000448030300d80d1121a092204d456000010b1592202c01082c014044c1c070210102124080452a81c0c003042e600038803524060640c08005182031414500c0703191312110305500180d0f014040c0d0240c903c00640032404880c4210301c1070040c1c031000c540e584046454880141c01c9815428a02814054051001d071051410761a54004402a041100318228042c009684c80303e0145 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 757926169 1250 757924919 757924931
    0x3040305030903100908120c09030d02070e0a0207030207030f051011030a0c030606020a1e080a110607030b06040b0705100f06050414010b09100203070f0b0a150b0f0a0c06 75
    0x1012000b004000812400c40310a000c80f0000c000880d00400c0e4000c0101c01e0400c02403051701f0300e8505039079014031007041c0c960030584008080b0b4180200703040c02c480160005001840902007188046410210700b070310860404000f903130040d40e151031a0101800c00745410504d6420804c00708922050884d146c1300c103001c030310602d81d285801d41d00180c0e0a00c01e424204a165101c0034440d10a450131503101e94010b061540d1a611440352807110312100c1c3d9102074000010314041001d4800500c5851100d03900c2080820041c440141402e81c058900d800305401c02c0745214490f48c0d800e0554050f01c0380306a44550b5a455440d11a240030540d00400904c3ca0034480700c84203103c082c4c4c1c0404120f0707405650070f104a88a94140c0e20901009000d00c06101c4001e210110040c1000d9103c042c2046850040b0780c5800b6031381e114000000c000c941c0858044841c2010000c0f074000c24064141208224408041d00d6400d2001c48500c90080b10b48608151a0100e0710f24501c0c0c1c80f40f02d08a500300d801000030050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 757927419 1250 757926169 757926173
    0x310121401140105010e030f061314060108030703080c030708150127090c08090706050a11060c190509030d030b210a0b07050a020c01030216060e0a0c050d020a05040c050c030403 78
    0xb0403d110756804101c01d035101017020304010500721095042c65020708050364441007840660318030044141c4407e01e84000008505c0420444180078281180c0196160445490700401c1828002c3c15011011424003e10a0180d0060113050b000324030144440404851500100c031b000105a4400410900c002c40c246e02e42d6803024400303010b40302c5401e0113000b201200e00c0f0981310310070260f403620110b40c04120704200440c440d0010304081e00d100c2c070f4144030007200b0907075491510308181c0350030284a500003189400c400c4080030076a51640380d400e00c0e43c108006080080c0d101c050300c4102809240e207035032a0001943c2c0d4070742c010002560607001340440c0e0040181e07040d81c2c2d07407094100300e86658041005c607055501400c141c902e540d44a900612840205800440c040c0d04541c0c2501103880168021400085244c020f0ba480e80d090f00004000c942c544e81005d0100c10301c2d650025008010100704680580c0b505a400317821380350240c1c2c0c0421004000305044030584036500d8103211900000c100071003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 757928669 1250 757927419 757927451
    0x4021218120711090703090c08030a020106140f040b0f0604121b0e1f0b031e0a0606051204021206040f06060e070c14010609020d060801050c0310121401 67
    0x400c49500908860459050074400072680c46550300140030000400c600303540c02c3c0740001c0002c0d80981a0f15010803240c0956498881009068104c034515800200b111040c0950911400d030090030407411480364003080d0004100c90b00d1200c4000750040740c40b84691441501ca000c0c0c022121000940001d030b0303496460007440da0701c07420080300300e03200c0028951407070042c083d01c2140e0b015a2000342c420000e0f9284d400d246a11a4860021020000c1e20080c0000b801c11340c04010350300c50700e40c0b4101400701400721b0310f035012424030090183e1a6603251003c1809101da1110503107000415a41d03007922144c03200d0000508041d09581c4001c020300c501002c12042100c4404a044868031031041405129111502510130600c21101040000c010100d80e001003140d001e030b10320b1034200341000019540e48402ca540141da03c100081805603444000401066800340301e4641d1098038802040e0450606d003202000c007148511640b415104490710a40c140310408040402101a4030020002d4070f418600d030903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 757929919 1250 757928669 757928701
    0x120c03061512070302010503191503030e1002010e030a0c0f1e02031204080c0d30111c0e01170103050c01090e04031e020c0409050606030106060c0c060e040212 70
    0x79020311a8500807005000c4001215415070341c5c16100d081c2075580d0070201820440c4c008180d5154584c6603895402c800e800e00e008070010b14001c1d590705c1c05428824090015003d0000f69810440e8508984180746902c088159008200f142c5041d0604428038149180c221001d140d02a20490082e40d90041d8864101c901d03d0b030083c07007030303040c1c80354a0043c0e00c80040c04e0090788240380084c3c01c40081c0382c01d14680011004c02051291405150701240c581940800401304528840065034000c1400c0c4070380c0c1c000445c05041680200140b41881c040f900320702c480c1d07500e83c007044240701d00c003100c3d11000c1c0c0c055855600d0045128203840401d40e500d04000c4e9403810b550b11001d001c20010400400c120b40483c8107a4403c942544440303001c40c40f80300f81c01c900b101c92840408214058020301001039599805a0303031400740100000c2c003440c00e00d0700403d821101103500c03550601503543d41c0400042ca100210404403600c905214000b85d03003030740102d0040e101c0d054000c0c1201c0b20700030401120b08038415220b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 757931169 1250 757929919 757929961
    0x3e0706050108030318030403110d3905220f0219020703030801060e1f050f070c0f1502060a0f0207060603120815060904110d020c07080f061005120c0306 67
    0x81c022071140303542117946038820303030101031305150000e80701d03808a00b0451000047c132403003036480106405089000d83c6518580307140514180a10328002c042100102d011007014190494852006082e207140d0b081c6490903454a041040340c0360301c0b1b0411072003200c2c1e05540303405680104d00d000c06900c034a80251101c000d804202c0224078600d0001c28070034454060716281400c0500080040d1f100a0703008071841145000d03d0b01000000c20400840c0311940c0d01074001c440c030548414124074244000900c00300c0f925041003a910307515441280000d03500081c07a580000c1e0420740010701d01c48240c0c94401a100b84030019000b5400d202c0f000040014280e0407040459440c0c0e9003901c1900c665040030440800c90409e545e0040052109852502c0c1950283c500c0d80ea5524146140008140c442c0d02031f40c10140302c814564000000c02c110480007413100d40c0000741e20101078002e0f89058900500c8244450090358041c80514120360020705040060054080008044940300d280140181040046464034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 757932419 1250 757931169 757931191
    0x506040605010e060105040b07060b10050409110909041407050607030f1b05031c14040b10060c15110c0718060b070f02010f140706060302043e07060501080303 70
    0x64044603ea03003035000e0001659103514041c074260f41c0301c08542103490241c0e640c0e5500c500744030450740e40d14650162604907071075054a81f440c08908604032080349051020001007000003142c256200c1a00942c81380d03208074418418070301c00c03103100c2c45c050141d005a5003004002a000c02416045040140007444582c3c0312074a503850602c62080c4412038000003440740c0d009024400c0c2c191840344c0d00e141c90008030300d07001a14414102c099610351009079001d0751105191420310080d484401110406890364ac2040e8902024079074a8100720354130b05a186e0304956441100c818502c25000c21136459001041c100ea440c540c41c4e102c6100d44002243c400240b8912b014000140300e01500c00b5116413580100481d801c0d0380654006442601d0608450070410440481c00031602c08981c004c0e01a03075000b843c00049640c154030520040710075050111034a04020049004a00c000514040d24480c0740d40304103030300204184070300c4003500450900400d868104400410f016500001540c416404401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 757933669 1250 757932419 757932421
    0x1b040605270a0b1b1006060305010b0403080f07030309210806180412022103090c010503130f210e090112080f211302090610090905040507120506040605 67
    0x8003400704480c224404941121600100b000010f41e404081c0c4600d0200ca030400d41c0303a41c040907209003410b0701d000c02c0c071510b00e90360030080c0300c0c082d810312609000d440b1841004c1d107054159111402c1c94041c2045003594100c0001e1078a00301480303a0041c5031080d5000c2c8204078990b81c07400398800b1060002c0012030000d0b02540c000b80703862a240c082010341c11412080e100c0991074a0b01c0310411180000005c005512031003c141138001400a09503000350b00360641c054580c200020710700e0504d941545220704001d801e000384a52102030ba40064001c47d401035014800c0e614034602031542c0e41e0907030016081c4140317032602e80e07100c1c0341c01801003200c28408032078190b0260b132281c05c0c081c030380d039a69103010341015005d1007500703d0081900700500d2030480179080000015503280035500c040da0201c40c9905040e0b00c1d0131023501141003203000030350030a0085501c1c03081905603c500030f00364103c51003203042203070320303240400e050042c180306200203000d0320381541c40304801c03c0c1080c42d61500309490403585285880 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 757934919 1250 757933669 757933717
    0x8310f060f021c15080303070504060306080102090f10030b060313031b110108150a0605090108090c0618040219020f06070804020d0201110f1b030706030501120204051b040605 77
    0x12084403188111169203150401002c14140f004080c20798010001d192440004180c81a00308065031040c2d0060340c03419512424010010242c03607003984000701980c01400000c3c0b1503036039400007505140040c1ca5010400030103220850203480520710f8603400240010074440001c8045d41c80700909070094940c540c54010114006400b094820030140c4801c12a00300b83c62150310804030300390080b0000024948007174509000800c88545540410003050000804010550b0024095a40601c00d01e01030591418040042150f0b0f118202c1c00c40407440001015035a0b0350340319810740c3d0b1442240b40c801034004e2101c10020750358010200910400303104071000110b4640c4111049485541e01426406080404d076005681c0e1114002c0180201d000d1410101c1c51104200706d80507207050000c103c0100c41d0700600603d41080e555403c880201410200140031141c49190320400107503061750000369903911600103c019505541d05445e00200000340050710591140281900e24540321561107640002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 757936169 1250 757934919 757934921
    0xf05010f0617100b030711010203070810050d0302071514040816121e060f2331020a03020604060804020109090912032c0f010e0102090108310f060f 65
    0x72500f0420b00159243c0a100382e182d19805550003400a0414a60105040482c07a0070ba0f0011540800018158001c11580b1101404603c0080009643d294000d20181d280252250f0716801008043c3d50904200d60f0490310440401e400c11010106040c4c07180e45801d0aa920b55a0b0040315502070424000042694565900341400b2143e201011405095a9040c0300881044070b12003918210703560300c1800141c0d2014021312826040c900c14031031605141550482200002820b503071115054a032417400001102c80c0844505049000d4072034000881e480040ca0040840e00003e402150108001071402d0b00800d40034000c42c802d0300d4424085860b01907010840b14618009400041d00d010845110380c000e40c00380c04110000d19004201c0202142c8840c1400c03003a030034810260b40541039181c140d0308207110f00000d18590384020752070b12030880f0008200040c0500100340e03807094001000501c40c88502441c2c1c0f50b00004030607600c98002428000f00d180b10040d015140c0b0360403d40f82c0d2000c0300705 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 757937419 1250 757936169 757936171
    0xc060905030d140f040b07050d0f0c0314130b0a020118030f0c0204090212030702030f0a0c17030d0c11010b010206040206180a09090605091c050307030509010f05010f0617 75
    0x1900510302e0690780301048840c2c091000c034841d01070000300030540260582c400103001501d02100b041d40c0da51808e140441c42c1a040161010420502d40b000c030030001c0e481310008002031781518028480c0c4802101520702e80c81880716080340c40c80324a00008000342a1000b401d42480c0503002000000341c1000d107509151070b403480013170002d945504440704507405200e0700c21316240054000540400300750302203007030704809010514155002040e120218a000c104420b001075264000e0001d003c000c0e6980b12000f803050088402d0741e00d50345042110300c0d000300181e40c400b0a80801c01e00c009851130401808600310001d0074466542010000740e032550001480741e0260707038054001e84c42d1000318444611110030074001c440e4000d010190001e040d40c0700d4000da024003801010001002e0501c04107061a156036000728100c1c2030042c40308050b1442d0803005072944060541404203241c0d8803404807034010302031040c400c2d42c840d00e0b0400100324145190001000d0b03403842e40710600404c3e0400d14100300720340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 757938669 1250 757937419 757937429
    0x18010501080a05070c023a110f010512130b01080a0312050601020a2910032f10111212041416030326090c01081b040b070c0609 56
    0x195290205000c0c2d40540c1c0055072040c41480c0000d82c03096564001801c940c1414101d106800b03145a0071080c5041050a00c007408488541c4003109000e80d68840342d40181120145100e080062154100c03a4003070720403501100e1100024403110328241c0b011811500c07541d00f0680b03450100400204055200081840c45190181c8891501201c3c08035408c0c09058003d214504600800b880c6400040040c0036042e113600c04100e500c0c039005586150310403031010040140b82c40801882041012603005078404c801e581011146001071605c1949260340c20b092526901d030010f007090441150103512001a00b000708000c429250500001843c0041c18012010714044114028010800240da03009008a00e008990b00382d07010032200c000548190880c540c010780100d84ca80c4e680641908060714080018043c00d080140941070404c9001d64401d26010001c0c10b03c414030300403c3c400720b41410000c001c10054080d00da621a00c6504111098020600480307c00824a00100300c0704d0164141a054407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 757939919 1250 757938669 757938677
    0x1061e180e0303160210020f0405091302060d09060213030501021c0b0a12050a08041e0605030708010308070c15020309090f0403020a0222050106030603030e0118091e05100518010501 80
    0x41c40303000c65003003031041d40132100b07081d8458060250320a0300c050010340901294a12003075125454401440a1580d000301403c00343c0790007a103020010380d1003c05568211b5407034000058440c41034039150000303100c1e4503040c1d404080c4410001081103c150000e209120f911380c002d50615006900d54001d855a00601552049400344140b11264591440e85401400b640c1162a070f81001e8560180c6c41d84290400300004601400710311402c00b40c5541e42d03004020b1490000e01d98501300f0340003042c028040c04002c0c6506000512441800f030101c00b0500a0601115981100c11680d80f000c0d550380d0051601901550006000401802000070381512a980540142009180650801c940004040780000324000303240d01c06c5205170014440c0c2ca010300643c1e24000b56441c1076040150003181240d0045041010079030300301911007540b9510004481403c4000328410310f80e4501c0540c40322108016040303503407804042010102000c5036000803075000740c1d01c3c100f1101021643c1000c0c11024041c460105d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 757941169 1250 757939919 757939921
    0x40e0c040b03030720090708041709190603290a0b0c031909030201030f0b010e010e032509060609080303130f0b04050a030e0604050f06030901061e180e0303 69
    0x160410307820a00180c1002410f483c9070981c0d942d1741064081c200748a64004a01c01c501c080c000e41401542140c1001c1c0d18100100c0c1403400b90746100c0051141c454008028001050260268480e81d41c26080c441c41268441c5d080d5844000c001e006010042c60503441c0408070b0f180ce480074011143c10480c00700040e0221640d80c4c146105282c0781d6010181c51002403004010981c945640740311415150301d610782e02c10b41a285940001010390300c2c5441c08440300c1d4a0241a080c0c01c2c1c0c3c0165016401110a00708080c000c0c1020300024142201c400b542c079003410158220280210814443c42d0998a100340b04009880d115003048402d2210741c003400710640c2c020030124007000742501e0342c4903105204110007146951a40d5462100b50401d54084a180d40022505402c00d500b205260800340c200352032071400d0510382000030f80fa201c1e2003401c0301d00900000022410050080d001751018204a50342c203d02400050400e2608510360300c241440300c140d41d900030840074003030b00440a0350100d07a030045040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 757942419 1250 757941169 757941193
    0x909020711100807021006150c0302010e030d0603020a0f031518120f080702010b03070515090303070819020a02220e100209030f1207030f2615040e 65
    0x3944400c100740c07204005000701115603590342100816802c03143d0707120001e609021102a141101c800c01e112102420094180104e0382d4003e442e0200694620f8010066002410181e0042c04c0b2040c1642c194080011444806001508030034203d078400d50b0782134500c81d9221103108102040c2d001c01000981c043c80ca02e6400c2003940c20450070156560b050880c0355080e595a45290700707401080303001182d50000ea01d8907042c0c101c007410394044101e000a20600400400103501e9a4140c00b40510401d8007042038041d084403442680d01c01c880203030440e0382c0c0b000c40b4101741d202600300420040d80100d0050510b06910701c0400c0f0b0242c150350103408000030100042002075a0680c3c01c216083c00e5965007030394022070004021610344048105c10050381c1c0d070f06400c141810140200100380031940300d400e08610188000049603c448c1d003529107100c42010788101200c400c21340d0600141950b480000c994002001915071501400d14407040c41d0401140c0c1c0d003032105a94112070040142d030406031170241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 757943669 1250 757942419 757942421
    0x31413050d0615030c140a0f061404031e0b100e18150703150b04080309010c210305013813050411030f07080906011214010e010b030c100909 62
    0x1909910541d80411003c01101050b440401258415984031924000030081000303012010080301e48155a5042d005041c10416000308100d0320540b41000200c008202c085000c00e0103480155612030103030540e5034042c11240050305a040e005641584065000c07500d61580501110b04079101400703122940e030790340c00c00400500c2071541000301c00c0c000c03c00c1900d207601c02c818003180300d49031a4070300150510b8554465200c0100a42080c0004c1004001c244200c40001007581c49001003440c0c80d4040f4001da2401d00242c0310106e00080700d1540c0520103059168150300440d058511000c5008090700106000caa50440141802d005092025901594841c03150009008450581c170361406503a81e2440850b084511500d00c0e12990003000c000e00c140c40c00f905403101c0d040016450f0401550a20281042d2a00b4043c03040d6034081461500c0076080062180182800c2d0304800d00070000d0b4400303145000c0c0a4240000c449101c0d0060407120445441c00d64460665450250340e05044070341031140d420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 757944919 1250 757943669 757943689
    0x70f12020d05030310031101020a02011205280906140106051e04050d0302012013090207110607060209030106051c14010603080c0307030210050112320a03141305 71
    0x681c00c0280c1e0162800480e104200450042c098240d44860291075824440c209902c0780d1801411504820b10142c0981c1e4050b0644a80001c60440010540c0f00d00c5031992550030813a000107001540d10310030400c01c0341ca0342e1084075114019113041c40030500152800002010901550022407400d200ba09605e400361130080000c00451006240342946030f00c001003c402c01c0800c100c0050b0344410320f11070128001544e03580d080100d09103e80c140030380c031361700c1401a0006020b1035038080e50224071031040c085c580f40a83c0321428040c042e030369500564208000a9445a00864003e6007400e07000101c60a02c00d440408106008401580a0050366a84032584008912220b141d40d00c813200032000c11406401042902200402907507648810300e8080d040100c1e40c105464214900b400412910004ca12058041c80d404145000000070b41402101e81010240b01644104c80f8403500b00160b1030001200e00c4040c1c040d0700c90b16054660350780302002900c10203a01200f00030002c40c00b080a410210444 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 757946169 1250 757944919 757944923
    0x6120709090e07081002040501320711040b0306040201020309040b010e1c031205040206070312090c0e07030e0604020d060c050d140f07020f0a0201080a020f0c010914070f12 76
    0x8161040e9036070754107401e4a2508102408680051808000d80a01003016801c00100030708154200f81c50100084e02c0190766039084001e030381100000d444000e00142c0406243c820000906860f6040741c1402035210035040c2055000b5031400a01c00342500c6c001a0b010301ca994141d00a6150902280c18440640031a0081c207050144c00c051456090f940d502e010301101c0900b01d05170402e5013040c10300810251140c206000341c24a01000d02001d42c40b1320088a4440340c0600b881440c0045a0b80410000d04a10001606030090200003050340000f400c500360045906513002d2000c010241d1a55888150540d4020b5000020780d84002c00070700146c21441100c07505080032410040344c1e888041c20707903840e80381201003140d1880401031245c038114042a0007003c1c2d4401001c005801c1103039280e0342c28603000084d06001030200081e10109144d01110a191048882a500c0c2e40b8010201400f8102111040315000145000e40c00c144a00003008021034000d4480c00000c00d00d040a4a04900083c10b07003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 757947419 1250 757946169 757946177
    0x16080c150c0c011b21180e011e0504020a0e03120405012f060f040323031f050301090c1d0906040807020312040312020601231e030109081215061207 65
    0x1040046485e026421800305402640300780b6401426000030300ca040c00681144e00d800001c1302c14003001c0c4540404a042d00c0c445140c0781c0d1000001c664190000a203a400f241d4494000140c0415403540700c090511003000035030132a048031100541c036a5890090b8011300d03001400d061650589803850369103a0107000070703c07500440f842105000e030a003800b4049070340da5916080e0005100416078030030380440c420f102c4d5241e000c040740da18050004007480040c281e20300c0680701c483c158092501c03241204008080c01402088809082d242c44003c0c404140f0408041007065002414a5003106103098496244500500340301c3d5101d030340b400002c0d04003580503601841a01045d00031680d00c40d00400103140181c045180f40000d2840081c90450141c1103100b00c03c49841510031040c110701203d94510004036040c01c61695107140c05c8480b01203581c801503140d030034582240280002c603001001c82100c1d400c2000c01c10f075640c042c00801843c41d001c0841c1c01413000c004408020001200180d0042020300d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 757948669 1250 757947419 757947467
    0xe090a06020d0f1d121204060207050c03070f030501140c0a1202040b03180c010e1c033c05090102070605031f140112141816080c150c0c01 61
    0x5244084803000c40d1104c011103006052480310400030412800041e030720f03e1002d8a0030444000e9200c40b424017131300090026401103520420050b052020705d17640c94000e82165143c907034900d51945c0c206170b07920050b03c20713510b4140d2540501c0e200d101d405205201e4108040d10306a00c00c0411224407090884500581d903080c40041100c0007203200460043c80c14040c44100328001d9041c090900c3c4103d01304505000c2244a0003096407a5450300b10360310910741405206019a604060b181075280d440140b48043c441eaa010705d50300c007042a1040705500c9001441a400d40b00d8500b616944584a94140135900c0f07040e00b080701c11b1040b4001c60707000800c0d10300080d8041c00110301f0b03254405a40c125104820b1b00403000c2c0100d59118145020394180f9503020b10142c41d04401200d0030705000303080810700a14013800e80340c03c0c6804000c5074104800c02c1e0b0550046a96680c012a16003500010301d5104002c00d406a50300350000c43c09490060070502e0140c02218981c4005680300040013140318583d5070000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 757949919 1250 757948669 757948691
    0x30307030c0516090f0e1516030209040f020d0b0d170f251101090513090317010e04110109030809191701021c0e06070804030c061a0a0e090a06020d 65
    0xb2500342c0c024894000c01240e52125440c80d14142c482d00c00c0321b5002548054202d51701e2418840b05150807002d03041c2d0076503c200403880c044010340f2500d0401d07500300307090580304030103929140d00030549096250010007403010382e2820000f44c150030703030b6010708040c0e140803100e0413121401000341450112100200d03d8034500070fa91a0046070185044148055015410342c1070042004d807401c00601c1c01d00e00020083d0400000070300003c1480c4480e41d20a96030b0000008040c040d001119011800620080030b96170750303001c01d94000c1070403182150704007003103041d0909950060908a040d698403a60755410440070400f40b12525503040071001c10144503e0b40010225500b80b10300c600007401200160341e0f02480c00404108041c2e407000314014521b010040500b4030004950241c000800f49405002a2190309048440314038a041c0a030550340b90200c1e004049009402074203200314296a401092541e8101c4500151011266400950804900f00002559940c01450703880c86100d40018862440c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 757951169 1250 757949919 757949953
    0x80c0901021c031a0604150c11040603050a05120f090f0a050a08010e01110702032d1c02060a060e011505070506011e15090506091c0605180a02030307030c05 69
    0x44a42c01190b078801d050704e40d91000b1032000c00100010781d825480c1c14a407075107401c1c01c0d8a103111910200000d03140032074104940c06209030310800008009109860301e038105a034403030303e0624048942c1d109401d52066106908020f4441083e1006d089a08102c4e83d0030502001c0b009200110f40d002c249140c0104040d42da040c3e800c405170020700d00000c2c44040750350405007100c88405c646c0d45041c00501c103d00040c0c0e000910001030350100700302929018000003d40c440e4041c520425103040c01200041807a2840c00d00c03040c00d0a040f04d41c00c540c40e907102c40d0104421610b090145142c85600c0000500030070b0541d2200581c82c4005280c0940741082030707118541488001e07001081d0342c00155181d02e10701005100d40320044c1800000009149039a2003000d00603500300d22031343d0700411001c1006061555885030706441404040c42c3c5001c10344540c9407070001800c0c216118043d0402509644900c6040042e060324403e50280066241c2a0207132005d880564500c07000300d4003445048070076840c6001c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 757952419 1250 757951169 757951213
    0x509040f140303011a040f0303140408010204081006060503090d030506150313020102062d0c07060213050a0b040b0d0b03010b100203271e0402160b010906080a03080c090102 76
    0x541c1c8051600c0394107107840d00d00c1311340043c2c08492142c00c0511080c0140e500720624074003280d506007000414401884000c1c0d00d80d004903400342c84c82d5403004c01d001031110808a4100166080c1c03160411861307448403c1911140000e0f81d80e10000d5000700524036160380258440c507089240200b840c1c109d50300032100117100b58011200341001ca03140200c05021540c040103815008442c800440c410203500300a07800070301c44001c1d000800000428080703500700c1c100008071250300d50005d60640d170b110b0846401c40c49102d103a1040600034000d103900018044440000d80e020f0b101e5141445251000800340080680909008070380c1c9035686a00700611a900c01e906104e104c0c491750040e50f103032102a80c0e5001e000b140b40003090100003030848601100c1d80c8141074011207510300808000f086604d800858000e00a80d910030003009800c06038002031168452a035812a524040107000c89500c0e207001c40d0701c074494a240203003c61880c0700460384564004d0064080154103104866101e42d54407444410342c84 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 757953669 1250 757952419 757952453
    0x151a0d05070504110a0507030c0323130618090203060402040f170d08010303080705160c17101b050c030c060c07060c0c0510020a03060803030106031d01150509040f 72
    0x44252001c2249041501421001000d50810135080a03d903200c09401485070360030090800802440c0030040600450050b601c0c41000011035480742003901c25040c065100f100300340c04000c02c42000042840c85400341403c0020b1109171290706510f002c1c03000003c0e40004d44817a40c0190240404142800c914106138001d09620a20003500c000d8582007e0405843d0820b0f802001340d80c10061003c650000d100f04d4101c00d05190450750f6205e5050b82c5a942e000c80310004144075407050000500c040d1060f00c211500b4048800e5441b40003d00c5603805c00c6070111909a40c000c228080032200c1d15006401820f500030420090b81d1612005c50060f504040003103899120700c50011408405100442c0b140c0c64820540e810300900d607812648031507545038061948189419000a00c51840603c03d03040342c0d006102c0141207946a503143c1c40081d001d0000b0112802c03000c40b540300c90850552050040212080101e0048112a810729007404502d1000410644208150700d00800001e51012000c0b03440b01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 757954919 1250 757953669 757953673
    0xe060d020702180f0c070311100b010f020f06060f061209060403030b1009090203060607020913020306100b0f090117152d0f0a03020a080304090c0903151a0d05 70
    0x20100307204100c108550b080031040a802c150f0300708051442d030019402e0b00001800c0000b6119080c9140c101c41c000f036040107048103402950b480c2c000e0900c1d10381200342d030003000343c95203a180415150102e95800d00344407510216800700020600c1e906104140252050001d4607042c503140c0444503105d944c030001e807003a00055001d20100030501d9818451000e1710380c41207031042d01e1080d13804001004906507001e40c004003940007020640680c0c403003081701c0b5095805803d850305c920703151386170b184641c845000590203406460006115088001c070003905442c4c2c540b00260910801c183c00e101c0c1c07500030740b80303c5d0f050010350798000341401d0350f48240d07a11941011089101140c0c0390800e11804009040d582503440500900002d14120b10b450907224005040c0c0d400c0c900d100480e00040d0b440101544080d41004039680045054040840140241c40e13007210280504114444200c90414907844041e0030f0704020910341c506506c1c10b0300f0618285100030300caa2001c0401400090703140c0240e203800c0341d941d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 757956169 1250 757954919 757954927
    0x209150a2402071a0904150909031d0a030506040f0203101b0906051608070807080703020d02010501050d0b0a0e07081b01083105150a06090b2d010e060d02 68
    0x407581080018058610b62613205441e1000442030352003400740307111a602c602c0c1c40395000b0300d1604079000410018054400b0500c450a024200507000c050074421000b525060008122003908082e03052900300e030360110080070a6691921000b803500e01a0300d00b02d900d4020340c41d123480751030324034001c9000325103551501900304000d804001c1c210040c69031281080c800180030300c000751141124401145c0c1d820010351503030340030140ba010400c0c1c4900c00d4014550800850039070103142e40020481c4a80113907400801890b6280d400300203010136040c1c001806401150001070704200315400c44c02c00003c82100303e43c002c40d107901a490800c0c18600c14a182122945c2000e205980d0003164607030005c5a2800400740704020b007199032000c40c000e03840001c103051011000810048100041c25401890303100c0500a810640d8119024000c0c0c1e1246800310f6042c424110001d24100d4600d4015080c0700c155140c40e540d0452490000707501070700320941402500c0d0444550360322150020482103408a8006170382d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 757957419 1250 757956169 757956239
    0xd0609080a0306080d0801150f030b0301020c0c01171314010902040501031202240103121b060b0a2c1b04080601061e02030f090d02041e180209150a 65
    0x150540151501c820171135011b0040180361040c0c1c564030302c01081898071030b004851220040e0080c1c982240d0040d003541c4002900c1d40382c1107010030750002d0b946e0247d030740c2d515401120b024840b40c040d040da4031700d07030101441841c00000344100700752070b180000400000c076007000306800240454009a10a5030300c108151100c2c142c140d0f06100d526004103003076070071410a490413020209090414000281030380800c412490b2014080c490050050311004040d40c9030300341038540340c40a0125072540074054a043c50300800c1d03880700213194512000079000348802150780719162000002c801741c00100c42802e141d41401903815030b1002040030b400084014000703035143c280000d202c56611840306006200400d01110707110342c0842101c032240f5104580e03d031078000b44000201c054030000d4000750300500c0c0c00f941c54000d9003200c0f406440b00e482d10604004448550485091442d000b0f07031300035401028000051f00048843d41d07000101400900900050307a11004401aa2445c1612148914455161180f8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 757958669 1250 757957419 757957423
    0x9040f090c08010c110a02090a021b03071b050117040809030a080919030c032a03060902030f030a0909050c0d1514010905130c0c1e0c050d110d0609080a030608 70
    0x101390481c0c90000800c20080640300d44601c1c80704002440b4803010408103051803450340544400540c4178103401a003010782600d25907203600c000c10450f422120b50300c402d081c03607680d0940c0700c003101c006840380e200e2510110302c030841c0b0083c0104100c524100c02d00410003980c4003084800c440b0392140348425525080348040082170100c524103440303c6c0341081400d0002440380d072491401c4270f50051a02580d124070314000c0c092400b011101c2c0d641000000c100000b1f203c5250811300915000b901513030044442c0050b490f0712403155652480c003040e8028000c102c01001f551020b035000000b49809030901d0448e68440b81503076041c400c5680f101e084641c092203001d0f062001d2200e458024200b94003803c1c5008082000c0580c481818030a00daa211460b90801d4080c020744c2023303a0b40300f0354205011121201c086402000c80310162040740084401080d1402e00c44010720020390800c800200b003aa18030200140300c290400203c400c81e403101c446600160491003d40041200c0b07031404900300e410156524 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 757959919 1250 757958669 757958681
    0xf14121f0c0e0a0f060507140616080708061c0204060510031d0105010e070f0e101806030227060708120403080f0708011e08060a02030a051803090609040f090c0801 72
    0xa1040d0f1801a0411418035002900350884e4800d00f840743c1c58440e0303824002c40341e00c210b95a608250040f2800c0140001714200e09a5041c01b10303884144c400e0711400c004451000044a1180d00a80390100c8a0319441d003240049090b144010008101c481c0c691000c114990504d5000c240483c0d00e852148003d00d10100740350243c0740144000b08029850410401e042c10005409042404012400b411005100c1c2540c1c0a220f00050220000650580c00045c5000051140d81d1449102007402150303040c400c0c0201d8845085c20320707401440c0304445c1c101c2548801c1c00c0409a40c803078010022031002645080181c40d0507070042440d0411071805007000b0b00380312001030525044501d01c03800c00403025080300ca69030540c0c1107071105120b286c42d00700014800241c140c100500b203200d40f00c20010465070079001075218400b403074800e01c083c0d15031a03e601914018a0400c200700c0c0c10500c820903da0070110f010300b00302d0307030014404a4401c05001c8048200c500408007030b900a2a400760600051200b40294 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 757961169 1250 757959919 757959947
    0x717030a090608190b0604050603040308090606120304030210050c100b03070f0b0720061b0f070522060f03050105041211030409020f091c03090f14121f0c 68
    0x140e18a0302c1c0050318808442910031544d0160b6484920707000c0c2d02c505054a001d0280a800ca40d528245410090868841120045814800e002c0020000d04000342c41d0500c400705280210308103400d55080242c8082c009000e0380400c64103006840b0754800170401c0d4031a101ca51013002403c5004c510516040000300d4000441c1c1c0c0d2a1360808101c10750b040700c01c9a20407174100104008508015000207440c42c1040469a400540480c1c03070000b0f0050f416081000d090440112a040c250405c81300780c0361002481000d9101e03880c0200c038014045154504280c030300700b0400000d007558a034003c0e1401c0c5615904140c80c140c0d960b00030041007103000490074074203003503c0c00d0404000c0d000782d0400380d4a03c92030281c041c000341c010502401d00188501076540140e4010b102c0c1510034900c200c3d0000c03001d440031060300064150318000034947e036000d803080c041c0d5402c0041c190781c104000c403d00424120700100705400f4480c409001060030782d001e1280e03940e200c05040101d00d10261303090080900c1080125 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 757962419 1250 757961169 757961177
    0x6041a07140d0b03010605030105071107050a060c080a0c020607390b0c01110c1c031116050c0307061d03010212070c0c030803010b120a0e15090717030a0906 69
    0x840300720803194410746184a50b02000402c0001d208004280980003540c000d540540c00c01c4240080541c01410110102500314101c40c0102e50300c0c4104003010555200380000300d10000d9102c40881c030b60100920b40307000681404583c08050398042003056000d07840999908000f5043e0403016034001078807038000441c03001a404035402116401c00185001d00c61000110303400035803207032020070a400c018035501042c110161114500400c00c1d44a5410014000714440d510003500074080c02881030000408100703415500b01032203034881c00403500300030b10f050f2020b100300f405661403a5410000540501190b641d04150340b08088001c0c4601e01000039014401d0340103110203a540700e402c1141d180e00071000d141c2041400210f050210410b006604082e040401c0040080340f0720650358000c0c00e15542c1e034807040c07105945000c0e07114102c0c0c056010f040303a690091150005c229413043c07005c5408c0f001c00c81c16200040d64030603074100c02c240e4100c00350000d41c0010410f583d905420040040080900e410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 757963669 1250 757962419 757962437
    0x30509010e030604050c1201060512011b02030322020a18061e03151a15040501080109090f020d050f070329070203040b07030507080c101a1804080c06041a07 69
    0x1540c44c1d1544002611b050003185106405d201c2c0d5082500294020b01000d010510360b0005800c41a000c0c140354525032840309801d00740040301c00d100000f228460800c5080e0034601d1500b5950190b40150345400580e40219800130105211000e070a0326a2024020800001d4841c5032103240c000001840751880b00002c42c0d06010400305084c250140e040c0e8041050019101681000c9211110340b03444042c0d802040c1101150001c11004008000b6a0004d0b00d80d100580e03641c01e2400d007650710a410043c52002141a9000141000001402060711403003e80b441e01d4000d8418919180c210350050302d40b4034400001d150700d108003641c01c1d151043c82010505040c604035034040c2d034a2140344244801810000303485801d061081d41601e44160b4042c0311590354121402400d543e481c2d0050582e0701a0349080c1c220085241e0032070700b80405080140921561403880c43c45020385440060040d80d448608011a240f0300c04d05008003482984192a0b004010b50191310b61400b50100820380000d014070700c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 757964919 1250 757963669 757963673
    0x3010e010c0e1219030206090606090105011707020109080c072d12030c050102191d030705061c020a0f021c0c020904020409050f060601030b0f060306010c0f0f030509010e030604 78
    0x1100749414402c00c0d03840a0310b824501c1101ca00c0d241d180d244602c0c000b080c400c00e241c2055804a4294012213107001100d1482c0c44000801511305001e00c030f0540032880b042d0300f0385030301d286440b0541d62000f410b000010b400601522450070743da1182c0d150100d650401c4005001d4151a045081e682002825507a5003c0d80c1c2016098680343c0f081c00768401643c1602041f0301014801d54888031560f074444029511810b55a0301071020405031500358002c03c041031a42c500c060044001d42c00c00c44001030041266a1070304083c0080da07801400700d682c1000300c0d81a8819003041a00041401036803591b5001c00c0542007050007401c29208203031002c2409803142441000c0341d03100d0358000c1c101e03030110f079100b01c41c2e2250b200140080803941700080640c020001d0300c0b01e1807200462024411102038038180304a44680c000c100d40409a544070642c41101400410300b0782d4892202c58001c144250010140d1590540f141403c6003000f00d81180001d80001e548515568003c50102100302e00b50001c2001c2c0c00c2075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 757966169 1250 757964919 757964927
    0x6050f03010b03090a1b0f06020607020718020408010908040302040c050c1f0e06040606030c050301150b0d020705030f250f0b042310140c03043503040203010e010c 72
    0x10710901c030042e0000700204500307420512aa0907540d0307108003c11300c5010740b102912107190042c030031141601c80c1d09800282007800454000d01c905c41640c0a4064181004004207400d103094200590340c2d07900b4040030852000901c103203404503014400e000d464034a5441080f0989210380c000004000d03050200040c0d0320340020300d105403990011400e286581c8803031100001044006e488012501c2814103220500031241e101400345c9000d400190465a21102403500742c8089201e0107982c60205802045038443e01d901403e0000700105000d49441c82d15154603180d9040040320160001c07000a8807224841c3c8186031196000e03070302c501071b08031220540b10000a002e0f82000a008407034403c0000301005012030242038840c00c418000a060415403d00315030320001a22049013540ca0310301c080b5000c0c800c01001900c2562041c001d10300c4d41e07130345a5a81c0003200c0340e41380b118006541511061b9003a001c1c003202c0e001d42506105d01e15141e00d03041c0109801c1d600780040300716259150480001c85140d01c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 757967419 1250 757966169 757966171
    0x624061b250e09010b0a14010201050114030d0804051005101701091e02150c01021c02030f070f0921120903020a05061e0c03120a150608041e1b06050f03 67
    0x210308400b1640d45000d00d0b40d01510781e40444e180d00030040c2d44042181144401264440380080c1d000f00480c1c3c2c0c0340e0f80481c249100f4000d415074141e0004100b01e401a11034000c59034418440d4080d109038190b1103241006640c400d6076104006020f01d1018005165611000e0703040c0112000288140c0b50b250701d6062900c002c030540f402c01e003500500c041065403900c40c04402004203001c841039036a400500098000e4201703481d41d0074070000d0a80000030312004d900941e40549810311010342c0d1519152425281c082c03003590184144800c44038005032100600c001e0342d400b03004610022125411900e0958845001945040c1c240006a6400e2016840b100110019541c0c2070301e02c1c0d5503500035840d12801c00d0310300d03040b00307402c003400090016007005020000d801001800321207800a51941c140d02026640e12001402c2490b808800400005224105184d0880e0040020341801101440b103141c0d140c3e801242aa02d9040d013034000043c03044030041050007030055180050600000040c0714900d0700c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 757968669 1250 757967419 757967429
    0x30d0903170301120803060409141c0e06040501030c0c080309070f050d030f0503090f01090c03022713030e0d0c0e012102060d06080a030c020301110702030624061b25 73
    0x80c01200041f05911168800c122203a084240040414070110403103507207449081d4003142d1414084442d00425004a0b07207103060b0f00000300a1418103007001b00441c02040408286402c006040c0c50b1000071801b80c0000b1030046003000098040350381404c100380080d0010f6441300b40103200241010007c03d40c0880840401001864260365940716120f415241c40514072400d810b80d403030018405c041109024403a41183d100f40c80761800308101c0309009219148042200300d400003198005a0800143c5c802040c5183c03090800351064074444c1d000c16520890f0b15801c5890001e1940180802c80e201e5051500412104880d6011011027014480b1b219444940c028010070740811080498000c1d500803002400c0b14900b00c4618043c2e5050092a0960380f201c1030307001c2d5184c0b49012000c40c0300d100460780c03416000380040000340c0311400410740091500946031075100ca01a4062182c0d600c44004002141090b5581048504030403c8142044060500f0700c2c4a4804008010304200c4c811650500b121 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 757969919 1250 757968669 757968683
    0x7020a080318092e050604090b040c02030a0915030f060b0714030421080f0307050403171207110a02060406031406040605091305071509081c082202030d090317030112 73
    0xc000307000300350041350745c0100764441c10100b00801c00f004260700032507503000c0854083c8031031981742c80b050740c070303881690030000004445103410f10090040d1a2a078240d0b10542c6400101d80320801e11140407524644c010b114540c0c00090702c1e40c04e21401c1d0b00b2040388048128040d601d4103107440150004840804542486210300c04484014010104144d07029040811090360b56440c0c010001040c0e68081d00040303e08016600f110b0f8021940c00095442c0d21142c150566140e480c2c4010a80d890800030070310b1301051050510840040e15030300041c20003850b860b10702044401c1d0380c00c0a01e804100003012580200c1c0b4040c402c00582d907411000c0d540000d80000112100012030910f2030400c0100e40000c002d0b0005c02d10310401166004c21601c040380c0425050765060600d40c0400769486c10b0702036a00b00001c28120100700761180c0c034030110b0840b11141e0400044141c4030b03404203051032a8000c1400106204050800c1800168908130341b90140b91000d151131907050500c0032100a078523800c080d080c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 757971169 1250 757969919 757969981
    0x4060314060a050606190e0603070906110d02031b030d110301060e040b03030a0f050409090f020a0b03100506090112060b070506160203030f180604121803020607080a030207020a08031809 82
    0x1290147e040d0003000c8502400070b646e02e02d00001c019014400c1417060300001240c5498207851800041615604000340d42d0203945032400c420000c00183d01c00c0c000f1510705000421005036540b00a1085444402c03400d510b041d00ca41c0f4101e400f500114814840500990400100600c0c81c1d901004a8440042c9c40c20700000040d68000c08480c1405550804940c039480c100a11341800700c03400044295034800c4a15410342522510743c024180000c1c1d4800c0415140110b040c04546403030000340c1842201850201d012b10442d100407802e84413140d0040c01d1a00c030005006041c00000d10025900080500c1440d8484451100080d96440010701c0d0783c0c0c0c0c0c0d0a0300004907142440580c1a0616201c495046404902341401c103564803002c801d40c460b0105174401406481d1841d02c0c1c03001c4045a4000701068142815500c2d55203e640c410070880c1c04065007000f60b280142d0340d120307007034002e081288000c6407100c001f0480003400000b447c2602e44540d40900402c26459411102d0440780c0110300500140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 757972419 1250 757971169 757971217
    0x6060603070e0a0801060e15010819200316020705224701050403020103091407080f010510030209040f0204110a17222004060314060a050606 62
    0x207000740b42d001e22a80b00c800c40303000080e403843c15000074043e50203800d440e14040d2039030782c2401c00303205002141a000c28490000145032617104000030400480c0120049074240c50038900098901c030000c1c03288885000401400100c80e11800746124031644d900052211070700306000035207220107070750710002915070312858080180740b1a00040b00c1807800c034910f00c2c650351404580d65001c060240403590540100c0741c01e16800c04140036810f01030300d0103840d1a0300c0e090542d00110080e000714901681c5060141d05d01d0b1410000400c40c1034000c0000d0400751112814219529084d01c01c01340222401c100840b80500c0565901210b16810a9002a0080340103400d0310106e4043d159000554035030003400310b20f008c01203400c280002c50900922108101c180d542c080440d0800b07601070042001d49111955907800105d610421048070140072490482981d4140c0c006400c3d0b8485420888100760b201c2005148180208513164100003900c005004601d403900105101c3c1c0581c01251400c09140300c10b0b120 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 757973669 1250 757972419 757972427
    0x812040807060501091406030d080a020c070e01060c020a06140a030b030c2809090812071407060f05010501020d23091815060a09061d030102130512010e0606060307 72
    0x96440e0b80000180507541e51a50307a80001c2c1114500f02c411078800200254036031074040784510340d030022030703c3d114012b0f1070705d0046800942207080b00150320710a1020108504c4128407116008003c1940e6285001030030348140549410954000004d00080d00f282460f080204015500c40c1c0585140c005211880c001c0002e241c101051482070300b1000300418448121a00684911100943c415802e0440c4e9600c60702401c40d0b0100300041c0c058002070044121000131041010341084107450302420075804400781300056440600111044d135a01c0b2241d65160f60203000b0b032401407600b40090101c88401500280950210030007007008491407900e555110070b0f5100980e480c900300a40b00f590503076690140090300e00000d55000c192444210031504940c83c000d82164400360701c40d61030600851411400382c50640310720501418014100d41c1c510829142403014068210391406c103100e00d140380c2001c0c03040ea808003155009283c0d041024500c003681001895035002202640c18540ea584e507144102c0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 757974919 1250 757973669 757973677
    0x14031522142a041809080309240c12040311120903010b0406031a07020c130504021e100509030c10050304030e040b100c21020109050c03060408120408 66
    0x240c00ea2030410300858400d1040840340c4600e615000d01d401d0b42d82d100c030300c031400510564040251203904200a03c500903030400104d04002490070081003904880c0d80d5209140c004445d400c200d50304c85503420340420110060008011b011521440d00d908001500000c2c502c9410304a0f601c00040b5400310f41094482d401c005006c1200105440d070628010f1a40400f9501030051584290b0030021640b04510307052060300d0480f0b9000e00c1d1400c03c2100c802507010180c4000f041d16055000c1c5800e400500e0302d40303201d140030011145c14001800d01e003603c10051103410721506d2442c400d00302c16a0076100d8807102d10010703011700c00342401a240d204c5035000a07c0d002e50015060341008421760b4604103d504640a140620305c00d0321064400c44110090000315859404059440000308190401d0b00340102d1071021614016000d601d40400034070040c0d080311140064003801070399618104030901005001d80320507043c044000d0082d5003401d072901c0e2400d020343d00744201450000d402003020008200210b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 757976169 1250 757974919 757974979
    0x209010519080d0e03160b07030f0c060903030603060c0801030b060112091e0506070c050703110607061103090705010e0f0103112b050106050918150405090d140315 72
    0x541107140c1c02d000042103030b1440c1140300d000b40706640b06c070074401c00024282c1c8150303034614190030b04107220303a1021105017103240440ea007481203103021400460624002c807090203000e9140800c140b8510714083c0c04803003540c1c12030410007101c0300040c400a11003040c0180c021000b40b0382150310032181ca4400004104840000b4070307810340c0341340e42c490800011221040d030b540500103641465460a1080d2121203a8041c014060b0300140000c3c80001d4040c406200300d0340c800741805090070025500e010480d9092490103c6a000100820249110401c4650080c00c0300b072030003c1c03010a403e808908030741d068618145c140b603219101d0f0445600c4060994440b00c400e070103c54880300540510251070f041e810300c8090054149400031503018012001c503202d454001d450b009080c0c400c8110070440050180800e08500089035411070300341d580d80500ba010b0280040500740c0c0c9200850040d002241c0b0030340c0142d80d240c090040041105500300700b9054500c0940e2080240000d00d5103544c00b0060342090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 757977419 1250 757976169 757976173
    0x30c0801030b0c09180709050307450b04050106091d0726010905180312060604082a0a0f0e1e04050a0308091b0f04020f03010b03071b020901051908 65
    0x4504281c1e14172081c2d0086030359454030701d906501d41d4241521203041c1d004c0ea420203800c1115030008a1148141125000320003103820602200c64640c0020146c0c0c0603100b40c90b00c82d2601c0c00b20038580f8061003420b004010070f0400040c0c540c07520170500c5e4010a42e20f048081e051000d40020103890042d100035102c80c3c0f503040344c0b03524803881003c0d20400c03207801c1c02161b402925090004a0101d500c01c0c007400c0c1d8000301c01c000c42c02c16260141c00c4a98a100801c00c03504100b090000007041c1c0010000c2608003000300040007085510820a58048801500071610403d0094804c000206c8100317428002e841d4030035586d00345596601c20161510014180800c030180d22101040103000000c00d85ca80058800d0f6a181c070940c03075050300e484d82cbc0d0a560700740d815445001c4440003160320f080c00c1c5030b001c260400780001d401c040d44500c0c90525504243d1090984940000070400181e0380314680c50903003420151440c100041d0f42e00800d010440501429020381c000500e00c100710b030403c0302030000500403401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 757978669 1250 757977419 757977439
    0x10c030c0f080310150306031a040203150108100b042d020405150307021005060a05010c0f05060c03070801171b13050405010b1528140a090312030c0801030b0c09 71
    0x51004203061041c811201d00c001005c041d0980d203842070007641e0480f50810784d01e00740b203210300700c4550754144040c00499041c031503032442401c541101c0d40c03a54000c11040010f0881c4101482e10101030701d0280014a203d0b174640320101e170b018600030741402c1c2c0196032030800c240175814901c1c040d0020b1040b40c00c550762001c0d0b0100380e01d1401e01201c00039403041c4c070345609880207440c00e1520001585c00c1942c2c0d440c0e01103d0218180310740c0d4032510300085058014003205200e5402034484a06021055900d501000400000c01c0052a04000d60383e00600240c2d003000c006548161100b81ca489018905809088086d43c9107115996142c0d060405101240820407140c01c16180042c005d002e40d96140e8011216203d1620840701c600e41906c21900c0801061101c01c07030201d0301c1c5000e50700480c00c2d10003031000103d1006a40c4143c2809418441565110300c01e8003401c41c00e081c0c031404000404a01010304212007448425030001b0603504480d805a40c480700740c0c039090444851030248203000d90308050801c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 757979919 1250 757978669 757978681
    0x4050f03030a062d03110319050c04050c040e160519080712060e04080705190309030c0b07030203120603030c010e010b0a1509060e010203090d050307120509010c030c0f0803 76
    0x10780240c0803140c0ca003480d20401c03032103400002d0844d0765240060740409054502000401d0700702c1ca01c0e40c4ca00308002e06075601982185044d13154020400d501741c0d42540640b003503032a281003510403a60400f250038202402d281c0b42c84100180782c94001c1070207400311468041c3c06200c5024506a4407900c01403103681c501ca486004000380500700480da5480040c1d41d0401c0411500c01512607a0b06032888504040314942d1103881c0d01c65598488001103920f031007031000030000a84401c0402e0021840303641c032480510b241d070420501c0e804081c0c02003241c42c0400c20069001079000811107860015929021a507655100b0000e030031809071000145030380d42483c240018241041d4400d14408004403010b50794252601c081045203884051402d0103d50828800c2c403045005103400d0031100814070450b0b15060300b090220300b140281c82011511940301003110010455852070b82d0b007400076580b825505000124000800034105104080c0900c2352084145090100c42440091000d40000c111030f5a42444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 757981169 1250 757979919 757979921
    0x30f030b10081e071b0f0215030709210b1005090907050316060f140c10060602010b040b030c0d1403030f0106110309060901080a0b090901050610020609060406020304050f03030a 78
    0x844860030780c000c0003094080103042d5810b20500070141c5940345800c468000315110030388000c1c400180c4002e00480e00b13550050b41c0303c80748e0300e4220b003d540c2026141e040090300a0320b400c40340e0b000358020ba0102020014070742c6141694103401500414504215207900402d802400c01981109802000030420880c0c100000200303401100c105504481070b6040080f01c122200025020b1000059848400e1200f00e51240b0b00f40705034111008001460410038003c0d251800c603c41d185109641c0e00c48204005090302840bc11090505c1030302d05018003c00800025121450400880e200f107070170048032014004c41401c10030f00200326000f100c2e030307034202032038604042c031024400d1100054500480150081010045e29110348010703050303904001c40c000040d90342c2c07040140510b00095072103800c01d642d80e8075004c203039001e81c91450001400c0d04104e4141f0403102c3c60010046c055502c00028440d6103440094402d5200d43c00440050702c9860f6442d1003414075444003410145480048103200c021034003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 757982419 1250 757981169 757981171
    0x9041e0e070b07020a090b130c02011e020306150c16090902090c0406170c0c0d091410020601090e0309030706020d12061202010f2c1219030f030b1008 66
    0xc0101100d010565605002c2510310078000003d4001c111030408200595080c1c201e0034581100a006011030a654a440350403100c1e04800c4c0c00c0140e4440003c2503c014004a28109201c10004194554502000440c4d030400514440d08014000081d43c00840740e03061005000e01d05080f401301c03071203607601c01601002c3c121484082c0d100d00074900108220340e02d200704481c2200c016489084030300544d00b6107032038031000c0105820141082009145070200303040c0030340011006c8039280c1000c00d03401d00e21640380a0080040541c012240c00300e2400010303400090700d41c11903d4195000c910740780100404c50841c059140850342522034060003042c3c0c1500400e5041040003d607899031849500741016800782c5020348a203d03050000f200c02c25015501c07035003101c000380000741800c10511000c0b8444000369010800d00401c00e4031245480910380c580468803078002c0640f00010100040050040707000840b0502e0000c0512414003000300c0300e00c3c06600045602c40004040040740403206d0000f41050310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 757983669 1250 757982419 757982441
    0x1121071b0f050106060e1c0302160324060501090302090a0204091401060e0d0f12230c0c0907050a121524170601030c03060e090703050607020d050f09041e 68
    0x4201200417992601c44c01207812500002400140c002c00d14040c114102180c2400a40450181c1140c5c040e1003240403200c00300640c0b2940b1003288804000c0e01c403034442031022458002c02424050b08212580e40034100005498040311540c003542c0b101403c00e4001d05c41c0d64481040d503802d021080c40014400e0694074100c402503101c3d0003214503e0703410007074031159681c4010b00d401807640305600480c00b451180441c02c640c0f030a112100c840080f4403801103440c1030700c1000c1c10860000d80000c0d10031041c0010004600192a104224142081d002c0c0c464040c95440c0d100b08280100c00d00862207294005d41e403d506050101d80000b5103c068401245c18042c92803c3c2851074100380304413461160303405803900580d916901e0029200c3e0401140a000c5078181c1c01c08154a803107010603404022204140105036500003000359901c1d520b0190b041c00002000c0c1d41c1990403186115400c1500002194805294403500660754032250300040d00800b10440c6082d045030300345804120683c11948005940d0b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 757984919 1250 757983669 757983671
    0xf0c03041208041509210602073306081005091e01050403031d120306131119020304060203180d05060a1d1218030a02030a151121071b0f0501 62
    0x10410720310940c0d0840b0548240c551001d40f041d00c6c0c2074010750010714425114440c2c031002d458035500d5229078401a800c0480b0900c1c10040070b403045082400207101e5501c101c1900810322003989043c80c003588418424981607581500c420010b951440d00303000160700d1410710608200361003202a161402444104c038100c1c08640340035070f400f21418000c40181c80c0c0441050003010038080c8107080c0081600302610064102c00c0807060400f00b9081400381c0650314983c400940d0b00e80c60717002000c00c0500134400c80007042d90020482440000c1d400b00c00ca800400301608941d49400c0c1c454007150003890700220207403150103524140680c01042e90012070084110382d103003c5240440e564000d403101c00e400d480b03d0150b2000c100b0344504241030a50340044800080036154420b0301500071074207000c60000100c410880300048010030541a103e80d09540000064450030001d44440e40107805013108001499003070b07103100152400b403003044620310b5292031004a0041c07140300d10306000c40d0707196007000300d4042d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 757986169 1250 757984919 757984949
    0xc0c040605060d110409020a020102030f0c070c140604030b250f0c02120a0203010207030512070c020d230d050403020a080303430801030b09070602030f0c0304120804 73
    0x54901805040c0c29654010440da181001d0405003200800c0850b02c040d076500010300000070484440d10250144241540000d03070b0364a0840f0004808620003440ca5103240814001407003c1449903056006442c040703011801740104244c0025903501480e40024905500d208c02c10108080105410380c1010b180e60541a00c402035050684a00c142c00554500140b5694400300151428420312544002c80000f51100c212040d008242a0f9118110540201c1d000084404810b040c038111168012400e03e03100c442c4103c581e0000c0e0000c841e00401800101601180615031001025444041c540f000101c0b0020001341c08054a2604184000c0c6e2144030b40100000c2d5020010044030f00c2003000e920510303003c8000322050700146025521800d00301007080010100034110454580c41c05010380c5030041d0355851403900610340301c8001c0420305d09400000c0704000540d0000203940418480340b2070141c5407804003040a240d801154000c00c00b09021800040501000b203004000307542c0c10707450101035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 757987419 1250 757986169 757986193
    0x80417060f160c060b04060e1b12070804110306152e031508010603200618040209010c020d0803041a01030c03021c08030a0c0806100815010c0f06020c 66
    0x100c1049a40100004400c24115690b40c441c4280322519442980009451640742d4007250464807650001454111607406000703034010a54446000b0010080e40349142c21002961002c01d13140140c10b07401071205080c00700381040100248107400c41c1002e821200c07545849507070b0040860046240354000c00c1c0c43c00300f2030381d604540f1090310096050104107603a01c002008045005041300c401000340042610b4000c02e2200080c02407100450140c0381031000035503d603c004c41b0395503100302e0340c500c540d00401c0007070009036211600c1090107508650041c0c80d2842c000c010f0781e005410b0703c0000d61104c4140d050000304100340c030146005a00603100741143d08080050300c0d640d51401c1c007000c0d20841d800b000400c014039001302808000e0032000381c40c601802d003581c0e030001241c00543e841c000d010386564560000b66882030000358000022240030200d21422600030b03061400150100c1d0312201d80c0c0e40301c00042c0e401110800030103a40902c00d4580d4103940c0c14a00c000350031901c020705040c041d1405100d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 757988669 1250 757987419 757987441
    0x130e09010b030a02100302041d041a06010c1b050a0e041b0303020a0b04030905040e011b02120403291009051b030f060103061517010b120105100c08041706 68
    0xd0a41010b03000346031100c159000c10a00050340c408207010150208000300c0c0c0c00d145003130b210340b21000700c5105e8003c500b81880e08244e0341510084003000080300d0001c1041c10703a441201d14519941100a61101103003c01000a076030446800440e04050110000074a5a207105222031141e0700814400415a0504006100802c0c2c5440058010307031001d2540d00c007160b0002401600180300742032040400b03944001107002c2e6281000c2c13101c0700e81d54958040a05040e112101d844685607880580004650791403208891300403030201030040b0542040316417100b0071315214000389402c09030310b807075051030005903030707055607990b40142c0c0000360400c0c0101700380c01132040303034806240f0000b1182c0c0d040d0355036018181642c5100505050402d0f49030a0005105442140040c49000300f55a0300200000e80320780100c158003044e801a140c54800b0010410550301c804422415100c013182d9407280c4a010f0841242d01510003000034060250004d4002a51210020b200d2200702e8101c0075203005980b080c41f000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 757989919 1250 757988669 757988681
    0x23041401110d0f120603200907030b01020618030c100203160c050c1309300914280e060f0d03020a0605060a0b0c070501020705061806070303090503130e0901 69
    0xb0001c40d000c05020b4500c1e600881da0701c0303860380c0709410004d44180e0340d8440b4545118a025015000ea9082a880782c42c2e00301114440c0d44150b860500b80004105240000d664520080c40f05454200b1228201c1200900340101d4039200134a03801c4a120015444032007000354002c0d9021600c07058040100418030f0300400904400a0300301000c4c046010b58603003440400d8024042d17600351a99556655070000b0444000189003660406981c141600c405a6010303408500c051888140400800b0801ca540011501da40020106a400c1d8400c2801031000d5040e248141e03040d4a500c40541d0400704a03d0900f00c2054841c0b403045520b400c0318100b1005021445d0351b51000600140c00c4043d9440220703e07030307030801d0ba0401d030003412020b445a5580c4003880503810807600300b0215040314000308050742e0b040000e4006810b00b100e0480c07400f07000c2c965481210130510003e501175540840c2100525000ba0302044490707421105882d07a88208080140c0c4065150007078420b500300000c04102a02014840c030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 757991169 1250 757989919 757989943
    0x706020d17060a08010515010813080910050c03070f0501140403080a1a190e010e0f01271113091505060c24150603040c05012304140111 60
    0x8404461490710000214500082103982c0001d00070000051003142481103034070942003540c12a28a41c10340300010550076001e051004008210001c0c800407803803e900301c2c4c600782c504482000c0e001c1c031440b81c25030b528080c40c0d403108031500021844200b441300c035040c04010144158020013201004400010607207c2c251005800610200c001030803442d210352056030201e01c3ca0700900422140f110003c0c07000c0d1410300341107502045081c0d0800c40d00c9001c0d900607000d04120507220b2284c0c9001111811420014802d107003480c20003440062510307458009054001000c50418032544513244094800d80d03126180d040c078245009400000c0141c010301c00c80081004100c45140c01500d44010403050303400c80e009058a6020360380b0001541620001508000403010007440c1d0703c2c0ca04980304c403052054444083d401602c0030020440042c90a0700190309950702401d00070150044c0b070000352107404540740381c2c030705054000901041e03600c0498079095880109a80b008812400740b1415622151541c1350 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 757992419 1250 757991169 757991177
    0x6050d0f050f03040f12110402130f05060705060601051608030c07140607020705010c03030f05090a05060c0c03071205190519090b0f0912010911130e120d090c0e01080706020d 77
    0x405e10040000042c068502401341c40310104020342c440c0041c040307032b0010007075010114500e0410040c6140001c01c10000380804c81e802403c0250a0303c07500d48662000f080c183c10000d0000d503d9080110480c003100100b9040b01440741c49180c5010380080903070200c1c000340c9120a0882210310003840000e0355034031a45d5560301409405190a005507001c1221803001c03001c1c1900c0b50f040d240842c42030710907144241689001841c01c0102400d01a0800e0009000007503090320070411601d44c03280020031218030641c46400322580094402e0300702c0d071034004c01c40c4401650305044000241c10b50301c038000c0d011126528110403005440755900350f841c01c0141c8120920400d041c80052130a0201501402820102408158040012206440c2100c50311001150729001c0100030040b01d042508800c9049a01100200700495100030015664145c510301901ca261002500e0110750f8140c0e00048140b0b41d1003501c1c0d9002c20349640c681c4a41d5035090051000500c50844009107461000681d0346101d01107840b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 757993669 1250 757992419 757992449
    0x3091f020a0201140f0c01020a11070f05060a030204150e0a050d20280305070e041a040201140c01050105090c0f040b2a010213050402030912090406050d0f050f0304 72
    0x40155a9240c0c0c80f13038070400022040c418040602d100750002c0404c0c00244000690741c0c10281800f9021010386c2c4401415684031030014411b030040c8240c6003040c0c80048400507110041801d0403000b0780306030340200e0728032418881d0310071083d600450480322600088491129841e2035030148092802c1100000d020400b00c2c0a86800040c080748402c0c01e40383d40034240c010b84c850681000387e05130300c640401c006088542c03101001404000d1001034050840383e04c41d400542400d40340c03650707144c00030b081c000781904030a0081011a0f009581c00c200c1614901841074858800e202c00700d000705000d00c42c0c680100c1c07041d0005945017481c0001c590110250000007400d150400404441c3c2d5005003e0540d0003400c0ba201e0351110320311040c40030022405030f500250391420100f9840503150b0300c65201d180140d005105012340f0840119a42c801388011107080c580360048100080c010700450392095420042c1e42c0744403400c0c001007003010800c09000388215540181550001656440346100d698030b0030805403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 757994919 1250 757993669 757993673
    0xc04060b090a1a16050c09011e060518101713020a080d020a0b1801021206041a01020d0e010309060c0203211506030601050d06081612080301030204090c030506070203091f020a 77
    0x40c0f130030481030f00440032600c2c00d034078040109a51010a800401200701010b4880080420f00c00d141c0700a4003441c50482c0c00d2202a0403c0700d0303030100c1c00a0140c42100c1c0c0c40d000410451182010b91986001c100c1d01000300d04244600c402903408070707482a4042e48010740042600000007840d1021540305a006140321038160325502c0741c00c80060610039a41140c8481c55902074800d00203040c080d6a03000c900f8600d41401810041141c0854810b40710303000d410102140107a8000c2400449107640c1d0612118418416004030300920030309000803c1c0510b811492940c0c60b500101070b001c48059050700b8404c082400c24071040b803a10407100c2c1400c0701504520002d55091040c09580c102c501814094103281501c0140c806440311500300b180a0740c809104100d000c59100c0c01c5400074684030007a10b0601b1074940307a640701803005001c0070b40503503154007400e0700f00160206060001e60b080070a0782c1781410300c0e44000303450764020f1001510482016035124500341c800c40b5001030b0104903400401c400c50303040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 757996169 1250 757994919 757994947
    0x1d0111130b070c0803030a020301090b0906010909021b0307050a02030d110c04182f12060109020a0212120f0c0a1e02012007050d081311030c04060b090a1a 68
    0x4880b084404240004000414007000c0014500542c02001c0143e142d605001e0070208540342c680e440c602c540b0340c0c1414003030540d801c0300d002d000340c1d0300e0320b00e0140e5a26121401582c00711110740d03092035a807200041c940207000000c1192100395208405489020024850807251401c002414100942240000124920f0107034000100700c0752668544186031000d4440301420100301e400000c03940b4003082d408a0540f50004140000c6001316150b00e01008540e4100355034603014098103107505d50005172004000d000308001c1c4000c000484009541c0d0081c0e10080b2b00c647c0003600c05000b0180020f010489100704001918015420380e501c94940c0c0345151040d200c02994007400c0b405655070713401c03031050300000f4005100e040311003444000d607100c400e840d20310328000100c3c8003a02004001014440002c1c0820b140544151300618004c1d0030b0500301c0d001904154144c1c1131300360301c103150501c000340d00c3d4070407800741103004001c49a0b211901d0f03540320314001615684d211a02920001c011040120f048 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 757997419 1250 757996169 757996177
    0x5060a0303090b360102011d030a081306020a090801050a0c1713141e0703120f02120a0306050415060509061b030406080603190305030f0702010f1d0111130b 69
    0x1441c801c44604c028090f16491165060080203036800062030704054a50b0240103402172a052410002042100d690880781c80340100c0c11090100324101c5e01040b0700e040215030724080c50b40c110004542d90030500341c0c0641200100e114048455003000b0000b0400011817294680301d01e465141c40442c1e40300c1034882c0c1c007100b5006240d810f03403c40d105405404039100400882442d0110300c001e00113110318400e80032880b5900985800c55900c200e4fc10f100013001e03401a60025440360500c90040444000d05a082840040311000190f00c0415442d000b107134907802801c1218025107080047c401562020b6103090382600500b80030400030400c00783e2609044009000900902241c4044910141603050650f44690700c4000082c124405221140c90148032140c00b03010b6404040300c00c05659038002c2d127107000041048a418a071140060074160003900108415050038000b041940505240c0400c8d8030f240e00c5c0311002a6280040c20700d00c0d01004030403a080d0f0f0700001407000d41c040c0740120814290744 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 757998669 1250 757997419 757997437
    0xc0d051303170d0c090602010f150b030705310902070b07050307090503100f1b09050105090a210506090c03070b07080f04031401050a050105060909062701030605060a0303090b 77
    0xb048032104209081c4941c0100c140c8071740d60313203a030503141034402800d680c00381d494000700c18544083c07058030014809140003242c294401054a0b6503031018151030901540701d8035507007200fa80104040000c07500d4482c000742c0741850a003071400c41c0c0b2064030008078001c2d480000c4c07000c2c00c41c1010498160055001c1d580c03043c40780c40c1418109450f0780100341403400c6d41207022800b80d200e07070700c0c403940000b68040e440c0358010044e140798912000d00c0008110081600c601d034180030340080d000005450b4001d4410140110459202c81c602e42e11160400c440d145800650b014015400450900240414a4004440c0c01001014251b082c92903e0050b40d001810458442108000041903401d002c00500011030044019107a20a0036620382c50944a00400c1d0383c202c03602d841e00500456517103200340c0f9229072003607406d05560b42d19100440c8401042e0802c0820075080d0a4014a054191541c5581a03a2042600b40703c1e98841606000340601079020040c04501040d03000e00c0212142005080101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 757999919 1250 757998669 757998713
    0xf09070b0c0303191401091808032d09150a090c0602030316020613060b0a080627070b0f0a050909011502010b0a0f050d020a0902030703020c0d051303 66
    0x155480c162600280e0140d01c208406400c00302c02c009113455003040944801c40c030070005114510070004540e05d0714505000d80c90700141e440b0480142c1a2950b100d40c108954003410781c40c3e403030402c0c0041840701544501154088024503010308003600c0980d02d03050060490a00404d0180c00858841410303232070003004030b08140d548240903008107000390005001061240c010f180d9a080c03021400444e5401180d05600b55486041400195600d4212105040781c00c614002640764458001512003030310b551046402e4031070903090100c0600c640728002100740c1e400407020b10600302203071065215000c0780b14803200c4103010701c00005081000c100510001c0c10526200d490041c080d000100c40700740030b07040a021144022a510100e580902c501c44040b14215124121940341c0440000e0044050042c6405495040710032411512085040030160140c000151348a00d48403500070020b4001c00e266050318071802e4624036103035005008541600c03503e02603200505065032601c621040c42541090341d03c0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 758001169 1250 757999919 757999933
    0x60315040207081803061312080915010b0d200f0c030d06262b0203070602070b04120f0503040308041e03030e0d05180d02060403020618150c060f09 65
    0x1e030300c0e40c0c010b1041800030450640301008904c245441c05030000c0840070300b600b07012501c0020642d260031156400d0030900d00a041581ca00b6442c608000c000381d1702038034440103280003080104090001c0c08a02c60b810304200480900012000d18580c51200c0c07481000c0c004000a000214100000300f501d401300c1d4048030301e450401680d0004583c070980c0704088070701d101d000381800150049010300d091481d076401440d00501c4403809100031100700408010f001039154160001c02e00030300c25683d6481c0c0054046440e5001d5080000d203140d0110340c202c0790740110720000807295004a491b807544150700c1d551281140c0d6260345c19980510080c100352101c01c8141481000c00941407411650780703102ea41d002c108100e07039a006070302e0803880d00e107000203110040c005000c1071607420a600201364421202c0540b0146540040ba400b40714540010b90009000150b8070104609818030380704011003500c0f403421752059981018694064601411001c0d0481d80102d403c0c0c02d091140123800203200000c0d5201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 758002419 1250 758001169 758001173
    0x30f040e1315050a0b0103020c2d0f0a0c0501031b03020306192411030906070618030c030905040515041e0c090501030e0307020907140c0a030e03061005060315040207 73
    0xc80c1c60034051612103d84800800c001e03025180581d4032064828201076040135145a030b003685800319503060048120441d00c03001070000800202000b0804244d09460084071003140c06a19080d003140e00307a458442c0790710009803951080c4600c40c5070402010342000f118460b140200c0c069071002d494640d12402024030460492043e1f40403070b0003003103038042e44030050401c01c00030700003106025407072000d0060b056080c040085000c41100d03800d400850b401c03695040d4a00e0050010090101100c40780c0080512103010990844494140a402504c0e0b0f082c1c280c1e07440d07003040103850303080f650351f43c10b03641c42c2c84182c516040a802110190144a445a001c4280c200d0321604680e003200c0c68000040c0c21240030003003035801d44200040c2e0f0b00a500039500e0403c094020410000300a0007090402241900110700080c99034251340910715000c09039003d51259060003070903510a5001140310b801020007095520180c10036203012144050f1819045a80302e60340a143d07440310883d00d5030000d0f000c000a40c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 758003669 1250 758002419 758002433
    0x2030c12031905040b061315030506071103090a03022209060614090c0a0513120c0303030f0506030d0f030605060f030a051333021308010e030f040e13 66
    0x940da00c00040450300d03850300c4000c4491040458121915807482c2c50306000101e0480842c4a40c4810180d6000b441c40200200303080080c4045522114030a0384520040204440810550302034202c0b40c1e24400380017034006000d522403260501e02903203e025010f080006007401109055024840182424800412860102034403040e0754211241c540c0e0340303000e2281e0b0b00f43d200c01ea40c0588058a00341c5440c0f41400110490741704002600f03003802400f08080314010801c42800c0c02900155031a110118124a402038981c402ca0104402203801c05440070128507292243c1845010001c00070000003c1e8404280c45000440c07005070201510b070a4040b0f400c2d110a002400038030002c540740343c1e5902c2e0000c03542c02104c1c00035043d50a05c0000c1e48030400030444902d141c009040440703c080800b4180c1c40040082c4446160381520850300115a4020b420740180c142001c80d40540024084005c009100c0f948900c200e1040340396050f000d0105111600f1441401540b121400c000f8100c0d003541501c2d00c83e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 758004919 1250 758003669 758003683
    0x10501090c11210f0d090203010e03120103080906090d210305130201110316050c0906010e061c021b060f060109080d08090304240f0e060906161401140606030405060106050a02030c 79
    0x342100b61581b1a10085042c24402d921004508002440c21b005504292298400040c40081e02c6180701062820b140d903035000c110390107114001c03c5004800c0e594a0044c4551a868024815200384074a030700500a000780121446400500e03065141c4002d0341c1e0042d10500030500c074466440c07006002c4440c4106501e00c246040e90301900040400e0041c000c100890424018110790400046600340071440e01c40d0b005503480400700010030103071a12046140d00007030090b4904070b42d0000c2107651001c1c04400104270079004242010313244402d0380d642d000550b0404054410075416a00512480c296184101440c0d40c001a00c4130540340380030b070344440d41d000021041c8000842031802482c2c4040980d08048008810031702410b0910f00e081c1c00200080c03c03402587e404900484002420700a050701c21910741c01100e91004d603805070040f841a40074000c1414a03d40400501404003003240303403a004041d0391107036074090000c2010340c0c20180221041e402000b544002d51009000100d4003030001c0c8401d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 758006169 1250 758004919 758004937
    0x105071b08030c060108121b0a080d2903031b011b090f06090501050a08060303120a061502010e07050d38010506090a0614120108010501090c11210f 65
    0xa50721035800e03c070070320b0810106030321918240d03000c4030100f0a40202001907450780112640d2491400000312440e030300b802e440c60b00041c03940360001502c0c0e6050346142e12080d4880c0b184081c07001d894060407081d0300600b403000c1485074964400d101c0c1c05400c083d190020300003004a03000104040c10603103010301c10b00c059500e04c60701040d1142c0301405a0044d807444c010040c08689004c030000707803070400060090301c030709509202080240030001e9040e480c10022180165003228184840340340401648004085901070301d5400702d401c40c5581c14062050103070300501c407900e0b070140036894684010000c020302c050504031b03900e031240341d02082c0351418a2400710401f07800030980206002c0c1c00c2100b03641c440303058004510543c410310a40caa00c0c2c07100d1143d103054074010300b02031840e142e030b17646042c1450154042c0c0707958600202c0004240004103401c000d049515190081c00306140400042d034440f20180b9000307082da80440c14103a4481c0c0c1c11f900030a0104072045900303103090004403507140a98010f80c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 758007419 1250 758006169 758006173
    0xc0303090c0a150f09050907090e100b0f0307210e150f15041d10110304080a080406180b0402030f0303072712121d0603060105071b08 59
    0x801103404000d000c001d180c0710040720010001400d00e582015010490000342e03041004074200e0b04003140c0100e08082c0a401d0050a02c5a90701d001500107106a005000c3c51691000400c0420700006030503042d0001c1c0c59805440c68100718000005a0881c0c1008040404100d0036401c1894058640801c000300458000b50100d1920031085140e0b1500032482c580310702e940032080030441c0315214900c0c40381d0032044a01400034015001e4001a001d400c18250382070600c04600404842c0d00000a00b04c035001d0350b054818000380c0b00c9541e501000e07010458020300302881c20080c0d503000e140b01b664500d5200744200340005500220352030700a00800301c1301e01101c0b00c013541e0061100b035207810010b0034030b2010101e000b10326515201c400101502140d000c510240c14400208113000383d05411071102030178020940700760580c22410040d40c140e000a1010012031a100d0303036550450200c10280b103406201400140c0b840d00d500d070045079994001712007922440005412142c00c80d14004243d4010980100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 758008669 1250 758007419 758007421
    0xf0f18010812040302010e040c020115120314031006050d020f190e0306042a05030a2f031b0d0b0901020301090b04020711190b03070f0915171005060c0303 68
    0x1458403101d0361040300c10b0b0405102c20030040c1e07880040059441c40c2511f02041d0100d2900c8203a01600e128817030302301e03c00310300306000c1401401d4170b2070001454001e5544419540c03221009550522082d20f41802c0301101a03418026540158000c1800701c4640400600d8280701240c03480c1540c0200e0707688a0024400343c01003000c560300107108000840100c019141c142466079030400390b0391320030445100380c0005040c0380800b410041440d800030440502a20080c1c0030740d24010712500460302e020b4503c0c81c1da02401c000c0c28504a0360344100800d01400904803500380e848005107001c07914000c0f0b03034022030303a5402c0b50020f09110032060242e103082d00003603225410560480c09075217050104c00d0107584140280d501040e01401401c208003410369282c045284400c40c0c400b100000d035041000890000020b10014590000003103482250321303641c544026845090702d1180c25540003201d400541c005400f50904482d491040e07801401c0c086111072443d503540d012541c0394220511690741030300040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 758009919 1250 758008669 758008679
    0x409180b010602031314030705060d0c090b03040b0a11160609060b1507060203091504050c100305011d15120a140f030708030606130e070f090f050f0f1801 68
    0x2403a01401d11400514108521aa540043c02c5007901c5491800d209034901725450b51424055100548005024155550300d8945080085c00800712a18002070044500085610041043d02c0c003c1d0750001c250240c0d9290341d040240509001000345001510410800400c20800711028031605d20a4401088107003203800c21a04076080420464003588840340e95480c078034110030440c0c511540c401070040e240c2c0c6400702404d01c1c280c0d1701c211030005400b0701000d00061020000c0c444414040848620100506031541201512020b10529a00c01c03030031a82002e018600c80c03100390b07001e00f68205800041c2e1443c80001c00003003110b0402e011641217615003100348007082840c0c0130f001c030b5064000c100000b07462800a540c1e1048030005403500f00c0c04400300728540d80d00000c40300c0943c00903480d0940380d03031207000b0700c0c80d601c409541c04804034800c1130382007188074000e10080003290350384401039002515100912902202b0341c812154805405500c00c0626079401105150901c102051034803258145 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 758011169 1250 758009919 758009933
    0x30c1403160206091606081b030c07150b060d0b0112020301060e120c030604030c060b060703030506010201050a0501030c1a0c0303010e01230f011b050607021006062a0305040918 78
    0x1501d19080c42d0050b0482c4410620b40900701811540c1c5072501f02170640d40c0b0401170f010a2500e803500c0c2c1c940f1000109000d9091078804c040c2401c0c60250400d0343e0480c030242d1807101111800034020b034110005210300850411a98802d000e031010604102c1900c0d01c074034103048100d038406d821001c0801e80e6001d915a0b5410090301c00300026481c600146025180700000030360300c0c9030041008003000340341c40b8414200f1146070414003038020050041d42c0c581d403407440c014000e03103030032244280103610303100006521030010701445048039001031f0203450650802803001210001c2c4a008a04540b041090790701804007080210300908103142986003a50401404441c42940c0d260005e081c0c03000d0007d0340c0d145aa81184041c10701d01c090915140070313060000c04c0300b40f0070b916550140940c05200108088541c020803030f4001105001d004200f5642c541000380c40d110b180c00c03401907054840c24141c1c1a51800c031584804402c0c003030308080e400e16030750b40c062409481c0c401041e003803156070604140c002c0180c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 758012419 1250 758011169 758011171
    0x60311042603041203031a061801050c010209060c0a14030406080c030402151309060515041406070506462a0302180619030c1403160206 60
    0x1581680a00e42440d008070390550aa4511a512a15004240281c454241001120700424501c10030000814507410050002e01610380e80500e5003400b840000100d14081085443c0d07912401c01c450f01c0307840030130011140c03604a1006280346e99800c101c4201950f54180150100500c5c4000900308400b040c0b400240080007442d03d13680e6a4010300044c40120313003003980b81d50f1155580c0005500c940d15400020391000c031006241c90b01d04800103000320403501000d82a000d461503260180201942c0c1c0341030001c14038040068901880051001380304ca22503540c10051010700050030b01d41400706517103416040110030b46140c4a515030302540c0e00c800705c54100344001140c3c3c400085d000c0d603140b0003900d0034003003050a28107280700750f072250a0900c0042d44c090000c010500d240252202045440000c0c00942c000b5008120804003041865030a292000071561542c0c48403403410a074410311030f0140c001d800c04000003c248a0313568460140039070b00d0400b46109081d001034084401503a24800b13401c3c204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 758013669 1250 758012419 758012441
    0x1002030402010516050a060e0d08010501020c01020c0420040f0311010503041119090e0109150e030919150e010336110a03060605031009030903110301090605040c0603 73
    0x100510400c03001d80e8025050310500341511910200460b0503140141c10f000003c2e40040100c1c0c9803850540b05128009881d01c2d006809071075051461340c80e5401a40d440305001c0c042801a0b1001d0f868807620b003050381001406d640f40005414024003080c4002d203a90300160420509500804020410700c011201d400140c1102800c040d0728504240c2c8500c40d1f0440001186070042401c0d03c241d101e07501214103502d00610464004000719014890640e000c0c0410b1070003914800349a8402040c03c526520031000048120343c0150300d0003c9030703014401e00032026441070360051004540080c8a0100d09187c240b039000c030380d8a40c40b800503d100090300300c1e480381180d10a170381546c001d05d0030801e0310141c0312404480403c480d410320013014075000a00b0340307200c40500d4010800c20400420004d058001c9420380d0b40482c01d8503401001001d5100454104190240c00a1504071041004c520300117020a40079030094004110204561960403d80e401602c00311625121440200310b160362620580348070305 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 758014919 1250 758013669 758013671
    0xf030f0b0c120106110f010e071502010e10150e010306020d14040b0106050c01060f030b0727050607020103091e110105120a05060d0c1e4b0b040810 65
    0x41c14a80b150541e5620500680003405a074a41048400c8800c01c40c841051464500900100d0381c4540e190381c075903000d4454889950309403501c0c48100341c018096854003180c000d0040016030051a40d100c05400b901c0341070150058245004215080146992400381d801080050703030b0707818000c103c0b00440c0c03003200c05030f941d0505e001d050100103101d080c070080c115421403501c00d884449503034445004001c0d55200c4c0e0712801d0007950000811060340c60242c4659480c0d22000010fa180081c5003140c01e03403a10417a030064100c20742c00c1c059031a05001405411307006140018920003d681c0c0c00b4403503101d00c180c14800d00c90580c0c0640420040c1041345200340028a4414180000c095102d08a0400a003480c1400d503200e0b40050100d0304e40c0b1004541054100d01e48800c07a80d44c0f520015100089030324990094050004e006c140c000c030030130501d00c207540144c40203108520000d00d8800140030340c81001028204415040d0042c2030586500c80140c8200412603a4651808c06124504840298400002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 758016169 1250 758014919 758014927
    0x30f020715020a0b07030209040603060b1e3102030c030a0c050a021005040501140c071401050c0409020309120f120604091a1005100c030813051e070f030f0b0c 70
    0x140d000c1440f001d260f9000d0603004854980c860150064000c0710102c0e50001d140c01c1e4000140710498101c55a0444151116105c003401100c1c18150755031061a8642c04c685000760b160100e523203e4032440c9a168055003420248880800000705030382c419185099030342e4020040c031401c50703007070300c142c0e1012051070520034900700001e034020f0740384d2202c8130b003c4801c02d682c2d6001500b800380a400006500c3c072050100e040c40c0c0f818101c10046500000c0050381c106504030041e030b00e020b02c14490140108105210b843c1024508000d50010350b00040c81c994aa016007245145000d9441010b4400b0f6440c605d11251038207003040c41d807101c44200406d040d1180e4281031442c0e01080e14200044145000500440c0245c0d071510340b0785c4000c40c05e5a014507080b02c49103080b46050307a402400640078030720035510400d45841c1c4401c882c58400c82c0700c00c042c0c403a4006400e00e440140303c2240c403840011259090716410303950703440300e441c800519600c00e0703940c4084492040204180303d143d01f0f90000748000001c1c14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 758017419 1250 758016169 758016209
    0x302180f07050a1115070908060402030a11010539011b0f0c080a0c14011407080604090222050c1c180209160806010e09040b1503030403030f0207 64
    0x45035030207403120052180000300841a1486084000301c42083c1000301c1d0001060480150000002218042c00103100382401086189021070745500558005008015a48642d26040000252845441e05005080040307a60106204500c28080804c00c00e40a100080b140382c400c0b000d81c9102e0410555034502068060850544220642c00c030035070b842d01010b80c2c41c84e202e05665403204444040c10b11000480c9503160079500040c041211842100d480c84105940240383e07003a104100c01c03170403115510b180001c1156110341035007640040001c2c004211840035402280400e07241d6201c0d980b00b80c0c00d41c040b241781904207008468014000c0c1d0304031850701480c2c2a024880030300701c01000300030a0b111580064081d00302c10b81c880d11705800500680c0381e0300300b0314980c0c001602c1280e00000442d09180003d8910742c011000d00c40010700250840c48290786135603032100262401008981e2200b40c2c400303440c8003610700300090005580311342c4400d2500d102d81407020b031410543d40e0200c1140b140c8044c540c06 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 758018669 1250 758017419 758017441
    0x4090203190c0b030c030121080306040b0406090e0f060615120411090921130314010f020327030a09170f0f160e010305060402090403050c070609030218 67
    0x20032112044018151070745915018045440719400314442d40d0000c014004010145ca000398100c2c1c441c0c0c00301e510b41d201400102ca0300b22000030300142107800280006085820a0341200000440041c00058842e8568080034100c800b0303455450703041c0c1d08c4601c010710000400c10415400201c200c8102d168400c00030b0420081d48900010350350515842400f280801481d2480381e607003100020001c07a4149000a02c1c00d68584001c4142c00000200c07400440801780e95008403014122014164074504c0d095440f04007003c003c50b6070f012019947c03010342d50081d10982c4050340c000c4076030500d0307803854520841c104070708040240404401078204101f00600183c000b0455021101c0540d00086003080080340b05040c80b0508504464500881c1924282501d000c10201080741f51000b12040d031030b45408003030710a1602400003e0040d8003410102e00513140000780160301c98828501145004407c40100381407000590000010031020103060046240005442c1c920f09030ba05400602446c1c4454210 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 758019919 1250 758018669 758018683
    0x12001110d3903060302181e070813030c0803042f0d0f031b0803090f1f0e0a06060306050601170402011707020c0a030c08010b060711152206080604090203 68
    0x500200000b02c1114025000340c0000e4011074000300030254461490021203a0440211082411900002c3e0000c0d400384500e40101e018403001e903261402c55075001e407040381500c5107400c25018408142d000c030f4001045040110f01c2f40b4424060391540c19183d402a41103c1da03070594003869007045407020401d070303140c5442c0001e01940100c0100540400741c00c0683d07205000480402e914400c035651801030140101c001d5000e80981300c101c51a4800c45410350380c03503040c0b05003118441900a984006d98100f590042000b9109040c16110b40050681d140c1c0c0403590076501c1128401d03102c2e0108540c1d50b03005121030121031a40c0307103e440030345002e40c0001e21858041e008940707011100381c04181c21764401c00c6500c0341d46801034440d0040c036480e81805541c1074510722994030301e982050000f054504090090301c40351540300c8a00000c0aa40608103c9080b41c44a442203071100c0910410207500c20310b1258000d1181c03022034120b642c900341000100001c800410030350081c0d0a290304540161000140c4c0e07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 758021169 1250 758019919 758020001
    0xe0901030b0a02130e250c1703090c09100602070e011d150409060f050601050a02030d0b0607021f08060108100e060301090204021201080706080114012001110d 70
    0x40c2c0d244413043d90428503215503088003481200030010401e0038011101085005c010f0030851488140c40e0b200112000080311030010030703080383d24445100791802c0303c0185820800e402c0c16100d00302c030b1440101e85104422241d80c4d91040c80e19404008a940500000c40071308003c808860056042c080c3c071040c03ca1411108885029091000814014090128912014005205000da00d075075080035000b500950424003540c62402012817007960044086449803840394001d1414008443c0d0f94030010301c3c1d04d2003ea0b4000c5000c10520005940b0502d9401400f0b982e803007480041201070000800c000350003022a418491130005006920340e20108070401c4492040c080c0c2195995240400d014004c01030300250080d0021504c1c00742035012003040f506841c1440200c90405a903030604445004003032160505011260012070095442012950540c00c40580200001802c0c50f02180c00c5504143c0750754030b01000422100b54502c3c4038055901d10f02904000d10311003502544154070a180c4803407074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 758022419 1250 758021169 758021171
    0x60915050a060b0f070201020c03070b09120a030e190f24020a081b1908070b1e04060902060c060403020f0c060f0313031101050103030f080c03100608130507080109030e0901030b0a 79
    0x1005e001c5a04c03c2021605003900517055070b80c80c84c2d49004600a54020008051041404000c405441d8900050605201f40c0540d41d01c126030701050f06004800d801e16803d00320003800031101107100340c0980b007114028441e0711712071000508807040410015889010840c210f41020313001c000031501c00c0b016a401240340305560a0321034145404289800b807807614848082c4248802141807215040140c56214012210390b0203941c0c07200a030703c410480c00a8070f0303900700100d580450042102540150399203071001d003c8514240504501c0b500c4d11a044a04500503801030b507291445410500150141c00000d072020303403c11980d11a00c5502d800002c1c4490240e88032840360300b05040c412110800300c50014002084903585a040007000600e90340d8405000c80d48444c007084807004910104c0388a607503120b42a600c0f0380d00342a8100c40c4407101030000c0d401904031194030070105006009240041400303a000189070022494090300301d070000e86840d171040540700d00400104810401451340300c1e040540c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 758023669 1250 758022419 758022427
    0x1b0314040b0714160c0501080f1306050a0905100e0c011106010308130b0f07020102010c05030402030a061a0612040b01050307060f0c030302160f140c06040303120207060915050a060b0f 81
    0x50800914004c04880101541d411460034007403004198510301640c400b80da41415a0707954000e00100321400392025005003e10b0701d0303a4030114042c1e0b800250001c04122001c03610301e0054880901d04240d070440c0c443c00903903402e44080d16200030014510708080078204507161400c1e040580c0e846200502c4098004200040e0b070580382c92004208201408264403180d48621030074000d89a26040f4050490256103061107000300d06020b43e064910031503004004094250995581101800c04a28000301406d41c0700b40011032941c0d030002601a0300342030300d083d480d245050f0030a50b42004040e0300c014044c0c0c1000d0014801d06501c102c030780c1d01c829094180801000403904c0c04a00900c600761003800341580080c3e0310420002d4840c0349c03514442c011100c0c110b10741d000011654541c202244e2083e400b107010082000000d01405a100e5007440068005040c406036456000668114030b100700c68074140060112903d03500c6114594002500085c1080118201100c0240d41c0c8545c80c0c0d04203c0c44000300d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 758024919 1250 758023669 758023697
    0x50f04152631020604030302150c2523010207020406140a1707050a061e020d02031e040807091d0c010e01050c1c03150803030903160c08011b0314040b07 67
    0x601c1880490b94040c081c0b40d90f483ea2807d0094440c01014044605069130340c000c91002d0490b48181c4d411001c40101319400700c00740da180d4030040e90b20100102c0c0d07900800f554010181031083d400c4056a2040400580e640304588108000ca41c403540002c5980402c9594510094a4101c849410741d940200c20368a03002c81c0320411440e05080317a100a0b0b000c003116002003009544501c2241983c44400401941680608030a03a211100f0120540040c0e1091100d12008400c4600c1c0e080c1d003100c0d602000e031501c1d403100440d500301182c503009000c8031512852038220804004a0185c5a03110b1603014200303461150b40024200418111110b040260101d1003003020402804403240e134042e11000407506119206c0080d0150620b0b0015518540b105440040c400070080101c0303208030b01c28009149044403580c18910f6020341d088058400d8448601c006c903058209214154801c0a00c0c624050001200600142958004540070301562025414400000c44440003240c20074640d040c00e121a918103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 758026169 1250 758024919 758025001
    0x30e1e120f120414040506011112071403030f0420030708060f1b120a14040317010923090a050601060903110a060519030e0a350703050f041526 63
    0x100d25150382754041c843c05800150400c2009001080c8200f240c2e10070070070090b04198076800112a640c103844e1049000034000f40303d000da130902000111000c1e0400001d580042403602c02150084540c9900003000e0054400d100c0300c040ba1b000c0d44004481410038203000e0340d9840c0d4055091803c80001c01580843c07452425500210021f200000c40184070f403520f400e00401c0041c02c14000101d4080c0c0c1d40003c01d041010303008480104a06c00003911040246c1c40c12400e0002006090042d58015205540001001445954003c028694484040d241541014000e136000c090030b0a22821240804011454112007504d10260184009281c10b103040c4009401030003000c4404241030007201c480a0401503241c2e0480184991640305440040072248902100e411070210742c10007880511200d07000a110b41d00524050035111001ca0405a0302c8203c844814a20512030010483c00c12494003800800c2d999810035400c1d044d580580d80c2001000d0b11a0003510703229440e10380040940c240301311045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 758027419 1250 758026169 758026187
    0xc04031505090106171e3c0604240c2a0206030a0606021b01200f070f1701090c1a161b080604030e1e120f12041404050601 54
    0x1405140461000600d0a1074075072042c90000c0b04050b00803410b403c05400d002611020518400455160720110072180034212034103c7c580d9011128008101a803809081c05070314012882071a5030103900d4100b034400d800400014900001d8a842d154504005079403110102011500713100341d0450b2100c4484070a1411482d191010750402c030000280500f40065500c080100e030441e90940340c1c940f0001591820280701d2800403400904c01541041c96840404103100750690f10301e00300e81403801d00ca00500e09041c03042c0c0c0306e00c5a01c03440220401c00b510301c4000d042086000e010003004164129a10002c220350350f13025030318003842c1201e101d0301d40743c00b1041290084d00646141c003210180526000020190540112034112740d0480001464800002d00d1400b80f0340c0342e01d6400e191a4550103124006401248500c03001c0034036a00d00c1c0707198881c03220000e110954240500b11080c004421540f4041e070320048002030200c100403c000b052200104003109420854003c1b6451f00c48000481d60120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 758028669 1250 758027419 758027429
    0x40803160210090c0807060309020609010f02150103050105060f03010905100b0f0301050109151205060726040b0103050d020714060702041e05011d06060a0e030f1609050c04031505090106 82
    0x125050703882c02803203940d01c0c4400407510f0020486d0070064481300304074180c88403003c00035000142400440031641c040c0c0c80180705031440340b040b100c0303020301104100020070080c0d005440996447c030030301c5090309200e00b9142510384203500901400c5400c0d07944554842c0c0b609101035079070f44c2d40d4003030b01266998150040c498100c024024800c17940c459202da00140340003105070240300c0300500001842e0081c050502c42e56500f08001e45910f5440c100240c60210fa00c504042040d2204400074500c02c3c046515980528014000410b503903042d0700e0003034a080c2c60310900109540c0138040402c592040540383c00d1038190190b07901c3d91981d1141c800720f4007512072000e0035285140301c00041042c0383c92079488a4103c03105a44c0346c4210762080c2c80c00c3c1140002c151807550300b010040113111070450291809510806003d021288c0c004900d0010078208110944a51500c010b030110401001c200382c0645034106200101741c07440c080c44e5130b03609920315400c2e0703403001d1380242c499000440b441c000b9442100200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 758029919 1250 758028669 758028671
    0x140d081303140d11090306100308030a11040b070807030237020d0605072c360a0c091d010e18070609030312060605031909060908031e040803160210 65
    0x40c0d000007a061680098920f00e006e4032035075001031000f243c0c0c1211102125001b6201600d1600e81c040b800c40500b0b441c5c0031146100700100320014164850400030640c581c013036074440c0e803074092a00e0000d0501105100070310f010054440c0c0c901c200d81c6001c10004984698501d01d043d6800d203480807881d144500c00b03000c0c055629003010484a1500b0511401a0891405660140240c01100c4500103c101c001d06508040745854224002902450104030004040da40321900c24030384402e021a81d10403560595075075281c400d00d040e55a08450b4400103003011044c03507040341e01e020b03602c40e071010814403607068241c040001003101c0ca09498a0001c110b10013405a8600d81e84a030000b40c40c0304000d10040700010882d410b02490040b252140d80c0545220b507503898699107039002011081c01449115100450380e8404c01c1000414920940c440f00344035032444c41c0c0300d1600340046485d80680c0c40c1d030071401c1e201440402000070320703040841e40c0c840c4450811104641d4003150481c60721074100ca040c1c00c41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 758031169 1250 758029919 758029931
    0x103110406030510080102030f24031f06090504112112120f070801030623010e0f01081f0c03140f01030c05010302040b161a04140d081303140d 63
    0x4540e16800161045140d12460000581c5d640140c900701e2000b00c0c0d0707080085e44014007041c170840c074526408481424904503204d24440400000c0c0c06c241e80c3c4d500400c4c0030342c40c0061241c14189a4040c08008110342d400070031051506890751141d00328081d171070a10031020302e00020311900d44402ca100c0360f214928100c07a030070115010314070150b41c000c0c2405011514884001400d1860484103d84a000140d440300318991859860401412071749683d032606424400614104200f00020710f80206685281400c0d00d003030078001c01542900607003041c199a0049070303091038031080c02c680c0c00c02c46060111001440c1d4003c0c010440c010701c0000c0586150800d05800d10002004141d141030680c0d020710f407911911981c81d0b005404030301c218414880300c00c0080c4912440007842c020070210041c0212140c40e0351180c1c1c0d000c0c6c0030782500116400c503000507250040721004042000500c03d408810308009819040050300008441b014110050402105444402d405507030042520740c2c22280f923800b4001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 758032419 1250 758031169 758031179
    0x90d0e0a03080306010c0b10090f0516080a061503021b0a051b0a031202060603070602061902071e12031401050609090702010609020c03090f060a080f0907120c05040f090506060f01031104 82
    0x21140c05200d110806820f04510851b05403640c46102d0261444007802e074330080101000b0340d5280b000620300c802541d43c520b000124a071034030f6035664814125507001646d8108800100700e1443d417954910b030140d8070545001000400015030328015200705d0003d083c6c1e80050300005082840c40d030b08002c100044030917a6026858000900501800d011400c0e2110790341c8852040b6a501d5089410341901002c0880711905940c640e401000114001c5c24a40084c489052480c07419070342c2c92404a842160480b4010800c65051007011040e0749070a60348600381d4903040001d1014001c0b03144280c418503c8401140c80c5038003d610400040040d00741c203544510b0903000041d145d8000100c0705002d11002c00b00ca40b500c2c0341201c1182c1e412152038a45240a8903013400c02041d510000389440b1040c07040c02c1000c1803860038410110b002c40d116078a0102424100700c02e120507107a600420941e0030b8280071101c80010404207445500c07610079a00c1d100350080d14030041b4040c000b100c0309200c0d0030400040201e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 758033669 1250 758032419 758032441
    0x5030919030f0e100f030b0105070204060807030c092a032319141f0f15030e0f150c07021509150c0a120507060f05090d0e0a03080306010c0b 62
    0x460016221a880c0c12a007000307000100301015091350000f1441d5401002a0780203038401240c0b21810303d0010305080d000da0218044510940103500c6c1ca40c00394008104200400728050050521060207009112010400c0416152010580540c80910880c0d0340e151038400d62200c541208200c003c030444100e4002003094458040c4d0780f1a20b06d580c0c0320314109a00080d0300802d410602504500001c90b52a90341d40d03a50000074081c3c04541000745c1d1030000b0035402c0301e0303c028060080b03000c50100202c0d2000300501203030441d01c424070603900289400610b403000464011450114844a10340350380d01e21486808074451140025800890400102101444903000d000350004c2591466982e03951045040a82d01820941d040b00307500604108c0d0020b014040d41030f605136a9414914244032241e51000c003034451098802d410203940d103007006003141081240c4185000300b4100064040031001c0881e222105c1e0b400003800c3c003100000841c01030b9100301c4203840a0354000451103180c1c100501584 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 758034919 1250 758033669 758033687
    0x4050f1f0303081626150409020904080d0e0f010507020d0c08190909020d0209040612081e040302042901051c020c03160f110f130c1101061502120301080d0503091903 73
    0x790111100306d41d40030070b03003458070860320303281e80043c0084440e507a103030f4036141035600c91442e640b00251284084658608100326103000b0b005910008a07940c03500e9003000b45081503803a041c9040000ca1001c6101294090080b41d516502c0030b8840f980d400c003010002e403101c4044da40706055440c40040c2900d59401d03254050030742e86008403414004180c0d916500c804003050140302601840b000c001c500400703151114041d5080300238048007410f00d5587e400107270885041c40d42040c0115001c2501031840300c271740402c210941a09003810b81c00c00c0c0480c0f800898002d022071003440119070006005a03200f00405c25107420613940500d0320750b03042481c5490402c400000c40e08440610308011044070600e00542c80790300c001c0b0b0140c4001c040c3c0c1003a000c40c4000d081494881424005480001141d41c1e8083c0500e001500f20461210780e51080281d0092500d141480440d10841c170a1006012240d808078140c0d0304550203207811901ca8072400e240c04e0030640d000c1501651814120300500400d9002142d40d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 758036169 1250 758034919 758034931
    0x11202090118151806020304050d0f0b0c03061011030a0507030e060d060e2203080613061712090307050415081005070908031e030c070204050f1f0303081626 69
    0x403441130019000d0044080401e026010150304280000d0200342054039040355024002c100c14802e404041d1a2810120b009840c2400746440020402180d07040c03c01c1c1c0305c03a2a00e868508aa050f11100180075100e000fa002604100503000514106061180c044010141402000f0ba9540c4094030302080081030300d0b124189500c1000f0001483ca990341121070219501d082070459042c8003181d400301c49422004003032a5200820712640340011805226400250a203c051013941c010788441c418500240040300d1001810100116500e03900d0105510b0225031082d640400d045a0910003000c1100641d0842c00f10f52294075590003154400360041390003000907888002c441c03512109056140c1c45610708090300c0803900d0702841d20000703d00c4000c40d800100144003d050807882ea00007010b413117043d901403803402d2640040c8015501c2d1500c15640443ea00d21801031040d2541e9409080181c004001c0c04140c5001400303e01514014800681c0c404e12032849103441c001b00f44011094000c080d501 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 758037419 1250 758036169 758036177
    0x515100804030207090c0908030c0c01030b06070c0312050c0f101439040b04080111070506131a07031d010204060203040509060f060a0807030b0f01120209011815 71
    0x11014180c06900010300998040c0c0c040c3c04110709005800d000380404581c01400c006171080e00240c001414009010031062403806090721034041030005042e500110783d9241325100410842d0300003504520725404683d4015400ca410b4004000162a10302030000b010310b103402504488074403034a01051910510042107820170201002c1620b45860100459203050003200d106402101030700e11131a07400d8200700c01036208001a440d08911619604190321403488048049000d00c0361306000c1c010701da00c00580710f42e50f41c1030815549400b5600d55020b0065102840205240d07410b000c1c00c002070b0484c014601c010b000b054104020f0080092036880600d44088010540410036050103000300c40445510f58021810503040c1400c00c00c040001030812940420b5038403a203102a168500500003140319030f103900c083c515000700c0240070395040250092050f1501e203403034030702aa08444170503000300c0c00a8005071900207541c010b84401945041103e07082c8000c1c2d600155002c51789818606c44402e40d65 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 758038669 1250 758037419 758037439
    0x1060e070503041a060906090406060b0f0d18031e0201060317030103050d020a0804050f03030c101e060b0703141621111b0a0f080706090605031005150702040515 71
    0x1684c00844140c900e07561140b01c1e078010a069142c5041e03604c0e00039000340303400030380a6500d8000c2c0405a0144c5502e4030600b0020a501c0c4c19610a0310030007181c540c41810044d0344075904d1f1760040010440000c0b140070100d001e8803000c80c091017544000081d55008a00382211402d6100c100317681e40091004448601c1150300b18405240702081c455402035101400e02d081905080c200f1201c4d140340da601d0354040c07000340b0015140c5002088901c113100d03d134483c0054000180e0030017400301504807800a509034180342080040c0c800000c102d400399030b018980806000c004035164210307885410303010100080380c0708078402404115031180110403d81041907000300200c24050361811103461070301c5c00c40d07045100b202503c51203040f40384128090061410781c4081d00c801d0880b01c8182c03180c000c0c0040c0d503c804d506001840e0450050000380c0258180a8214500a59a075180700c1e861302659004c0c5220000102055409105541d89154020800e000e2860040318102c010049510002e119a400030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 758039919 1250 758038669 758038703
    0x51e01060e0f010f17070210050c09030d0801062a080a020c040b0103150e040303091a0105150301150e0f03030a05120609090312040f02100e042004060c0501060e07050304 75
    0x403801951440300e034403401818017540c1940f40c2000b40040c180f00c1940115015170826518920845108407032500301c141d2506050b1081c540360030a282040750a000c0380348c0050214a820942403007280b00341d0884660304552400005e141a20384030360090454402040b81034800c0e03000326585045210aa6013046004406401102514201c04420141c8049503900b0703c00d0340003d181140c0c0c440d0082c1030208001c0403d640c0c49100c98441c02c0e200e1082c446000041c0841d00d0000751260034405032800300da0441d41009034051300d07504050080030034064603070410000c0ba2182e800340712103c0d0005040c3e81c1c0b680140da40c040d200361711942c081440030ba0240009009841c0803180180034400b048015030802410700300301c41201030701810940f2181c81070186640140c1e40d0300414401c0070b10560310001e48691a00c2800241ca0140f0752003a000040c0c0d0650142c0c040500c0c060302c045901c146070050110606046c0783d4010308564200303003403d1444000300149540c2000c001d43c0540e100301081e000d941009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 758041169 1250 758039919 758039927
    0x201b010311070308060301090c0e0103030f1d0108090717030a08090f0d050d0b06030406022520060403050d02010c02101107030c02060c0706080703180c09051e01060e0f01 75
    0x1c100001e0108009116082c0480d2054181d654001006000041c01c545161948604619242c0c062600581100010b208050344000c20301414078050900400729851b81c000301c4204002000c600b8100700807500004d481c601c040000714010443c0070446400190b1144d50b45450703501001c5440003003100303440415082680050841090865800507015402c50340c001110158004a0041d11403030300d90014990325074600e03000b14040c901c80c600c0182c2c2c40803244103e07411201140e5183c182d401c0904140004600745070715070421700d40c41c0c1141d00d10000544000503141e000b180c00c054510f11807808440d14a58055000140c2c0c1e4489408451141a82046880544000c3c00950314121030611078000002e000d15507010350244020300e020300309041c041c40549080515884100051000018001440d415200e002c01c1c2e07002c0101a40348041d441e4684c000104d00e40d1241c5910983da0390000703a5001e140c0324904100e4170310607034040940e5075a0340006250350809201c00344154a01e0251580315030107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 758042419 1250 758041169 758041181
    0x40c020325051c111609180506070305270d1107031707080403120206010618050603040b0901240e0a02040e040201030e0c030313141210050403201b0103 67
    0x31150003809a42e00c1c807001c1101081505219800344000754001302d0504030140041000c0e2845030802c048458070307041100c010f0350400c0901000020a000000300881c0f40410b481e98040042e0a000c5490745071100c2e40400d4141e8000104141180880500c01e55900800c00b400e64031000ea41d6101c1002c84102140c1d1aa8010307c80100000c851440d00c1416030380100141002c94051585c09003419560389881c8622800c6241100058210000500c50307150841849841c044004620400b101e0900010170398500c80584003a00303050b41c4200003220f0000c01d4208100302c90282d00310464807000d03103200c2c540b410210302864080f065030100240f9503406074425502210b08403081c2801645030ba800541c0207281e000c012209a000e006480e0722070f03440400040192000c80e4080f05a00c41c81e24441c108070004000003036204a5a03890340c5038014400207500140034046181c0001c043d00c5620301a656400300c9590803c0110031140204035019010070040d00401c0d466a500c010012000d00440c00c03612 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 758043669 1250 758042419 758042423
    0x503060a0203101e031a0f090c0a0515040807032001031512030306081902130b06042102030a061418061602010b0d0602070212010c05070204020315040c020325 70
    0x41002c03810013080088056000c1c803880702e0758000e000e41d512030b00c40c07083e0750a054031100c40c480480d000344840c41112071903080c6d00088410242c1400001000050741000561182502c83c000c10305544040038000800c0714020034040045405082d80e0f4580018140309421100e094010f400c81c440256501a006406940111050304240d25007452443d100400d00c0070f0060341010b559000115000c68100300350302598003c8607001800402d6407040040380da00400c0380d0a645c03403c0203c00907a54540e4029142642d0320380b02855074612000ca40e03804440300742075003e5414450038407440c05014a6078000380c000391942415800f940d440c000c0401208516005041d0039600c40f10005080c0c90901b0f103c0c8a0a41d40d070300c004600100c0700c4000070508240300d0002d40b100b0340d00140c04011481d125219204401d0745200074003910b040070038080c1c49800b8012000e4000c2d50008000ba0f0031511490950b140214001c00400a80c2d0103124025507036000a40600d8901c4c1c0142102a141e02070343c01640390050f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 758044919 1250 758043669 758043691
    0xa091809150b1c0f0f0507080f0318060304020102030f0a08040c09020703140906130824130201050904090204052a0909130c08071e21060911040905010203010503060a0203 75
    0x3e54045100c0782d501c0c180503400d03156125444002da000034064200a01c000b4011001443c4150508020504100200f26105040d43c010010384000c0421f0390080c100c00c5000310344841e1650743e03500044c0e080d442120705d0303020b9400c3e000075030010440e00f1401407402140030b404210641e5489000c00350891145d000042d01244c0340112010841d44030078010509800081d200c81d091280c20201091003c41c0d40e000095540c1010200d400040720204110650030440e089030029800e12800e4900d00c100e00351030203410044001a02040c580ba1508844440741e80134008004902d05120400000031807e044248031100d01180180309030854819109400801002c0c0c11350307174646003240c05c04503825410840d000c003602140010954418058400204001000003a010010300044a00c0106c190801c50514808801d230813014140d4080c42c0d1983c60b03110f41e0000c1d0b02c40d5542031601e000d28407035543c01d40c490b0410b11030504100c4103401035812100f0550482e82c1541355901c4c0203050b4003046075050701c89 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 758046169 1250 758044919 758044939
    0x70e0a050f0f0a080d0509030f0d090b0304030309170a0e040606051210080601080a0308010f0f03030c052e230415023007020604021003020a091809150b 67
    0x3501d4004842d400711240205042101c81d074402900381050078001c030b9107010640c042080c800302d0070b003480029081d0840b400907101243c50380740f01400200650091204100002c4000344c1098000c0c1c0c01300750310301d030002c03103007503414201f01c05440031640650303061000580141d09450017400e15010b076405454482d200d0505000c1240c0c03034030828240040c004040d00911010000d2035560a010030360203414210081c1c01c0d50001810050708051044e0301090005c004940100300801341c46a844054a500d032401c800081c1c0613040c141c0c48d190318011442000c4414510000040303030701412165600c203100750240a1080e801d07407d290201643d020454400001d000010700150000040601006c1e1000b0010b04202d56011031100070024103141c1c00300748002d81084c1480105d59038444d603104003944010300c21494242c0c00301c0c0c008072a44207000300b415001302c0c40e034494034000d600a10280020317654400e408001d800300348000e005a12800e80c4c2649018845101c0201140143d000d8080302414409030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 758047419 1250 758046169 758046199
    0x110102281d060a0c29090c0a030f02060d05011820040303031113030c0f050405090a030e01030605130911060f0a0810031b0f080a0506010e1b040e070e0a05 68
    0x2940e10840c01c500401400b1941d1000050112a100c00c03100c02c0c21200c8888551a200c00e100102001b419040306a0300003180f0303c034695200804c000699503c9030200c01030418074808242c1c54021500b13a202c0481c104000400c50030480c014508210f4280e80051118000781d01c69110350035551401d02c04000340411041c80030902a400040700724821003112860700f100c0c601007070341e03000d01a041200c10140c3d001080000329071041d01d2002810040300c080002e81072418a5641e1b80401e02c030010709014100001c0101a8001d5220030028003001d000b90290074070b00c80e614401080084003c496181030a002d15900d0b007000b02c240c4d005114111a8145041e2400e07109030790440c0b00030320700d60f0628144040400040e8113001300c82d0b20703800c1c003648003d662070802c1c4481d50781c0358480d0490691075100355440b8021900002e1518116600c520307500441c0e0722402c1498000c90441100059044070020f00094241c01c3c400c150391094040d60340301000c081c901c404005103e64944501680002c0e91901c400b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 758048669 1250 758047419 758047429
    0x4020421030c083601020a1401020c0a03120f0b01050f07060f060b0703021c0905091005030a0c140906100815030d03020a03110906030412110102281d 66
    0x10018020b08041200301010780c2e40820b07a41c031048000c0c0c4604000072800e2007100710342080d103141d440c100d03102c40b140540d043d00003940d503401020f0180c45c0c54445681ca5030724201c00c2d4100d4a54420305015148490098100075203442405800c03074494514103a008000200c040c0311b140c2182d10165100f6207800ca00d181700b211541c100700003d6079215031710586420b804d4117034031400c0c0c002e061515000d602c64800c0d003400703401c0a4111a047c2c0d010b502040007034042940c001920030550f001240c0c4c549003512104080c940b0080140c01050301441801e0400060100501103039003100d400711200b4900000300c0d000e1080380301003951039580204181c500809124014500c45a010105203440070340e50040c580003e1a004910000c01c010960000d003541c6500c1e4140114204041c000d00701a1401800c2d00210b055444010300251204814850641e82103102d0b070f80c41062851100025902c84149001c040d590b0700481c180c92124629007407440f4020717030144008041000c10040c0c0024542a0081440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 758049919 1250 758048669 758048729
    0x14010c051c020901080601081e1501021005220609020613080f010209030c010309051606090f080f0d230708030609090f06060f0102150f0708091203060d02060702040e010902030606040204 82
    0x8030342d0301e27030164001c0c001015201d4468451104d03c0307a1880a1341140300064140098004441c28842c1003070100030003080c070440c5014070850005440c0141014504144004201c2054001e600243c0040c1c10041e90132481c19030025a000c540030b803000c1003090b0011900306d21503c841c07550923804c000c8a2811560103036100440c40341c043c0c400c1e80c2c014507880d440c0c00b00060049d0080700200b44100c2050201030442c0032090041d11549005000303000a40c54440e40d5044003071420410040407244104070a03500150f008d0280c6401420203440f1a100e14200496401c00c481c07042c000c8035802c1c0002c0e07101100295200004071340c1c00c040c06040c1c031690305000c020141c02001605501c1171008825610b02e094064511039004140410703210705002c0e4004102044c05050199687e0128036070113140300c0000200c03a0044411107501e109048503202007002801a2a800fa5019103840503601c51890190818040c0364800c03419a01c455549000308000c9000354080c1c0c400704407509003501a0524224824 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 758051169 1250 758049919 758049931
    0x2130e0f0c07170d05040618152c010609050604051513110a02030d061703040605091c14150903070213090804121502040303170414010c051c02090108060108 69
    0x301c14003201d83d42410b05902a201105a00e9524410401031143d0f07031040c2060082d80052075002c200544c0c03516507180d056a0704840d5120340d605411109402d504d40c0503002c1d901c000c04007090f1a00711480d00ca00904941c07240240603130400b00019460301c0c0c07510074a44581d0b1401281400b04890409200e81c0c50310b4002d50700142565410640030343d040c4400900420b020507401581d480140219160950714180d01c803081c014044c5601380b4524401000356025600c180ca0400d0300c074014400000c0c0300b00740120080740707203850691f405006c0c401d0826030901c0c0301020b681110701c1c0741e00445c0380c030360311030b000b1120b043c0030384c0041c07240000500d00261100da500d03410780300105401c0441d842c3c41c0d2882e403040c4c2c081341c0b00e0804141c3c070308200b007040d05070501c009405100860800d45103403400384c03142100340303241d601390752614000600700b201c10003040700038404410007006901c14455002c6c0403580480c50150702164138003141d11003581c0d035000301d62513600103954217282922004015502404007502c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 758052419 1250 758051169 758051183
    0x703140d270902031519080c060304030225080c03060714130b132904060305060102101d1b030c0405180312012c1909060e0102130e0f0c07 61
    0x10001c0d5140061030050003120030030100c1060203c03c11105440080000a051011b44403c10002e0008a103c1070504010345c0c2207a680d540710f203801c80c18072602c640644480c42d61041e14142505d002c4035030302c0c1510001d0007211203040c54101007580d00c0700c0445103a400200340c1c02014803101c3c1c21402521500900310640c607451601e40401080a4001c5104643c007013600c14010444a035080c8580119006100c0090030b480403030401daa18184102d001c0d9500f40364884003c21000c0c1d1081000c601c01400c84001000f200881c1c40d46044440600c181c200c040748102004480c4aa8240800c006c115000500905880001c1d100380030203008000c1c00e42d0600b001d400907105448001780024003442e03040c0c0801103103560411003150030b042e065100807102503c040701100b01800a802d41241c01001c04506424001002c001c0040a071105807030040116091103403109880005402410f82c44211045003400c45444076214080090b00710740ea51640302868012a005540d554010440075005140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 758053669 1250 758052419 758052497
    0x210030e030408031804151202091e0f04060b06040501021c05040b0a0206060a140f04050406020d0612020a0602061b1809010b0d05091207021207170703140d 69
    0x190f201c3c1180c018400362505986174800c0e4107264949480780c0204a28128441c1304030701e040c015802036000c140c50f40240201e0035407001c100160b04040f01a0712107100c150110f011490501382102127041d0503901210a24102000380c1c5040c40c021065509175001a401030064546d42450a41c2c1406940c0c0d0301c000f48800dc10000c51540d9a120050404440369002042c0d9820200107008100c0201d50008000f032510049443e6245c1d200301c0f10030510b1008540103d016151810500003c0c071580840d09102c61812a0018a6002c06000400218000c50782c0341031844d81e40304241d840f000210f810b64000d6806030715070711020111801414602039501103c41400f4890000309031540020b810200e0144800301d40503081e10311a004123940f0409400240050700b00340301c15084680a00e14000744511400585105041c43c20002d0078000e15440c440317001018103080c80c403516400d441c042907801d995081024510350800041001503d000c80d501c02e02c0304882940801c1c2c00d9200f884030704504d010000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 758054919 1250 758053669 758053679
    0x50f031606022802031c05011505071104150603050112050a021005072003011811010e06090a030b19090209010e0a1b02010203150301140a020f0c0d02150105010c0210030e0304 77
    0xa015070442030059002555078030404401c0100500b10300740c4841d11b050030540140001880c41b07540d0b6048006604050b40c80e4005880c00310409508240c640c1c1d041f601e8010098000d03041a9036910803900d454400b00440d9032560507040304444460b801400c20741c40000c00c000141030001244202d105103251090609a0594075406403000d141000298208041902c00744c4d45400e202d02503403c40f40b14001c8800c881c00307650b0485c10702c082400b100e06000c4518516892910380e0800ca0b04000002403030200d0194691400070701a401c20f0b5600389003180303454070300052100c040c41102401c0303400810541c00e680c600602030018950040505c01d0954944090544420100311004510300544d000540c691030b10041c0d008800007008034191180c0c1c144070180c441c0c14150498290000404200940c0d0340000c2920001c140c45407104041113880381d007160038482a03010500741c0720340300780c5807288080b80d0740c0c3c0e001103441c60748500c0003950183c8940c000504060003544a4404084400b05407410070f6907030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 758056169 1250 758054919 758054977
    0x20a1e1a0a02071208060d110111100c0906180302091b0304140d0315090e24011a070b18070510080603010c0921021912050f03160602 59
    0x41c1c41007040c0320b0b004102a400c124410512050000c094540055203191200029128140c030604c040c107076148860040c00141d201c0c08484c1221744c00b42c4210b6080b00c4603003003104014560013001d20b0010364203040100d582489101c090030b034044034032821400340d400d603000c21600c4440501201c561416400c014081c643c00103000d503205032701600c85440742da9107a00c595800c0540703612840081618124100ca078140100e0b00b000b00791032064000054003101d80c16642e207402d91b8a012400000c2d04820b0054209006210030ba05039003185029001c020007084440c1541d000714a40100048158000660248040d0a500c07040f000346800b120100c80d0b6070306c0420702125a814900300010403150400010f402c09000b8449820005d2078011489882c3c80c110444500c2040c00501c00d0510301001507081d540c4416220130503140b040320305142540c1d640840101c0b03c07050081140c842c092840c00580721007021080d43d400c80302034900c06103c4421580c03407400a51050341e203511444105050104030101d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 758057419 1250 758056169 758056171
    0x6080a0308090109330507171005060c031b0c060412020f040e0114060f0114070602040323010b090705030613021b03131401050a03020307200d0f020a1e1a 68
    0x29440441c0e0b500b281204003440104194820045d165041c031040c0040a58007204401d401025045c00148513141d001c50a809800564446580f0140124080007808404001440b00300d503200c100980c55072100940c0e030344451010320242d03408501400100070708902190302908503480102003840b0101408001411590520343c00e1103a603648035407010000d00038803011500300100302ca1007604074001400007440c40c4008801e25013480c50104414080022030340665000c0d65102d06491080d48140140650846250229030b40560a00c1100c0d12a820400721741c500030300481c1d44991840d6283d80074041c0702c941c840e40e55110580d00300301c03000080c160708603040c0c48019074002540e40c507081d80312034209820094008208518118003900c105a07000b00803194003c0ca45d040160f1079070f0742e88034192200d0100c648040ca5041c441c0c030300100100404900b04141902c3c03501c0f481214400080220380d11030050400500d0036080450440d07800040b1100003403150b100b414600c403401ca1880c0d04010390070f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 758058669 1250 758057419 758057453
    0x30a050a0e1503011a18010c0f0819091d15010c0c030c14031203130309030f05060406050a02090105040308070611070c14041803110f07060504030b0a06080a0308090109 74
    0x9000f000501614440392a85446540c4c1811200d051a040c004180044041005000e040c080031481560400041c0003000805640040500c0d8540d8540701c20700901d45054045040002c20314000400c2c112900603201c01c0740c3c11808010000c42d07680b1075007141008410326040d07040c0007070340740340c6800101344448600107940301c0d660740d00010b40341002c1d0002075030045010703d20030b8001402d0300f400410302c17100f40da40c04100f8000d5401c41d03954a00303007511901c0c042d400113482d505003403440c2000d00000290b03c6028038401c0800704035680e00e490350302d0201d002e101443c50001d6010002040800d000b00302070300321640181c80000f28100d044020810790780c0030b4001103680300106082040000d05038201008000400e40b400d00001c0d503420b440030f8210b401180000c09200300d14100e2103000318100100c240d845c802c030044820003512804003030002d400c64482100c2c1d6070312010010b11580c09a00861045500c02e6004050b0300040e0b55007562081030007071911010f50340e02c40300040403451800c50880420 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 758059919 1250 758058669 758058709
    0xb030c03131103251a030c0a0309060e030705100216030809030d0c120605010509220b042c150c1b06041a0f0f180c03030f0309190302030a050a0e 64
    0x21a42058580350320030651060780e070008410a18000d82e8440e20840f0f50140341d00b071074240d0310b41c000d048c284c1c0100792096010309880c0c030703001d0a861000000802003c4c3d041c0540100c50480003920800003e0b440359582018003607000d15002c000281c055550b46030130240c10004c1d2400c00c0c0780c2c0b5040c00216501d14103a03030001a4050151100e01016200e00c4000c1c140131b01c2c1040c54080c0391008130b0220008500180614203521800248440181c2e12041c1c44810040c01809a00c400011411503464403000450041e41811461a10716000041a0100301c104803407103101d41c0d5905a45201c43d8200081c0722241031844a00510b0a203c1441b41c68402c3e4072900214084040a1200d500319a4005180500200003801489020102159226401704100e10181c920551040e40310b800c14800d4240142c00d48004101c40301d46a00c0c0001451091131558101c0e1090a6486508002c1c0c400c91540a80960410002e801c26030740309400803d000c102600700080601d40180224040446034140c4070115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 758061169 1250 758059919 758059963
    0x24040f140f011508010b0a0f020102070b0c090414040f060207050703061506140a020c10170421090308250219170109050c1c1b030b010b030c03131103 66
    0x341d101004001e4541c840f514003c0ca9940c1000c030b46801c03900c600d030609802d01c03105014110030b65100350100c8288980c001c010704c03d54100410740c196150000050036204074207165900500b00020508248241d40100034450400c1c0d9030385621000354400f0030151114080d00c0c0d0f001c0b011580c2c0e0b00a01640e500301c820500d0503a45030950042032011441e0305284601000c021103030701d09900141107190600b0481d0450007241310303c141624900c403044a2065000314000412040c0b05000761074481451803081e500a442c070f0303608011500040c141c00002c0008206010f1022035032812031800c440b0603d403400301035070fa002580004950003129440807031004081007080c0030208041610340c1c40b8005c1703e1b000b4400e0740950350f510b45d290040700320303854040c041c10805501c007005114229035084c0c0d0005035444030081c1208034180c0c1c603181c81c082564914001000042c10140c02c0781281c0c4542525081c1d80d055455481c00e094040303d0804060300c105040d403401701a2998240310801c46e6584a0001e00c4e61 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 758062419 1250 758061169 758061179
    0x6030f1503060203250e030d0305131103030408070f080f03040806011a0912031810090902070c0521060702150606033304050903030603060403110a080a030b01030524040f140f01 78
    0xe00035043c00c44c00c8c00c041c00e0105115a50310f28a80343d590040e80102000032039000140800d03e1070003654480f00c0359100b8400c0004a50b43c5402c071180640d82000240d68104e40c034400020f50340d00c035620800440398044001003080740d0b6420031200c1602c1c0c03d13150261404039a140021000b203041d5591f000701e500300191140000c0700b204944451842c090300c0042d1011124480600000101d00c100310310550006166000c002e03450f680b01015141c010041c000000584040c0503101840070f82c0820b0703611815001c9601207000180c0070a20301c4a00c40d84000698410702440a41e803c044c108004102004403d0391500180b0301051001c401072826250001201508000640d40c01074003400c203d820400c1407040b582c602081c000e51144e05402c003641418400c411091510101e14805008000e001c00c564200941c55003141303000d50803d82e400c0c801c0d40c654001d842d603040c240e603149441f4900c440c0182042420550401d421074000303d54000390442e11100602c20215003210b117106484884401440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 758063669 1250 758062419 758062423
    0xf030106300b0d0f23060603060c09041e1a0f030604110d12091404050610080c09041b03110c07061409030d030606030f1503060203250e03 61
    0x7000081c0351420031461069020540c10341800e410a14a00d15201d2045801944507640007440303095100d40401c00c41c0150741010784003841c00c600255500c10a400105504d0070000030254041c000007005420152102e566030070040d40a4040b00ea0071035120100311242c600380b690340d02100d1096110104215440c010402000c07285101170611902070f40d0b0072800749840014485902540c004801e421250075a000101ca9929024008002d20f204d03601200e00e15034024102811a0501d664865a01c41d14904000c192941203603115000003801c280751080a100d00d41060700012072806243c03800b01410042400e546050820800840d406c1d1102e01400d6850b11804c0e100c0c241300b460780d03410300800840301078540d03440f0310a0742c0030005080e281c1282508514121100f4103001011a80003846250003d40034180d0340c46240c021910b041201000d0980a001c0c40340500f0f603801950320118110b80d2004025040036002c402d14400034031240300031100b00c100703040c100f0b2205e0700c55800045035001014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 758064919 1250 758063669 758063687
    0x609160e04020a0314012f030a110f0c03220321120204031110032a200c04050f0601020706050d0b030d02060a0b0a18020304110319150c0212130305030f030106 70
    0x200d115130888000c3c1c0c00701011f8026281c00600c0c0b608007103076a02e18102d041e01e15019046140c500200b00052050b00c001c000001004c90050705000801c0c0e002010741c40300e0032030816103c007421030000b400312115294002c2c200030100343e1003410f00414812410103040220b800a030030803103841003401c190440c07516010300c0c640c000340603e19041c49030000c4040355403410602981401074a540960300c4600050103507130401c040341d40c0d055400203001d40131600d1030703a0380250922040c003403468980451780522040e02d51034440c01040e0000d04c0c4076032401f54201c803690300c006072010390740d0b503504000744890750b092041002031042c90b40201340c50308016215204682180180d10310685400908001031219a05100303022a2714005c0181c50b0b50303507400c08010020305060300f81e0789406414000c80f00142c007615401181409900d0700c1c600604820f80031302c12251940c800f140560302c20405004c0d020880c0000340f40781c007030039441d005c2100ea80360303034440c59900700300c206c1c0d00500404401442103690203d891 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 758066169 1250 758064919 758064971
    0x150a08010c091502010603240510061b05010e060405061f050d020906031e0d121a28080c0f011b0b10030c08070303020609160e04020a031401 62
    0x1c000605064001a166086612a0540c5100c01401c0308055034000e5000c64015034004280c80070030380813001c00070314a02c403442510008929000200e1082030841320319400741c0c0c10ba920b5440802c02450600550819107a00032181503484500004601200740b00050140c1e05c140c00070300c0e16082c26100c1c00005c0c81c00c0300c230203043e04000380743c00c00503a43ea1140701a0701940660f018000b544401011a0a003000c80034000310032070200c40345922004000907046812a420740c0c80d45078462220000c4010381348004565018902a0945c40020340380ca0242c0601d510007249114010000d6800c181d030180405130b0014140790044400c0c07440c281003240310340060032000d182c2320811080040f010750489500701d002030050304181000480180b941e00112000e583c201201292859440340b4066441000e030100314010b0140c83c012a0781d0020000d08540c10b042ca141d80544c00714146100c0072079150000f042a6408101c4006c0000070409860020071a410b011002042e1f01500b0700c03440ca03281ea03170840c80d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 758067419 1250 758066169 758066171
    0xb1f0e07260f100b130e0106090515090a08061009061208191107090603050c0d12030b060f18010e01110304050904061b02031c020306100302070317150a0801 69
    0xc800700d40c0c82000344035a4090000050701e4540d854404026480d0010b0760401040703c103000807003041c4030b07450082ca80111806e840b40b080d00c81c0c2c2c84510841c1d036044103206240d0000c2c4040f540301b2281124074007034591180050102e40f00c065685148514180342030714400d02e040b24911041c0f003015014000c00010b01411500c110a0804564401c16940304070b0001980c800c407a60300d0031074035030701c41c5501792002090031040316020b0b40c03226181c2c4010041031000316054895444401c0082c1001f80c81c0f100d00682185d5184490300815006402416012441950160041107207580c41c0c4a2280502481c00d640c1030368161190043c000503146117650a1400e0500420783d014070711045000084a055800558980e2400c0e00c1c1c03072404901824030030003040c4440002c000d100703c60550000141c900304003011540f000300084101100202d12050320ba040d00b004400210700380d0503020390000d001052003440c000315950b8480b4002e0a80740d1003911001d19110340080141c16500e80121754002400082c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 758068669 1250 758067419 758067467
    0x3010e1303080f09010605090a0218041a13061e05130504050606040b030a0512030f0c0a0806010e012106150e100f110f160b0a0c0b1f0e07 61
    0x1c0203803041d40010100038200d0a0140000e1034840203411040080074040d00014060030580d1910700a500040d0701c00309506503261110f03625241c14001c4070007a080341c4491541c0303440210280b0480001907043c0102c0300d510390304005800408032251050a511104408614504081c02c121684500341c03d014241c0741468107020119401051468228034101e800041101d0100040313410240b840390301030902e018070000e01010284441c003d621400c008001c0820564030401c82e4451802034003081400190001c2c0099a254010b110851840505042c16040c04402d040100d00e058543c4030254501600d64000300510b1040203a5a495400c80e070400347c0c41068070034007248401c03a80704004410402c1011210480300d000e001c41070604120704054545a000f08100c0c11790b107141c0c48031500e042100744c40c2c0c00140d00030440e060ba69001003a9039000f244190580711740c8040d140240c19039284a0310210b48404d03030a0655050401003441164a203964a005100500100c181207441c5910030300d428 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 758069919 1250 758068669 758068673
    0xc0c080f010b310e071211010806030f070b033105060117030d1a0303040807030c060809060a093e1f050304050a1e0c060311070602090d1703010e13 65
    0x303d1400d204100c0c40c000508002021107246444095131054501d02490b00060041c00354103011800c010500ba216103480d51940418035980d0446507a044c019600304039001d201c589130000043d42c10000314aa41c80702001402080d210070103c040411308086504d0000030104541032024038010072130059071a5200d0301d1510b210740c9030303c6481000c405560380d5050b201c1a164125100480c64000501101c2d1115200e2001c20759032403460000b03807000c842c1d80c80d0000303501d8860605148152907140107890152075003500c00010300b03c05501100d02c2c1820f85056010058454072800c080d00d41d612200c11448088820f49800d0041422180e01440440d9180da12110031a80c6040c4404d500746003859680c0c2d181d040c81c80c141903144200500d050040d03c0c2c001c50741c221030344c111041c0c80d0244915020850383d0f188180d0803214090881691640140030000200e480c60707026149040d00540060606401079848800c03a840d000031800008601200511180d100818ad0941c415114a5070400b030301711507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 758071169 1250 758069919 758069989
    0x1c08070905100e061e0f131203120e0a080a0513090902060703140c100b090a0504051b061c090c0b211503010e0309030c01030902100c0c080f010b 64
    0x1103d140c6020300d0000a14546001a9843c50010302c0e2400500319140c1c40300e0070950f000d6501c600c0721a001c00e0800000840e000050f00401a46168103032101450040015103641c080d21101119443c04c0c000c5004580205044a0041c4000350442d6180342d44c560b401100c0040c0b154460b0010a240c0345000d44500060319000210792020303416041070705815040ba20f5120040c403031094406540d02403407080c18459105900304549005046410568541e1a550424115001110058503560000381c0c0200207050a16110c10440000b0304650720780035000c8912140000c48210352510140d81c0d0581e1401c0c091502c000310045e0400b450002e18166001030055010088600702e1303210340848401181b80001600010001c81c00050000d211400100082c0360326504080002e0740a0300401550b2002da40c82440340414065009104000039024640101c1c0c601205001c121032200d004503021905500400c0080385044001c0b0020a020a002052220781d052507210011a10281d202c041681410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 758072419 1250 758071169 758071187
    0x12060d05010c09170a12054504051603180803240307030302063403050711010b180a060e0405060108010c0e030c0f01050d060605041e0b19021c0807090510 68
    0x390b49803564480a020390040d8847c8d00803204004c3c04e120214500300151300c44c6020481e1410501012170201d1511014002a910700f260b480c00035104051071080a580aa40040c2090b050030305c0410502c600e5036038041c0c00d540b09540d042e0810306c04042280d640500502e0b10540314000b603014181300c070300d581c0e0065270790303100074101c2070600825800d4100d10712100d4907845095420041480303c4c4038680e000242c000e00d410fa0380072002850600b0b98109130b1005015001040c4c0c1c02400411000922400070b0301d101c0005046c5901d03150700d07950001214022506028042c2d801040901442d514003800d25085611105082c002d1005288451556540100f002000c015007505d01c0c040540d061001214148500091340071a40d01e00319000c202d03541c0c014060000d5441c0f030b2010050800440300a602c242201d48220a1601010400404031503602e14100040b101180100e81703801d80303016074030031812020284042c0020703260000c0017605507021540000501081d141c42c004071a60324001072000c84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 758073669 1250 758072419 758072453
    0x10e06040608090c0a03030f020709020a0f20030403050607080f13122a050c1903080c030405100804060b1e01032403081b030f12060d05010c09170a 65
    0x780b4400043c0700b82c034090008001c404401001d00551a0300c80c50050038a00c0e61001c044018410700b00301049403042c40c821102904410385500c41482e0071504100ca0340740b0b60310040300f0440c00d01c1d180b102c0014001c0010f0805144110007400c1c6078645107a00810801000703042007080e0803c0418000c4803e000d510032003c854202c4011059100303001c0b0140ea0810581c0034003913050150702d01080754480e01d88140010b20744660309640c400025030080041c0252000c0f440103600c000310701d0810024031008010043c0d070b811401540c1c01c0c25900d100260041300361013032817004075003240104010072071103208508045104a4401d40031024440c1492094041d4103250b60500d5503c0040340da1014402000c0202e00b031000122611050716890b28803010f80000700f103080c924039911005000c0d003101000b5103081000303d2034030a00b401c4101c40d4034103601001601c0d40c1d800c5210310004102045080c01404407080407500d803102154a45082107160740d001101310119500710341071000004603848101d4910300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 758074919 1250 758073669 758073677
    0xc03080306030f07081f05090c2e03050415201305032b02061501120b0306040b01050f0103020a080a09020f031c02120301140409080d02070f11010e060406 68
    0xc0d9403200031070700e0100200f104000a2169460010b503078140020500141301d07282c0700c5004803981118542060f44d000760b07140c9266030030645182c00345080288940c41c0348180c0034550080607042c01c1d42861000c06102d080c00010352208100310a008221403a01140f100d0b01c1400c100d10302e007040d141101450606a01c01d2880e90028110007506000d0b000070001e040300600350762807000307000c8903800017030446a9003070000166854030b40302442c00420305502c10010500c045007011042c40045860240c80307145400400c2c0c2c0c40d4485802610100a800e21840c850f11845906504003400c0049410b00d029030607041600400001008951162909801006031040400c86598520000d0305040c0f641042035058414502c4000b01c0240d0b13a0b00fa442000e02c079800341c5034154041420445a40310900543d0b4031208213017441111420994040021113000702949410020120502c1c0181d0b800b000b4142c0b0b141840480c3d080c24007001490b070b80249082420003904210303c1901283c101d00803442281300f84 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 758076169 1250 758074919 758074921
    0x7020d03050c0d0c0614010e0412230d0b03070b12060d060504050d08070315050909010f021b10150512010e03210f0f0a0e0304030203010606091e030c030803 69
    0x250082054500b04400310040d14008545500e000f0030341001c40d2403e50b44c2c242005200b6107007090400d82c039030680340c0ca81c240d9155076440780c80f001d0100e910120500200200c00440161160400007a601c03640f4000401c030340c1d100b19444240040c0c914041d01c06119404c0500100000c2c80c0301012502d1400b0a01001500d9546201c0064400c40000002401c2d5038203210030031080010100f03220b5200c044a895000d05a00c1d820021000c40c0e00c0c40c021011407440302071b0300784031030300d00b0303441d920303030020402d0004a0703200a81789001040e81c015408035040741414001c280500c01050140312140c2542960030002605507030030500b20320036984126401880984000d0740440710a410440028500e4000c695494204040003001403c2e6011074178043d28155011500c00154211200d02958180d916900c803500c6150000005148600710b5a4440c802040b0000042e1070038001c4000514a64480c0808a49841e00020f0b140018201c80b4401d82c030300c0d01042c8000344032000c0407010b0b41d410402207a12 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 758077419 1250 758076169 758076173
    0x50a0b16180f1517040501020702090c04050306010e040809030a03110f0118080f07050d090509060409020114130e0a0501141002030403080d060b130302030c1914030307020a140f0f0607020d 83
    0x200c031450318901c0c04c02040d44401c1101780301c0150010b00c1030910998902c0031a640d035031030501c010700440c014a50b042e044540100714288d0100d0160390000d006103102d0346080d4104000031b03e03103402e500046000c24420141c00a840e1000e1205004a00791840240180500091003080d403890f1800c00900030400803500c0344461540200365a5495440300840b440b1faa40003401505602062007040c0c03207a00c07010001211400c09009903966243d041e164030740c0c8540105c1d0700d10b0198010782a00300c3c0003c600b51000595a4000e02d586010702031900001070994105000300925440e03075000680680d01c03000c4405c8650b540002151304807030f00300301101c0d114000d040d4800b02408655006c2d403c0120b001c01c0c504070070603111100e4004c0300e00c2141112030100c408410b10407181595000d400808207484410404194001040c40d0f81140040a030781c9444601c1d80041c030044026080456000d00009a01d5494105030700039444c6044110707071150021041000046640c41941e5009000c1ea04944032101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 758078669 1250 758077419 758077427
    0x12070207031e0b012d060e10140703081f2c0613020f16052b23040509070f09050a0302060703030c03110412111504030f050a0b16180f15 60
    0x2d001001c6246520391702c0e82d01c031030040004c5506103d0758841d1981202c08a8000d00030030100780c11202500120741003020544060720419002002910000d050848031000c020700f074a2258058002b171010704181e80c4081c00d4281803601c018082e81d001000741828000c82da914006089a8050380d00780144c2d82d911010807512480c0503404441d52500e40842e05101007180205a20401281c1e0f40944818014603d6403103560342e0b4480426000316040003000200440851821120b54080da20b946180c681d0700c00c0440e0062000b2240800050b012078030840d4602e0b0322072101780003080304881c0c0071912410341c0c00280840c0302e1100020281650340c4141c0751707158003d41040314a14061814a5101c5907100b0340b00c0040d5580c1d503030480d00319400c400036804070b00c5c0441070135680c007101007226424503007103035951212481003142c25151403082010003800a0320011800e84942064034130003050b0111503101410318034480e41c142c02102c42e420405d2144c0b07040350b90002c080300e003c40d4007002c1101b40171106503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 758079919 1250 758078669 758078729
    0x12061214062a12131a0613090201020f0a0f021c0b0c09011707050c0c06130b0306060d1a040c1e140f0f09100c0305180612070207031e0b01 61
    0x85101a0203c2000351944001c0307000b110150207000040000568058284d901000444201e07900c08065103400100c40d07001d0384111100c2d88103004a40008400ca00c0b43c81c0b40001c076180032252400700c04541e05c21420301d9601008106da101600360740c0d20009d550f0b200b12030280244211a050307408120301d00e55030720526288020100d60b002000c52802c0020009085511500c003060b583d00c40c400c80ca402d14140700c82115050b4031042e0030743c500c00d070510010140690003e054190712140602401030301e50891b108210b0b8005d9080311005404030301100b408280c8000390460b2041c0f000c070314480300c407400541c811000711016a240502542448100d0881c02e8002d8006206c20400082a400d0f100c0e03502d00001c2450060444402519800300fa00c211360070100c0010040000b40c1c20300c602001001510704134803040358001e006070300313049002c0d46000600e001103e204005034007108040060000000e02588911952415007080002503110052880c0c0e06124401d40080e04150342014516001828 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 758081169 1250 758079919 758079937
    0x20103090f1a070e010c0206030112030933170402040f020f210c030c070308270a0b060906030d08060f0301090c17070f090207020112061214062a 64
    0x2d042e00c01e4148842e0b4410030011284403021980194040c0d00b9580901040107103154014070081c03540c0e007801e0000c90f004d07500005c200c0500c08039010104124642107806154001c044500040c001c1495100e0320300000341683c3e0350140681201c041503903035038039966603501580503180403440003c4105807030000d100c7c462036810780a0000c10a000170200c0010713601c1c40030540d00380903882d9443e0703016125805d00c0306440c41c180f059070070006e4100003409034660650003101186030908554241003000e132204564203042c455604401c3d4800b0030001054440783c2c0100040d00c0070200e5141c00b81c0840d9452650086140a0160a40004074107aa0b00500f6850340c100c098000d1002030298034100a0745a4140508141000e0141c84001030300300004a040803540c1480b40060714900c1c0000340002075021000c2a410003032840b5404541203820700886005018004480215441e1803c0c890341c01c03201040101c1d021340001081c03004400c41404040590b0018400c03040d9994584103141110344244000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 758082419 1250 758081169 758081183
    0x40b042d0807020f150706110c0a020d0519080a1b02010914042013060309020105250203060403020d0f03020408250e04050c0f0f010c03141b0105070f0206010f03020103090f 76
    0x1c4106882807203000f400e2883d00c201028400e8500d0300c1d40c0f1051600645055110951003044ac8030003600e4004401017001c0d009009450140000103421a04240206c40503117600e00c0000300c1e1006c0303a038810422030a2032070010106003002c410781d000030102d143c41c3c0701e4444168100300902c0700982d2285c1c0464604682e40c81311203c144040600500a50003801620118981403175001841c64000d015600b0a242d05a403000e16000d0b0902c0120120b060740706088010001281840c001a20204040d070f0080e030094005085040001c0d42c020581d4203c108203c3c1014014041001001c0c00000c1200a110322180c0030091030051103801da0796000b44c2c0d40301014090701c0009100c14800003007203040c940001921100841c0480505004c190700103c0b060300c0c0000c0781152000003092081c0c0c40a0362006416510b9880e000f0780c45034000c110f030648448100300d40d560300244203829401900d000e01d8440c4038005000175600d810f09500d6020414071000c2d040c0741c1c0303540c1440108890340c1c424814040d0700203e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 758083669 1250 758082419 758082439
    0x901060504020c07151b0b04061803020c090c09061803210901080601030204140904021207170c0d0506130807060c180803041a0c070905040b042d0807020f 68
    0x80c160b40e50b0346091045c2603001442c85055450782d031041441c2001400244407002c0009800da88401030000001d000b0303070741543d42d0801d4004640128040398003d0340a6802808000e140000f08610b0b85805000401250410062020280c6480301585d8105100318000d040d44c2c0901000b003814000c2d0450f1410301540c500400e1100700f540d00c1c3c0a001300007404e80c0d641a255a4000043d03040b03100e00d0140c07000709000d00c11000118602900c0a42d030092024104000041b2080c0006142140e07941007002040d004959042503407400704200d00c842c5c18121044030302c0c00201d07210b280e19040041c2041880642c10302d445800c4c08030410465000383c0c0c2c4800c0c100030005403180010b0030103050420200e100301c0c840c14001100c47c800800d44040d12500c0d0820129908401260b2085900010201c0c5990107003c4001402008600c11140b20b82d0007407050b0011454549030249003c08510421a246007504090032036410058141d40d5030305034000241951404a070000503a203030800040c1d60b42c03041c0e000e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 758084919 1250 758083669 758083687
    0x7050f03280306060c1e140a060f05070c031b0b0406020408010b040905070902090117041a1608180a23011406060d0207080409020a0f090e0618090106050402 69
    0x4035505504250403a070100c8108812401241551800d21409002403101c5144501142e0000000b028202d40d800d004142001550755804148150000400d1039401000c1c4107002e1001c0c502a903445410204410131003031074100c001918002501c1406410841140d501d0502e81c5950030702c007290340340c10140341d002034075143c50194043d501ca80150b980075420002840c440e410a40501c0500e56448409440f58906101c2040000c4d000044280d0400103190031400c226080c184501d8040e038040e03881910b070407016184021a00380040c101401c0300000c0c0311800c652070341c004a000d8000c40045422000b02c070701240c0e894500805403c020340448249540710040e080540c2400b0b0030441c104e4001d200a000b54202403040c00001c8030b600e0b410500c20415601940d442c0c2d401048080e02c036401403424503488455400c01c80e0460881d207004a1080f5400300409a000583d21005008820801c03d951800502054018403e40003441c11034191002207400c52500790040c401804c0d01900c11512030300c4d51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 758086169 1250 758084919 758084947
    0x10207080406320a030b270c070804090f090213050708010602070303050313020a03080a030906110a020a060515100c021306240e0a120b01062307050f03 67
    0x9100d002c0100e681e01c03440e802410088150002c2d07651419260302a40042081c54121075400004a4030400d0b40e12080d1030f485503940454006ca11803008001c011400c0702d6160b00204800c050001c0e2200ca03028482c000000710400125001d999010001182c100902c2020001070140b88000a41c00403100540c41c2c0c4441c4241d000502c10441070b5684003007030b40c2c2c891040c2e0f04c5d0f2a285c040640001d03801c00c0010324000001468141e9a88050501050340c2e07500d46810510340c01071061540080d03269040b940a01c02c0c2406035201d8483c10801041c40c00241040c0030b9500d424034400100a192913030009401801d18030104031045001522032001c02e142d0080040c086603452004900c509060040f40c0040641c41c45201e043c0c9401c2c8080c0010f501c0260740461080c80200480020880c1d04080d4410b01d4848083e104020300f20303260703030803c017000c1361030041c8032a82c0c160802c2041190a0124a0044e140011245840c45d20006003a965540f05d09160741094501c0324069198400050001d0740700c540 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 758087419 1250 758086169 758086177
    0x60204140a090506010c02191a030a0b0105040509160e03060106030e011b0822061103010302031903020d0e06040504051e090a0c0905190906020a140f0d1d01020708 72
    0x4032402098a40c03a01c0300c1c00c080343c100b0340300340e4002000d4076021801424075550300100848e00c201c50424896640c83c00303400c0900846080110000040244151205c0c4c0c1d00076401d0b000c1003400c00e03508040c1014041455090010f011001c1107011207540b8403172501402e00f406100d0409003c1d03d00d6981c403214050b0240c41c1a040320f040030362a10f148110004216058042001e5203546e035a0a42d468001154064644039115007402001000381c680c000f031154402e805171360f82180c1c8803c0d242e41c5140101400c00c0c40c400c401000803c040922000000e41c0030612a401501500380658512071190102d501401160050342e001481d1a040c0f000303c000e40401542280811411040541d0742c00c0781648d21140c500b80300506040b00c0b5030061180700040d81015522a9204a04003201d0150b20030300c500b610482e000659949900003841c001041d40420080d005070b10f0501c00324680050400407144500c030340407120110f03030741d1743d481a40c2c0c00c036544211180c1044950029529451141088800c0ba40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 758088669 1250 758087419 758087459
    0xa060e01022e0c0f021515010c02150309010501050f0301050403090519180f15080709090204020c1606080903090904080903031207030b0a09060b0d09170a0903110607051b030703060204 81
    0x11550306e80134010800d40c035699104100004404c0d85c69407201005440703c2d6a00344c0201c1c0c1c0000203001c21426011003030040d5102d14540300c0041140c1d45424140a24020201e00d0380d4000c0e4144010040404d030041e80d240110303441603592905c10b10040b40c10a61040d2a604215140c0201c0c0e81180360740d05a903003041d10f03008510b000070084181d1909480804841520400c07200307420015042011a01c25800741c1a503a00182c805498006601034050404c0c2445041e0800c81409150900030103a101041070b80c010011001035207011186000680030401c0140010240480011050301f60f4400b07005555425440500c510a2810402030140c040d000741c0708600e000e680c1902d400205a1214002e003000c4461143e4214600403061038508003038000e02006a80c03003410921500f1038003003034030024824004039a660007401421840d01301d0003072580000701c0d40700d1842445031340c010810116803101544148001c50b00140c080c0790219007800010b5002614aa101080000e2100141e000c1a45000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 758089919 1250 758088669 758088673
    0x17010506152106011403010305030a020607091a030a0603050327010507030504030f051f020a03051006050301151103030c18010c08030109091106180a060e01022e0c0f02 74
    0x4005010504490044204101c00321900c2c0442401a140c1072182642240045c0352800f003d00c08210900119803003030340100c4d01544001240c042e0b4542c14080d1a81000040c80c140d217203d86010028500c1c4500515605204c40001000c28540e446542c03003100255805410782e51a00008034070708043d28000072200c50b600307803103000c6d400003584624200c50036991315894181c2860300390b407142100404108412907646c0310f54282c10011041c50706011002d01401800542d4980017002c0040590f1005000043c8008108005004080e0440700b501e06682d50001d08050711800d2010440302400d0911008005010000034012524005d4006029219004400e907900a40f20b41c011252842d05c0741003d080e4240a1006210740b20150f0410362045014270b48407036070000100000362890748403c0394140503101140b482c003414180010002e006003402d0814809441a03100041e44034071241150141c451040803000b040250060034010803260301c04001c002410781c2d0980034240448a10b1940054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 758091169 1250 758089919 758089939
    0x906050a17150601030b030709061e050312030726370b0f0301020310030506010b07080307120e03220f030c0306020a0e120109021005070308180717010506 68
    0xc03055469460881d81d05a0001c1156940c80103200e15a044040c148034100750319002c588855a41c2080040c0246c92080000a202442e010742c821003015901c20b5100c40c000341200410032a60040390581c2d0001c000d8511a80e6a81c0e420400c443c01502c0d00000045150220707501d22082e007202850a226080382e04002e00544890074841090405031100d003c10f1680303003852055081104d4011069841020345851140340c3c030000080d017a80c0040b62032205120452104106010040200d035006102c000c01c002e1401e01d2030b4440c00320074400100602c090041403c1c00310f541450550160609010f00702c2a292282000c03003403300c061000003540e1406615480011602c4480783e06844102c83e8044c42e249030413442c654440010f50003c25010b4140919558021041d40391800038403040b01c8290000294205644100120701c2c802c00310031410008284600320000c3e411201c403681003d01c6212402c029102030045925040441e0000d941c00310200a00c0c820708141500418022030040303800d0500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 758092419 1250 758091169 758091179
    0x504120c03141b0105191101061d090d030b09070c0203070542071b0503120a02070e0f01090515031b040b0d0203030a230a050d1508030f180a0906050a 66
    0x2d1b001c1c03204072902c02c528626550300c040340240d1403c01d604e80d500b1b0000c54400d545190f4500c40d15035a40745001200210030400080901c03e0050062030000342c10200100e041a002050803a00300038124802e11405580d65001e558042001c24003c1000901c424900244444507a413014075107040c3d0304014410b4000c0404041442d0540c1a00f4108002118101001d94481c0e90350100000000000101141808101a1414000d08400c4541760040c0e075603d0300c0e4040024a80042caa2209080035201e60600009880c9485050b044400030500070400352200020b6488004401600c42d43c584201441c0c50b400100302020f014203000100c1e4100100e1403000240050031601c41c000030340c113400030422040b2590240040c5000503080c45a20090440503151a091030f0348464101400300b040031900d0020003e450280da1407003c0c0d031449012502c1e140800c4c80303945c2d0064008a5080c0c440100701585c591300306031040c102c5032301c0043c907405400c1e41d039540e941c000300703c01d015680c0500208540811 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 758093525 1106 758092419 758092427
    0x3150406030c0b040e0a0b030d0e0402134721040305120109022d1201090f0c0c08030f190c03051005010f0504120c03141b01 55
    0x4d50f840c18600103520200c1300034941c1c0c00343d0342042c040c0517280e24007040c0e28400c200076040650a008581002074041d000d50340350b4829518070b07403200040c1c62038a0100c18a07580440c0395402c01003910328132641348450788003600041070000e01d542d40c20341c802000000c01e0407440c3c08440c0c00300c20346494140c0b0000d540544065002600c00300b80e032031b0b008100c045420300505000c1c4007140b0b40325581d45100d1081041300400c50300c0400305802206480062011281400a41900e00c25550f03103841e92140108891110720405514169841040c2d0340a090152003817600314041c5401c9d56908415541a03030401405c05611141c51240d04052900b20f00580382066001e85002c50980750000404400f00c1c5968045030412401c2c52402c803606030400221425200b42d80100700010107681480d0098406a40c0700130401c25102c09800b4040c03c02298000c124451029548501004440116 = true := by decide +kernel

theorem cover : BRFrame.Cov 757913669 758093525 := by
  have h0 := BRFrame.cov_init 757913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 757913669 ≤ n) (h2 : n < 758093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
