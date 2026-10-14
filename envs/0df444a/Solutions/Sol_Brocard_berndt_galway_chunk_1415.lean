-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1415
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:52:27.66319+00:00
-- url     : https://prove2.me/submissions/0513f3f3-8956-4f7f-9674-9b62938a9d92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 254316546 ≤ n < 254496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 254317796 1250 254316546 254316551
    0xe090106030f1406060616140703061a011409060a050307052208190308011503020f03090606120d09090906180803180f19031701090b0f01020102070b1503070306050901 74
    0x10a4201801e013180201000c0c054401040803440d041f00c03031200410000da001c440080072441075280e0601d040d00302d0b00000c00c0c96190415000080200800798140444240e81710b000c00d003061004c01d0342c24007030740941c15000030b800c0c0106503c5070300074009503074041c02c2807403e40d082c040042d0b088040c11310507400700781c0d0241c4515030070302c40c25405100309100400c440c0c0001c10000030030760303008091403c14446d541d001e0b805210009002071080d0104d40c00030301140c2501d6100e0402c0c2068a40b500c2094800038841c04409004d00a00300002c1200c24a045150b00c0b1021020b26200020001c0d003601c4808484143e03031280a071101d1003441100411043c0181e48481e00e80c5001011400c28050000f003100d00f41d84100d01c0c80d4001c420001d40740c41100a20f1103103c0d8000e00a1800b40d41c03003d410b0320340c1c4031211400000814100459402800d0b400d82c21075080320440300c000d005900703d124240002c2e118a0440d40040d0602e101101e460000c2e013000f400b00c03520030740c2d240c403048101d0303105a032114040e94 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 254319046 1250 254317796 254317823
    0x114040606060e220207060e07150804050d03020315130f0e03090a03080a09030b0c07120504060509040b032e050a02040b1917070c05010515010203040e090106030f 72
    0x203020312500001d01083e052400100c0aa40c0c00946480c0040600c08071000c10108458482c0308190182c403003165002805124410b01036102944505884c060600c801e4000c0114003c501c1c415022035003c0e40e006009489029030541044000c0d62000b00441c02c0741080c084440c0d1692038240c82c240f801c40c26407200140032a240e0310900c00f40d034580840014036600611140b841c6564801c889011203138070925065840a0010099400e100e8603803015140030402c0003041400c40070780700185002480303401c220000840060003518107008501a12000410a00101645052940c0704061811004044440811040302100604441611441603603180c2a850b420300da040b90040c1e40d04980380c510705508040c20f08488800c02c1c041c003c9951300c0040d03088840440540210042400a0074019450703c00c1d103000c140c040c150300c202c1601100c00758038107000030b912080003941545812005030702451a141ca0300780000030b500000f8024160b00e56a844001000030444402c0e40d034824444c084d03006051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 254320296 1250 254319046 254319053
    0xf04122d0206060415050d060b04021b010c0f0801051201091506050f03010e03071716030302071a0910020d0b040c0905092a0c011407080a1d0726011404 67
    0x18000382c5041e001d5805c040c0034020700310898002c0d006851042d64454201100390804070b000e040803102c0300381c02510010b9801e503000744260700c98900b4400e4500a02091074100011503001d211000413030002054040180003d10340b607034241d40b11410700c2d400410800a151524100d1404000d10411036507641d031005c024605041c248010070300d0f0202d000704641c6e8821042030380c4034403a41400908411500024081e2018040c05a4501c0b1030980d01c0703060b0f40405417502500030350000f00c05581d03601c1c1940d54094a009003560661242c900a0042c182c0c03032941e085410046e41214070304103045a05e070404011282c0b10b6208200303c2c5d041a40e911881076151006200359428003900550400d1192100d801e5200c410360b2a11004058421141e503442e00035004643c014810f0520f680e80c00541d20091100485d800320384140101091030302002074442400c150141d41c990311866070042d800c140400c12810288082d00000511004c00b0301c5034864049040600b1100964141500a1544070900060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 254321546 1250 254320296 254320303
    0x4300905011713050a0c090605010914150f09090c0307090b03070905010c0201090510031d03070f060911030f0a05071203121a1503040213050f04122d02 67
    0xe000c203082240341004116804030240030700400b48803840307070140c1c0a1030400c6000c015501d4200d41040d000071010361a0400d00c406800e6510600740082c40720840441c3d00d0380c1081d5101c400301402003444101082c0c4113070b150307002d800c0720f2044416400240903810503504d070344550511500a00502030f540b0324080c90b010341040034540184484000a001700300d8107075013200e04582611000d0a205880c00c5407031004841c00c02c1c80c1c0d08040d401054060100e001150180c001d0b14140c4280f844802c80c910100000da503890003583d4025001c21881d800c0344000c03481030340c003000b1954064100425003440b9600802e1400c041118038901c00c0c0e06c01d514000601209009040140c80989040f0710028840e840c001c0040001007140035400e6551103414961042c440071840b140d03180a8412605500d2000034003038a60811541640601d00010240f03542411034400e43e4426607400a50444540b80c54070380052501d03105004009000f0104a803c05000710309514201c507595200b0011460b50300790350700908 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 254322796 1250 254321546 254321549
    0xd0f09051320072004020d0e01090302010b06130611011515020c0103110306060d060e16080c0406090b0c030409112508180105040308070b0609011706010e043009 71
    0x48440b024000540000c101c0e84504606540d402144903c01c0c800d000081d0003403051a4169201900d0240040c44801d419040440d81c6030194001b0440c01c17903250103014451040424034012561031107000d01400b8081d4080c0c80104010000001d100f105d501c80a020340c80d0f540c0c0014058214825100300450740c10046124044028a02400b00451000201209010140c840391088001003150080da0352640c0c00200140f4803d0082c10450512207040c8043c1c03c0c090325400c002600000020b00304698000450702110150707610414910f02e0081c010303140f5000380442d42e10303e0100300f05c0003034101400d000310f1800c03c401c08081c0fa503402c84a25016030241420710710300c079008600a03810f400b03e1103800a40740001654242e0307800010703a641c012a501d22503034100901d0f120010500300240010740148500c5090140d40c1e2406903604d41619480800e8403460500490307100c50b005104201104140d5030b0084d100d500841200d03038644040c610001440e13008007999210103010030350350f9036110101e0b00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 254324046 1250 254322796 254322851
    0x3030605210303061011011b1419050c03040b0d020405040b01030e0d08100f0803030f060a0308160611120f0109090804120f0503070321020c0d0f090513 67
    0x711064500c0001649074000109164440c00740b040c074588039035004da10340308034a11044000704111a84690018030751300c2c041445800150780c0190b5207203407004000c101c5c1d000034580c40c04460311030210641112241d020b0054048940400d020000e60416483c001e03000c5885a82005038850b41094140b000f00c1307141a8155041500b080307045851703004003248880e40116285400c8007207640300c0c40f881c42134208550010030154034103c40012841c070080301940c081d480c56440c1c1c4843ea04c501c000c1140c4800f45010141a03c2e81c108111101d240d480c40280e06414814440441c22640b8100c00f210740c1e401c09550f0090132089242000650308035010214050280c0584c2080004100d4903460f00c0f5010700d000e980d13140406e1100f0035040c000e0340c95441178000c2d44101160303500c8600e0300d401082c600b00102c0310802c03400510001001030b40c04e8000c1d45c0342070340c02000070406006c031114100c9002c00b05210308030a00c0a41200459151600e1b1810b0304164600c082c00310f4410110010528441501003020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 254325296 1250 254324046 254324089
    0x305120f0901030b040b030706020c03060106030b060301060f14181311160503071e060b0a0b0f03071e0c033c020118060c1206060e0d0c050a0303030605 67
    0x451103004040580e00c5208081c0380002c0c8490f20107011500a00540710b201d507262180c1d101c00200b480c1d0008400d00c400c24243c0c1901d8884c1da0b9640158240c9503a5078005d6445182400140070341c5100c2d41c1c0c0000307015942e1a0401845805449040c82644501000700c00d861460100c82c8950034000400344199a80400070000c50404541d601158001d4081010b100e0140000b98018803c2c1001903e2540d904500365282e0a00d8103c16000f40c90440b410480300300c3d0802c500b951441c80d000210004a4503404566131900f245040c1c40180c5500c0100707040d06100c5016010180300300040b00d00444c410030754071081c540c0c084609000d841c004800c01e2440e07004001c0c0f10a044443d03061510640712074141b100c0c0890203c103080040e40903111440e07402c07803010040c6d911007060100e26040320303101c015030780c8800f00301200000200c8240e41c80c9007c0c40e40880d403100d030a01c002d41440035041003285e01070010301410759190b200003461428142d1003640001c0e1103580500c028640103505c40020103034400d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 254326546 1250 254325296 254325307
    0x1208040e16022503050d050306030d03060803070605060d0f050102130b0f0a0305040302030d1e05130302210706061805010512060a111908090111040806040b041a10030512 75
    0x3d5480700411880c814000c040044504907604030500d81015590140c19500d002d00755240c000c6c181d4100b01c81081c424403528140d0000030b8080e100d0754098400d000701543c030b81812921284080d201c0a412180c01c48060003144001c1003c02000070382440c4594000350f500e02d214003002c1101d281c00e80040011950810012070085040c0c000c940020010b82404580340c1c2d04d13030a0507801e501954504040311030920000800b0000c108240400d501104038042090352073b41803240c040303900d11080003005603003d082c58810480261702c5011001141c00d20252606d51b6550303d031819540b083d800009402c085013030802c40c104043c0500b602508041c2e801540021052142e16070b2044082e01c41c0030300c65a540c50800c2c14512070303403c5601828030000da1000541072800020008001180c01908039481c0c03940c80d0b14440e400d20111000c4800410003401c150700c980c3c485004078007014104480c0c00c2c0e10074025a01e00c03881e40d290188961403c0d40d00046091945c01c00e1350402911a0350043e490208210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 254327796 1250 254326546 254326591
    0x50f091501030f0303021b010903080a1406041125120e10120b06120f0601110a031b0501090507140108010f09050709092f040f0e0408041208040e 64
    0x34524112a04940d280c900f040040c14158000e10481a4248003910744000c008201d2030150803108001d8403a035500c0c111941c98950000c11602000141c2501100c10800700e071541c0785c00e810009011744d094000c18a0200c0700c0c0c1031029058050300301c490f5030a1180004030144440c115100d45c20b0141410200002d18002d4002000c410b48007034220b05014100207140361000096100c12108100680307807582d9009413012140748610200d8000c3c18012001001840035403240d41c4016540d072603040102500c00035540c1c1691800c1d000036401410014982d00c1502082090295400c0c05000e1406059403a060103010b84020b42400807490501403a100104003c01180c90450b0480e40348000c00070b8176032600e141c100d03031a0301d8a03841018020b0a1072070300d520a5052031608010300d14030032200248100c814504007028041c9104d6010b81101c04002003010407480ca0401360721074440c490540c9069115011004194240c3c0001c2c1d0301604041014020007a030b10b00030b03640102c180751b48090030051940d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 254329046 1250 254327796 254327833
    0x60306150910050d060905012f0c011e0c0807020c03060a0908070b1503210d11072907030506030703140f0304080d022802150c030a03050f09 62
    0x50949004416800018640c00840c900b92000341000502d100d800c91000c0c2042c2001d4038403103109907015403a210b96a0b50012003101c4101c00d10f5400800744192506418110207175030441d5038001015500d43c8104100480010510400041c5c04840003640c03502b1100000c2c00035400420210070340d4400307084680c040d0f40c0001c0c81c65129540b5000422008424a4655841d00420400910440307400047c00b001107030900050900590a8003103606441e413409410240c1d400d40d0110f076210724020002504071180a42041414420307e0034035924000c00741c0c1e00e0f00845152158401d04e2030541e60692141c100d811071045810251901c0d003072105043c00c0001944846ca40e22000300654002d040d00342480609016040d00640144180c0340c8482d55600750b181ca03541a0441840140107050460ba44149510041d4012081000108000c00340c3d560a01c000744541062484614a061214001e4844104004c0980b10480c0d68040b4081c140000c420b00c041d90060000c602d180c010094003640d040307400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 254330296 1250 254329046 254329081
    0x3200c0c060f030f060d02032407090e150d0f03080403020d030e0c090402040e070806061003051603020307032d0f0501120f020f0910030b0907050901090207240f05060306 75
    0x3514665111174000480d4905500f500940500642044121114813061007080340b2007080202030700d130740d68030408a45414590103840b951317403900404241040260b00070011020005408019540e41c617440301d00d60400551000c43c00910035404000c02c060303040c4020f1225a60904051003404002d2600640b20711580e002640144020707000501550f40710703044004250946c40c1038400c29610341c80c40e5601c0c0c1c2c4003200c0d118003900034ad0709154190303407181c440c1c1803143d4802001010588202e42c0b080380a5407000c0c1c07030030003015105c0894894401840c5090410f40801c80c500120842041200c503040d07604a45d0845100341c42c2000404c00b1040f10541d214010741d001000070030321041c6200160340f20074601c440d6074000034200100071110860000c000300f902c0c001ca031048003581d01c2581484e0341d1151409041c1d08600c41c40010403071262960090004a8030910410b005000505000f68034018842d000c0001c1c01c4d155560a4140d030004c0c0b003543e4000d10190041e100d1450306000c40d140500f00c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 254331546 1250 254330296 254330311
    0x106030b1c02040b24091e1807020c0406150e030f030405060708070606080105040b0906011511011b08070e0d1106090316060503160f1202030703200c0c060f03 70
    0x11850303c0d4015981e020300d8000094002c00d044082c17402c00b1901c1580c250400d511b00c6000300801c4408451242040f022910002002407150412544500301c48910003c081c00150a5104401081510359140d02404002e0300c1c99000f0440f050b0140d6030300811031000742c813415000741c000003036004401700088112400d032170b01980d8080c0c0c0c42d070f558501190359216810026001c5440d01d400420b04220641206018500991080003a034841c00b42c940d44600c800c1c0705600006050701082000113001301c0390780116014450001410b1104421503107107407601c641c01a030006000724200f100a03038102501002195080d50a03a0402c115507484c5e480003c002220a0321035000801c1d016015681000b1180514101041c03051549641c3c0c81d01504940050b642407003441c0503401000c540034071600d880040b1811a0b520001c40b0300c03c85d51400001d50000c0c241703404050b1107255060794003c4003e850b80090300c0c10240b8954951141203400e040003028805140304102c201b0904031440d00d04001c1d00e810100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 254332796 1250 254331546 254331551
    0x42d0602130302040e2d030409050403030b030d0c0210020a0b01090908070f06020403110913030c020f0d05070807090203130312091205030f010f0602030d1d0303010e0106030b1c0204 80
    0x2081000c0d40d00c41c8203034030080d40320342041210b010500e00815913402440c1002c9803030045411455000e1b425a0261002c8442035105000030004141d00740c103c950064000c2c18000b401c100108017080c1450038200002c400310769017181000443c200074101d001c0c04036041c0301801d1080702c0c40c0d03540c548520061050b8000d4a40326003424091200d01c1040b07401d5260b1000d01d1001c603e41600c4c1810294000784020b070f44851047d001c03000700d4286581c001c0d00c10b1281c85a00e140c1c04e442640c00b9036003c11a1603042c0e070051a014071001c403903150048200c030b40d40e00800003031403c1c4c1c0c5006411450010903401001c15140140240305c0c6032292a24100282c83d49810207600750900300d0341407001003400c0030000d003204400c00a40300e003054004008500801001c05807c3c11607072a00d0418150b05880c0c410200140d0040080900a641a42c0b00c400b4042e4060500c40a003165041c086c0c1c9190002c0c3c000209402c08100100f08090300752180c0b400c0d007030b01a100201c0141094401352400a440803010b8040c94 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 254334046 1250 254332796 254332807
    0xb010e0d08160302070f06050913200f1c0605100c14031206120705010203040b07110a060305180d0f11010b0301060b090324041b090203040803042d0602 67
    0x15075041e2481c0c14190b141180c1902c4850400941d50060744c82000d5a543c034a44001c00e900384104202c0f10130610140c404280034a480318160020201b805141810134403a118010705100754030020050025545801c507102c941541c00480c940d01114584100e10781340400c01c01880e200e0b030344900612842814200c400100c241041c0d00d00300e0300c08281190601001075a072035045141c40f4010f00030034090b036928801ca10b0000c0d0a527075a0ba66405098096481070004000c5815020014810203108101e280180040d07840031840403112500304401094603041009050854007504021241e1081d000740138800f417696020f8280708498407884100007000c2c1d8902c401070400d40200003d20800f030020130440303540c4e01c185441c940103000c41c6440790280c02c1c020b4007400d08203949804c1e1a002000c80181640780d039030300c0300702001c2803280003142c402e141540005c000c1040c0c40558401c3c0c0c058903215551b46464a040c921156403d4007140400c20482036684404035961148200580d121000503600c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 254335296 1250 254334046 254334053
    0x510030902031c02060708010608042001020102070503030f012909010e0604081e010e0d08181504030903050114040b07030b0a0f08010f060501030615120f090f150b010e0d 75
    0x3c100d00c202e2458030725005100c005442c1d40000c40d01e1181e440c0b55605036081e62100c808560380001a0b4018040f000b0f00f4001d4600509500b283c07490380441400018030b00701c072599601e4255001121142200c80110004000d01c0c0c100000c02d035400f0742408601c60340780c110044e14040c10b00920524170b0400c1580c4d00c06111548038441260003401c007050488a010900f00f40794041400b20740d11641140d400c00002010b8504001140c6d03e007030542d030b1540e010300d40c1c0fa40d032012001d50346018442d07454810007050f6034108000d200401d008501960b200d049860541c2001d1b030940d002944e1001440140c001003002003000844400c1e00550207250105120911500040040034250407110b03103c040303808001038444c1c05522808079400c81e40d80620103030790707220015421100244a2000112010301a40e81d0441c40741c3e10850300300307050780c4000490702c044800c4d2000700c0349001c04c101c440710ba000c500d480600c084200c0c00f08a1001618040c007140c10f0440c0001d00c101c091601c9980101a01e00c0c102040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 254336546 1250 254335296 254335303
    0x30703080c010b0604181e0905031801030b0a060513150507050f0a02010e121e01020d230610030e100209090f010501140a050c0a0506040209150307030305090102031c1a0901051003090203 82
    0x78100184040c0302d80709050905030782b01d504c06032403288009500c4003c45041e50182c003030108003070720060160388210f1901c0011f540f6980320442c04d5000800c20380d008200210200710060103021599200b54a5024a1508628006813880b460310558002c0c1c0315100141ea01103490111440180c0e41c42c08680b108aa02a15140600608001401d0600f1540c0682c0300c0540c01b500200200310010702440380b202003c01d00e4407040d1a16121a045280001401404d00c025004080c01c0240780002d085482903201600b092032007000c68601a07000282c1610381e00e400042c00da00081329903012801549001d0000e0020403200181c1041d08501080042e9414001c3c07080e245040e45410995003004c91900e012512080e08403812441900803002240e4009044900c6c16003509016000305009425918152071903000010806e04500c010464406a10b040c540b1038881f00c0041c00011400c0d000880d041903c0201c1c0300140d030300940c5400010020b0b0358410b041c00071038061ba418001036860207030010908 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 254337796 1250 254336546 254336591
    0x3060a150911130308180a031a100801050f040210030b030706030e0c030304181503050a02240705100c0302090f0d0c0b0c03040f0603020307020312070e030703080c010b060418 77
    0x501c0b803d41400418012104010030044006a0100341c15081d05810850b041105d400041c0c49035080010008c2c002c0c4580c2402d0f50082801381d4242c40e8035030340390011425030300100c45425100c43d1400c140801c5081998600d50000c0080c01d06018541d544008640e0b40c103d075125103020580c542c100394840380e00521a0000305240a415641e41d283c80d2414002d18104850107052102e2a08000c40031220a20800d0410351354072402428005800340c003040355644080c2e220755000ea54160b1003100034144000107040f00c0d0300c90400342c91b207140217907412070407102c0000920f814180100505165a07071041c0540605d00741c00c0b10303000140485c0d1708011101c1103880d004007812034400140051400d00000c01b4008541c4041049500c0b83e459400880903400250707400000f5030720502c400c1460408400c0496440002c1e40f0380001c00140c503c0011713142400542c000d403180d404c002001c901401080c0200f2917841c1c03003030f5000c600e00f40c6000715865001300c100030840e4406542e8408030482c514908561103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 254339046 1250 254337796 254337817
    0x9050c1909060f1505090d11031504200109080d05070819091a070209060f03010e100209030c060406050a1119030302090301200306010e040906060e0603060a150911 72
    0x201c0692910300c032281e008018090001400b85411145a02905c142c0490b0b0340c18030094100100301101e9a80e8400c2e1122010480360701d80641300b900382e1a0248000c41d24410307406140700e0000035000902d000c0d04200103000b0036040050218051207012800540010202181c1c80e02035a104000e00704441140a01702a000c4d4092600e0403491156500560b80c4d41551190004214108940c03228075145106000d00203404c030902500190b0385113450508101c80304400b400114a25400381c1805080241e00000202d03180c0c1c1c0410083d42c3d905040040d402102001c3d551107203094104400907015000b1700c11440304106c2c80c452003a040d40d400740501c0300c2408201140c040ea4200034980030380a500107030100c0740603618245e81d0039501401003603d403007042c1c245141c041c95070302c80c030004461031014440f50b0340c0c109440d007441e0070000f001d034403603c401402c6400611044e8103282c4101828018050640c0e01c03402d0410f40003041d1400d002c0045012240303060b000243c98610711000100c0c0d40201c41a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 254340296 1250 254339046 254339051
    0x905040509030310090e0d030b06070f0c090b03060606300106030614030d090303110309090f07020111270114220501030e03030411010302090607050a03030b010309050c1909 76
    0xc0032841e000070145010391401c48a01503c00c0d00e80d14080100c03480610410303025441015114a940d000360b100c4400890043c1210b8a86906900c480d404403540400488418040c0b4204005034501c620801e660b51800f200606114280040041c483e405000d90002c082902e4500c80c11403802d40300300b820041c4c031a10034125810b46e51100040c004040d035114002e07140e18039601d000300d0303450b001c40c04003200c0c040d907240d002e2458107545040b2000340d420801c00c0800c0c402000010300f25900c5c210428403903440c024806003640392040000b8255580d881c0e805c00100414091840101d544410400c0300191042c1301d56094042540100e03000c0c10350f2400700306414000101b0704030203400058070551620216440b604520340d120011001c41d022101131015540050021030001000b5071030103000400149405800d2a52034000503110750321009040f6a1035116402010800d600340c0200a41241c0c242000c0040c50f420b40c803040c2d1550700c00c031130700385c41170340400c007403043d4124140803403030240c80c0c2d16008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 254341546 1250 254340296 254340301
    0xa09020d031805040c122403111206040b1501030209040c03091106030c071b080708060109060905010e04110114030114010e0a030302030421020d20030a030509010f09050405 76
    0x504031480101c5140802d4010690110305400c0034010344c0001d05460703842c10a480c4110000f1001024142504e0401c100700d06000116100c19412607000f460240d05103101156441c01004a15006001500d030640c001c03404003c0410302a400a0354050000c08003900403081800c0120002d103d08804241e02ca8a060756041101c1e80c11f500038500248611902201c000d50b05040000c10301041b59030040b100d01c00c03c8a5000203800c240e0305141d01a40610021105844021841c00c10540340c0052100350701500040080c040b090003079800810484808201e154103040300e8400c80036000340040d0423800070050500559104030004481c40f016a06c44079200d50715160300c43c003102c1b100c0c62582d0014145506521071fa1910007a003804403503240c0c0096140600c1d0070155045940318000940384000c2143c0d007503015031a140f0464151074460742c011302003000c100480c16103901b50640458044c2d0310801f1100d0000350000121012070100342071003900c9a0100b002111a048a90043c41c1c000c1e09041c01d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 254342796 1250 254341546 254341553
    0x3080c03090a0909110111060a09020418060504120c11040b1801090c1d0f0418050a05010227010c110406031e0203010b060717030415140108330a09020d 67
    0x9140580c45044d1940d403003a030344801110b600d14080e02d07c86103600030401080510007030354400624540b024001140030001d80310090003000a03000300351001342e01d4400b00004c0124807070051002175024207101c1740340c1d006511401daa048019400900459460f00e40d00c05a60b180c44034103410320b44141c644501507850344c0307035034001d00a45540080440c061548011080045680240c400280030b01015180d032521020030019000d544841c2c86008034072081c51020400074000e461069000710300245c1e40341d0941c01c0d211403084240b80746200c2542e03280d480d88840c0ea4440b94039004a6001070450500b81403a200180c01050291300042a101603034050031b0702e1b54103070700d8481d00c1c49000300c00030480b881408040c040184a00e040060540c4030f280f0403001e50000c207034051074200c0e000300040030a440880100d20b007200e0407034007a0000444c000004004e1440f04100d40e54844401c5404481040700014481c0115185a42034034015590314000a015460607484900c64a800401c1d85078810811304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 254344046 1250 254342796 254342801
    0x203040c05100306060e03010204181a0607030206060906090103020303030f07030b0d05070f1a040306020711120604140d0f08060d02060703091701140606030901151404050a060b0403080c03090a09 86
    0xc03a00002c509601e80c1800c152406109903006c84a0700c8002d09036200351301d180f440091200cc9626551b48841c00c440b11016107861015080c8248650018480e40c2004401c03c241c8480007060b4512500c025030050006031000320551350000140e08100502c0e448010051340a0840c024a070781d0021400c0c600303002400000106c0383c04881c0740104d0740410540315500442140c00c4a10040b00c0210304000810000c0c001d94000d110749d44c000d1500717030411010301000a000200313003201041d05501007024002400b010b038a094598115040040c04010b541703c07406015451002d440b1740c02e0010045c00544185c40e02c41030420f0507a40208a580e0352003132840c010f000142503002d03a00140c41001990300c1d9007071051161600c0e40341141d030a45000d684030803c20003070340d1009005880d155203c00304204001c4800c411040a440d062500100c0f07840b08a00340300413650000e101c170501c682000320412100b002e034002c64040c0c0790402d0f83c0555a240b2070f15654594403503201013581242002c48005040217069 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 254345296 1250 254344046 254344049
    0x1e05071505040306050604060b040524031501020105070e01020607030b0d120206010806180a02040c030e07090506130b090c03070203130b09040e0c01080f09010b04050a0221070903060203040c05100306 88
    0x1943c04102d15211b640c244011281c49000c0e4a1180c48104014400c510303280c0c004405192080d0500302510b40e0600884181c1c0d0000d5400701140d48440303010f40007540c1c080c02007075408a80752401200301d154841c0001d50b503180143c81c400c01c0c151750700700f850030302d44030341110f200d81e950049141810201c03120f07002507641c6800d204020241c016000440c0c1c04c00d4082403c0ca108044c0300d0000c041082079070f000c1000414070174a060003416507a6280314020305017848808010502618000350030300e89881880080000e406640d502136260058103006561111803803070b000504442620388a6640c000706030301c1d502c102170012000b900c0c49100020040c0e81040100103004050b00c00b0701c02030542e05c40640d91281c4d0b0358002800710703100000107240c040a03984510b071300c14004800407a5100520007c50b049030020750b0016001a00054030b4003054403200c24000751000e1070314400c0325526041b01c00070000001030000509680e000030119080c040c0800003940580002003c0c0c11001858040180081110b07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 254346546 1250 254345296 254345303
    0x100602010506060a090605030a1d010501080d110316020409050618120a1b0206130618051008010b0c0c1e0a08030a0f0309170a1115041e050715050403 66
    0x2071900040e618142041a5011010a51610040d403410f040082d80c0c1a04020b15041e000b0b41d031036442607004001c09481242c00308800700002440d50520340c0c601e06100003402c142051114841c54183d04c658000101c0304880d803c8a80803900003000d00c0000c02400b42801c02a0031841440148550a000c00b400d02070f089240004a901ca9594080f0b000b01e04e0080220390004200c0d09480c00218100c0e2214a4000a1004080500d024120402424018615000300001a011942e82131000c01c880d402d940250404581880030319028060013400710b2414000c03a908000040b500504080c0708010092460b44000c29089a1021910303e6444445400b40810b100d1041380000040f1090040100d0302140020354947c0744503600725400350f002d440001c0040781d0450004002850b41d21007913024041c0600300e59210b40341000c00200c00d41c500052220301e030b10340d071003620240000170307800f802d1985141c062100b80310f05541e0541041400c000796940850b10809405410320922640319009000382ca21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 254347796 1250 254346546 254346551
    0x32303011508150105030105040c09050306010b0d0605030a05120d0b0604060806030d0e01140a090b041511060c07150b130e15060d0b180d0f12050402090402040c0201090203030310060201 82
    0x540c48038029002da40c83c0642070203c0c008100522184c1081e40156180c0030046c10118903150b039840119281a4003680005119030303020a500000d080c0c603005403801440201c008203440d41d004d0700c0c0c060700c561090f412100607443c0001d0398001d480c156040409040170082a09884a07075500e00078012500c110b541c0d0303119000d051103001d00d040c000d101e4030311384c80e0381a51340b24003100b00000c001d00c50341d1080014606110000c1000215040c8480042c8041d101c040f070001c20301c6101c250040c03d143d0b10036450608641206003000544c07040e60054584003a00804c1c0019441c00900c201c000400a0114864020840d0b8448184c2c60b038003500304400c046040c3c003c0711040d490380001540385c4801a11110380c4944d1000745040800c920b1070310b050f0801c41000300ca41c8030001245440b440e0190591000c40419605040c0080064111440007484901d10000b8013480c90290300023464a0401003000b84034599508841040c9403007540308840055000e4201c03a600e05004a20345400f075200c1c41900c00660 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 254349046 1250 254347796 254347801
    0x807030c1409091203060d051014070c030f03090c0e0a0603030806060a021b06042301090906050108040f1401020d0203040b06040b0d11041107080c01050f1003032303011508 76
    0xa0060b5040e2043c4011006030204055000210030694030150035168407095661503440400e000b4040500f881076651400206441a0300c03607020303101002002d0b0f40511020b40b12400c00309810846030f044000d460f00d0001a0221286807e000082d00c0b44c0107c0169604041040440750b082d03841101901c0c06600c40054640d640c03010491244103440d008030041c2c0280161b5110803c0c892510300ba07000000b480d140c1403e88074248000405d454161122a102084d0040c140c5560171a120354090901d0b000c2c2800441d091500107002c101c0b015100a04030003032410503109110400c0c0700c000240800000942d03450001d828403002a401c182d5042ea58200110b0105000b841e2a100381140200e01410311911080551119001400100640d982144d03d80341000c001400a03801040018454682582c4605c1d000c0b00f4142185d1004001080b181000c1e07042c800384110030210301003142d03410724080050640b2081450308210411480004500b004000407440341800114a00340003440e07607480200b603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 254350296 1250 254349046 254349049
    0x131a07020f0c031911270a0203010e040305070c030803091609150317090312030a0c0309150e07090203130302060705040501090e09031b01020c0f0303010312030c02070807030c14 78
    0x12200b2981d9283d0507800460300161420001140d040c0036400784059103035009400c8003044403481241c40034a111800c0c0c03041ea4015a190b8004141c101c1000e01c81103056604218450071200c0c00a0006010b004000c9405030401003000e1344100a0350b40a80c02945130b083c40107210365910700c407103021b14040b41440e2002c00c0840440c89000c0520f40ca03040c0c1100800d2035515030200b2030581c11044c1d8026001008040003d0301d04100580c0c002d001880440c1ea203140040c003a008403074003802100c0403d400d00a4030800320384a03900300c100000203100700103200b92a1351041441c0c0b0b00076078803880d41c650010041060809104044d00072a41c040e400351030260341c50740b40c00c449600c100c3c0605800b00b280c4110600421500c0c40e400c0754428915004c83e0320740110700c400c02260420921b0080c240b03a4002a00c00000381c000c1c040c1140e40c04039840191b0079941165104045a000e1201c0a820545d0700c00060300f09920802c8220010004442a1100180c80e07061070054141c0500890502c903d6403442d900c0726 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 254351546 1250 254350296 254350303
    0xc2a0d022a03120406080a0509010506150a0e0901030803010611070b040b1c05150307170c040f0902121005060105041202010c0204020d020409090b09030a0203070b131a07020f 77
    0x50400d0380e20038107040001c0105031084581909021901889107000d1468540005001440a041503845e102c1c03142c540b610304132090b40d90007409926140d0600080c03111540300c140c3c825a802c40035010707a40d190030724000111030501030030100f994001a0a000003040c4a100da0046051341c1036035440b1040c2c1296140c1c4141d489105100d03000d0328690410040254020703c07400380c50741441560042016000c4a0030346403c0da0000e0710300c02e90031401c000750384001d403504002c068020846043c85c56100c0504170910f549406498040500544d2034001c46d80d01404254401035620b43e0040c1082d60210f40f44681c190b071103086040070b0044614000100d152f0b58040c10640d021652a401c48404031801d40c0d00468002090503400c9802a80a10190782d901d941c0e4000340c0081c0c0001c410001342201f40d170800300e40640011b00482c050b03400410a80c00e031a58080116000e040c0c104020890b1903d940c0c00d0f01c41854100400680390b580c0070f20304850702041410703209000319225400c4485462280802944 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 254352796 1250 254351546 254351563
    0x2030708010e0c040306110d0b01110c06090604030f050604051027061b0e0102060c07081b0a0501020304031106090706081614070501200408030403020402030c2a0d02 73
    0x840c95090040000800000c1c190703501000005100d410709a5944e5a102910030030900408454000700350034a082104d071046801d441000d103440301501859020b10781c4c035111490310300390103940300084481f22606c900003110015540b00002d11150855403d0681e1580f1042d6400c0307507079020381003001880f000c46000700300a81e8006051100c0e080301405e0118120798009a0450749942c440c0080010107840340d80c001007480c00c503255a0061101d2030002810510b004000d005200810310690022440401c251012114400200001d00c00c0c441c001d03528103200e402006141d0b41c00041080205688241d0800b00445c4c808101e402640701c3d9180141c075101c15005d40300000e40d503840010304480c0556841044d04810342452080140b52031183c15003a88161700581d01c0d030391203110710b0382c0c003404450350366000040c4031050741c4c10305050600302d0b5224401e5200203445a41c010000c540009400d0080340c1202d803010020440780d0320300e950395800450702400741040394001c0f81440c0401c140040b139501c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 254354046 1250 254352796 254352811
    0xc0305060a29030d0e0102011416021e0c060703051303060b0f060a021002130f0e0106020d1806030b0f090406060905220f0809061201050f0d0506060108061507030804060f0203 77
    0x5651000f1003000c40d003224030b01317818a046640358480440b5031854075214901402c056140444030071a00a03000e40f802000c01c800071384880919007600d2803540d000c600000030351801c44020381d0b5214141811115030250b0740c0800420500e544001080005c0c41d44001d40c1140d0070b4802080703130082c4004000680c010001d5460140e0840c42c21803510600590052401100415805c0340da280c55240202c0c0680080d00032165034960300b0f0060001c0d0390100010014482180303031030060100c9507820503240c9401881006c00b41916245e60020329640e0000c11004404040c100c3c0301140360900b025000707400c0501c2111b0f00c151905000c654942810081417181030030303424051803c481c05645a081920b103414054403090414040c0042c59900d0000603e450440808100c2481d41403400308a0b036076214840e5244500d040000c6000050720100340700f54082000d0814030b007141c0d1b41c0808200450051601c00c1d04101d00083c02c0010540c00c503100e50300803801040c0400041a01075900d404030f200988000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 254355296 1250 254354046 254354053
    0x20301081501050d020909011b020309030105130f0f05100203070c060509010b0609091504020c0a1217071d190603062c0c121003021003050106090504090c0305060a2903 74
    0x4d0150500a4109800c180a0000012502c110f50011524903d4001c600e40068000180c81d0217980703000d0103100e8024804c1048030700c2280b0986d5403807041c403481010080000d04003440358014042e0a000c000e411000c801001d66807407400e0b0360000c141d1a50039070100c41e05403610001c076514074030501c00d0b0940c020002c0c1035280b905000408000461500034980700c10078100050301901d640740c50015004284800009040c168418603243c3e00a120b2041e901080025001c20a900f0800f00c81607550000c000d400c00b1190040341d0903841d101e0003c258a12500712117188ca40040040c4641c03019011503440d50340400480b44c0310008110344600e0342c030089040c0c010031701d9040d9005042c103051a411507440340c00b152901c41e25099a01070044110f030354142c0030b522481d0070019400c003030080020000711454104015810048060f1000c1d04c01e0140e0342c000e9a032102c98404000c24040325501a6030404d048801074a844e10144018140c0b000c0c03403041604414080c1d002d1802400107103000280000d018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 254356546 1250 254355296 254355319
    0x8120c04052d12010213141e01120207030309050f0304141f0503060a0909380f0603190507090c020703050c06160f05060f06030708070b03070c0c060302030108150105 73
    0x100120005003d1561032195820440b8100056404901034020580c500711020401080800c1040410303142c044501c0d4141e8101081050780c0c0d001c02c401c1240c4d40000c40c01600ca4030642404c40040611038801410b9200b14600580038020010140003202e0038030342700c4c908941d1144148a0942d070710060080c461050b145145180c54003d02c0910780c0000040e100b102a0703a42c034903007a0140c0e41a40700603110103401d010f812240c07044440380040ca9900c89541154a07205420b9079010980008000440c2c41c0d81c050041511580c041c0101d5403108a80700d00b21151442a08005032074251620800c0717070907807900d030300140102d0012030440e040f2500000503040806c2c41c1000d21880794010500c140034140c0c4901c80400003408607195004c15400780c001024285401d5007603116181015003554803d9005a80422540c400000c003001565030015549450343c46010003900da040007400001d01600c00f04102048040d0b15a0103981214880343c01c607226040102160220780c0340030302620341c010030320854 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 254357796 1250 254356546 254356549
    0x105040506100f08120a02030f0406050406030609050f0f15040c030608010606020c060d0e0703060f090c05060319020f3a110904020306010909020a031d030c03040e0408120c04052d 79
    0x5032200746d40c03600569141c49510a1242d19540c00741d0051300c040355000c0f03014000c0d6945403141d04007030319200c40c3c104183e0804580a442000c0700030600000c0400031000038944154081e21010481d60140043c06014240e96000e03000d0080d03805940b0b0290700e840e20001c3c8a92000480c4000e4000103081c07c0d15019803055410050415100818100c2c40382d40740c0040000e0302072084d41e0951000d0000000c0c00c2602e45400c20a0340390b5a0710080c0300d05000d109100e1080c0d07420481c8048500781d0350006a0310140320704110964080d40407103031072452101c00c00a03803040c80c0071125010b1520080044da81460522501008c48a04403001500c0d90801c0c0551141c03401d0682c015508500141854418255500ea40303006a034000aa81000280c480d880e42c600c8209013080c41c09000546405541840032003101107a403402144610298040c0d80804103091141c03220485000da81300c1c10740000c451400d01800001035209101c0d80d4018a8102d080100403510401c07040048c0d01d03504a05c85031620942d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 254359046 1250 254357796 254357833
    0xd030c020108180a0308041509050c060a020c0a1512050702060103030e180106020d020d0203040e060607151a12030306090f181501060216030312110c0105040506100f08 74
    0x10409415030100400750050840c040080e04d012601c2941c07098450325240c43c0040488c010154502107140c10720801c00e0000b4000b041e2080303003140660340070303456600c044d80407842d003c500300b00181c001c2080c9101240e000303640025162004800d8503020454402144940e0844104030b13422001a0010740050000078899681281340040043c0108400075841485d02141c0c8001e91140707015a001140729103402c0d405103e2050030030111300185081c50310f000c8032007010700e00c0200a40d00c204000a210030801c5003008540c626481e0f0000c0c10040711050650210001d038512602e144100308040300100005400070481e84241000b61460040e07888100003540b0500c000303010486480c41c02038048250541c00c0044907450080418581c0070355240c004064104402c503c0c160303440d15244c03035050000c0380c3c00c10010402c02e0b034075203c0003c1d011280c4a519055001c1e0310b030002076075400d207014801071000024020b4050b0809503680388070b15a44003640d140b03803040c0c2e20600d5607a42000112210442812 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 254360296 1250 254359046 254359051
    0x12041103121303061e0e010605120f0703080d020f0d0b0901050d0f02010c030224060a080106290403140c0f0406051507061410090507020d0e22060906080c0d030c020108 74
    0x111742c60200404078409100aa80e0038240444c40c036907444008210724507000e000385070784494110291041610f1944407680350034050002030681000081d19060740310543d411180e4082200907415201c100e040480c0d40074090194101c7d101c0c00000c0000701d89864402250790b1010b5102e0240402e0490300e074015100c80380c1401094040d4001e4030f080003214942009441741c1c0c41000d11005480b0b00e4103030100229403445421000380360785815010300080001c0241800e8030000d4506851089017401881c21881c4107607003000744950521401da000c5034400180c1c01558a108a820020481000d402e01003210618030400358071904250b8940482c66410b4014421580240c82c0030810000302041d1501030130050350a003000300c1e19094200044c40052290942100151000c3c2c51a601d400e80001c011075096040d01d031003107010682003c2042c1420380c200144508490051003001d98400b2428001d007014890b82c145809256a461202c0c03401c40b13070500c40903608d82c03140c16203409540c0044420f02c400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 254361546 1250 254360296 254360321
    0x801060e0108090a0b270c0a12050c030102040e0a0e1501060c02010e040203150108090a02090402060307120e011e0b03030a0e0d080301260a05100e031204110312130306 74
    0x6107102c1d02e0220701d40848042c410b030303070703102240f0400440306c45c03401840788000c021421140c01400219100d03513542d0340302e802164230040d0402020312580c1007560030a0f8000b403407240d00d588002070020303126000480644c892700c1d0200041200c0d09a0925260b2121010802c882d441025040140400c5008401e8445c1c25070040c0b400030380c01000c42c40400c049900c01c0d2085a054551800301032700560340200461760000040e4080c5c01000503650204914940161000784076280103c001360810384203462492040c40c5c520402d012200000711407500030120a143c1d28000c0c0d420183d60740345841c07180210340100b200900154980b40c144d40089402807071075008030b83c0c401c2c50000b2a0380400e400501541c0039141c000700d85466012181e01e006554600503c00581c0c17904080c0c240d40100700d02250500f925541400b020801039200000e80c0c1c15882068038038240480d00000340002e1181424136a43c039583c0503802c50b44204200043c1c030b040d42c06074406100300c000742031300c00b400000e0700c1d40c001c00c0c100c000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 254362796 1250 254361546 254361553
    0x50703060e0a05070321180302040203151c0c050a03081204060608030403030203031009062103090503010903050c120f030c2107050d0b060f161b080d03050105010801060e010809 78
    0x282c5540300780c10442182e0064444001e0040061031041200d20b4400d840606814000715480041da50101014000d12020b4480d90b408000109602d0308148001081e0000070300c05a401801e801f1a01a824035082d0159000402d060011400d0f0401c01d403948150381d0000c031144d09180c103070300003481a814020000c4a00640711440018a07400410140002e07500c02d80207035440c2c0c03610440c0704511a1840d03004035001801c20704100480c0d5030641302e542c034003c00c20b50640b80004141c20251041070465000c103405601e01150b4100341503214002c1c080100c910b40944910b40d4038201c6080c041c2c0101847c0b031b91007003010030210781072100c0e0000802120320214010310b910a01404a0b0300b18400856035000403480020f0b507105014514801d011f112181190141d003030800c40c011082050084c5600c2030100c0395004254420700c50350010795081d0601d612128144a522450910f0700d40381541c0119002c40d00b480000b04842d80545822410b0b501c290390740142c107100d5131004480c00c2101402a51540c003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 254364046 1250 254362796 254362813
    0x5060105120921040603110f090409030320070308150a05010f111e010b0411030703090510020406020a02010f02150601050a051207110c0a0b07081309050901050f060607050703060e 79
    0x2ca01c44141d00f51408201c1d02e562030300c1c540000542501e140703146100b05100f0802c00d03030400ca44003405441402200365400960b0303913414602a4000c184402c07078001251404103c20840340c0e05400140f995511036640c40700360b1707110700308901030703030303040b4540c856480710844e803091099500c52034210050038198034280c0840954034803991b0a018800d80888607440700b1210f000316100c42401003101c51081582d04014142038103202c010280401340c900010582c07520480018000c040051840e000e00080d000c543d81c0c1d59030035010707681c1c10120100301e001c9030040750020110f0f400030401019004001103490200e40c3c8680046840d80c0c07040c201c810034000140412081945030141161150b00c154807242060307100e542155140064140710301e4402c1c2c00c10701082c0507004c002c2c01034a0409038048405615090810b04800c040041c0390824080103247c10100840c080e815040349014190078100307035085032128400d100f1544503030800035101d584503060400000d41940c1c800d00c080d202c020b09807020003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 254365296 1250 254364046 254364073
    0x4051305160f02030d091208091f1505040e0307020a0e040c03020f011116030606091107060b010e031b0901050a080d0e01021f020d0605100c0609050a0209010806070909050601051209 80
    0x110043c100c1940c81c101f5800303941601c079400070070b090f820043c282e00510320100d050190040354841909100c0c11940c42d09000c81d42d0600c8249240060600200140403c100070300151b543c070340009109074442c0302c0f0a8000141102c1c107110907809540c22954101c1c02e00d0440c4c00384600b030749200e904141003002c1c10014081d594014091540c014071503c4685100302e1540c1403c00a60300b480e00030865051400400b81611500d2100700c2d080e883d071002000c1161b0f008180103907aa10380d11056107406004000c419201c00203501c25400e45082d086402000fa41d0f01ca400740f042007044c60040341a203a1000444100c41c0e8058202840b00b91014411558041e030840300003802c0d0020006440501900414050152661801035001425043d42c030110340131441e150044c0b009481c400c0280c0502e50340c50301a8248a0309200c000310a60b00980030081550b9214000c40d0785040c21608100061140140401c1d00030103401041d0184c0c4e8142d4501c0d04080e220f42e100101d02e4805000780005108112044150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 254366546 1250 254365296 254365301
    0x7080403060c0c1209080a11040603080c06090f0106180f06030203030d0b042912160605041701050103030e0f03010b040905030a080c03040c18021c0204051305160f02030d 75
    0x480b1800d81d1410355448032403901c81e41c0c040b6080251800d11030385000074801c0010014008540c55004140c00981500c0e80b408900100400d40000d440790400003000c600c0c244000a400e401411010304840c038100c003c07101c07203080b101e142c0940d00900700303403032030031050824550001480c40e800113400140380c60b42c0780e00292560384045207882956071159040355407880c151245420440c1c080c180c02d02041003500f05255014503501e0014030545041010500302c0701c00b0815141416400000c00f0001034440e81f01604607000351140c2c414003807030541e1195000d10180140340c12a54561611654400f0100800c640546500203180c1c0541d40d079541804540c1e114043c1c82003044c0a0405103549d048081401840e6110040c0f801800b014100180070002d03101e403801c1c100304c46144a850074010104902c45002c1d22a058080004c3e001c80f080019a0260590087c07045400803142c84807614000901941504d4045400c00300e66000302c000131a10500440001326803031250710540345096200c002503403c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 254367796 1250 254366546 254366561
    0x1005101a120f060a0e060a15021c0e151303021002030904050a1401050904120507020d120f030b03070b07080c031c02070501140c0a031e0f0b091b0706020708040306 72
    0x640e040500b05000035400d104040b0720160640b00d00c2d00c134051611001040025649215054888201c040b80300d01092082c000a260f00c15002042c88408030405801490301f41c1c0c20354001c0c4507008400558403001342e9030007200d03c031640c2e500c41c05e0360052440d02001589041c107212142135000400c1078207400d0340c480c4640c620030b01007088002407100e00c40895200e6008141c0041c2d014040034020b00c0041000034985441c012000e24043d070384c41250f80f012a8102d0f4080d000100740010781c4050b2148940c004404081281c0325a4040010440c41810950b03508124400e0500d0204100324400124280200038a0151030700c2080302d150800d00c21a01c80b28805810194800303507400b140c100104402801200118201c0749000c03211424448554105807140541000030f0640d40e407160707408a4814441c114a600e00395004011908050001802070210940b000c1e00c039020300c0300020f81d2411462100c4070480e4230903040a00300038103550f400f402580700f0002916038090070b02002000982a004001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 254369046 1250 254367796 254367811
    0x30304020301050a2f2a10021e030406020f0c0d12050115050d02040e0c12060d021507022e021c0804140c1e010e0103060806060d06110d09051005101a12 67
    0x40640761014903607814584000900b020140c010440c2c0e80c9c405000c81044030740a4040c61216580f81c94a107040002841b86940080c1c007a140411055a1854081950003010b01d00340c5404030030109440001c821513000740100d4400d0044200c800001c02e1040e8080c1c221007503003040c010b141c1500c0320442485840d04441310895582c00040c111140d00c4402e00c031a80141064414030b000e200c3c15400030b88016a107441010460030041561825552900c030315503256075200d000500007107400ca210480303828400d41d04001520440d992422030300400101182843c0040e9102c0030035442d680d0381c98055002c000c22840d1644168001e080c01c6a40f80f1110b0000c0394009a81e034548080c508001504090385503c00381d052518001041100390004107400c0d5220800700c80c0040b501c0c003d890004018a80c1c0c081903824214003040682d4100b141ea4820040c80340914200c2d0130044201d030800c0180e40c011201043d003d00301000030403441d20b801d0240d1404000000c4040d0510f455600c1c038a1504104540c0d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 254370296 1250 254369046 254369107
    0x206040819021203040e0c0903100f060807060c05032d271210051012050318190608070c060f14070e031203040309050d05030304020301050a2f 63
    0x1101103203400421007030b80040c114040e5081c43d180c0606e41000110040501c0a50702e400582034032140c0c0c0c14803101403d1000e00b4000c10810120200440040c00503025003060752080344c1022402c0c0b40502650071030194050000c5190a2442d0748421110008684821030300c1015801c040b01521003001500000b6008c0341c202003050506080c1482000c0000446070081944040504030803501080b1002c51401c0300c00007141684400b0000d4480c0046a8080071410b00d810fa40c0004022000c00144032001481032001c0c0e280d15184100031000000c2440c1d50404c030030360036040150901603080d16901503268106425009151f40f038540a03078050100280c03900340d5401c10070b221888050101ca42014061921805a8840301c02080d0780d00600040403c48400200000d030030184214510030182034054200004d02e80185000d90307994100303540c201d00c01d50a1400042c0c5c03400c40c0380301d1000c14a0b03070101c015a49807030f070704076051f8010103902858000000c2004030700010a4400e0400c5408040401352 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 254371546 1250 254370296 254370343
    0xd050109060c0e03060703360605060f012a0f0311010518070e1f060c05010501060e10030b0d02040e0c1203030c03061302220608090a05060a0902060408 67
    0x704030707001510441c06104001e901c000260700d00042c3e207503016100e402c0000b02c10b071403070007500555444518000901c0d04403600306d88a10503c8072502c0d480300c0c0304003002d10140d00e8200821482c094900a02d40c0010700564107030456942420040103040042c00d01000c900c1960740ba10301074918001c1d400e4000c107000e0740c001c144000b424810550b0021140400018420348004c10541351031240c407e20055011013004904018201400b8051404180a14080061303466102030070f15101c66030180c1c0c0c3c40d440e110000820714041d1426103403040e00200240c00c40800e0640c190028215a00721640003000841c9000060300c840c0700d101e203180c070780348010040c8a81708001c200d642010000c40380c1043d00180203020b104503418065942018044915100d00e0300146820f900038025119408510045c04c040e0406502c1c088111b001520030b43d58031000c503981d0700c00d9000c0e81d07407101800003011a4403c2c4009918244940d00004060740700a003040e01d842c0e510b40445162043c0301c00000700c41d1850303605 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 254372796 1250 254371546 254371553
    0x2030d05120901050402090c072d03020d0e0312070516140f0d120e0d06020310060e0d020a0501120b150415090602071a070501052503020c06011e050d050109 69
    0x9801d40d00c040818001c3c002454507501084840b00e0242c1080500c1c00086280400c2040c40808501100300c0860300014005050580b500600c0b41c1581c01c4c0c000d07014088000452521996406001010140040c4400b032003038180300c090b96004c888107850600484200a03c9004d021902c0c10040c0070030501400900c0b8614100130649101128280c800c801342c1c0700c00d400148030f5041c0d04a81c0002c03410150701c003910501c0880c542013225080100708500c00410400004161024403040d1150340d90380e1242c01d413003102440405642e002001c0e6200000c0601081a50312940520130001d0040d1404030354040b0f4000800c860750901130a01c0311400c00403c013403101b1145030702d14121075411440c200d0040c07860440080d494841d01c0c010048040c0341c0003441c08100130007108450000d44d001000b01300528044504290304402c0800420481e04810380c0087c0141c0320b80203880743c082914011303080d1079191003030581000d01903c0440c0741d04407198400140c1c81d0f032412010b0101c28064030001c12800030301c0c503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 254374046 1250 254372796 254372827
    0x81603030e01050403030e04020a0504330804081c0605060a03020306131806020a1e030506010207080d021b0a0504020307120b0a032406150e01120b010c02190302030d05 74
    0x40c107450401000b8482000802e510074640d01d0012410f540042c0e0300d00c50080101da29102d190018048004a03144840e5186800d0383c02d40c070b80c000e80e104006105038584130304461003801950041c04e00c503402d002e584c0095101c102d01c03800c5850804400039140d41c1e2000440c03003640101e11000e01096000c001c00200781041e0400210078a21044200507121001e01c803202d400f0b40100c0003405c910790104004d4005802002d0240c01c09039200c44a41c0f0701c034881100200034160403520b050041c0201d0348002286000002c480d119141250003804080d400c0b00f0040740c1e0720350421440d40c3e210090610010315512248000d500408460744da08401c0c40c200c2d0542d41c241c80c80d0000440c040c0302c04010400100b00c42c3d000c1110aa904003418150740030070703a0140d20117810240c2020205094491103122103d40022140203e268280c82e010007031310542031507104a4486d44601c0d130208940d25223030001440c04030801030100c1a0030032103c4c2d07045e8032030300407a2030312a0503042d4801156000030f40303982811910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 254375296 1250 254374046 254374067
    0x120b120f06060307081c031e0c0e2d0303070c060917030703090308032e090e07080c01050a110d0206071707020a0314070b0a0b1906051204060608160303 67
    0x75001054a01c0ca40b550441d55a1188002ca11481190011b88000203109804c04060781b5004c150340d9241d076a10b200c40100412404c950240800c0c0c0c0d52503103d01c542000c040648605035075102064200f007000611f02e8110309030121281d0f040c00200700c00d4002030500030901c000303080f942d515146900c3c2480e00d600903110b0780040c00600760380b081c03010300c000039408541e241c162030340203030025120707110040c0b40303210460240c81c26452032204221000c0742254081c0b190301280d10003003080c080e217034228100e523858058a004503035070340e0840300c00314200303500544c0144208c40e420319006012198054140d42801000324003e00160002c01c248a200c5d6440380182d40c01c0c2c5071038a08200349050403040655100a0070500500303118104000104040203401565482e40d00322003904c03020700e404200c0c00300500c0f01c803070458440d8030301403e5455201d546001e00401d460840d1940392400030302e0410580b60090050003110403030b85400020a00e01014000321250104e0301c000c00c0f03891400c502e005002c400d4034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 254376546 1250 254375296 254375299
    0x20f0706092a083a020105060102120f0904090f0b0f011503141803220f0801050106051602031612020907050a0c0f05010b150414010207050f01120b120f0606 69
    0x49034140030707154001c41e4003074140004d120a0540c526407112100c0d010501e9201241e152608020700b05019501900b00502c203140c240d003591000b00740500d440809024001a101340364201b4403101ca85410b1a0b03010721b4190b03009000301081d03c80907645010210b84111102e6420300402c4004001d43d0341c0480f01d00c0010045414148000c0d0110549010300c000d000b04030040400078812018001c2c1400d00480d48407080710a808400e910714500c01c40c44000180c46203000c0210101400280d41206104d803034140e6200ea504c0d80d240000d15106800e13240010304040c5d0345401146840074100300c00040c0d51005015043ca0281103203032034010855040d1004000d0b00900c001003002500c0d40f0343c00030005c0d08507940325882c80f504000c141490f500400400c40250f410012a07a852154910040b00ac3c00072103000e40200710a5410b82d1004903100c442901c2110382084411b17001d045658081c484c070100704156918002443c41c0058005828001d004e204c8101c0c680082e81c482e14100d6042c0012a8810f03030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 254377796 1250 254376546 254376623
    0xf03050f0d050d0513020a0b040e0c12072001090b040b06120d1110020a0503011a09030c010509060d0603081902150a110c03180405071b0204020f070609 67
    0x35058400b80c8940306141c020190a40c0d50400240c4089542c1e080e600d4041d0050b040001d0580c4500d0340c0310107907000303014206507401c00300006024296400d00310741d2440d03a081195035090300c81c04015210307080c4600031841080c0181100c4010f141c400d109480181f0701a209800b21414182407003001400e018004500911281c2800085441e002030305141c4e03500c1e1881e140100c2e200d9003d800d03003003041e049059450b49000213030b10848240e104010318140e41040010381e207603526035100301c0f0680c41808006505504103d5803946d0ba58025000ba0111140103001c280c81c003c030f04009403003203134810340044880c0c1101007001c05440c049090481c0b1242224002003d048024242400e0008030042ca0030f0703440c6460b400c1f0903007244030480940e846c1d0760950f8200c80d104e440116007815035100d00f1484900580c6017400203080390b0b2094818460151182405502681444c1c0078403020703500402003800c004008000761381c009030781d620451464502440c411030034020815015840030f0032509600c02140c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 254379046 1250 254377796 254377813
    0x1140603040f0b07020f01020d0e06010e01140621090d1e02070e0403020106080708060109050c090d02010c0203010204180905010c030e030a0e0301061205010c09170a060b060f040f03050f 82
    0x4801c0b95034481916049002d500350b954403081c04a1074030700c000c1080d080742d5001040b41412440b00d90045c9d04e03200c7c03859003503e00e07a0b0380b00c801864ac054002d201d803030340543e2580f2994860307040683c010204505d9a003028134010030100c80c0e00190312015104100a1ba01450344150010307070183c1106075503401c04290704410912284025a0f64403e40990f4810341d800700c01040030076000b540300100806810b400d9400e60350340c8264460302d40400344154211581001e00042280425504907201040c0c02480b14528600c550011504230003500d004980540d801c10000c1100415111a40c04441c0a207401007402d44492520a084d80c07600d4000c0005c1c14113210203014149000710507104045980e2600180c0c0b82c2c004c03400640034007029844814902c650032060014808107402c0704a40c052142c80d1000c10030755504441082d50300801d4601019000810f42c030000130119044101400c030f00505441c1084007000c104062540325a1040c1400c4148210810030050f0901c02c52454540d490040c04102c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 254380296 1250 254379046 254379053
    0x1c020609010506150f0d090b040b01060f05090108040b090a06020c2506020307200a12031803020319031827021c0207240507110a02030a060c02030409020a080114060304 74
    0xe01551420b00d4170060046095041008175900602600b50402075a0081e41003070304202c85507038001e01072100082c05c2d1345007032801103001c1c8044501d1038106035101c070740a5480c0d4485250081c4040c0200e1494080c184948021401d580003030561500448003606071100c440002c0c130394201c020f03800e02e426001401b03410030800d074003c004d5030b8030716030003496211440388500342150f1140c550b14034059100c40041e2000c2940311303c4508121f035891090712150316015183c164040c0a43d428030009600d0f500c5210900f40d400040c0503415181c600c03d080041c020101c0e1004940c00d6020358210a003c0508509417050036000e1880c82c0030401d460074021441d20300b02001c02200d06100d06090080e0b81d4001441d0b208103d441d54200d0901890340c84400c250161030742d45003024140503248003001859540d5004812039011480c03002d1154014020202030342180c0da030302c0207011041d03001c1c015400240400600001103000910b142191656070048542c1007030030021002001c178060034050a07007801000b000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 254381546 1250 254380296 254380339
    0x9030801140a031121070306090611120408090f120c0102060f07080c092d030f0c01050315180106020109031d011d0a1a0c0f0d09090e1c020609010506 66
    0x1da4003614244030140c96480d0004510300d40d500000b24a00c64a0400014414230f940601e4869105032428404541590030419083c051010780303002c611854008100003a06a90003045100c2c800781c0240c0040081c9000541420032013281600a604501440000f642e810f00c0801d61083c0d6602c1d403a206410101c1b40102880c5005101c481c840ca0001080f540590b1143c03400f807034070a0958500e02c2e44006401c10261401007400c0b040340a48600445000c421030041000c05c180d19040e524682103a880b04064042122070101c481d03000a801c2c1c2c60b06d4050154129100d001e05100c0e000810004800c0c5001890352021400009420441a58442890380c6c0401c10100c003400c0d01d03107000b580711044400185180c1c81d950041c40d82c1c0d602d10b012501c00703815600240032a51407550694170820b04400e49a520f0b001c401000030f0000c0d089000503c9400510350000814400500880d8014000305d03840e40701d10b1000c400d848015a01107010420116170900480d58458002c1d14840c00c02d40307221001301ca0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 254382796 1250 254381546 254381573
    0x305090a121e02010f0f020301060c2006070f050f15060904111c0201020f01050f01032d030801030b060f03030f091504030c150503060604051e0409030801140a03 71
    0x1080e00d030602015840744589040b42c0c0e49420418511582007103001c0280c000d207107105a4600c0c980c1482d107042da44c1d25283c400c1c1c0b4101c500369152104502c40603550300342c0040d80e0b65000c2c0c1d240c0b451103000100c1c0e03844050141110510840300b4002d45c00c11810134034075040382111405141c0d40b00408116a03008401c80594001d41c0603030303912880c2e40703c038682092813000302050030382c10050425801c410840740c030f24907503a20790003a000d90f4004141404d8007170176524215400c880113500b0400410000c0c007101844070400711190558200342c01c018811015540c15103c064000030591001801171109031179195030800f0046440f207450b100400f010a440303000f901140307a810320000c2480189134903502200101c3d181c010700c0c42c0d5030f03031500da141102150403a801039002c076595414815098501580840e401190010000d40c20240b9000401220264211514450345144500b81c1802c5c0c55602554030301d18441c2d1940c071540d41c1031003000c1c1440d03004908402e01c2404001c0080011a0b8882171107403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 254384046 1250 254382796 254382803
    0x3030a030f02070203120d0c08060a12020102030705060408190507020904030f0c020a0803030a0c0801120204020706111804180201080a05090a0f12030c050c06070e0f060c0c0f010305090a 82
    0x241d007070710324039100001d004485020350180981a4005418210310000b40301c884c0842608008200003175004840d5004121415900041262014401c2c0d1185010f100f4440d441441200e16203980303030b80c8403130a02c0e1042c4e40c2154a0500800e01c3c909014062216441e80000c91402c0740c14129140c0020b030100c0340c090006030030b00c46d071103034805c103190710944240b0403154010341281d0000e0398848003150390303500880c1c604204c070340740004100f0014414034180b8121042c10171400c00640782502000025400000300320380c0365940320744002181d00311b0005803081c0c41c0c20440120314100f56806202c1a81c03907140c1040e2a05118002c9000140c0e0001c40c995000105030308000380130394030100340c00e1418141000c0640745003803903030301c0c80200000c081c040144000c803554107100f0304628034001c0e580c0d4062074259941c0d45c0c10010004100034414481c081c0c00e618004c1204800140d420701260240d400164009010b030440030365030080e03082001000c0c0ca420404e203410001c80c90820105a22100c0a0078000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 254385296 1250 254384046 254384051
    0x40c020d080c04050612150a030b0c0a180605070201090509071215030501021b010606020313090203091006150315030c05060d020d050a091103150105150f070c0f09060503030a03 78
    0x194182d103061060360082c010180803076a0f14541441a50182113048600d108210803001c08203116041c07840d0100200c235070041c1c00e0185520b6003261031021380c000201d014100403400d06803c18807511100c1410060042e40c039015964041400014100300858021a01486015050096481e8041d480c1c003000480c81600280740d8009400d01c10000f000c9900281c059030000c161225442018200c2c0082c80d00000f000300304e030980e50b620907070312805010707845010039281040403c05401150011680300c5148402d845008842071024400c4400c02d411004641d60041c28140b4015098420300c5140c2044c208880e04683c40c581e250740710300c040b5004071802a500815403940511454054851000c1c0c1507405001500d0150052070090620100580e004070504014130032508000ca10721515007540c03010b200c1c06a00b84003c0c80103142c9001d80b05800c00380304028145408050b04041e0214038404c160300c1c0c0c0c0c8245081020100e20219410012a4510700360703080006660000407036946c00c0071130601 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 254386546 1250 254385296 254385301
    0xe0f0d030b030c090109060e091b04020c0a021503010618050a060c0201020709050f0f01060c1a07090b040f06033e160c08010e01020a0e06030a11040b030402040605040c020d08 77
    0x441d0620403c0c080700c0d600000e15500110740c00c00035400c103d0540780041114029640c0c1c41c0083ca640b03914445071302e54202d004480c02c0c2601c0c202078008040b0844080102c0d441c2060350707404500301d00c82c002d440f01d40600c0c011005003e12580302901a07220710b544104a0031041c1442c000594288080c85003009015400801c48116402030000c04000c043c0c0c0e903000c00207490000001c1c800d890044540a041c2d80d820000070907030741c2c0200c0070b41c942c194000d40160071107030180d0055140140094581c0090000300440010070f00300e070b10000d202a180c50300d0364400151624601038140d80c0114055400c013050030340c182d269000d00e640c560015090304d90515804104280f462210341c03103044001503410246e255640b00303004204009400702c500e1035008020340180d202896080340160b403400c40000b03580c0d076502e1f1901d00c7d1480103140c0103c01d40d080001d1000850030713140c8413a0b21982c88026052004070402041d0319142c45107200410301a601030001070b98005000b521101c040d0750100602058002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 254387796 1250 254386546 254386549
    0x6120c0201240e0601141e09031e2103040b060a03061a1e0d030e1503011214121603110f0a020f10050405060a05160c08010e0f0d030b 59
    0xc00148000d48031003070048281541d25505400b4280038508524803000b0100d070881d445880302e403142000358104541055044000700b420309010f418440b1191200344110304c2c0c03e030303030034044d03035180004141058100b6a03600322070f2400d01c0060302c201c030300c1a0880c8a6040c54648110110307a0702c40d03800b80600e14980e540c0700003e42c0303510352500007500071807030030b000030704029100d418140600724115998000404140d0340e031419441e0400d100b0b81c00880301a40c20002030300800040508460082c1018074001c011004d00c4000e810036402808e0681c0e460300d20006200e446440905092002c4021b450a0041c03a51001d149110340051803061142101c0a4024540300d140b03a0401942280280d6128200c2000407665502620005900ca01740e0015651034604e01300c0000d030480000c035181c07281420316060400030703d03401445c80f810601004006070140206841006042507126466804c0141e0a0020703450842e9440704510405034801b200034560244001661010f154140c50045891204c020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 254389046 1250 254387796 254387801
    0x2060c0a0908060c030702061503030d0c09170106150c0b01031721010807080109150c0504030c0801140703150b0306011107121406130201030203060402090607111906120c0201 77
    0x502c025202e00030b40c0c0c1440b2074140c0744001140240c01540c2210429140c3d50320340b0240c1c07123014000079030580c0200b007840c5c0e1410740c5401c030720110f60302e07030400c920119502e9902580c07444650001d40700c20b9549900600801c064078080301400081440e000c88621100d42e190f6100030b5040c040035002024008802100e1509141211558078900352810380d00e80601c00c1031803203520b083c0030310741d09800b6070a400300340200305104003c4a203801880d034030b5000e150440202c000704885110b141c1045010007021001c218081210300003404040d00001d41c4821148182042c44d0018203241c04240c01e00011014803842c241d20300040d90f0360b940ca00c84e42d9458a00043c4c548040e604094540c40c001c0400000b25058034a0362490100d0192039403c44507420a10311035103441007260300c80504110404550301651080d4040c0d0b6210201070b000500e0065240c0001c2c086400001c41111680700207500c80c0c80303500303003156100501383c1e1101d6000c41c91810454098010340d0f0000108019503a90b101d2114961702c00d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 254390296 1250 254389046 254389049
    0xb070602071202070302120f03030f0603010908120609010b042402011b080f091204090e010902041b030b061804090f290708160e0a050901061206080d02060c0a09 71
    0x404924440102c02948903a640d1109034802d4440d00c460314110790780810074011003854440a1459030355200b103180480c0c000981040d4056580b10f08800010748404014a68a0030300f101e0044240341c03030020040981c0301600481ea13301e1080c041086845201c5840030b900ca281140c0d01c0e1010300800d10228010124100304051a589211103c0015600f007801940111090952108240d030751305103155882580180060102508003c100300017601544004060b00d036100c008030b2140c0c021340004d0251400148081c2404080250b0700f400c05415104d034958125094030a5410720140300141c840f185020003a05000e02d4803110a9402c00150030070101c180b680c001c03d241e0045100300d00e903000c0c2d0805440d00a03000c0c0351b00d802082016003d984514490318405080240e22196520122401c084420216808c0607440401040f10740d56860243d0180c6925610300c185804400000790503100705910511081e00095640d100303950b4040f80d210b07880011409095942c65240c0c1c8211100c2529 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 254391546 1250 254390296 254390303
    0x3061202133b01020702030a030f11010510080607030c050306010302071a0f010503060c04080604080a1e03021e04050a03111804030c0b070305070903061512060c0314010303090b07060207 82
    0x140c44251509110000800c200410442c41c003410200d0200c014900704c1c441c186029500d5400f1a21000c002032007554101094990f500c2c160003500007100105081d1001079a500445461441c014401040e0421080d6404400d5250511043c4461074002e00148005441d4038100750300010038005101810141900e41442c0d001035a505152840003114185001c1c0170702e9120303000b00c001081200e8110402e0720140c80542c000380440b0340303c55951206035400104002c0500c80210100803401d03201e5030310318001c04105d45003d40e55030120000401100302450f1034000200090105101545034243d520064a6010f1880040d448000d000614010340c00e2803d44440740140c001c21082640c44081c05c0d000710f12440c5440c41688501a081c0c0c1a0744040740c03407000013040320f5000c1020980a420810780800362416005c0742645171002c0020480c4210005e0740e11a48032840608016494841d281600c400e8021380b0f48030394110390f80100402c8a5129010f00e0b21008103d50050146c02d5044070240d036070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 254392796 1250 254391546 254391581
    0xa08010e072d170f01060f0c0209040606050102060603010213050405041e05030918070c0f06180b01030506090c090c071e030c020f030f0a0b040f120203040905070306120213 76
    0x103441100041da040503070300e0030b8001603403034000c00c1c2290307a190b1030030340a00060440c1240d00e070f00308041180e41c0071200e15408204140c613402040903032508810503000310301810001c18100d0808002a203410b801034080781c001c2c1c1c0f04104444d4000e09041050055610494000c03d894071b4900300502c1e05901004000480c410140c410410028000000c10f540d00d800d030f0304013a0301314031801e000104100c212140000314200410020014070710840c0718800e140710b90400181400e042401c0d11103030701040800c882088142d030050050020070440b585d84448100010815900f101001c980f4208002e001e0306060040481c1101c20801854042403541d0407840a00312038241e241001409940f1002c0264011701a19036811054100403072025400d080030070061280000036998407086200c028401c1d42e112201402d6080014001401984421039550046440e01e081c00303485001c40303801408103002c0c1441c00794200605000c20300c03486035107901108c540302c1310710340140700b00050505825804480607 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 254394046 1250 254392796 254392847
    0x4051003050114150a0302060a0503070c05010216061109031518010f06092a14040503060a021201060207080604060e100507030c09050405150402070203100504050106030311030a08010e07 82
    0x400c00b50342c3c80c1c8901d5141c00610503812085007800600000d900000e0b4100b01c04219181800d801640250381083d414a030460701c0d0460382d11100c2c02c982003080e014102c101038204140a119560080818503044a0005440c0c014001c002955440d46c2b10386101300f180c04a070008a4010f0895040a440300880d0024010b41c2c0134034400c1d40007040c541c003a4000c46464080b500346c0d01c0e41080d241039488584001c04500c2d0401040090344e070700714402c80c810003800c020800840c41c0c1c0c84c1800700030301a0514050147e1540103160380e000640e48143c00c40c20456110380d5080010240010743c0c59006500600c002650b09a08906242080c0e075004040410905101c10320800380e500d548201c00401040da120440c5030380328800c00065a0b002d0355210035101802c1090021444d003607006001c0b1501c002c00310341008440e03018000039548200c50030380d00750b55104000c105264000301c00300c1c0c0000c140740166280450f21100900304500c1030060b05074030410f0034001140710740944a01d020001c000803517110b811 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 254395296 1250 254394046 254394071
    0x4020f01020f0607032a0f11010b0402040305150105240a0504090e06042105091003020715140a1b030f061e080f06010305030a0c111f0e010509010c02040510030501 72
    0x80604051b00e041da18281030b4090110081e031030040094940f1503841c03080380d10741801e080b0f170505030b00320845299542e1510310201c0b594451005100075071042c5d0151001802041d100f280a0105a000310702600d0200c1402c0904000d4070b070700c5071007001d40182e455100c080e80c0100301c80500403034200a45140c604449010310407400113485101f54410202c604451420200c42e1440c00d1030f801000c00421000d101d40326242c908800c1d02410002e140c5801803c0800d903880380c100e000407008100903041e0f40c42030701d441d05a1101203080d40c04001c00ca01840361404022401110802e43c0c04910b0401d40d0300c10841c825006150424001005003540341586000c681c007083c0f00401c468403074941c2a1040c0c07401c80048500104050f8102d0750000081d40c1040080d41042e61740511840044030800011400c88079103030380e102043c0d640944192200c15039600903139005024680780e0b650711418032030180251021683e00503030844003586c0c1914007003010384410004620340c1195400040c119401c1580c076082d80b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 254396546 1250 254395296 254395301
    0x4020403050a02040e07081b191806060203070803010311030703021f090503160605031801020a050a020f0c1309080909310b01061d030f1606140304020f01020f060703 73
    0x180c0e402204c0800c00b4505103e19269586901d2061104c6608112041e28040d500f206e41c14071403581c0034042c0701400b000a09003c0440174242c001d4410342c4054181d0690016091041202a082c42d0004524122080c2c8507010540414400180240c61400f12103109482c14001c0000840e4060b2241143c5015002081c00100c810007120000611a03c000500340c50005114103d0038003201c0d4501201d424460201e500e90300080004c0112500c1140c50a40f0400c244000c140c000903517039030243c882000800003400d1560341e490310120303540201c4902480790740b081e494164402f08448009020001c1d40340800e01e80c00340c081041c1c4e0046540c0c0400083c80503035600c071001e40c088401807103c0b5507240502c04080b02c143c1c08000d85003003042030051000501680f949980c0c85411400000025004c03400207151260000400103150482500c5503c907510240e01040070309141d0811501c0c042d5031081c9006207010060002c0e01c281c40c0c1301c0a00c070440e4020b02110000c1010181910740034030305940c01802 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 254397796 1250 254396546 254396563
    0x504050c0f030610090b1215072c10111509010b01020f0d030203040317160306090e0c040b0604170601180b0310051810050a0c030608100510050402040305 68
    0x1191102240712981c6004903240d4401c8070008240b0300c07682c2c1048090401000b141064076040f16180100b00d80910040200d001c01c0303140ca09142e5464076000da402410b4515000c002950179600241c4170245072401d200b1307421009026214210a4251020304541c858500c161003c02030184c0c100c500c110301c81081d5130364807686008000740030344024400120ba80b0000c60316040c505030041009884454800c2d0021904640249841c8800300c0400c6d04199810308142c800d68060b150200c030070f52071680c260240c9402001560b000304505035060402ca03848049901c0e40728030031075480240c4030172580c604040e1400340103510314880144e1040072003203564030300030b01600700740e038082c40c034410180410750064800529016000c1c1c9194015040080094100907041081019440c101030354025400c002146d81c901560718041404d003440c000071000c40f10030591400405080c144180710a42c8009901c1c80300008141002a05643d05103643c1c1d411040c2d40c215541c450300008c0c0010a00c00005035850 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 254399046 1250 254397796 254397799
    0x3061701051b03042a030c090209030606090705040b1e0c0d02010e0102070f110321070317010303091a07060603060501141801060f0c021f02060a02040308030f090109060504050c 78
    0x30400307850880d0002c4a4001100c0007003105009644588842e0480c120202d0b2440e81000503140c1142c80341e42d100e072658a0340c1c010403801c990114540c000c0380b0b800c002c4240c10513020760b18254641031248006015104601490030441c0c400038000681d1050450034040c00300448800c1921070b45442105922007034503500707200066080011080d0140e0040c0700710380c51103612400d0040201042c0da281003060a51815042d414054406c030480070948140c00120152105598a47d8036003180c900500480d903136016540315810001c00600001e900440c0d41004e540780d040e060614074a001e0410384d400e01c1080001003007139041a038000104070040d0000d9041ea03540844101701d0346080014091034042440f40c0074016190000100a800d0084070b892804c9145858071003039040d0a90041585200170b0318030706104d4400c010002e07001640c1406500d0700b001150209500d400e255859001082c040940080c21911026000c12220ba801354003520002da4042401d104918060031b100307403108030055005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 254400296 1250 254399046 254399071
    0x6070e09010602031204031101020706060605131a070803060a0f03060906060608060307060f030b0a0320011d0411090315010f0501020312040f031413050102010f05071d010306170105 80
    0x200310b5900110a030b5080e00c20305601103000d43d485403001c40d0400250341c0c107e12070755400c100311408542e01d8000c85002e026646c032040d0343c0b0000410615503d1010354800114403c0752a40000000c8140084510050300710208503129220080010912141507000b032031000740c100b4001041103280e41154040a01402c4100a880c0e035507042550741540c0bc40d0309641c590000403050080314003035503903041005a14500012104003140228440c070800b600b00391000000e030000c668034880c0718a07900c808018203180c0340d0300c6510800d0240e006809420400d5120f07a48400c400303403e0000001c20364000710001001c40d0f020303424a001424034940f0a006222281502e10004102035000008890140e980f070164211030355619291540140740f80c41d411002c0020205030b900c2d22944130342c0070701480119440211250391500001908440c006402101114103000c200b000301074005560341440311a020456400d41c880780012002000c07e50407400c50b074640c5075900c64221382c05502051081d2f85401d044d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 254401546 1250 254400296 254400299
    0xa230901060c05060412090b280306051f050f16030905060f0a0518040903051201050f090a18050105012601020f090607080f03010914161b1406070e0901 67
    0x1c03030320020340b410b002d00f11358402004140003402c1d11039409070b01c0d01e19141c0508074036141d20608005901c50398a00000e00e81e0144609030614200115140d4038078942001c0090601c0d140115041d10000d902c030110783c132001c80e81c0c05047c81c010b80880304c4e0540074065003503440303c44e50360fa000410080c4600b03400007220280701065a040881c1252058045400f00d941044129070084980d98002c0d004015446240070b02030b141512140590502d4920030303120750f0340714510f14240c0d62583d02c05074842442140d103138200d0f00c0755803240e06201c0d401641d8140c0200f0b00205a40e04014440300021004007650310303182c0002600358842e80000aaa00c03208100f102414132144010309031300501489145404040001c0300061421400a12040b4880e9901e0703401e0603450803e00c80c05030070076030140c01c600340c1b03817a280c02c026841c0380700d40c4d903015440906203801e000c8041c0000705440341003014401c0030300a0359066000d2124103210510100019400c9405a00d40744000814905221242c1801030b54407500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 254402796 1250 254401546 254401559
    0x804031b03081c090503040927080702041a0a2907020a210807080406091e0927060b0906090708041106040b12160f08060f0a230901 58
    0x30000c594114510342d05014072100031504004100000b80070841c0c0c0c403c8814001401807016100800800f4400a078400042910502e810080c0c3c40054000e0310b420115800100001e09071683c40da011307a400038204140607401070910314403910040d230200070b0040001d1035030200e0143c0302500507003603012040d07490940c0f0801600c0c010380800a6000402a00500504091401c1c108036a8034051003064003416945a400c0030790f1009805036018200000c0500c0141d40000303580e8014018800c1442070340c80144100418400540141070f0000d44440441c6540f030f40e600c0f450b01546641150b1418034801c6460100000c11a9100d11800b5503003480005200c0c2c901886c41c04d01c02e6209440b007480c83e035240d036100c48030000004009a03115005000226000c3c0550024260002e0760803542c85043c10000030002000300c2c07100f01c1504000c41c1c60001d900d00d990024420782c0008055601d40c1045030b80000251140b0383d60381103000282440c0030384614111120f114100b041d0001d0301c1d41001030340c03980d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 254404046 1250 254402796 254402843
    0x2a0a050c0a0e1b2709060904021f0e0a060e09060609060406030c0c08040608040b0c031e1305061006080609010308071212060605040302040e0f19030c02040504080403 73
    0x1103200c07001450880000d8000000303d0b07810310601940c2e003026203020701c000300c0161000e5590803941100300324807030000300c5030800294098101c0c03012900c1d90b10610702980040c0c1003000440100480c40c0c035030301c00d030580c5500031a1455138190009051120789500c07810010071020320b69141511501c0ca25012074083c1c200030f01111290743c00523009514290030004103401400d81160800304001621000101003036000d000390010b000c8a5550023000c3c08c00c5e0400c8240c4200140504540360741c100288008800c0110104800c01c06541620f40640e80d50044107a06801c5080050054080d1038104500800c00003280029100c0644590030140c86070010b0100c3d9440034000200302403400c00940003c1a142c0014400e1540e040ca4203283c0c0301d01007196901941c0071540580042440440c041c0214030301303802001301080036480200401200310003180c1da5850303d0b00c03d5a41c4040c9841d41082850720608043c0c40e80c84d0041c00510041c1410314099000741d00034072040d11442c040100d041203003640e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 254405296 1250 254404046 254404049
    0x9011805010e01060207032904060c11011a010c0c0f0b1b01090b15040207051b1c0506060d0309091b030c020102071112151501080f070f052a0a050c0a 66
    0x217134000e111850541d5207880800c074208450040c400003072010b409030440403030070451060b80700b03000104c0c13041c04814001c2c2035000a07600120303403a410844183c80c108141c201080788600240380c0000c0a1806051414000040741c1110381040410704002c02c580780b0780300080214021040c60008441041d18109089801c0b003103008055031408cc012403002d00422401042e0502d0082c40107240400c10ba46d45440c0c0001c4aa100c0108604004400c41515241c03003070100c0a52890104141449680d1340c49458003002040603104120a11484c403d062284881a0103490b82420400c108035100034946890b85070851342c1341c002800d02c1c1031030036500d2060095075403035680210f54080030007500e020081c4011481205600c10301c5000d040703130040f180084582d401040039141e4100003c103081d0004124a90040141c5990614201881902d50703004034100901200c91404540b642c40484000c110741c80c584460322044290851500c1c540103001c110a11201d11900c1221021185003050150703805d440e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 254406546 1250 254405296 254405309
    0x82b0903150b010e03030705100b0f06030609090a0206040909050d050a05030a050411130f230103030503060d0f080c0f19080904060902040f0e0105180a0207020f09011805010e01 78
    0x155034400641110781d0002044024141846000540301c0d002003440c40d00300e0b0b001900d860740000d5905d4104220381c42416007000e410b0319003010a4411202107242448054241401601c001001401d007079428004800d00750f500401c0c5075943c07640c6680203c00f42c00484d00a0310540a1500110714050180741180d20201c0b06889541c1540d451942c41001803030024019034404070a455441401d95541c1c407181190310080000040e024010300d040000c59404c441d01d4800c0000d02d00e10007881030300c000c3d440c6044903030500c0e11a83e01d60340d907008160700200c0818003c100d00c115a584000300010100680003000f101003c4407480507400f0f20f10b40d507502d400740450080403500507040e0040340010b4000d0804402c00f030408102650741d498884100c1c0c0c070640c0309002000640e0340c14400302001c080c1c91801050201c48100703650201c06104602e402003c1c00200351640d002030710004546540764101a00c4100401a2601d580d44564404041c80502200d211452525001181c0a036502584c981620b11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 254407796 1250 254406546 254406563
    0x409050a151e090f0501050c040f050a0e01150509030d080403270b0c0312070906020706020d050a050304061803030509010c080408030402010c03050c0613020901060e180a06082b0903 80
    0x110501007400900001c50f064034124012a00d07940480c0303090007141e0203100d5110f001d42c1c0d00c1e4540060260781540d41e80040e0700c00c2a0742d20342088106420141581590750f400c0282d442c4807011a03059800d0700c90710644603058007e1900e911082070b00700d10018890740c06074540d030420441d010315000c0050851318190b10b640805182c02c5c04448550800750040da40b6074070840c0d1501c0303190922280c80b424129085000100c0042081c040b043e41402104028506400200740d9060880006407030350040d60314440402c880840014188501c50300810b404500c13066481251402604004001d40000c4400910640c28a440741c40104e201e0440507116a4005d20480c1c1542c0742c95004403041c031048141039081180078400c02d29080401d02201e0700400e000f0255015100ca0f901c148201e19005a04c81803d00031000d4801b481a1206140441c6200101070a540c80366a140c1e84400200840e4000c3c0c001131045007500081400182c00d80b405c00225440c4d5501034132101c080c22100031030f85020040400c039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 254409046 1250 254407796 254407841
    0x301151209052a090411041d0106150c120503060f090907050a14030309091305060f040c060302271f0503040507090207230a0b070503250e0607020d020409050a15 71
    0x103100c51004946c407000204007040c59031050010468440002c910300c406c2e070f55106c2d01007140f01800c80500101401a041c18500b200301a101c0390f1504520810030302c1840000400500141e6400440b0154110014801c100a081036840141d4a603950f00901d0b020743c0c50241c0c080b444013002c03007105000c3c134030041c01541340900c0c0c4011b0041d08140681010000049000c0003000101e0a00080d4441c400c0301c0b02d4002c16150606001041080f151300c21401d240c810010007002031411101c1d160f580304003200d50350300c0b00980d402140b1000303034281402021400d04007008202e61383c80030040d4002ca00a10807294080c2e201c24016003280300e1400000c2000c401d91545e100304219405024544212090541c0c040c3e4001303465140d41003804984201c0060b100004008a031340f0703200e41c0c0764403200c80310727a920890340c40c0d6110260111031442c1009206000100e6864210750307070362541000c0654094014010082d05141031940c0310708840c0e040355041040c0000c881c51420b103100f012140d070750300301030f00d007540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 254410296 1250 254409046 254409053
    0x906090708070308073e0901150804031e03020703170717040503160b060108090a11062b0209030f0a030c0b06030a020916030606020a0203030301151209052a0904 71
    0x151700a0704100d038a11261091000d000426011108000c2c1a515090710b4031aa905a0100101480b2003014030034030f21600140108900104c41015000b4142400c14864445050644038403492030383c42c0e1104136071079001081c9207505070058640248070381c8405002c00507165240310340780c1c030441d101700014070403c01283d2030041600095801c1802402900e151070f019a412481000c220b403802c0e52060308010a212055900c072104507840403e10024101210299880c141011b501041e500d22403400454001c1c0001901851641034070150a4100b404000c90030540c0040e400c60011148280100880c030b1500b02d40129103514419450b50380e1411003012135603070440c0d405020700615090b100f5031090400584800e501140200c0004103040300e0312214210013000d81f80c194100d10115048017050000580340003007a80c0c1500c10400450b44604004801110740c8020304041394280d80c02c2c41e1a95040c090b0110390190084110b640c1d41103203228904199a003600070002e403e170480300b10360004020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 254411546 1250 254410296 254410313
    0xc091802180d1a01030804050909010203040c0501052113030315080604030f05120a0b03120f0711040e031b010b0108070c140c120c18060315070c060903030509060907080703 76
    0x100d449114070000d203600d400c2c00e03c400c91000360411206480006014015454410420b40d484503e080c000d51a5242c260740310f100c203180d64401c42e41070041c0030820048811500412840203402081000030500d814014002408850442980800d1038010006660428109103005880c6203200500e403d07211546c3c100da81c000100052401c1107003c0c0704179503ea42014105900034011810007040500c4244201070501b0f024101c9040c440d60b00f040002c071030310440c4090362601500704801100307120036200498040c06122059400c540400203c00c02051010707421910500d241b0402040011056001940c080304181d40f501c1c04580350713072030b11400a880004114030828883c8242c0702c1c001003040128110008003806c48006400203842c01c032050070480009000e2980e009801245424601d002c2a190b080381500103c41d01d0700c00001410450007406400106075110b0020012a407860800600034042640c40880a0207454085207843c000007031500213998104001d0300d801451aa111020f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 254412796 1250 254411546 254411569
    0x17132001031409060402191419050d0506190c050d02030a0e0f150901060e0c070c0e0a020307020c01020a020102070b090a03060207080702031009230a02040c09180218 73
    0x4242e20b48600c6191141c1d040c010030701802032240140003a052600c1003002e0802e200384007204201481004000702e0391240c025411000b000d0342c0d0307500708074008880c00e019490030b50001c6400ca40343e0344500080100014560744240c20700154107011260202d083c00550340180b60090008006200c46050500c02d0760007507400c09c140c5040080c034180b04000440c01e103001806402801d40100400000084601c02a00e500110f5080200f01e118200b00c507140d0300002c0a486081003130700209007070041085521f04240501002a00b12410345000301c8458041e50040b1440001805400804001c3e540000307100da0303400394160040c050300c50804d40c003000700e9005121070795808529000000040b442510041c48603a0140c00c0480e940e0441d801030500e00360001c103040c200c052512650300c0214420741414500c0b08104100c10000c0048102030034a88a030000300030350b0003442c00c41c0a121898110b403507141100c0904440c10b102410031007903030049004c0c2c6080039461200c40a802d24035854001c40481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 254414046 1250 254412796 254412799
    0x3070312020c03011a01090b0903071203180b0702040b06090306061309020607050303090f061005010302030601032306040f02070506040f02062209051015030911040c171320 76
    0x710b0401c02d040000303080d030b800001288014a41c014690303015590080300ea00c041d0500100c0c90b80380c604190042641c0f280503200307a40e20329040052943c2007520904001d1100442c104401c0a040c0d2a14444445948030040c202e00c150301d040200c001a04106080e140c0c00310009000e01801d603199401d009890440391800c140c0c5a54414804005035160806061080e000b48019501d07454151183c501d003680050040141e94401e90030426800001d6240d0000d8440a2a0150b00c0703480c0c0000681c01b4000800010b035100029401c68a49900340544451003004122021300400120340c07041400c9204044010385a90000400903000c600090040c0c0140340c40542081c4c6881e9074a00c80c00200070318808a070701a149846400c11000c8074a02485400c800030819900c80307a443c2081c4504e02101407a0030744107160f22200110188a0060240b80d03c80301e002c0c00a00a4108031303a0014800068401010038030b8a5100105120690301340c070010000d54401214a004904c0c000c1c00440c02d105103070f069 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 254415296 1250 254414046 254414053
    0x5090a150807180c090b03070c050316081e03150f0609060c071d01180e0f1603031b0203060601050c030904020d06081c050f09010e12160905060307031202 68
    0x407110001c2114030000c100180342498040280c10000c425520049440f104000b6807990501100d44040120794001c4103d0612850300c3e2000c0c5000e50a50151007038458001c2c100403840411300082034010000c12482c1081044008100810401c80380002d0701c5800740004503044480460900711031001c41040c009001360f081c007151000040c401c0c0c0c014020750303030755820024042180054a10710384010529000d005180c96041c94400d042c042249411440240c4e01c8102c1e801800c030381803040c0500022000280c4011310007400700901480540e101c201d0000f200c1c5d120782c0010280c08603040e400940c0c0180a0441034942900448a07074111000d00030141c0000c102410700c5681d11701c01817110044110300854501e00c2d0003043c0d414051079031f980c030000c00c1a00003c6035080d80e01c541101c1c2440c0c02001c415484d00041d42c0103c03100400241c0586d0000c2010315000d03159038001421001480504030146962521041ca00c8141e41c400d8400d40c2e019805018140001641d040c40001781c071a21f0b1044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 254416546 1250 254415296 254415299
    0xd09060504090f0b0a0326090609010521040302010203070e03060c1207021204080105040b0703020a08010509100905010305161d06012303161b05070b03040c0b0d0c0f030605090a15 79
    0x1110030015034002c8683d4000300316103441c20091f01d00700d240c01101146445050400c1c54010a5031440b49040306410400001810b884100c10003911510001625011658600d000d1401034000d40c81521200c1c0495024120300b2000e1030300160300c3d4842d03030340e0205003801e14603c6400300d07113030002c041d00c40750a6004540c6641c400d40d40355805080185842c000101300c03800c140c200103485040107040c0c64109401000900395150304000046d0440328142d0b900d07486680c071481d10390600368280e0000f40503a81044000002d110002620205e03100c14096414022592581078100a000c2007408020701145600059000d40c001e0016800c040f44103a1010f02d000c004201c2042242d10407500030380d40383e0a68420005584d80314070501e10f01d0398102c030031042d014456117a641ea9a4540d01c610500240300100044c100200011702c00002c10010302c4d4503403145545214803000d0300014008800040b1110b20b504000b900c00c1c02110100c0784041c0940c4040d49803c140080a000f250b00100303400030318541d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 254417796 1250 254416546 254416549
    0x15090315060b03070c020a0608060913051009030504090b01020601050a140102010b0d1a0619120f020a0e0f060907080c0901090b040f0e0901140606070c090c110d09060504090f0b 78
    0x210300c00c00329a80d80d170102d5180707403040200d81e040f00d420500820200d441007044e40e4440403044c50b0001d1040080744418002898194681182e803448100c41c80c1c1000d25030341c10940c000021301300b40e4850100600070319800c2e00c012656050244551070b809105d00400b0040b105640e1143d03015100c045c070000c40e040490801003004050702403c102d40c0140c18103a00d04165610030903a64220340300b100c0c41c080d40341801100d02030009860054000c00190100300ca0b0401030030103544190365a01602c01a0920b60702c0345207640e4003c0464001c404c1405100c005465480e140813114407410403500c4c0d00d0196102c081200c1c03420740020100a041c8800742001203406003268003d00001c007165161112101d06018540741184005410820b841c0e052101103c00d08c40c103042c060341e01c210b085c0c4005880f50b490303041081d09111540d02621801382303060003840c0c00b41d5201c0c008402840032141211000c59094800b00c40c1402148180000600d0500c0103121a43e129004020311080c0c0c0300010816018020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 254419046 1250 254417796 254417819
    0x18030d030e1b010e1903210e151c020d09050705090108010519051f090b0f06040302060403060b0112060f0e061e220e03030402030c03060112030e1c050a06061509031506 74
    0x14201c0f4140b404452080b60255008d20301d2005040180e5030885d2019883c1005403040c0503030456444d00b030081141804035401168192400700f22110414440701d411824142c3e1500715a004072030184000304e0000c03551050500038103000d841c0b19001041e00d1303001e10003102d004107006004000701c0c00e542c040403180d1015400141000e000c0e8000001505580f80d01000800c0d07044d2010280a101c1c02e202c100007603541c404c25101201d0b0002d1011907900010f00c0100e440340e24510a803030403076140900128151b00300d11001411745503020303038440344c0352500030030040c90304941c008400c42c00c40300705980708203030401c003e003003a10105502800b040d80a0aa2445054464a4a4074559a480071041205600c3c04200c01090444c00760040c0903d54140a00f02196529214000d03003408021a0725403801d45070050340c2c9404441c00e10406c509580c103450200d44940d00d4820544600f400c00c9004a610030020074041400007880c1c6403240d02601d10707642e540d02600024041e4005e255243c41c005403424424 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 254420296 1250 254419046 254419073
    0x120a082205041a043b0102070212030702010f0c110103200a02160f030506070e010203130909060b060307050403060e0a0c080601060f09150518030d030e1b010e1903 72
    0x440c52a80200c0f0100148422030340c3e11654225a04200360014401107002d41c03668400300d20340744580b49040724001e54240a40704502d0020f40081254035468191a40400a082d0f614802d0780d44800c10740d07110908491500c00e030340d40681030004413a16480c00e58082d034030581c491094a28070020031000040780202540060f848200960441180641c13a08285460903029150188541b407041d4119103542ea82e03548000c00c50002e0001d144400c0768241c1c0208166030200000c000b07094092a1282c0392107014051082e0100c8060707050a07519200e616110064920644075603407070300e0400f495030715010082c0c8071407500410140036015801c001b05032851400005400002c1c0140441d516019000340700403c0354043e0001c101c5503000c148400035007030045101e08805850415211800ba1021070242100c802c3c0066241c0324841c44003031400d07050341007094042c508805076140080e00c0742c1c7c1d4519a64040e00300380e000403c502004000d9207484450b00e4401c0440b10f168a8880b600c03540d0707101d03114490 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 254421546 1250 254420296 254420321
    0x4030909020d0b040f020c0601030f030219060b13140a0216050106090204050102060a060f0626162d050304081c09140a0b0601080901020c010f0605120a08220504 71
    0x100c0c280d14240e42024011460b10110711178003140b41c0103a07003107400d80340c0c0c0060000410961101c041001458806c100c042c060304484102c0c0f0781d042d946898042d005182001c0160300071589400000a6010030b4422030189003141081e01c2c0843c3e486581020081d401060f41030716840c00c00030f160340424800d21624014041161005070303108d00301000a07140100040038a00018104403007840908025000202146c101c3e083c10b80030a0740781c8140581610411600d05031000e90b01c020420700118041c2400e000b060b290311050504c260a86089844c141445000d2903100f1b240c90b00301e408144588011540640124040303400c1003d41c0307411120314074240120050440d01d03851640b0900c40300349550b0b1070481d4040001c0c040404e00f907454403485a4024001c0e410b020701080081c103622000e404813004144004000c0081c1c2480e614000001c003898007030765000d9103819606118840d000103200042c1c0e90800708450a2a08903260300d82c40c00c2256011103650103141400041c15219405140e00300010b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 254422796 1250 254421546 254421551
    0xc1401020304021c081e0c03070501050402120312061002010b1801030b01050a05031e100924060803030103060c09091d0c010504351e0c03030403021804030909020d 72
    0x2098010410b40e210070300078481104e40f0f01504c0d10006034450040320f51b0001d001040d03005946030408020064003611841ea080e0780000503000b0304011040d40b0881c80381c3d1007151401c013010b100da00c0c401e81d01e0140316140d600038582c100c040340c1c0d00c0ca4038080803541c1899520012038605628804221708055812050002880c2c510050041084400c000350240c0019a202c0300c030286404002580c3d10000014480d0210807080309500b564012b11035549007000c101010300ca2178580d03280150030b941d01c8036100209a4100d800c0d400e0f804c00c03980222005c50300f001e0f00440c1142d003103866160003040990440024440741c60300c00101c10447c4d02624062904101c0c50f100c8080d4003015440c00c0040c600c031503504116042205200000c440f0700d981c0f040e802030801c465900783e04010811114480c0327005c580d0140c42058100480c0d0752541000051143c0c1c0c54055442c090a000e040c16924007690000950280c1840744904411105000040c0d0140c000d142c4a41180e9440340c1c2c0001b00e03444a501c8902968 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 254424046 1250 254422796 254422801
    0x406181d010806090a0f021915171302030705090a02070b15010f03060803220305060a02090316531b0d110102030d0c0201020d06150f0f0c14010203 65
    0x75414050a5444841c2c1c3c40070304005c000c20354800002e0b0f540b80c42e000303214401c5144440d040d9000c0c1510b90026003024410450300c0b0b403a645024000403c0c1c84400b02d10300d5070b4140001c50b007001c1c2409001031154090001c02105c0d0070101080600310004081710042c1d582801b0403404a42314005407801061440c490719013210b08030380018848644142d00500b45424840d0421000c0d400004882442c50305030100c03104102c560310341101803040740d40098010f1090f90b00f40080051164018138141074100c00319071101da40003408148603443c6120b41828080e6940c0401144402d984545040010850340c03034080420fa200004500c00c00d100c8a84550110a01a001d6009003044459407100d11031a034295501023690020702c003545546002004840c1c0c140d003400341c41e4020015104480e0144005022604010300c0c001d0003504040800348545085c0080014800468640c03001c4038207044e914102c2c81c0f01100020364444211120000802003144c0030381c0023046a0442803d959210000013680c2d90 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 254425296 1250 254424046 254424059
    0xc08040c090e0601060305060f0a030501141b04060c02010e03060f010303030e030c030d021803030d09060c09080c010e0f2106010b0a1205130f060203070201200406181d01 75
    0x200c0180e08150800c6103044101482070100281ea0ba0446960b841c010070b06603500300204132004011805282c1081615501004010341034100c84135100c00764000009540d11104e0a9004030354031a10244498420442880000d20400601a4a50042c10300ca00c070602e80c0e03000300b8038115044906640c0c1d050424018410590305019105030608124000c5040c40d100511064032882200c804c601845c0d8005071100419960316007030141c400c401015280c4928903200300c6000f030320541c40e0440d1007034034200c18410254003401802c410b0350f288400034500b4820941c01580c5885c8102c0c2165840340500f50405840d50741c104680e9140c0700d00c80000101e01c1d102903009464080706811130341c80f40c0320520000c04400e41c08402d41881c1044c00c0300119240d111641d6070400f070044c04001801c58005002e000d400c0c040302ea0001c50198074594000c00c04402d00040c07820b800b010454641e0f00040040004010390cc2c0f003040c1c00f420882c0b48400026100b0f507100260106800d8650021618500f1a001003108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 254426546 1250 254425296 254425313
    0xb01020f0601080c010806131803020c01050a05030a0b120105011502150f0c0a140a0e030c0121020901050c0a05160e04030203071202011b021609140a0e0a060c0804 72
    0x92000300c00140103650516103183e807541c0b40d0114040c100400d01000a0701031382e0740b03465200010304000c020407507500c03506644000080000c40503000751041c8a004451540b00780e0481c2c82805190b59001e085850320044c08028210110910741e021070042c0303507281e018400380b04082c000d00180d048d2803500020002c011342801c2000c08400c56061401c000c20803a024030300c141c140c0c010120280c00369101940001500c18400741ca07500c583c0781300e0100b2450312003504920781c0340700360004a0480d0034400d80c5000464034000410851409905600300b00140c0c00a19000f0b80813101e8141800e07410040c43d00c4074a85030203070b6208141c030b196004c0310b0000c0d1440110740d00c00c0082c1644d000809a185010348003c2d40d68411074600070010f96900b807000c0e0240f03200390310500e14403120312800d40d01100305500096545080030010342a00319030800014000300688107840355280c410307000c2c0b4002e94a000c0501c00504801d23040d02c03c1406003003100c20026205202d201000c0c0400d0b10f40c100d1609090038001c44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 254427796 1250 254426546 254426563
    0x1205060c221413091109060613030f0303060801450c0e0906090606010503061f020708010b0a030f0206031f090e06011a09150415020102090906010912290403030b0102 73
    0x211149024890404601c803841c034a0540d031400d84002c1d141f62540f07004203c103882900c0d1000e508203001d82d40401000180c804a400c000d02135602440080e49a04a103401c940003003130282244803044400040940001c2d4000700310400d00b241112401010407400f501404000e282110540c4212a0031b11400020540850300141c5250061040d840c0c01e41859550f481c0140c202c6052190100c0000c6e89079031000740c48a0820007548001220a603081c0d0082d60300c060174000e40b04507508200d1004c895042c00c00e0010201c0345c00418261141c1c80b50307001c2c070050b0391000d0300318203984040203035207606840920032501c01000340782c00c006a44680c01c0669400c100040e0846031481c4d041d02600c0b107001035001d0903940c212508480000c40c0350300c5841c0340d813101d2107030350701858141c62411a4132041a4040d030192000b8682601d00f04e4460340c4e407100445446a2900540c259000b80c2405030f40030070740b5224843d03c00684060004042071000d208404c01e800f0495080300060f0b103445c0c6000b01940d042c4202007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 254429046 1250 254427796 254427829
    0x2040b040f08030309060415020904090b04030908011503170c0303040c0f0b090109170106034806050f040503070902180a0b0f0c010b0603090c0a1205060c2214 70
    0x14250b082240d0361750340310600980050a4200502091401100d81e07034120b030700340e070340040007003100469038505800c6415088400360046100042c00040400b4113010369004007259181c207885c00790442e51544c050074010704c14013100c01000d104100d07423110108000c60203a4010074a0302641482d02001600d40d0340d2942040c880c2d880c0920400220741d0704146602c0680d034810701d65010302d002c020990b5005103250740c00500244a180362b000d6a1003950f00c9114082c00818a0180741d048010035442000c2c845101406000030f20f60508002c1c0c2c034440d0025040703886c503151440f89410764a00019140c9103072030300911211540026200c05c00001c04a03c1c840c40c207000d440c18440e8524203503208001c0d010b4018020340a80f0005450110f44e002948414094500103001d540c590030003034804c0d95079100e00f048150107040100c6001c103075445d0201000403c10341c400024081903035003901d025404c4c2c2002c2030029000040741f12007214441c1e4100c41c0d4020740040040140c08420003020408160b88641015 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 254430296 1250 254429046 254429053
    0x30e0904032d02030d09030c02090f0612060c0f07050a080a02030d1802031002031e01170106050d1e080403120e0a050d02010e061813020d0b0f09070f050d02040b040f08 74
    0x240b0015004015910300708000800007801c5011800d05584c9058a020020b6200340034004024011401c603c0180c06080300740e0303840483c901000c00941c2e4440040c1c40c0c044d4801c10920510b041c07070710020018142c6900c104150303040d0039a9552820442c3d0064084d54001d0382002c681c07078200f400e083c4101d848404015202c2280798074141c010a40317545010341340c42c0265800000149488030b010700025600c1034910810000e9603034a449400313103041140800d04240d42803400c0001c0c54a803140009a050b82c220b40500b400c8100c400c2c8415203031249500031a03002130144030010101e411001407080d060a9526240c1c00d184045040003412111900f000d40301d8100c1440c1b0b00d0150741c4c17011070808181c00503126203030f40d11036880c0000d62071800c072104540d11420000c440c1c08820180d070050521221000814803500507580100301c269400104070036049200c1500040540e44101d1001880501504100d80340c20802035081b41030703a101d034000c41020000001c00b00f03d6000004513034001040c00c0f4014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 254431546 1250 254430296 254430377
    0x150d1a092203020f07120506060a030206160c03020414150913060203091e0304080d03050f04030e040f05240a03080f030907120309030b060405040203030a0c030e090403 74
    0x214110045214503007105441c5005031201010700800c1080d0351102000d00b21452942e80e1202d0301c5050b103086108507014043c9074007243e041c0c103004580ba01681d81c024403407070404403500844007140c010401c044e50b083d00e00740e5000016885512940d02112080d00302c01f80c2604e000c1c2c1c4682c0e160041c2c040000d000d800a6800c02c0084000c12414a2803d980400c2c051703070301c0d2500518a45041c01e200403007400c000b101c0500342c4240a00100800c1110401c00503140c880c4401c0c1350a80031100211281c0742e0198011000400091142c00f0910030070100800000d02640c1e595100000c03543c04075200140109104403a542070a2410704061261208852003203903541583c0e03035100503001b04860410720078400301c04034080d00c0c0c043c8100400341c6509441101c2c005003606009022881c02c0c48142c8400030040301180c600e06140c06854881c9802800440c50200d02541c111042c0c00b400c0c00950400400c0741e8468490395564000768001c1d8044e036203254441e4024062800b24071040b0b0015003143d50701000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 254432796 1250 254431546 254431561
    0x301090e0c03030307050d0b03030a08091005100905061305040606061d0a060e01091a19022e0b060301150f080f0f250309050c03160e06150d1a09 64
    0x440c0c3e4017155525000d03440340d4100754110050302c0c105203555418000465072043c403650005201e0b1141041004568400010b1401c0301c0883c2c10a4030103490030107100074107010f040784c1500704c250003040c090a4401241c1c50000c541c0200c900c00d580407a010358030f1710000c005880d4001003411b600a2100e02540b00182e01d100087c54801aa1140009008229802011503130056003030740d0040c11000404c40003090014140c08560b44540038030140071084a0300b130240a0310014103613a4100d04410440c0d40360420018001c2d056403d00d04c0c0d051050340300d1409804a44914020b5402003859203080c040256143c40c001d070030808054519010015201d0801500c1501400041e40166030b40c60602c0c2c181c2c0302d4074200c04801e214071405001102c2c911204810300369143d44800070290243d42178400e00d456030b80816480348140d1a00c0c10040084000501c04407404402107908980c00074410107555003007401200c9903400040405050703a40d80c00185181c01c1c2c0c68424001c11240465001519140105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 254434046 1250 254432796 254432803
    0xc02130c05030a05060315040312060608010302090a05180304030b09120304020a140d0c1e08031804050c070f03050703030b0303070201050d0203100503060112020102010f061401050705010b0603010b0301090e0c03 93
    0x4244a803021303201c0300400c4454406105001d15181c0c06e01101d00b182c44c081c10301070602c0501c0000c58045524140d0001055481107500c181641d500800c2001d49465000d2107001402c030142014640340350380d1600c0d04840c0070410051005602c2404107991a2501d10901c5041c07600308501e100c41041e0400c1080010707980d22a42c101910607500c11000440407aa01084078144680801094814500d0307020414117200701e102c82c210250016502001510b0b00c201940360f00401030000141040720744050001d150a2300900c0d441068403008505040d140d480b42c00c8c0700540400700350301141c00050683d0602d0b030305019036504800150021440c1440c1a40001c0c00340c89505240c5880365404000b14041d440800ca48130000c0200070115230f16940c542d1152200280580070807405507181101c14010180d0b2070050100b207603d00300000c150082c4030001543c5940c080c9008940795513036100078410982e100d801940c00383c20a00881030712581030409500443e00d480e00c80200d50f43c0700c01031121459a001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 254435296 1250 254434046 254434051
    0xe1e01080a1a07021f0b0913020108162c011806050a0c06020c010c080117071a0c0a1407050f04020304020901090e030702180906070c0b0601030c0504090c0c02130c0503 74
    0xb0740d981c116594600320101e044c5a0f094100c42c801400141e05517041202c1078104861080c0d00f01c3d00c042207a121044101802c42001c407000340441d0311000001c80140310412a22a03452441c20a00b020b148800034881659203420035010108000c482e65450959114030b100c07161000346681d010f5581d003000005000c6005403043c40c000c20410311340c0b0004000680d0192101e902040f0001d00615003510740140c0b041909004030211500c5030081c440c1103020004d0300504417541300e03250b07444004124402e8209a886020580c1441c4a1040c0040002c0c514107002e05051548034003800519040c0340c101b01c1440211100c942c881e60041c01801f000d41e0358440703054119101c00d01d00140c840c40c40d003041d82c1907001e2180080c1d4130410814089040b000d0a4810707611480048003991082d945200095407952400b03940684030340f0350840041c11b0303035020350b12422104003942056810603070740e401210f080d00c5c0b0343c00c0d20300001000c44003104110704015040d2004e0703401000d005e11540c0c0740382c4030041050100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 254436546 1250 254435296 254435333
    0x703031401030812100b1201030204050705040e060409063908040305030a090c051207170303190b03100903020c0102011505130f0207050729030f0f07090e1e01080a 72
    0x401c80840d07030b0b001c40e2017001c20091070041d1541c0e07207640700c00b204110401c409102c01c6e40070710305100c0042d20061041c0f0803a0181c03410780310840d40f2519a030781480024801c45504844450352104c2e40000d5144041032903252105800010319100d224450441c005c0160902000a01108500740b200007504917050300e50000f0310182c0000d20001c01d0605598151141d40101d4001104480c144150440482c0b01e1041d140074400180c04100c900d40441d131350344400c441c0399400002c003011034514002d2942011009610040c1181c00c51445100302c00e0865002a404074050b038044900c2006039602030050700c01c01898034220200c150701e44004603540b000c200303401030700556803400214001c00240d41070b617540d41e821904039070915813a410140070303072a00c49189481c00580f03030f00740ea002c01da051f00071240f0805070381c1d03840641030702ca030f003099103c185000d44040c0c24071070704440102d0031054088250f0301c2500000c80c0300a8101580301c0f402e44081060700190b080703030000b9441401080403007189071030b0442e1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 254437796 1250 254436546 254436577
    0x5090d02010f170907050a080c010c0f141b100908060112052401061706010f0507020f041a01030f0908160c0807030f111801151202070807030314010308 67
    0x11502c00725039002c0c0211469840800510500000d81e60010b12401510030a03581003e04644504045070303030b0b40707083e2052070008840490382c100081303452a40d181c2c002d1107002050030001020200c0b50070414900155001003030040030700c1c001840c050b140048030014500300002200d082c2007034151180814013450840e54000e00a000c00c0150401401c03840c00410032601241154401400c45010000e106100006444a07504620802c100e03003030601800c0c1c1611450b2905003801e000750b84540001c0c0301640d01480b224260b25442c0c4441c0610558281045500e06403a0080c0b000901282c254080c418026490281410001042c8804690107400d030038075207400400340e503d801c0e0441d403010740007201140038594002040084c1f42c000d412400784120001d940700d000c0201800700a003e03420110b008681500c0c0100b21103c40d001d502107000768646460000c441580c00e90105a07031228a0450b030304d4000007145010b140e4540308140b1710310503042c451116035140d5103c1d0b09440c02030303003040c01d0100c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 254439046 1250 254437796 254437817
    0xf010e210c0d0b0103021011030a08040206040b0d0b120c01120e1c080403120b010503040303090302030405030a0308010806010806090d030506010219030804031706010210090203010605040203180106050105090d0201 94
    0x49041004110380c080003004540c10b0101d5151020090300c2c28030040303014003510b800102419000703005440e0b509a01000640c1401c0303650800300d0b02c1d44c0015006030b0b0810420000440c1e80740d040b100400004012410104080d8040002c0c000e00a0282c60f02c20078039003040390440b22580e440050300b00c06443d800f10101e100c40c1000169030414500407102c928014554a210201503000380304903224038043d0b01c3d91b5081101c40c8210780140c455510341d030307030000300104001030000e0b009500080340c2078001c2c41141d0034943c842c030200c5c0c5042424070003580818400b1004202c400c004002503030151100c0d00c00761400313040001c00c0a5946461b4542e100500d5110400140603903c03c1008210408410b4000080da407a40d08001d0058401503030700764001281005412410101c2403000d0340075000607401001000c45951800000b06800030040f60301d5503c4074000207140e80e036030003e503016881c1c840745290105440d035880e5003140e107154452410700c881030045888a039100720b0a400c10b10340a0a04940a5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 254440296 1250 254439046 254439109
    0x102030903072709120206060a140d1502030c04030c050a05031e0a0501050c0d050906060a1502100507030c090812031b0705120406021209060a0f021c0e0f010e 70
    0xb0101c10301580c0e00e03e80b902c42039900307200030a41043c00f4641c0d41c1e025135804d91030350030501001030b13964024055146100c2907403400c070f1304003c102e052410740104002d240c908000b00100081e40d00c1a1555443d070b52010a00b44240180c10980708002c15044401c040c4140c54580402e0311150400380c50143c002108280080c408400d02c0200d07a040e50200081007a46401c0c02170810755042032003001c040703e140c00006091003c000030741c40d0089000a0680c011305251903420103080340c0d000c40e45400c50003114100c507144c6907a0f0207803a004042e0b50714041590f4106600c0181194a9507010100039407200450100006803101180d811015508120900c1c114074620400e540c495508010001d1080000d49610341403404054010340b100c076426140088155010780145000f1201c9040c1d1082c004c00088542c41d004080c01042a4014016240360007401c4000d00700c040074461101000c110445020010b5260466001310f01c0c003c02d0900018214580011521060142001d1103808045d1312150702e02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 254441546 1250 254440296 254440349
    0x60c030c0403080d0518010b01080a02031003050a23070f09020703050708030a0b130b011e09080d0305100e070c1203181103120c191703150f010203090307 68
    0x180d40c004004954a134440300e105001420704458145200d01c3c0002c1030540d445e010b025030240c8020507515445151502d040d400025480035002041d044000365000000138424044910b07214040e50040d80c440b4080c1d01094042108a48a0f600a40101c10300303000c0100c10300541001d5071703000320005803a0803081c81e059a41d8882d1b20b502030101107012081000720b50301074100c011403c20913120143c80d8040d511559068400a00f40315010691200e40e40b0f00942540b484609c40122601d04070700400d94034140281030030a801c20313803000a0748910400c00b50000701c0504100038007040d04d0b040503d00c2d01a800a003140320003900141a280103100310150644a074000b07c01400102c03240d84040707042442c0801c811040814864000c1c040d03c0c0c40314909040030707015030702131042c071102038515a40c401002490041c40c000c41181d0070711480401a05019894001d54400c2903881142690b100c0508200016244e0342d040580c119401000000c4a40d00c0119035041110a20b140c12480641000f0385000c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 254442796 1250 254441546 254441549
    0x203010b012307082511100e0f0f061b0d0f12020304060e010e0f07080303131401230601030e070b1b0c031603030810030b010e060d0609141002030405060c030c04 71
    0x40d031030242044142509130407404010399101c6c400c4003802d1010001480503418214203401c010a146a0800000d0b04042c00c0c00e00242100500386061075110000044807078016135001e000041200341d05070b640920812000c0e00e00e181e1800c01c0b560749a48030900a01a00c8213160b4451042e40100200301040b000740c01610707a58862078024031240150014031a03444801c0400c0c7c141601c919107000480140c0482200c3c040d151120729030000d20b4140d10f803444002015802480b02c0d660703401b0b101d114496042140c5502c50241e0465000034281640010165041c55003161510713000316000700002103582c02101c0b81c43c55400140c50340310701c150b0981030804c01000f0010303415014900045190142e10003024081c7c0e03129442b04000c0e0346601083e444050281d000061100064500510a544d026280603602140050010b400000150b684005589500400b1524074094080c035800030102440030503a0011811001c40c154500354a070b0580d94440030f00111401500000400d980203032580c201d50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 254444046 1250 254442796 254442817
    0x3080f16030503072727060605040f06030212061c021327030c15020405120706080703020708030a0b0111030c0d031505060d051f060207030203010b01230708 69
    0x400c0300d45a0502410070b0740111004000070f070105030801d00c1e520f16080401920041c940040c5d051030304001d0b907584c0c1c0e010f680d201c030b1303a8910b1200211009082c9502840b0054103056036042c2d100c62030140c01d148030303008581004040c5401445411070145031001c586030320050032102e13081e01e101d00365840d42221a83c1d88020350040608a004800c0c4100c0b03402070410385c880c10402d050308109004014110006103c002030000d43c5d60b101903070220700300003054a14441c150400628080d5144001001201c28800c00c5030b6640000f4008c0000d242c21403c00359006500342415480e102030755694100c1844018100d0811558859203045a648034850440300d50001000300c03541c90901c4207505a82e00e184989082c0001d082085040384110801904002c4034800f51101c1e050245105925003c1d1400810309101c2112040d04e0b242a0b440c81d9213244010003e40e0060020142140103040c2501d0741069500d05000b1074100c0010f0544140f07040d4213041040382c20540d200c000780e19168119128200501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 254445296 1250 254444046 254444077
    0x2041d0703060522030c030c08093118080c07150207080c0f010f05031f09090b0c0903030406120b040504211718010b03014203080f 58
    0x70003000355650025006401c0007100c85080510107082030b4a5140c0c406000f80000c140c1c08245c400280183c40381100d00340b24885e45414030b510280802e100420201040e61101d0000700038001d450030881070610681c0c0c03c00801e12299500403800716241e1013806009102d104001038401d032822050020401071b00c84000403e0001145180003503450f84c031030240410341c1c0242c441180140c070b07243c0030340031403900181c4804860074050030040c0c546400c010842401d00044240e02040c9002c128000b0000d08805000015075903551b084c400780d0158010402c2821640401001c0d00e640da001003607400f15501483e001c80703000c40d803008a802800d60f01c16003903041820070b02440204103c030070f65400030400c0013030a50b550440b52070044400c0254607c6030a1681440c001043c6008a0000034020141c426000400e0300003030000801d0850750344e0b07420304218a041d1186500c2550513551112412081303201c0b40890201c003081502c507625440d1000800c0c420700000c60419031a603903015030300704500c420f009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 254446546 1250 254445296 254445299
    0x103030306080d0807080a090201022b030b01020307170304050312040b1503061302120f12030901060605040e011206110c060109150e010323030406020304081903020a02041d07 77
    0x2802500481c003941c1100e0250914965400c0e118068981c03041300c191b9a202a1a2506880c0200400c81c07210705904502070680e1014101c125031144103d1180b04144a035588800b040c0b000742102c04c0d410086046410400103000030039103214800c40069901c142e00c079130740c1d103461815501c0c52103140007850041e01c02108000912440101403446500000d0308007400f090000c0c00c040c0c880b00100d50310381c15030b4840c8415001504195008070301c0400b00004803500442c0c9203441c10714080c02c0f1b240750b1a01181c00410020803100a0003140001d000c030707051060500d03003084510030f00000140103c15400c034103c92803e09114480d082171150790b00d044a819030b1402c80100340350b1200d609014000c9200d042c03e000161030500805406c0c00c8a012158101c43c41c1d007580d0316038680c4850300e0300c01c00456102c00030720017151006000800040c9101d400443d80e0f03500d011003540c20502031001d007618800c48100c0b5403011035008035030484640e0b41240c000814001044145084840d504031007040392040301c60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 254447796 1250 254446546 254446553
    0x30607020f070e01210320060109061202012705060f2205030c060705030702030312040c090c1407020103060306050109151e050111240a14010807150c0b0103 69
    0x111500c4604141042d00c07440794072200b400340280000c4c840d2419001032400d05503518150b41d60400c011038800d240202c121501406500704454208440400c550801c900410a05600d0722603180200407144040e0801c240308e40018040d0050001c4600283c8802071403072024180c3c0ca070f8080b028080080c4101c1c0c0321461f005071505250031103540042d40071250b000d0311007188440c440b840b003101c8004000f483c1c895514000d010141d003010108651600c01823081c0b50041c2d030148003611407205070380701c0e460141c606820082082c10055000841e02c80c6400512002c5039840041c40d000000c0d8030702c51543d614528401240180102c2d07001501441c50400045013100c0190000d18075180140b010108071903c80300c56220310754084480c0c2181d0065828100050b500a070000b00c0407038195001d03215450030051f500d007222031709010b020040044d0842004039101c001c3c0300340c803000e210303500c055102d560401010540d03590321802000c49903140b913002003c81c184034204001c106540b080f00c10284d0b5a6918 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 254449046 1250 254447796 254447803
    0x3030d0203150a08102c060912190e0d0606030506071d0a0504050612030705010219020a030f080a020c0114092103010303032a170702010e03030408130503060702 71
    0x1e0b9690524458145160711900d0a00d00d84800c2e15842c0300504004946041e00c413000f0a498602c0d050444040541c0e0002d50f00b180c12070900000000003c0c4c00c061408044c0c8608112181c00d035800e628200703001380d01d00d4103c4e105980d000d000382c9080a2498000c1500060b149841c0300000405007410100c0100402070046a140e00400c100d840e00c010314036400e9200d0b00f019020b405140d4003c041a4400c005504e800c1c5c02964001001804d02040c052a001c80141140d100b00019103090390002806202c1e08486048009840100d02c0501044c41d0340355001000380044031300c5c60b02003180c890007146014140c2d030b04031010710036050000c0103050756600100d5801d410455958070300d07000d0900f050111500a407040340c44d540107402010702c0c0d6030860703406800a2140c040809050010251410354220140042040e601e40d1070b25290000300d41c040c05401c902e000244101c08690600c4400484002d0000c01d4a0300319510090071511111094448400b2000380e5010550501c924400e2120164011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 254450296 1250 254449046 254449051
    0x13150f05090f01050105010504080318041104060926030307200f0a1e03050d15030b0c0702090603120d0e030c01150f06090e04030e0d0c0b25030503041b0503030d0203 73
    0x2800034800385c1c0c0d0396001540e0f6405144100038454000f01700c408001c90f00e0300d1b01c486c50803400500c00660b000c181f100f01585900603402c0030300820b00e401c5003031002681c8a241142112040ca500c00d494001d2050050344134003000e0107510502400750780e000400a240645051405046000c0301c20703803540c01d00881e60391446500c0948036150425440c030421003075600508001905611841c1ca400e07030358180c4400414506c0142002090740300404000104100500d84c040d0095a00850715407100c1e00401000030350103400603210b5401180740c4c00814031418290ba4841d24a03190004900307000c0c011b62400c40c072a03c040c02d151540380602c407040032005440250141c03441b40e507804418a440b0407055403104001d005240100740c8100008002034841c02c1070b040754013000b0b8a000c415a03040d0b580c15030005c5650304030000b0340c0300100e1680b05943c0148401c016403801000580190001c5840161203840f0180019103846603803a0500296034070750990100904010f01201e41d0342e130403000e1400094205 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 254451546 1250 254450296 254450323
    0x120a0f1d1210050c09010c020907090302030a0305031504090b1302040207080c011b0f0206060d0f0605010602070501030c1e3014010e040c0b0c0c03100c08070813150f0509 75
    0x2480f021440b000895410346500c071a043c1c440e880c0c1900d9503000c100740302301c000704500100b0092500200052b1400c1c0650b6a8451081d19115100d090901f91441034403028000d460285d4030704078022011503401038569030800b01d1044100308179181030000c80c010344654800908892800102e214441905501407015a005180c0941c000081c803082218050741402050006900c80000305041d850071078800c003000d03880348464081d0441d069840206407042688602e025070040b6004002c10758140c041c0744010a0240b030a82041c030b550b10700c040381404200d9014801c010406610a902c510394105402c0b65041c5460800b201c455884020710246c54042c80060840010400024090b04a0001c00c0d00550f030101201000ca400d0a101144a4001d1840320040e072255080703100268500344071440181300c1c07862010032a407810310f4000c1d1000c2000b500280401c6208000c10034940e41c030350400c3d15810b6101d2440500c2810301104200038010042130100c48078074041c1032000800c00010703040e2071500c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 254452796 1250 254451546 254451551
    0xc0a080304030c05090c040515071e0302060703060b0d02070f050708100b0402040b0a0e0f041802030714060a14070c0608090601050a08030715060305030f0705120a0f1d1210 76
    0x8454040c0201080180d400a54400c0113000612140c50071409c3e82514038190b03840d982c103001c07c980350580c481c040390701143e030680c21601c5003005240e814095580e01030b5841c10140f001c0d030b192001510315407103102c00542005501084d82c030200700410840345d0b074580d0480e0071035181039210000070707441d11400e0311100e20b11443c00c102008142007030300139541280d141041b81420f0828110b0255460b072074200c1007540c04a03034450000342c940d44a210b00c0c007d00e0054128000b400009105061903c030503170308100c400c400207125501060359081c04071004900b00e07180c003c07004083c0b0391213034140d4061010024420482010046401c540c400442441130083e042100c08d10790780c81c024400018114002c0b618142c20400644002c0303071720329603c03580c074149482e000110243d0340d480300ca017107821101c00801c0c00b01340002c00c042804401c000e82d140c890014034a0614040501e80060a40003401c1c20101c24010f220b081d07420070302c01082c040d407240b850190040d001c852040700e1b015110011041101035151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 254454046 1250 254452796 254452799
    0xa020d1a09031c0b010801031101030b031c02160302030604080d02040e0c090301150503030d020705070b0c06060306090105100501080a0e0105040c15030621021201020d050105010e101d01020c0a080304030c 90
    0x72404c1c01140551481a1682801c40e400c41d01e5903c141e91400310b010b41419154078000402c2e490801807a8020540a0070600e881c401c804802801d00400f01c807064480e5601540a1025a5011801c0d54200c1d0707021845079516045100c0f200b02a014035446807000c0c80c40b0314108503007417190f00010040340d5012402000090803010410414940034000d058250348140b0203101d1250300c9600612400c0d010350204c6c0c0f099076941e60310900035401550016400d070407260071303c0380508081150031b4000c02000001d0005203030020004d1564030041c418a410490307850301090118040340d008001c0b50070400d0003441586000d05000142520600c0340c0010480a6a0580c504030b10a204a100707450721644900c1078109200c60958070007e4800003680d0080d8041d1b070340488040244020544000c01c81c00c007003029890500090181401075034424040e840700010304840943c4268401c038100409883c0c2d0141c40c00d40c0740101c1c0b0388a0500d00e000e40151001c41c02280040b00040a0411648150745411209 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 254455296 1250 254454046 254454097
    0x30b040c120b0a02090a0b03160306170a1523040201140f0403020d0201030e060703051f15120b060a0c050c0312070821010e0a0c0e030a020d1a0903 65
    0x41c44640c800390040001c0c0303010603403440c0207800400c21540c0003020f400c4125180e101c000c41e69032090b03401c65099580382c62080d0f03000703405010750030060401190185281d410808441e1300d964420344000e224040c840c00c006c03103141c820784c8040d001c410b001d03985400e805940503260543e00025241030780418510340580201c2c05080c42202c0e8210110240281070500c0c55080c031000b583c0701103081b4107050b2a00314411000788100040c510070029a900400c05040046146884034065980d440202104050074401d41c0c1081500d8001003960f407415550229400c2610340080c80d0742841c5503840b00001070030100c4140d1110600c100c06020714156a4a204451704040d82d82444082d0356840c29030a0042e2400f01d2032180140c01c0c0170032290030003140c40040340c050021410090300004018030a40d03007801003128103449860110450b90500c881e61062603c0004c0c0e880002c40c0d00203115205a40131141040b012921150500c81c0c401c0710803a06003482c04c02c403526a04110459007981d0074060503413152 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 254456546 1250 254455296 254455319
    0x30103061d0f07050111210406030b0d020a0e040f020a0909030e1008040212162301081b1303080a0504060f020c100807031d01020301140405100501030504031404030b040c 75
    0x802c04500003440071619010040d510300e00d0540021040380100b41030860203a41030b403d482042c0100030f41c9950366606000020b4120b03003c004038580604d41d030411200040e1514800907040da52891f1072402655954500401003104908009400c40520b03400010b500c2c000340c0010140900c240c6030090002421000c0c0900e205510301640d0001d401140420007504003869441148240310080e00c030350f945503490503230780e030001d59000000c941c144032089500c42201d508100c0c130281003441d0a09403400c0001c500d181e12140a84100b00100000603106a10750754040104002c550110303429444030224000503003d07411600c199000701d42042c100100243c404a5000070100009140c0414096940070403107402ea0000c101a045c0f43c0d40300d9844840c00c1c16019000e850340141c0d000581d9039810031000c4500c50005804040c001d90612060040b0b90b204000340c0002c0d601c0c01c1c41e0015440d40d481c14100c40b0000c01040e50088908001404018007201300c1030b40d880360740140c698860465071085400e52 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 254457796 1250 254456546 254456563
    0x60902091302090a0317030708280c090305100203090f0f0a0807030306121b290f0f030108010c0e060a081b0408031804050703020a02120717030103061d 67
    0x140021181400c04035040d10354040c100c6100094950603c1d55101e07a1049101e4401c03c44031b07441490040108018941c0c0903990640c4000200c038048050380c80f265040700f005001980c90b0782102c0d20b0303c0051112502c1110704100440e0011f0446010400d840c072070070000d500560380f280c80d83c02000511516900005007103414040c405004000400c450b0b1240000754000340001c80401d5280c15000401c40741b00c02200b1099070007120551604e11240da105a405131459000180100001c07420200108580091000d5aa0702c0d0343c6166985040c40040c01d010f100f614002e24003400b001c4004102208154805000c1032040c0d03c2e01aa00c06240c0c08200c003900a00550708001501c12000500f18540d0018541c0d00e940038039211030902e911008800e00b1030b0042000d0401c010b0382003040741050f20301801095041509810114600500c114000307403a10700303503a070f103159500c130000e621820810510380c8007010b15001c080807a203a503100d1030300d070703000e896030000c0b0802001c1031209c10703044003d0100f040f49 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 254459046 1250 254457796 254457799
    0xe0102030f13050909010b0301060e010803040314070e010b040f0e060a0311010c0602031e130305040e0c090301060306050405160b030612100203010e04020a060801060e041d100f06090209 82
    0x181401c100e114101c0d000ea1000c0b600704032414403a2000142516400c00b61406900d0410001c240950913105050840f00c1e2039005001c04c40c0038500401c001c11000c0119000c0c1d9400100c010140501a42040c0c90442c49070302030940000350300300000b98000c000c8060f0040e954623150381c1a5082da91f000070f0241040030b44d103165019100c400700300300241613040c1c0c0034442401810103510740e100c0b9854030300032604200c1306e60050b2040c1d40700008034903904c0e030f07101135101d03880c9401501101c00346c1d10700500d81c0c0124002c131030070a003441000c5404040d410081c0c407840b0754024008c1c0300741522443c101018060945045845109000a0200c2d203440000d094050b1141100d01a003035594401c20002d543d0001c180b428010301404403401000102ca000450181507c07520502da0381c102841031112098482d80304004105146006011040e482000350010140440d0003103001300b9603c0e1a840400c0003000100400e00c40c0c0844156200c110b030f0030017030220b9100c16080104035602c48448003603100707443d03445 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 254460296 1250 254459046 254459053
    0x103090b25110c01110c030a110307050307120f050a05060721021e090a0b160c0509090a11060d090c0608090a020d021314070203030103020418200102030c0129010e0102 74
    0x81e005540300e4085d451000c0c4041040b21400d84400021a0400180800c1a50f041414248184480c1420410f21008081c01da00414135146414540d16203c0451800100035202c1c094001d0f003441010132103020310b40d0300441a9013080c207041001900c4004000e11000c41444200c0c80c024484180e442510300030420000903900c2044e004030f41c2002d642c00400400d0344030110340d8020803200088006020103804d24541200310b10030783d00b08401c802003036a01c400c0c07051181c142000b0003950042480d81e4100da004c2c10b11200311110000251050042c184180002071902180c041445004c0d1502001ca0700306071503010242d11030800c0f81d0b407549982c5030084e402c81003e50104c00141003018141d40e503802d0340d41c23001910401d244103500c1890020303034201005038404801030080d45441d100712046101c0980c100c00c6060700540c1c60124050741145000c50700900200d140130306900910440311a020b0041c02042011443ca0300256601d80c286c04c046249001c0c102420752030f501034403200c2c00d1240160010f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 254461546 1250 254460296 254460313
    0x8041e020f0927010f05010e01050a0b0901020c0402160b01060203030108070608190e030307140403110d02040e0304080f0606151e1204060b1c030504050f0103090b2511 74
    0x1440040c24001d081d0b50810521940390380055800d09a0f8020403080380800482c44c46202c41000054400603001500c00d0001e20004210341d0b900c00c6801d50403603001e42009074a5295940050f401c0c152003445040d0018000500c012448854440c0c1c082c0c7c1c2da1203000b19124690304e44c01d00300d03500d0100340100f030402d42c4440b0092000c40e000b03110655015031500004d502e10010b4107210015905a0a12f44419510100a204946800001d42a0320742c1d21300307140c41d0030103255840342c0c0100c2d48040200c0c3d001f040d03034000c510300390340710742d0881c200c0c00303c451085a54640c1d583e4940c595072050020760050500607038002c40d24601d0056040700720a440702ca0460b0504c910494001c2084148400e00c8040f10f404211884980740b41ca4030442c0700741c0c0984000216584003c007449000d020400007049460b1030b59204400094101c0150740a8031030903907102c0c038040101401a0001d220402024100024590401080b24640f03000035003007980800e14a480800800b409445401d000740101546800174201d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 254462796 1250 254461546 254461549
    0x30f05071707050c240906070e130b1c050631021c0c0b0a0f11070e150a0308091203031e0604140f01030203010605120303060411040b0a08041e020f 65
    0x29003032941045060b1500d85d000d04606040400000c091543c080448104010111005014440d408800b41c200340350203426150014445044049a0130141943d80c0028644c6441e00041c0308805024150007000d00b00030f50800960f00c020480b44000c04003202940280c841c0035942c225003840000c02c407114042c2c802a400c00007050840c1c851414140a00131540000c00c25400959009005401071940c1c1c500a07070000401810b0141302c00030a00c201000c0d00085103000007040c404507032205104a040c0e84441d0b0508003141403101140c2e030310582c1500007005008041e0000d110051088800401074010f02c00a16281c1c002102c82180c030015912850001c0d04a0900e441d500c001e00500020761003400210303a41c8401020340c0c0480403141072400510440c2001d10502d806020200c81e94407c8020700c140a44e0b80740b100410b22070103a51262401c100100000082c1c60103001a00f00349078548920f542c00908038582114107448141070b440b20310300f41010603c0780328420340c2c01821216441d184c0d0340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 254464046 1250 254462796 254462807
    0x2107081215100518040e0a0503070807111f0e040209041d0618070608040303020d050112020108100f090207050f030f031005090c04141305090a02121b0d0c0902030106030f05071707 79
    0x140c1b10307a940106a0f04200041050000f4064684143e188a4503144203042128518400c2c881030b0380141c2d00100f4000c0c48121605180c80344808500d40380305249406030201d8081e0061242c4960424181782da49051550080517031001d50b14480304940316545e030f0012091420000740c029035181c0d00908001e02c02e0611802846a01c54007e090241c0350544140c072080c21103009174411484c00115222041c110b43e4410362040e00203e0141c10300004500700040f003c6c0e00c1409200d8000b030958001a03182c03c021040c0702c40c050000441096980302c01d020302d02c807801c1e58001c992040e08141c04180c046940c0c940641050300910340300511030b04250500c2044d124001c074149070356a105c01010032040810324030b070184a200d081c10b130010301083c1c000d620500410780301007804440160881340c580905d9480c075504210441000715010320074251181444004805940c11144034036000000100f03d090f0190010412080064020003065440d04000c44580c400001161401c00515000c510074501c02e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 254465296 1250 254464046 254464061
    0x312030e0c042a030605091311030c091f05040e03090112090b010b070303020903060a1b0e09270609010203060a060203090a09020f0c01020d0914210708121510051804 73
    0x900700003d110340c171b41c0c0014081640484442c48000c0802c4220805c00c074040c1c00b0340d80714801c01c1c0c008001003681100000c3c04014024803034407401100400860131800c240c4007400080501400400a84026104031601ca601c11725245020030041007103a4200c24207441158911500324134041c000380d00340380400299500001d0241c0426800f800a248180d400380010f0340900d035502380000c6c0c0c4240204031880040f401c1500c89040c410300b074000c003241e61103a10300f59a2240e8526683c1c955050541d1440001083c2075952504a11030442040743e10601503005502a03c0112500f0548544e90001242e6900c40c08081ca5040010503804020017155900a05686003005070043d0074400e25440c854226048540c210785519111443c1c141444154181e45042c407007540003804003247d070040060705408020354001a541300004980082c01107180a03500390345032815142c035503414080400b44004144624040c480ca004000400d0800e0088085442c0f50819040c024160040001080300400ca80c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 254466546 1250 254465296 254465381
    0x31506170316081806130905100e06060f19090806010f0305031602010203041518240f030b040516020601090c0903080c010f020f0d0605010e1c0c0312030e0c04 70
    0x6035140400103545d844081e081e00910446a02d080d585050060802d4440280905150038071801d824045030040001442e4408800e4920319030300e40941c1344000072071044801d81d2a12104089039541115405403011088030180030441e402c3d80d8030750700c0080d1f070104144401019684101300c100c0014484820400790301d80140141c03804c0554901070039040c046200e4442000910245180c1c9048010050b0400908110300b9400d80c2d590a5081c4062006170054401c0d09101c3c9280081c024203210303820000d2440e4004d0024812418811618401084a4020b581c0580590b000201c0c0140f41e034811141099160f0380d81756100392840e21903512640c402c0070104860f540302d02c1a02c201a140e40002c0c05801d22113445e055455110b5680b00003115102d070442030401c55992070b001041d548408055142d01082082038400c6501840d10074410501548010401c10b210b941c40000d00e5090750014001c0750041042d0307064071824004200c203e94000c0d01c0012910900303504030a2148c0104d01c48c01e40f0050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 254467796 1250 254466546 254466577
    0x30901090608060f10090807080a0209060120070f030204050f250201021317070b0309060403050c24060112060b030705070519050318010215040209090703150617031608 74
    0x101d103011421404030b11107100c011031b5036072004004640042188030010625035024040b58101503002400d8200b010700f01504200410f8001542c5e101c000c19000c484040c03031011107030015511850740c01403d450340f00581c450380c0352400080d94641a801c43c0b922542240b043c2d0002e45407200e080300c402ca01d07421910021036500740080001d80f001c03603003800040c1294442c404401a22030600500d8443d032900500341191041c4140a24140001055500203500d820010384400c00010060701d0171943e4110a14402803404149028020b4452a94003962081e80c0e08001110108403180c20380f0718611518146c2041000011100c0b4800c5000e4a20b2501c10400e07181781ea190300048140c01d01d011001594035400000b00015100d8041c03400c002c19050a001a14008640101d1040d00d4140100003a0161040701c000500c2c3c6c1c2014001000034640c44105812001c48802c422802880d050150600031180b007020340000d407400101396070802c1d1006100006a040c9545c681f80c0541103030f050003001e0070307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 254469046 1250 254467796 254467819
    0x13230a020c10180b01030f1e0b0a0207032a020103050c07050c090601110a080301150306150f030b06041706060d02061c06030209040803090607081504090c2d050303090109060806 78
    0x1040042c10a009601a5140d203107c0049414030003521b080c525a145c42c05043d100385040020f1923540180e500c601e55420050301c1785c040b8241910124610700c8a1301c580f48450030002d03d0014548505013159000703030307070030481655074540340e0030175106810002d0710607841400c0f80c003114039050294039400700041c0340402034000c0408285141240b040001c450003034012005125200e40d41c1c0800840c0800b91901744500d6140a00c00780469441020312001c11102c031208505680c06500030551043d40580220759480c2e5a01c03407070a001c9024041030007240100d50100c2d5a614040e0400b040c5aa0020f111920303081c0401300000b050b0024117280001603494400000c00350f9a89891035100d40d0148044680ea480d084403e5030900d0710041960f020b2009a00a000312441c148041042404007506c00068600a6041c01254042a68404102d0b881e002041e002000392a0031000b480d030f80c05650194410361030380d08241e228050099200c0c00140c0b1420304000030742c401c012681d00203501404415a14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 254470296 1250 254469046 254469053
    0xb160311070215090d2a0f171e0c01020f0d02070b0c01060b030a020703080a050919080408010204080a020a15120207020607021020060405061513230a020c1018 70
    0x10721000000c0e02c0c10781c040301c1128050782541403031043c44d00c042420069840d0070000040d249040a0080b03202320060000f0341c655030b5204001d001d400c0c40410007032015040c503128840d5a600c490203c9103006026040314001005400203c005076041d0680140c07002500f84000300a40d81c1101281c00155034030307a2000104045404000c40c0164010034003d640ea4519040107005020058808030023180f4142c10000b852601084000c1e61000081209000203000c2c1001d032281d005076084180e140d40f00140000c1e40090010f4401c84092094803880740300780e500c0380341c5d01c1c90081044101c0045a0b0030302c202c401728001c42d4014000248000c05403800d260091f00845c0c4440450281c100110b0005201d007040544c41e90950140d001c6081d000f02400e2915595907a10349901a200d90014003010154080c141d9034458504d103071308540d00c0200040d0030394030b14880b113040c0d800c0e402c400760200c03440105000d40450300032900d0300b129000003080036081401c1201e00404038011039004c042c85c40310720301000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 254471546 1250 254470296 254470309
    0x1501030b01060806150d020d0b030d080103060c02070806091c02030f092707080109150b07020d0606050603040501060303140403031b05100f020c1c171003020406030b16031107021509 80
    0x4c0c46c8002600503211100c11040340210f0300c181c0c80c220321941c0480026691642e00c07101c00c60540340c1c0220046000904080e060b880c1c40401c4d04103641c103029203800c01900c0b0a0003c0c1c1c41039640b540c085401c4150301040c1c01681c49105405000000110402c1200c000307080050341e80b910180988100790f600000020b00d80810142980c818000403034144c010810842c442c064620910440c591440344145401c21481c81c511403600000e00640e6141c8006090003082c0c0d10000c001d02000c0c140607640d140915141d4001c0855001c1100402e030031800ca07122248650090b24241c1c1c0d49a121030196055031951502c010852003400c075042e01c100c80140c07010320464094034034156182c00025898509982c4140e060140e29820120940d4000300e00200c6142e0080d00d40c2c0111f070711058505e40540380d00101c2a55040950006074100d030510000000308050121000e02c90340c92040151001c6062200407000d40700125a0403848400038007842015140c2846040d010309030480c85a4505224040032664 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 254472796 1250 254471546 254471557
    0xd0c0203160e0a06091802130b040c111510260111070501051302010e0613121101170601080a0f02090307060306030308010f050303070605090118050706021501030b0106080615 77
    0x20403202e88000c0c000d4112071406100301412001809200000c2031880220807000c0c55203019108001c80c440982920b115644403e0108401500612a90740e00d02c101600d500040f101c40c40241c80f58a4102d4460100410224041e004183e0940c1d400342c036200007071072003130110b20741c44c5055844030310410080b4009101d103d420b0315071544042c1d2101002d0900e1401c440008041d4041020408102001030703a0298282000b00d80c201e0b095500c0b0000310400003191102c540100514100c0312400d80b05014400e81c40c201c00740000d0340c130782081c030781490704440e02150b054441c2070109401501040c902c0a150304110681004444010700341090301001901d80105948001c3c0881e03035504c014002c0c194010700c1e0901410a58401710f40640c94940400eaa80c42540006080540d0760740102c1d425003000c0d00407032050f601091610b01c100810b401c09030b40302c004911600c0d000d48a40a6240e00c01001e04521034100c07900007210702c69581c6000c106481070680140030660212515080c1c00e500301c056030143c80c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 254474046 1250 254472796 254472809
    0x2119050705030f061302011815031a010e0f060d15030b010812070809060901091e0503070603090b1f050a0306020909072d0e030d0203030f16020d0c020316 68
    0x1140a180205050814444421080480d000134007044400c2c44c0d9403240300002907082ca402c403005918400e000ca0919002d8000d17400071901b02e509402d0f441d91503001031110b42c2e20000c071707a0a00c691205c01507400030b03000b0541316007000140e2034100c0d0310325100707000d400c1550360800040369000c0a941c0f201c140d250300d0307001290101031000046c8911101042008594120b0301c0840e843d0000c1d41d00c80e888540203422400d40300305800180219680d10403606040140f5440602c03c42c0d10031205143c2d042d01c6064000d1b2402803280d1013000603078a110b8007458151030781107220610344d40c890304001403000007030a003000e080c2940444001110b40381c8000c8071006600070320b8010b85030701c401000c0200001c009007500d02000885000c2c21485080c0034810403c46103503420140100901c0001503409412049802d54140a240740c1036150540101c000c501c500d26484c84603465590b40448040051102202e80f401070b03210014a803a41b0740500d0481d01000d00040403204c4450904800d0b2070060a60f4100b02c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 254475296 1250 254474046 254474053
    0xc08090607140106050306010b12071202030c0d0b030c01200a14060f0702370204020a09030510061a0a050c0d0f0f110d051605010203010602061e06211905 68
    0x2002c0b8200288200b40c040c2504a002c0c21203949050b02c40f000a014030342507801e644d050400402c0340c10b400b8010124482a960703500755205c0c6000d49070b002a40e044000d80c11030050420400304640d01d07020139001f484c4070058640e0602c0580d031542042c04d01e1a201148016803082012900101c0d101c042d0006040b504840146202c0c81c00005050001c0405488031055510004a224030030303d40f141d03a0360009442544040e0388481611002c1c0448c592050f010b90072520000306c0d210783c9030b448080502664000c2049403a103100303d144810459400d07100c1c01c007103078221a084131045803075100101051031151805c0c0e41410060018142003261a01400010071404c00781c80c00b80c50303000711466500070000d00b00740440e07039000e070706041d15100244286020040c0000b03040c03415100030001d403411310783c002c40215100d40c1c503010060b564200a903059100174401c115100e1110540c80215882200040c01c1c149052942d4002007100141c0c00d240c6c11261b00071100031000c20b407400f100b114134050040008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 254476546 1250 254475296 254475323
    0x60304060b130203070f0e0f0a09020309011d0c090c0d050108010c11060f010603270507050312180405061c05010c0806040605010903141c03091703040b04030c08090607 74
    0x3040b400d00d6190504070700c42401072003046203550308210710000d48003da0900f034598400380d40028509006030460160701104804002c90032000035400b0354800ea00c030400030411b52003002d04450711946ca4100004003070703209142c1c2c41c0c0717541000c4020580111600c042d0350308049130000001c080c1c8809800c0203516a6485c003000d18641d600c42841b880e40303200c030409413806082c80c610850710a4014041d52082c15212455441c11040f002c18408808404190200f1801058038006407501d45038460340c1d10a20844100542d030081e400b0894101d0400c08413a28441ca07200414000980030040c04da507440700c40b010490410b41d000b802070042c00c51040000040d071800d0514040d12000010700903e009030300e00a4240403503600f0107070703040c1541d030030000f40c0101c00032081c001440c010340303458580c02c903048904030041050b401d6000295414803c6021441d40416400c10b14014001210081c0041c51000e010601290080c62903e0b0041e01600d0150300e03100401010440d42d91004400700d4208050094 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 254477796 1250 254476546 254476549
    0xf11030a050f1002040303050d0e0f0a05030403050f030a080a05150406080c030114060a06080405011104030b0f06030109080d151a0403110d03090302120304080a300801060f0e060304060b 82
    0x1200d074107280003c400c42c1001e0031074a001304540075018000e54050355401d0b242e00902d10800440c00460000411070316040c0700343c50229180e0b041440704450511030505c041c041101301100381d446514155175240480c0d542d4110301009010003610403104d02402d2016901c01e92160301a4101031320002c401080501d902c0303c2031601315031021610610b42503c980601100c0c1e6184a2200111021481c0000e21030304ca40c18024010640280e000900d040e000400008007c45030703102c103104049070410840250745650a05081e1a4034101c01801c1da03108000504000a80364041001c003951884100003241d1188aa402180310140c0b20307000d5040d020404000f00710a07030240500d032240030341d4030000b5610340307507800360a0113200d02000340304600c020140500e80f803082003901d004003d20300441d0221039050601c03080368202c80c0344000b209401c074031440190001c0200c2d0b444014010780e0b5135200302d0b8600301044561920f1420381b2010009401250040703552182c0245010310b004103800101c2105120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 254479046 1250 254477796 254477803
    0x9120c030e0307030510090c0915080d0203191b14030c0705010e03070b031e0106030914010506091503030403051f150b09090606040504020d0b012006040f11030a050f 73
    0x8000751290f80701d460709000140d8003190310f10080d0031410740840c10307004030b161049076644c00c0d03000b20410a241c98003a0613400d9100c0e120201320780c110030540d5007514580f8070482e1030748a010b07050b000d000110000b40a540b4402c42500304251011030b5500e42403120740d520050955241c02819a0f154408641816404414019000242030900b0f12001419199001c01d490700024818800040030210004104400700e40303154203030b2800103044928540c1c403040042c0c018448a241a15242164a124145e00d1320502c1420f010700001444002c6030790b10803012501070450741040c260540000e100000003d20200910186124801c00c04c004100201d041340f000c0f10a8008000c1003900001c80c200710744440b1808aa001c850180ca0b0798401ea81c3d500302041d20740c410f5a0110360018400520f0070b070292116403081a8080003640d9013181208039541740584107048070b694101940103200402c001070350320024074021610518464440d480403000180c01c0c920021400c2d40c40d44c000c00e5468202603401d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 254480296 1250 254479046 254479067
    0xa0605061005070317090321090607050f070210031820010918050a090b040501200901171905010303050a0314011401110c060d0f05060d080a0f0309120c03 68
    0x30b01e8118201443e0b41c40090035803a6081240054061803008181e008609008598240c40c803e00c18850b280c100c5041c1032640c85d01202c1c041154081e00313002c96140380c895000c0710030005480d001503042c481c07542c0810500a8001400e00103065480c441d0312080f10400320140501c502030010300741c11b0500452403120300340350342402c0e60401c02d0144c03052105250059014251215030540004e565841c0d054040c0201880e010184c10651410300700010003038150000303c1028008580c04101003041c08241d0074070700031200303502d01095084161461492125a20350360100c80e40c2d00b4100c07400085001c3c1000c4030400e80040d000100d0000d8210700c0d20b034240c0500b580c007414884881e165585000000c281c4400000d0229041013075411041d14042810800c0005113480104a0307903070b0780d540210010091215406400c82a4101030004541e86081540241070740d0700182028a040ca03401741c112080e9414124146c01e00d40d8421005020903606550ac20000c4a2915040113144044c14054855080c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 254481546 1250 254480296 254480329
    0x609042c0703030305130c0e0912070b09011812050f040302040c0908120a09030f050a121d06030907060c020a09020a020c2803080a03060b0f0a1704030507080a110a060506 75
    0xc6d0111400101d0002c0b0705c4003107440c1c0c03860191054962020645c10008400e03605141100d0119104003442031342120a0b003d001e162008018110f803181e0300c00d98904d040b04001d800c1410031410310046500a0f8000e0008064020070640340035142d60000e8100ea001000286c0013805950062104a8003001900303401c000414602c1c2c03c05074540c41c02050360007107000081556005800ca0020001b0800044002c16071280110004400e014002028103000756220060b078050180c00c40c400342886070840780140034000250a60a0038290143c60001030140200e030401e8001500003042c11462016000c3c034907896000c5c0403045004010000b2000c038020100103c04080c6482100030400d0540c1c007000c6039402140291200a40d510640c0141860741c44074200b240e000a10503107014291008009040302c5458000100201281d400e0f03c1602c11100180850010016040071a0002002d0801c0030b20710700c0c1040160f240c00c2d600c2030820703a0b030390700840d106a101d8040c05858070700401c0030001000b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 254482796 1250 254481546 254481571
    0x1030501050a12030516020402030f190c02030d150305300306090f1906030503070b0c0405010207030f020301090f030e040c030c020d120b09070c110904020609042c0703030305 77
    0x80c403500785409000c094005080c8040010480307400c1aa440c01b5200c0c407500204111745a2502c0f940d0007030700380c0c000c40d03071016018901c1802c2c0442d14481d00c240602800c040d07000714100444a80210010b0058950304105124503d10010000c0d02c200488410b165900d15a42c2c8081c1e4541c5511141c51485007188602410500030800b0540f14a03075400d42c0189000320b801c1d810746600d0b015000e903404c0f00e0f85420400d820403001009002d000002001014810795400c0761903540c810031780380c80b070040313000d40c42c0160001101080850400c405029050340004e00021f81540c00742d485442c8404a01000c80100d01540441e0480d40b5041c402c1d00c00450700c2d4202030125041e00d40c8001c0d180c00050901d8400c3c803c140e030581d029260542d00080c1c0701480a0900c0081d420808070103403091b42404801c4403041c950040355442d03800c00d80c8009000c7c5030f010b00140d00340700e10001000090705101e4900011000e4900780a1340b40c3da48002014416000b203006080304a00310305004043c0c820003086c0d8008000d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 254484046 1250 254482796 254482799
    0x90d0e030c01051207030902060307020102120c09010207030b1b18030d0206010605032a1204140109083a06150c0c05040c270509010510020a032a1101030501050a 71
    0x760840c04644412242a2402104e40c0d603c507410b4000305034001e070182d0880b50100401c0309440c2c05500401c0d580300c1d003000d80a455035501c0f280d041c2c0392185107101401030b045401c4c100001520806025041400700221000301c0c6841c68450740181c11507801540b014100c111520400d04003482200344510461001c1c0000b503040403009401c40c40302030585071060407140461b042880410b0044580840d4030b4080c259201503056018804220544054420207150205a051080c0500c504000c0d42c1d03008908900384100213002e28940b401851002a28204406d130b5200714190803442043d250901a03000540b06060070305c01c1040d81c040c03100d05000e004108205ca80454400c039403c000b12801190302081d00307502400d0444180300c0c0f19001c28000002650440781c07100e4480491404d60b0741c00d94880700075a81e54810403002c030005000010158101c007002d400828031400c06c1e00221b074240c11100e000006414514604600b5040c0d00b520442c40c2600d40c032415682c180943c40c01040112408030045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 254485296 1250 254484046 254484049
    0xa060c0f0e0904050c130b04020403150509070f060507140f0f0111040e01090b1f050405090f0c072a0b0d14160503130209040605060102010b1e1c050105090d0e030c 72
    0x3d80c41416046e210341144254504800c02c59040004440b101074401c2d9111540ca20744800420103246242d4107407814200060b0409000045003411107000100c40b02a00e4070f052400e543e1540000c3d800e0341c0e07c00340d41031042c2c00b000c010040e416102079042d00402c3c40070745170703000f943c01c40d010050184540c443c100b004101c40d40c29005141d054400580c8000303000c6113072100141036082400074202c0c0e400c902c0030303202c2122a0083c002d401150010307104900a40d849200c17a40001e0310896100840050502844012a455030880208030700700340215250b02c15a2060b5000c0300107941d004540e0550006804400240d8600034100d031800701e084440040c0c14800d8002900304001c5200000300321020000459003551504100c40c5142c01800e01500d9042c24180307100905012540240590b003010600700d203d08040c0981880419880fa01c10050071410007080031803485c4402d0f0034541c220b0801001e0200d0028405c10b806616030600800c070191073b0f0100a00040c98803020b6034426045801e014805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 254486546 1250 254485296 254485303
    0x3051507030c02120c240103154d0703110c0105040e040305040e0703060312090f050d020102120c0f06181005060303130312020c1c0f050a060c0f0e090405 68
    0x1c9030040c10050b85a0b0f1242d09000d00d03000c540300d007042208000041d5001c20000c1b109800b41a04d0064031000400f40c41c40030000240c40d501024400d45020f01c903009004c0402c1601081e580c2441d46074650300c11010029460410105c0950341744c140c0c1d00001d0b24000309600441030400198112000e04141c0417840000783c0180180d02c1406d9145859000090400d4460030841d00a07145600bd41d004074217102000800815960104440800006101c10440c500070140002105c5641c018141d40b58105424004601c0110000f00e0640c82918441c003810500320015001880514005018028800b0090348c9004000780002c18a8149c00e6095490780030003082c0c55112260410b4045070035203860002c0f91942c400e13035082015000b0310702004070400505030000c0c1c0d0022a65402c0382c2d801100c10040000c1520280d0724a85400d090300c61810000e007a80760082d50305030040c01690f09503003041d02c50109440c4840b65150010b580c0c8000090b500c0e030822080000c8500983e181030440c80c1a0b600c5503038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 254487796 1250 254486546 254486563
    0x20310080114061207030b0405070e150d24050a0f060f0602060c0a09030f0c08250510020a08040b070203100902131509060f090f091a0a02040e0103051507030c02 71
    0x480c1e134001118600001008100003c56001d01a2022850305062081e01d41403140a0441c040300f5104c041600c2c0001e08426068000c40144040720541c1c60340d0342c0291040860881402c0301d000c0e11581c1c40140c00c00d1040a1241c03c403848082258410a90180c003215142d40102e030348203280f44002d00030950700084480c2c1c06902c0914940e07403218481c0054640400359840141015071040541041008010b503100484801900301e81c850240c481c0410414007021402a250120f9503001300114078041e0f82c00300380034002e40103031840c0c003c040e1540840b5038099042040814000190001182000c00c8800e0a0100e850230810141480741c4c0006e020002c0410801100c580301e0221442024075051408018034041108200305036550705a0110050248241c001f8145401c6281d40c0e03444880c0100c8100d20380c00304000c11440c0316080440c05440d00076140d140826420311020666100c070048a50107076001d000140b00b14480b0003200f4011400c0104640209411703c842d10003c540c0001d8000c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 254489046 1250 254487796 254487799
    0x7090902040f05091207021f050702040f110d11040b0a050705060c070308060906012c040608060408030412090f0e04061d0304120311100b01080c0a0e12030706090602031008011406 79
    0x107541e0340c1c0c3d900005020000040a045481443d20308508c02c094000009084291003540c00780310b03d1142c80c01b0101283c4205100030960f2008008a1034442c01c01c2e070080983c1c039901c1d810f1314140f039115030f882080303904148401008210000f030b02c0f20031b0150400c400d03544160300c44c9041d46482002e40d00200710801c06040c0394001c5c441d8001140d803a0380100000050106c00c0da00c5c0c1d01d07401c0080030524280030045455a0b01451402402103454040442c1141c401c6400609040c42d5450f6541c4411180700c0c021146001c0005d0b410700800c02030aa10649402040d40a0040d82e040c00e06007006022181c024050184140002d900d1600544000c415903046449032411074182c0f0086040680d40841d2403040e0b0031160085130b80401c20740921354000040e101e0b00ba681c0d03246503a14803240420b20b115628883e804110050940c800701d19000002100c3c000140c0b00352410b2a031560785043c1550003004049841039004420820160020080e0070000c000f6038000384026039508031f801c56a803c0103000715 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 254490296 1250 254489046 254489083
    0x7050f010c03031b2a0203030f0304030908030409050109061403070303111002190306050d0305030105151b0705030606030a0807110a030c06030615170f07030e07090902040f0509 78
    0x107050013076000c00010311408902090302143c020000340072421031241820403480e100c1c100c0301d240000501c0742180c2075010b4000c502d095061200b20030680c10083c0704030200440403038003003141d00050015100810044802150650401460100780e88840c0c000741c0707045903a06072500040e80c0020741181180d40500b003a000d05035a80084034201482d42c1c540c00c3c10503000240d107050422004580442c1070074959801c20002d40c4901c200b1480c400481c034064000f407401d00041c801da00d0274080300c00400c5014021140303024a00070f41380c055644c5008826445070030256007006141001e100e802e81c4103108401910010290390786030b01c0740e0b0081d040040c001900c81c2c60703d00f00e103454125841d03020395004518469076596505005015010300c5c0103140c502160400b904500301d00491815540012807401d025107076441000d55042608024002e0f030030142c039100085005131b41400341a0107844900c501155902580c018081550402d00b4070884052800c1c0c20170400c0000400d5200100e519882d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 254491546 1250 254490296 254490317
    0x6040509010b060406020a2021011d01090308060a0f03080c0c0301150807061407080306010c0b010f05010908030301080303060108041401020307052206140a0504030c06081807050f01 80
    0x1254010402c90803030035001400002c002c501107400003a42c500c4a441241039403043ca94903048180f4a0790b42c841c525070000704503502c0d0a5014001085011108441c4000041c0d0075040e18400c002c40e40d00803c113110695503108003109040e40041c43c60fa12410070b031074050f8018580442841b901050381b2000e012048040b58016a50000384003807030b680c4030b00600920010549404258008840307114116803489201400103482d40210081d416031924446031904048080d242c0d0308a6a0004041034100850305160a00040c03000070524003134003002c1c0302040b02504010002d0b00d12a41900f0001541c1c3c001e00c01009060000000c0703a074403490a2921a5490721a40f5002d0045c5244041903802940040704020200e9800809092002e0f200c0d0b403502e440010568035000c0d04072284c02042c000410040306005000c0f40c1000500596020b0301d0583e1600c0e680c2e840d600d0130408503401040024120000703020704405a1100315112151001c003412440746080700086070000000e21160600c40b903900e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 254492796 1250 254491546 254491561
    0xf130201110a1a07020d02100c0e190f06110c1203040807090f05010605070213050711060406020703020c1c0210210e070906080304090504110a0305010b130b09060405 73
    0x210711484214800300c03000000d440c40c003054084403a82c0c040c5032022070840000c403018800214100d103014240c02500210390300368030b110302800c10300500d10113010204160165a403956460300203d0a81041d010502508000a180d1088040d90000c41005050307180788040c0c0001164100000740120b61071203d01c0204420740c2d08502803130b44582242c1c0900d442c00074071517000c1d030010411030b228800e08000320380c0c031408140e6150003560b1001c0c0d002681d564502a01c090305134042a0455000d0504c500482804582d0a140003411201221450340200f095070405404014000042008903601245141c04031070811083d0703056040030307100e458803c100c426510300482c0000d2141d203290005110780d1140340d01c0c0102500b81c000007583c461107503a5002601d01ea2030b00c05c000030b80300c000c2d0145241500d0001010040e10002e007050b02e00b00f03158044101107564a44081008510603400810a1003250041104c0c40103071134000307c20a4203242031480540e40d6039000c5980106e0403140004c00d5210a40c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 254494046 1250 254492796 254492807
    0x12041418090106030204060510020d081b0c07090f05010e072708210a0509060d0605060a0807080105180a090c051e03011505031e15010b0702090f0f130201 68
    0x400540d603404060140100800c040d009601524020344003070000c1e40e65881405009101d40c41e1f29001a040300202000040c07207030440c1c81e000701461140e514034101030f941d0f030401c070307440605d130003041d87d000e07e0081004000a01030810f000c0f9012750104203a40c500040603174a00b200925134010021170701041c4071150b0205074210b06c500000702c0c131444100e8031162220740c2c82c0c0ca0504011102d00d200c6c4404690140000b00315029140203a551909043d011020f1180d01e40140e0500751105407030b5103000c946a02c41ca8042e100040b8241d4550101d4140101c01400c5030b403041e04094044e02c003183c22644041412403006030810710707042e4001090490b5040c1038841400c0c9410031a400820030310703854080070100a0328040c102045000308100c0f1100c0415501c1c40700703503210301c0345c1640001150500c5602040e0800c4d03945010201601c0480c80a55142c825024003600004d5040a0119908095080c543e66040d13200c13601041030392250421003001e582803000149102541410619140d00710791182 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 254495296 1250 254494046 254494069
    0x150b0708070219032906030109020f0d08040312051b0a030c0213090c06050c0f06040c0312050d020307030204150503060a03110402070b01081c020706052a0d020f0f120414 75
    0x46400e0100345c400740e14100943e400d00c00800864030440340412141d150600c03500c01c00700e5004040148501d02c1c801400015050300000b40d8021002744800004100040e20b8840c84041ca0b81e0b6955490425565801c0c7c040013419a24410340c0c80047c2c0c11000980040152216a40450380002c0025400104902030200c8800081604811210014070350350068040c00c40d0021341010340d02d607104a40e010640e100c1c0120340280001d410f103072040000c501941c0d603881000085181840ca8500c80201c0355060340d005170b0706180000e0303001030b0820a000003442881c9029400e031520030301e54102007001482082c0b1030300005c1c01d9501c058668002ca80e580d98100c40c0000e03400b0518085030340c0d4444005864100550382543c0b65440036402040b02403001c100203058601503141c031400c0218407120111445040700701a502d401d1020355200c003084c4c08000b80240e42d242a4000e040850501c1c040c2810014070a26158456100600b4000150030841c1910140c3c0d510051004010240703200040400380d85 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 254496402 1106 254495296 254495303
    0xa0b0604090b010c021207050925030c03020408070b0306041b09060302030402040f051302031606021b030c0405040c031704030f122001150b070807021903 68
    0x41d41c0402081c0750b040c50712030080c0c20140d002c618941c1c0181c0074420b156218110804c00d82c50130458080e4400008016840d807060b10614030190424410203140034552140300121904e8403ea0560b4020101c0104031000300755202c0d415001d6a005480d0180100c4c240b000e40003540b40c1d000f40c01440050950b650035412071500b0030071030094001401c126031083d222018210000c203240109030140d00142c283c220002a01c0c410103190410040680d920a00d04140420403217030040f40410001170004107201c103810401c00043e00700310b03d05440b640d00c0744c039080510050100080d41501582e12a04180d0300a004140000f000b5010341e1100520f205103145070350700000e046180120040c400d9040590980018442400c0c03501c9074611908020b80d55101c40c0308840444031405170042a481340c5042c0381c00001d480b00b80c401c3c8103400c0060b02800c2e000ba503a84105600b40c0802e4020743c2c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 254316546 254496402 := by
  have h0 := BRFrame.cov_init 254316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 254316546 ≤ n) (h2 : n < 254496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
